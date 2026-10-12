import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

/-! Manually constructed engine probe, not solidity_import acceptance. -/
namespace SolidityImportSmoke.MemoryOverlapProbe
open Compiler.CompilationModel

def fn : FunctionSpec :=
  { name := "read", params := [], returnType := some .uint256,
    returns := [.uint256], isPure := true,
    localObligations := [{
      name := "physical_memory_engine_probe",
      obligation := "UNPROVED diagnostic only: establish physical overlap semantics before any importer admission",
      proofStatus := .unchecked }],
    body := [.mstore (.literal 0) (.literal (2^256-1)),
      .mstore (.literal 1) (.literal 0), .return (.mload (.literal 0))] }


def model : CompilationModel :=
  { name := "MemoryOverlapProbe", fields := [], constructor := none, functions := [fn] }

end SolidityImportSmoke.MemoryOverlapProbe

def main (args : List String) : IO UInt32 := do
  let [selectorText, output] := args | return 1
  let some selector := selectorText.toNat? | return 1
  let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
    SolidityImportSmoke.MemoryOverlapProbe.model [selector] .osaka)
  IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
  let result := Compiler.CompilationModel.Denote.denoteFunction
    Compiler.CompilationModel.SolidityImport.Differential.oracle
    SolidityImportSmoke.MemoryOverlapProbe.model SolidityImportSmoke.MemoryOverlapProbe.fn
    { sender := 0, functionSelector := selector, args := [] } Verity.defaultState
  unless result.success do return 1
  let some value := result.returnValue | return 1
  IO.println value
  return 0
