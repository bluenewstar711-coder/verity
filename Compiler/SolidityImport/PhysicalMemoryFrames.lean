import Verity.Core.Model.PhysicalMemory
import Compiler.SolidityImport.Transactions

/-! Exact frame-boundary obligations for the new physical memory carrier.
This does not establish coherence of legacy word-only statement writes. -/
namespace Compiler.CompilationModel.PhysicalMemory
open DenoteMemory Verity.Core

@[simp] theorem empty_wordValue (offset : Nat) :
    wordValue (Memory.empty.readWord offset) = Uint256.ofNat 0 := by
  have bytes : Memory.empty.readWord offset = valueWord (Uint256.ofNat 0) := by
    funext index
    apply Fin.ext
    simp [Memory.readWord, Memory.readByte, Memory.empty, zeroByte, valueWord,
      Uint256.val_ofNat]
  rw [bytes, wordValue_valueWord]

theorem beginTransaction_coherent (world : Verity.ContractState) :
    Coherent (SolidityImport.Transactions.beginTransaction world) := by
  intro offset
  change Uint256.ofNat 0 = wordValue (Memory.empty.readWord offset)
  exact (empty_wordValue offset).symm

@[simp] theorem beginTransaction_physical_empty (world : Verity.ContractState) :
    (SolidityImport.Transactions.beginTransaction world).byteMemory = Memory.empty := rfl

theorem committedWorld_static_byteMemory (mod : Compiler.ECM.ExternalCallModule)
    (receipt : Option Verity.ContractState) (caller : Verity.ContractState)
    (static : mod.writesState = false) :
    (mod.committedWorld receipt caller).byteMemory = (receipt.getD caller).byteMemory := by
  simp [Compiler.ECM.ExternalCallModule.committedWorld, static]

theorem committedWorld_static_coherent (mod : Compiler.ECM.ExternalCallModule)
    (receipt : Option Verity.ContractState) (caller : Verity.ContractState)
    (static : mod.writesState = false) (coherent : Coherent (receipt.getD caller)) :
    Coherent (mod.committedWorld receipt caller) := by
  intro offset
  simpa [Compiler.ECM.ExternalCallModule.committedWorld, static] using coherent offset

end Compiler.CompilationModel.PhysicalMemory
