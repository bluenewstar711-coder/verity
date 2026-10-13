import Verity.Core.Model.Denote
import Compiler.SolidityImport.LoopInvariants

namespace Compiler.CompilationModel.Denote

open Compiler.CompilationModel.PhysicalMemory

/-- Exact canonical state after one zero store, including byte-backed memory. -/
def physicalZeroStoreState (state : DenoteState) (address : Nat) : DenoteState :=
  { state with world := state.world.writePhysicalMemoryValue address (Verity.Core.Uint256.ofNat 0) }

/-- A bounded, evaluated offset executes an actual physical zero store. -/
theorem execStmt_zeroStore_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offset : Expr) (address : Nat)
    (evaluated : evalExpr oracle fields state offset = some address)
    (bounded : address < Verity.Core.Uint256.modulus) :
    execStmt oracle fields state (.mstore offset (.literal 0)) =
      .continue (physicalZeroStoreState state address) := by
  have zero : evalExpr oracle fields state (.literal 0) = some 0 := rfl
  simp only [execStmt, evaluated, zero]
  have normalized : (Verity.Core.Uint256.ofNat address).val = address :=
    Nat.mod_eq_of_lt bounded
  rw [normalized]
  rfl

/-- The actual store extends the complete byte-level zero prefix. -/
theorem execStmt_zeroStore_prefix (oracle : DenoteOracle) (fields : List Field)
    (initial : Verity.ContractState) (state : DenoteState)
    (offset : Expr) (base count : Nat)
    (evaluated : evalExpr oracle fields state offset = some (base + 32 * count))
    (bounded : base + 32 * count < Verity.Core.Uint256.modulus)
    (invariant : PhysicalZeroPrefix initial state.world base count) :
    execStmt oracle fields state (.mstore offset (.literal 0)) =
      .continue (physicalZeroStoreState state (base + 32 * count)) ∧
    PhysicalZeroPrefix initial
      (physicalZeroStoreState state (base + 32 * count)).world base (count + 1) := by
  exact ⟨execStmt_zeroStore_physical oracle fields state offset _ evaluated bounded,
    physicalZeroPrefix_step initial state.world base count invariant⟩

end Compiler.CompilationModel.Denote
