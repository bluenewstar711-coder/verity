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

theorem physicalZeroPrefix_loop
    (varName : String) (runBody : DenoteState → StmtOutcome)
    (initial : Verity.ContractState) (base : Nat) (limit : Nat)
    (step : ∀ index state, index < limit →
      PhysicalZeroPrefix initial state.world base index →
      LoopOutcomePost
        (fun next => PhysicalZeroPrefix initial next.world base (index + 1)) (fun _ => False)
        (runBody state))
    (state : DenoteState)
    (initialInvariant : PhysicalZeroPrefix initial state.world base 0) :
    LoopOutcomePost
      (fun next => PhysicalZeroPrefix initial next.world base (0 + limit)) (fun _ => False)
      (execForEachLoop varName runBody state 0 limit) := by
  have step' : ∀ (index : Nat) (before : DenoteState), index < limit →
      PhysicalZeroPrefix initial before.world base index →
      LoopOutcomePost (fun next => PhysicalZeroPrefix initial next.world base (index + 1))
        (fun _ => False)
        (runBody { before with bindings := bindValue before.bindings varName (wordNormalize index) }) := by
    intro index before bounded invariant
    exact step index { before with bindings := bindValue before.bindings varName (wordNormalize index) }
      bounded invariant
  simpa only [Nat.zero_add] using (execForEachLoop_bounded_invariant varName runBody limit
    (fun index next => PhysicalZeroPrefix initial next.world base index)
    (fun _ => False) step' limit 0 state (by omega) initialInvariant)

end Compiler.CompilationModel.Denote
