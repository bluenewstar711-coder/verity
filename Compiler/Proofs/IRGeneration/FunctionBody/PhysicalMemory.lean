import Compiler.Proofs.IRGeneration.FunctionBody.Stmt
import Compiler.Proofs.IRGeneration.PhysicalMemory

/-! Strong physical-memory simulation obligations. This retains every legacy
runtime/IR conjunct and adds byte coherence and carrier equality. It does not
claim preservation by legacy statement arms. -/
namespace Compiler.Proofs.IRGeneration.FunctionBody
open Compiler.CompilationModel
open Compiler.CompilationModel.DenoteMemory

/-- The physical simulation relation refines, rather than replaces, the existing
world/IR relation. Arbitrary incoherent word maps are not physical EVM memory. -/
def runtimeStateMatchesPhysicalIR (fields : List Field)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) : Prop :=
  runtimeStateMatchesIR fields runtime state ∧
  PhysicalMemory.Coherent runtime.world ∧
  runtime.world.byteMemory = state.byteMemory

theorem runtimeStateMatchesPhysicalIR_legacy {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (aligned : runtimeStateMatchesPhysicalIR fields runtime state) :
    runtimeStateMatchesIR fields runtime state := aligned.1

theorem runtimeStateMatchesPhysicalIR_irCoherent {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (aligned : runtimeStateMatchesPhysicalIR fields runtime state) :
    state.PhysicalMemoryCoherent := by
  intro offset
  have memory := aligned.1
  simp only [runtimeStateMatchesIR] at memory
  have words := memory.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [congrFun words offset, aligned.2.1 offset, aligned.2.2]

theorem runtimeStateMatchesIR_installPhysicalMemory {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (aligned : runtimeStateMatchesIR fields runtime state) (physical : Memory) :
    runtimeStateMatchesPhysicalIR fields
      { runtime with world := runtime.world.installPhysicalMemory physical }
      (state.installPhysicalMemory physical) := by
  refine ⟨?_, PhysicalMemory.installPhysicalMemory_coherent _ _, rfl⟩
  unfold runtimeStateMatchesIR at aligned ⊢
  rcases aligned with ⟨hstor, htrans, hsender, hmsg, hthis, htime, hnumber,
    hchain, hblob, horigin, hselector, hcalldata, hsize, hmemory, hreturn,
    hevents, hcode, hreturndata⟩
  refine ⟨?_, htrans, hsender, hmsg, hthis, htime, hnumber, hchain, hblob,
    horigin, hselector, hcalldata, hsize, rfl, hreturn, hevents, hcode, hreturndata⟩
  change state.storage = _
  rw [hstor]
  funext slot
  exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)

theorem runtimeStateMatchesPhysicalIR_write {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (aligned : runtimeStateMatchesPhysicalIR fields runtime state)
    (offset value : Nat) :
    runtimeStateMatchesPhysicalIR fields
      { runtime with
        world := runtime.world.writePhysicalMemoryValue offset (Verity.Core.Uint256.ofNat value) }
      (state.writePhysicalMemoryValue offset value) := by
  unfold Verity.ContractState.writePhysicalMemoryValue
    Verity.ContractState.writePhysicalMemoryWord IRState.writePhysicalMemoryValue
  rw [← aligned.2.2]
  exact runtimeStateMatchesIR_installPhysicalMemory aligned.1 _

theorem runtimeStateMatchesPhysicalIR_copy {fields : List Field}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (aligned : runtimeStateMatchesPhysicalIR fields runtime state)
    (source : Nat → Byte) (destOffset sourceOffset size : Nat) :
    runtimeStateMatchesPhysicalIR fields
      { runtime with
        world := runtime.world.copyPhysicalMemory source destOffset sourceOffset size }
      (state.copyPhysicalMemory source destOffset sourceOffset size) := by
  unfold Verity.ContractState.copyPhysicalMemory IRState.copyPhysicalMemory
  rw [← aligned.2.2]
  exact runtimeStateMatchesIR_installPhysicalMemory aligned.1 _

end Compiler.Proofs.IRGeneration.FunctionBody
