import Compiler.Proofs.IRGeneration.IRRuntimeTypes
import Verity.Core.Model.PhysicalMemory

/-! Physical IR memory operations and their exact world relation. The legacy
IR interpreter statement arms are not changed by these preparation APIs. -/
namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel.DenoteMemory

namespace IRState

def installPhysicalMemory (state : IRState) (physical : Memory) : IRState :=
  { state with
    byteMemory := physical
    memory := fun offset => (wordValue (physical.readWord offset)).val }

def writePhysicalMemoryValue (state : IRState) (offset value : Nat) : IRState :=
  state.installPhysicalMemory
    (state.byteMemory.writeWord offset (valueWord (Verity.Core.Uint256.ofNat value)))

def copyPhysicalMemory (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : IRState :=
  state.installPhysicalMemory (state.byteMemory.copyFrom source destOffset sourceOffset size)

def PhysicalMemoryCoherent (state : IRState) : Prop :=
  ∀ offset, state.memory offset = (wordValue (state.byteMemory.readWord offset)).val

theorem installPhysicalMemory_coherent (state : IRState) (physical : Memory) :
    PhysicalMemoryCoherent (state.installPhysicalMemory physical) := by
  intro offset
  rfl

theorem writePhysicalMemoryValue_at (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).memory offset =
      (Verity.Core.Uint256.ofNat value).val := by
  change (wordValue ((state.byteMemory.writeWord offset
    (valueWord (Verity.Core.Uint256.ofNat value))).readWord offset)).val = _
  rw [Memory.readWord_writeWord_at, wordValue_valueWord]

@[simp] theorem writePhysicalMemoryValue_storage (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).storage = state.storage := rfl

@[simp] theorem writePhysicalMemoryValue_events (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).events = state.events := rfl

@[simp] theorem writePhysicalMemoryValue_vars (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).vars = state.vars := rfl

theorem installPhysicalMemory_storage_frame (state : IRState) (physical : Memory) :
    (state.installPhysicalMemory physical).storage = state.storage := rfl

theorem installPhysicalMemory_vars_frame (state : IRState) (physical : Memory) :
    (state.installPhysicalMemory physical).vars = state.vars := rfl

end IRState

/-- Equality of physical memory and all overlapping word observations. -/
def PhysicalMemoryMatches (world : Verity.ContractState) (state : IRState) : Prop :=
  world.byteMemory = state.byteMemory ∧
  ∀ offset, (world.memory offset).val = state.memory offset

theorem installPhysicalMemory_matches (world : Verity.ContractState) (state : IRState)
    (physical : Memory) :
    PhysicalMemoryMatches (world.installPhysicalMemory physical)
      (state.installPhysicalMemory physical) := by
  exact ⟨rfl, fun _ => rfl⟩

theorem writePhysicalMemoryValue_matches (world : Verity.ContractState) (state : IRState)
    (offset value : Nat) (physical : world.byteMemory = state.byteMemory) :
    PhysicalMemoryMatches
      (world.writePhysicalMemoryValue offset (Verity.Core.Uint256.ofNat value))
      (state.writePhysicalMemoryValue offset value) := by
  unfold Verity.ContractState.writePhysicalMemoryValue
    Verity.ContractState.writePhysicalMemoryWord IRState.writePhysicalMemoryValue
  rw [physical]
  exact installPhysicalMemory_matches _ _ _

theorem copyPhysicalMemory_matches (world : Verity.ContractState) (state : IRState)
    (source : Nat → Byte) (destOffset sourceOffset size : Nat)
    (physical : world.byteMemory = state.byteMemory) :
    PhysicalMemoryMatches (world.copyPhysicalMemory source destOffset sourceOffset size)
      (state.copyPhysicalMemory source destOffset sourceOffset size) := by
  unfold Verity.ContractState.copyPhysicalMemory IRState.copyPhysicalMemory
  rw [physical]
  exact installPhysicalMemory_matches _ _ _

end Compiler.Proofs.IRGeneration
