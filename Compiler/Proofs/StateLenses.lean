import Compiler.Proofs.IRGeneration.SourceSemantics

/-!
# Compositional frame lenses for `ContractState` storage writes

Every source-semantics storage writer (`writeUintSlots`, `writeStorageWordSlots`,
`writeAddressSlots`, `writeTransientTargets`, and the field-dispatching
`write*FieldSlots`/`writeMappingTargets` wrappers) only replaces the storage
backing of a `ContractState`: its `storageWords` map and the concrete
`accountWorld`. This module packages that fact once, as the frame predicate
`StorageWordsFrame`, and derives from it:

* `@[simp]` projection lenses (`memory_writeUintSlots`, `events_writeAddressFieldSlots`, …)
  so downstream proofs never unfold a writer to read an untouched field;
* channel lenses showing persistent, transient, and address storage are disjoint
  (`transientStorage_writeUintSlots`, `storage_writeTransientTargets`, …).

`StorageWordsFrame` is reflexive and transitive, so composite writers are framed
by composing the frames of their parts instead of by record destruction.
-/

namespace Compiler.Proofs.StateLenses

open Compiler.Proofs.IRGeneration.SourceSemantics

/-- `s'` differs from `s` at most in its storage backing (`storageWords` and
`accountWorld`): every execution-context field is framed. -/
structure StorageWordsFrame (s s' : Verity.ContractState) : Prop where
  storageArray : s'.storageArray = s.storageArray
  memory : s'.memory = s.memory
  byteMemory : s'.byteMemory = s.byteMemory
  returndata : s'.returndata = s.returndata
  events : s'.events = s.events
  knownAddresses : s'.knownAddresses = s.knownAddresses
  calls : s'.calls = s.calls
  calldata : s'.calldata = s.calldata
  selector : s'.selector = s.selector
  sender : s'.sender = s.sender
  thisAddress : s'.thisAddress = s.thisAddress
  msgValue : s'.msgValue = s.msgValue

namespace StorageWordsFrame

theorem refl (s : Verity.ContractState) : StorageWordsFrame s s := by
  constructor <;> rfl

theorem trans {s mid s' : Verity.ContractState}
    (h₁ : StorageWordsFrame s mid) (h₂ : StorageWordsFrame mid s') :
    StorageWordsFrame s s' :=
  ⟨h₂.storageArray.trans h₁.storageArray, h₂.memory.trans h₁.memory,
    h₂.byteMemory.trans h₁.byteMemory, h₂.returndata.trans h₁.returndata,
    h₂.events.trans h₁.events, h₂.knownAddresses.trans h₁.knownAddresses,
    h₂.calls.trans h₁.calls, h₂.calldata.trans h₁.calldata, h₂.selector.trans h₁.selector,
    h₂.sender.trans h₁.sender, h₂.thisAddress.trans h₁.thisAddress,
    h₂.msgValue.trans h₁.msgValue⟩

end StorageWordsFrame

/-! ## Frames of the primitive `Verity.ContractState` writers

Each primitive writer only replaces `storageWords` (and, for physical slots, the
self account), so every framed field agrees definitionally. -/

theorem storageWordsFrame_writePhysicalSlots (s : Verity.ContractState) (targets : List Nat)
    (value : Verity.Core.Uint256) : StorageWordsFrame s (s.writePhysicalSlots targets value) := by
  constructor <;> rfl

theorem storageWordsFrame_modifyPhysicalSlots (s : Verity.ContractState) (targets : List Nat)
    (f : Verity.Core.Uint256 → Verity.Core.Uint256) :
    StorageWordsFrame s (s.modifyPhysicalSlots targets f) := by
  constructor <;> rfl

theorem storageWordsFrame_writeAddrSlots (s : Verity.ContractState) (targets : List Nat)
    (value : Verity.Address) : StorageWordsFrame s (s.writeAddrSlots targets value) := by
  constructor <;> rfl

theorem storageWordsFrame_writeTransientSlots (s : Verity.ContractState) (targets : List Nat)
    (value : Verity.Core.Uint256) : StorageWordsFrame s (s.writeTransientSlots targets value) := by
  constructor <;> rfl

theorem storageWordsFrame_modifyTransientSlots (s : Verity.ContractState) (targets : List Nat)
    (f : Verity.Core.Uint256 → Verity.Core.Uint256) :
    StorageWordsFrame s (s.modifyTransientSlots targets f) := by
  constructor <;> rfl

/-! ## Frames of the source-semantics writers -/

theorem storageWordsFrame_writeUintSlots (world : Verity.ContractState) (slots : List Nat)
    (value : Nat) : StorageWordsFrame world (writeUintSlots world slots value) :=
  storageWordsFrame_writePhysicalSlots _ _ _

theorem storageWordsFrame_writeStorageWordSlots (world : Verity.ContractState)
    (slots : List Nat) (wordOffset value : Nat) :
    StorageWordsFrame world (writeStorageWordSlots world slots wordOffset value) :=
  (storageWordsFrame_writePhysicalSlots _ _ _).trans (storageWordsFrame_writeAddrSlots _ _ _)

theorem storageWordsFrame_writeAddressSlots (world : Verity.ContractState) (slots : List Nat)
    (value : Nat) : StorageWordsFrame world (writeAddressSlots world slots value) :=
  storageWordsFrame_writeAddrSlots _ _ _

theorem storageWordsFrame_writeTransientTargets (world : Verity.ContractState)
    (targets : List Nat) (value : Nat) :
    StorageWordsFrame world (writeTransientTargets world targets value) :=
  storageWordsFrame_writeTransientSlots _ _ _

theorem storageWordsFrame_writeUintFieldSlots (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    StorageWordsFrame world (writeUintFieldSlots fields fieldName world slots value) := by
  unfold writeUintFieldSlots
  split
  · split
    · split
      · exact storageWordsFrame_modifyTransientSlots _ _ _
      · exact storageWordsFrame_modifyPhysicalSlots _ _ _
    · split
      · exact storageWordsFrame_writeTransientTargets _ _ _
      · exact storageWordsFrame_writeUintSlots _ _ _
  · exact storageWordsFrame_writeUintSlots _ _ _

theorem storageWordsFrame_writeStorageWordFieldSlots
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value : Nat) :
    StorageWordsFrame world
      (writeStorageWordFieldSlots fields fieldName world slots wordOffset value) := by
  unfold writeStorageWordFieldSlots
  split
  · exact storageWordsFrame_writeTransientTargets _ _ _
  · exact storageWordsFrame_writeStorageWordSlots _ _ _ _

theorem storageWordsFrame_writeAddressFieldSlots (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    StorageWordsFrame world (writeAddressFieldSlots fields fieldName world slots value) := by
  unfold writeAddressFieldSlots
  split
  · exact storageWordsFrame_writeTransientTargets _ _ _
  · exact storageWordsFrame_writeAddressSlots _ _ _

theorem storageWordsFrame_writeMappingTargets (fields : List Compiler.CompilationModel.Field)
    (fieldName : String) (world : Verity.ContractState) (targets : List Nat) (value : Nat) :
    StorageWordsFrame world (writeMappingTargets fields fieldName world targets value) := by
  unfold writeMappingTargets
  split
  · exact storageWordsFrame_writeTransientTargets _ _ _
  · exact storageWordsFrame_writePhysicalSlots _ _ _

/-! ## `@[simp]` projection lenses

Each lens reads a framed field through a writer without unfolding it. -/

section ProjectionLenses

variable (fields : List Compiler.CompilationModel.Field) (fieldName : String)
  (world : Verity.ContractState) (slots : List Nat) (wordOffset value : Nat)

@[simp] theorem storageArray_writeUintSlots :
    (writeUintSlots world slots value).storageArray = world.storageArray :=
  (storageWordsFrame_writeUintSlots world slots value).storageArray
@[simp] theorem memory_writeUintSlots :
    (writeUintSlots world slots value).memory = world.memory :=
  (storageWordsFrame_writeUintSlots world slots value).memory
@[simp] theorem byteMemory_writeUintSlots :
    (writeUintSlots world slots value).byteMemory = world.byteMemory :=
  (storageWordsFrame_writeUintSlots world slots value).byteMemory
@[simp] theorem returndata_writeUintSlots :
    (writeUintSlots world slots value).returndata = world.returndata :=
  (storageWordsFrame_writeUintSlots world slots value).returndata
@[simp] theorem events_writeUintSlots :
    (writeUintSlots world slots value).events = world.events :=
  (storageWordsFrame_writeUintSlots world slots value).events
@[simp] theorem knownAddresses_writeUintSlots :
    (writeUintSlots world slots value).knownAddresses = world.knownAddresses :=
  (storageWordsFrame_writeUintSlots world slots value).knownAddresses

@[simp] theorem storageArray_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).storageArray = world.storageArray :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).storageArray
@[simp] theorem memory_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).memory = world.memory :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).memory
@[simp] theorem byteMemory_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).byteMemory = world.byteMemory :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).byteMemory
@[simp] theorem returndata_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).returndata = world.returndata :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).returndata
@[simp] theorem events_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).events = world.events :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).events
@[simp] theorem knownAddresses_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).knownAddresses =
      world.knownAddresses :=
  (storageWordsFrame_writeStorageWordSlots world slots wordOffset value).knownAddresses

@[simp] theorem storageArray_writeAddressSlots :
    (writeAddressSlots world slots value).storageArray = world.storageArray :=
  (storageWordsFrame_writeAddressSlots world slots value).storageArray
@[simp] theorem memory_writeAddressSlots :
    (writeAddressSlots world slots value).memory = world.memory :=
  (storageWordsFrame_writeAddressSlots world slots value).memory
@[simp] theorem byteMemory_writeAddressSlots :
    (writeAddressSlots world slots value).byteMemory = world.byteMemory :=
  (storageWordsFrame_writeAddressSlots world slots value).byteMemory
@[simp] theorem returndata_writeAddressSlots :
    (writeAddressSlots world slots value).returndata = world.returndata :=
  (storageWordsFrame_writeAddressSlots world slots value).returndata
@[simp] theorem events_writeAddressSlots :
    (writeAddressSlots world slots value).events = world.events :=
  (storageWordsFrame_writeAddressSlots world slots value).events
@[simp] theorem knownAddresses_writeAddressSlots :
    (writeAddressSlots world slots value).knownAddresses = world.knownAddresses :=
  (storageWordsFrame_writeAddressSlots world slots value).knownAddresses

@[simp] theorem storageArray_writeTransientTargets :
    (writeTransientTargets world slots value).storageArray = world.storageArray :=
  (storageWordsFrame_writeTransientTargets world slots value).storageArray
@[simp] theorem memory_writeTransientTargets :
    (writeTransientTargets world slots value).memory = world.memory :=
  (storageWordsFrame_writeTransientTargets world slots value).memory
@[simp] theorem byteMemory_writeTransientTargets :
    (writeTransientTargets world slots value).byteMemory = world.byteMemory :=
  (storageWordsFrame_writeTransientTargets world slots value).byteMemory
@[simp] theorem returndata_writeTransientTargets :
    (writeTransientTargets world slots value).returndata = world.returndata :=
  (storageWordsFrame_writeTransientTargets world slots value).returndata
@[simp] theorem events_writeTransientTargets :
    (writeTransientTargets world slots value).events = world.events :=
  (storageWordsFrame_writeTransientTargets world slots value).events
@[simp] theorem knownAddresses_writeTransientTargets :
    (writeTransientTargets world slots value).knownAddresses = world.knownAddresses :=
  (storageWordsFrame_writeTransientTargets world slots value).knownAddresses

@[simp] theorem storageArray_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).storageArray =
      world.storageArray :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).storageArray
@[simp] theorem memory_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).memory = world.memory :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).memory
@[simp] theorem byteMemory_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).byteMemory = world.byteMemory :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).byteMemory
@[simp] theorem returndata_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).returndata = world.returndata :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).returndata
@[simp] theorem events_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).events = world.events :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).events
@[simp] theorem knownAddresses_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).knownAddresses =
      world.knownAddresses :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).knownAddresses
@[simp] theorem calldata_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).calldata = world.calldata :=
  (storageWordsFrame_writeUintFieldSlots fields fieldName world slots value).calldata

@[simp] theorem storageArray_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).storageArray =
      world.storageArray :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).storageArray
@[simp] theorem memory_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).memory = world.memory :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).memory
@[simp] theorem byteMemory_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).byteMemory =
      world.byteMemory :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).byteMemory
@[simp] theorem returndata_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).returndata =
      world.returndata :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).returndata
@[simp] theorem events_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).events = world.events :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).events
@[simp] theorem knownAddresses_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).knownAddresses =
      world.knownAddresses :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).knownAddresses
@[simp] theorem calldata_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).calldata = world.calldata :=
  (storageWordsFrame_writeAddressFieldSlots fields fieldName world slots value).calldata

@[simp] theorem storageArray_writeStorageWordFieldSlots :
    (writeStorageWordFieldSlots fields fieldName world slots wordOffset value).storageArray =
      world.storageArray :=
  (storageWordsFrame_writeStorageWordFieldSlots fields fieldName world slots wordOffset
    value).storageArray
@[simp] theorem memory_writeStorageWordFieldSlots :
    (writeStorageWordFieldSlots fields fieldName world slots wordOffset value).memory =
      world.memory :=
  (storageWordsFrame_writeStorageWordFieldSlots fields fieldName world slots wordOffset
    value).memory
@[simp] theorem events_writeStorageWordFieldSlots :
    (writeStorageWordFieldSlots fields fieldName world slots wordOffset value).events =
      world.events :=
  (storageWordsFrame_writeStorageWordFieldSlots fields fieldName world slots wordOffset
    value).events

@[simp] theorem storageArray_writeMappingTargets :
    (writeMappingTargets fields fieldName world slots value).storageArray =
      world.storageArray :=
  (storageWordsFrame_writeMappingTargets fields fieldName world slots value).storageArray
@[simp] theorem memory_writeMappingTargets :
    (writeMappingTargets fields fieldName world slots value).memory = world.memory :=
  (storageWordsFrame_writeMappingTargets fields fieldName world slots value).memory
@[simp] theorem events_writeMappingTargets :
    (writeMappingTargets fields fieldName world slots value).events = world.events :=
  (storageWordsFrame_writeMappingTargets fields fieldName world slots value).events

end ProjectionLenses

/-! ## Storage-channel lenses

Persistent (`storage`), transient (`transientStorage`), and address
(`storageAddr`) views live under disjoint `StorageKey` constructors, so a writer
for one channel leaves the others untouched. -/

section ChannelLenses

variable (fields : List Compiler.CompilationModel.Field) (fieldName : String)
  (world : Verity.ContractState) (slots : List Nat) (wordOffset value : Nat)

@[simp] theorem transientStorage_writeUintSlots :
    (writeUintSlots world slots value).transientStorage = world.transientStorage := by
  simp only [writeUintSlots, Verity.ContractState.transientStorage_writePhysicalSlots]

@[simp] theorem storageAddr_writeUintSlots :
    (writeUintSlots world slots value).storageAddr = world.storageAddr := by
  simp only [writeUintSlots, Verity.ContractState.storageAddr_writePhysicalSlots]

@[simp] theorem transientStorage_writeStorageWordSlots :
    (writeStorageWordSlots world slots wordOffset value).transientStorage =
      world.transientStorage := by
  simp only [writeStorageWordSlots, Verity.ContractState.transientStorage_writeAddrSlots,
    Verity.ContractState.transientStorage_writePhysicalSlots]

@[simp] theorem storage_writeAddressSlots :
    (writeAddressSlots world slots value).storage = world.storage := by
  simp only [writeAddressSlots, Verity.ContractState.storage_writeAddrSlots]

@[simp] theorem transientStorage_writeAddressSlots :
    (writeAddressSlots world slots value).transientStorage = world.transientStorage := by
  simp only [writeAddressSlots, Verity.ContractState.transientStorage_writeAddrSlots]

@[simp] theorem storage_writeTransientTargets :
    (writeTransientTargets world slots value).storage = world.storage := by
  simp only [writeTransientTargets, Verity.ContractState.storage_writeTransientSlots]

@[simp] theorem storageAddr_writeTransientTargets :
    (writeTransientTargets world slots value).storageAddr = world.storageAddr := by
  simp only [writeTransientTargets, Verity.ContractState.storageAddr_writeTransientSlots]

@[simp] theorem storageAddr_writeUintFieldSlots :
    (writeUintFieldSlots fields fieldName world slots value).storageAddr =
      world.storageAddr := by
  unfold writeUintFieldSlots
  split
  · split
    · split
      · exact Verity.ContractState.storageAddr_modifyTransientSlots _ _ _
      · exact Verity.ContractState.storageAddr_modifyPhysicalSlots _ _ _
    · split
      · exact storageAddr_writeTransientTargets _ _ _
      · exact storageAddr_writeUintSlots _ _ _
  · exact storageAddr_writeUintSlots _ _ _

@[simp] theorem storage_writeAddressFieldSlots :
    (writeAddressFieldSlots fields fieldName world slots value).storage = world.storage := by
  unfold writeAddressFieldSlots
  split
  · exact storage_writeTransientTargets _ _ _
  · exact storage_writeAddressSlots _ _ _

end ChannelLenses

end Compiler.Proofs.StateLenses
