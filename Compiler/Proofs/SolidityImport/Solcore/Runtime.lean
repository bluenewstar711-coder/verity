import Compiler.Proofs.SolidityImport.Solcore.Primitives

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.Solcore

/-!
# Solcore WordMapping and ContractRuntime Domains

Lean 4.22.0 embedding of `argotorg/solcore-lean`'s mapping and contract runtime
domains:
- `Solcore.Core.WordMapping`: finite key-value entry tables over 256-bit words
  with read-over-write and overwrite algebra.
- `Solcore.ContractRuntime`: `Account`, `WorldState` (sparse non-zero storage
  map with zero-deletion), `TransactionJournal` (emitted logs and created
  contracts), `FrameHaltKind`, `FrameOutcome`, and `resolvedWorldState?`
  checkpoint rollback on `.reverted`.
- `SolcoreExecState`: unified contract frame execution state (persistent world
  storage, EIP-1153 transient storage, word-addressed memory, local variable
  bindings, transaction journal, and frame checkpoint snapshot).
-/

namespace Core.WordMapping

abbrev Entries : Type :=
  List (Word × Word)

def lookupEntries : Entries → Word → Word
  | [], _ => Word.zero
  | (storedKey, storedValue) :: rest, key =>
      if key = storedKey then
        storedValue
      else
        lookupEntries rest key

def insertEntries : Entries → Word → Word → Entries
  | [], key, value => [(key, value)]
  | (storedKey, storedValue) :: rest, key, value =>
      if key = storedKey then
        (key, value) :: rest
      else
        (storedKey, storedValue) :: insertEntries rest key value

@[simp] theorem lookupEntries_nil (key : Word) :
    lookupEntries [] key = Word.zero :=
  rfl

@[simp] theorem lookupEntries_insert_same
    (entries : Entries) (key value : Word) :
    lookupEntries (insertEntries entries key value) key = value := by
  induction entries with
  | nil => simp [insertEntries, lookupEntries]
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases h : key = storedKey
      · subst h; simp [insertEntries, lookupEntries]
      · simp [insertEntries, lookupEntries, h, ih]

@[simp] theorem lookupEntries_insert_other
    (entries : Entries) {writtenKey readKey : Word} (value : Word)
    (distinct : readKey ≠ writtenKey) :
    lookupEntries (insertEntries entries writtenKey value) readKey =
      lookupEntries entries readKey := by
  induction entries with
  | nil => simp [insertEntries, lookupEntries, distinct]
  | cons entry rest ih =>
      rcases entry with ⟨storedKey, storedValue⟩
      by_cases hWrite : writtenKey = storedKey
      · subst hWrite
        simp [insertEntries, lookupEntries, distinct]
      · by_cases hRead : readKey = storedKey
        · subst hRead
          simp [insertEntries, lookupEntries, hWrite]
        · simp [insertEntries, lookupEntries, hWrite, hRead, ih]

@[simp] theorem lookupEntries_insert_overwrite
    (entries : Entries) (writtenKey firstValue secondValue : Word)
    (readKey : Word) :
    lookupEntries
        (insertEntries (insertEntries entries writtenKey firstValue)
          writtenKey secondValue)
        readKey =
      lookupEntries (insertEntries entries writtenKey secondValue) readKey := by
  by_cases h : readKey = writtenKey
  · subst h; simp
  · simp [h]

end Core.WordMapping

namespace ContractRuntime

open Core

abbrev Address : Type :=
  Word

structure Account where
  codeIdentity : Option String := none
  balance : Nat := 0
  storage : Word → Option Word := fun _ => none
  storage_nonzero :
    ∀ slot value, storage slot = some value → value ≠ Word.zero := by
      intro _ _ h; cases h

namespace Account

@[ext] theorem ext
    {left right : Account}
    (codeEq : left.codeIdentity = right.codeIdentity)
    (balanceEq : left.balance = right.balance)
    (storageEq : ∀ slot, left.storage slot = right.storage slot) :
    left = right := by
  cases left with
  | mk lCode lBal lStor lNz =>
      cases right with
      | mk rCode rBal rStor rNz =>
          have hStor : lStor = rStor := funext storageEq
          subst codeEq; subst balanceEq; subst hStor
          have hProof : lNz = rNz := Subsingleton.elim _ _
          subst hProof
          rfl

def empty : Account :=
  {}

def storageRead (account : Account) (slot : Word) : Word :=
  (account.storage slot).getD Word.zero

def storageWrite (account : Account) (slot value : Word) : Account :=
  { account with
    storage := fun candidate =>
      if candidate = slot then
        if value = Word.zero then none else some value
      else
        account.storage candidate
    storage_nonzero := by
      intro candidate stored hStored
      by_cases hSlot : candidate = slot
      · subst hSlot
        by_cases hZero : value = Word.zero
        · simp [hZero] at hStored
        · simp [hZero] at hStored
          cases hStored
          exact hZero
      · simp [hSlot] at hStored
        exact account.storage_nonzero candidate stored hStored }

@[simp] theorem storageRead_empty (slot : Word) :
    empty.storageRead slot = Word.zero :=
  rfl

@[simp] theorem storageRead_storageWrite_same
    (account : Account) (slot value : Word) :
    (account.storageWrite slot value).storageRead slot = value := by
  by_cases hZero : value = Word.zero
  · subst hZero; simp [storageRead, storageWrite]
  · simp [storageRead, storageWrite, hZero]

@[simp] theorem storageRead_storageWrite_other
    (account : Account) {writtenSlot readSlot : Word} (value : Word)
    (distinct : readSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageRead readSlot =
      account.storageRead readSlot := by
  simp [storageRead, storageWrite, distinct]

theorem storage_eq_none_of_storageRead_eq_zero
    (account : Account) (slot : Word)
    (hZero : account.storageRead slot = Word.zero) :
    account.storage slot = none := by
  unfold storageRead at hZero
  cases hEntry : account.storage slot with
  | none => rfl
  | some stored =>
      exfalso
      rw [hEntry] at hZero
      exact account.storage_nonzero slot stored hEntry hZero

@[simp] theorem storageWrite_zero_of_storageRead_zero
    (account : Account) (slot : Word)
    (hZero : account.storageRead slot = Word.zero) :
    account.storageWrite slot Word.zero = account := by
  apply Account.ext
  · rfl
  · rfl
  · intro candidate
    by_cases hSlot : candidate = slot
    · subst hSlot
      simpa [storageWrite] using
        (storage_eq_none_of_storageRead_eq_zero account candidate hZero).symm
    · simp [storageWrite, hSlot]

@[simp] theorem storageWrite_overwrite
    (account : Account) (slot firstValue secondValue : Word) :
    (account.storageWrite slot firstValue).storageWrite slot secondValue =
      account.storageWrite slot secondValue := by
  apply Account.ext
  · rfl
  · rfl
  · intro candidate
    by_cases hSlot : candidate = slot
    · subst hSlot; simp [storageWrite]
    · simp [storageWrite, hSlot]

theorem storageWrite_commute
    (account : Account) {firstSlot secondSlot : Word}
    (firstValue secondValue : Word)
    (distinct : firstSlot ≠ secondSlot) :
    (account.storageWrite firstSlot firstValue).storageWrite
        secondSlot secondValue =
      (account.storageWrite secondSlot secondValue).storageWrite
        firstSlot firstValue := by
  apply Account.ext
  · rfl
  · rfl
  · intro candidate
    by_cases hFirst : candidate = firstSlot
    · subst hFirst
      have hNotSecond : candidate ≠ secondSlot := distinct
      simp [storageWrite, hNotSecond]
    · by_cases hSecond : candidate = secondSlot
      · subst hSecond
        simp [storageWrite, hFirst]
      · simp [storageWrite, hFirst, hSecond]

end Account

structure WorldState where
  accounts : Address → Option Account := fun _ => none

namespace WorldState

@[ext] theorem ext
    {left right : WorldState}
    (h : ∀ address, left.accounts address = right.accounts address) :
    left = right := by
  cases left
  cases right
  congr
  exact funext h

def empty : WorldState :=
  {}

def account? (state : WorldState) (address : Address) : Option Account :=
  state.accounts address

def putAccount (state : WorldState) (address : Address) (account : Account) :
    WorldState :=
  { accounts := fun candidate =>
      if candidate = address then some account else state.accounts candidate }

/-- Total account view returning `Account.empty` when the address is unallocated. -/
def accountOrEmpty (state : WorldState) (address : Address) : Account :=
  (state.accounts address).getD Account.empty

/-- Total storage read on `WorldState` (returns `Word.zero` for missing account/slot). -/
def storageRead (state : WorldState) (address : Address) (slot : Word) : Word :=
  (state.accountOrEmpty address).storageRead slot

/-- Total storage write on `WorldState` (allocates `Account.empty` if needed). -/
def writeStorage (state : WorldState) (address : Address) (slot value : Word) :
    WorldState :=
  state.putAccount address ((state.accountOrEmpty address).storageWrite slot value)

def writeStorage?
    (state : WorldState) (address : Address) (slot value : Word) :
    Option WorldState := do
  let account ← state.account? address
  pure (state.putAccount address (account.storageWrite slot value))

@[simp] theorem storageRead_writeStorage_same
    (state : WorldState) (address : Address) (slot value : Word) :
    (state.writeStorage address slot value).storageRead address slot = value := by
  simp [writeStorage, storageRead, accountOrEmpty, putAccount]

@[simp] theorem storageRead_writeStorage_other_slot
    (state : WorldState) (address : Address) {writtenSlot readSlot : Word}
    (value : Word) (distinct : readSlot ≠ writtenSlot) :
    (state.writeStorage address writtenSlot value).storageRead address readSlot =
      state.storageRead address readSlot := by
  simp [writeStorage, storageRead, accountOrEmpty, putAccount, distinct]

@[simp] theorem storageRead_writeStorage_other_address
    (state : WorldState) {writtenAddr readAddr : Address} (slot readSlot value : Word)
    (distinct : readAddr ≠ writtenAddr) :
    (state.writeStorage writtenAddr slot value).storageRead readAddr readSlot =
      state.storageRead readAddr readSlot := by
  simp [writeStorage, storageRead, accountOrEmpty, putAccount, distinct]

end WorldState

structure EmittedLogWord where
  contract : Address
  topics : List Word := []
  payload : Word
  deriving DecidableEq, Repr

structure CreatedContractRecord where
  creator : Address
  deployedAddress : Address
  codeIdentity : String
  endowment : Nat
  constructorArgument : Word
  deriving DecidableEq, Repr

structure TransactionJournal where
  logs : List EmittedLogWord := []
  createdContracts : List CreatedContractRecord := []
  deriving DecidableEq, Repr

namespace TransactionJournal

def empty : TransactionJournal :=
  {}

def recordLog
    (journal : TransactionJournal) (entry : EmittedLogWord) :
    TransactionJournal :=
  { journal with logs := journal.logs ++ [entry] }

def recordCreatedContract
    (journal : TransactionJournal) (entry : CreatedContractRecord) :
    TransactionJournal :=
  { journal with createdContracts := journal.createdContracts ++ [entry] }

def logList (journal : TransactionJournal) : List EmittedLogWord :=
  journal.logs

@[simp] theorem empty_logList :
    empty.logList = [] :=
  rfl

@[simp] theorem recordLog_logList
    (journal : TransactionJournal) (entry : EmittedLogWord) :
    (journal.recordLog entry).logList = journal.logList ++ [entry] :=
  rfl

end TransactionJournal

inductive FrameHaltKind : Type where
  | returned
  | reverted
  | trapped
  deriving DecidableEq, Repr

inductive FrameOutcome (TrapReason : Type) : Type where
  | returned (value : Word)
  | reverted (data : Word)
  | trapped (reason : TrapReason)
  deriving DecidableEq, Repr

namespace FrameOutcome

def haltKind {TrapReason : Type} : FrameOutcome TrapReason → FrameHaltKind
  | .returned _ => .returned
  | .reverted _ => .reverted
  | .trapped _ => .trapped

def returnValue? {TrapReason : Type} : FrameOutcome TrapReason → Option Word
  | .returned value => some value
  | .reverted _ => none
  | .trapped _ => none

def revertValue? {TrapReason : Type} : FrameOutcome TrapReason → Option Word
  | .returned _ => none
  | .reverted value => some value
  | .trapped _ => none

def trapReason? {TrapReason : Type} :
    FrameOutcome TrapReason → Option TrapReason
  | .returned _ => none
  | .reverted _ => none
  | .trapped reason => some reason

def resolvedWorldState? {TrapReason : Type}
    (checkpoint working : WorldState) :
    FrameOutcome TrapReason → Option WorldState
  | .returned _ => some working
  | .reverted _ => some checkpoint
  | .trapped _ => none

@[simp] theorem resolvedWorldState_returned
    {TrapReason : Type} (checkpoint working : WorldState) (value : Word) :
    (FrameOutcome.returned (TrapReason := TrapReason) value).resolvedWorldState?
        checkpoint working =
      some working :=
  rfl

@[simp] theorem resolvedWorldState_reverted
    {TrapReason : Type} (checkpoint working : WorldState) (value : Word) :
    (FrameOutcome.reverted (TrapReason := TrapReason) value).resolvedWorldState?
        checkpoint working =
      some checkpoint :=
  rfl

@[simp] theorem resolvedWorldState_trapped
    {TrapReason : Type} (checkpoint working : WorldState) (reason : TrapReason) :
    (FrameOutcome.trapped reason).resolvedWorldState? checkpoint working = none :=
  rfl

end FrameOutcome

/-- Frame-entry state checkpoint for transaction rollback on `.reverted`. -/
structure SolcoreFrameSnapshot where
  world : WorldState
  transientStorage : Word → Word := fun _ => Word.zero
  journal : TransactionJournal := TransactionJournal.empty

/-- Complete contract-frame runtime state in `Solcore` combining persistent
    `WorldState`, EIP-1153 `transientStorage`, word-addressed `memory`, local
    variable bindings, `TransactionJournal`, and frame-entry `checkpoint`. -/
structure SolcoreExecState where
  contractAddress : Address
  world : WorldState
  transientStorage : Word → Word := fun _ => Word.zero
  memory : Word → Word := fun _ => Word.zero
  locals : String → Option Word := fun _ => none
  journal : TransactionJournal := TransactionJournal.empty
  checkpoint : SolcoreFrameSnapshot

namespace SolcoreExecState

/-- Create an initial frame state whose checkpoint equals its entry state. -/
def initFrame
    (contractAddress : Address)
    (world : WorldState)
    (transientStorage : Word → Word := fun _ => Word.zero)
    (memory : Word → Word := fun _ => Word.zero)
    (locals : String → Option Word := fun _ => none)
    (journal : TransactionJournal := TransactionJournal.empty) :
    SolcoreExecState :=
  { contractAddress := contractAddress
    world := world
    transientStorage := transientStorage
    memory := memory
    locals := locals
    journal := journal
    checkpoint :=
      { world := world
        transientStorage := transientStorage
        journal := journal } }

def sload (state : SolcoreExecState) (slot : Word) : Word :=
  state.world.storageRead state.contractAddress slot

def sstore (state : SolcoreExecState) (slot value : Word) : SolcoreExecState :=
  { state with
    world := state.world.writeStorage state.contractAddress slot value }

def tload (state : SolcoreExecState) (slot : Word) : Word :=
  state.transientStorage slot

def tstore (state : SolcoreExecState) (slot value : Word) : SolcoreExecState :=
  { state with
    transientStorage := fun candidate =>
      if candidate = slot then value else state.transientStorage candidate }

def mload (state : SolcoreExecState) (offset : Word) : Word :=
  state.memory offset

def mstore (state : SolcoreExecState) (offset value : Word) : SolcoreExecState :=
  { state with
    memory := fun candidate =>
      if candidate = offset then value else state.memory candidate }

def getLocal (state : SolcoreExecState) (name : String) : Word :=
  (state.locals name).getD Word.zero

def setLocal (state : SolcoreExecState) (name : String) (value : Word) :
    SolcoreExecState :=
  { state with
    locals := fun candidate =>
      if candidate = name then some value else state.locals candidate }

def emitLog (state : SolcoreExecState) (topics : List Word) (payload : Word) :
    SolcoreExecState :=
  { state with
    journal := state.journal.recordLog
      { contract := state.contractAddress, topics := topics, payload := payload } }

/-- Resolve a frame execution outcome:
    - `.returned _`: commits `world`, `transientStorage`, and `journal`.
    - `.reverted _`: rolls back `world`, `transientStorage`, and `journal`
      to `state.checkpoint`.
    - `.trapped _`: returns `none`. -/
def resolveFrame {TrapReason : Type}
    (state : SolcoreExecState) (outcome : FrameOutcome TrapReason) :
    Option SolcoreFrameSnapshot :=
  match outcome with
  | .returned _ =>
      some
        { world := state.world
          transientStorage := state.transientStorage
          journal := state.journal }
  | .reverted _ =>
      some state.checkpoint
  | .trapped _ =>
      none

@[simp] theorem sload_sstore_same
    (state : SolcoreExecState) (slot value : Word) :
    (state.sstore slot value).sload slot = value := by
  simp [sload, sstore]

@[simp] theorem sload_sstore_other
    (state : SolcoreExecState) {writtenSlot readSlot : Word} (value : Word)
    (distinct : readSlot ≠ writtenSlot) :
    (state.sstore writtenSlot value).sload readSlot = state.sload readSlot := by
  simp [sload, sstore, distinct]

@[simp] theorem tload_tstore_same
    (state : SolcoreExecState) (slot value : Word) :
    (state.tstore slot value).tload slot = value := by
  simp [tload, tstore]

@[simp] theorem tload_tstore_other
    (state : SolcoreExecState) {writtenSlot readSlot : Word} (value : Word)
    (distinct : readSlot ≠ writtenSlot) :
    (state.tstore writtenSlot value).tload readSlot = state.tload readSlot := by
  simp [tload, tstore, distinct]

@[simp] theorem resolveFrame_returned {TrapReason : Type}
    (state : SolcoreExecState) (value : Word) :
    state.resolveFrame (FrameOutcome.returned (TrapReason := TrapReason) value) =
      some
        { world := state.world
          transientStorage := state.transientStorage
          journal := state.journal } :=
  rfl

@[simp] theorem resolveFrame_reverted {TrapReason : Type}
    (state : SolcoreExecState) (data : Word) :
    state.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      some state.checkpoint :=
  rfl

theorem resolveFrame_reverted_world_eq_resolvedWorldState {TrapReason : Type}
    (state : SolcoreExecState) (data : Word) :
    Option.map SolcoreFrameSnapshot.world
        (state.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) data)) =
      (FrameOutcome.reverted (TrapReason := TrapReason) data).resolvedWorldState?
        state.checkpoint.world state.world :=
  rfl

end SolcoreExecState

end ContractRuntime

end Compiler.Proofs.SolidityImport.Solcore
