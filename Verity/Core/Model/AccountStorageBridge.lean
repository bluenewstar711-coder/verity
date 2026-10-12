import Verity.Core.Model.Create2Opcode

/-! Exact flat persistent self-storage/account relation. Imported mappings and
packed fields already use flat, word-normalized Solidity slots. Legacy shadow
keys and transient storage are not falsely collapsed into persistent storage.
Canonical flat persistent writes synchronize account storage without altering
code, balance or transient/legacy shadow channels. -/
namespace Compiler.CompilationModel.AccountStorageBridge

open Verity.Core

def SelfCoherent (world : Verity.ContractState) : Prop :=
  ∀ slot, world.storageWords (.slot slot) = (world.accountWorld world.thisAddress).storageAt slot

/-- Commit a physical persistent self slot through both representations. -/
def writeSelfSlot (world : Verity.ContractState) (slot value : Uint256) : Verity.ContractState :=
  world.writePhysicalSlot slot.val value

theorem writeSelfSlot_account_same (world : Verity.ContractState) (slot value : Uint256) :
    ((writeSelfSlot world slot value).accountWorld world.thisAddress).storageAt slot.val = value := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot, AccountWorld.write]

theorem writeSelfSlot_account_other (world : Verity.ContractState) (slot value : Uint256)
    (address : Address) (different : address ≠ world.thisAddress) :
    (writeSelfSlot world slot value).accountWorld address = world.accountWorld address := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot, AccountWorld.write, different]

theorem writeSelfSlot_word_same (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).storageWords (.slot slot.val) = value := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot]

theorem writeSelfSlot_preserves_coherent (world : Verity.ContractState) (slot value : Uint256)
    (coherent : SelfCoherent world) : SelfCoherent (writeSelfSlot world slot value) := by
  intro query
  by_cases same : query = slot.val
  · subst query
    simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot,
          AccountWorld.write]
  · simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot,
          AccountWorld.write, AccountState.storageAt_writeStorage, same, coherent query]

theorem writePhysicalSlots_preserves_coherent (world : Verity.ContractState) (targets : List Nat)
    (value : Uint256) (coherent : SelfCoherent world) :
    SelfCoherent (world.writePhysicalSlots targets value) := by
  intro query
  simp [Verity.ContractState.writePhysicalSlots, AccountWorld.write,
        AccountState.storageAt_writeStorageValues, coherent query]

theorem modifyPhysicalSlots_preserves_coherent (world : Verity.ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) (coherent : SelfCoherent world) :
    SelfCoherent (world.modifyPhysicalSlots targets f) := by
  intro query
  simp [Verity.ContractState.modifyPhysicalSlots, AccountWorld.write,
        AccountState.storageAt_writeStorageValues, coherent query]

theorem writeSelfSlot_balance_view_frame (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).selfBalance = world.selfBalance := rfl

theorem writeSelfSlot_code_view_frame (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).codeSize = world.codeSize := rfl

theorem commitRuntime_preserves_coherent (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List DenoteMemory.Byte) (coherent : SelfCoherent world)
    (self : creator = world.thisAddress) (other : target ≠ world.thisAddress) :
    SelfCoherent (DenoteCreate2.commitRuntime world creator target value runtime) := by
  intro query
  subst creator
  simpa [DenoteCreate2.commitRuntime, Verity.ContractState.writeAccount,
         AccountWorld.write, Ne.symm other, AccountState.storageAt] using coherent query

/-- Account metadata updates preserve the storage relation when the replacement
account has the same storage as the original self account. -/
theorem writeAccount_preserves_coherent (world : Verity.ContractState)
    (address : Address) (account : AccountState) (coherent : SelfCoherent world)
    (storage : address = world.thisAddress →
      ∀ slot, account.storageAt slot = (world.accountWorld world.thisAddress).storageAt slot) :
    SelfCoherent (world.writeAccount address account) := by
  intro slot
  by_cases same : address = world.thisAddress
  · subst address
    simpa [Verity.ContractState.writeAccount, AccountWorld.write, storage rfl slot]
      using coherent slot
  · simpa [Verity.ContractState.writeAccount, AccountWorld.write, Ne.symm same]
      using coherent slot

/-- A nonce-incremented creator cannot also be a non-colliding target. This
uses Osaka's actual collision rule, with no assumption on hash injectivity. -/
theorem incremented_creator_collides (world : Verity.ContractState) (creator : Address)
    (bound : (world.accountWorld creator).nonce.val + 1 < 2^64) :
    ((world.writeAccount creator
      { world.accountWorld creator with nonce := ⟨(world.accountWorld creator).nonce.val + 1, bound⟩ }).accountWorld creator).collidesOsaka = true := by
  simp [AccountState.collidesOsaka]

/-- Every supported concrete creation outcome preserves the self-storage
relation, including nonce-only failure transitions and successful creation.
Unsupported initcode remains an error, not an approximated transition. -/
theorem denoteCreate2_preserves_coherent (hash : DenoteCreate2.ByteHash)
    (world : Verity.ContractState) (context : DenoteCreate2.Context)
    (salt : Uint256) (code : List DenoteMemory.Byte) (result : DenoteCreate2.Result)
    (coherent : SelfCoherent world) (self : context.creator = world.thisAddress)
    (executed : DenoteCreate2.denoteCreate2 hash world context salt code = .ok result) :
    SelfCoherent result.world := by
  have nonceCoherent : ∀ (bound : (world.accountWorld context.creator).nonce.val + 1 < 2^64),
      SelfCoherent (world.writeAccount context.creator
        { world.accountWorld context.creator with nonce := ⟨(world.accountWorld context.creator).nonce.val + 1, bound⟩ }) := by
    intro bound
    apply writeAccount_preserves_coherent _ _ _ coherent
    intro same slot
    simp [AccountState.storageAt, same]
  by_cases hs : context.isStatic = true
  · simp [DenoteCreate2.denoteCreate2, hs] at executed
    cases executed
    exact coherent
  by_cases hsize : code.length > 49152
  · simp [DenoteCreate2.denoteCreate2, hs, hsize] at executed
    cases executed
    exact coherent
  by_cases hdepth : context.depth ≥ 1024
  · simp [DenoteCreate2.denoteCreate2, hs, hsize, hdepth] at executed
    cases executed
    exact coherent
  by_cases hbalance : context.value > (world.accountWorld context.creator).balance
  · simp [DenoteCreate2.denoteCreate2, hs, hsize, hdepth, hbalance] at executed
    cases executed
    exact coherent
  by_cases bound : (world.accountWorld context.creator).nonce.val + 1 < 2^64
  · let incremented := world.writeAccount context.creator
      { world.accountWorld context.creator with nonce := ⟨(world.accountWorld context.creator).nonce.val + 1, bound⟩ }
    have incrementedCoherent : SelfCoherent incremented := nonceCoherent bound
    let target := DenoteCreate2.derivedAddress hash context.creator salt code
    by_cases collision : (incremented.accountWorld target).collidesOsaka = true
    · dsimp only [incremented, target] at collision
      simp [DenoteCreate2.denoteCreate2, hs, hsize, hdepth, hbalance, bound, collision] at executed
      cases executed
      exact incrementedCoherent
    dsimp only [incremented, target] at collision
    have targetOther : target ≠ world.thisAddress := by
      intro same
      have creatorSame : target = context.creator := same.trans self.symm
      have actualCollision := incremented_creator_collides world context.creator bound
      apply collision
      change (incremented.accountWorld target).collidesOsaka = true
      rw [creatorSame]
      exact actualCollision
    have execution := executed
    simp only [DenoteCreate2.denoteCreate2, if_neg hs, if_neg hsize, if_neg hdepth,
      if_neg hbalance, dif_pos bound, if_neg collision, pure_bind] at execution
    cases costEq : DenoteCreate2.templateCost code with
    | none => simp [costEq] at execution
    | some cost =>
      simp only [costEq] at execution
      by_cases insufficient : context.childGas < cost
      · simp [insufficient] at execution
        cases execution
        exact incrementedCoherent
      simp only [if_neg insufficient] at execution
      cases runEq : InitCodeExecution.run 9 code {} with
      | running machine => simp [runEq] at execution
      | failed error =>
        cases error <;> simp [runEq] at execution
        all_goals cases execution; exact incrementedCoherent
      | returned runtime =>
        simp only [runEq] at execution
        by_cases tooLarge : runtime.length > 24576
        · simp [tooLarge] at execution
          cases execution
          exact incrementedCoherent
        by_cases forbidden : (runtime.head?).map (·.val) == some 0xef
        · simp [tooLarge, forbidden] at execution
          cases execution
          exact incrementedCoherent
        by_cases deposit : context.childGas < cost + 200 * runtime.length
        · simp [tooLarge, forbidden, deposit] at execution
          cases execution
          exact incrementedCoherent
        simp [tooLarge, forbidden, deposit] at execution
        cases execution
        exact commitRuntime_preserves_coherent incremented context.creator target context.value runtime
          incrementedCoherent self targetOther
  · simp [DenoteCreate2.denoteCreate2, hs, hsize, hdepth, hbalance, bound] at executed
    cases executed
    exact coherent

/-- The composed opcode preserves coherence too: parent gas failures leave
storage intact, creation preserves it, and clearing returndata cannot affect it. -/
theorem create2Opcode_preserves_coherent (hash : DenoteCreate2.ByteHash)
    (world : Verity.ContractState) (memory : DenoteMemory.Memory)
    (context : Create2Opcode.Context) (salt offset size : Uint256)
    (result : Create2Opcode.Result) (coherent : SelfCoherent world)
    (self : context.creator = world.thisAddress)
    (executed : Create2Opcode.execute hash world memory context salt offset size = .ok result) :
    SelfCoherent result.world := by
  by_cases hs : context.isStatic = true
  · simp [Create2Opcode.execute, hs] at executed
    cases executed
    exact coherent
  by_cases oversized : size.val > 49152
  · simp [Create2Opcode.execute, hs, oversized] at executed
    cases executed
    exact coherent
  by_cases aligned : memory.size % 32 = 0
  · have execution := executed
    simp only [Create2Opcode.execute, if_neg hs, if_neg oversized,
      if_pos aligned, pure_bind] at execution
    cases chargeEq : Create2ParentGas.charge context.gas (memory.size / 32) offset.val size.val with
    | outOfGas =>
      simp [chargeEq] at execution
      cases execution
      exact coherent
    | charged charged =>
      let code := List.ofFn fun index : Fin size.val => memory.readByte (offset.val + index.val)
      let childContext : DenoteCreate2.Context :=
        { creator := context.creator, value := context.value, childGas := charged.childGas,
          depth := context.depth }
      cases childEq : DenoteCreate2.denoteCreate2 hash world childContext salt code with
      | error message =>
        dsimp only [childContext, code] at childEq
        simp [chargeEq, childEq, Bind.bind, Except.bind] at execution
      | ok created =>
        dsimp only [childContext, code] at childEq
        have childCoherent := denoteCreate2_preserves_coherent hash world childContext salt code created
          coherent self childEq
        cases finishEq : Create2ParentGas.finish charged created.childGasLeft with
        | error message =>
          simp [chargeEq, childEq, finishEq, Bind.bind, Except.bind] at execution
        | ok gasLeft =>
          simp [chargeEq, childEq, finishEq, Bind.bind, Except.bind] at execution
          cases execution
          exact childCoherent
  · simp [Create2Opcode.execute, hs, oversized, aligned, Bind.bind, Except.bind,
      Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at executed

end Compiler.CompilationModel.AccountStorageBridge
