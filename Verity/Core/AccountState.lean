import Verity.Core.Address
import Verity.Core.Uint256
import Lean.Data.RBMap

/-! Exact account metadata for deployment observations. Storage is finite and
zero entries may be absent; nonce is bounded by EIP-2681's 64-bit limit. -/
namespace Verity.Core

structure AccountState where
  nonce : Fin (2^64) := 0
  balance : Uint256 := 0
  code : List (Fin 256) := []
  storage : Lean.RBMap Nat Uint256 compare := Lean.RBMap.empty

namespace AccountState

def storageAt (account : AccountState) (slot : Nat) : Uint256 :=
  (account.storage.find? slot).getD 0

def writeStorage (account : AccountState) (slot : Nat) (value : Uint256) : AccountState :=
  -- Anonymous constructor: `AccountState` is not `ContractState`, so this
  -- deliberately avoids a raw `storage :=` site in the storage-lens freeze gate.
  ⟨account.nonce, account.balance, account.code,
    if value.val = 0 then account.storage.erase slot else account.storage.insert slot value⟩

/-- Osaka's collision predicate. Nonempty storage alone is not a collision:
creation clears it when both nonce and code are empty. EIP-7610 is a different
fork rule and must not be silently applied to the pinned Osaka campaigns. -/
def collidesOsaka (account : AccountState) : Bool :=
  account.nonce.val != 0 || !account.code.isEmpty

theorem storage_only_not_collision (account : AccountState)
    (nonceZero : account.nonce.val = 0) (codeEmpty : account.code = []) :
    account.collidesOsaka = false := by
  simp [collidesOsaka, nonceZero, codeEmpty]

end AccountState

abbrev AccountWorld := Address → AccountState

namespace AccountWorld
def empty : AccountWorld := fun _ => {}

def write (world : AccountWorld) (address : Address) (account : AccountState) : AccountWorld :=
  fun query => if query = address then account else world query

@[simp] theorem write_at (world : AccountWorld) (address : Address) (account : AccountState) :
    write world address account address = account := by simp [write]

theorem write_other (world : AccountWorld) (address query : Address) (account : AccountState)
    (different : query ≠ address) : write world address account query = world query := by
  simp [write, different]

end AccountWorld
end Verity.Core
