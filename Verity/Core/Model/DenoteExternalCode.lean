import Verity.Core

/-!
Exact external-code observations over the account world. `EXTCODESIZE` and
`EXTCODECOPY` read the runtime code recorded in `ContractState.accountWorld`;
an address without code observes the empty byte string. `EXTCODECOPY` reads
past the end of the code as zero bytes and always yields exactly `size` bytes.

An SSTORE2-style data pointer stores its payload as runtime code behind a single
leading byte (`STOP`, so the account can never be executed meaningfully). A
pointer without code holds no payload; this is distinct from an empty payload.
No Solidity construct is admitted by this module.
-/
namespace Compiler.CompilationModel.DenoteExternalCode

/-- Runtime code of `target`, as bytes. -/
def accountCode (world : Verity.ContractState) (target : Verity.Address) : List UInt8 :=
  (world.accountWorld target).code.map fun byte => UInt8.ofNat byte.val

/-- EVM `EXTCODESIZE`. -/
def extCodeSize (world : Verity.ContractState) (target : Verity.Address) : Nat :=
  (accountCode world target).length

/-- EVM `EXTCODECOPY` source bytes: `size` bytes starting at `offset`, with bytes
beyond the end of the code read as zero. -/
def extCodeSlice (world : Verity.ContractState) (target : Verity.Address)
    (offset size : Nat) : List UInt8 :=
  (List.range size).map fun index => (accountCode world target).getD (offset + index) 0

/-- Payload of an SSTORE2-style data pointer: the runtime code after its single
leading byte, or `none` when the pointer has no code. -/
def sstore2Payload? (world : Verity.ContractState) (pointer : Verity.Address) :
    Option (List UInt8) :=
  if extCodeSize world pointer = 0 then none else some ((accountCode world pointer).drop 1)

@[simp] theorem length_accountCode (world : Verity.ContractState) (target : Verity.Address) :
    (accountCode world target).length = (world.accountWorld target).code.length := by
  simp [accountCode]

theorem accountCode_eq_nil_iff (world : Verity.ContractState) (target : Verity.Address) :
    accountCode world target = [] ↔ (world.accountWorld target).code = [] := by
  simp [accountCode]

@[simp] theorem extCodeSize_eq (world : Verity.ContractState) (target : Verity.Address) :
    extCodeSize world target = (world.accountWorld target).code.length := by
  simp [extCodeSize]

theorem extCodeSize_eq_zero_iff (world : Verity.ContractState) (target : Verity.Address) :
    extCodeSize world target = 0 ↔ accountCode world target = [] := by
  simp only [extCodeSize, List.length_eq_zero_iff]

@[simp] theorem extCodeSlice_length (world : Verity.ContractState) (target : Verity.Address)
    (offset size : Nat) : (extCodeSlice world target offset size).length = size := by
  simp [extCodeSlice]

@[simp] theorem extCodeSlice_zero (world : Verity.ContractState) (target : Verity.Address)
    (offset : Nat) : extCodeSlice world target offset 0 = [] := rfl

theorem getElem_extCodeSlice (world : Verity.ContractState) (target : Verity.Address)
    (offset size index : Nat) (hindex : index < (extCodeSlice world target offset size).length) :
    (extCodeSlice world target offset size)[index] =
      (accountCode world target).getD (offset + index) 0 := by
  simp [extCodeSlice]

/-- A slice lying entirely within the code is the plain sublist. -/
theorem extCodeSlice_of_le (world : Verity.ContractState) (target : Verity.Address)
    (offset size : Nat) (hbound : offset + size ≤ extCodeSize world target) :
    extCodeSlice world target offset size =
      ((accountCode world target).drop offset).take size := by
  apply List.ext_getElem
  · simp only [extCodeSize] at hbound
    simp only [extCodeSlice_length, List.length_take, List.length_drop]
    omega
  · intro index hleft _
    simp only [extCodeSlice_length] at hleft
    simp only [extCodeSize] at hbound
    have hlt : offset + index < (accountCode world target).length := by omega
    simp [getElem_extCodeSlice, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

/-- Reading past the end of the code yields only zero bytes. -/
theorem extCodeSlice_of_ge (world : Verity.ContractState) (target : Verity.Address)
    (offset size : Nat) (hbound : extCodeSize world target ≤ offset) :
    extCodeSlice world target offset size = List.replicate size 0 := by
  apply List.ext_getElem
  · simp
  · intro index _ _
    simp only [extCodeSize] at hbound
    have hge : (accountCode world target).length ≤ offset + index := by omega
    simp [getElem_extCodeSlice, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

theorem sstore2Payload?_eq_none_iff (world : Verity.ContractState) (pointer : Verity.Address) :
    sstore2Payload? world pointer = none ↔ extCodeSize world pointer = 0 := by
  unfold sstore2Payload?
  split <;> simp_all

theorem sstore2Payload?_of_extCodeSize_ne_zero (world : Verity.ContractState)
    (pointer : Verity.Address) (hsize : extCodeSize world pointer ≠ 0) :
    sstore2Payload? world pointer = some ((accountCode world pointer).drop 1) := by
  simp only [sstore2Payload?, if_neg hsize]

theorem sstore2Payload?_of_accountCode_cons (world : Verity.ContractState)
    (pointer : Verity.Address) (leading : UInt8) (payload : List UInt8)
    (hcode : accountCode world pointer = leading :: payload) :
    sstore2Payload? world pointer = some payload := by
  have hsize : extCodeSize world pointer ≠ 0 := by simp [extCodeSize, hcode]
  simp [sstore2Payload?_of_extCodeSize_ne_zero world pointer hsize, hcode]

/-- An SSTORE2 data pointer (`STOP` followed by the payload) reads back its
payload exactly, including an empty payload. -/
theorem sstore2Payload?_of_sstore2_layout (world : Verity.ContractState)
    (pointer : Verity.Address) (payload : List UInt8)
    (hcode : accountCode world pointer = 0x00 :: payload) :
    sstore2Payload? world pointer = some payload :=
  sstore2Payload?_of_accountCode_cons world pointer 0x00 payload hcode

end Compiler.CompilationModel.DenoteExternalCode
