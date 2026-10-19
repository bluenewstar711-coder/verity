import Verity.Core.Uint256
import Verity.Core.Int256

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.Solcore

namespace Core

/-!
# Solcore Core Syntax, Primitives, and Big-Step Evaluation

Lean 4.22.0 embedding of the core semantic domains of `argotorg/solcore-lean`:
- 256-bit EVM words (`Word := Fin (2 ^ 256)`) and canonical bijections with
  `Verity.Core.Uint256` and `Verity.Core.Int256`.
- Word primitive operations (`ModularArithmetic`, `TernaryModularArithmetic`,
  `UnsignedDivision`, `SignedDivision`, `BitwiseLogic`, `LogicalShifts`,
  `ArithmeticShift`, `SignExtension`, `DirectWordComparisons`,
  `SignedComparison`).
- Core expression AST (`Ty`, `HostFunction`, `UnaryOp`, `BinaryOp`, `TernaryOp`,
  `Expr`, `Value`) including derived boolean/word flag and short-circuit forms
  (`ShortCircuit`).
- Relational big-step operational semantics (`Evaluates`) and determinism.
-/

def wordModulus : Nat :=
  2 ^ 256

theorem wordModulus_eq_uint256_modulus :
    wordModulus = Verity.Core.UINT256_MODULUS :=
  rfl

theorem wordModulus_pos : 0 < wordModulus := by
  decide

abbrev Word : Type :=
  Fin wordModulus

namespace Word

def zero : Word :=
  ⟨0, wordModulus_pos⟩

def maximum : Word :=
  ⟨wordModulus - 1, Nat.sub_lt wordModulus_pos (by decide)⟩

def ofNat? (value : Nat) : Option Word :=
  if h : value < wordModulus then
    some ⟨value, h⟩
  else
    none

def ofNatModulo (value : Nat) : Word :=
  ⟨value % wordModulus, Nat.mod_lt _ wordModulus_pos⟩

/-- Canonical conversion from `Solcore.Core.Word` to `Verity.Core.Uint256`. -/
def toUint256 (w : Word) : Verity.Core.Uint256 :=
  ⟨w.val, w.isLt⟩

/-- Canonical conversion from `Verity.Core.Uint256` to `Solcore.Core.Word`. -/
def ofUint256 (u : Verity.Core.Uint256) : Word :=
  ⟨u.val, u.isLt⟩

/-- Canonical conversion from `Solcore.Core.Word` to `Verity.Core.Int256`. -/
def toInt256 (w : Word) : Verity.Core.Int256 :=
  Verity.Core.Int256.ofUint256 w.toUint256

/-- Canonical conversion from `Verity.Core.Int256` to `Solcore.Core.Word`. -/
def ofInt256 (i : Verity.Core.Int256) : Word :=
  ofUint256 i.toUint256

@[simp] theorem val_zero : zero.val = 0 := rfl

@[simp] theorem val_maximum : maximum.val = wordModulus - 1 := rfl

@[simp] theorem val_ofNatModulo (n : Nat) :
    (ofNatModulo n).val = n % wordModulus := rfl

@[simp] theorem ofNatModulo_val (w : Word) :
    ofNatModulo w.val = w := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

@[simp] theorem val_toUint256 (w : Word) :
    w.toUint256.val = w.val := rfl

@[simp] theorem val_ofUint256 (u : Verity.Core.Uint256) :
    (ofUint256 u).val = u.val := rfl

@[simp] theorem ofUint256_toUint256 (w : Word) :
    ofUint256 w.toUint256 = w := rfl

@[simp] theorem toUint256_ofUint256 (u : Verity.Core.Uint256) :
    (ofUint256 u).toUint256 = u := rfl

@[simp] theorem ofInt256_toInt256 (w : Word) :
    ofInt256 w.toInt256 = w := rfl

@[simp] theorem toInt256_ofInt256 (i : Verity.Core.Int256) :
    (ofInt256 i).toInt256 = i := rfl

def add (left right : Word) : Word :=
  left + right

def sub (left right : Word) : Word :=
  left - right

def mul (left right : Word) : Word :=
  left * right

def addMod (left right modulus : Word) : Word :=
  if modulus.val = 0 then
    Word.zero
  else
    Word.ofNatModulo ((left.val + right.val) % modulus.val)

def mulMod (left right modulus : Word) : Word :=
  if modulus.val = 0 then
    Word.zero
  else
    Word.ofNatModulo ((left.val * right.val) % modulus.val)

def udiv (left right : Word) : Word :=
  if right.val = 0 then
    Word.zero
  else
    left / right

def umod (left right : Word) : Word :=
  if right.val = 0 then
    Word.zero
  else
    left % right

def signedNegative (value : Word) : Bool :=
  decide (2 ^ 255 ≤ value.val)

def signedMagnitude (value : Word) : Nat :=
  if value.val < 2 ^ 255 then
    value.val
  else
    wordModulus - value.val

def ofSignedMagnitude (negative : Bool) (magnitude : Nat) : Word :=
  let normalized := magnitude % wordModulus
  if negative then
    if normalized = 0 then
      Word.zero
    else
      Word.ofNatModulo (wordModulus - normalized)
  else
    Word.ofNatModulo normalized

def signedGt (left right : Word) : Bool :=
  let leftNegative := left.signedNegative
  let rightNegative := right.signedNegative
  if leftNegative != rightNegative then
    rightNegative
  else
    decide (left > right)

def bitAnd (left right : Word) : Word :=
  left &&& right

def bitOr (left right : Word) : Word :=
  left ||| right

def bitXor (left right : Word) : Word :=
  left ^^^ right

def bitNot (value : Word) : Word :=
  Word.maximum - value

def clzAux : Nat → Nat → Nat
  | 0, _ => 0
  | remaining + 1, value =>
      if value < 2 ^ remaining then
        1 + clzAux remaining value
      else
        0

def clz (value : Word) : Word :=
  Word.ofNatModulo (clzAux 256 value.val)

def shiftLeft (value shift : Word) : Word :=
  if shift.val < 256 then
    value <<< shift
  else
    Word.zero

def shiftRight (value shift : Word) : Word :=
  if shift.val < 256 then
    value >>> shift
  else
    Word.zero

def shiftArithmeticRight (value shift : Word) : Word :=
  if shift.val < 256 then
    if value.val < 2 ^ 255 then
      Word.ofNatModulo (value.val / 2 ^ shift.val)
    else
      Word.ofNatModulo
        (wordModulus - 1 - ((wordModulus - 1 - value.val) / 2 ^ shift.val))
  else if value.val < 2 ^ 255 then
    Word.zero
  else
    Word.maximum

def byteAt (index value : Word) : Word :=
  if index.val < 32 then
    let shiftBits := (31 - index.val) * 8
    Word.ofNatModulo ((value.val / 2 ^ shiftBits) % 256)
  else
    Word.zero

def pow (base exponent : Word) : Word :=
  Word.ofNatModulo (base.val ^ exponent.val)

def signExtend (index value : Word) : Word :=
  if index.val < 32 then
    let widthBits := 8 * (index.val + 1)
    let modulus := 2 ^ widthBits
    let signBit := 2 ^ (widthBits - 1)
    let low := value.val % modulus
    if low < signBit then
      Word.ofNatModulo low
    else
      Word.ofNatModulo (wordModulus - modulus + low)
  else
    value

def sdiv (dividend divisor : Word) : Word :=
  if divisor.val = 0 then
    Word.zero
  else
    let quotientMagnitude := dividend.signedMagnitude / divisor.signedMagnitude
    let negative := dividend.signedNegative != divisor.signedNegative
    Word.ofSignedMagnitude negative quotientMagnitude

def smod (dividend divisor : Word) : Word :=
  if divisor.val = 0 then
    Word.zero
  else
    let remainderMagnitude := dividend.signedMagnitude % divisor.signedMagnitude
    Word.ofSignedMagnitude dividend.signedNegative remainderMagnitude

/-! ### ModularArithmetic interface -/

@[simp] theorem add_zero (value : Word) :
    value.add Word.zero = value := by
  change value + Word.zero = value
  apply Fin.ext
  change (value.val + 0) % wordModulus = value.val
  exact Nat.mod_eq_of_lt value.isLt

@[simp] theorem add_maximum_one :
    Word.maximum.add (Word.ofNatModulo 1) = Word.zero :=
  rfl

@[simp] theorem sub_zero (value : Word) :
    value.sub Word.zero = value := by
  change value - Word.zero = value
  apply Fin.ext
  have zeroLe : Word.zero ≤ value := Nat.zero_le value.val
  rw [Fin.sub_val_of_le zeroLe]
  simp [Word.zero]

@[simp] theorem sub_self (value : Word) :
    value.sub value = Word.zero := by
  change value - value = Word.zero
  apply Fin.ext
  rw [Fin.sub_val_of_le (Fin.le_refl value)]
  simp [Word.zero]

@[simp] theorem zero_sub_one :
    Word.zero.sub (Word.ofNatModulo 1) = Word.maximum :=
  rfl

@[simp] theorem mul_zero (value : Word) :
    value.mul Word.zero = Word.zero := by
  change value * Word.zero = Word.zero
  apply Fin.ext
  change (value.val * 0) % wordModulus = 0
  simp

@[simp] theorem mul_one (value : Word) :
    value.mul (Word.ofNatModulo 1) = value := by
  change value * Word.ofNatModulo 1 = value
  apply Fin.ext
  change (value.val * (1 % wordModulus)) % wordModulus = value.val
  have oneLt : 1 < wordModulus := by decide
  rw [Nat.mod_eq_of_lt oneLt]
  simp [Nat.mod_eq_of_lt value.isLt]

/-! ### TernaryModularArithmetic interface -/

@[simp] theorem addMod_zero (left right : Word) :
    left.addMod right Word.zero = Word.zero :=
  rfl

theorem addMod_nonzero
    (left right modulus : Word) (nonzero : modulus.val ≠ 0) :
    left.addMod right modulus =
      Word.ofNatModulo ((left.val + right.val) % modulus.val) := by
  simp [addMod, nonzero]

@[simp] theorem mulMod_zero (left right : Word) :
    left.mulMod right Word.zero = Word.zero :=
  rfl

theorem mulMod_nonzero
    (left right modulus : Word) (nonzero : modulus.val ≠ 0) :
    left.mulMod right modulus =
      Word.ofNatModulo ((left.val * right.val) % modulus.val) := by
  simp [mulMod, nonzero]

@[simp] theorem addMod_no_prewrap :
    Word.maximum.addMod (Word.ofNatModulo 1) Word.maximum =
      Word.ofNatModulo 1 :=
  rfl

@[simp] theorem mulMod_no_prewrap :
    Word.maximum.mulMod Word.maximum Word.maximum = Word.zero :=
  rfl

/-! ### UnsignedDivision interface -/

@[simp] theorem udiv_zero (left : Word) :
    left.udiv Word.zero = Word.zero :=
  rfl

@[simp] theorem umod_zero (left : Word) :
    left.umod Word.zero = Word.zero :=
  rfl

theorem udiv_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.udiv right = left / right := by
  have valueNonzero : right.val ≠ 0 := fun h => nonzero (Fin.ext h)
  simp [udiv, valueNonzero]

theorem umod_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.umod right = left % right := by
  have valueNonzero : right.val ≠ 0 := fun h => nonzero (Fin.ext h)
  simp [umod, valueNonzero]

/-! ### SignedDivision & SignedComparison interface -/

@[simp] theorem sdiv_zero (dividend : Word) :
    dividend.sdiv Word.zero = Word.zero :=
  rfl

theorem sdiv_nonzero
    (dividend divisor : Word) (nonzero : divisor.val ≠ 0) :
    dividend.sdiv divisor =
      Word.ofSignedMagnitude
        (dividend.signedNegative != divisor.signedNegative)
        (dividend.signedMagnitude / divisor.signedMagnitude) := by
  simp [sdiv, nonzero]

@[simp] theorem smod_zero (dividend : Word) :
    dividend.smod Word.zero = Word.zero :=
  rfl

theorem smod_nonzero
    (dividend divisor : Word) (nonzero : divisor.val ≠ 0) :
    dividend.smod divisor =
      Word.ofSignedMagnitude dividend.signedNegative
        (dividend.signedMagnitude % divisor.signedMagnitude) := by
  simp [smod, nonzero]

@[simp] theorem sdiv_minimum_negative_one :
    (Word.ofNatModulo (2 ^ 255)).sdiv Word.maximum =
      Word.ofNatModulo (2 ^ 255) :=
  rfl

@[simp] theorem smod_minimum_negative_one :
    (Word.ofNatModulo (2 ^ 255)).smod Word.maximum = Word.zero :=
  rfl

@[simp] theorem signedGt_self (value : Word) :
    value.signedGt value = false := by
  simp [signedGt]

theorem signedGt_both_nonnegative
    (left right : Word)
    (leftNonnegative : left.val < 2 ^ 255)
    (rightNonnegative : right.val < 2 ^ 255) :
    left.signedGt right = decide (left > right) := by
  have hL : left.signedNegative = false :=
    decide_eq_false (Nat.not_le_of_lt leftNonnegative)
  have hR : right.signedNegative = false :=
    decide_eq_false (Nat.not_le_of_lt rightNonnegative)
  simp [signedGt, hL, hR]

theorem signedGt_both_negative
    (left right : Word)
    (leftNegative : 2 ^ 255 ≤ left.val)
    (rightNegative : 2 ^ 255 ≤ right.val) :
    left.signedGt right = decide (left > right) := by
  have hL : left.signedNegative = true := decide_eq_true leftNegative
  have hR : right.signedNegative = true := decide_eq_true rightNegative
  simp [signedGt, hL, hR]

@[simp] theorem signedGt_nonnegative_negative
    (left right : Word)
    (leftNonnegative : left.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ right.val) :
    left.signedGt right = true := by
  have hL : left.signedNegative = false :=
    decide_eq_false (Nat.not_le_of_lt leftNonnegative)
  have hR : right.signedNegative = true := decide_eq_true rightNegative
  simp [signedGt, hL, hR]

@[simp] theorem signedGt_negative_nonnegative
    (left right : Word)
    (leftNegative : 2 ^ 255 ≤ left.val)
    (rightNonnegative : right.val < 2 ^ 255) :
    left.signedGt right = false := by
  have hL : left.signedNegative = true := decide_eq_true leftNegative
  have hR : right.signedNegative = false :=
    decide_eq_false (Nat.not_le_of_lt rightNonnegative)
  simp [signedGt, hL, hR]

/-! ### BitwiseLogic interface -/

@[simp] theorem bitAnd_zero (value : Word) :
    value.bitAnd Word.zero = Word.zero := by
  apply Fin.ext
  simp [bitAnd, Word.zero]

@[simp] theorem bitAnd_self (value : Word) :
    value.bitAnd value = value := by
  apply Fin.ext
  simp [bitAnd]

theorem bitAnd_comm (left right : Word) :
    left.bitAnd right = right.bitAnd left := by
  apply Fin.ext
  simp [bitAnd, Nat.and_comm]

@[simp] theorem bitOr_zero (value : Word) :
    value.bitOr Word.zero = value := by
  apply Fin.ext
  change (value.val ||| 0) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] theorem bitOr_self (value : Word) :
    value.bitOr value = value := by
  apply Fin.ext
  change (value.val ||| value.val) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

theorem bitOr_comm (left right : Word) :
    left.bitOr right = right.bitOr left := by
  apply Fin.ext
  change (left.val ||| right.val) % wordModulus =
    (right.val ||| left.val) % wordModulus
  rw [Nat.or_comm]

@[simp] theorem bitXor_zero (value : Word) :
    value.bitXor Word.zero = value := by
  apply Fin.ext
  change (value.val ^^^ 0) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] theorem bitXor_self (value : Word) :
    value.bitXor value = Word.zero := by
  apply Fin.ext
  change (value.val ^^^ value.val) % wordModulus = 0
  simp

theorem bitXor_comm (left right : Word) :
    left.bitXor right = right.bitXor left := by
  apply Fin.ext
  change (left.val ^^^ right.val) % wordModulus =
    (right.val ^^^ left.val) % wordModulus
  rw [Nat.xor_comm]

/-! ### LogicalShifts interface -/

@[simp] theorem shiftLeft_zero (value : Word) :
    value.shiftLeft Word.zero = value := by
  apply Fin.ext
  simp [shiftLeft, Word.zero, Nat.mod_eq_of_lt value.isLt]

@[simp] theorem shiftRight_zero (value : Word) :
    value.shiftRight Word.zero = value := by
  apply Fin.ext
  simp [shiftRight, Word.zero]

theorem shiftLeft_of_lt_256
    (value shift : Word) (small : shift.val < 256) :
    value.shiftLeft shift = value <<< shift := by
  simp [shiftLeft, small]

theorem shiftRight_of_lt_256
    (value shift : Word) (small : shift.val < 256) :
    value.shiftRight shift = value >>> shift := by
  simp [shiftRight, small]

@[simp] theorem shiftLeft_of_ge_256
    (value shift : Word) (large : 256 ≤ shift.val) :
    value.shiftLeft shift = Word.zero := by
  simp [shiftLeft, Nat.not_lt_of_ge large]

@[simp] theorem shiftRight_of_ge_256
    (value shift : Word) (large : 256 ≤ shift.val) :
    value.shiftRight shift = Word.zero := by
  simp [shiftRight, Nat.not_lt_of_ge large]

/-! ### ArithmeticShift interface -/

@[simp] theorem shiftArithmeticRight_zero (value : Word) :
    value.shiftArithmeticRight Word.zero = value := by
  by_cases nonnegative : value.val < 2 ^ 255
  · apply Fin.ext
    simp [shiftArithmeticRight, Word.zero, nonnegative, Word.ofNatModulo,
      Nat.mod_eq_of_lt value.isLt]
  · have valueLe : value.val ≤ wordModulus - 1 :=
      Nat.le_sub_one_of_lt value.isLt
    apply Fin.ext
    simp [shiftArithmeticRight, Word.zero, nonnegative, Word.ofNatModulo,
      Nat.sub_sub_self valueLe, Nat.mod_eq_of_lt value.isLt]

theorem shiftArithmeticRight_of_lt_256_nonnegative
    (value shift : Word)
    (small : shift.val < 256)
    (nonnegative : value.val < 2 ^ 255) :
    value.shiftArithmeticRight shift =
      Word.ofNatModulo (value.val / 2 ^ shift.val) := by
  simp [shiftArithmeticRight, small, nonnegative]

theorem shiftArithmeticRight_of_lt_256_negative
    (value shift : Word)
    (small : shift.val < 256)
    (negative : 2 ^ 255 ≤ value.val) :
    value.shiftArithmeticRight shift =
      Word.ofNatModulo
        (wordModulus - 1 -
          ((wordModulus - 1 - value.val) / 2 ^ shift.val)) := by
  simp [shiftArithmeticRight, small, Nat.not_lt_of_ge negative]

@[simp] theorem shiftArithmeticRight_of_ge_256_nonnegative
    (value shift : Word)
    (large : 256 ≤ shift.val)
    (nonnegative : value.val < 2 ^ 255) :
    value.shiftArithmeticRight shift = Word.zero := by
  simp [shiftArithmeticRight, Nat.not_lt_of_ge large, nonnegative]

@[simp] theorem shiftArithmeticRight_of_ge_256_negative
    (value shift : Word)
    (large : 256 ≤ shift.val)
    (negative : 2 ^ 255 ≤ value.val) :
    value.shiftArithmeticRight shift = Word.maximum := by
  simp [shiftArithmeticRight, Nat.not_lt_of_ge large, Nat.not_lt_of_ge negative]

/-! ### SignExtension interface -/

theorem signExtend_clear
    (index value : Word)
    (small : index.val < 32)
    (clear :
      value.val % 2 ^ (8 * (index.val + 1)) <
        2 ^ (8 * (index.val + 1) - 1)) :
    index.signExtend value =
      Word.ofNatModulo (value.val % 2 ^ (8 * (index.val + 1))) := by
  simp [signExtend, small, clear]

theorem signExtend_set
    (index value : Word)
    (small : index.val < 32)
    (set :
      2 ^ (8 * (index.val + 1) - 1) ≤
        value.val % 2 ^ (8 * (index.val + 1))) :
    index.signExtend value =
      Word.ofNatModulo
        (wordModulus - 2 ^ (8 * (index.val + 1)) +
          value.val % 2 ^ (8 * (index.val + 1))) := by
  simp [signExtend, small, Nat.not_lt_of_ge set]

@[simp] theorem signExtend_ge_32
    (index value : Word) (large : 32 ≤ index.val) :
    index.signExtend value = value := by
  simp [signExtend, Nat.not_lt_of_ge large]

@[simp] theorem signExtend_zero (index : Word) :
    index.signExtend Word.zero = Word.zero := by
  by_cases small : index.val < 32
  · have signPositive : 0 < 2 ^ (8 * (index.val + 1) - 1) := Nat.two_pow_pos _
    apply Fin.ext
    simp [signExtend, small, signPositive, Word.zero, Word.ofNatModulo]
  · simp [signExtend, small]

@[simp] theorem signExtend_index31 (value : Word) :
    (Word.ofNatModulo 31).signExtend value = value := by
  have small : (Word.ofNatModulo 31).val < 32 := by decide
  have width : 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) = wordModulus := by decide
  have signEq : 2 ^ (8 * ((Word.ofNatModulo 31).val + 1) - 1) = 2 ^ 255 := by decide
  have low : value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) = value.val := by
    rw [width]
    exact Nat.mod_eq_of_lt value.isLt
  have ofValue : Word.ofNatModulo value.val = value := ofNatModulo_val value
  by_cases clear : value.val < 2 ^ 255
  · have clearBranch :
        value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) <
          2 ^ (8 * ((Word.ofNatModulo 31).val + 1) - 1) := by
      rw [low, signEq]; exact clear
    rw [signExtend_clear _ _ small clearBranch, low, ofValue]
  · have setBranch :
        2 ^ (8 * ((Word.ofNatModulo 31).val + 1) - 1) ≤
          value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) := by
      rw [low, signEq]; exact Nat.le_of_not_gt clear
    rw [signExtend_set _ _ small setBranch, low, width]
    simp [ofValue]

end Word

/-! ### Solcore Core AST and Operational Semantics -/

inductive Ty : Type where
  | unit
  | bool
  | word
  | integer
  | product (left right : Ty)
  | function (domain codomain : Ty)
  | sum (left right : Ty)
  | cell (content : Ty)
  | namedData (name : String)
  deriving DecidableEq, Repr

inductive HostFunction : Type where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
  | inputDataByte?
  | inputDataSize
  | inputDataWordBE?
  | currentAddress
  | callContractWord
  | callContractWordWithValue
  | createContractWord
  | emitLogWord
  deriving DecidableEq, Repr

inductive UnaryOp : Type where
  | boolNot
  | wordNot
  | wordClz
  | intNeg
  | intToWord
  | wordToUint
  | wordToSint
  deriving DecidableEq, Repr

inductive BinaryOp : Type where
  | wordAdd
  | wordSub
  | wordMul
  | wordDiv
  | wordMod
  | wordEq
  | wordGt
  | wordSgt
  | wordAnd
  | wordOr
  | wordXor
  | wordShl
  | wordShr
  | wordByte
  | wordSar
  | wordPow
  | wordSignExtend
  | wordSdiv
  | wordSmod
  | intAdd
  | intSub
  | intMul
  | intDiv
  | intMod
  | intEq
  | intLt
  | intLe
  deriving DecidableEq, Repr

inductive TernaryOp : Type where
  | wordAddMod
  | wordMulMod
  deriving DecidableEq, Repr

inductive Expr : Type where
  | var (index : Nat)
  | unit
  | bool (value : Bool)
  | word (value : Word)
  | integer (value : Int)
  | host (function : HostFunction)
  | unary (op : UnaryOp) (argument : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | ternary (op : TernaryOp) (first second third : Expr)
  | pair (left right : Expr)
  | fst (pair : Expr)
  | snd (pair : Expr)
  | inl (leftType rightType : Ty) (value : Expr)
  | inr (leftType rightType : Ty) (value : Expr)
  | case (scrutinee : Expr) (leftBranch rightBranch : Expr)
  | construct (typeName : String) (constructorIndex : Nat) (payload : Expr)
  | matchData (scrutinee : Expr) (branches : List Expr)
  | alloc (value : Expr)
  | load (cell : Expr)
  | store (cell value : Expr)
  | letE (bound body : Expr)
  | lam (parameterType : Ty) (body : Expr)
  | fix (functionType : Ty) (body : Expr)
  | app (function argument : Expr)
  | ifE (condition thenBranch elseBranch : Expr)
  deriving Repr

namespace Expr

def seq (first second : Expr) : Expr :=
  .letE first second

def boolToWord (condition : Expr) : Expr :=
  .ifE condition (.word (Word.ofNatModulo 1)) (.word Word.zero)

def wordToBool (value : Expr) : Expr :=
  .ifE (.binary .wordEq value (.word Word.zero)) (.bool false) (.bool true)

def wordIsZero (value : Expr) : Expr :=
  boolToWord (.binary .wordEq value (.word Word.zero))

def wordEqFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordEq left right)

def wordGtFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordGt left right)

def wordSgtFlag (left right : Expr) : Expr :=
  boolToWord (.binary .wordSgt left right)

def wordLt (left right : Expr) : Expr :=
  .binary .wordGt right left

def wordLtFlag (left right : Expr) : Expr :=
  wordGtFlag right left

def wordSlt (left right : Expr) : Expr :=
  .binary .wordSgt right left

def wordSltFlag (left right : Expr) : Expr :=
  wordSgtFlag right left

def boolAnd (left right : Expr) : Expr :=
  .ifE left right (.bool false)

def boolOr (left right : Expr) : Expr :=
  .ifE left (.bool true) right

end Expr

inductive Value : Type where
  | unit
  | bool (value : Bool)
  | word (value : Word)
  | integer (value : Int)
  | pair (left right : Value)
  | inl (value : Value)
  | inr (value : Value)
  | dataValue (typeName : String) (constructorIndex : Nat) (payload : Value)
  | ref (address : Nat)
  | closure (environment : List Value) (parameterType : Ty) (body : Expr)
  | fixClosure (environment : List Value) (functionType : Ty) (body : Expr)
  deriving Repr

abbrev Environment : Type :=
  List Value

abbrev Store : Type :=
  List Value

namespace UnaryOp

def apply : UnaryOp → Value → Option Value
  | .boolNot, .bool value => some (.bool (!value))
  | .wordNot, .word value => some (.word value.bitNot)
  | .wordClz, .word value => some (.word value.clz)
  | .intNeg, .integer value => some (.integer (-value))
  | .intToWord, .integer value =>
      let modulus : Int := Int.ofNat wordModulus
      some (.word (Word.ofNatModulo (Int.toNat (value % modulus))))
  | .wordToUint, .word value => some (.integer (Int.ofNat value.val))
  | .wordToSint, .word value =>
      let raw : Int := Int.ofNat value.val
      let signBit : Int := Int.ofNat (2 ^ 255)
      let modulus : Int := Int.ofNat wordModulus
      some (.integer (if raw < signBit then raw else raw - modulus))
  | _, _ => none

end UnaryOp

namespace BinaryOp

def apply : BinaryOp → Value → Value → Option Value
  | .wordAdd, .word left, .word right => some (.word (left.add right))
  | .wordSub, .word left, .word right => some (.word (left.sub right))
  | .wordMul, .word left, .word right => some (.word (left.mul right))
  | .wordDiv, .word left, .word right => some (.word (left.udiv right))
  | .wordMod, .word left, .word right => some (.word (left.umod right))
  | .wordEq, .word left, .word right => some (.bool (left == right))
  | .wordGt, .word left, .word right => some (.bool (decide (left > right)))
  | .wordSgt, .word left, .word right => some (.bool (left.signedGt right))
  | .wordAnd, .word left, .word right => some (.word (left.bitAnd right))
  | .wordOr, .word left, .word right => some (.word (left.bitOr right))
  | .wordXor, .word left, .word right => some (.word (left.bitXor right))
  | .wordShl, .word value, .word shift => some (.word (value.shiftLeft shift))
  | .wordShr, .word value, .word shift => some (.word (value.shiftRight shift))
  | .wordByte, .word index, .word value => some (.word (index.byteAt value))
  | .wordSar, .word value, .word shift =>
      some (.word (value.shiftArithmeticRight shift))
  | .wordPow, .word base, .word exponent =>
      some (.word (base.pow exponent))
  | .wordSignExtend, .word index, .word value =>
      some (.word (index.signExtend value))
  | .wordSdiv, .word dividend, .word divisor =>
      some (.word (dividend.sdiv divisor))
  | .wordSmod, .word dividend, .word divisor =>
      some (.word (dividend.smod divisor))
  | .intAdd, .integer left, .integer right => some (.integer (left + right))
  | .intSub, .integer left, .integer right => some (.integer (left - right))
  | .intMul, .integer left, .integer right => some (.integer (left * right))
  | .intDiv, .integer left, .integer right =>
      if right = 0 then some (.integer 0) else some (.integer (Int.tdiv left right))
  | .intMod, .integer left, .integer right =>
      if right = 0 then some (.integer 0) else some (.integer (Int.tmod left right))
  | .intEq, .integer left, .integer right => some (.bool (left == right))
  | .intLt, .integer left, .integer right => some (.bool (decide (left < right)))
  | .intLe, .integer left, .integer right => some (.bool (decide (left ≤ right)))
  | _, _, _ => none

end BinaryOp

namespace TernaryOp

def apply : TernaryOp → Value → Value → Value → Option Value
  | .wordAddMod, .word left, .word right, .word modulus =>
      some (.word (left.addMod right modulus))
  | .wordMulMod, .word left, .word right, .word modulus =>
      some (.word (left.mulMod right modulus))
  | _, _, _, _ => none

end TernaryOp

def readStore? (store : Store) (address : Nat) : Option Value :=
  store[address]?

def writeStore? : Store → Nat → Value → Option Store
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => do
      let updatedRest ← writeStore? rest index value
      pure (head :: updatedRest)

inductive Evaluates : Environment → Store → Expr → Value → Store → Prop where
  | var
      {environment : Environment} {store : Store} {index : Nat} {value : Value} :
      environment[index]? = some value →
      Evaluates environment store (.var index) value store
  | unit {environment : Environment} {store : Store} :
      Evaluates environment store .unit .unit store
  | bool {environment : Environment} {store : Store} {value : Bool} :
      Evaluates environment store (.bool value) (.bool value) store
  | word {environment : Environment} {store : Store} {value : Word} :
      Evaluates environment store (.word value) (.word value) store
  | integer {environment : Environment} {store : Store} {value : Int} :
      Evaluates environment store (.integer value) (.integer value) store
  | unary
      {environment : Environment} {initialStore finalStore : Store}
      {op : UnaryOp} {argument : Expr} {argumentValue result : Value} :
      Evaluates environment initialStore argument argumentValue finalStore →
      op.apply argumentValue = some result →
      Evaluates environment initialStore (.unary op argument) result finalStore
  | binary
      {environment : Environment} {initialStore intermediateStore finalStore : Store}
      {op : BinaryOp} {left right : Expr} {leftValue rightValue result : Value} :
      Evaluates environment initialStore left leftValue intermediateStore →
      Evaluates environment intermediateStore right rightValue finalStore →
      op.apply leftValue rightValue = some result →
      Evaluates environment initialStore (.binary op left right) result finalStore
  | ternary
      {environment : Environment}
      {initialStore afterFirstStore afterSecondStore finalStore : Store}
      {op : TernaryOp} {first second third : Expr}
      {firstValue secondValue thirdValue result : Value} :
      Evaluates environment initialStore first firstValue afterFirstStore →
      Evaluates environment afterFirstStore second secondValue afterSecondStore →
      Evaluates environment afterSecondStore third thirdValue finalStore →
      op.apply firstValue secondValue thirdValue = some result →
      Evaluates environment initialStore (.ternary op first second third)
        result finalStore
  | pair
      {environment : Environment} {initialStore intermediateStore finalStore : Store}
      {left right : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore left leftValue intermediateStore →
      Evaluates environment intermediateStore right rightValue finalStore →
      Evaluates environment initialStore (.pair left right)
        (.pair leftValue rightValue) finalStore
  | fst
      {environment : Environment} {initialStore finalStore : Store}
      {pairExpr : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore pairExpr
        (.pair leftValue rightValue) finalStore →
      Evaluates environment initialStore (.fst pairExpr) leftValue finalStore
  | snd
      {environment : Environment} {initialStore finalStore : Store}
      {pairExpr : Expr} {leftValue rightValue : Value} :
      Evaluates environment initialStore pairExpr
        (.pair leftValue rightValue) finalStore →
      Evaluates environment initialStore (.snd pairExpr) rightValue finalStore
  | alloc
      {environment : Environment} {initialStore allocatedStore : Store}
      {valueExpr : Expr} {storedValue : Value} :
      Evaluates environment initialStore valueExpr storedValue allocatedStore →
      Evaluates environment initialStore (.alloc valueExpr)
        (.ref allocatedStore.length) (allocatedStore ++ [storedValue])
  | load
      {environment : Environment} {initialStore finalStore : Store}
      {cellExpr : Expr} {address : Nat} {storedValue : Value} :
      Evaluates environment initialStore cellExpr (.ref address) finalStore →
      readStore? finalStore address = some storedValue →
      Evaluates environment initialStore (.load cellExpr) storedValue finalStore
  | store
      {environment : Environment}
      {initialStore cellStore valueStore updatedStore : Store}
      {cellExpr valueExpr : Expr} {address : Nat} {storedValue : Value} :
      Evaluates environment initialStore cellExpr (.ref address) cellStore →
      Evaluates environment cellStore valueExpr storedValue valueStore →
      writeStore? valueStore address storedValue = some updatedStore →
      Evaluates environment initialStore (.store cellExpr valueExpr)
        .unit updatedStore
  | letE
      {environment : Environment} {initialStore boundStore finalStore : Store}
      {bound body : Expr} {boundValue result : Value} :
      Evaluates environment initialStore bound boundValue boundStore →
      Evaluates (boundValue :: environment) boundStore body result finalStore →
      Evaluates environment initialStore (.letE bound body) result finalStore
  | ifTrue
      {environment : Environment} {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      Evaluates environment initialStore condition (.bool true) branchStore →
      Evaluates environment branchStore thenBranch result finalStore →
      Evaluates environment initialStore (.ifE condition thenBranch elseBranch)
        result finalStore
  | ifFalse
      {environment : Environment} {initialStore branchStore finalStore : Store}
      {condition thenBranch elseBranch : Expr} {result : Value} :
      Evaluates environment initialStore condition (.bool false) branchStore →
      Evaluates environment branchStore elseBranch result finalStore →
      Evaluates environment initialStore (.ifE condition thenBranch elseBranch)
        result finalStore

theorem evaluation_deterministic
    {environment : Environment} {initialStore firstStore secondStore : Store}
    {expr : Expr} {firstValue secondValue : Value}
    (firstEval : Evaluates environment initialStore expr firstValue firstStore)
    (secondEval : Evaluates environment initialStore expr secondValue secondStore) :
    firstValue = secondValue ∧ firstStore = secondStore := by
  induction firstEval generalizing secondValue secondStore with
  | var h1 => cases secondEval with | var h2 => exact ⟨Option.some.inj (h1.symm.trans h2), rfl⟩
  | unit | bool | word | integer => cases secondEval; exact ⟨rfl, rfl⟩
  | unary _ h1 ih =>
      cases secondEval with | unary e2 h2 =>
        rcases ih e2 with ⟨rfl, rfl⟩; exact ⟨Option.some.inj (h1.symm.trans h2), rfl⟩
  | binary _ _ h1 ihL ihR =>
      cases secondEval with | binary eL2 eR2 h2 =>
        rcases ihL eL2 with ⟨rfl, rfl⟩; rcases ihR eR2 with ⟨rfl, rfl⟩
        exact ⟨Option.some.inj (h1.symm.trans h2), rfl⟩
  | ternary _ _ _ h1 ih1 ih2 ih3 =>
      cases secondEval with | ternary e1 e2 e3 h2 =>
        rcases ih1 e1 with ⟨rfl, rfl⟩; rcases ih2 e2 with ⟨rfl, rfl⟩
        rcases ih3 e3 with ⟨rfl, rfl⟩; exact ⟨Option.some.inj (h1.symm.trans h2), rfl⟩
  | pair _ _ ihL ihR =>
      cases secondEval with | pair eL2 eR2 =>
        rcases ihL eL2 with ⟨rfl, rfl⟩; rcases ihR eR2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | fst _ ih =>
      cases secondEval with | fst e2 => rcases ih e2 with ⟨hP, rfl⟩; cases hP; exact ⟨rfl, rfl⟩
  | snd _ ih =>
      cases secondEval with | snd e2 => rcases ih e2 with ⟨hP, rfl⟩; cases hP; exact ⟨rfl, rfl⟩
  | alloc _ ih =>
      cases secondEval with | alloc e2 => rcases ih e2 with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | load _ h1 ih =>
      cases secondEval with | load e2 h2 =>
        rcases ih e2 with ⟨hR, rfl⟩; cases hR; exact ⟨Option.some.inj (h1.symm.trans h2), rfl⟩
  | store _ _ h1 ihC ihV =>
      cases secondEval with | store eC2 eV2 h2 =>
        rcases ihC eC2 with ⟨hR, rfl⟩; cases hR; rcases ihV eV2 with ⟨rfl, rfl⟩
        exact ⟨rfl, Option.some.inj (h1.symm.trans h2)⟩
  | letE _ _ ihB ihBody =>
      cases secondEval with | letE eB2 eBody2 => rcases ihB eB2 with ⟨rfl, rfl⟩; exact ihBody eBody2
  | ifTrue _ _ ihC ihT =>
      cases secondEval with
      | ifTrue eC2 eT2 => rcases ihC eC2 with ⟨_, rfl⟩; exact ihT eT2
      | ifFalse eC2 _ => rcases ihC eC2 with ⟨hC, _⟩; cases hC
  | ifFalse _ _ ihC ihF =>
      cases secondEval with
      | ifTrue eC2 _ => rcases ihC eC2 with ⟨hC, _⟩; cases hC
      | ifFalse eC2 eF2 => rcases ihC eC2 with ⟨_, rfl⟩; exact ihF eF2

end Core

end Compiler.Proofs.SolidityImport.Solcore
