import Compiler.Proofs.SolidityImport.Solcore.Primitives

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.Solcore.Core.Word

/-!
# Solcore Word ↔ Verity Uint256 / Int256 Exact Semantic Alignment

Proves exact word-level agreement between every 256-bit `Solcore.Core.Word`
primitive and its `Verity.Core.Uint256` / `Verity.Core.Int256` counterpart used
by `Verity.Core.Model.Denote.evalExpr`.
-/

/-! ### Unsigned modular arithmetic (`add`, `sub`, `mul`, `div`, `mod`, `pow`) -/

@[simp] theorem word_add_val_eq (left right : Word) :
    (left.add right).val = (left.toUint256 + right.toUint256).val :=
  rfl

@[simp] theorem word_sub_val_eq (left right : Word) :
    (left.sub right).val = (left.toUint256 - right.toUint256).val := by
  have hl : left.val < wordModulus := left.isLt
  have hr : right.val < wordModulus := right.isLt
  change (left - right).val = (Verity.Core.Uint256.sub left.toUint256 right.toUint256).val
  by_cases hle : right.val ≤ left.val
  · have hle' : right ≤ left := hle
    have hleU : right.toUint256.val ≤ left.toUint256.val := hle
    rw [Fin.sub_val_of_le hle']
    exact (Verity.Core.Uint256.subNoWrap hleU).symm
  · have hgt : right.val > left.val := Nat.lt_of_not_ge hle
    rw [Verity.Core.Uint256.sub_val_of_gt hgt]
    simp only [Fin.sub_def, val_toUint256, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS]
    have hEq : wordModulus - right.val + left.val =
        wordModulus - (right.val - left.val) := by
      unfold wordModulus at hl hr ⊢; omega
    rw [hEq]; rfl

@[simp] theorem word_mul_val_eq (left right : Word) :
    (left.mul right).val = (left.toUint256 * right.toUint256).val :=
  rfl

@[simp] theorem word_udiv_val_eq (left right : Word) :
    (left.udiv right).val = (left.toUint256 / right.toUint256).val := by
  have hl : left.val < wordModulus := left.isLt
  unfold udiv
  change (if right.val = 0 then Word.zero else left / right).val =
    (Verity.Core.Uint256.div left.toUint256 right.toUint256).val
  unfold Verity.Core.Uint256.div
  by_cases hz : right.val = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, val_toUint256, Verity.Core.Uint256.val_ofNat,
      Verity.Core.Uint256.modulus, ← wordModulus_eq_uint256_modulus]
    change left.val / right.val = (left.val / right.val) % wordModulus
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hl)).symm

@[simp] theorem word_umod_val_eq (left right : Word) :
    (left.umod right).val = (left.toUint256 % right.toUint256).val := by
  have hl : left.val < wordModulus := left.isLt
  unfold umod
  change (if right.val = 0 then Word.zero else left % right).val =
    (Verity.Core.Uint256.mod left.toUint256 right.toUint256).val
  unfold Verity.Core.Uint256.mod
  by_cases hz : right.val = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, val_toUint256, Verity.Core.Uint256.val_ofNat,
      Verity.Core.Uint256.modulus, ← wordModulus_eq_uint256_modulus]
    change left.val % right.val = (left.val % right.val) % wordModulus
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hl)).symm

@[simp] theorem word_pow_val_eq (base exponent : Word) :
    (base.pow exponent).val =
      (Verity.Core.Uint256.powEff base.toUint256 exponent.toUint256).val := by
  rw [Verity.Core.Uint256.powEff_eq_pow]
  rfl

/-! ### Bitwise logic (`and`, `or`, `xor`, `not`) -/

@[simp] theorem word_bitAnd_val_eq (left right : Word) :
    (left.bitAnd right).val =
      (Verity.Core.Uint256.and left.toUint256 right.toUint256).val :=
  rfl

@[simp] theorem word_bitOr_val_eq (left right : Word) :
    (left.bitOr right).val =
      (Verity.Core.Uint256.or left.toUint256 right.toUint256).val :=
  rfl

@[simp] theorem word_bitXor_val_eq (left right : Word) :
    (left.bitXor right).val =
      (Verity.Core.Uint256.xor left.toUint256 right.toUint256).val :=
  rfl

@[simp] theorem word_bitNot_val_eq (value : Word) :
    value.bitNot.val = (Verity.Core.Uint256.not value.toUint256).val := by
  have hv : value.val < wordModulus := value.isLt
  have hle : value ≤ Word.maximum := Nat.le_sub_one_of_lt hv
  unfold bitNot Verity.Core.Uint256.not
  rw [Fin.sub_val_of_le hle]
  simp only [val_maximum, val_toUint256, Verity.Core.Uint256.val_ofNat,
    Verity.Core.MAX_UINT256, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, wordModulus]
  have hlt : 2 ^ 256 - 1 - value.val < 2 ^ 256 := by omega
  exact (Nat.mod_eq_of_lt hlt).symm

/-! ### Logical shifts (`shl`, `shr`) and `byteAt` -/

@[simp] theorem word_shiftLeft_val_eq (value shift : Word) :
    (value.shiftLeft shift).val =
      (Verity.Core.Uint256.shl shift.toUint256 value.toUint256).val := by
  unfold shiftLeft Verity.Core.Uint256.shl
  by_cases hs : shift.val < 256
  · simp [hs]; rfl
  · have hge : 256 ≤ shift.val := Nat.le_of_not_lt hs
    simp only [hs, ↓reduceIte, val_zero, val_toUint256,
      Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, Nat.shiftLeft_eq]
    have hpow : 2 ^ shift.val = 2 ^ (shift.val - 256) * 2 ^ 256 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hge]
    rw [hpow, ← Nat.mul_assoc, Nat.mul_mod_left]

@[simp] theorem word_shiftRight_val_eq (value shift : Word) :
    (value.shiftRight shift).val =
      (Verity.Core.Uint256.shr shift.toUint256 value.toUint256).val := by
  have hv : value.val < 2 ^ 256 := value.isLt
  unfold shiftRight Verity.Core.Uint256.shr
  by_cases hs : shift.val < 256
  · simp only [hs, ↓reduceIte, val_toUint256, Verity.Core.Uint256.val_ofNat,
      Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    rfl
  · have hge : 256 ≤ shift.val := Nat.le_of_not_lt hs
    have hpow : 2 ^ 256 ≤ 2 ^ shift.val := Nat.pow_le_pow_right (by decide) hge
    simp only [hs, ↓reduceIte, val_zero, val_toUint256,
      Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv hpow), Nat.zero_mod]

@[simp] theorem word_byteAt_val_eq (index value : Word) :
    (index.byteAt value).val =
      (Verity.Core.Uint256.byte index.toUint256 value.toUint256).val := by
  unfold byteAt Verity.Core.Uint256.byte
  by_cases hlt : index.val < 32
  · have hnotGt : ¬ (index.val > 31) := by omega
    simp only [hlt, hnotGt, ↓reduceIte, val_ofNatModulo, val_toUint256,
      Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, Nat.shiftRight_eq_div_pow]
    rw [show (0xff : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  · have hgt : index.val > 31 := by omega
    simp [hlt, hgt]

/-! ### Direct and signed comparisons (`eq`, `lt`, `gt`, `slt`, `sgt`, `iszero`) -/

@[simp] theorem word_eq_eq_decide (left right : Word) :
    (left == right) = decide (left.val = right.val) := by
  by_cases h : left.val = right.val
  · have hFin : left = right := Fin.ext h
    simp [hFin]
  · have hFin : left ≠ right := fun heq => h (congrArg Fin.val heq)
    simp [h, hFin]

@[simp] theorem word_gt_eq_decide (left right : Word) :
    decide (left > right) = decide (right.val < left.val) :=
  rfl

@[simp] theorem word_lt_eq_decide (left right : Word) :
    decide (right > left) = decide (left.val < right.val) :=
  rfl

@[simp] theorem word_isZero_eq_decide (value : Word) :
    (value == Word.zero) = decide (value.val = 0) :=
  word_eq_eq_decide value Word.zero

theorem toInt256_coe_eq (w : Word) :
    (w.toInt256 : Int) =
      if w.val < 2 ^ 255 then
        Int.ofNat w.val
      else
        Int.ofNat w.val - Int.ofNat wordModulus :=
  rfl

theorem toInt256_eq_zero_iff (w : Word) :
    (w.toInt256 : Int) = 0 ↔ w.val = 0 := by
  have hw : w.val < wordModulus := w.isLt
  rw [toInt256_coe_eq]
  unfold wordModulus at hw ⊢
  by_cases h : w.val < 2 ^ 255 <;> simp [h] <;> omega

theorem toInt256_lt_zero_iff (w : Word) :
    (w.toInt256 : Int) < 0 ↔ 2 ^ 255 ≤ w.val := by
  have hw : w.val < wordModulus := w.isLt
  rw [toInt256_coe_eq]
  unfold wordModulus at hw ⊢
  by_cases h : w.val < 2 ^ 255 <;> simp [h] <;> omega

@[simp] theorem decide_toInt256_lt_zero (w : Word) :
    decide ((w.toInt256 : Int) < 0) = w.signedNegative := by
  unfold signedNegative
  exact decide_eq_decide.mpr (toInt256_lt_zero_iff w)

@[simp] theorem word_signedGt_eq_decide (left right : Word) :
    left.signedGt right = decide ((right.toInt256 : Int) < (left.toInt256 : Int)) := by
  have hl : left.val < wordModulus := left.isLt
  have hr : right.val < wordModulus := right.isLt
  unfold signedGt
  rw [toInt256_coe_eq left, toInt256_coe_eq right]
  change (if decide (2 ^ 255 ≤ left.val) != decide (2 ^ 255 ≤ right.val) then
      decide (2 ^ 255 ≤ right.val) else decide (right.val < left.val)) = _
  unfold wordModulus at hl hr ⊢
  by_cases hlS : left.val < 2 ^ 255 <;> by_cases hrS : right.val < 2 ^ 255
  · have hlN : ¬ (2 ^ 255 ≤ left.val) := Nat.not_le.mpr hlS
    have hrN : ¬ (2 ^ 255 ≤ right.val) := Nat.not_le.mpr hrS
    simp [hlS, hrS, hlN, hrN]
  · have hlN : ¬ (2 ^ 255 ≤ left.val) := Nat.not_le.mpr hlS
    have hrP : 2 ^ 255 ≤ right.val := Nat.le_of_not_lt hrS
    simp [hlS, hrS, hlN, hrP]; omega
  · have hlP : 2 ^ 255 ≤ left.val := Nat.le_of_not_lt hlS
    have hrN : ¬ (2 ^ 255 ≤ right.val) := Nat.not_le.mpr hrS
    simp [hlS, hrS, hlP, hrN]; omega
  · have hlP : 2 ^ 255 ≤ left.val := Nat.le_of_not_lt hlS
    have hrP : 2 ^ 255 ≤ right.val := Nat.le_of_not_lt hrS
    simp [hlS, hrS, hlP, hrP]

@[simp] theorem word_signedLt_eq_decide (left right : Word) :
    right.signedGt left = decide ((left.toInt256 : Int) < (right.toInt256 : Int)) :=
  word_signedGt_eq_decide right left

/-! ### Signed division and modulo (`sdiv`, `smod`) -/

theorem signedAbsNat_toInt256 (w : Word) :
    Verity.Core.Int256.signedAbsNat (w.toInt256 : Int) = w.signedMagnitude := by
  have hw : w.val < wordModulus := w.isLt
  unfold signedMagnitude Verity.Core.Int256.signedAbsNat
  rw [toInt256_coe_eq]
  by_cases h : w.val < 2 ^ 255
  · simp [h]
  · simp only [h, ↓reduceIte]
    unfold wordModulus at hw ⊢
    have hsub : Int.ofNat w.val - Int.ofNat (2 ^ 256) =
        -Int.ofNat (2 ^ 256 - w.val) := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [hsub, Int.natAbs_neg, Int.ofNat_eq_natCast, Int.natAbs_natCast]

theorem ofSignedMagnitude_val_eq_ofInt (neg : Bool) (mag : Nat) :
    (Word.ofSignedMagnitude neg mag).val =
      (if neg then Verity.Core.Int256.ofInt (-Int.ofNat mag)
       else Verity.Core.Int256.ofInt (Int.ofNat mag)).toUint256.val := by
  unfold ofSignedMagnitude Verity.Core.Int256.ofInt
  cases neg
  · have hnn : ¬ (Int.ofNat mag < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp only [Bool.false_eq_true, ↓reduceIte, hnn,
      Verity.Core.Int256.toUint256_ofUint256, Verity.Core.Uint256.val_ofNat,
      Verity.Core.Uint256.modulus, ← wordModulus_eq_uint256_modulus,
      val_ofNatModulo, Nat.mod_mod]
    rfl
  · by_cases hm0 : mag = 0
    · subst hm0; simp
    · have hneg : (-Int.ofNat mag : Int) < 0 := by
        rw [Int.ofNat_eq_natCast]; omega
      have hAbs : Int.natAbs (-Int.ofNat mag) = mag := by simp [Int.natAbs_neg]
      simp only [↓reduceIte, hneg, hAbs, Verity.Core.Int256.toUint256_ofUint256,
        Verity.Core.Uint256.val_ofNat, Verity.Core.Int256.modulus,
        Verity.Core.Uint256.modulus, ← wordModulus_eq_uint256_modulus]
      by_cases hnorm : mag % wordModulus = 0 <;> simp [hnorm]

@[simp] theorem word_sdiv_val_eq (dividend divisor : Word) :
    (dividend.sdiv divisor).val =
      (Verity.Core.Int256.div dividend.toInt256 divisor.toInt256).toUint256.val := by
  unfold sdiv Verity.Core.Int256.div
  by_cases hz : divisor.val = 0
  · have hzInt : (divisor.toInt256 : Int) = 0 := (toInt256_eq_zero_iff divisor).mpr hz
    simp [hz, hzInt]; rfl
  · have hzInt : (divisor.toInt256 : Int) ≠ 0 :=
      fun h => hz ((toInt256_eq_zero_iff divisor).mp h)
    simp only [hz, hzInt, ↓reduceIte, signedAbsNat_toInt256]
    rw [ofSignedMagnitude_val_eq_ofInt]
    rw [← decide_toInt256_lt_zero dividend, ← decide_toInt256_lt_zero divisor]
    cases decide ((dividend.toInt256 : Int) < 0) <;>
      cases decide ((divisor.toInt256 : Int) < 0) <;> rfl

@[simp] theorem word_smod_val_eq (dividend divisor : Word) :
    (dividend.smod divisor).val =
      (Verity.Core.Int256.mod dividend.toInt256 divisor.toInt256).toUint256.val := by
  unfold smod Verity.Core.Int256.mod
  by_cases hz : divisor.val = 0
  · have hzInt : (divisor.toInt256 : Int) = 0 := (toInt256_eq_zero_iff divisor).mpr hz
    simp [hz, hzInt]; rfl
  · have hzInt : (divisor.toInt256 : Int) ≠ 0 :=
      fun h => hz ((toInt256_eq_zero_iff divisor).mp h)
    simp only [hz, hzInt, ↓reduceIte, signedAbsNat_toInt256]
    rw [ofSignedMagnitude_val_eq_ofInt, ← decide_toInt256_lt_zero dividend]
    by_cases hlt : (dividend.toInt256 : Int) < 0 <;> simp [hlt]

/-! ### Arithmetic right shift (`sar`) -/

private theorem int_fdiv_ofNat_two_pow (value shift : Nat) :
    (Int.ofNat value).fdiv (Int.ofNat (2 ^ shift)) =
      Int.ofNat (value / 2 ^ shift) := by
  have hpos : 0 < 2 ^ shift := Nat.two_pow_pos shift
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n =>
      cases value with
      | zero => simp [Int.fdiv]
      | succ m => simp [Int.fdiv]

private theorem int_sub_modulus_eq_negSucc (value : Nat)
    (hv : value < wordModulus) :
    Int.ofNat value - Int.ofNat wordModulus =
      Int.negSucc (wordModulus - 1 - value) := by
  unfold wordModulus at hv ⊢
  rw [Int.negSucc_eq]
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem int_fdiv_neg_two_pow (value shift : Nat)
    (hv : value < wordModulus) :
    (Int.ofNat value - Int.ofNat wordModulus).fdiv (Int.ofNat (2 ^ shift)) =
      Int.negSucc ((wordModulus - 1 - value) / 2 ^ shift) := by
  rw [int_sub_modulus_eq_negSucc value hv]
  have hpos : 0 < 2 ^ shift := Nat.two_pow_pos shift
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n => simp [Int.fdiv]

private theorem ofInt_negSucc_val (n : Nat) (hn : n + 1 < wordModulus) :
    (Verity.Core.Int256.ofInt (Int.negSucc n)).toUint256.val =
      wordModulus - 1 - n := by
  have hneg : Int.negSucc n < 0 := by simp
  have hAbs : (Int.negSucc n).natAbs = n + 1 := rfl
  have hSubLt : wordModulus - (n + 1) < wordModulus := by
    have : 0 < wordModulus := wordModulus_pos; omega
  simp only [Verity.Core.Int256.ofInt, hneg, ↓reduceIte, hAbs,
    Verity.Core.Int256.toUint256_ofUint256, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
    ← wordModulus_eq_uint256_modulus, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hSubLt]
  omega

@[simp] theorem word_shiftArithmeticRight_val_eq (value shift : Word) :
    (value.shiftArithmeticRight shift).val =
      (Verity.Core.Int256.sar shift.toInt256 value.toInt256).toUint256.val := by
  have hv : value.val < wordModulus := value.isLt
  have hsMod : shift.toInt256.word.val % Verity.Core.Int256.modulus = shift.val :=
    Nat.mod_eq_of_lt shift.isLt
  unfold shiftArithmeticRight Verity.Core.Int256.sar
  rw [hsMod]
  by_cases hs : shift.val < 256
  · have hnotGe : ¬ (shift.val ≥ 256) := Nat.not_le_of_lt hs
    simp only [hs, hnotGe, ↓reduceIte]
    rw [toInt256_coe_eq value]
    by_cases hvS : value.val < 2 ^ 255
    · rw [if_pos hvS, if_pos hvS, int_fdiv_ofNat_two_pow]
      have hnn : ¬ (Int.ofNat (value.val / 2 ^ shift.val) < 0) :=
        Int.not_lt.mpr (Int.natCast_nonneg _)
      simp only [Verity.Core.Int256.ofInt, hnn, ↓reduceIte,
        Verity.Core.Int256.toUint256_ofUint256, Verity.Core.Uint256.val_ofNat,
        Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, val_ofNatModulo]
      rfl
    · have hvGe : 2 ^ 255 ≤ value.val := Nat.le_of_not_lt hvS
      have hdivLe : (wordModulus - 1 - value.val) / 2 ^ shift.val ≤
          wordModulus - 1 - value.val := Nat.div_le_self _ _
      have hqLt : (wordModulus - 1 - value.val) / 2 ^ shift.val + 1 < wordModulus := by
        unfold wordModulus at hv hvGe hdivLe ⊢; omega
      have hresLt : wordModulus - 1 - (wordModulus - 1 - value.val) / 2 ^ shift.val <
          wordModulus :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by unfold wordModulus; omega)
      rw [if_neg hvS, if_neg hvS, int_fdiv_neg_two_pow value.val shift.val hv,
        ofInt_negSucc_val _ hqLt, val_ofNatModulo, Nat.mod_eq_of_lt hresLt]
  · have hge : shift.val ≥ 256 := Nat.le_of_not_lt hs
    simp only [hs, hge, ↓reduceIte]
    by_cases hvS : value.val < 2 ^ 255
    · have hnotNeg : ¬ ((value.toInt256 : Int) < 0) := by
        rw [toInt256_lt_zero_iff value]; omega
      simp [hvS, hnotNeg]; rfl
    · have hNeg : (value.toInt256 : Int) < 0 := by
        rw [toInt256_lt_zero_iff value]; omega
      simp only [hvS, hNeg, ↓reduceIte, val_maximum]
      exact (ofInt_negSucc_val 0 (by decide)).symm

/-! ### Sign extension (`signextend`) -/

private theorem tb_pow_sub_pow {n k : Nat} (hkn : k ≤ n) (i : Nat) :
    (2 ^ n - 2 ^ k).testBit i = (decide (k ≤ i) && decide (i < n)) := by
  have := Nat.one_le_pow k 2 (by omega)
  have := Nat.pow_le_pow_right (show 0 < 2 from by omega) hkn
  rw [show 2 ^ k = (2 ^ k - 1) + 1 from by omega,
      Nat.testBit_two_pow_sub_succ (by omega),
      Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < k <;> by_cases h2 : i < n <;> simp_all

private theorem testBit_and_two_pow_ne_zero {v k : Nat} :
    v &&& 2 ^ k ≠ 0 ↔ v.testBit k = true := by
  constructor
  · intro h
    cases hf : v.testBit k
    · exfalso; apply h; apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hik : k = i
      · subst hik; simp [hf]
      · simp [hik]
    · rfl
  · intro htb h0
    have : (v &&& 2 ^ k).testBit k = true := by simp [Nat.testBit_and, htb]
    rw [h0] at this; simp at this

private theorem testBit_eq_true_iff_mod_ge (v bp : Nat) :
    v.testBit bp = true ↔ 2 ^ bp ≤ v % 2 ^ (bp + 1) := by
  have hmod : (v % 2 ^ (bp + 1)).testBit bp = v.testBit bp := by
    rw [Nat.testBit_mod_two_pow]; simp
  have hlt : v % 2 ^ (bp + 1) < 2 ^ bp * 2 := by
    rw [← Nat.pow_succ]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdivLt : (v % 2 ^ (bp + 1)) / 2 ^ bp < 2 :=
    Nat.div_lt_of_lt_mul hlt
  have hpos : 0 < 2 ^ bp := Nat.two_pow_pos bp
  have hdivGe : 1 ≤ (v % 2 ^ (bp + 1)) / 2 ^ bp ↔ 2 ^ bp ≤ v % 2 ^ (bp + 1) := by
    rw [Nat.le_div_iff_mul_le hpos, Nat.one_mul]
  rw [← hmod, ← hdivGe, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1,
    Nat.and_one_is_mod, Nat.mod_eq_of_lt hdivLt]
  generalize (v % 2 ^ (bp + 1)) / 2 ^ bp = q at hdivLt ⊢
  simp only [bne_iff_ne, ne_eq]
  omega

private theorem testBit_high_add_low (v k : Nat) (hk : k ≤ 256) (i : Nat) :
    (2 ^ 256 - 2 ^ k + v % 2 ^ k).testBit i =
      (if i < k then v.testBit i else decide (i < 256)) := by
  let m := 2 ^ (256 - k) - 1
  let r := v % 2 ^ k
  have hr : r < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hm : 2 ^ 256 - 2 ^ k = m * 2 ^ k := by
    dsimp [m]; rw [Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk, Nat.one_mul]
  rw [hm, Nat.add_comm (m * 2 ^ k) r]
  by_cases hik : i < k
  · have hmod : (r + m * 2 ^ k) % 2 ^ k = r := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have htb : (r + m * 2 ^ k).testBit i = v.testBit i := by
      have h1 := Nat.testBit_mod_two_pow (r + m * 2 ^ k) k i
      have h2 := Nat.testBit_mod_two_pow v k i
      rw [hmod] at h1
      dsimp [r] at h1
      rw [decide_eq_true hik, Bool.true_and] at h1 h2
      exact h1.symm.trans h2
    rw [htb, if_pos hik]
  · have hge : k ≤ i := Nat.le_of_not_lt hik
    have hi : i = (i - k) + k := (Nat.sub_add_cancel hge).symm
    have hdiv : (r + m * 2 ^ k) / 2 ^ k = m := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hr, Nat.zero_add]
    rw [if_neg hik, hi, Nat.testBit_add, hdiv]
    dsimp [m]
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_decide.mpr (by omega)

private theorem or_high_mask_eq_add_mod (v k : Nat) (hv : v < 2 ^ 256) (hk : k ≤ 256) :
    v ||| (2 ^ 256 - 2 ^ k) = 2 ^ 256 - 2 ^ k + v % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, tb_pow_sub_pow hk, testBit_high_add_low v k hk i]
  by_cases hik : i < k
  · have hnotLe : ¬ (k ≤ i) := Nat.not_le_of_lt hik
    simp [hik, hnotLe]
  · have hle : k ≤ i := Nat.le_of_not_lt hik
    by_cases hi256 : i < 256
    · simp [hik, hle, hi256]
    · have hvGe : v < 2 ^ i :=
        Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi256))
      simp [hik, hle, hi256, Nat.testBit_lt_two_pow hvGe]

private theorem word_signExtend_val_eq_of_lt31 (index value : Word)
    (hlt31 : index.val < 31) :
    (index.signExtend value).val =
      (Verity.Core.Uint256.signextend index.toUint256 value.toUint256).val := by
  have hv : value.val < 2 ^ 256 := value.isLt
  have hlt32 : index.val < 32 := by omega
  have hnotGe31 : ¬ (index.val ≥ 31) := by omega
  let bp := index.val * 8 + 7
  have hkEq : 8 * (index.val + 1) = bp + 1 := by dsimp [bp]; omega
  have hbpSub : bp + 1 - 1 = bp := by omega
  have hkLe : bp + 1 ≤ 256 := by dsimp [bp]; omega
  have hpowLt : 2 ^ (bp + 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hkLe
  have hmodBp : value.val % 2 ^ (bp + 1) < 2 ^ (bp + 1) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlowLt : value.val % 2 ^ (bp + 1) < 2 ^ 256 :=
    Nat.lt_of_lt_of_le hmodBp hpowLt
  have hhighLt : 2 ^ 256 - 2 ^ (bp + 1) + value.val % 2 ^ (bp + 1) < 2 ^ 256 := by omega
  unfold signExtend Verity.Core.Uint256.signextend
  simp only [hlt32, hnotGe31, ↓reduceIte, val_toUint256, hkEq, hbpSub]
  change (if value.val % 2 ^ (bp + 1) < 2 ^ bp then
      ofNatModulo (value.val % 2 ^ (bp + 1))
    else
      ofNatModulo (wordModulus - 2 ^ (bp + 1) + value.val % 2 ^ (bp + 1))).val =
    (if value.val &&& 2 ^ bp ≠ 0 then
      Verity.Core.Uint256.ofNat (value.val ||| (Verity.Core.Uint256.modulus - 1 - (2 ^ (bp + 1) - 1)))
    else
      Verity.Core.Uint256.ofNat (value.val &&& (2 ^ (bp + 1) - 1))).val
  by_cases hset : value.val &&& 2 ^ bp ≠ 0
  · have hgeSign : 2 ^ bp ≤ value.val % 2 ^ (bp + 1) :=
      (testBit_eq_true_iff_mod_ge value.val bp).mp (testBit_and_two_pow_ne_zero.mp hset)
    have hnotLt : ¬ (value.val % 2 ^ (bp + 1) < 2 ^ bp) := Nat.not_lt_of_ge hgeSign
    have hmask : 2 ^ 256 - 1 - (2 ^ (bp + 1) - 1) = 2 ^ 256 - 2 ^ (bp + 1) := by
      have := Nat.two_pow_pos (bp + 1); omega
    rw [if_neg hnotLt, if_pos hset]
    simp only [val_ofNatModulo, Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, wordModulus, hmask,
      or_high_mask_eq_add_mod value.val (bp + 1) hv hkLe, Nat.mod_eq_of_lt hhighLt]
  · have hltSign : value.val % 2 ^ (bp + 1) < 2 ^ bp :=
      Classical.byContradiction fun hge =>
        hset (testBit_and_two_pow_ne_zero.mpr
          ((testBit_eq_true_iff_mod_ge value.val bp).mpr (Nat.le_of_not_lt hge)))
    rw [if_pos hltSign, if_neg hset]
    simp only [val_ofNatModulo, Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS, wordModulus,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlowLt]

@[simp] theorem word_signExtend_val_eq (index value : Word) :
    (index.signExtend value).val =
      (Verity.Core.Uint256.signextend index.toUint256 value.toUint256).val := by
  by_cases hge32 : 32 ≤ index.val
  · have hge31 : index.val ≥ 31 := by omega
    rw [signExtend_ge_32 index value hge32]
    unfold Verity.Core.Uint256.signextend
    simp [hge31]
  · by_cases heq31 : index.val = 31
    · have hIdx : index = Word.ofNatModulo 31 := by
        apply Fin.ext; rw [heq31, val_ofNatModulo]; rfl
      have hge31 : index.val ≥ 31 := by omega
      rw [hIdx, signExtend_index31]
      unfold Verity.Core.Uint256.signextend
      rw [← hIdx]
      simp [hge31]
    · exact word_signExtend_val_eq_of_lt31 index value (by omega)

end Compiler.Proofs.SolidityImport.Solcore.Core.Word
