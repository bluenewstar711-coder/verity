/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/

namespace Compiler.Autoresearch.GasCostModel

/-!
# Exact Formal EVM Cancun/Prague Gas & Bytecode Cost Model

This module formalizes the exact EVM Cancun/Prague (EIP-2929, EIP-3529, EIP-1153)
opcode gas schedule, quadratic memory expansion cost, and parametric cost profiles
(`ShimCostProfile`) for compiler runtime shims evaluated by `ShimArena`.

## Main Definitions
1. **EVM Cancun/Prague Opcode Constants**:
   `G_verylow`, `G_low`, `G_mid`, `G_high`, `G_keccak256_base`, `G_keccak256_word`,
   `G_sload_cold`, `G_sload_warm`, `G_sstore_set`, `G_sstore_reset`, `G_sstore_warm`,
   `G_tload`, `G_tstore`, `G_call_warm`.
2. **Quadratic Memory Expansion**:
   `memoryExpansionCost` and marginal `memoryExpansionDelta`.
3. **Shim Cost Profile (`ShimCostProfile`)**:
   Couples static opcode gas, words allocated beyond `0x40`, warm storage reads/writes,
   transient storage ops, and runtime bytecode size, with state-dependent gas
   evaluator `totalExecutionGas`.
4. **Formal Gas Dominance Theorems**:
   - `memoryExpansionCost_monotone`
   - `scratchSpaceHashing_strictly_dominates_bumpAlloc`
   - `coalescedPackedSlot_strictly_dominates_uncoalesced`
   - `transientLock_strictly_dominates_storageLock`
-/

/-! ## 1. EVM Cancun/Prague Opcode Gas Schedule -/

/-- `G_verylow`: `ADD`, `SUB`, `NOT`, `LT`, `GT`, `EQ`, `ISZERO`, `AND`, `OR`, `XOR`,
`SHL`, `SHR`, `SAR`, `CALLDATALOAD`, `MLOAD`, `MSTORE`, `PUSH*`, `DUP*`, `SWAP*`. -/
def G_verylow : Nat := 3

/-- `G_low`: `MUL`, `DIV`, `SDIV`, `MOD`, `SMOD`, `SIGNEXTEND`, `SELFBALANCE`. -/
def G_low : Nat := 5

/-- `G_mid`: `ADDMOD`, `MULMOD`, `JUMP`. -/
def G_mid : Nat := 8

/-- `G_high`: `JUMPI`. -/
def G_high : Nat := 10

/-- Base cost of `KECCAK256`. -/
def G_keccak256_base : Nat := 30

/-- Per-32-byte-word cost of `KECCAK256`. -/
def G_keccak256_word : Nat := 6

/-- Cold `SLOAD` cost under EIP-2929. -/
def G_sload_cold : Nat := 2100

/-- Warm `SLOAD` cost under EIP-2929. -/
def G_sload_warm : Nat := 100

/-- Zero-to-nonzero `SSTORE` cost (`G_sset`). -/
def G_sstore_set : Nat := 20000

/-- Nonzero-to-nonzero original-value `SSTORE` cost (`G_sreset`, EIP-2929). -/
def G_sstore_reset : Nat := 2900

/-- Warm dirty-slot `SSTORE` cost (`G_warmaccess`, EIP-2929). -/
def G_sstore_warm : Nat := 100

/-- EIP-1153 `TLOAD` cost (Cancun). -/
def G_tload : Nat := 100

/-- EIP-1153 `TSTORE` cost (Cancun). -/
def G_tstore : Nat := 100

/-- Warm `STATICCALL` / `CALL` base access cost under EIP-2929. -/
def G_call_warm : Nat := 100

/-! ## 2. Quadratic EVM Memory Expansion Cost -/

/-- Yellow Paper quadratic memory cost `C_mem(a) = 3 * a + floor(a^2 / 512)`
for `words` 32-byte words of active memory. -/
def memoryExpansionCost (words : Nat) : Nat :=
  3 * words + (words * words) / 512

/-- Marginal memory expansion gas incurred when expanding active memory from
`oldWords` to `newWords` 32-byte words. -/
def memoryExpansionDelta (oldWords newWords : Nat) : Nat :=
  memoryExpansionCost newWords - memoryExpansionCost oldWords

/-- Monotonicity of the EVM quadratic memory expansion cost function. -/
theorem memoryExpansionCost_monotone {oldWords newWords : Nat}
    (h : oldWords ≤ newWords) :
    memoryExpansionCost oldWords ≤ memoryExpansionCost newWords := by
  unfold memoryExpansionCost
  have hlin : 3 * oldWords ≤ 3 * newWords := Nat.mul_le_mul_left 3 h
  have hsq : oldWords * oldWords ≤ newWords * newWords := Nat.mul_le_mul h h
  have hdiv : (oldWords * oldWords) / 512 ≤ (newWords * newWords) / 512 :=
    Nat.div_le_div_right hsq
  exact Nat.add_le_add hlin hdiv

/-- Allocating zero additional words beyond `baseWords` incurs zero memory expansion gas. -/
@[simp]
theorem memoryExpansionDelta_self (baseWords : Nat) :
    memoryExpansionDelta baseWords baseWords = 0 := by
  simp [memoryExpansionDelta]

/-- Marginal memory expansion delta is monotone in the number of newly allocated words. -/
theorem memoryExpansionDelta_monotone_alloc (baseWords : Nat) {alloc₁ alloc₂ : Nat}
    (h : alloc₁ ≤ alloc₂) :
    memoryExpansionDelta baseWords (baseWords + alloc₁) ≤
      memoryExpansionDelta baseWords (baseWords + alloc₂) := by
  unfold memoryExpansionDelta
  have hmono : memoryExpansionCost (baseWords + alloc₁) ≤
      memoryExpansionCost (baseWords + alloc₂) :=
    memoryExpansionCost_monotone (Nat.add_le_add_left h baseWords)
  exact Nat.sub_le_sub_right hmono (memoryExpansionCost baseWords)

/-- Expanding active memory by 2 words (`64` bytes) always costs at least `6` gas. -/
theorem memoryExpansionDelta_two_words_ge_six (baseWords : Nat) :
    6 ≤ memoryExpansionDelta baseWords (baseWords + 2) := by
  unfold memoryExpansionDelta memoryExpansionCost
  have hsq : baseWords * baseWords ≤ (baseWords + 2) * (baseWords + 2) := by
    have hle : baseWords ≤ baseWords + 2 := Nat.le_add_right baseWords 2
    exact Nat.mul_le_mul hle hle
  have hdiv : (baseWords * baseWords) / 512 ≤ ((baseWords + 2) * (baseWords + 2)) / 512 :=
    Nat.div_le_div_right hsq
  omega

/-! ## 3. Shim Cost Profile & Total Execution Gas -/

/-- Parametric gas and bytecode cost profile for a compiler runtime shim. -/
structure ShimCostProfile where
  /-- State-independent opcode execution gas (excluding warm storage/transient counts and memory expansion). -/
  staticGas : Nat
  /-- Number of 32-byte words allocated above the active high-water mark (`0x40`). -/
  memWordsAllocated : Nat
  /-- Number of warm `SLOAD` operations executed by the shim. -/
  warmSloads : Nat
  /-- Number of warm `SSTORE` operations executed by the shim. -/
  warmSstores : Nat
  /-- Number of EIP-1153 transient storage operations (`TLOAD` / `TSTORE`) executed by the shim. -/
  transientOps : Nat
  /-- Runtime bytecode footprint of the shim in bytes. -/
  bytecodeBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- State-independent execution gas component of a `ShimCostProfile`. -/
def fixedExecutionGas (p : ShimCostProfile) : Nat :=
  p.staticGas +
    p.warmSloads * G_sload_warm +
    p.warmSstores * G_sstore_warm +
    p.transientOps * G_tload

/-- Total execution gas of a `ShimCostProfile` starting from an active memory footprint
of `baseMemWords` 32-byte words. -/
def totalExecutionGas (baseMemWords : Nat) (p : ShimCostProfile) : Nat :=
  fixedExecutionGas p +
    memoryExpansionDelta baseMemWords (baseMemWords + p.memWordsAllocated)

/-- Componentwise dominance of fixed gas and memory allocation implies total gas dominance
across all active memory states `baseMemWords`. -/
theorem totalExecutionGas_le_of_fixed_and_alloc_le
    {cand baseline : ShimCostProfile}
    (hfixed : fixedExecutionGas cand ≤ fixedExecutionGas baseline)
    (halloc : cand.memWordsAllocated ≤ baseline.memWordsAllocated)
    (baseMemWords : Nat) :
    totalExecutionGas baseMemWords cand ≤ totalExecutionGas baseMemWords baseline := by
  unfold totalExecutionGas
  exact Nat.add_le_add hfixed (memoryExpansionDelta_monotone_alloc baseMemWords halloc)

/-! ## 4. Canonical Shim Profiles & Formal Gas Dominance Theorems -/

/-- Cost profile for 2-word `keccak256` hashing in scratch space `[0x00, 0x40)`
(`0` words allocated beyond `0x40`). -/
def scratchKeccakCostProfile : ShimCostProfile where
  staticGas := G_keccak256_base + 2 * G_keccak256_word + 2 * G_verylow
  memWordsAllocated := 0
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 18

/-- Cost profile for 2-word `keccak256` hashing using bump allocation at `0x40`
(`+2` words allocated beyond `0x40` plus `mload(0x40)` / `mstore(0x40, ...)` overhead). -/
def bumpAllocKeccakCostProfile : ShimCostProfile where
  staticGas := G_keccak256_base + 2 * G_keccak256_word + 5 * G_verylow
  memWordsAllocated := 2
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 32

/-- **Gas Dominance Theorem 1 (`scratchSpaceHashing_strictly_dominates_bumpAlloc`)**:
2-word `keccak256` hashing in scratch space `[0x00, 0x40)` (`0` words allocated beyond `0x40`)
costs strictly less execution gas than bump allocation (`+2` words beyond `0x40`) for every
active memory size `baseMemWords`. -/
theorem scratchSpaceHashing_strictly_dominates_bumpAlloc (baseMemWords : Nat) :
    totalExecutionGas baseMemWords scratchKeccakCostProfile <
      totalExecutionGas baseMemWords bumpAllocKeccakCostProfile := by
  have hmem : 6 ≤ memoryExpansionDelta baseMemWords (baseMemWords + 2) :=
    memoryExpansionDelta_two_words_ge_six baseMemWords
  simp only [totalExecutionGas, fixedExecutionGas, scratchKeccakCostProfile,
    bumpAllocKeccakCostProfile, G_keccak256_base, G_keccak256_word, G_verylow,
    G_sload_warm, G_sstore_warm, G_tload, Nat.add_zero, memoryExpansionDelta_self]
  omega

/-- Cost profile for coalesced packed-slot read-modify-write of `fieldCount` fields
within a single 256-bit storage slot (`1 SLOAD + 1 SSTORE`). -/
def coalescedPackedSlotCostProfile (fieldCount : Nat) : ShimCostProfile where
  staticGas := fieldCount * (3 * G_verylow)
  memWordsAllocated := 0
  warmSloads := 1
  warmSstores := 1
  transientOps := 0
  bytecodeBytes := 14 + 6 * fieldCount

/-- Cost profile for uncoalesced packed-slot updates performing `fieldCount` separate
`SLOAD`/`SSTORE` pairs. -/
def uncoalescedPackedSlotCostProfile (fieldCount : Nat) : ShimCostProfile where
  staticGas := fieldCount * (3 * G_verylow)
  memWordsAllocated := 0
  warmSloads := fieldCount
  warmSstores := fieldCount
  transientOps := 0
  bytecodeBytes := 20 * fieldCount

/-- **Gas Dominance Theorem 2 (`coalescedPackedSlot_strictly_dominates_uncoalesced`)**:
For `2 ≤ fieldCount` packed fields in a storage slot, coalescing into `1 SLOAD + 1 SSTORE`
strictly dominates `fieldCount` separate `SLOAD`/`SSTORE` pairs across all memory states. -/
theorem coalescedPackedSlot_strictly_dominates_uncoalesced
    (fieldCount baseMemWords : Nat)
    (hfields : 2 ≤ fieldCount) :
    totalExecutionGas baseMemWords (coalescedPackedSlotCostProfile fieldCount) <
      totalExecutionGas baseMemWords (uncoalescedPackedSlotCostProfile fieldCount) := by
  simp only [totalExecutionGas, fixedExecutionGas, coalescedPackedSlotCostProfile,
    uncoalescedPackedSlotCostProfile, G_verylow, G_sload_warm, G_sstore_warm,
    G_tload, Nat.add_zero, memoryExpansionDelta_self]
  omega

/-- Cost profile for an EIP-1153 transient reentrancy lock (`TLOAD + TSTORE = 200` gas). -/
def transientLockCostProfile : ShimCostProfile where
  staticGas := 2 * G_verylow
  memWordsAllocated := 0
  warmSloads := 0
  warmSstores := 0
  transientOps := 2
  bytecodeBytes := 16

/-- Cost profile for a persistent storage reentrancy lock (`SLOAD + SSTORE` reset `2900` gas). -/
def storageLockCostProfile : ShimCostProfile where
  staticGas := 2 * G_verylow + (G_sstore_reset - G_sstore_warm)
  memWordsAllocated := 0
  warmSloads := 1
  warmSstores := 1
  transientOps := 0
  bytecodeBytes := 28

/-- **Gas Dominance Theorem 3 (`transientLock_strictly_dominates_storageLock`)**:
An EIP-1153 transient reentrancy lock (`TLOAD + TSTORE = 200` gas) strictly dominates a
persistent storage lock (`SLOAD + SSTORE`) across all active memory states. -/
theorem transientLock_strictly_dominates_storageLock (baseMemWords : Nat) :
    totalExecutionGas baseMemWords transientLockCostProfile <
      totalExecutionGas baseMemWords storageLockCostProfile ∧
    G_tload + G_tstore = 200 ∧
    G_tload + G_tstore < G_sload_warm + G_sstore_reset := by
  simp [totalExecutionGas, fixedExecutionGas, transientLockCostProfile,
    storageLockCostProfile, G_verylow, G_sload_warm, G_sstore_reset, G_sstore_warm,
    G_tload, G_tstore]

/-- Cost profile for branchless full-precision `mulDiv512` runtime shim (0 memory words). -/
def mulDiv512FastCostProfile : ShimCostProfile where
  staticGas := 6 * G_low + 8 * G_verylow + G_mid
  memWordsAllocated := 0
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 54

/-- Baseline cost profile for memory-spilling `mulDiv512` runtime shim (+2 memory words). -/
def mulDiv512BaselineCostProfile : ShimCostProfile where
  staticGas := 8 * G_low + 14 * G_verylow + 2 * G_mid
  memWordsAllocated := 2
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 88

/-- Cost profile for scratch-reusing 1-word `staticcall` wrapper (+2 words). -/
def staticCallWordFastCostProfile : ShimCostProfile where
  staticGas := G_call_warm + 4 * G_verylow
  memWordsAllocated := 2
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 36

/-- Baseline cost profile for unoptimized 1-word `staticcall` wrapper (+4 words). -/
def staticCallWordBaselineCostProfile : ShimCostProfile where
  staticGas := G_call_warm + 9 * G_verylow
  memWordsAllocated := 4
  warmSloads := 0
  warmSstores := 0
  transientOps := 0
  bytecodeBytes := 58

end Compiler.Autoresearch.GasCostModel
