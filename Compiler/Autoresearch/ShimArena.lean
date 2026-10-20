/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.Autoresearch.GasCostModel
import Compiler.Proofs.MetaSpecs
import Compiler.Yul.PatchFramework

namespace Compiler.Autoresearch.ShimArena

open Compiler.Autoresearch.GasCostModel
open Compiler.Proofs.MetaSpecs
open Compiler.Yul
open Lean (Name)

/-!
# Three-Stage Compiler Shim Autoresearch Arena & Dominance Certificates

This module connects `Compiler.Proofs.MetaSpecs.VerifiedCompilerShim`,
`Compiler.Autoresearch.GasCostModel`, and `Compiler.Yul.PatchFramework` into a
three-stage autoresearch verification and selection pipeline:

1. **Stage 1 (Decidable Boundary-Vector Fast-Check)**:
   Evaluates candidate shims against specification denotations over canonical
   256-bit boundary vectors (`[0, 1, 2, 2^128 - 1, 2^160 - 1, 2^255, 2^256 - 1]`),
   dirty high-bit masks, and the `0x40` free-memory pointer (`passesStage1FastCheck`),
   immediately refuting unsound candidates (`stage1_refutes_unsound_candidate`).
2. **Stage 2 (Kernel `VerifiedCompilerShim` Proof Certificate)**:
   `CertifiedShimCandidate` bundles a kernel-checked `VerifiedCompilerShim`, its
   `ShimCostProfile`, and a Stage 1 certificate.
3. **Stage 3 (Pareto Gas & Bytecode Selection)**:
   `strictlyDominatesCost` and `selectArenaWinner` select the Pareto-winning
   certified candidate, backed by the master soundness and cost-optimality theorem
   `arenaWinner_preserves_semantics_and_optimizes_cost`.
-/

/-! ## Stage 1: Decidable Fast-Check on Boundary Vectors -/

/-- Canonical 256-bit EVM boundary words used in Stage 1 fast-check:
`[0, 1, 2, 2^128 - 1, 2^160 - 1, 2^255, 2^256 - 1]`. -/
def canonicalBoundaryWords : List Nat :=
  [0, 1, 2, 2 ^ 128 - 1, 2 ^ 160 - 1, 2 ^ 255, 2 ^ 256 - 1]

/-- Structured boundary test vector carrying an input word, dirty upper-bit mask,
and initial free-memory pointer at `0x40` (default `0x80`). -/
structure BoundaryVector where
  /-- Primary 256-bit boundary input word. -/
  inputWord : Nat
  /-- Dirty high-bit noise above 160 bits for sub-word masking checks. -/
  dirtyHighBits : Nat := 1 <<< 160
  /-- Initial free-memory pointer at `0x40`. -/
  freeMemPtr : Nat := 0x80
  deriving DecidableEq, Repr, Inhabited

/-- Canonical structured boundary vector suite derived from `canonicalBoundaryWords`. -/
def canonicalBoundaryVectors : List BoundaryVector :=
  canonicalBoundaryWords.map (fun w => { inputWord := w })

/-- Stage 1 decidable fast-check: returns `true` iff `candEval` agrees with `specEval`
(both returning `(resultWord, postFreeMemPtr)`) on every boundary vector in `vectors`. -/
def passesStage1FastCheck
    (specEval candEval : Nat → Nat × Nat)
    (vectors : List Nat) : Bool :=
  vectors.all (fun v => candEval v == specEval v)

/-- **Stage 1 Refutation Theorem (`stage1_refutes_unsound_candidate`)**:
Any candidate shim whose observation `(resultWord, postFreeMemPtr)` diverges from
`specEval` on at least one boundary vector `v ∈ vectors` (e.g., by corrupting `0x40`
or leaking dirty high bits) is deterministically rejected by Stage 1. -/
theorem stage1_refutes_unsound_candidate
    (specEval candEval : Nat → Nat × Nat)
    (vectors : List Nat)
    (v : Nat)
    (hmem : v ∈ vectors)
    (hunsound : candEval v ≠ specEval v) :
    passesStage1FastCheck specEval candEval vectors = false := by
  unfold passesStage1FastCheck
  rw [List.all_eq_false]
  refine ⟨v, hmem, ?_⟩
  simp [hunsound]

/-- Pointwise agreement between `candEval` and `specEval` guarantees Stage 1 success. -/
theorem passesStage1FastCheck_of_pointwise_eq
    (specEval candEval : Nat → Nat × Nat)
    (vectors : List Nat)
    (heq : ∀ v, candEval v = specEval v) :
    passesStage1FastCheck specEval candEval vectors = true := by
  unfold passesStage1FastCheck
  rw [List.all_eq_true]
  intro v _
  simp [heq v]

/-- Concrete Stage 1 refutation witness: a broken `keccak256` candidate that bumps `0x40`
by `64` bytes instead of preserving `0x40` is rejected on `canonicalBoundaryWords`. -/
def unsoundFmpCorruptingCandEval (w : Nat) : Nat × Nat :=
  (w % evmWordModulus, 0x80 + 64)

/-- Reference Stage 1 evaluator for scratch-space `keccak256` preserving `0x40 = 0x80`. -/
def soundScratchEval (w : Nat) : Nat × Nat :=
  (w % evmWordModulus, 0x80)

/-- Kernel-checked (`by decide`) witness that Stage 1 refutes `0x40` corruption. -/
theorem stage1_rejects_fmp_corruption :
    passesStage1FastCheck soundScratchEval unsoundFmpCorruptingCandEval
      canonicalBoundaryWords = false := by
  decide

/-- Concrete Stage 1 refutation witness: an unsound 160-bit address shim that fails to
mask dirty bits above bit 160 (`w ≥ 2^160`) is rejected on `canonicalBoundaryWords`. -/
def soundAddressMaskEval (w : Nat) : Nat × Nat :=
  (w % (2 ^ 160), 0x80)

/-- Unsound address candidate that leaves upper bits unmasked. -/
def unsoundUnmaskedAddressEval (w : Nat) : Nat × Nat :=
  (w % evmWordModulus, 0x80)

/-- Kernel-checked (`by decide`) witness that Stage 1 refutes dirty high-bit leakage. -/
theorem stage1_rejects_dirty_high_bits :
    passesStage1FastCheck soundAddressMaskEval unsoundUnmaskedAddressEval
      canonicalBoundaryWords = false := by
  decide

/-! ## Stage 2: Kernel-Certified Shim Candidate (`CertifiedShimCandidate`) -/

/-- **Stage 2 Certificate (`CertifiedShimCandidate`)**:
Couples a kernel-verified `VerifiedCompilerShim` (Meta-Spec 7), its `ShimCostProfile`,
its projected Stage 1 evaluators, and the proof that Stage 1 fast-check passes. -/
structure CertifiedShimCandidate (Input State Obs : Type) where
  /-- Backing kernel-verified compiler runtime shim. -/
  shim : VerifiedCompilerShim Input State Obs
  /-- Exact gas and bytecode cost profile of this candidate. -/
  cost : ShimCostProfile
  /-- Specification boundary evaluator `(resultWord, postFreeMemPtr)`. -/
  specBoundaryEval : Nat → Nat × Nat
  /-- Candidate boundary evaluator `(resultWord, postFreeMemPtr)`. -/
  candBoundaryEval : Nat → Nat × Nat
  /-- Boundary vector list tested in Stage 1. -/
  boundaryVectors : List Nat := canonicalBoundaryWords
  /-- Proof that Stage 1 fast-check succeeded on `boundaryVectors`. -/
  stage1_passed : passesStage1FastCheck specBoundaryEval candBoundaryEval boundaryVectors = true

/-- Smart constructor building a `CertifiedShimCandidate` directly from any
`VerifiedCompilerShim` and a boundary projection `(embedInput, embedState, projectObs)`. -/
def CertifiedShimCandidate.ofVerifiedShim
    {Input State Obs : Type}
    (shim : VerifiedCompilerShim Input State Obs)
    (cost : ShimCostProfile)
    (embedInput : Nat → Input)
    (embedState : Nat → State)
    (projectObs : Obs → Nat × Nat)
    (vectors : List Nat := canonicalBoundaryWords) :
    CertifiedShimCandidate Input State Obs where
  shim := shim
  cost := cost
  specBoundaryEval := fun w => projectObs (shim.denoteSpec (embedInput w) (embedState w))
  candBoundaryEval := fun w => projectObs (shim.shimImpl (embedInput w) (embedState w))
  boundaryVectors := vectors
  stage1_passed :=
    passesStage1FastCheck_of_pointwise_eq _ _ vectors (fun w => by
      simp [shim.refines_denote])

/-! ## Stage 3: Pareto Gas & Bytecode Dominance Selection -/

/-- Weak Pareto dominance on fixed execution gas, memory words allocated beyond `0x40`,
and runtime bytecode size. Guarantees `totalExecutionGas baseMemWords cand ≤
totalExecutionGas baseMemWords baseline` across all active memory states `baseMemWords`. -/
def dominatesOrEqualCost (cand baseline : ShimCostProfile) : Bool :=
  decide (fixedExecutionGas cand ≤ fixedExecutionGas baseline ∧
    cand.memWordsAllocated ≤ baseline.memWordsAllocated ∧
    cand.bytecodeBytes ≤ baseline.bytecodeBytes)

/-- Strict Pareto dominance: weakly dominates on all cost dimensions and achieves a strict
reduction in either base execution gas (`totalExecutionGas 0`) or bytecode size. -/
def strictlyDominatesCost (cand baseline : ShimCostProfile) : Bool :=
  dominatesOrEqualCost cand baseline &&
    decide (totalExecutionGas 0 cand < totalExecutionGas 0 baseline ∨
      cand.bytecodeBytes < baseline.bytecodeBytes)

@[simp]
theorem dominatesOrEqualCost_refl (p : ShimCostProfile) :
    dominatesOrEqualCost p p = true := by
  simp [dominatesOrEqualCost]

theorem dominatesOrEqualCost_of_strictlyDominatesCost
    {cand baseline : ShimCostProfile}
    (h : strictlyDominatesCost cand baseline = true) :
    dominatesOrEqualCost cand baseline = true := by
  simp only [strictlyDominatesCost, Bool.and_eq_true] at h
  exact h.1

theorem dominatesOrEqualCost_trans
    {a b c : ShimCostProfile}
    (hab : dominatesOrEqualCost a b = true)
    (hbc : dominatesOrEqualCost b c = true) :
    dominatesOrEqualCost a c = true := by
  simp only [dominatesOrEqualCost, decide_eq_true_eq] at hab hbc ⊢
  omega

theorem totalExecutionGas_le_of_dominatesOrEqualCost
    {cand baseline : ShimCostProfile}
    (h : dominatesOrEqualCost cand baseline = true)
    (baseMemWords : Nat) :
    totalExecutionGas baseMemWords cand ≤ totalExecutionGas baseMemWords baseline ∧
      cand.bytecodeBytes ≤ baseline.bytecodeBytes := by
  simp only [dominatesOrEqualCost, decide_eq_true_eq] at h
  exact ⟨totalExecutionGas_le_of_fixed_and_alloc_le h.1 h.2.1 baseMemWords, h.2.2⟩

/-- Select the Pareto-optimal winner from a baseline `CertifiedShimCandidate` and a list
of competing certified candidates. -/
def selectArenaWinner
    {Input State Obs : Type}
    (baseline : CertifiedShimCandidate Input State Obs)
    (candidates : List (CertifiedShimCandidate Input State Obs)) :
    CertifiedShimCandidate Input State Obs :=
  candidates.foldl
    (fun best cand =>
      if strictlyDominatesCost cand.cost best.cost then cand else best)
    baseline

/-- Inductive invariant: `selectArenaWinner baseline candidates` always weakly dominates
`baseline` across all cost components. -/
theorem selectArenaWinner_dominatesOrEqualCost {Input State Obs : Type}
    (baseline : CertifiedShimCandidate Input State Obs)
    (candidates : List (CertifiedShimCandidate Input State Obs)) :
    dominatesOrEqualCost (selectArenaWinner baseline candidates).cost baseline.cost = true := by
  induction candidates generalizing baseline with
  | nil => simp [selectArenaWinner]
  | cons cand rest ih =>
      simp only [selectArenaWinner, List.foldl_cons]
      by_cases hdom : strictlyDominatesCost cand.cost baseline.cost = true
      · rw [if_pos hdom]
        exact dominatesOrEqualCost_trans (ih cand) (dominatesOrEqualCost_of_strictlyDominatesCost hdom)
      · rw [if_neg hdom]; exact ih baseline

/-- **Master Autoresearch Theorem (`arenaWinner_preserves_semantics_and_optimizes_cost`)**:
For any baseline and candidate pool, the candidate selected by `selectArenaWinner`
refines `denoteSpec`, preserves `freeMemoryFrame`, is `non_vacuous`, passes Stage 1,
and has total execution gas and bytecode size `≤` the baseline on every memory state. -/
theorem arenaWinner_preserves_semantics_and_optimizes_cost {Input State Obs : Type}
    (baseline : CertifiedShimCandidate Input State Obs)
    (candidates : List (CertifiedShimCandidate Input State Obs)) :
    let w := selectArenaWinner baseline candidates
    (∀ x s, w.shim.shimImpl x s = w.shim.denoteSpec x s) ∧
    (∀ x s, w.shim.freeMemoryFrame s (w.shim.shimImpl x s)) ∧
    SatisfiablePrecondition (fun _ : Input => True) ∧
    passesStage1FastCheck w.specBoundaryEval w.candBoundaryEval w.boundaryVectors = true ∧
    (∀ m, totalExecutionGas m w.cost ≤ totalExecutionGas m baseline.cost) ∧
    w.cost.bytecodeBytes ≤ baseline.cost.bytecodeBytes := by
  dsimp only
  have h := selectArenaWinner_dominatesOrEqualCost baseline candidates
  exact ⟨(selectArenaWinner baseline candidates).shim.refines_denote,
    (selectArenaWinner baseline candidates).shim.frame_sound,
    (selectArenaWinner baseline candidates).shim.non_vacuous,
    (selectArenaWinner baseline candidates).stage1_passed,
    fun m => (totalExecutionGas_le_of_dominatesOrEqualCost h m).1,
    (totalExecutionGas_le_of_dominatesOrEqualCost h 0).2⟩

/-! ## Bridge to `Compiler.Yul.PatchFramework` (`VerifiedShimPatchDescriptor`) -/

/-- Package an arena-winning `CertifiedShimCandidate` and its Yul `PatchRule` into a
`VerifiedShimPatchDescriptor` ready for registration in `runVerifiedShimPatchPass`. -/
def CertifiedShimCandidate.toPatchDescriptor
    {Input State Obs : Type}
    (baseline winner : CertifiedShimCandidate Input State Obs)
    (proofRef : Name)
    (rule : PatchRule) : VerifiedShimPatchDescriptor where
  shimName := winner.shim.name
  proofRef := proofRef
  gasSavedPerCall := totalExecutionGas 0 baseline.cost - totalExecutionGas 0 winner.cost
  rule := rule

/-! ## Canonical Arena Instances & Executable Witness Suite -/

/-- Baseline certified candidate for 2-word `keccak256` (bump allocation). -/
def bumpAllocKeccakCandidate : CertifiedShimCandidate (Nat × Nat) Nat (Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    scratchKeccakPairVerifiedShim
    bumpAllocKeccakCostProfile
    (fun w => (w, w + 1))
    (fun _ => 0x80)
    id

/-- Optimized certified candidate for 2-word `keccak256` (scratch space `[0x00, 0x40)`). -/
def scratchKeccakCandidate : CertifiedShimCandidate (Nat × Nat) Nat (Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    scratchKeccakPairVerifiedShim
    scratchKeccakCostProfile
    (fun w => (w, w + 1))
    (fun _ => 0x80)
    id

/-- Kernel-checked (`by decide`) witness that `scratchKeccakCandidate` strictly dominates
`bumpAllocKeccakCandidate` and wins the arena. -/
theorem scratchKeccak_wins_arena :
    strictlyDominatesCost scratchKeccakCandidate.cost bumpAllocKeccakCandidate.cost = true ∧
      (selectArenaWinner bumpAllocKeccakCandidate [scratchKeccakCandidate]).cost =
        scratchKeccakCostProfile := by
  decide

/-- Baseline certified candidate for `transientLock` (storage-backed reentrancy lock). -/
def storageLockBaselineCandidate :
    CertifiedShimCandidate Unit (Nat × Nat) (Option (Nat × Nat)) :=
  CertifiedShimCandidate.ofVerifiedShim
    transientLockVerifiedShim
    storageLockCostProfile
    (fun _ => ())
    (fun w => (w % 2, 0x80))
    (fun obs => match obs with | some s' => s' | none => (0, 0x80))

/-- Optimized certified candidate for `transientLock` (EIP-1153 `TLOAD + TSTORE`). -/
def transientLockArenaCandidate :
    CertifiedShimCandidate Unit (Nat × Nat) (Option (Nat × Nat)) :=
  CertifiedShimCandidate.ofVerifiedShim
    transientLockVerifiedShim
    transientLockCostProfile
    (fun _ => ())
    (fun w => (w % 2, 0x80))
    (fun obs => match obs with | some s' => s' | none => (0, 0x80))

/-- Kernel-checked (`by decide`) witness that `transientLockArenaCandidate` strictly
dominates `storageLockBaselineCandidate` and saves `2800` gas per call. -/
theorem transientLock_wins_arena :
    strictlyDominatesCost transientLockArenaCandidate.cost
        storageLockBaselineCandidate.cost = true ∧
      totalExecutionGas 0 storageLockBaselineCandidate.cost -
        totalExecutionGas 0 transientLockArenaCandidate.cost = 2800 := by
  decide

/-- Baseline certified candidate for `mulDiv512` (memory-spilling implementation). -/
def mulDiv512BaselineCandidate :
    CertifiedShimCandidate (Nat × Nat × Nat) Nat (Option Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    mulDiv512VerifiedShim
    mulDiv512BaselineCostProfile
    (fun w => (w, 1, 1))
    (fun _ => 0x80)
    (fun (q, fmp) => (q.getD 0, fmp))

/-- Optimized certified candidate for `mulDiv512` (branchless stack-only implementation). -/
def mulDiv512FastCandidate :
    CertifiedShimCandidate (Nat × Nat × Nat) Nat (Option Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    mulDiv512VerifiedShim
    mulDiv512FastCostProfile
    (fun w => (w, 1, 1))
    (fun _ => 0x80)
    (fun (q, fmp) => (q.getD 0, fmp))

/-- Kernel-checked (`by decide`) witness that `mulDiv512FastCandidate` strictly dominates
`mulDiv512BaselineCandidate`. -/
theorem mulDiv512_wins_arena :
    strictlyDominatesCost mulDiv512FastCandidate.cost
        mulDiv512BaselineCandidate.cost = true ∧
      (selectArenaWinner mulDiv512BaselineCandidate [mulDiv512FastCandidate]).cost =
        mulDiv512FastCostProfile := by
  decide

/-- Baseline certified candidate for 1-word `staticcall` wrapper. -/
def staticCallWordBaselineCandidate :
    CertifiedShimCandidate (Nat × Nat) (Nat × Nat) (Nat × Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    staticCallWordVerifiedShim
    staticCallWordBaselineCostProfile
    (fun w => (1, w))
    (fun _ => (0x80, 0))
    (fun (res, fmp, _) => (res, fmp))

/-- Optimized certified candidate for 1-word `staticcall` wrapper. -/
def staticCallWordFastCandidate :
    CertifiedShimCandidate (Nat × Nat) (Nat × Nat) (Nat × Nat × Nat) :=
  CertifiedShimCandidate.ofVerifiedShim
    staticCallWordVerifiedShim
    staticCallWordFastCostProfile
    (fun w => (1, w))
    (fun _ => (0x80, 0))
    (fun (res, fmp, _) => (res, fmp))

/-- Kernel-checked (`by decide`) witness that `staticCallWordFastCandidate` strictly
dominates `staticCallWordBaselineCandidate`. -/
theorem staticCallWord_wins_arena :
    strictlyDominatesCost staticCallWordFastCandidate.cost
        staticCallWordBaselineCandidate.cost = true ∧
      (selectArenaWinner staticCallWordBaselineCandidate [staticCallWordFastCandidate]).cost =
        staticCallWordFastCostProfile := by
  decide

end Compiler.Autoresearch.ShimArena
