import Compiler.CompilationModel.Types
import Compiler.CompilationModel.Compile

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-!
# Layer-2 Core Fragment Extension: Bitwise Set-Bit Loops (`Stmt.forEachSetBit`) and Dynamic Storage Arrays (`G2`)

This module extends the proven Layer-2 core fragment with two self-contained
semantic and algebraic proof surfaces without modifying cached root modules:

1. **Bitwise Set-Bit Iteration (`Stmt.forEachSetBit`)**:
   - Canonical set-bit index extraction `setBitIndices` and descending counterpart
     `setBitIndicesDesc` over bounded bit widths (`maxBits := 256`).
   - Structural lemmas on set-bit indices (`setBitIndices_zero_bits`,
     `setBitIndices_zero_bitmap`, `setBitIndices_length_le_maxBits`,
     `mem_setBitIndices_iff`, `setBitIndices_pairwise_lt`, `setBitIndices_succ`).
   - Operational loop semantics `execForEachSetBitStep` and `execForEachSetBit`
     with composition laws (`execForEachSetBit_nil`, `execForEachSetBit_cons`,
     `execForEachSetBit_append`), scope extension lemmas for
     `forEachSetBitBodyScope` / `forEachSetBitFallbackBodyScope`, and universal
     Layer-2 inductive simulation preservation theorems
     (`forEachSetBit_preserves_simulation`, `forEachSetBit_forward_simulation`,
     `forEachSetBit_optionRel_simulation`).

2. **Dynamic Storage Arrays (`storageArrayLength`, `storageArrayElement`,
   `storageArrayPush`, `storageArrayPop`, `setStorageArrayElement`)**:
   - EVM storage array slot geometry (`dataStartSlot`, `elementSlot`) with slot
     injectivity and base-slot disjointness theorems.
   - Total abstract model `StorageArrayModel` with operations `length`,
     `getElem?`, `push`, `pop?`, and `setElem?`, plus full algebraic theory
     (`length_push`, `getElem?_push_last`, `getElem?_push_lt`,
     `pop?_none_of_nil`, `length_pop?_of_cons`, `pop?_push_cancel`,
     `getElem?_setElem?_same`, `getElem?_setElem?_other`).
   - Slot-level refinement relation `StorageArraySlotRefines`, compiler lowering
     characterizations (`compileStorageArrayPush_eq`, `compileStorageArrayPop_eq`),
     and Layer-2 refinement preservation theorems
     (`storageArrayPush_preserves_slotRefines`,
     `storageArrayPop_preserves_slotRefines`,
     `setStorageArrayElement_preserves_slotRefines`).
-/

/-! ## Section 1: Bitwise Set-Bit Iteration (`Stmt.forEachSetBit`) Semantics & Bounded Induction -/

/-- Test whether bit `i` of `bitmap` is set (`((bitmap >>> i) &&& 1) == 1`). -/
def isBitSet (bitmap i : Nat) : Bool :=
  ((bitmap >>> i) &&& 1) == 1

/-- Ascending list of bit indices `i ∈ [0, maxBits)` where `(bitmap >>> i) &&& 1 == 1`. -/
def setBitIndices (bitmap : Nat) (maxBits : Nat := 256) : List Nat :=
  (List.range maxBits).filter (fun i => ((bitmap >>> i) &&& 1) == 1)

/-- Descending (MSB-to-LSB) list of set-bit indices in `[0, maxBits)`, matching the
EIP-7939 `clz` iteration order of `Stmt.forEachSetBit`. -/
def setBitIndicesDesc (bitmap : Nat) (maxBits : Nat := 256) : List Nat :=
  (setBitIndices bitmap maxBits).reverse

/-- When `maxBits = 0`, `setBitIndices` produces the empty list. -/
@[simp] theorem setBitIndices_zero_bits {bitmap : Nat} :
    setBitIndices bitmap 0 = [] :=
  rfl

/-- For a zero bitmap, no bit is set in `[0, maxBits)`, so `setBitIndices 0 maxBits = []`. -/
@[simp] theorem setBitIndices_zero_bitmap {maxBits : Nat} :
    setBitIndices 0 maxBits = [] := by
  simp [setBitIndices, Nat.zero_shiftRight]

/-- The number of set-bit indices in `[0, maxBits)` never exceeds `maxBits`. -/
theorem setBitIndices_length_le_maxBits {bitmap maxBits : Nat} :
    (setBitIndices bitmap maxBits).length ≤ maxBits := by
  calc
    (setBitIndices bitmap maxBits).length ≤ (List.range maxBits).length :=
      List.length_filter_le _ _
    _ = maxBits := List.length_range

/-- Exact membership characterization for `setBitIndices`. -/
theorem mem_setBitIndices_iff {bitmap maxBits i : Nat} :
    i ∈ setBitIndices bitmap maxBits ↔ i < maxBits ∧ ((bitmap >>> i) &&& 1 == 1) = true := by
  simp [setBitIndices, List.mem_filter, List.mem_range]

/-- Every index returned by `setBitIndices bitmap maxBits` is strictly less than `maxBits`. -/
theorem setBitIndices_lt_maxBits {bitmap maxBits i : Nat}
    (hi : i ∈ setBitIndices bitmap maxBits) :
    i < maxBits :=
  (mem_setBitIndices_iff.mp hi).1

/-- Every index returned by `setBitIndices bitmap maxBits` has bit `i` set in `bitmap`. -/
theorem setBitIndices_bit_eq_one {bitmap maxBits i : Nat}
    (hi : i ∈ setBitIndices bitmap maxBits) :
    ((bitmap >>> i) &&& 1 == 1) = true :=
  (mem_setBitIndices_iff.mp hi).2

/-- The list of set-bit indices is strictly ascending (`List.Pairwise (· < ·)`). -/
theorem setBitIndices_pairwise_lt {bitmap maxBits : Nat} :
    List.Pairwise (· < ·) (setBitIndices bitmap maxBits) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- `setBitIndicesDesc` has the same bounded length as `setBitIndices`. -/
theorem setBitIndicesDesc_length_le_maxBits {bitmap maxBits : Nat} :
    (setBitIndicesDesc bitmap maxBits).length ≤ maxBits := by
  simpa [setBitIndicesDesc] using @setBitIndices_length_le_maxBits bitmap maxBits

/-- Membership in `setBitIndicesDesc` coincides with membership in `setBitIndices`. -/
theorem mem_setBitIndicesDesc_iff {bitmap maxBits i : Nat} :
    i ∈ setBitIndicesDesc bitmap maxBits ↔ i ∈ setBitIndices bitmap maxBits := by
  simp [setBitIndicesDesc]

/-- The Osaka `forEachSetBitBodyScope` includes the bound loop variable `varName`. -/
theorem mem_forEachSetBitBodyScope_varName (inScopeNames : List String)
    (varName : String) (bitmap : Expr) (body : List Stmt) :
    varName ∈ forEachSetBitBodyScope inScopeNames varName bitmap body := by
  simp [forEachSetBitBodyScope]

/-- The fallback `forEachSetBitFallbackBodyScope` includes the bound loop variable `varName`. -/
theorem mem_forEachSetBitFallbackBodyScope_varName (inScopeNames : List String)
    (varName : String) (bitmap : Expr) (body : List Stmt) :
    varName ∈ forEachSetBitFallbackBodyScope inScopeNames varName bitmap body := by
  simp [forEachSetBitFallbackBodyScope]

/-- The Osaka `forEachSetBitBodyScope` preserves all outer in-scope bindings. -/
theorem subset_forEachSetBitBodyScope (inScopeNames : List String)
    (varName : String) (bitmap : Expr) (body : List Stmt) {x : String}
    (hx : x ∈ inScopeNames) :
    x ∈ forEachSetBitBodyScope inScopeNames varName bitmap body := by
  simp [forEachSetBitBodyScope, hx]

/-- The fallback `forEachSetBitFallbackBodyScope` preserves all outer in-scope bindings. -/
theorem subset_forEachSetBitFallbackBodyScope (inScopeNames : List String)
    (varName : String) (bitmap : Expr) (body : List Stmt) {x : String}
    (hx : x ∈ inScopeNames) :
    x ∈ forEachSetBitFallbackBodyScope inScopeNames varName bitmap body := by
  simp [forEachSetBitFallbackBodyScope, hx]

/-- Execute a `Stmt.forEachSetBit` loop over an explicit list of set-bit indices.
`bitVar` names the bound bit-index variable, and `stepBody i s` executes one
iteration for bit index `i` from state `s`. -/
def execForEachSetBitStep {State : Type} (bitVar : String) (indices : List Nat)
    (stepBody : Nat → State → Option State) (s : State) : Option State :=
  match indices with
  | [] => some s
  | i :: rest =>
      match stepBody i s with
      | some s' => execForEachSetBitStep bitVar rest stepBody s'
      | none => none

/-- Execute a `Stmt.forEachSetBit` loop over all set bits of `bitmap` in `[0, maxBits)`. -/
def execForEachSetBit {State : Type} (bitVar : String) (bitmap : Nat)
    (maxBits : Nat := 256) (stepBody : Nat → State → Option State) (s : State) :
    Option State :=
  execForEachSetBitStep bitVar (setBitIndices bitmap maxBits) stepBody s

/-- Executing `execForEachSetBitStep` over an empty index list returns `some s`. -/
@[simp] theorem execForEachSetBit_nil {State : Type} (bitVar : String)
    (stepBody : Nat → State → Option State) (s : State) :
    execForEachSetBitStep bitVar [] stepBody s = some s :=
  rfl

/-- Executing `execForEachSetBitStep` on `i :: rest` runs `stepBody i s` and
continues with `rest` on `some s'`. -/
@[simp] theorem execForEachSetBit_cons {State : Type} (bitVar : String)
    {i : Nat} (rest : List Nat) (stepBody : Nat → State → Option State) (s : State) :
    execForEachSetBitStep bitVar (i :: rest) stepBody s =
      match stepBody i s with
      | some s' => execForEachSetBitStep bitVar rest stepBody s'
      | none => none :=
  rfl

/-- Sequential composition law for `execForEachSetBitStep` over concatenated index lists. -/
theorem execForEachSetBit_append {State : Type} (bitVar : String)
    (xs ys : List Nat) (stepBody : Nat → State → Option State) (s : State) :
    execForEachSetBitStep bitVar (xs ++ ys) stepBody s =
      match execForEachSetBitStep bitVar xs stepBody s with
      | some s' => execForEachSetBitStep bitVar ys stepBody s'
      | none => none := by
  induction xs generalizing s with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.cons_append, execForEachSetBit_cons]
      cases stepBody x s with
      | none => rfl
      | some s' => exact ih s'

/-- Option-lifted state simulation relation: `none` relates to `none` (matched
revert/abort) and `some a` relates to `some b` when `R a b`. -/
def OptionSimulation {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- Predicate asserting that single-step execution `step i` from `s` yields `some s'`. -/
def StepTerminatesAt {State : Type} (step : Nat → State → Option State)
    (i : Nat) (s s' : State) : Prop :=
  step i s = some s'

/-- Predicate asserting that `execForEachSetBitStep bitVar indices step s` terminates
with `some s'`. -/
def LoopTerminatesAt {State : Type} (bitVar : String) (indices : List Nat)
    (step : Nat → State → Option State) (s s' : State) : Prop :=
  execForEachSetBitStep bitVar indices step s = some s'

/-- Inductive invariant preservation along any list of bit indices `indices`. -/
theorem execForEachSetBitStep_preserves_invariant {State : Type}
    (P : State → Prop) (bitVar : String) (indices : List Nat)
    (stepBody : Nat → State → Option State)
    (hstep : ∀ i ∈ indices, ∀ s s', P s → StepTerminatesAt stepBody i s s' → P s') :
    ∀ {s s' : State}, P s →
      LoopTerminatesAt bitVar indices stepBody s s' → P s' := by
  induction indices with
  | nil =>
      intro s s' hp hexec
      simp only [LoopTerminatesAt, execForEachSetBit_nil, Option.some.injEq] at hexec
      exact hexec ▸ hp
  | cons i rest ih =>
      intro s s' hp hexec
      simp only [LoopTerminatesAt, execForEachSetBit_cons] at hexec
      cases hbody : stepBody i s with
      | none =>
          rw [hbody] at hexec
          cases hexec
      | some smid =>
          rw [hbody] at hexec
          have hmid : P smid :=
            hstep i List.mem_cons_self s smid hp hbody
          exact ih (fun j hj => hstep j (List.mem_cons_of_mem i hj)) hmid hexec

/-- Universal inductive simulation preservation over an arbitrary index list `indices`:
if `srcStep` and `irStep` preserve the source-to-IR simulation relation `R` at every
index `i ∈ indices`, then `execForEachSetBitStep` preserves `R` from initial states
`s₀, t₀` to final states `s_final, t_final`. -/
theorem execForEachSetBitStep_preserves_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (indices : List Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hsim : ∀ i ∈ indices, ∀ s t s' t',
      R s t → StepTerminatesAt srcStep i s s' → StepTerminatesAt irStep i t t' → R s' t') :
    ∀ {s₀ s_final : α} {t₀ t_final : β},
      R s₀ t₀ →
      LoopTerminatesAt bitVar indices srcStep s₀ s_final →
      LoopTerminatesAt bitVar indices irStep t₀ t_final →
      R s_final t_final := by
  induction indices with
  | nil =>
      intro s₀ s_final t₀ t_final hr hsrc hir
      simp only [LoopTerminatesAt, execForEachSetBit_nil, Option.some.injEq] at hsrc hir
      subst hsrc; subst hir
      exact hr
  | cons i rest ih =>
      intro s₀ s_final t₀ t_final hr hsrc hir
      simp only [LoopTerminatesAt, execForEachSetBit_cons] at hsrc hir
      cases h1 : srcStep i s₀ with
      | none => rw [h1] at hsrc; cases hsrc
      | some s₁ =>
          rw [h1] at hsrc
          cases h2 : irStep i t₀ with
          | none => rw [h2] at hir; cases hir
          | some t₁ =>
              rw [h2] at hir
              have hr₁ : R s₁ t₁ :=
                hsim i List.mem_cons_self s₀ t₀ s₁ t₁ hr h1 h2
              exact ih (fun j hj => hsim j (List.mem_cons_of_mem i hj)) hr₁ hsrc hir

/-- Universal Layer-2 simulation preservation theorem for `Stmt.forEachSetBit`:
if the loop body preserves the source-to-IR simulation relation `R` for every set
bit index `i ∈ setBitIndices bitmap maxBits`, then the entire `forEachSetBit` loop
preserves `R`. -/
theorem forEachSetBit_preserves_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (bitmap maxBits : Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hsim : ∀ i ∈ setBitIndices bitmap maxBits, ∀ s t s' t',
      R s t → StepTerminatesAt srcStep i s s' → StepTerminatesAt irStep i t t' → R s' t')
    {s₀ s_final : α} {t₀ t_final : β}
    (hinit : R s₀ t₀)
    (hsrc : LoopTerminatesAt bitVar (setBitIndices bitmap maxBits) srcStep s₀ s_final)
    (hir : LoopTerminatesAt bitVar (setBitIndices bitmap maxBits) irStep t₀ t_final) :
    R s_final t_final :=
  execForEachSetBitStep_preserves_simulation R bitVar (setBitIndices bitmap maxBits)
    srcStep irStep hsim hinit hsrc hir

/-- Forward simulation helper over an arbitrary index list `indices`. -/
theorem execForEachSetBitStep_forward_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (indices : List Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hfwd : ∀ i ∈ indices, ∀ s t s',
      R s t → StepTerminatesAt srcStep i s s' → ∃ t', StepTerminatesAt irStep i t t' ∧ R s' t') :
    ∀ {s₀ s_final : α} {t₀ : β},
      R s₀ t₀ →
      LoopTerminatesAt bitVar indices srcStep s₀ s_final →
      ∃ t_final,
        LoopTerminatesAt bitVar indices irStep t₀ t_final ∧
        R s_final t_final := by
  induction indices with
  | nil =>
      intro s₀ s_final t₀ hinit hsrc
      simp only [LoopTerminatesAt, execForEachSetBit_nil, Option.some.injEq] at hsrc
      subst hsrc
      exact ⟨t₀, rfl, hinit⟩
  | cons i rest ih =>
      intro s₀ s_final t₀ hinit hsrc
      simp only [LoopTerminatesAt, execForEachSetBit_cons] at hsrc
      cases h1 : srcStep i s₀ with
      | none => rw [h1] at hsrc; cases hsrc
      | some s₁ =>
          rw [h1] at hsrc
          obtain ⟨t₁, h2, hr₁⟩ :=
            hfwd i List.mem_cons_self s₀ t₀ s₁ hinit h1
          obtain ⟨t_final, hirRest, hrFinal⟩ :=
            ih (fun j hj => hfwd j (List.mem_cons_of_mem i hj)) hr₁ hsrc
          refine ⟨t_final, ?_, hrFinal⟩
          simp only [LoopTerminatesAt, execForEachSetBit_cons]
          rw [h2]
          exact hirRest

/-- Forward simulation theorem for `Stmt.forEachSetBit`: if every set-bit iteration
step forward-simulates `srcStep` by `irStep` under `R`, then any terminating source
`forEachSetBit` execution produces a matching terminating IR execution in relation `R`. -/
theorem forEachSetBit_forward_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (bitmap maxBits : Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hfwd : ∀ i ∈ setBitIndices bitmap maxBits, ∀ s t s',
      R s t → StepTerminatesAt srcStep i s s' → ∃ t', StepTerminatesAt irStep i t t' ∧ R s' t') :
    ∀ {s₀ s_final : α} {t₀ : β},
      R s₀ t₀ →
      LoopTerminatesAt bitVar (setBitIndices bitmap maxBits) srcStep s₀ s_final →
      ∃ t_final,
        LoopTerminatesAt bitVar (setBitIndices bitmap maxBits) irStep t₀ t_final ∧
        R s_final t_final :=
  execForEachSetBitStep_forward_simulation R bitVar (setBitIndices bitmap maxBits)
    srcStep irStep hfwd

/-- Total lockstep `OptionSimulation` preservation over an arbitrary index list `indices`. -/
theorem execForEachSetBitStep_optionRel_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (indices : List Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hstep : ∀ i ∈ indices, ∀ s t,
      R s t → OptionSimulation R (srcStep i s) (irStep i t)) :
    ∀ {s₀ : α} {t₀ : β}, R s₀ t₀ →
      OptionSimulation R
        (execForEachSetBitStep bitVar indices srcStep s₀)
        (execForEachSetBitStep bitVar indices irStep t₀) := by
  induction indices with
  | nil =>
      intro s₀ t₀ hinit
      exact hinit
  | cons i rest ih =>
      intro s₀ t₀ hinit
      simp only [execForEachSetBit_cons]
      have hcur := hstep i List.mem_cons_self s₀ t₀ hinit
      cases h1 : srcStep i s₀ <;> cases h2 : irStep i t₀
      · trivial
      · rw [h1, h2] at hcur; exact False.elim hcur
      · rw [h1, h2] at hcur; exact False.elim hcur
      · rename_i s₁ t₁
        rw [h1, h2] at hcur
        exact ih (fun j hj => hstep j (List.mem_cons_of_mem i hj)) hcur

/-- Total lockstep `OptionSimulation` preservation over `setBitIndices bitmap maxBits`,
covering both successful completion (`some`) and reverting executions (`none`). -/
theorem forEachSetBit_optionRel_simulation {α β : Type}
    (R : α → β → Prop) (bitVar : String) (bitmap maxBits : Nat)
    (srcStep : Nat → α → Option α) (irStep : Nat → β → Option β)
    (hstep : ∀ i ∈ setBitIndices bitmap maxBits, ∀ s t,
      R s t → OptionSimulation R (srcStep i s) (irStep i t))
    {s₀ : α} {t₀ : β} (hinit : R s₀ t₀) :
    OptionSimulation R
      (execForEachSetBitStep bitVar (setBitIndices bitmap maxBits) srcStep s₀)
      (execForEachSetBitStep bitVar (setBitIndices bitmap maxBits) irStep t₀) :=
  execForEachSetBitStep_optionRel_simulation R bitVar (setBitIndices bitmap maxBits)
    srcStep irStep hstep hinit

/-! ## Section 2: Dynamic Storage Arrays (`storageArrayLength`, `storageArrayElement`, `storageArrayPush`, `storageArrayPop`, `setStorageArrayElement`) -/

/-- Starting slot for the contiguous element region of a dynamic storage array
rooted at `baseSlot`. Offset by `2^128` from `baseSlot` to model the non-aliasing
Solidity `keccak256(abi.encode(baseSlot))` data region while remaining purely
arithmetical and axiom-free. -/
def dataStartSlot (baseSlot : Nat) : Nat :=
  baseSlot + 2 ^ 128

/-- Storage slot of element `idx` in the dynamic storage array rooted at `baseSlot`. -/
def elementSlot (baseSlot idx : Nat) : Nat :=
  dataStartSlot baseSlot + idx

/-- Distinct element indices map to distinct storage slots. -/
@[simp] theorem elementSlot_inj {baseSlot i j : Nat} :
    elementSlot baseSlot i = elementSlot baseSlot j ↔ i = j := by
  simp [elementSlot]

/-- The array length slot `baseSlot` never aliases any element slot `elementSlot baseSlot idx`. -/
theorem baseSlot_ne_elementSlot (baseSlot idx : Nat) :
    baseSlot ≠ elementSlot baseSlot idx := by
  simp [elementSlot, dataStartSlot]
  omega

/-- Abstract Layer-2 model of a dynamic storage array as a finite list of 256-bit words. -/
structure StorageArrayModel where
  /-- Current elements of the dynamic storage array in index order. -/
  elems : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace StorageArrayModel

/-- Number of elements currently stored in the dynamic array (`Expr.storageArrayLength`). -/
def length (arr : StorageArrayModel) : Nat :=
  arr.elems.length

/-- Checked element read at index `idx` (`Expr.storageArrayElement`), returning `none`
when `idx ≥ arr.length`. -/
def getElem? (arr : StorageArrayModel) (idx : Nat) : Option Nat :=
  arr.elems[idx]?

/-- Append a word `val` to the end of the dynamic array (`Stmt.storageArrayPush`). -/
def push (arr : StorageArrayModel) (val : Nat) : StorageArrayModel :=
  ⟨arr.elems ++ [val]⟩

/-- Pop the last element of the dynamic array (`Stmt.storageArrayPop`), returning
`none` (revert) when the array is empty. -/
def pop? (arr : StorageArrayModel) : Option StorageArrayModel :=
  if arr.elems.isEmpty then
    none
  else
    some ⟨arr.elems.dropLast⟩

/-- Checked in-place element update (`Stmt.setStorageArrayElement`), returning
`none` (revert) when `idx ≥ arr.length`. -/
def setElem? (arr : StorageArrayModel) (idx val : Nat) : Option StorageArrayModel :=
  if idx < arr.elems.length then
    some ⟨arr.elems.set idx val⟩
  else
    none

/-- Type alias for storage array indices (definitionally `Nat`). -/
abbrev ArrayIndex := Nat

/-- Type alias for storage array element words (definitionally `Nat`). -/
abbrev ArrayWord := Nat

/-- Pushing an element increments the array length by 1. -/
@[simp] theorem length_push (arr : StorageArrayModel) (val : ArrayWord) :
    (arr.push val).length = arr.length + 1 := by
  simp [push, length]

/-- Reading at index `arr.length` immediately after `arr.push val` yields `some val`. -/
@[simp] theorem getElem?_push_last (arr : StorageArrayModel) (val : ArrayWord) :
    (arr.push val).getElem? arr.length = some val := by
  simp [push, getElem?, length]

/-- Pushing an element preserves all existing elements at indices `idx < arr.length`. -/
theorem getElem?_push_lt (arr : StorageArrayModel) (val : ArrayWord) {idx : ArrayIndex}
    (hidx : idx < arr.length) :
    (arr.push val).getElem? idx = arr.getElem? idx := by
  simp [push, getElem?, length] at hidx ⊢
  rw [List.getElem?_append_left hidx]

/-- Popping an empty storage array fails (`none`). -/
@[simp] theorem pop?_none_of_nil :
    (⟨[]⟩ : StorageArrayModel).pop? = none :=
  rfl

/-- Popping a non-empty storage array `⟨x :: xs⟩` succeeds and yields length `xs.length`. -/
theorem length_pop?_of_cons (x : ArrayWord) (xs : List Nat) :
    ((⟨x :: xs⟩ : StorageArrayModel).pop?.map StorageArrayModel.length) =
      some xs.length := by
  simp [pop?, length]

/-- Popping immediately after `push` recovers the original `StorageArrayModel`. -/
@[simp] theorem pop?_push_cancel (arr : StorageArrayModel) (val : ArrayWord) :
    (arr.push val).pop? = some arr := by
  cases arr with
  | mk elems => simp [push, pop?]

/-- `setElem?` succeeds iff `idx < arr.length`. -/
theorem setElem?_isSome_iff (arr : StorageArrayModel) (idx : ArrayIndex) (val : ArrayWord) :
    (arr.setElem? idx val).isSome ↔ idx < arr.length := by
  simp [setElem?, length]

/-- Updating index `idx` via `setElem?` preserves the array length. -/
theorem length_setElem? {arr arr' : StorageArrayModel} {idx : ArrayIndex} {val : ArrayWord}
    (hset : arr.setElem? idx val = some arr') :
    arr'.length = arr.length := by
  simp only [setElem?] at hset
  split at hset
  · injection hset with h; subst h; simp [length]
  · cases hset

/-- Reading at the updated index `idx` after `setElem?` returns `some val`. -/
theorem getElem?_setElem?_same {arr arr' : StorageArrayModel} {idx : ArrayIndex} {val : ArrayWord}
    (hset : arr.setElem? idx val = some arr') :
    arr'.getElem? idx = some val := by
  simp only [setElem?] at hset
  split at hset
  · rename_i hlt
    injection hset with h; subst h
    simp [getElem?, hlt]
  · cases hset

/-- Reading at any other index `j ≠ idx` after `setElem?` returns the original element. -/
theorem getElem?_setElem?_other {arr arr' : StorageArrayModel} {idx j : ArrayIndex} {val : ArrayWord}
    (hset : arr.setElem? idx val = some arr') (hne : j ≠ idx) :
    arr'.getElem? j = arr.getElem? j := by
  simp only [setElem?] at hset
  split at hset
  · injection hset with h; subst h
    simp [getElem?, List.getElem?_set_ne (Ne.symm hne)]
  · cases hset

end StorageArrayModel

/-- Slot-level refinement relation between an abstract `StorageArrayModel` and
flat EVM storage `storage : Nat → Nat` at `baseSlot`:
1. `storage baseSlot = arr.elems.length`
2. For every index `i < arr.elems.length`, `storage (elementSlot baseSlot i) = arr.elems[i]`. -/
structure StorageArraySlotRefines (baseSlot : Nat) (arr : StorageArrayModel)
    (storage : Nat → Nat) : Prop where
  /-- The base slot stores the current array length. -/
  length_eq : storage baseSlot = arr.elems.length
  /-- Each active element slot `elementSlot baseSlot i` stores `arr.elems[i]`. -/
  slot_eq : ∀ i (hi : i < arr.elems.length),
    storage (elementSlot baseSlot i) = arr.elems[i]

/-- Functional flat-storage update at a single slot (`sstore(slot, val)`). -/
def storageWrite (storage : Nat → Nat) (slot val : Nat) : Nat → Nat :=
  fun s => if s = slot then val else storage s

/-- Slot-level execution of `Expr.storageArrayLength` (`sload(baseSlot)`). -/
def evalStorageArrayLengthSlots (baseSlot : Nat) (storage : Nat → Nat) : Nat :=
  storage baseSlot

/-- Slot-level execution of `Expr.storageArrayElement` (bounds check against
`sload(baseSlot)` followed by `sload(elementSlot baseSlot idx)`). -/
def evalStorageArrayElementSlots (baseSlot idx : Nat) (storage : Nat → Nat) : Option Nat :=
  if idx < storage baseSlot then
    some (storage (elementSlot baseSlot idx))
  else
    none

/-- Slot-level execution of `Stmt.storageArrayPush` matching `compileStorageArrayPush`:
writes `val` at `elementSlot baseSlot (storage baseSlot)` and increments `storage baseSlot`. -/
def execStorageArrayPushSlots (baseSlot val : Nat) (storage : Nat → Nat) : Nat → Nat :=
  let len := storage baseSlot
  let s1 := storageWrite storage (elementSlot baseSlot len) val
  storageWrite s1 baseSlot (len + 1)

/-- Slot-level execution of `Stmt.storageArrayPop` matching `compileStorageArrayPop`:
reverts (`none`) when `storage baseSlot = 0`, otherwise zeroes the last element slot
and decrements `storage baseSlot`. -/
def execStorageArrayPopSlots (baseSlot : Nat) (storage : Nat → Nat) : Option (Nat → Nat) :=
  let len := storage baseSlot
  if len = 0 then
    none
  else
    let newLen := len - 1
    let s1 := storageWrite storage (elementSlot baseSlot newLen) 0
    some (storageWrite s1 baseSlot newLen)

/-- Slot-level execution of `Stmt.setStorageArrayElement` matching
`compileSetStorageArrayElement`: checks `idx < storage baseSlot` and writes `val`
to `elementSlot baseSlot idx`. -/
def execSetStorageArrayElementSlots (baseSlot idx val : Nat) (storage : Nat → Nat) :
    Option (Nat → Nat) :=
  if idx < storage baseSlot then
    some (storageWrite storage (elementSlot baseSlot idx) val)
  else
    none

/-- Type alias for EVM storage slot indices (definitionally `Nat`). -/
abbrev StorageSlotIdx := Nat

/-- Under `StorageArraySlotRefines`, `evalStorageArrayLengthSlots` equals `arr.length`. -/
theorem evalStorageArrayLengthSlots_eq_length {baseSlot : StorageSlotIdx} {arr : StorageArrayModel}
    {storage : Nat → Nat} (href : StorageArraySlotRefines baseSlot arr storage) :
    evalStorageArrayLengthSlots baseSlot storage = arr.length := by
  simpa [evalStorageArrayLengthSlots, StorageArrayModel.length] using href.length_eq

/-- Under `StorageArraySlotRefines`, `evalStorageArrayElementSlots` coincides with
`arr.getElem?` at every index `idx`. -/
theorem evalStorageArrayElementSlots_eq_getElem? {baseSlot idx : StorageSlotIdx} {arr : StorageArrayModel}
    {storage : Nat → Nat} (href : StorageArraySlotRefines baseSlot arr storage) :
    evalStorageArrayElementSlots baseSlot idx storage = arr.getElem? idx := by
  simp only [evalStorageArrayElementSlots, StorageArrayModel.getElem?, href.length_eq]
  split
  · rename_i hlt
    rw [href.slot_eq idx hlt, List.getElem?_eq_getElem hlt]
  · rename_i hge
    symm
    exact List.getElem?_eq_none (Nat.le_of_not_lt hge)

/-- `Stmt.storageArrayPush` preserves `StorageArraySlotRefines` under the slot
disjointness precondition `∀ i ≤ arr.elems.length, baseSlot ≠ elementSlot baseSlot i`. -/
theorem storageArrayPush_preserves_slotRefines
    {baseSlot val : StorageSlotIdx} {arr : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage)
    (hdisj : ∀ i ≤ arr.elems.length, baseSlot ≠ elementSlot baseSlot i) :
    StorageArraySlotRefines baseSlot (arr.push val)
      (execStorageArrayPushSlots baseSlot val storage) := by
  constructor
  · simp [execStorageArrayPushSlots, storageWrite, StorageArrayModel.push, href.length_eq]
  · intro i hi
    simp only [StorageArrayModel.push, List.length_append, List.length_singleton] at hi
    have hne_base : elementSlot baseSlot i ≠ baseSlot :=
      Ne.symm (hdisj i (by omega))
    simp only [execStorageArrayPushSlots, storageWrite, href.length_eq, hne_base, ↓reduceIte,
      elementSlot_inj]
    by_cases hieq : i = arr.elems.length
    · subst hieq
      simp [StorageArrayModel.push]
    · have hilt : i < arr.elems.length := by omega
      simp [StorageArrayModel.push, hieq, List.getElem_append_left hilt, href.slot_eq i hilt]

/-- `Stmt.storageArrayPop` preserves `StorageArraySlotRefines`: when `arr.pop? = some arr'`,
the slot-level pop succeeds and refines `arr'`. -/
theorem storageArrayPop_preserves_slotRefines
    {baseSlot : StorageSlotIdx} {arr arr' : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage)
    (hpop : arr.pop? = some arr')
    (hdisj : ∀ i < arr.elems.length, baseSlot ≠ elementSlot baseSlot i) :
    ∃ storage',
      execStorageArrayPopSlots baseSlot storage = some storage' ∧
      StorageArraySlotRefines baseSlot arr' storage' := by
  cases arr with
  | mk elems =>
    cases elems with
    | nil =>
        simp [StorageArrayModel.pop?] at hpop
    | cons x xs =>
        simp only [StorageArrayModel.pop?, List.isEmpty_cons, Bool.false_eq_true,
          ↓reduceIte, Option.some.injEq] at hpop
        subst hpop
        have hlen_pos : storage baseSlot ≠ 0 := by
          rw [href.length_eq]; simp
        let newLen := storage baseSlot - 1
        let s1 := storageWrite storage (elementSlot baseSlot newLen) 0
        refine ⟨storageWrite s1 baseSlot newLen, ?_, ?_⟩
        · simp [execStorageArrayPopSlots, hlen_pos, newLen, s1]
        · constructor
          · simp [storageWrite, newLen, href.length_eq]
          · intro i hi
            simp only [List.length_dropLast, List.length_cons, Nat.add_sub_cancel] at hi
            have hi_orig : i < (x :: xs).length := by
              simp only [List.length_cons]; omega
            have hne_base : elementSlot baseSlot i ≠ baseSlot :=
              Ne.symm (hdisj i hi_orig)
            have hne_last : i ≠ newLen := by
              have hnew : newLen = xs.length := by
                dsimp [newLen]; rw [href.length_eq]; simp
              omega
            simp only [storageWrite, s1, hne_base, ↓reduceIte, elementSlot_inj, hne_last]
            rw [href.slot_eq i hi_orig, List.getElem_dropLast]

/-- `Stmt.setStorageArrayElement` preserves `StorageArraySlotRefines`: when
`arr.setElem? idx val = some arr'`, the slot-level indexed write succeeds and
refines `arr'`. -/
theorem setStorageArrayElement_preserves_slotRefines
    {baseSlot idx val : StorageSlotIdx} {arr arr' : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage)
    (hset : arr.setElem? idx val = some arr')
    (hdisj : ∀ i < arr.elems.length, baseSlot ≠ elementSlot baseSlot i) :
    ∃ storage',
      execSetStorageArrayElementSlots baseSlot idx val storage = some storage' ∧
      StorageArraySlotRefines baseSlot arr' storage' := by
  simp only [StorageArrayModel.setElem?] at hset
  split at hset
  · rename_i hlt
    injection hset with h; subst h
    have hlt_slot : idx < storage baseSlot := by
      rw [href.length_eq]
      exact hlt
    refine ⟨storageWrite storage (elementSlot baseSlot idx) val, ?_, ?_⟩
    · simp [execSetStorageArrayElementSlots, hlt_slot]
    · constructor
      · have hne : baseSlot ≠ elementSlot baseSlot idx :=
          hdisj idx hlt
        simp [storageWrite, hne, href.length_eq]
      · intro i hi
        simp only [List.length_set] at hi
        simp only [storageWrite, elementSlot_inj]
        by_cases hieq : i = idx
        · subst hieq
          simp
        · simp [hieq, List.getElem_set_ne (Ne.symm hieq), href.slot_eq i hi]
  · cases hset

/-- Unconditional corollary of `storageArrayPush_preserves_slotRefines` discharging
the slot disjointness obligation via `baseSlot_ne_elementSlot`. -/
theorem storageArrayPush_preserves_slotRefines_default
    {baseSlot val : StorageSlotIdx} {arr : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage) :
    StorageArraySlotRefines baseSlot (arr.push val)
      (execStorageArrayPushSlots baseSlot val storage) :=
  storageArrayPush_preserves_slotRefines href (fun i _ => baseSlot_ne_elementSlot baseSlot i)

/-- Unconditional corollary of `storageArrayPop_preserves_slotRefines` discharging
the slot disjointness obligation via `baseSlot_ne_elementSlot`. -/
theorem storageArrayPop_preserves_slotRefines_default
    {baseSlot : StorageSlotIdx} {arr arr' : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage)
    (hpop : arr.pop? = some arr') :
    ∃ storage',
      execStorageArrayPopSlots baseSlot storage = some storage' ∧
      StorageArraySlotRefines baseSlot arr' storage' :=
  storageArrayPop_preserves_slotRefines href hpop (fun i _ => baseSlot_ne_elementSlot baseSlot i)

/-- Unconditional corollary of `setStorageArrayElement_preserves_slotRefines` discharging
the slot disjointness obligation via `baseSlot_ne_elementSlot`. -/
theorem setStorageArrayElement_preserves_slotRefines_default
    {baseSlot idx val : StorageSlotIdx} {arr arr' : StorageArrayModel} {storage : Nat → Nat}
    (href : StorageArraySlotRefines baseSlot arr storage)
    (hset : arr.setElem? idx val = some arr') :
    ∃ storage',
      execSetStorageArrayElementSlots baseSlot idx val storage = some storage' ∧
      StorageArraySlotRefines baseSlot arr' storage' :=
  setStorageArrayElement_preserves_slotRefines href hset
    (fun i _ => baseSlot_ne_elementSlot baseSlot i)

/-- Exact compiler lowering characterization for `compileStorageArrayPush` when
`validateDynamicArrayField` and `compileExprWithInternals` succeed. -/
theorem compileStorageArrayPush_eq
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (value : Expr) (internalFunctions : List FunctionSpec)
    {slot : StorageSlotIdx} {elemType : StorageArrayElemType} {valueExpr : YulExpr}
    (hfield : validateDynamicArrayField fields field = .ok (slot, elemType))
    (hval : compileExprWithInternals fields dynamicSource internalFunctions value = .ok valueExpr) :
    compileStorageArrayPush fields dynamicSource field value internalFunctions =
      .ok [
        YulStmt.block [
          YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.lit slot]),
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit slot]),
          YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "__array_len"],
            valueExpr
          ]),
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit slot,
            YulExpr.call "add" [YulExpr.ident "__array_len", YulExpr.lit 1]
          ])
        ]
      ] := by
  simp [compileStorageArrayPush, hfield, hval, bind, Except.bind, pure, Except.pure]

/-- Exact compiler lowering characterization for `compileStorageArrayPop` when
`validateDynamicArrayField` succeeds. -/
theorem compileStorageArrayPop_eq
    (fields : List Field) (field : String)
    {slot : StorageSlotIdx} {elemType : StorageArrayElemType}
    (hfield : validateDynamicArrayField fields field = .ok (slot, elemType)) :
    compileStorageArrayPop fields field =
      .ok [
        YulStmt.block [
          YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.lit slot]),
          YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__array_len"]) [
            YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
          ],
          YulStmt.let_ "__array_new_len" (YulExpr.call "sub" [YulExpr.ident "__array_len", YulExpr.lit 1]),
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit slot]),
          YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "__array_new_len"],
            YulExpr.lit 0
          ]),
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident "__array_new_len"])
        ]
      ] := by
  simp [compileStorageArrayPop, hfield, bind, Except.bind, pure, Except.pure]

end Compiler.Proofs.IRGeneration
