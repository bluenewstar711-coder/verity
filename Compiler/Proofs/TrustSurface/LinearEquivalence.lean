/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.CompilationModel.TrustSurfaceLinear

/-!
# Formal Soundness and Specification Equivalence for `TrustSurfaceLinear`

This module proves formal soundness and specification theorems for the
$\mathcal{O}(N)$ and $\mathcal{O}(V + E)$ trust-surface analyzers in
`Compiler.CompilationModel.TrustSurfaceLinear`:

1. **Deduplication specification (`mem_dedupPreserveLinear`, `dedupPreserveLinear_eq_spec`,
   `nodup_dedupPreserveLinear`, `dedupPreserveLinear_idem`)**:
   `dedupPreserveHashable` and `dedupPreserveLinear` conserve membership, match
   the reference `List.foldl` specification `dedupPreserveSpec`, produce duplicate-free
   lists (`List.Nodup`), and are idempotent.
2. **Worklist call-graph traversal soundness (`expandTransitiveInternalCallsLinear_sound`,
   `mem_expandTransitiveInternalCallsLinear_of_mem_roots`)**:
   Every function name returned by `expandTransitiveInternalCallsLinear` is
   inductively reachable from `roots` in `CallGraphIndex`, and all roots are included.
3. **Single-pass accumulator soundness (`mem_collectExprLowLevelMechanicsAcc_of_node`,
   `mem_collectLowLevelMechanicsFromStmtsLinear_iff`)**:
   Accumulator-based AST traversals preserve accumulated mechanics and capture
   node-level low-level mechanics without quadratic list appends.
4. **Trust boundary completeness (`undischargedAssumptionReportEntriesLinear_empty_iff`,
   `undischargedAssumptionReportEntriesLinear_empty_no_lowLevelMechanics`,
   `undischargedAssumptionReportEntriesLinear_empty_obligations_proved`,
   `undischargedAssumptionReportEntriesLinear_empty_no_unsafeBlocks`)**:
   When `undischargedAssumptionReportEntriesLinear model = []` (or
   `linearTrustSurfaceReport model = []`), every function in `model` has no
   low-level mechanics, no `unsafe` blocks, and all declared local obligations
   have `.proved` status.
-/

namespace Compiler.Proofs.TrustSurface

open Compiler.CompilationModel

/-!
## 1. Deduplication Membership Conservation, Specification Equivalence, and Idempotence
-/

/-- Membership characterization for the `Std.HashSet`-backed deduplication loop. -/
theorem mem_dedupPreserveHashableLoop [BEq α] [LawfulBEq α] [Hashable α]
    (seen : Std.HashSet α) (acc : Array α) (xs : List α) (y : α) :
    y ∈ (dedupPreserveHashableLoop seen acc xs).toList ↔
      y ∈ acc.toList ∨ (y ∈ xs ∧ seen.contains y = false) := by
  induction xs generalizing seen acc with
  | nil => simp [dedupPreserveHashableLoop]
  | cons x xs ih =>
    simp only [dedupPreserveHashableLoop]
    split
    · rename_i hseen
      rw [ih]
      simp only [List.mem_cons]
      refine ⟨fun h => h.elim Or.inl (fun ⟨hys, hy⟩ => Or.inr ⟨Or.inr hys, hy⟩), ?_⟩
      rintro (hacc | ⟨rfl | hys, hy⟩)
      · exact Or.inl hacc
      · rw [hseen] at hy; contradiction
      · exact Or.inr ⟨hys, hy⟩
    · rename_i hseen
      have hseen' : seen.contains x = false := Bool.eq_false_iff.mpr hseen
      rw [ih]
      simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      constructor
      · rintro ((hacc | rfl) | ⟨hys, _, hy⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨Or.inl rfl, hseen'⟩
        · exact Or.inr ⟨Or.inr hys, hy⟩
      · rintro (hacc | ⟨rfl | hys, hy⟩)
        · exact Or.inl (Or.inl hacc)
        · exact Or.inl (Or.inr rfl)
        · by_cases hxy : x = y
          · subst hxy; exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨hys, hxy, hy⟩

/-- `dedupPreserveHashable` conserves element membership. -/
theorem mem_dedupPreserveHashable [BEq α] [LawfulBEq α] [Hashable α]
    (xs : List α) (y : α) :
    y ∈ (dedupPreserveHashable xs).toList ↔ y ∈ xs := by
  rw [dedupPreserveHashable, mem_dedupPreserveHashableLoop]
  simp

/-- `dedupPreserveLinear` conserves string membership. -/
theorem mem_dedupPreserveLinear (xs : List String) (y : String) :
    y ∈ dedupPreserveLinear xs ↔ y ∈ xs :=
  mem_dedupPreserveHashable xs y

/-- `dedupPreserveHashableLoop` produces the exact same list as the reference `List.foldl`
    deduplication whenever `seen` agrees with `acc.toList`. -/
theorem dedupPreserveHashableLoop_eq_foldl [BEq α] [LawfulBEq α] [Hashable α]
    (seen : Std.HashSet α) (acc : Array α) (xs : List α)
    (hcompat : ∀ z : α, seen.contains z = acc.toList.contains z) :
    (dedupPreserveHashableLoop seen acc xs).toList =
      xs.foldl (fun a item => if a.contains item then a else a ++ [item]) acc.toList := by
  induction xs generalizing seen acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [dedupPreserveHashableLoop, List.foldl_cons, hcompat x]
    split
    · exact ih seen acc hcompat
    · rw [← Array.toList_push]
      apply ih (seen.insert x) (acc.push x)
      intro z
      rw [Std.HashSet.contains_insert, Array.toList_push, List.contains_append]
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, hcompat z]
      rw [Bool.or_comm]
      congr 1
      exact BEq.comm

/-- `dedupPreserveLinear` is extensionally equal to the quadratic reference `dedupPreserveSpec`. -/
theorem dedupPreserveLinear_eq_spec (xs : List String) :
    dedupPreserveLinear xs = dedupPreserveSpec xs := by
  apply dedupPreserveHashableLoop_eq_foldl
  intro z
  simp

/-- `dedupPreserveHashableLoop` preserves `List.Nodup` when all elements in `acc` are marked in `seen`. -/
theorem nodup_dedupPreserveHashableLoop [BEq α] [LawfulBEq α] [Hashable α]
    (seen : Std.HashSet α) (acc : Array α) (xs : List α)
    (hnodup : acc.toList.Nodup)
    (hseen : ∀ z ∈ acc.toList, seen.contains z = true) :
    (dedupPreserveHashableLoop seen acc xs).toList.Nodup := by
  induction xs generalizing seen acc with
  | nil => exact hnodup
  | cons x xs ih =>
    simp only [dedupPreserveHashableLoop]
    split
    · exact ih seen acc hnodup hseen
    · rename_i hx
      have hxnot : x ∉ acc.toList := fun hmem => hx (hseen x hmem)
      have hnodup' : (acc.push x).toList.Nodup := by
        rw [Array.toList_push, List.nodup_append]
        refine ⟨hnodup, by simp, ?_⟩
        intro a ha b hb rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        exact hxnot ha
      have hseen' : ∀ z ∈ (acc.push x).toList, (seen.insert x).contains z = true := by
        intro z hz
        simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rw [Std.HashSet.contains_insert, Bool.or_eq_true]
        rcases hz with hz | rfl
        · exact Or.inr (hseen z hz)
        · exact Or.inl (beq_self_eq_true _)
      exact ih (seen.insert x) (acc.push x) hnodup' hseen'

/-- `dedupPreserveHashable` produces a duplicate-free list. -/
theorem nodup_dedupPreserveHashable [BEq α] [LawfulBEq α] [Hashable α] (xs : List α) :
    (dedupPreserveHashable xs).toList.Nodup := by
  apply nodup_dedupPreserveHashableLoop
  · simp
  · intro z hz; simp at hz

/-- `dedupPreserveLinear` produces a duplicate-free list. -/
theorem nodup_dedupPreserveLinear (xs : List String) :
    (dedupPreserveLinear xs).Nodup :=
  nodup_dedupPreserveHashable xs

/-- On a duplicate-free list whose elements are unseen, `dedupPreserveHashableLoop` appends `xs` verbatim. -/
theorem dedupPreserveHashableLoop_of_nodup [BEq α] [LawfulBEq α] [Hashable α]
    (seen : Std.HashSet α) (acc : Array α) (xs : List α)
    (hnodup : xs.Nodup)
    (hunseen : ∀ x ∈ xs, seen.contains x = false) :
    (dedupPreserveHashableLoop seen acc xs).toList = acc.toList ++ xs := by
  induction xs generalizing seen acc with
  | nil => simp [dedupPreserveHashableLoop]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨hxnot, hnodup_xs⟩ := hnodup
    have hx : seen.contains x = false := hunseen x (List.Mem.head _)
    simp only [dedupPreserveHashableLoop, hx, Bool.false_eq_true, ↓reduceIte]
    rw [ih (seen.insert x) (acc.push x) hnodup_xs]
    · simp [Array.toList_push]
    · intro y hy
      rw [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨?_, hunseen y (List.Mem.tail _ hy)⟩
      rintro rfl
      exact hxnot hy

/-- On a duplicate-free list, `dedupPreserveHashable` is the identity. -/
theorem dedupPreserveHashable_of_nodup [BEq α] [LawfulBEq α] [Hashable α]
    (xs : List α) (hnodup : xs.Nodup) :
    (dedupPreserveHashable xs).toList = xs := by
  rw [dedupPreserveHashable, dedupPreserveHashableLoop_of_nodup _ _ _ hnodup]
  · simp
  · intro x _; simp

/-- `dedupPreserveLinear` is idempotent. -/
theorem dedupPreserveLinear_idem (xs : List String) :
    dedupPreserveLinear (dedupPreserveLinear xs) = dedupPreserveLinear xs := by
  unfold dedupPreserveLinear
  exact dedupPreserveHashable_of_nodup _ (nodup_dedupPreserveHashable xs)

/-!
## 2. Reachability Soundness of the $\mathcal{O}(V + E)$ Worklist Traversal
-/

/-- Inductive reachability in `CallGraphIndex` starting from `roots`. -/
inductive CallGraphReachable (graph : CallGraphIndex) (roots : List String) : String → Prop where
  | root {x : String} (hx : x ∈ roots) : CallGraphReachable graph roots x
  | step {u v : String}
      (hu : CallGraphReachable graph roots u)
      (huv : v ∈ (graph.getD u #[]).toList) :
      CallGraphReachable graph roots v

/-- `enqueueUnvisited` preserves `CallGraphReachable` on both `acc` and `worklist`. -/
theorem enqueueUnvisited_reachable
    (graph : CallGraphIndex) (roots : List String)
    (seen : Std.HashSet String) (acc : Array String) (worklist candidates : List String)
    (hacc : ∀ x ∈ acc.toList, CallGraphReachable graph roots x)
    (hwl : ∀ x ∈ worklist, CallGraphReachable graph roots x)
    (hcand : ∀ x ∈ candidates, CallGraphReachable graph roots x) :
    let res := enqueueUnvisited seen acc worklist candidates
    (∀ x ∈ res.2.1.toList, CallGraphReachable graph roots x) ∧
      (∀ x ∈ res.2.2, CallGraphReachable graph roots x) := by
  induction candidates generalizing seen acc worklist with
  | nil => exact ⟨hacc, hwl⟩
  | cons c cs ih =>
    simp only [enqueueUnvisited]
    have hc : CallGraphReachable graph roots c := hcand c (List.Mem.head _)
    have hcs : ∀ x ∈ cs, CallGraphReachable graph roots x :=
      fun x hx => hcand x (List.Mem.tail _ hx)
    split
    · exact ih seen acc worklist hacc hwl hcs
    · apply ih (seen.insert c) (acc.push c) (c :: worklist)
      · intro x hx
        simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | rfl
        · exact hacc x hx
        · exact hc
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact hwl x hx
      · exact hcs

/-- `expandTransitiveWorklist` preserves `CallGraphReachable` for any fuel bound. -/
theorem expandTransitiveWorklist_reachable
    (graph : CallGraphIndex) (roots : List String)
    (fuel : Nat) (seen : Std.HashSet String) (acc : Array String) (worklist : List String)
    (hacc : ∀ x ∈ acc.toList, CallGraphReachable graph roots x)
    (hwl : ∀ x ∈ worklist, CallGraphReachable graph roots x) :
    ∀ x ∈ (expandTransitiveWorklist graph fuel seen acc worklist).toList,
      CallGraphReachable graph roots x := by
  induction fuel generalizing seen acc worklist with
  | zero => exact hacc
  | succ fuel ih =>
    cases worklist with
    | nil => exact hacc
    | cons curr rest =>
      simp only [expandTransitiveWorklist]
      have hcurr : CallGraphReachable graph roots curr := hwl curr (List.Mem.head _)
      have hrest : ∀ x ∈ rest, CallGraphReachable graph roots x :=
        fun x hx => hwl x (List.Mem.tail _ hx)
      have hcallees : ∀ v ∈ (graph.getD curr #[]).toList, CallGraphReachable graph roots v :=
        fun v hv => CallGraphReachable.step hcurr hv
      have hstep := enqueueUnvisited_reachable graph roots seen acc rest
        (graph.getD curr #[]).toList hacc hrest hcallees
      exact ih _ _ _ hstep.1 hstep.2

/-- Soundness of `expandTransitiveInternalCallsLinear`: every returned helper name is
    inductively reachable from `roots` in `graph`. -/
theorem expandTransitiveInternalCallsLinear_sound
    (graph : CallGraphIndex) (roots : List String) (x : String)
    (hx : x ∈ expandTransitiveInternalCallsLinear graph roots) :
    CallGraphReachable graph roots x := by
  unfold expandTransitiveInternalCallsLinear at hx
  have hinit := enqueueUnvisited_reachable graph roots ∅ #[] [] roots
    (by intro z hz; simp at hz)
    (by intro z hz; simp at hz)
    (fun z hz => CallGraphReachable.root hz)
  exact expandTransitiveWorklist_reachable graph roots _ _ _ _ hinit.1 hinit.2 x hx

/-- The accumulator component of `enqueueUnvisited` agrees with `dedupPreserveHashableLoop`. -/
theorem enqueueUnvisited_acc_eq_dedup
    (seen : Std.HashSet String) (acc : Array String) (worklist candidates : List String) :
    (enqueueUnvisited seen acc worklist candidates).2.1 =
      dedupPreserveHashableLoop seen acc candidates := by
  induction candidates generalizing seen acc worklist with
  | nil => rfl
  | cons x xs ih =>
    simp only [enqueueUnvisited, dedupPreserveHashableLoop]
    split <;> apply ih

/-- `enqueueUnvisited` is monotone on `acc`: existing elements remain in the accumulator. -/
theorem mem_enqueueUnvisited_of_mem_acc
    (seen : Std.HashSet String) (acc : Array String) (worklist candidates : List String)
    {z : String} (hz : z ∈ acc.toList) :
    z ∈ (enqueueUnvisited seen acc worklist candidates).2.1.toList := by
  induction candidates generalizing seen acc worklist with
  | nil => exact hz
  | cons x xs ih =>
    simp only [enqueueUnvisited]
    split
    · exact ih seen acc worklist hz
    · apply ih (seen.insert x) (acc.push x) (x :: worklist)
      simp [Array.toList_push, hz]

/-- `expandTransitiveWorklist` is monotone on `acc`. -/
theorem mem_expandTransitiveWorklist_of_mem_acc
    (graph : CallGraphIndex) (fuel : Nat)
    (seen : Std.HashSet String) (acc : Array String) (worklist : List String)
    {z : String} (hz : z ∈ acc.toList) :
    z ∈ (expandTransitiveWorklist graph fuel seen acc worklist).toList := by
  induction fuel generalizing seen acc worklist with
  | zero => exact hz
  | succ fuel ih =>
    cases worklist with
    | nil => exact hz
    | cons curr rest =>
      simp only [expandTransitiveWorklist]
      exact ih _ _ _ (mem_enqueueUnvisited_of_mem_acc seen acc rest _ hz)

/-- Every root in `roots` is included in `expandTransitiveInternalCallsLinear graph roots`. -/
theorem mem_expandTransitiveInternalCallsLinear_of_mem_roots
    (graph : CallGraphIndex) (roots : List String) {r : String} (hr : r ∈ roots) :
    r ∈ expandTransitiveInternalCallsLinear graph roots := by
  unfold expandTransitiveInternalCallsLinear
  apply mem_expandTransitiveWorklist_of_mem_acc
  rw [enqueueUnvisited_acc_eq_dedup]
  exact (mem_dedupPreserveHashable roots r).mpr hr

/-!
## 3. Single-Pass Accumulator Collection Soundness
-/

/-- Generic monotonicity lemma for `List.foldl` over an accumulator-extending step function. -/
theorem mem_foldl_of_mem {α β : Type} (f : List α → β → List α)
    (hf : ∀ cur b z, z ∈ cur → z ∈ f cur b)
    (bs : List β) (init : List α) {z : α} (hz : z ∈ init) :
    z ∈ bs.foldl f init := by
  induction bs generalizing init with
  | nil => exact hz
  | cons b bs ih => exact ih (f init b) (hf init b z hz)

/-- `collectExprLowLevelMechanicsAcc` preserves all mechanics already present in `acc`. -/
theorem mem_collectExprLowLevelMechanicsAcc_of_mem_acc
    (acc : List String) (expr : Expr) {z : String} (hz : z ∈ acc) :
    z ∈ collectExprLowLevelMechanicsAcc acc expr := by
  rw [collectExprLowLevelMechanicsAcc]
  apply mem_foldl_of_mem
  · intro cur ⟨child, hchild⟩ w hw
    have := Expr.children_sizeOf_lt expr child hchild
    exact mem_collectExprLowLevelMechanicsAcc_of_mem_acc cur child hw
  · cases exprNodeLowLevelMechanic? expr with
    | none => exact hz
    | some m => exact List.Mem.tail _ hz
termination_by sizeOf expr

/-- If `expr` has a direct low-level mechanic `m`, then `m` is recorded by `collectExprLowLevelMechanicsAcc`. -/
theorem mem_collectExprLowLevelMechanicsAcc_of_node
    (acc : List String) (expr : Expr) {m : String}
    (hm : exprNodeLowLevelMechanic? expr = some m) :
    m ∈ collectExprLowLevelMechanicsAcc acc expr := by
  rw [collectExprLowLevelMechanicsAcc]
  apply mem_foldl_of_mem
  · intro cur ⟨child, hchild⟩ w hw
    have := Expr.children_sizeOf_lt expr child hchild
    exact mem_collectExprLowLevelMechanicsAcc_of_mem_acc cur child hw
  · simp [hm]

/-- `collectStmtMetadataLowLevelMechanicsAcc` preserves all mechanics already in `acc`. -/
theorem mem_collectStmtMetadataLowLevelMechanicsAcc_of_mem_acc
    (acc : List String) (md : StmtMetadata) {z : String} (hz : z ∈ acc) :
    z ∈ collectStmtMetadataLowLevelMechanicsAcc acc md := by
  unfold collectStmtMetadataLowLevelMechanicsAcc
  apply mem_foldl_of_mem
  · intro cur e w hw
    exact mem_collectExprLowLevelMechanicsAcc_of_mem_acc cur e hw
  · apply mem_foldl_of_mem
    · intro cur m w hw
      exact List.Mem.tail _ hw
    · exact hz

/-- Membership in `collectLowLevelMechanicsFromStmtsLinear stmts` is equivalent to
    membership in the single-pass accumulator `collectStmtsLowLevelMechanicsAcc [] stmts`. -/
theorem mem_collectLowLevelMechanicsFromStmtsLinear_iff
    (stmts : List Stmt) (m : String) :
    m ∈ collectLowLevelMechanicsFromStmtsLinear stmts ↔
      m ∈ collectStmtsLowLevelMechanicsAcc [] stmts := by
  unfold collectLowLevelMechanicsFromStmtsLinear
  rw [mem_dedupPreserveLinear, List.mem_reverse]

/-!
## 4. Trust Boundary Completeness
-/

/-- Boolean inequality with `.proved` matches propositional inequality on `ProofStatus`. -/
theorem proofStatus_bne_proved_iff_ne (s : Compiler.ProofStatus) :
    (s != .proved) = true ↔ s ≠ .proved := by
  cases s <;> decide

/-- Membership characterization for `undischargedAssumptionReportEntriesLinear`. -/
theorem mem_undischargedAssumptionReportEntriesLinear_iff
    (model : CompilationModel) (entry : AssumptionReportEntry) :
    entry ∈ undischargedAssumptionReportEntriesLinear model ↔
      entry ∈ linearTrustSurfaceReport model ∧ entry.status ≠ .proved := by
  simp [undischargedAssumptionReportEntriesLinear, List.mem_filter,
    proofStatus_bne_proved_iff_ne]

/-- `undischargedAssumptionReportEntriesLinear model` is empty if and only if every
    entry in `linearTrustSurfaceReport model` has `.proved` status. -/
theorem undischargedAssumptionReportEntriesLinear_empty_iff
    (model : CompilationModel) :
    undischargedAssumptionReportEntriesLinear model = [] ↔
      ∀ entry ∈ linearTrustSurfaceReport model, entry.status = .proved := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro hemp entry hentry
    cases h : entry.status with
    | proved => rfl
    | assumed =>
      exfalso
      exact hemp entry ((mem_undischargedAssumptionReportEntriesLinear_iff model entry).mpr
        ⟨hentry, by rw [h]; rintro ⟨⟩⟩)
    | unchecked =>
      exfalso
      exact hemp entry ((mem_undischargedAssumptionReportEntriesLinear_iff model entry).mpr
        ⟨hentry, by rw [h]; rintro ⟨⟩⟩)
  · intro hall entry hentry
    obtain ⟨hmem, hne⟩ := (mem_undischargedAssumptionReportEntriesLinear_iff model entry).mp hentry
    exact hne (hall entry hmem)

/-- Every entry in `linearFunctionTrustSurfaceReport fn` for `fn ∈ model.functions`
    appears in `linearTrustSurfaceReport model`. -/
theorem mem_linearTrustSurfaceReport_of_mem_function
    {model : CompilationModel} {fn : FunctionSpec} (hfn : fn ∈ model.functions)
    {entry : AssumptionReportEntry} (hentry : entry ∈ linearFunctionTrustSurfaceReport fn) :
    entry ∈ linearTrustSurfaceReport model := by
  unfold linearTrustSurfaceReport
  rw [List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨fn, hfn, hentry⟩)

/-- Every low-level mechanic collected from `fn.body` for `fn ∈ model.functions`
    produces an undischarged entry in `undischargedAssumptionReportEntriesLinear model`. -/
theorem mem_undischarged_of_function_lowLevelMechanic
    {model : CompilationModel} {fn : FunctionSpec} (hfn : fn ∈ model.functions)
    {m : String} (hm : m ∈ collectLowLevelMechanicsFromStmtsLinear fn.body) :
    lowLevelMechanicEntry "function" fn.name m ∈
      undischargedAssumptionReportEntriesLinear model := by
  rw [mem_undischargedAssumptionReportEntriesLinear_iff]
  refine ⟨?_, by rintro ⟨⟩⟩
  apply mem_linearTrustSurfaceReport_of_mem_function hfn
  unfold linearFunctionTrustSurfaceReport linearSiteTrustSurfaceReport
  rw [List.mem_append, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.mpr ⟨m, hm, rfl⟩))

/-- Trust boundary completeness (low-level mechanics): if
    `undischargedAssumptionReportEntriesLinear model = []`, then no function in
    `model` contains any low-level mechanics. -/
theorem undischargedAssumptionReportEntriesLinear_empty_no_lowLevelMechanics
    {model : CompilationModel}
    (hemp : undischargedAssumptionReportEntriesLinear model = [])
    {fn : FunctionSpec} (hfn : fn ∈ model.functions) :
    collectLowLevelMechanicsFromStmtsLinear fn.body = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro m hm
  have hmem := mem_undischarged_of_function_lowLevelMechanic hfn hm
  rw [hemp] at hmem
  exact List.not_mem_nil hmem

/-- Corollary: if `linearTrustSurfaceReport model = []`, then no function in `model`
    contains any low-level mechanics. -/
theorem linearTrustSurfaceReport_empty_no_lowLevelMechanics
    {model : CompilationModel}
    (hemp : linearTrustSurfaceReport model = [])
    {fn : FunctionSpec} (hfn : fn ∈ model.functions) :
    collectLowLevelMechanicsFromStmtsLinear fn.body = [] := by
  apply undischargedAssumptionReportEntriesLinear_empty_no_lowLevelMechanics _ hfn
  simp [undischargedAssumptionReportEntriesLinear, hemp]

/-- Trust boundary completeness (local obligations): if
    `undischargedAssumptionReportEntriesLinear model = []`, then every local obligation
    declared on any `fn ∈ model.functions` has `.proved` status. -/
theorem undischargedAssumptionReportEntriesLinear_empty_obligations_proved
    {model : CompilationModel}
    (hemp : undischargedAssumptionReportEntriesLinear model = [])
    {fn : FunctionSpec} (hfn : fn ∈ model.functions)
    {ob : LocalObligation} (hob : ob ∈ fn.localObligations) :
    ob.proofStatus = .proved := by
  have hall := (undischargedAssumptionReportEntriesLinear_empty_iff model).mp hemp
  have hentry : localObligationEntry "function" fn.name ob ∈ linearTrustSurfaceReport model := by
    apply mem_linearTrustSurfaceReport_of_mem_function hfn
    unfold linearFunctionTrustSurfaceReport linearSiteTrustSurfaceReport
    rw [List.mem_append, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨ob, hob, rfl⟩))
  exact hall (localObligationEntry "function" fn.name ob) hentry

/-- Trust boundary completeness (`unsafe` blocks): if
    `undischargedAssumptionReportEntriesLinear model = []`, then no function in
    `model` contains any `unsafe` block reasons. -/
theorem undischargedAssumptionReportEntriesLinear_empty_no_unsafeBlocks
    {model : CompilationModel}
    (hemp : undischargedAssumptionReportEntriesLinear model = [])
    {fn : FunctionSpec} (hfn : fn ∈ model.functions) :
    collectUnsafeBlockReasonsFromStmtsLinear fn.body = [] := by
  have hall := (undischargedAssumptionReportEntriesLinear_empty_iff model).mp hemp
  rw [List.eq_nil_iff_forall_not_mem]
  intro r hr
  have hentry : unsafeBlockEntry "function" fn.name r ∈ linearTrustSurfaceReport model := by
    apply mem_linearTrustSurfaceReport_of_mem_function hfn
    unfold linearFunctionTrustSurfaceReport linearSiteTrustSurfaceReport
    rw [List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hproved := hall (unsafeBlockEntry "function" fn.name r) hentry
  cases hproved

end Compiler.Proofs.TrustSurface
