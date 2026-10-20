import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.SupportedSpec.SurfaceMask

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

/-!
# Mathlib-Style Parametric `SupportProfile` Capability Lattice (Node R1)

This module unifies the parallel whole-contract Layer 2 support predicates
(`SupportedSpec`, `SupportedSpecWithScalarEvents`,
`SupportedSpecExceptMappingWrites`, `SupportedSpecWithHelpers`) into a single
parametric family `SupportedSpecAt (p : SupportProfile) (spec : CompilationModel)`
indexed by a finite capability lattice `SupportProfile`.

## Main Definitions
- `SupportProfile`: 5-bit boolean capability record governing whole-contract
  admission extensions beyond the minimal core fragment.
- `SupportProfile.minimal`, `SupportProfile.scalarEvents`,
  `SupportProfile.uncheckedMapping`, `SupportProfile.withHelpers`,
  `SupportProfile.full`: Standard points in the capability lattice.
- `SupportProfile.le` (`≤`): Componentwise implication order on capabilities.
- `SupportedSpecAt`: Unified capability-indexed whole-contract specification
  predicate.

## Main Theorems
- `SupportProfile.le_refl`, `SupportProfile.le_trans`,
  `minimal_le_withHelpers`, `withHelpers_le_full`: Partial-order laws on
  `SupportProfile`.
- `supportedSpecAt_minimal_iff_supportedSpec`,
  `supportedSpecAt_withHelpers_iff_supportedSpecWithHelpers`,
  `supportedSpecAt_scalarEvents_iff`,
  `supportedSpecAt_uncheckedMapping_iff`: Exact equivalence bridges to legacy
  specification structures.
- `SupportedSpecAt.mono`: Universal monotonicity theorem lifting any
  `SupportedSpecAt p₁ spec` witness along `p₁ ≤ p₂`.
-/

/-- Mathlib-style bundled capability profile indexing the supported CompilationModel
fragments across the Layer 2 preservation hierarchy. -/
structure SupportProfile where
  /-- Admit declared scalar events and top-level `Stmt.emit` heads. -/
  allowScalarEvents : Bool := false
  /-- Admit indexed and unindexed dynamic ABI event encodings. -/
  allowDynamicEvents : Bool := false
  /-- Admit compositional internal helper calls (`WithInternals`). -/
  allowInternalHelpers : Bool := false
  /-- Admit singleton mapping and struct-member storage writes. -/
  allowUncheckedMappingSlot : Bool := false
  /-- Admit External Call Modules (`Stmt.ecm`) and `fallback` / `receive` entrypoints. -/
  allowEcmAndSpecialEntrypoints : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace SupportProfile

/-- Minimal core support profile with all optional capability extensions disabled. -/
def minimal : SupportProfile := {}

/-- Support profile enabling the top-level scalar event emission slice. -/
def scalarEvents : SupportProfile :=
  { allowScalarEvents := true }

/-- Support profile enabling singleton mapping and struct-member storage writes. -/
def uncheckedMapping : SupportProfile :=
  { allowUncheckedMappingSlot := true }

/-- Support profile enabling compositional internal helper calls. -/
def withHelpers : SupportProfile :=
  { allowInternalHelpers := true }

/-- Full Core Fragment support profile enabling all five capability tracks. -/
def full : SupportProfile :=
  { allowScalarEvents := true
    allowDynamicEvents := true
    allowInternalHelpers := true
    allowUncheckedMappingSlot := true
    allowEcmAndSpecialEntrypoints := true }

/-- Componentwise capability ordering on `SupportProfile`: `p₁ ≤ p₂` holds iff
every capability enabled in `p₁` is also enabled in `p₂`. -/
def le (p₁ p₂ : SupportProfile) : Prop :=
  (p₁.allowScalarEvents = true → p₂.allowScalarEvents = true) ∧
  (p₁.allowDynamicEvents = true → p₂.allowDynamicEvents = true) ∧
  (p₁.allowInternalHelpers = true → p₂.allowInternalHelpers : Prop) ∧
  (p₁.allowUncheckedMappingSlot = true → p₂.allowUncheckedMappingSlot = true) ∧
  (p₁.allowEcmAndSpecialEntrypoints = true → p₂.allowEcmAndSpecialEntrypoints = true)

instance : LE SupportProfile where
  le := SupportProfile.le

/-- Reflexivity of the capability partial order `SupportProfile.le`. -/
@[simp]
theorem le_refl (p : SupportProfile) : p ≤ p :=
  ⟨id, id, id, id, id⟩

/-- Transitivity of the capability partial order `SupportProfile.le`. -/
theorem le_trans {p₁ p₂ p₃ : SupportProfile}
    (h₁₂ : p₁ ≤ p₂) (h₂₃ : p₂ ≤ p₃) : p₁ ≤ p₃ :=
  ⟨fun h => h₂₃.1 (h₁₂.1 h),
   fun h => h₂₃.2.1 (h₁₂.2.1 h),
   fun h => h₂₃.2.2.1 (h₁₂.2.2.1 h),
   fun h => h₂₃.2.2.2.1 (h₁₂.2.2.2.1 h),
   fun h => h₂₃.2.2.2.2 (h₁₂.2.2.2.2 h)⟩

/-- `SupportProfile.minimal` is the bottom element of the capability lattice. -/
theorem minimal_le (p : SupportProfile) : minimal ≤ p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- `SupportProfile.full` is the top element of the capability lattice. -/
theorem le_full (p : SupportProfile) : p ≤ full :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- `SupportProfile.minimal` embeds into `SupportProfile.withHelpers`. -/
theorem minimal_le_withHelpers : minimal ≤ withHelpers :=
  minimal_le withHelpers

/-- `SupportProfile.withHelpers` embeds into `SupportProfile.full`. -/
theorem withHelpers_le_full : withHelpers ≤ full :=
  le_full withHelpers

/-- `SupportProfile.minimal` embeds into `SupportProfile.scalarEvents`. -/
theorem minimal_le_scalarEvents : minimal ≤ scalarEvents :=
  minimal_le scalarEvents

/-- `SupportProfile.minimal` embeds into `SupportProfile.uncheckedMapping`. -/
theorem minimal_le_uncheckedMapping : minimal ≤ uncheckedMapping :=
  minimal_le uncheckedMapping

/-- Surface bitmask of AST statement families permitted by a `SupportProfile`. -/
def allowedSurfaceMask (p : SupportProfile) : SurfaceMask :=
  bitStateRead ||| bitConstructorRaw |||
    (if p.allowScalarEvents || p.allowDynamicEvents then bitEventEmit else 0) |||
    (if p.allowInternalHelpers then bitInternalCall else 0) |||
    (if p.allowUncheckedMappingSlot then bitMappingWrite else 0) |||
    (if p.allowEcmAndSpecialEntrypoints then bitExternalCall ||| bitLowLevelMem else 0)

end SupportProfile

export SupportProfile (minimal_le_withHelpers withHelpers_le_full)

/-! ## Unified Parametric `SupportedSpecAt` Specification Predicate -/

/-- Unified capability-indexed specification predicate generalizing `SupportedSpec`,
`SupportedSpecWithScalarEvents`, `SupportedSpecExceptMappingWrites`, and
`SupportedSpecWithHelpers` over the `SupportProfile` lattice. -/
def SupportedSpecAt (p : SupportProfile) (spec : CompilationModel)
    (selectors : List Nat := []) : Prop :=
  Nonempty (SupportedSpec spec selectors) ∨
    (p.allowScalarEvents = true ∧ Nonempty (SupportedSpecWithScalarEvents spec selectors)) ∨
    (p.allowInternalHelpers = true ∧ Nonempty (SupportedSpecWithHelpers spec selectors)) ∨
    (p.allowUncheckedMappingSlot = true ∧ Nonempty (SupportedSpecExceptMappingWrites spec selectors)) ∨
    (p.allowDynamicEvents = true ∧ SupportedSpecInvariants spec selectors) ∨
    (p.allowEcmAndSpecialEntrypoints = true ∧ SupportedSpecInvariants spec selectors)

/-- Universal monotonicity of `SupportedSpecAt` along the capability lattice:
if `p₁ ≤ p₂`, any contract supported at profile `p₁` is supported at profile `p₂`. -/
theorem SupportedSpecAt.mono {p₁ p₂ : SupportProfile} (hle : p₁ ≤ p₂)
    {spec : CompilationModel} {selectors : List Nat} :
    SupportedSpecAt p₁ spec selectors → SupportedSpecAt p₂ spec selectors := by
  intro h
  rcases h with hmin | ⟨hs, hspec⟩ | ⟨hh, hspec⟩ | ⟨hm, hspec⟩ | ⟨hd, hinv⟩ | ⟨he, hinv⟩
  · exact Or.inl hmin
  · exact Or.inr (Or.inl ⟨hle.1 hs, hspec⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hle.2.2.1 hh, hspec⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hle.2.2.2.1 hm, hspec⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hle.2.1 hd, hinv⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hle.2.2.2.2 he, hinv⟩))))

/-- Every `SupportedSpecAt` witness preserves the profile-invariant global
contract invariants `SupportedSpecInvariants`. -/
theorem SupportedSpecAt.invariants {p : SupportProfile} {spec : CompilationModel}
    {selectors : List Nat} (h : SupportedSpecAt p spec selectors) :
    SupportedSpecInvariants spec selectors := by
  rcases h with hmin | ⟨_, hspec⟩ | ⟨_, hspec⟩ | ⟨_, hspec⟩ | ⟨_, hinv⟩ | ⟨_, hinv⟩
  · obtain ⟨hspec⟩ := hmin; exact hspec.invariants
  · obtain ⟨hspec⟩ := hspec; exact hspec.invariants
  · obtain ⟨hspec⟩ := hspec; exact hspec.invariants
  · obtain ⟨hspec⟩ := hspec; exact hspec.invariants
  · exact hinv
  · exact hinv

/-- Equivalence at `SupportProfile.minimal`: `SupportedSpecAt .minimal` holds iff
`SupportedSpec` is inhabited. -/
theorem supportedSpecAt_minimal_iff_supportedSpec
    (spec : CompilationModel) (selectors : List Nat := []) :
    SupportedSpecAt SupportProfile.minimal spec selectors ↔
      Nonempty (SupportedSpec spec selectors) := by
  simp [SupportedSpecAt, SupportProfile.minimal]

/-- Equivalence at `SupportProfile.withHelpers`: `SupportedSpecAt .withHelpers`
holds iff `SupportedSpecWithHelpers` is inhabited. -/
theorem supportedSpecAt_withHelpers_iff_supportedSpecWithHelpers
    (spec : CompilationModel) (selectors : List Nat := []) :
    SupportedSpecAt SupportProfile.withHelpers spec selectors ↔
      Nonempty (SupportedSpecWithHelpers spec selectors) := by
  simp only [SupportedSpecAt, SupportProfile.withHelpers, Bool.false_eq_true,
    true_and, false_and, or_false, false_or]
  constructor
  · rintro (h | h)
    · obtain ⟨h⟩ := h; exact ⟨h.withHelpers⟩
    · exact h
  · intro h
    exact Or.inr h

/-- Equivalence at `SupportProfile.scalarEvents`: `SupportedSpecAt .scalarEvents`
holds iff either `SupportedSpec` or `SupportedSpecWithScalarEvents` is inhabited. -/
theorem supportedSpecAt_scalarEvents_iff
    (spec : CompilationModel) (selectors : List Nat := []) :
    SupportedSpecAt SupportProfile.scalarEvents spec selectors ↔
      Nonempty (SupportedSpec spec selectors) ∨
        Nonempty (SupportedSpecWithScalarEvents spec selectors) := by
  simp [SupportedSpecAt, SupportProfile.scalarEvents]

/-- Equivalence at `SupportProfile.uncheckedMapping`:
`SupportedSpecAt .uncheckedMapping` holds iff `SupportedSpecExceptMappingWrites`
is inhabited. -/
theorem supportedSpecAt_uncheckedMapping_iff
    (spec : CompilationModel) (selectors : List Nat := []) :
    SupportedSpecAt SupportProfile.uncheckedMapping spec selectors ↔
      Nonempty (SupportedSpecExceptMappingWrites spec selectors) := by
  simp only [SupportedSpecAt, SupportProfile.uncheckedMapping, Bool.false_eq_true,
    true_and, false_and, or_false, false_or]
  constructor
  · rintro (h | h)
    · obtain ⟨h⟩ := h; exact ⟨h.exceptMappingWrites⟩
    · exact h
  · intro h
    exact Or.inr h

/-! ## Sound Equivalence Bridges Connecting `SurfaceMask` to `SupportedSpec` Classifiers -/

/-- Node-level event classifier `stmtTouchesEventSurface` agrees identically
with `stmtIsEventEmit`. -/
@[simp]
theorem stmtTouchesEventSurface_eq_stmtIsEventEmit (s : Stmt) :
    stmtTouchesEventSurface s = stmtIsEventEmit s := by
  cases s <;> rfl

/-- If `bitEventEmit` is absent from `stmtSurfaceMask s`, then
`stmtTouchesEventSurface s = false`. -/
theorem stmtTouchesEventSurface_eq_false_of_no_eventEmitMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitEventEmit = false) :
    stmtTouchesEventSurface s = false := by
  rw [stmtTouchesEventSurface_eq_stmtIsEventEmit]
  exact stmtIsEventEmit_eq_false_of_no_eventEmitMask h

/-- Node-level direct helper classifier `stmtTouchesDirectInternalHelperSurface`
agrees identically with `stmtIsDirectInternalCall`. -/
@[simp]
theorem stmtTouchesDirectInternalHelperSurface_eq_stmtIsDirectInternalCall (s : Stmt) :
    stmtTouchesDirectInternalHelperSurface s = stmtIsDirectInternalCall s := by
  cases s <;> rfl

/-- If `bitInternalCall` is absent from `stmtListSurfaceMask stmts`, then
`stmtListTouchesDirectInternalHelperSurface stmts = false`. -/
theorem stmtListTouchesDirectInternalHelperSurface_eq_false_of_no_internalCallMask
    {stmts : List Stmt}
    (h : hasMask (stmtListSurfaceMask stmts) bitInternalCall = false) :
    stmtListTouchesDirectInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => rfl
  | cons s ss ih =>
      simp only [stmtListSurfaceMask_cons, hasMask_or, Bool.or_eq_false_iff] at h
      simp [stmtListTouchesDirectInternalHelperSurface,
        stmtTouchesDirectInternalHelperSurface_eq_stmtIsDirectInternalCall,
        stmtIsDirectInternalCall_eq_false_of_no_internalCallMask h.1,
        ih h.2]

/-- Sound equivalence bridge for mapping writes on `stmtTouchesUnsupportedStateSurface`:
when `bitMappingWrite` is absent from `stmtSurfaceMask s`, the strict state-surface
classifier and its `ExceptMappingWrites` relaxation agree. -/
theorem stmtTouchesUnsupportedStateSurface_eq_of_no_mappingWriteMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitMappingWrite = false) :
    stmtTouchesUnsupportedStateSurface s =
      stmtTouchesUnsupportedStateSurfaceExceptMappingWrites s := by
  have hm := stmtIsMappingWrite_eq_false_of_no_mappingWriteMask h
  cases s <;> first | contradiction | rfl

/-- List-level equivalence bridge for mapping writes on `stmtListTouchesUnsupportedStateSurface`. -/
theorem stmtListTouchesUnsupportedStateSurface_eq_of_no_mappingWriteMask
    {stmts : List Stmt}
    (h : hasMask (stmtListSurfaceMask stmts) bitMappingWrite = false) :
    stmtListTouchesUnsupportedStateSurface stmts =
      stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts := by
  induction stmts with
  | nil => rfl
  | cons s ss ih =>
      simp only [stmtListSurfaceMask_cons, hasMask_or, Bool.or_eq_false_iff] at h
      simp [stmtListTouchesUnsupportedStateSurface,
        stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedStateSurface_eq_of_no_mappingWriteMask h.1,
        ih h.2]

end Compiler.Proofs.IRGeneration
