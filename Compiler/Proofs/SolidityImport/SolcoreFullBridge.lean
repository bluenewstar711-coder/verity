import Compiler.Proofs.SolidityImport.SolcoreGeneric
import Compiler.Proofs.SolidityImport.TranslationValidation
import Compiler.Proofs.MetaSpecs

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.SolcoreFullBridge

open Compiler
open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.MetaSpecs
open Compiler.Proofs.SolidityImport.Solcore
open Compiler.Proofs.SolidityImport.Solcore.Core
open Compiler.Proofs.SolidityImport.Solcore.ContractRuntime
open Compiler.Proofs.SolidityImport.SolcoreBridge
open Compiler.Proofs.SolidityImport.SolcoreGeneric
open Compiler.Proofs.SolidityImport.TranslationValidation

/-!
# Full Formal `Solcore ⟷ Verity` Semantic Bridge (Phase 3B)

This module extends `SolcoreGeneric` (`N11`) and `TranslationValidation` (`N10`)
to the full checked-arithmetic and control-flow fragment (`SolcoreCheckedStmt`)
and composes it with `MetaSpecs` (`TriangularSemanticMetaSpec` and
`CertifiedOrExplicitlyFlagged`) into a single quadrangular preservation theorem
connecting `Solcore` (`Layer 0`), `Denote` (`Layer 1`), `SourceSemantics`
(`Layer 2`), and `IRState` (`Layer 2 IR`):

1. **`ClockedStepBudget` & Extended `SolcoreCheckedStmt` Language**:
   Covers straight-line statements (`straight`), persistent storage loads into
   locals (`sloadLocal`), EIP-1153 transient storage loads into locals
   (`tloadLocal`), word-aligned memory writes (`mstoreWord`), checked 256-bit
   addition and subtraction with `Panic(0x11)` revert (`addChecked`,
   `subChecked`), guarded `requireGuard`, conditional `iteBranch`, and
   fuel-bounded iteration (`boundedIter`).
2. **Checked Statement Semantic Preservation (`compileSolcoreCheckedStmt_preserves_semantics`)**:
   Proves that on `.continued sFinal`, `Denote.execStmtList` reaches
   `.continue dFinal` with `StateRefines sFinal dFinal initialWorld`, and on
   `.reverted sFinal revWord`, `sFinal.resolveFrame (.reverted revWord)` rolls
   back storage and events to `sState.checkpoint` and refines `Denote.revertedResult`.
3. **Quadrangular End-to-End Preservation (`solcore_to_verity_quadrangular_preservation`)**:
   Unites `CertifiedContractTranslationWitness` (`Solcore → Denote`),
   `TriangularSemanticMetaSpec` (`Denote → SourceSemantics → IR`), and
   `CertifiedOrExplicitlyFlagged` (`SurfaceMask` trust-boundary partition).
-/

/-! ## 1. Fuel-Bounded Step Budget & Iteration Helpers -/

/-- Declarative step-budget record for fuel-bounded `Solcore` loop execution. -/
structure ClockedStepBudget where
  remainingSteps : Nat
  deriving DecidableEq, Repr

namespace ClockedStepBudget

/-- Consume a single step from the budget when `remainingSteps > 0`. -/
def consumeStep? (b : ClockedStepBudget) : Option ClockedStepBudget :=
  match b.remainingSteps with
  | 0 => none
  | n + 1 => some ⟨n⟩

end ClockedStepBudget

/-- Unroll `fuel` iterations of a straight-line statement body into a `List Stmt`. -/
def iterToVerity : Nat → SolcoreStraightLineStmt → List Compiler.CompilationModel.Stmt
  | 0, _ => []
  | fuel + 1, body => body.toVerity ++ iterToVerity fuel body

/-- Execute `fuel` iterations of `body` on `SolcoreExecState`. -/
def execIterSolcore : Nat → SolcoreStraightLineStmt → SolcoreExecState → SolcoreExecState
  | 0, _, sState => sState
  | fuel + 1, body, sState => execIterSolcore fuel body (body.execSolcore sState)

/-- Execute `fuel` iterations of `body` on `(SolcoreExecState, DenoteState)`. -/
def execIterDenote :
    Nat → SolcoreStraightLineStmt → SolcoreExecState → DenoteState → DenoteState
  | 0, _, _, dState => dState
  | fuel + 1, body, sState, dState =>
      execIterDenote fuel body (body.execSolcore sState) (body.execDenote sState dState)

private theorem execStmtList_append_of_continue
    (oracle : DenoteOracle) (fields : List Field) :
    ∀ (s1 s2 : List Compiler.CompilationModel.Stmt) (dState dMid : DenoteState),
      Denote.execStmtList oracle fields dState s1 = .continue dMid →
      Denote.execStmtList oracle fields dState (s1 ++ s2) =
        Denote.execStmtList oracle fields dMid s2
  | [], _, _, _, h => by
      injection h with hEq
      subst hEq
      rfl
  | stmt :: rest, s2, dState, dMid, h => by
      simp only [List.cons_append, Denote.execStmtList] at h ⊢
      revert h
      cases Denote.execStmt oracle fields dState stmt <;> intro h
      · exact execStmtList_append_of_continue oracle fields rest s2 _ dMid h
      · contradiction
      · contradiction
      · contradiction
      · contradiction

/-- Fuel-bounded iteration preserves `StateRefines` for every `fuel : Nat`. -/
theorem execIter_preserves_stateRefines
    (fuel : Nat) (body : SolcoreStraightLineStmt)
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (hFields : body.FieldsAligned fields) :
    Denote.execStmtList oracle fields dState (iterToVerity fuel body) =
      .continue (execIterDenote fuel body sState dState) ∧
    StateRefines
      (execIterSolcore fuel body sState)
      (execIterDenote fuel body sState dState)
      initialWorld := by
  induction fuel generalizing sState dState with
  | zero => exact ⟨rfl, hRef⟩
  | succ n ih =>
      obtain ⟨hStepExec, hStepRef⟩ :=
        compileSolcoreStmt_preserves_stateRefines body hRef oracle fields hFields
      obtain ⟨hRestExec, hRestRef⟩ := ih hStepRef
      exact ⟨(execStmtList_append_of_continue oracle fields
        body.toVerity (iterToVerity n body) dState _ hStepExec).trans hRestExec, hRestRef⟩

/-! ## 2. Checked 256-Bit Arithmetic Lemmas (`Panic(0x11)`) -/

/-- Canonical Solidity `Panic(0x11)` revert word used on arithmetic overflow/underflow. -/
def panicArithWord : Word :=
  Word.ofNatModulo 0x11

/-- For 256-bit words `wa, wb : Word`, `(wa.add wb).val ≥ wa.val` holds iff
    `wa.val + wb.val < wordModulus` (no 256-bit unsigned addition overflow). -/
theorem word_add_no_overflow_iff_le (wa wb : Word) :
    (wa.val ≤ (wa.add wb).val) ↔ (wa.val + wb.val < wordModulus) := by
  have hA := wa.isLt
  have hB := wb.isLt
  change (wa.val ≤ (wa.val + wb.val) % wordModulus) ↔ (wa.val + wb.val < wordModulus)
  by_cases hlt : wa.val + wb.val < wordModulus
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hge : wordModulus ≤ wa.val + wb.val := Nat.le_of_not_lt hlt
    have hlt2 : wa.val + wb.val - wordModulus < wordModulus := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
    omega

/-- Boolean equivalence between `decide (wa.val ≤ (wa.add wb).val)` and
    `decide (wa.val + wb.val < wordModulus)`. -/
theorem decide_word_add_le_eq_decide_lt_modulus (wa wb : Word) :
    decide (wa.val ≤ (wa.add wb).val) = decide (wa.val + wb.val < wordModulus) :=
  decide_eq_decide.mpr (word_add_no_overflow_iff_le wa wb)

/-! ## 3. Extended `SolcoreCheckedStmt` AST, Compiler, and Execution Semantics -/

/-- Extended `Solcore` statement language supporting storage/transient loads,
    aligned memory writes, checked 256-bit arithmetic (`Panic(0x11)`),
    `require` guards, conditionals, and bounded loops. -/
inductive SolcoreCheckedStmt where
  | straight (s : SolcoreStraightLineStmt)
  | sloadLocal (dst : String) (fieldName : String) (slot : Word)
  | tloadLocal (dst : String) (slot : Word)
  | mstoreWord (offset : Word) (valExpr : SolcorePureExpr)
  | addChecked (dst : String) (a b : SolcorePureExpr)
  | subChecked (dst : String) (a b : SolcorePureExpr)
  | requireGuard (cond : SolcorePureExpr) (errWord : Word)
  | iteBranch (cond : SolcorePureExpr) (thenBr elseBr : SolcoreStraightLineStmt)
  | boundedIter (fuel : Nat) (body : SolcoreStraightLineStmt)
  deriving Repr

/-- Execution outcome of a `SolcoreCheckedStmt`: either continues with an
    updated `SolcoreExecState` or reverts with `(sState, revWord)`. -/
inductive SolcoreCheckedOutcome where
  | continued (sState : SolcoreExecState)
  | reverted (sState : SolcoreExecState) (revWord : Word)

namespace SolcoreCheckedStmt

/-- Total compiler from `SolcoreCheckedStmt` to `List Compiler.CompilationModel.Stmt`. -/
def toVerity : SolcoreCheckedStmt → List Compiler.CompilationModel.Stmt
  | .straight s => s.toVerity
  | .sloadLocal dst fieldName _ => [.assignVar dst (.storage fieldName)]
  | .tloadLocal dst slot => [.assignVar dst (.tload (.literal slot.val))]
  | .mstoreWord offset valExpr => [.mstore (.literal offset.val) valExpr.toVerity]
  | .addChecked dst a b =>
      [.ite (.ge (.add a.toVerity b.toVerity) a.toVerity)
        [.assignVar dst (.add a.toVerity b.toVerity)]
        [.panic .arithmeticOverflow]]
  | .subChecked dst a b =>
      [.ite (.ge a.toVerity b.toVerity)
        [.assignVar dst (.sub a.toVerity b.toVerity)]
        [.panic .arithmeticOverflow]]
  | .requireGuard cond _ =>
      [.require cond.toVerity "solcore_require"]
  | .iteBranch cond thenBr elseBr =>
      [.ite cond.toVerity thenBr.toVerity elseBr.toVerity]
  | .boundedIter fuel body =>
      iterToVerity fuel body

/-- Field-slot and word-aligned memory precondition for `SolcoreCheckedStmt`. -/
def StmtAligned (fields : List Field) (dState : DenoteState) : SolcoreCheckedStmt → Prop
  | .straight s => s.FieldsAligned fields
  | .sloadLocal _ fieldName slot =>
      ∃ field : Field,
        findFieldWithResolvedSlot fields fieldName = some (field, slot.val) ∧
        field.isTransient = false ∧
        field.packedBits = none
  | .tloadLocal _ _ | .addChecked _ _ _ | .subChecked _ _ _ | .requireGuard _ _ => True
  | .mstoreWord offset _ =>
      ∀ (v : Word) (candidate : Word),
        ((dState.world.writePhysicalMemoryValue offset.val v.val).memory candidate.val).val =
          if candidate = offset then v.val else (dState.world.memory candidate.val).val
  | .iteBranch _ thenBr elseBr =>
      thenBr.FieldsAligned fields ∧ elseBr.FieldsAligned fields
  | .boundedIter _ body =>
      body.FieldsAligned fields

/-- Execute a `SolcoreCheckedStmt` on `SolcoreExecState`. -/
def execSolcore (stmt : SolcoreCheckedStmt) (sState : SolcoreExecState) : SolcoreCheckedOutcome :=
  match stmt with
  | .straight s => .continued (s.execSolcore sState)
  | .sloadLocal dst _ slot => .continued (sState.setLocal dst (sState.sload slot))
  | .tloadLocal dst slot => .continued (sState.setLocal dst (sState.tload slot))
  | .mstoreWord offset valExpr => .continued (sState.mstore offset (valExpr.evalWord sState))
  | .addChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      if decide (wa.val + wb.val < wordModulus) then
        .continued (sState.setLocal dst (wa.add wb))
      else
        .reverted sState panicArithWord
  | .subChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      if decide (wb.val ≤ wa.val) then
        .continued (sState.setLocal dst (wa.sub wb))
      else
        .reverted sState panicArithWord
  | .requireGuard cond errWord =>
      if (cond.evalWord sState).val != 0 then
        .continued sState
      else
        .reverted sState errWord
  | .iteBranch cond thenBr elseBr =>
      if (cond.evalWord sState).val != 0 then
        .continued (thenBr.execSolcore sState)
      else
        .continued (elseBr.execSolcore sState)
  | .boundedIter fuel body =>
      .continued (execIterSolcore fuel body sState)

/-- Target `DenoteState` reached when `stmt` continues without reverting. -/
def execDenote (stmt : SolcoreCheckedStmt) (sState : SolcoreExecState) (dState : DenoteState) :
    DenoteState :=
  match stmt with
  | .straight s => s.execDenote sState dState
  | .sloadLocal dst _ slot =>
      { dState with bindings := Denote.bindValue dState.bindings dst (sState.sload slot).val }
  | .tloadLocal dst slot =>
      { dState with bindings := Denote.bindValue dState.bindings dst (sState.tload slot).val }
  | .mstoreWord offset valExpr =>
      { dState with
          world := dState.world.writePhysicalMemoryValue offset.val (valExpr.evalWord sState).val }
  | .addChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      { dState with bindings := Denote.bindValue dState.bindings dst (wa.add wb).val }
  | .subChecked dst a b =>
      let wa := a.evalWord sState
      let wb := b.evalWord sState
      { dState with bindings := Denote.bindValue dState.bindings dst (wa.sub wb).val }
  | .requireGuard _ _ => dState
  | .iteBranch cond thenBr elseBr =>
      if (cond.evalWord sState).val != 0 then
        thenBr.execDenote sState dState
      else
        elseBr.execDenote sState dState
  | .boundedIter fuel body =>
      execIterDenote fuel body sState dState

end SolcoreCheckedStmt

/-! ## 4. Per-Construct & Master Semantic Preservation Theorems -/

private theorem mstoreWord_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (offset valWord : Word)
    (hMemAlign : ∀ (v : Word) (candidate : Word),
      ((dState.world.writePhysicalMemoryValue offset.val v.val).memory candidate.val).val =
        if candidate = offset then v.val else (dState.world.memory candidate.val).val) :
    StateRefines
      (sState.mstore offset valWord)
      { dState with world := dState.world.writePhysicalMemoryValue offset.val valWord.val }
      initialWorld where
  storage_eq := hRef.storage_eq
  transient_eq := hRef.transient_eq
  memory_eq := fun candidate => by
    rw [hMemAlign valWord candidate]
    by_cases hEq : candidate = offset
    · subst hEq; simp [SolcoreExecState.mload, SolcoreExecState.mstore]
    · simp only [SolcoreExecState.mload, SolcoreExecState.mstore, hEq, ↓reduceIte]
      exact hRef.memory_eq candidate
  locals_eq := hRef.locals_eq
  journal_len_eq := hRef.journal_len_eq
  checkpoint_storage_eq := hRef.checkpoint_storage_eq
  checkpoint_transient_eq := hRef.checkpoint_transient_eq
  checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq

private theorem evalExpr_ge_add_toVerity
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (a b : SolcorePureExpr) :
    Denote.evalExpr oracle fields dState (.ge (.add a.toVerity b.toVerity) a.toVerity) =
      some (Denote.boolWord (decide ((a.evalWord sState).val + (b.evalWord sState).val < wordModulus))) := by
  have hAdd := evalExpr_toVerity_eq_evalWord hRef oracle fields (.add a b)
  have hA := evalExpr_toVerity_eq_evalWord hRef oracle fields a
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hAdd
  change ((Denote.evalExpr oracle fields dState (.add a.toVerity b.toVerity)).bind fun lhs =>
    (Denote.evalExpr oracle fields dState a.toVerity).bind fun rhs =>
      some (Denote.boolWord (decide (rhs ≤ lhs)))) = _
  rw [hAdd, hA, ← decide_word_add_le_eq_decide_lt_modulus]
  rfl

private theorem evalExpr_ge_sub_toVerity
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (a b : SolcorePureExpr) :
    Denote.evalExpr oracle fields dState (.ge a.toVerity b.toVerity) =
      some (Denote.boolWord (decide ((b.evalWord sState).val ≤ (a.evalWord sState).val))) := by
  have hA := evalExpr_toVerity_eq_evalWord hRef oracle fields a
  have hB := evalExpr_toVerity_eq_evalWord hRef oracle fields b
  change ((Denote.evalExpr oracle fields dState a.toVerity).bind fun lhs =>
    (Denote.evalExpr oracle fields dState b.toVerity).bind fun rhs =>
      some (Denote.boolWord (decide (rhs ≤ lhs)))) = _
  rw [hA, hB]
  rfl

/-- Target postcondition of `compileSolcoreCheckedStmt_preserves_semantics`. -/
def CheckedStmtPreservesSemantics
    {TrapReason : Type}
    (stmt : SolcoreCheckedStmt)
    (sState : SolcoreExecState) (dState : DenoteState)
    (initialWorld : Verity.ContractState)
    (oracle : DenoteOracle) (spec : CompilationModel) : Prop :=
  match stmt.execSolcore sState with
  | .continued sFinal =>
      Denote.execStmtList oracle spec.fields dState stmt.toVerity =
        .continue (stmt.execDenote sState dState) ∧
      StateRefines sFinal (stmt.execDenote sState dState) initialWorld
  | .reverted sFinal revWord =>
      (∃ bytes, Denote.execStmtList oracle spec.fields dState stmt.toVerity =
        .revertWithData bytes) ∧
      ∃ snap : SolcoreFrameSnapshot,
        sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) =
          some snap ∧
        SnapshotRefinesResult sState.contractAddress snap
          (Denote.revertedResult oracle spec initialWorld)

private theorem compileSolcoreCheckedStmt_sloadLocal
    {TrapReason : Type} (dst fieldName : String) (slot : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.sloadLocal dst fieldName slot).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.sloadLocal dst fieldName slot) sState dState initialWorld oracle spec := by
  rcases hAligned with ⟨field, hField, hPers, hUnp⟩
  have hSload := sload_refines_evalExpr_storage hRef oracle spec.fields fieldName field slot hField hPers hUnp
  refine ⟨?_, setLocal_preserves_stateRefines hRef dst (sState.sload slot)⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hSload]

private theorem compileSolcoreCheckedStmt_tloadLocal
    {TrapReason : Type} (dst : String) (slot : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.tloadLocal dst slot) sState dState initialWorld oracle spec := by
  have hSlot : Denote.evalExpr oracle spec.fields dState (.literal slot.val) = some slot.val :=
    (exprRefines_word [] [] oracle spec.fields dState slot).2
  have hTload := tload_refines_evalExpr hRef hSlot
  refine ⟨?_, setLocal_preserves_stateRefines hRef dst (sState.tload slot)⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hTload]

private theorem compileSolcoreCheckedStmt_mstoreWord
    {TrapReason : Type} (offset : Word) (valExpr : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.mstoreWord offset valExpr).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.mstoreWord offset valExpr) sState dState initialWorld oracle spec := by
  have hOff : Denote.evalExpr oracle spec.fields dState (.literal offset.val) = some offset.val :=
    (exprRefines_word [] [] oracle spec.fields dState offset).2
  have hVal := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields valExpr
  refine ⟨?_, mstoreWord_preserves_stateRefines hRef offset (valExpr.evalWord sState) hAligned⟩
  simp [SolcoreCheckedStmt.toVerity, SolcoreCheckedStmt.execDenote,
    Denote.execStmtList, Denote.execStmt, hOff, hVal]

private theorem compileSolcoreCheckedStmt_addChecked
    {TrapReason : Type} (dst : String) (a b : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.addChecked dst a b) sState dState initialWorld oracle spec := by
  have hGe := evalExpr_ge_add_toVerity hRef oracle spec.fields a b
  have hAdd := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields (.add a b)
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hAdd
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hCond : decide ((a.evalWord sState).val + (b.evalWord sState).val < wordModulus)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.panicBytes 0x11, ?_⟩,
      revert_rollback_refines_denote hRef oracle spec panicArithWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord]
  · simp only [↓reduceIte]
    refine ⟨?_, setLocal_preserves_stateRefines hRef dst ((a.evalWord sState).add (b.evalWord sState))⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord, hAdd]

private theorem compileSolcoreCheckedStmt_subChecked
    {TrapReason : Type} (dst : String) (a b : SolcorePureExpr)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.subChecked dst a b) sState dState initialWorld oracle spec := by
  have hGe := evalExpr_ge_sub_toVerity hRef oracle spec.fields a b
  have hSub := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields (.sub a b)
  simp only [SolcorePureExpr.toVerity, SolcorePureExpr.evalWord] at hSub
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hCond : decide ((b.evalWord sState).val ≤ (a.evalWord sState).val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.panicBytes 0x11, ?_⟩,
      revert_rollback_refines_denote hRef oracle spec panicArithWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord]
  · simp only [↓reduceIte]
    refine ⟨?_, setLocal_preserves_stateRefines hRef dst ((a.evalWord sState).sub (b.evalWord sState))⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hGe, hCond, Denote.boolWord, hSub]

private theorem compileSolcoreCheckedStmt_requireGuard
    {TrapReason : Type} (cond : SolcorePureExpr) (errWord : Word)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.requireGuard cond errWord) sState dState initialWorld oracle spec := by
  have hCondEval := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields cond
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hNz : ((cond.evalWord sState).val != 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨Denote.errorStringBytes "solcore_require", ?_⟩,
      revert_rollback_refines_denote hRef oracle spec errWord hEncodeInit⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt, hCondEval, hNz]
  · simp only [↓reduceIte]
    refine ⟨?_, hRef⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt, hCondEval, hNz]

private theorem compileSolcoreCheckedStmt_iteBranch
    {TrapReason : Type} (cond : SolcorePureExpr) (thenBr elseBr : SolcoreStraightLineStmt)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : (SolcoreCheckedStmt.iteBranch cond thenBr elseBr).StmtAligned spec.fields dState) :
    CheckedStmtPreservesSemantics (TrapReason := TrapReason)
      (.iteBranch cond thenBr elseBr) sState dState initialWorld oracle spec := by
  have hCondEval := evalExpr_toVerity_eq_evalWord hRef oracle spec.fields cond
  simp only [CheckedStmtPreservesSemantics, SolcoreCheckedStmt.execSolcore,
    SolcoreCheckedStmt.execDenote]
  cases hNz : ((cond.evalWord sState).val != 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hExecE, hRefE⟩ :=
      compileSolcoreStmt_preserves_stateRefines elseBr hRef oracle spec.fields hAligned.2
    refine ⟨?_, hRefE⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hCondEval, hNz, hExecE]
  · simp only [↓reduceIte]
    obtain ⟨hExecT, hRefT⟩ :=
      compileSolcoreStmt_preserves_stateRefines thenBr hRef oracle spec.fields hAligned.1
    refine ⟨?_, hRefT⟩
    simp [SolcoreCheckedStmt.toVerity, Denote.execStmtList, Denote.execStmt,
      hCondEval, hNz, hExecT]

/-- **Master `SolcoreCheckedStmt` Semantic Preservation Theorem**:
    - On `.continued sFinal`, `Denote.execStmtList` reaches `.continue (stmt.execDenote sState dState)`
      and `StateRefines sFinal (stmt.execDenote sState dState) initialWorld` holds.
    - On `.reverted sFinal revWord`, `Denote.execStmtList` reverts with `revertWithData` and
      `sFinal.resolveFrame (.reverted revWord)` rolls back storage and events to refine
      `Denote.revertedResult oracle spec initialWorld`. -/
theorem compileSolcoreCheckedStmt_preserves_semantics
    {TrapReason : Type} (stmt : SolcoreCheckedStmt)
    {sState : SolcoreExecState} {dState : DenoteState} {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (hAligned : stmt.StmtAligned spec.fields dState)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val = (initialWorld.readSlot slot.val).val) :
    match stmt.execSolcore sState with
    | .continued sFinal =>
        Denote.execStmtList oracle spec.fields dState stmt.toVerity =
          .continue (stmt.execDenote sState dState) ∧
        StateRefines sFinal (stmt.execDenote sState dState) initialWorld
    | .reverted sFinal revWord =>
        (∃ bytes, Denote.execStmtList oracle spec.fields dState stmt.toVerity = .revertWithData bytes) ∧
        ∃ snap : SolcoreFrameSnapshot,
          sFinal.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revWord) = some snap ∧
          SnapshotRefinesResult sState.contractAddress snap
            (Denote.revertedResult oracle spec initialWorld) := by
  change CheckedStmtPreservesSemantics (TrapReason := TrapReason)
    stmt sState dState initialWorld oracle spec
  cases stmt with
  | straight s => exact compileSolcoreStmt_preserves_stateRefines s hRef oracle spec.fields hAligned
  | sloadLocal d f s => exact compileSolcoreCheckedStmt_sloadLocal d f s hRef oracle spec hAligned
  | tloadLocal d s => exact compileSolcoreCheckedStmt_tloadLocal d s hRef oracle spec
  | mstoreWord o v => exact compileSolcoreCheckedStmt_mstoreWord o v hRef oracle spec hAligned
  | addChecked d a b => exact compileSolcoreCheckedStmt_addChecked d a b hRef oracle spec hEncodeInit
  | subChecked d a b => exact compileSolcoreCheckedStmt_subChecked d a b hRef oracle spec hEncodeInit
  | requireGuard c e => exact compileSolcoreCheckedStmt_requireGuard c e hRef oracle spec hEncodeInit
  | iteBranch c t e => exact compileSolcoreCheckedStmt_iteBranch c t e hRef oracle spec hAligned
  | boundedIter k b => exact execIter_preserves_stateRefines k b hRef oracle spec.fields hAligned

/-! ## 5. Quadrangular Preservation (`Solcore → Denote → SourceSemantics → IR`) -/

/-- **Quadrangular End-to-End Semantic Preservation (`solcore_to_verity_quadrangular_preservation`)**:
    Composes:
    1. `CertifiedContractTranslationWitness` (`Layer 0 Solcore → Layer 1 Denote`),
    2. `MetaSpecs.TriangularSemanticMetaSpec` (`Layer 1 Denote → Layer 2 SourceSemantics → Layer 2 IR`), and
    3. `MetaSpecs.CertifiedOrExplicitlyFlagged` (`SurfaceMask` trust-boundary partition)
    into a single end-to-end preservation theorem from `Solcore` to `IRState`. -/
theorem solcore_to_verity_quadrangular_preservation
    {SourceState IRState Obs : Type}
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {retWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .returned retWord))
    {obsDenote : DenoteResult → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteResult → DenoteResult}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteResult → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    {s0 : SourceState} {i0 : IRState}
    (hDS : relDS (Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld) s0)
    (hSI : relSI s0 i0)
    (allowedMask : SurfaceMask) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = true ∧
    dResult.returnValue = some retWord.val ∧
    (∀ slot : Word,
      (sState.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.journal.logs.length = dResult.events.length ∧
    obsDenote dResult = obsIR i0 ∧
    obsDenote (stepDenote dResult) = obsIR (stepIR i0) ∧
    CertifiedOrExplicitlyFlagged cw.spec allowedMask := by
  obtain ⟨hMem, hSucc, hRet, hStor, hLogs⟩ :=
    certifiedContractTranslationWitness_returned_soundness
      cw hLookup tx sWorld initialWorld hInit hEval
  exact ⟨hMem, hSucc, hRet, hStor, hLogs,
    triangular_obs_eq hTri hDS hSI,
    triangular_commutes hTri hDS hSI,
    trust_boundary_partition_complete cw.spec allowedMask⟩

/-- **Quadrangular Revert & Rollback Preservation (`solcore_to_verity_quadrangular_revert_preservation`)**:
    On `.reverted revWord`, storage and journal roll back to `sState.checkpoint`,
    `Denote` and `IRState` agree on revert classification across `n` steps, and
    `CertifiedOrExplicitlyFlagged` holds for `cw.spec`. -/
theorem solcore_to_verity_quadrangular_revert_preservation
    {SourceState IRState Obs : Type}
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {revWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .reverted revWord))
    {obsDenote : DenoteResult → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteResult → DenoteResult}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteResult → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    (isRevert : Obs → Bool) (n : Nat)
    {s0 : SourceState} {i0 : IRState}
    (hDS : relDS (Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld) s0)
    (hSI : relSI s0 i0)
    (allowedMask : SurfaceMask) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = false ∧
    dResult.returnValue = none ∧
    (∀ slot : Word,
      (sState.checkpoint.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.checkpoint.journal.logs.length = dResult.events.length ∧
    isRevert (obsDenote (iterateStep stepDenote n dResult)) =
      isRevert (obsIR (iterateStep stepIR n i0)) ∧
    CertifiedOrExplicitlyFlagged cw.spec allowedMask := by
  obtain ⟨hMem, hSucc, hRet, hStor, hLogs⟩ :=
    certifiedContractTranslationWitness_reverted_soundness
      cw hLookup tx sWorld initialWorld hInit hEval
  exact ⟨hMem, hSucc, hRet, hStor, hLogs,
    triangular_revert_equivalence hTri isRevert n hDS hSI,
    trust_boundary_partition_complete cw.spec allowedMask⟩

end Compiler.Proofs.SolidityImport.SolcoreFullBridge
