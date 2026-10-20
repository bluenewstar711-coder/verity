/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Std.Data.HashSet
import Std.Data.HashMap
import Compiler.CompilationModel.Types
import Compiler.ProofStatus

/-!
# Linear-Time Trust Surface Collectors and Call-Graph Analyzer

This module provides $\mathcal{O}(N)$ and $\mathcal{O}(V + E)$ algorithms for
`TrustSurface` analysis over `CompilationModel` ASTs:

1. `dedupPreserveHashable` and `dedupPreserveLinear`: single-pass order-preserving
   deduplication backed by `Std.HashSet` and `Array` in $\mathcal{O}(N)$ time.
2. `CallGraphIndex` and `expandTransitiveInternalCallsLinear`: explicit worklist
   traversal with a `Std.HashSet` visited set and `Std.HashMap` adjacency index
   in $\mathcal{O}(V + E)$ time, bounded by `graph.size + roots.length` fuel so
   that all definitions remain total without `partial`.
3. `collectExprLowLevelMechanicsAcc` and `collectStmtLowLevelMechanicsAcc`:
   single-pass accumulator traversals using $\mathcal{O}(1)$ list cons (`::`)
   instead of quadratic `++` appends.
4. `linearTrustSurfaceReport` and `undischargedAssumptionReportEntriesLinear`:
   linear-time assumption and trust-boundary inventory generation.
-/

namespace Compiler.CompilationModel

/-!
## Order-Preserving $\mathcal{O}(N)$ Deduplication
-/

/-- Single-pass worker loop for order-preserving deduplication using a `Std.HashSet`
    seen-set and an `Array` accumulator. -/
def dedupPreserveHashableLoop [BEq α] [Hashable α]
    (seen : Std.HashSet α) (acc : Array α) : List α → Array α
  | [] => acc
  | x :: xs =>
      if seen.contains x then
        dedupPreserveHashableLoop seen acc xs
      else
        dedupPreserveHashableLoop (seen.insert x) (acc.push x) xs

/-- Generic $\mathcal{O}(N)$ order-preserving deduplication over hashable elements. -/
def dedupPreserveHashable [BEq α] [Hashable α] (xs : List α) : Array α :=
  dedupPreserveHashableLoop (∅ : Std.HashSet α) #[] xs

/-- $\mathcal{O}(N)$ order-preserving deduplication over `String` lists using
    `Std.HashSet String` and `Array String`. -/
def dedupPreserveLinear (xs : List String) : List String :=
  (dedupPreserveHashable xs).toList

/-- Reference specification for order-preserving deduplication via `List.foldl`. -/
def dedupPreserveSpec [BEq α] (items : List α) : List α :=
  items.foldl (fun acc item => if acc.contains item then acc else acc ++ [item]) []

/-!
## $\mathcal{O}(V + E)$ Internal Call-Graph Worklist Traversal
-/

/-- Adjacency index mapping each internal function name to its direct internal callees. -/
abbrev CallGraphIndex := Std.HashMap String (Array String)

/-- Enqueue all unvisited callee names into `(seen, acc, worklist)` in a single pass. -/
def enqueueUnvisited
    (seen : Std.HashSet String) (acc : Array String) (worklist : List String) :
    List String → Std.HashSet String × Array String × List String
  | [] => (seen, acc, worklist)
  | x :: xs =>
      if seen.contains x then
        enqueueUnvisited seen acc worklist xs
      else
        enqueueUnvisited (seen.insert x) (acc.push x) (x :: worklist) xs

/-- Fuel-bounded worklist traversal over `CallGraphIndex`. Each step pops one
    visited vertex `curr` from `worklist` and enqueues its unvisited neighbors. -/
def expandTransitiveWorklist (graph : CallGraphIndex) :
    Nat → Std.HashSet String → Array String → List String → Array String
  | 0, _, acc, _ => acc
  | _ + 1, _, acc, [] => acc
  | fuel + 1, seen, acc, curr :: rest =>
      let callees := (graph.getD curr #[]).toList
      let step := enqueueUnvisited seen acc rest callees
      expandTransitiveWorklist graph fuel step.1 step.2.1 step.2.2

/-- Expand all internal helper names transitively reachable from `roots` in `graph`
    using an explicit worklist and `Std.HashSet` visited set in $\mathcal{O}(V + E)$ time. -/
def expandTransitiveInternalCallsLinear (graph : CallGraphIndex) (roots : List String) : List String :=
  let init := enqueueUnvisited (∅ : Std.HashSet String) #[] [] roots
  (expandTransitiveWorklist graph (graph.size + roots.length) init.1 init.2.1 init.2.2).toList

/-- Single-pass accumulator traversal collecting direct internal call names from an `Expr`. -/
def collectDirectInternalCallNamesExprAcc (acc : List String) (expr : Expr) : List String :=
  let accAfterNode :=
    match expr with
    | .internalCall calleeName _ => calleeName :: acc
    | _ => acc
  expr.children.attach.foldl
    (fun cur ⟨child, hchild⟩ =>
      have := Expr.children_sizeOf_lt expr child hchild
      collectDirectInternalCallNamesExprAcc cur child)
    accAfterNode
termination_by sizeOf expr

/-- Single-pass accumulator collection of direct internal call names from a `List Stmt`. -/
def collectDirectInternalCallNamesStmtsAcc (acc : List String) (stmts : List Stmt) : List String :=
  Stmt.foldList
    (fun cur stmt md =>
      let afterStmt :=
        match stmt with
        | .internalCall calleeName _ => calleeName :: cur
        | .internalCallAssign _ calleeName _ => calleeName :: cur
        | _ => cur
      md.subexpressions.foldl collectDirectInternalCallNamesExprAcc afterStmt)
    acc
    stmts

/-- Collect deduplicated direct internal call names from `stmts` in $\mathcal{O}(N)$ time. -/
def collectDirectInternalCallNamesStmtsLinear (stmts : List Stmt) : List String :=
  dedupPreserveLinear (collectDirectInternalCallNamesStmtsAcc [] stmts).reverse

/-- Build a `CallGraphIndex` (`Std.HashMap String (Array String)`) for all internal functions. -/
def buildCallGraphIndex (internalFunctions : List FunctionSpec) : CallGraphIndex :=
  internalFunctions.foldl
    (fun acc fn =>
      let callees := collectDirectInternalCallNamesStmtsLinear fn.body
      acc.insert fn.name callees.toArray)
    (∅ : CallGraphIndex)

/-- Collect all internal helper names transitively reachable from `stmts` in `model`
    in $\mathcal{O}(V + E)$ time. -/
def collectTransitiveInternalCallsLinear (model : CompilationModel) (stmts : List Stmt) : List String :=
  let internalFunctions := model.functions.filter (·.isInternal)
  let graph := buildCallGraphIndex internalFunctions
  let direct := collectDirectInternalCallNamesStmtsLinear stmts
  expandTransitiveInternalCallsLinear graph direct

/-!
## Single-Pass Accumulator Collection of Low-Level Mechanics
-/

/-- Direct low-level mechanic name at a single `Expr` AST node, if any. -/
def exprNodeLowLevelMechanic? : Expr → Option String
  | .intrinsic _ (.builtin "create2") _ _ => some "create2"
  | .intrinsic _ (.builtin "extcodecopy") _ _ => some "extcodecopy"
  | .intrinsic _ (.builtin "codecopy") _ _ => some "codecopy"
  | .call _ _ _ _ _ _ _ => some "call"
  | .staticcall _ _ _ _ _ _ => some "staticcall"
  | .delegatecall _ _ _ _ _ _ => some "delegatecall"
  | .returndataSize => some "returndataSize"
  | .blobbasefee => some "blobbasefee"
  | .tload _ => some "tload"
  | .returndataOptionalBoolAt _ => some "returndataOptionalBoolAt"
  | .mload _ => some "mload"
  | .calldataload _ => some "calldataload"
  | .extcodesize _ => some "extcodesize"
  | _ => none

/-- Single-pass accumulator traversal collecting low-level mechanics from `expr`
    using $\mathcal{O}(1)$ list cons (`::`) without quadratic `++` appends. -/
def collectExprLowLevelMechanicsAcc (acc : List String) (expr : Expr) : List String :=
  let accAfterNode :=
    match exprNodeLowLevelMechanic? expr with
    | some m => m :: acc
    | none => acc
  expr.children.attach.foldl
    (fun cur ⟨child, hchild⟩ =>
      have := Expr.children_sizeOf_lt expr child hchild
      collectExprLowLevelMechanicsAcc cur child)
    accAfterNode
termination_by sizeOf expr

/-- Single-pass accumulator update for a statement metadata node without `++`. -/
def collectStmtMetadataLowLevelMechanicsAcc (acc : List String) (md : StmtMetadata) : List String :=
  let accAfterStmt :=
    md.lowLevelMechanics.foldl (fun cur m => m.toReportString :: cur) acc
  md.subexpressions.foldl collectExprLowLevelMechanicsAcc accAfterStmt

/-- Single-pass accumulator collection of low-level mechanics over a single `Stmt`. -/
def collectStmtLowLevelMechanicsAcc (acc : List String) (stmt : Stmt) : List String :=
  stmt.fold (fun cur _ md => collectStmtMetadataLowLevelMechanicsAcc cur md) acc

/-- Single-pass accumulator collection of low-level mechanics over a `List Stmt`. -/
def collectStmtsLowLevelMechanicsAcc (acc : List String) (stmts : List Stmt) : List String :=
  Stmt.foldList (fun cur _ md => collectStmtMetadataLowLevelMechanicsAcc cur md) acc stmts

/-- Collect deduplicated low-level mechanics from `stmts` in $\mathcal{O}(N)$ time. -/
def collectLowLevelMechanicsFromStmtsLinear (stmts : List Stmt) : List String :=
  dedupPreserveLinear (collectStmtsLowLevelMechanicsAcc [] stmts).reverse

/-- Collect deduplicated low-level mechanics across an entire `CompilationModel` in $\mathcal{O}(N)$ time. -/
def collectLowLevelMechanicsLinear (model : CompilationModel) : List String :=
  let afterCtor :=
    match model.constructor with
    | some ctor => collectStmtsLowLevelMechanicsAcc [] ctor.body
    | none => []
  let afterFns :=
    model.functions.foldl
      (fun acc fn => collectStmtsLowLevelMechanicsAcc acc fn.body)
      afterCtor
  dedupPreserveLinear afterFns.reverse

/-- Single-pass accumulator collection of `unsafe` block reasons from `stmts`. -/
def collectUnsafeBlockReasonsAcc (acc : List String) (stmts : List Stmt) : List String :=
  Stmt.foldList
    (fun cur _ md => md.unsafeReasons.foldl (fun c r => r :: c) cur)
    acc
    stmts

/-- Collect deduplicated `unsafe` block reasons from `stmts` in $\mathcal{O}(N)$ time. -/
def collectUnsafeBlockReasonsFromStmtsLinear (stmts : List Stmt) : List String :=
  dedupPreserveLinear (collectUnsafeBlockReasonsAcc [] stmts).reverse

/-!
## Linear-Time Assumption and Trust-Surface Report
-/

/-- Public trust-report entry recording a single assumption, obligation, or low-level mechanic
    at a constructor or function usage site. -/
structure AssumptionReportEntry where
  category : String
  boundaryClass : String
  siteKind : String
  siteName : String
  name : String
  status : ProofStatus
  detail : String := ""
  assumption : String := ""
  linkMode : String := ""
  moduleName : String := ""
  axioms : List String := []
  mutability : String := ""
  selector : Option Nat := none
  deriving Repr, BEq

/-- Construct a trust-report entry for a low-level mechanic at `(siteKind, siteName)`. -/
def lowLevelMechanicEntry (siteKind siteName mechanic : String) : AssumptionReportEntry :=
  { category := "lowLevelMechanic"
    boundaryClass := "compilerIntrinsic"
    siteKind := siteKind
    siteName := siteName
    name := mechanic
    status := .assumed }

/-- Construct a trust-report entry for a local proof obligation at `(siteKind, siteName)`. -/
def localObligationEntry
    (siteKind siteName : String) (obligation : LocalObligation) : AssumptionReportEntry :=
  { category := "localObligation"
    boundaryClass := "gate"
    siteKind := siteKind
    siteName := siteName
    name := obligation.name
    status := obligation.proofStatus
    detail := obligation.obligation }

/-- Construct a trust-report entry for an `unsafe` block reason at `(siteKind, siteName)`. -/
def unsafeBlockEntry (siteKind siteName reason : String) : AssumptionReportEntry :=
  { category := "unsafeBlock"
    boundaryClass := "gate"
    siteKind := siteKind
    siteName := siteName
    name := reason
    status := .assumed
    detail := reason }

/-- Linear-time trust-surface report entries for a single usage site (`constructor` or `function`). -/
def linearSiteTrustSurfaceReport
    (siteKind siteName : String)
    (localObligations : List LocalObligation)
    (stmts : List Stmt) : List AssumptionReportEntry :=
  let mechanics :=
    (collectLowLevelMechanicsFromStmtsLinear stmts).map
      (lowLevelMechanicEntry siteKind siteName)
  let obligations :=
    localObligations.map (localObligationEntry siteKind siteName)
  let unsafeBlocks :=
    (collectUnsafeBlockReasonsFromStmtsLinear stmts).map
      (unsafeBlockEntry siteKind siteName)
  mechanics ++ obligations ++ unsafeBlocks

/-- Linear-time trust-surface report entries for a single `FunctionSpec`. -/
def linearFunctionTrustSurfaceReport (fn : FunctionSpec) : List AssumptionReportEntry :=
  linearSiteTrustSurfaceReport "function" fn.name fn.localObligations fn.body

/-- Linear-time trust-surface report entries for the optional constructor of `model`. -/
def linearConstructorTrustSurfaceReport (model : CompilationModel) : List AssumptionReportEntry :=
  match model.constructor with
  | some ctor =>
      linearSiteTrustSurfaceReport "constructor" "constructor" ctor.localObligations ctor.body
  | none => []

/-- Compute the linear-time trust-surface report for `model`. -/
def linearTrustSurfaceReport (model : CompilationModel) : List AssumptionReportEntry :=
  linearConstructorTrustSurfaceReport model ++
    model.functions.flatMap linearFunctionTrustSurfaceReport

/-- Filter `linearTrustSurfaceReport model` to undischarged (`status != .proved`) entries. -/
def undischargedAssumptionReportEntriesLinear
    (model : CompilationModel) : List AssumptionReportEntry :=
  (linearTrustSurfaceReport model).filter (fun entry => entry.status != .proved)

/-- Deduplicating the empty list yields the empty list. -/
@[simp] theorem dedupPreserveLinear_nil : dedupPreserveLinear [] = [] := rfl

/-- Every low-level mechanic entry has `.assumed` proof status. -/
@[simp] theorem lowLevelMechanicEntry_status (siteKind siteName mechanic : String) :
    (lowLevelMechanicEntry siteKind siteName mechanic).status = .assumed := rfl

end Compiler.CompilationModel
