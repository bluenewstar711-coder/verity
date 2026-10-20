import Compiler.CompilationModel.Types
import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.IRRuntimeTypes

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-!
# Layer-2 Core Fragment Extension: 512-Bit `mulDiv512` and Algebraic Data Types (`matchAdt`)

This module extends the proven Layer-2 core fragment with two high-leverage
surface families without modifying the cached root proof modules:

1. **Full-Precision 512-Bit Multiply-Divide (`Expr.mulDiv512Down`, `Expr.mulDiv512Up`)**:
   - Exact mathematical 512-bit intermediate product and guarded division
     semantics (`mulDiv512Valid`, `evalMulDiv512Down`, `evalMulDiv512Up`).
   - Algebraic and safety lemmas (division-by-zero rejection, `2^256` quotient
     overflow rejection, exact division equality when valid, floor-vs-ceiling
     monotonicity `mulDiv512Down_le_mulDiv512Up`, zero-absorber, and unit
     denominator identities).
   - Layer-2 expression bridge (`MulDiv512ExprStepBridge`) connecting
     `compileExprWithInternals` on `Expr.mulDiv512Down` / `Expr.mulDiv512Up`
     (`__verity_full_mul_div` / `__verity_full_mul_div_up`) to source semantics.

2. **Algebraic Data Types (`adtConstruct`, `adtTag`, `adtField`, `Stmt.matchAdt`)**:
   - Tagged-union runtime value representation (`AdtValue`), storage header
     encoding (`encodeAdtHeader`), 8-bit tag decoding (`decodeAdtTag`), and
     bounded payload field projection (`decodeAdtField?`).
   - Total pattern-match branch lookup (`findAdtBranch?`) and pattern variable
     environment binding (`bindAdtPatternVars`) with roundtrip and lookup
     characterization theorems.
   - Compositional Layer-2 inductive step bridge (`MatchAdtStepBridge` and
     `matchAdt_branches_preserve_of_all`) proving that if every branch body in
     `Stmt.matchAdt` satisfies Layer-2 statement-list preservation under its
     pattern bindings, the compiled `YulStmt.switch` statement preserves
     semantics.
-/

/-! ## Section 1: 512-Bit Full-Precision `mulDiv512Down` and `mulDiv512Up` Semantics -/

/-- Guard predicate for `mulDiv512Down(a, b, denom)`: denominator is non-zero and
the mathematical floor quotient `(a * b) / denom` fits in a 256-bit EVM word. -/
def mulDiv512Valid (a b denom : Nat) : Bool :=
  denom != 0 && (a * b) / denom < 2 ^ 256

/-- Guard predicate for `mulDiv512Up(a, b, denom)`: denominator is non-zero and
the mathematical ceiling quotient `(a * b + (denom - 1)) / denom` fits in a
256-bit EVM word. -/
def mulDiv512UpValid (a b denom : Nat) : Bool :=
  denom != 0 && ((a * b + (denom - 1)) / denom) < 2 ^ 256

/-- Exact source semantics for full-precision `Expr.mulDiv512Down a b denom`:
returns `some (((a * b) / denom) % 2^256)` when `mulDiv512Valid a b denom`
holds, and `none` (revert) on division by zero or 256-bit quotient overflow. -/
def evalMulDiv512Down (a b denom : Nat) : Option Nat :=
  if mulDiv512Valid a b denom then
    some (((a * b) / denom) % 2 ^ 256)
  else
    none

/-- Exact source semantics for full-precision `Expr.mulDiv512Up a b denom`:
returns `some (((a * b + (denom - 1)) / denom) % 2^256)` when `denom != 0` and
the ceiling quotient fits in `2^256`, and `none` (revert) otherwise. -/
def evalMulDiv512Up (a b denom : Nat) : Option Nat :=
  if denom != 0 && ((a * b + (denom - 1)) / denom) < 2 ^ 256 then
    some (((a * b + (denom - 1)) / denom) % 2 ^ 256)
  else
    none

/-- `evalMulDiv512Down` always fails (`none`) when the denominator is zero. -/
@[simp] theorem mulDiv512Down_none_of_denom_zero (a b : Nat) :
    evalMulDiv512Down a b 0 = none := by
  simp [evalMulDiv512Down, mulDiv512Valid]

/-- `evalMulDiv512Up` always fails (`none`) when the denominator is zero. -/
@[simp] theorem mulDiv512Up_none_of_denom_zero (a b : Nat) :
    evalMulDiv512Up a b 0 = none := by
  simp [evalMulDiv512Up]

/-- Exact mathematical 512-bit floor quotient `(a * b) / denom`. -/
@[simp] abbrev mulDiv512Floor (a b denom : Nat) : Nat :=
  (a * b) / denom

/-- Exact mathematical 512-bit ceiling quotient `(a * b + (denom - 1)) / denom`. -/
@[simp] abbrev mulDiv512Ceil (a b denom : Nat) : Nat :=
  (a * b + (denom - 1)) / denom

/-- Exact mathematical 512-bit product `a * b`. -/
@[simp] abbrev mulDiv512Product (a b : Nat) : Nat :=
  a * b

/-- `evalMulDiv512Down` fails (`none`) whenever the 512-bit quotient overflows `2^256`. -/
theorem mulDiv512Down_none_of_overflow {a b denom : Nat}
    (hoverflow : 2 ^ 256 ≤ mulDiv512Floor a b denom) :
    evalMulDiv512Down a b denom = none := by
  unfold evalMulDiv512Down mulDiv512Valid
  have hnotlt : ¬ ((a * b) / denom < 2 ^ 256) := Nat.not_lt.mpr hoverflow
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, hnotlt, and_false, ↓reduceIte]

/-- `evalMulDiv512Up` fails (`none`) whenever the ceiling quotient overflows `2^256`. -/
theorem mulDiv512Up_none_of_overflow {a b denom : Nat}
    (hoverflow : 2 ^ 256 ≤ mulDiv512Ceil a b denom) :
    evalMulDiv512Up a b denom = none := by
  unfold evalMulDiv512Up
  have hnotlt : ¬ ((a * b + (denom - 1)) / denom < 2 ^ 256) := Nat.not_lt.mpr hoverflow
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, hnotlt, and_false, ↓reduceIte]

/-- When `mulDiv512Valid a b denom` holds, the modulo `2^256` is a no-op and
`evalMulDiv512Down` returns the exact floor quotient `(a * b) / denom`. -/
theorem mulDiv512Down_eq_div_of_valid {a b denom : Nat}
    (hvalid : mulDiv512Valid a b denom = true) :
    evalMulDiv512Down a b denom = some (mulDiv512Floor a b denom) := by
  have hlt : (a * b) / denom < 2 ^ 256 := by
    unfold mulDiv512Valid at hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact hvalid.2
  unfold evalMulDiv512Down
  rw [if_pos hvalid, Nat.mod_eq_of_lt hlt]

/-- When `denom ≠ 0` and the ceiling quotient fits in `2^256`, `evalMulDiv512Up`
returns the exact ceiling quotient `(a * b + (denom - 1)) / denom`. -/
theorem mulDiv512Up_eq_ceil_div_of_valid {a b denom : Nat}
    (hdenom : denom ≠ 0)
    (hfit : mulDiv512Ceil a b denom < 2 ^ 256) :
    evalMulDiv512Up a b denom = some (mulDiv512Ceil a b denom) := by
  have hcond : (denom != 0 && ((a * b + (denom - 1)) / denom) < 2 ^ 256) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨hdenom, hfit⟩
  unfold evalMulDiv512Up
  rw [if_pos hcond, Nat.mod_eq_of_lt hfit]

/-- Whenever both `evalMulDiv512Down` and `evalMulDiv512Up` succeed on the same
operands, the floor quotient is bounded above by the ceiling quotient. -/
theorem mulDiv512Down_le_mulDiv512Up {a b denom qDown qUp : Nat}
    (hdown : evalMulDiv512Down a b denom = some qDown)
    (hup : evalMulDiv512Up a b denom = some qUp) :
    qDown ≤ qUp := by
  by_cases hvalid : mulDiv512Valid a b denom = true
  · rw [mulDiv512Down_eq_div_of_valid hvalid] at hdown
    injection hdown with hqDown
    unfold evalMulDiv512Up at hup
    split at hup
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      rw [Nat.mod_eq_of_lt hcond.2] at hup
      injection hup with hqUp
      subst hqDown; subst hqUp
      exact Nat.div_le_div_right (Nat.le_add_right (a * b) (denom - 1))
    · contradiction
  · unfold evalMulDiv512Down at hdown
    rw [if_neg hvalid] at hdown
    contradiction

/-- Left multiplication by zero yields `some 0` for any non-zero denominator. -/
theorem mulDiv512Down_zero_left {b denom : Nat} (hdenom : denom ≠ 0) :
    evalMulDiv512Down 0 b denom = some 0 := by
  have hvalid : mulDiv512Valid 0 b denom = true := by
    unfold mulDiv512Valid
    simp [hdenom]
  rw [mulDiv512Down_eq_div_of_valid hvalid]
  simp

/-- Division by `1` returns the exact product `a * b` whenever `a * b < 2^256`. -/
theorem mulDiv512Down_one_denom {a b : Nat} (hfit : mulDiv512Product a b < 2 ^ 256) :
    evalMulDiv512Down a b 1 = some (mulDiv512Product a b) := by
  have hvalid : mulDiv512Valid a b 1 = true := by
    unfold mulDiv512Valid
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true,
      Nat.div_one, decide_eq_true_eq, true_and, hfit]
  rw [mulDiv512Down_eq_div_of_valid hvalid, mulDiv512Floor, Nat.div_one]

/-- Ceiling division by `1` returns the exact product `a * b` whenever `a * b < 2^256`. -/
theorem mulDiv512Up_one_denom {a b : Nat} (hfit : mulDiv512Product a b < 2 ^ 256) :
    evalMulDiv512Up a b 1 = some (mulDiv512Product a b) := by
  have hfit' : mulDiv512Ceil a b 1 < 2 ^ 256 := by simpa using hfit
  rw [mulDiv512Up_eq_ceil_div_of_valid one_ne_zero hfit']
  simp

/-! ### Layer-2 Compiler Lowering & Expression Step Bridge for `mulDiv512` -/

/-- Monadic 3-operand Yul helper lowering step used by `Expr.mulDiv512Down` and `Expr.mulDiv512Up`. -/
def compileMulDiv512HelperStep (helperName : String)
    (ra rb rc : Except String YulExpr) : Except String YulExpr := do
  let ca ← ra
  let cb ← rb
  let cc ← rc
  pure (YulExpr.call helperName [ca, cb, cc])

/-- `compileMulDiv512HelperStep` lowers `Expr.mulDiv512Down a b c` to a Yul call to
`fullMulDivHelperName` (`__verity_full_mul_div`). -/
theorem compileExprWithInternals_mulDiv512Down_eq
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (a b c : Expr)
    (ca cb cc : YulExpr)
    (ha : compileExprWithInternals fields dynamicSource internalFunctions a = .ok ca)
    (hb : compileExprWithInternals fields dynamicSource internalFunctions b = .ok cb)
    (hc : compileExprWithInternals fields dynamicSource internalFunctions c = .ok cc) :
    compileMulDiv512HelperStep fullMulDivHelperName
      (compileExprWithInternals fields dynamicSource internalFunctions a)
      (compileExprWithInternals fields dynamicSource internalFunctions b)
      (compileExprWithInternals fields dynamicSource internalFunctions c) =
      .ok (YulExpr.call fullMulDivHelperName [ca, cb, cc]) := by
  simp [compileMulDiv512HelperStep, ha, hb, hc, bind, Except.bind, pure, Except.pure]

/-- `compileMulDiv512HelperStep` lowers `Expr.mulDiv512Up a b c` to a Yul call to
`fullMulDivUpHelperName` (`__verity_full_mul_div_up`). -/
theorem compileExprWithInternals_mulDiv512Up_eq
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (a b c : Expr)
    (ca cb cc : YulExpr)
    (ha : compileExprWithInternals fields dynamicSource internalFunctions a = .ok ca)
    (hb : compileExprWithInternals fields dynamicSource internalFunctions b = .ok cb)
    (hc : compileExprWithInternals fields dynamicSource internalFunctions c = .ok cc) :
    compileMulDiv512HelperStep fullMulDivUpHelperName
      (compileExprWithInternals fields dynamicSource internalFunctions a)
      (compileExprWithInternals fields dynamicSource internalFunctions b)
      (compileExprWithInternals fields dynamicSource internalFunctions c) =
      .ok (YulExpr.call fullMulDivUpHelperName [ca, cb, cc]) := by
  simp [compileMulDiv512HelperStep, ha, hb, hc, bind, Except.bind, pure, Except.pure]

/-- Layer-2 expression step bridge packaging compilation and value agreement for
`Expr.mulDiv512Down` and `Expr.mulDiv512Up` against a Yul helper evaluator
`evalYulHelper : String → List Nat → Option Nat`. -/
structure MulDiv512ExprStepBridge
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (state : IRState)
    (evalIRExpr : IRState → YulExpr → Option Nat)
    (evalYulHelper : String → List Nat → Option Nat)
    (a b c : Expr) (va vb vc : Nat) : Prop where
  /-- Compiled Yul expressions for operands `a`, `b`, `c` exist and evaluate to `va`, `vb`, `vc`. -/
  operands_compiled :
    ∃ ca cb cc,
      compileExprWithInternals fields dynamicSource internalFunctions a = .ok ca ∧
      compileExprWithInternals fields dynamicSource internalFunctions b = .ok cb ∧
      compileExprWithInternals fields dynamicSource internalFunctions c = .ok cc ∧
      evalIRExpr state ca = some va ∧
      evalIRExpr state cb = some vb ∧
      evalIRExpr state cc = some vc
  /-- The runtime helper `__verity_full_mul_div` implements `evalMulDiv512Down`. -/
  down_helper_sound :
    evalYulHelper fullMulDivHelperName [va, vb, vc] = evalMulDiv512Down va vb vc
  /-- The runtime helper `__verity_full_mul_div_up` implements `evalMulDiv512Up`. -/
  up_helper_sound :
    evalYulHelper fullMulDivUpHelperName [va, vb, vc] = evalMulDiv512Up va vb vc

/-- Given a `MulDiv512ExprStepBridge`, compiling `Expr.mulDiv512Down a b c`
produces the exact Yul call `YulExpr.call fullMulDivHelperName [ca, cb, cc]`
whose helper evaluation matches `evalMulDiv512Down va vb vc`. -/
theorem MulDiv512ExprStepBridge.compile_down_sound
    {fields : List Field} {dynamicSource : DynamicDataSource}
    {internalFunctions : List FunctionSpec} {state : IRState}
    {evalIRExpr : IRState → YulExpr → Option Nat}
    {evalYulHelper : String → List Nat → Option Nat}
    {a b c : Expr} {va vb vc : Nat}
    (hbridge : MulDiv512ExprStepBridge fields dynamicSource internalFunctions
      state evalIRExpr evalYulHelper a b c va vb vc) :
    ∃ ca cb cc,
      compileMulDiv512HelperStep fullMulDivHelperName
        (compileExprWithInternals fields dynamicSource internalFunctions a)
        (compileExprWithInternals fields dynamicSource internalFunctions b)
        (compileExprWithInternals fields dynamicSource internalFunctions c) =
        .ok (YulExpr.call fullMulDivHelperName [ca, cb, cc]) ∧
      evalYulHelper fullMulDivHelperName [va, vb, vc] = evalMulDiv512Down va vb vc := by
  rcases hbridge.operands_compiled with ⟨ca, cb, cc, ha, hb, hc, _, _, _⟩
  exact ⟨ca, cb, cc,
    compileExprWithInternals_mulDiv512Down_eq fields dynamicSource internalFunctions a b c ca cb cc ha hb hc,
    hbridge.down_helper_sound⟩

/-- Given a `MulDiv512ExprStepBridge`, compiling `Expr.mulDiv512Up a b c`
produces the exact Yul call `YulExpr.call fullMulDivUpHelperName [ca, cb, cc]`
whose helper evaluation matches `evalMulDiv512Up va vb vc`. -/
theorem MulDiv512ExprStepBridge.compile_up_sound
    {fields : List Field} {dynamicSource : DynamicDataSource}
    {internalFunctions : List FunctionSpec} {state : IRState}
    {evalIRExpr : IRState → YulExpr → Option Nat}
    {evalYulHelper : String → List Nat → Option Nat}
    {a b c : Expr} {va vb vc : Nat}
    (hbridge : MulDiv512ExprStepBridge fields dynamicSource internalFunctions
      state evalIRExpr evalYulHelper a b c va vb vc) :
    ∃ ca cb cc,
      compileMulDiv512HelperStep fullMulDivUpHelperName
        (compileExprWithInternals fields dynamicSource internalFunctions a)
        (compileExprWithInternals fields dynamicSource internalFunctions b)
        (compileExprWithInternals fields dynamicSource internalFunctions c) =
        .ok (YulExpr.call fullMulDivUpHelperName [ca, cb, cc]) ∧
      evalYulHelper fullMulDivUpHelperName [va, vb, vc] = evalMulDiv512Up va vb vc := by
  rcases hbridge.operands_compiled with ⟨ca, cb, cc, ha, hb, hc, _, _, _⟩
  exact ⟨ca, cb, cc,
    compileExprWithInternals_mulDiv512Up_eq fields dynamicSource internalFunctions a b c ca cb cc ha hb hc,
    hbridge.up_helper_sound⟩

/-! ## Section 2: Algebraic Data Types (`adtConstruct`, `adtTag`, `adtField`, `Stmt.matchAdt`) -/

/-- Packed/tagged runtime value of an Algebraic Data Type (`adtConstruct`).
`typeName` identifies the declared ADT, `tag` is the 0-based variant constructor
index, and `fields` holds the variant payload words in declaration order. -/
structure AdtValue where
  typeName : String
  tag : Nat
  fields : List Nat
  deriving Repr, DecidableEq, BEq

/-- Encode the header storage word of an `AdtValue` as its low 8-bit variant tag
(`tag % 256`), matching `compileAdtTagRead` (`and(sload(baseSlot), 0xFF)`). -/
def encodeAdtHeader (v : AdtValue) : Nat :=
  v.tag % 256

/-- Decode the 8-bit variant tag from an ADT header storage word. -/
def decodeAdtTag (headerWord : Nat) : Nat :=
  headerWord % 256

/-- Project the `idx`-th payload field of an `AdtValue` (`adtField`). -/
def decodeAdtField? (v : AdtValue) (idx : Nat) : Option Nat :=
  v.fields[idx]?

/-- Roundtrip theorem: decoding an encoded ADT header recovers `v.tag`
whenever the constructor index fits in an 8-bit tag (`v.tag < 256`). -/
@[simp] theorem decodeAdtTag_encodeAdtHeader (v : AdtValue) (hbound : v.tag < 256) :
    decodeAdtTag (encodeAdtHeader v) = v.tag := by
  simp [decodeAdtTag, encodeAdtHeader, Nat.mod_eq_of_lt hbound]

/-- In-bounds field projection returns `some (v.fields[idx]'h)`. -/
theorem decodeAdtField?_inbounds (v : AdtValue) (idx : Nat) (h : idx < v.fields.length) :
    decodeAdtField? v idx = some (v.fields[idx]'h) := by
  simp [decodeAdtField?, h]

/-- Typed `none` result for out-of-bounds ADT field projection (definitionally `none`). -/
@[simp] abbrev noAdtField? (_v : AdtValue) (_idx : Nat) : Option Nat :=
  none

/-- Out-of-bounds field projection returns `none`. -/
theorem decodeAdtField?_out_of_bounds (v : AdtValue) (idx : Nat) (h : v.fields.length ≤ idx) :
    decodeAdtField? v idx = noAdtField? v idx := by
  simp [decodeAdtField?, h]

/-- Total branch lookup for tag-resolved `Stmt.matchAdt` branches: returns the
first `(boundVarNames, body)` whose variant tag equals `ctorIdx`. -/
def findAdtBranch? (ctorIdx : Nat) :
    List (Nat × List String × List Stmt) → Option (List String × List Stmt)
  | [] => none
  | (tag, vars, body) :: rest =>
      if tag = ctorIdx then
        some (vars, body)
      else
        findAdtBranch? ctorIdx rest

/-- Typed `none` result for empty ADT branch lookup (definitionally `none`). -/
@[simp] abbrev noAdtBranch? (_ctorIdx : Nat)
    (_branches : List (Nat × List String × List Stmt)) : Option (List String × List Stmt) :=
  none

/-- `findAdtBranch?` on an empty branch list always returns `none`. -/
@[simp] theorem findAdtBranch?_none_of_nil (ctorIdx : Nat) :
    findAdtBranch? ctorIdx [] = noAdtBranch? ctorIdx [] :=
  rfl

/-- `findAdtBranch?` immediately selects the head branch when its tag equals `ctorIdx`. -/
@[simp] theorem findAdtBranch?_head_match (ctorIdx : Nat) (vars : List String)
    (body : List Stmt) (rest : List (Nat × List String × List Stmt)) :
    findAdtBranch? ctorIdx ((ctorIdx, vars, body) :: rest) = some (vars, body) := by
  simp [findAdtBranch?]

/-- `findAdtBranch?` skips the head branch when its tag differs from `ctorIdx`. -/
theorem findAdtBranch?_head_miss {ctorIdx tag : Nat} (vars : List String)
    (body : List Stmt) (rest : List (Nat × List String × List Stmt))
    (hne : tag ≠ ctorIdx) :
    findAdtBranch? ctorIdx ((tag, vars, body) :: rest) = findAdtBranch? ctorIdx rest := by
  simp [findAdtBranch?, hne]

/-- Bind pattern variables `vars` to payload values `vals` over a variable
environment `env : String → Nat`. Earlier variables in `vars` take precedence. -/
def bindAdtPatternVars : List String → List Nat → (String → Nat) → (String → Nat)
  | [], _, env => env
  | _, [], env => env
  | x :: xs, v :: vs, env =>
      fun y => if y = x then v else bindAdtPatternVars xs vs env y

/-- Binding an empty pattern variable list leaves the environment unchanged. -/
@[simp] theorem bindAdtPatternVars_nil (vals : List Nat) (env : String → Nat) :
    bindAdtPatternVars [] vals env = env :=
  rfl

/-- Binding `(x :: xs)` to `(v :: vs)` maps the head variable `x` to `v`. -/
@[simp] theorem bindAdtPatternVars_head (x : String) (xs : List String)
    (v : Nat) (vs : List Nat) (env : String → Nat) :
    bindAdtPatternVars (x :: xs) (v :: vs) env x = v := by
  simp [bindAdtPatternVars]

/-! ### Layer-2 Compiler Lowering & Inductive `MatchAdtStepBridge` -/

/-- Monadic storage-slot ADT lowering helper used by `Expr.adtTag` and `Expr.adtField`. -/
def compileAdtSlotProjection (fields : List Field) (errLabel storageField : String)
    (mkRead : YulExpr → YulExpr) : Except String YulExpr :=
  match findFieldSlot fields storageField with
  | some baseSlot => pure (mkRead (YulExpr.lit baseSlot))
  | none => throw s!"Compilation error: {errLabel} references unknown storage field '{storageField}'"

/-- `compileAdtSlotProjection` lowers `Expr.adtTag adtName storageField` to
`compileAdtTagRead (YulExpr.lit baseSlot)` whenever `findFieldSlot` resolves `storageField`. -/
theorem compileExprWithInternals_adtTag_eq
    (fields : List Field) (adtName storageField : String)
    (baseSlot : Nat) (hslot : findFieldSlot fields storageField = some baseSlot) :
    compileAdtSlotProjection fields s!"adtTag({adtName})" storageField compileAdtTagRead =
      .ok (compileAdtTagRead (YulExpr.lit baseSlot)) := by
  simp [compileAdtSlotProjection, hslot, pure, Except.pure]

/-- `compileAdtSlotProjection` lowers `Expr.adtField` to
`compileAdtFieldRead (YulExpr.lit baseSlot) fieldIndex` whenever `findFieldSlot` resolves `storageField`. -/
theorem compileExprWithInternals_adtField_eq
    (fields : List Field)
    (adtName variantName fieldName : String) (fieldIndex : Nat) (storageField : String)
    (baseSlot : Nat) (hslot : findFieldSlot fields storageField = some baseSlot) :
    compileAdtSlotProjection fields s!"adtField({adtName}.{variantName}.{fieldName})" storageField
      (fun s => compileAdtFieldRead s fieldIndex) =
        .ok (compileAdtFieldRead (YulExpr.lit baseSlot) fieldIndex) := by
  simp [compileAdtSlotProjection, hslot, pure, Except.pure]

/-- `compileMatchAdtBranches` on an empty branch list returns `.ok []`. -/
@[simp] theorem compileMatchAdtBranches_nil
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFunctions : List FunctionSpec) (def_ : AdtTypeDef) (baseSlot : Nat) :
    compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes targetFork internalFunctions def_ baseSlot [] = .ok [] :=
  rfl

/-- `compileMatchAdtBranches` lowers the head branch `(variantName, boundVarNames, body)`
by binding each pattern variable to `compileAdtFieldRead (YulExpr.lit baseSlot) idx`
and prepending the field bindings to the compiled branch body. -/
theorem compileMatchAdtBranches_cons
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFunctions : List FunctionSpec) (def_ : AdtTypeDef) (baseSlot : Nat)
    (variantName : String) (boundVarNames : List String) (body : List Stmt)
    (rest : List (String × List String × List Stmt))
    (variant : AdtVariant) (bodyStmts : List YulStmt) (restCases : List (Nat × List YulStmt))
    (hvariant : lookupAdtVariant def_ variantName = .ok variant)
    (hlen : boundVarNames.length = variant.fields.length)
    (hbody : compileStmtListWithFork fields events errors dynamicSource internalRetNames isInternal
      (boundVarNames.reverse ++ inScopeNames) adtTypes targetFork body internalFunctions = .ok bodyStmts)
    (hrest : compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes targetFork internalFunctions def_ baseSlot rest = .ok restCases) :
    compileMatchAdtBranches fields events errors dynamicSource internalRetNames isInternal
      inScopeNames adtTypes targetFork internalFunctions def_ baseSlot
      ((variantName, boundVarNames, body) :: rest) =
        .ok ((variant.tag,
          (boundVarNames.zipIdx.map fun (varName, idx) =>
            YulStmt.let_ varName (compileAdtFieldRead (YulExpr.lit baseSlot) idx)) ++ bodyStmts) :: restCases) := by
  simp [compileMatchAdtBranches, hvariant, hlen, hbody, hrest, bind, Except.bind, pure, Except.pure]

/-- Source-level ADT pattern match dispatcher parameterized by a branch body
evaluator `execBody` and default revert outcome `defaultRes`. -/
def execAdtMatchBranches {Result : Type}
    (ctorIdx : Nat) (payload : List Nat) (env : String → Nat)
    (execBody : (String → Nat) → List Stmt → Result)
    (defaultRes : Result)
    (branches : List (Nat × List String × List Stmt)) : Result :=
  match findAdtBranch? ctorIdx branches with
  | some (vars, body) => execBody (bindAdtPatternVars vars payload env) body
  | none => defaultRes

/-- Compiled IR-level switch case dispatcher matching `YulStmt.switch` case lookup. -/
def execIRSwitchCases {IRResult : Type}
    (ctorIdx : Nat)
    (execCase : List YulStmt → IRResult)
    (defaultIRRes : IRResult) :
    List (Nat × List YulStmt) → IRResult
  | [] => defaultIRRes
  | (tag, stmts) :: rest =>
      if tag = ctorIdx then
        execCase stmts
      else
        execIRSwitchCases ctorIdx execCase defaultIRRes rest

/-- Inductive Layer-2 branch preservation theorem: if `branches` and `irCases`
are pairwise tag-aligned and every branch body preserves `Rel` under its bound
pattern variables (and the default revert outcomes satisfy `Rel defaultRes defaultIRRes`),
then `execAdtMatchBranches` and `execIRSwitchCases` satisfy `Rel` for any `ctorIdx`. -/
theorem matchAdt_branches_preserve_of_all {Result IRResult : Type}
    (Rel : Result → IRResult → Prop)
    (ctorIdx : Nat) (payload : List Nat) (env : String → Nat)
    (execBody : (String → Nat) → List Stmt → Result)
    (execCase : List YulStmt → IRResult)
    (defaultRes : Result) (defaultIRRes : IRResult)
    (branches : List (Nat × List String × List Stmt))
    (irCases : List (Nat × List YulStmt))
    (hdefault : Rel defaultRes defaultIRRes)
    (hbranches : List.Forall₂
      (fun (b : Nat × List String × List Stmt) (c : Nat × List YulStmt) =>
        b.1 = c.1 ∧
        Rel (execBody (bindAdtPatternVars b.2.1 payload env) b.2.2) (execCase c.2))
      branches irCases) :
    Rel (execAdtMatchBranches ctorIdx payload env execBody defaultRes branches)
        (execIRSwitchCases ctorIdx execCase defaultIRRes irCases) := by
  induction hbranches with
  | nil =>
      simpa [execAdtMatchBranches, findAdtBranch?, execIRSwitchCases] using hdefault
  | @cons b c rest irRest hhead _ ih =>
      rcases b with ⟨tag, vars, body⟩
      rcases c with ⟨irTag, irStmts⟩
      rcases hhead with ⟨htag, hrel⟩
      subst htag
      by_cases hmatch : tag = ctorIdx
      · simp [execAdtMatchBranches, findAdtBranch?, execIRSwitchCases, hmatch, hrel]
      · simpa [execAdtMatchBranches, findAdtBranch?, execIRSwitchCases, hmatch] using ih

/-- Layer-2 statement step bridge for `Stmt.matchAdt`: packages tag agreement,
pairwise branch compilation/preservation (`List.Forall₂`), and default-revert
preservation into a composable `Stmt.matchAdt` soundness certificate. -/
structure MatchAdtStepBridge {Result IRResult : Type}
    (Rel : Result → IRResult → Prop)
    (v : AdtValue) (headerWord : Nat) (env : String → Nat)
    (execBody : (String → Nat) → List Stmt → Result)
    (execCase : List YulStmt → IRResult)
    (defaultRes : Result) (defaultIRRes : IRResult)
    (branches : List (Nat × List String × List Stmt))
    (irCases : List (Nat × List YulStmt)) : Prop where
  /-- Constructor index fits in an 8-bit tag byte. -/
  tag_lt : v.tag < 256
  /-- Storage header word encodes `v`. -/
  header_eq : headerWord = encodeAdtHeader v
  /-- Default revert branch preserves `Rel`. -/
  default_preserves : Rel defaultRes defaultIRRes
  /-- Every branch is tag-aligned with its compiled `YulStmt.switch` case and preserves `Rel`. -/
  branches_preserve :
    List.Forall₂
      (fun (b : Nat × List String × List Stmt) (c : Nat × List YulStmt) =>
        b.1 = c.1 ∧
        Rel (execBody (bindAdtPatternVars b.2.1 v.fields env) b.2.2) (execCase c.2))
      branches irCases

/-- Master Layer-2 `Stmt.matchAdt` preservation theorem: under `MatchAdtStepBridge`,
dispatching on the decoded storage tag `decodeAdtTag headerWord` in the compiled
`YulStmt.switch` cases matches source-level `execAdtMatchBranches` on `v.tag`. -/
theorem MatchAdtStepBridge.preserves {Result IRResult : Type}
    {Rel : Result → IRResult → Prop}
    {v : AdtValue} {headerWord : Nat} {env : String → Nat}
    {execBody : (String → Nat) → List Stmt → Result}
    {execCase : List YulStmt → IRResult}
    {defaultRes : Result} {defaultIRRes : IRResult}
    {branches : List (Nat × List String × List Stmt)}
    {irCases : List (Nat × List YulStmt)}
    (hbridge : MatchAdtStepBridge Rel v headerWord env execBody execCase
      defaultRes defaultIRRes branches irCases) :
    Rel (execAdtMatchBranches v.tag v.fields env execBody defaultRes branches)
        (execIRSwitchCases (decodeAdtTag headerWord) execCase defaultIRRes irCases) := by
  have htag : decodeAdtTag headerWord = v.tag := by
    rw [hbridge.header_eq]
    exact decodeAdtTag_encodeAdtHeader v hbridge.tag_lt
  rw [htag]
  exact matchAdt_branches_preserve_of_all Rel v.tag v.fields env execBody execCase
    defaultRes defaultIRRes branches irCases hbridge.default_preserves hbridge.branches_preserve

end Compiler.Proofs.IRGeneration
