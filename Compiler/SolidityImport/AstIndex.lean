import Lean
import Std.Data.HashMap

set_option autoImplicit false

/-!
# $\mathcal{O}(1)$ Solc AST Node Index (`Compiler.SolidityImport.AstIndex`)

Precomputes a flat hash-table index over a `solc --standard-json` AST tree so
that declaration lookups by AST node `id`, `referencedDeclaration` resolution,
and typed node queries (`StructDefinition`, `EnumDefinition`,
`UserDefinedValueTypeDefinition`, `FunctionDefinition`) run in $\mathcal{O}(1)$
lookup time instead of repeated $\mathcal{O}(|\text{AST}|)$ recursive scans.

All traversals are structurally bounded by an explicit `fuel : Nat` parameter
without `partial def`.
-/

namespace Compiler.CompilationModel.SolidityImport

open Lean

/-- Extract an optional object field from a `Lean.Json` value. -/
def jsonField? (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

/-- Extract an optional string field from a `Lean.Json` object. -/
def jsonStrField? (j : Json) (key : String) : Option String :=
  match jsonField? j key with
  | some v => v.getStr?.toOption
  | none => none

/-- Extract an optional natural-number field (stored as JSON number or decimal string). -/
def jsonNatField? (j : Json) (key : String) : Option Nat :=
  match jsonField? j key with
  | some v =>
      match v.getNat? with
      | .ok n => some n
      | .error _ =>
          match v.getStr? with
          | .ok s => s.toNat?
          | .error _ => none
  | none => none

/-- Extract an optional signed integer field from a `Lean.Json` object. -/
def jsonIntField? (j : Json) (key : String) : Option Int :=
  match jsonField? j key with
  | some v => v.getInt?.toOption
  | none => none

/-- Extract `"nodeType"` from a solc AST JSON object. -/
def astNodeType? (j : Json) : Option String :=
  jsonStrField? j "nodeType"

/-- Extract `"name"` from a solc AST JSON object. -/
def astNodeName? (j : Json) : Option String :=
  jsonStrField? j "name"

/-- Extract `"id"` from a solc AST JSON object. -/
def astNodeId? (j : Json) : Option Nat :=
  jsonNatField? j "id"

/-- Precomputed $\mathcal{O}(1)$ lookup index over a `solc --standard-json` AST.
    Maps AST node IDs (`id : Nat`) to their `Lean.Json` objects and maintains
    secondary indices by `nodeType : String` and `name : String`. -/
structure AstNodeIndex where
  /-- Primary $\mathcal{O}(1)$ map from solc AST node `id` to its `Lean.Json` node. -/
  byId : Std.HashMap Nat Json := {}
  /-- Secondary index mapping `nodeType` strings to arrays of matching node IDs. -/
  byNodeType : Std.HashMap String (Array Nat) := {}
  /-- Secondary index mapping declaration `name` strings to arrays of matching node IDs. -/
  byName : Std.HashMap String (Array Nat) := {}
  deriving Inhabited

/-- The empty `AstNodeIndex`. -/
def AstNodeIndex.empty : AstNodeIndex := {}

/-- Number of indexed AST nodes in `byId`. -/
def AstNodeIndex.size (idx : AstNodeIndex) : Nat :=
  idx.byId.size

/-- Insert an AST node with identifier `id` into `idx`, updating the primary
    `byId` table and the secondary `byNodeType` and `byName` tables. -/
def AstNodeIndex.insert (idx : AstNodeIndex) (id : Nat) (node : Json) : AstNodeIndex :=
  let byId' := idx.byId.insert id node
  let byNodeType' :=
    match astNodeType? node with
    | some nt =>
        let prev := idx.byNodeType[nt]?.getD #[]
        idx.byNodeType.insert nt (prev.push id)
    | none => idx.byNodeType
  let byName' :=
    match astNodeName? node with
    | some nm =>
        let prev := idx.byName[nm]?.getD #[]
        idx.byName.insert nm (prev.push id)
    | none => idx.byName
  { byId := byId', byNodeType := byNodeType', byName := byName' }

/-- Single-pass structural traversal over `j` bounded by `fuel`, indexing every
    JSON object that carries both `"nodeType"` and `"id"`. -/
def AstNodeIndex.indexJson : Nat → AstNodeIndex → Json → AstNodeIndex
  | 0, idx, _ => idx
  | fuel + 1, idx, j =>
      match j with
      | .obj kvs =>
          let idx1 :=
            match astNodeType? j, astNodeId? j with
            | some _, some id => idx.insert id j
            | _, _ => idx
          kvs.foldl (init := idx1) fun acc _ child =>
            AstNodeIndex.indexJson fuel acc child
      | .arr elems =>
          elems.foldl (init := idx) fun acc child =>
            AstNodeIndex.indexJson fuel acc child
      | _ => idx

/-- Construct an `AstNodeIndex` in a single $\mathcal{O}(|\text{AST}|)$ pass over
    `root` with structural recursion depth bounded by `fuel` (default `32`). -/
def AstNodeIndex.ofRootJson (root : Json) (fuel : Nat := 32) : AstNodeIndex :=
  AstNodeIndex.indexJson fuel AstNodeIndex.empty root

/-- $\mathcal{O}(1)$ lookup of an AST node by its solc node `id`. -/
def AstNodeIndex.findById? (idx : AstNodeIndex) (id : Nat) : Option Json :=
  idx.byId[id]?

/-- $\mathcal{O}(1)$ lookup of all node IDs registered under `nodeType`. -/
def AstNodeIndex.idsOfNodeType (idx : AstNodeIndex) (nodeType : String) : Array Nat :=
  idx.byNodeType[nodeType]?.getD #[]

/-- $\mathcal{O}(1)$ lookup of all node IDs registered under `name`. -/
def AstNodeIndex.idsOfName (idx : AstNodeIndex) (name : String) : Array Nat :=
  idx.byName[name]?.getD #[]

/-- Resolve the AST declaration referenced by `node`'s `"referencedDeclaration"`
    attribute in $\mathcal{O}(1)$ time. Negative IDs (solc magic builtins) yield `none`. -/
def AstNodeIndex.resolveReferencedDeclaration? (idx : AstNodeIndex) (node : Json) : Option Json :=
  match jsonIntField? node "referencedDeclaration" with
  | some i => if i ≥ 0 then idx.findById? i.toNat else none
  | none => none

/-- Look up AST node `id` and require its `"nodeType"` to match `expectedType`. -/
def AstNodeIndex.findByIdWithNodeType? (idx : AstNodeIndex) (expectedType : String) (id : Nat) :
    Option Json :=
  match idx.findById? id with
  | some node => if astNodeType? node == some expectedType then some node else none
  | none => none

/-- $\mathcal{O}(1)$ lookup of a `"StructDefinition"` AST node by `id`. -/
def AstNodeIndex.findStructDef? (idx : AstNodeIndex) (id : Nat) : Option Json :=
  idx.findByIdWithNodeType? "StructDefinition" id

/-- $\mathcal{O}(1)$ lookup of an `"EnumDefinition"` AST node by `id`. -/
def AstNodeIndex.findEnumDef? (idx : AstNodeIndex) (id : Nat) : Option Json :=
  idx.findByIdWithNodeType? "EnumDefinition" id

/-- $\mathcal{O}(1)$ lookup of a `"UserDefinedValueTypeDefinition"` AST node by `id`. -/
def AstNodeIndex.findUdvtDef? (idx : AstNodeIndex) (id : Nat) : Option Json :=
  idx.findByIdWithNodeType? "UserDefinedValueTypeDefinition" id

/-- $\mathcal{O}(1)$ lookup of a `"FunctionDefinition"` AST node by `id`. -/
def AstNodeIndex.findFunctionDef? (idx : AstNodeIndex) (id : Nat) : Option Json :=
  idx.findByIdWithNodeType? "FunctionDefinition" id

/-! ## Formal Invariants -/

/-- Looking up any node ID in `AstNodeIndex.empty` returns `none`. -/
@[simp]
theorem AstNodeIndex.empty_findById? (id : Nat) :
    AstNodeIndex.empty.findById? id = none := by
  simp [AstNodeIndex.empty, AstNodeIndex.findById?]

/-- Inserting `(id, node)` and immediately looking up `id` returns `some node`. -/
@[simp]
theorem AstNodeIndex.insert_findById?_self (idx : AstNodeIndex) (id : Nat) (node : Json) :
    (idx.insert id node).findById? id = some node := by
  simp [AstNodeIndex.insert, AstNodeIndex.findById?]

/-- Inserting `(id, node)` preserves `findById?` at any distinct `id' ≠ id`. -/
theorem AstNodeIndex.insert_findById?_of_ne (idx : AstNodeIndex) {id id' : Nat} (node : Json)
    (h : id ≠ id') :
    (idx.insert id node).findById? id' = idx.findById? id' := by
  simp [AstNodeIndex.insert, AstNodeIndex.findById?, Std.HashMap.getElem?_insert, h]

/-- `indexJson` with zero fuel returns the accumulator unchanged. -/
@[simp]
theorem AstNodeIndex.indexJson_zero (idx : AstNodeIndex) (root : Json) :
    AstNodeIndex.indexJson 0 idx root = idx := rfl

/-- `ofRootJson` with zero fuel produces `AstNodeIndex.empty`. -/
@[simp]
theorem AstNodeIndex.ofRootJson_fuel_zero (root : Json) :
    AstNodeIndex.ofRootJson root 0 = AstNodeIndex.empty := rfl

/-- Looking up any `id` in `ofRootJson root 0` returns `none`. -/
@[simp]
theorem AstNodeIndex.findById?_ofRootJson_fuel_zero (root : Json) (id : Nat) :
    (AstNodeIndex.ofRootJson root 0).findById? id = none := by
  simp [AstNodeIndex.ofRootJson]

/-- `findByIdWithNodeType?` succeeds iff `findById?` returns `some node` with matching `nodeType`. -/
theorem AstNodeIndex.findByIdWithNodeType?_eq_some_iff
    (idx : AstNodeIndex) (expectedType : String) (id : Nat) (node : Json) :
    idx.findByIdWithNodeType? expectedType id = some node ↔
      idx.findById? id = some node ∧ astNodeType? node = some expectedType := by
  unfold AstNodeIndex.findByIdWithNodeType?
  cases h : idx.findById? id with
  | none =>
      simp
  | some found =>
      by_cases hnt : astNodeType? found == some expectedType
      · have hntEq : astNodeType? found = some expectedType := eq_of_beq hnt
        simp [hntEq]
        intro hEq
        subst hEq
        exact hntEq
      · simp [hnt]
        intro hEq
        subst hEq
        intro contra
        exact hnt (beq_iff_eq.mpr contra)

/-- `findStructDef?` succeeds iff `findById?` returns a `"StructDefinition"` node. -/
theorem AstNodeIndex.findStructDef?_eq_some_iff
    (idx : AstNodeIndex) (id : Nat) (node : Json) :
    idx.findStructDef? id = some node ↔
      idx.findById? id = some node ∧ astNodeType? node = some "StructDefinition" :=
  idx.findByIdWithNodeType?_eq_some_iff "StructDefinition" id node

/-- `findEnumDef?` succeeds iff `findById?` returns an `"EnumDefinition"` node. -/
theorem AstNodeIndex.findEnumDef?_eq_some_iff
    (idx : AstNodeIndex) (id : Nat) (node : Json) :
    idx.findEnumDef? id = some node ↔
      idx.findById? id = some node ∧ astNodeType? node = some "EnumDefinition" :=
  idx.findByIdWithNodeType?_eq_some_iff "EnumDefinition" id node

/-- `findUdvtDef?` succeeds iff `findById?` returns a `"UserDefinedValueTypeDefinition"` node. -/
theorem AstNodeIndex.findUdvtDef?_eq_some_iff
    (idx : AstNodeIndex) (id : Nat) (node : Json) :
    idx.findUdvtDef? id = some node ↔
      idx.findById? id = some node ∧ astNodeType? node = some "UserDefinedValueTypeDefinition" :=
  idx.findByIdWithNodeType?_eq_some_iff "UserDefinedValueTypeDefinition" id node

/-- `findFunctionDef?` succeeds iff `findById?` returns a `"FunctionDefinition"` node. -/
theorem AstNodeIndex.findFunctionDef?_eq_some_iff
    (idx : AstNodeIndex) (id : Nat) (node : Json) :
    idx.findFunctionDef? id = some node ↔
      idx.findById? id = some node ∧ astNodeType? node = some "FunctionDefinition" :=
  idx.findByIdWithNodeType?_eq_some_iff "FunctionDefinition" id node

/-- A single AST node ID cannot simultaneously resolve as both a `StructDefinition`
    and an `EnumDefinition`. -/
theorem AstNodeIndex.findStructDef?_disjoint_findEnumDef?
    (idx : AstNodeIndex) (id : Nat) (sNode eNode : Json)
    (hs : idx.findStructDef? id = some sNode) :
    idx.findEnumDef? id ≠ some eNode := by
  intro he
  have ⟨hsId, hsNt⟩ := (idx.findStructDef?_eq_some_iff id sNode).mp hs
  have ⟨heId, heNt⟩ := (idx.findEnumDef?_eq_some_iff id eNode).mp he
  rw [hsId] at heId
  injection heId with hEq
  subst hEq
  rw [hsNt] at heNt
  nomatch heNt

/-- Typed lookups on `AstNodeIndex.empty` always return `none`. -/
@[simp]
theorem AstNodeIndex.empty_findStructDef? (id : Nat) :
    AstNodeIndex.empty.findStructDef? id = none := by
  simp [AstNodeIndex.findStructDef?, AstNodeIndex.findByIdWithNodeType?]

/-- Total lookup determinism: equal indices and node IDs produce identical lookup results. -/
theorem AstNodeIndex.findById?_deterministic
    (idx₁ idx₂ : AstNodeIndex) (id₁ id₂ : Nat)
    (hIdx : idx₁ = idx₂) (hId : id₁ = id₂) :
    idx₁.findById? id₁ = idx₂.findById? id₂ := by
  subst hIdx; subst hId; rfl

/-- Total reference-resolution determinism: equal indices and AST nodes produce
    identical `resolveReferencedDeclaration?` results. -/
theorem AstNodeIndex.resolveReferencedDeclaration?_deterministic
    (idx₁ idx₂ : AstNodeIndex) (n₁ n₂ : Json)
    (hIdx : idx₁ = idx₂) (hNode : n₁ = n₂) :
    idx₁.resolveReferencedDeclaration? n₁ = idx₂.resolveReferencedDeclaration? n₂ := by
  subst hIdx; subst hNode; rfl

end Compiler.CompilationModel.SolidityImport
