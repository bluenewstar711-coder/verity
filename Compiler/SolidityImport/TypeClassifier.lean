import Compiler.CompilationModel.Types
import Compiler.SolidityImport.SolidityAbi

set_option autoImplicit false

/-!
# Solidity Type String & `typeIdentifier` Classification Algebra (`Compiler.SolidityImport.TypeClassifier`)

Formalizes a total, deciduous classification algebra over Solidity `typeString`
and `typeIdentifier` descriptors emitted by `solc --standard-json`:

* `SolidityScalarKind`: elementary value types (`uint<N>`, `int<N>`, `address`,
  `bool`, `bytes<M>`, `enum`, `udvt`).
* `SolidityRefLocation`: data location qualifiers (`memory`, `calldata`,
  `storageRef`, `storagePointer`, `transient`, `unspecified`).
* `SolidityTypeDescriptor`: algebraic classification of value types, dynamic
  byte arrays (`bytes` / `string`), dynamic and fixed arrays, struct references,
  storage mappings, and function pointers.
* `classifyTypeIdentifier : String → SolidityTypeDescriptor`: total classifier
  handling both human-readable `typeString` and internal `t_*` `typeIdentifier`
  spellings.
* `storageWordCount`, `isValueType`, `isDynamicAbiType`: layout and ABI
  predicates with machine-checked algebraic invariants.
-/

namespace Compiler.CompilationModel.SolidityImport

open Compiler.CompilationModel

/-- Classification of Solidity elementary value / scalar types. -/
inductive SolidityScalarKind where
  /-- Unsigned integer `uint<bits>` (default `uint` = `uint256`). -/
  | uint (bits : Nat)
  /-- Two's-complement signed integer `int<bits>` (default `int` = `int256`). -/
  | int (bits : Nat)
  /-- 20-byte Ethereum address (`address`, `address payable`, or `contract ...`). -/
  | address (payable : Bool := false)
  /-- Boolean (`bool`). -/
  | bool
  /-- Fixed-width byte array `bytes<width>` for `1 ≤ width ≤ 32`. -/
  | fixedBytes (width : Nat)
  /-- Solidity `enum` type (up to 256 members, 8-bit representation). -/
  | enumType (name : String)
  /-- User-defined value type wrapping an underlying scalar kind. -/
  | udvt (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- Data location qualifier for Solidity reference types. -/
inductive SolidityRefLocation where
  | memory
  | calldata
  | storageRef
  | storagePointer
  | transient
  | unspecified
  deriving Repr, DecidableEq, Inhabited

/-- Algebraic descriptor for a parsed Solidity `typeString` or `typeIdentifier`. -/
inductive SolidityTypeDescriptor where
  /-- Elementary value / scalar type occupying one EVM word in the ABI head. -/
  | value (scalar : SolidityScalarKind)
  /-- Dynamically sized byte buffer (`bytes` or `string`) at a reference location. -/
  | dynamicBytes (isString : Bool) (loc : SolidityRefLocation)
  /-- Dynamically sized array `elem[]` at a reference location. -/
  | dynamicArray (elem : String) (loc : SolidityRefLocation)
  /-- Statically sized array `elem[length]` at a reference location. -/
  | fixedArray (elem : String) (length : Nat) (loc : SolidityRefLocation)
  /-- Struct reference (`struct Name` or `t_struct(Name)`) with root word count. -/
  | structRef (name : String) (loc : SolidityRefLocation) (words : Nat := 1)
  /-- Storage mapping (`mapping(K => V)` or `t_mapping(...)`). -/
  | mapping (keyType : String) (valueType : String)
  /-- Internal or external function pointer (`function (...)`). -/
  | functionPtr
  /-- Unrecognized or opaque Solidity type string. -/
  | unknown (raw : String)
  deriving Repr, DecidableEq, Inhabited

/-- Bit width of a `SolidityScalarKind` when statically fixed. -/
def SolidityScalarKind.bitWidth : SolidityScalarKind → Option Nat
  | .uint bits => if 8 ≤ bits && bits ≤ 256 && bits % 8 == 0 then some bits else none
  | .int bits => if 8 ≤ bits && bits ≤ 256 && bits % 8 == 0 then some bits else none
  | .address _ => some 160
  | .bool => some 8
  | .fixedBytes w => if 1 ≤ w && w ≤ 32 then some (8 * w) else none
  | .enumType _ => some 8
  | .udvt _ => none

/-- Lower a `SolidityScalarKind` to its `CompilationModel.ParamType` when supported. -/
def SolidityScalarKind.toParamType? : SolidityScalarKind → Option ParamType
  | .uint 256 => some .uint256
  | .uint 8 => some .uint8
  | .uint 16 => some .uint16
  | .uint bits =>
      if 8 ≤ bits && bits < 256 && bits % 8 == 0 then some (.uintN bits) else none
  | .int 256 => some .int256
  | .int bits =>
      if 8 ≤ bits && bits < 256 && bits % 8 == 0 then some (.intN bits) else none
  | .address _ => some .address
  | .bool => some .bool
  | .fixedBytes 32 => some .bytes32
  | .fixedBytes w => if 1 ≤ w && w < 32 then some (.bytesN w) else none
  | .enumType _ => some (.uintN 8)
  | .udvt _ => none

/-- True iff the descriptor represents an elementary Solidity value type. -/
def isValueType : SolidityTypeDescriptor → Bool
  | .value _ => true
  | _ => false

/-- True iff the descriptor uses a dynamic ABI encoding (head offset + tail payload). -/
def isDynamicAbiType : SolidityTypeDescriptor → Bool
  | .dynamicBytes _ _ => true
  | .dynamicArray _ _ => true
  | _ => false

/-- Number of 256-bit EVM storage slot words reserved at the root slot for a descriptor. -/
def storageWordCount : SolidityTypeDescriptor → Nat
  | .value _ => 1
  | .dynamicBytes _ _ => 1
  | .dynamicArray _ _ => 1
  | .fixedArray _ len _ => max 1 len
  | .structRef _ _ words => max 1 words
  | .mapping _ _ => 1
  | .functionPtr => 1
  | .unknown _ => 0

/-- Extract a trailing data-location suffix from a `typeString` or `typeIdentifier`. -/
def stripRefLocation (raw : String) : String × SolidityRefLocation :=
  if raw.endsWith " storage pointer" then
    ((raw.dropEnd 16).toString, .storagePointer)
  else if raw.endsWith "_storage_ptr" then
    ((raw.dropEnd 12).toString, .storagePointer)
  else if raw.endsWith " storage ref" then
    ((raw.dropEnd 12).toString, .storageRef)
  else if raw.endsWith "_storage" then
    ((raw.dropEnd 8).toString, .storageRef)
  else if raw.endsWith " calldata" then
    ((raw.dropEnd 9).toString, .calldata)
  else if raw.endsWith "_calldata_ptr" then
    ((raw.dropEnd 13).toString, .calldata)
  else if raw.endsWith " memory" then
    ((raw.dropEnd 7).toString, .memory)
  else if raw.endsWith "_memory_ptr" then
    ((raw.dropEnd 11).toString, .memory)
  else if raw.endsWith " transient" then
    ((raw.dropEnd 10).toString, .transient)
  else
    (raw, .unspecified)

/-- Classify a stripped prefix (after fast-path exact matches) into `SolidityTypeDescriptor`. -/
private def classifyFallback (raw : String) : SolidityTypeDescriptor :=
  let (core, loc) := stripRefLocation raw
  if core.endsWith "[]" then
    .dynamicArray (core.dropEnd 2).toString loc
  else if core.startsWith "mapping(" || core.startsWith "t_mapping(" then
    .mapping core core
  else if core.startsWith "struct " then
    .structRef (core.drop 7).toString loc 1
  else if core.startsWith "t_struct(" then
    .structRef (core.drop 9).toString loc 1
  else if core.startsWith "enum " then
    .value (.enumType (core.drop 5).toString)
  else if core.startsWith "t_enum(" then
    .value (.enumType (core.drop 7).toString)
  else if core.startsWith "contract " || core.startsWith "t_contract(" then
    .value (.address false)
  else if core.startsWith "t_userDefinedValueType(" then
    .value (.udvt (core.drop 23).toString)
  else if core.startsWith "function " || core.startsWith "t_function_" then
    .functionPtr
  else
    let norm := if core.startsWith "t_" then (core.drop 2).toString else core
    if norm.startsWith "uint" then
      match (norm.drop 4).toNat? with
      | some bits =>
          if 8 ≤ bits && bits ≤ 256 && bits % 8 == 0 then .value (.uint bits)
          else .unknown raw
      | none => .unknown raw
    else if norm.startsWith "int" && !norm.startsWith "int_const" then
      match (norm.drop 3).toNat? with
      | some bits =>
          if 8 ≤ bits && bits ≤ 256 && bits % 8 == 0 then .value (.int bits)
          else .unknown raw
      | none => .unknown raw
    else if norm.startsWith "bytes" then
      match (norm.drop 5).toNat? with
      | some w =>
          if 1 ≤ w && w ≤ 32 then .value (.fixedBytes w)
          else .unknown raw
      | none => .unknown raw
    else
      .unknown raw

/-- Classify a Solidity `typeString` or `typeIdentifier` into a `SolidityTypeDescriptor`.
    Common canonical scalar and byte/string types reduce definitionally in $\mathcal{O}(1)$. -/
def classifyTypeIdentifier (raw : String) : SolidityTypeDescriptor :=
  match raw with
  | "uint256" | "uint" | "t_uint256" => .value (.uint 256)
  | "uint128" | "t_uint128" => .value (.uint 128)
  | "uint96" | "t_uint96" => .value (.uint 96)
  | "uint64" | "t_uint64" => .value (.uint 64)
  | "uint48" | "t_uint48" => .value (.uint 48)
  | "uint32" | "t_uint32" => .value (.uint 32)
  | "uint16" | "t_uint16" => .value (.uint 16)
  | "uint8" | "t_uint8" => .value (.uint 8)
  | "int256" | "int" | "t_int256" => .value (.int 256)
  | "int128" | "t_int128" => .value (.int 128)
  | "int64" | "t_int64" => .value (.int 64)
  | "int32" | "t_int32" => .value (.int 32)
  | "int16" | "t_int16" => .value (.int 16)
  | "int8" | "t_int8" => .value (.int 8)
  | "address" | "t_address" => .value (.address false)
  | "address payable" | "t_address_payable" => .value (.address true)
  | "bool" | "t_bool" => .value .bool
  | "bytes32" | "t_bytes32" => .value (.fixedBytes 32)
  | "bytes20" | "t_bytes20" => .value (.fixedBytes 20)
  | "bytes16" | "t_bytes16" => .value (.fixedBytes 16)
  | "bytes8" | "t_bytes8" => .value (.fixedBytes 8)
  | "bytes4" | "t_bytes4" => .value (.fixedBytes 4)
  | "bytes1" | "t_bytes1" => .value (.fixedBytes 1)
  | "bytes" => .dynamicBytes false .unspecified
  | "bytes memory" | "t_bytes_memory_ptr" => .dynamicBytes false .memory
  | "bytes calldata" | "t_bytes_calldata_ptr" => .dynamicBytes false .calldata
  | "bytes storage ref" | "t_bytes_storage" => .dynamicBytes false .storageRef
  | "bytes storage pointer" | "t_bytes_storage_ptr" => .dynamicBytes false .storagePointer
  | "string" => .dynamicBytes true .unspecified
  | "string memory" | "t_string_memory_ptr" => .dynamicBytes true .memory
  | "string calldata" | "t_string_calldata_ptr" => .dynamicBytes true .calldata
  | "string storage ref" | "t_string_storage" => .dynamicBytes true .storageRef
  | "string storage pointer" | "t_string_storage_ptr" => .dynamicBytes true .storagePointer
  | _ => classifyFallback raw

/-- Lower a `SolidityTypeDescriptor` to a `CompilationModel.ParamType` when directly representable. -/
def SolidityTypeDescriptor.toParamType? : SolidityTypeDescriptor → Option ParamType
  | .value scalar => scalar.toParamType?
  | .dynamicBytes false _ => some .bytes
  | .dynamicBytes true _ => some .string
  | .dynamicArray elem _ =>
      match classifyTypeIdentifier elem with
      | .value scalar => scalar.toParamType?.map .array
      | _ => none
  | .fixedArray elem len _ =>
      match classifyTypeIdentifier elem with
      | .value scalar => scalar.toParamType?.map (fun p => .fixedArray p len)
      | _ => none
  | _ => none

/-! ## Formal Algebraic Lemmas -/

/-- Every value type is statically encoded in the ABI head (never a dynamic ABI type). -/
theorem isValueType_implies_not_dynamic (d : SolidityTypeDescriptor)
    (h : isValueType d = true) :
    isDynamicAbiType d = false := by
  cases d <;> simp [isValueType, isDynamicAbiType] at h ⊢

/-- Conversely, every dynamic ABI type is not a value type. -/
theorem isDynamicAbiType_implies_not_valueType (d : SolidityTypeDescriptor)
    (h : isDynamicAbiType d = true) :
    isValueType d = false := by
  cases d <;> simp [isValueType, isDynamicAbiType] at h ⊢

/-- Every value type occupies a positive number of storage words (`storageWordCount d = 1 > 0`). -/
theorem storageWordCount_pos_of_valueType (d : SolidityTypeDescriptor)
    (h : isValueType d = true) :
    0 < storageWordCount d := by
  cases d <;> simp [isValueType, storageWordCount] at h ⊢

/-- Every value type occupies exactly `1` storage word at its root slot. -/
@[simp]
theorem storageWordCount_value (s : SolidityScalarKind) :
    storageWordCount (.value s) = 1 := rfl

/-- Fixed arrays occupy at least `1` storage word (`0 < storageWordCount (.fixedArray e n loc)`). -/
theorem storageWordCount_fixedArray_pos (elem : String) (len : Nat) (loc : SolidityRefLocation) :
    0 < storageWordCount (.fixedArray elem len loc) := by
  simp only [storageWordCount]
  omega

/-- Struct references occupy at least `1` storage word (`0 < storageWordCount (.structRef n loc w)`). -/
theorem storageWordCount_structRef_pos (name : String) (loc : SolidityRefLocation) (words : Nat) :
    0 < storageWordCount (.structRef name loc words) := by
  simp only [storageWordCount]
  omega

/-- Classification of `"uint256"`. -/
@[simp]
theorem classifyTypeIdentifier_uint256 :
    classifyTypeIdentifier "uint256" = .value (.uint 256) := rfl

/-- Classification of `"t_uint256"`. -/
@[simp]
theorem classifyTypeIdentifier_t_uint256 :
    classifyTypeIdentifier "t_uint256" = .value (.uint 256) := rfl

/-- Classification of `"address"`. -/
@[simp]
theorem classifyTypeIdentifier_address :
    classifyTypeIdentifier "address" = .value (.address false) := rfl

/-- Classification of `"t_address"`. -/
@[simp]
theorem classifyTypeIdentifier_t_address :
    classifyTypeIdentifier "t_address" = .value (.address false) := rfl

/-- Classification of `"bytes32"`. -/
@[simp]
theorem classifyTypeIdentifier_bytes32 :
    classifyTypeIdentifier "bytes32" = .value (.fixedBytes 32) := rfl

/-- Classification of `"t_bytes32"`. -/
@[simp]
theorem classifyTypeIdentifier_t_bytes32 :
    classifyTypeIdentifier "t_bytes32" = .value (.fixedBytes 32) := rfl

/-- Classification of `"bool"`. -/
@[simp]
theorem classifyTypeIdentifier_bool :
    classifyTypeIdentifier "bool" = .value .bool := rfl

/-- Classification of `"int256"`. -/
@[simp]
theorem classifyTypeIdentifier_int256 :
    classifyTypeIdentifier "int256" = .value (.int 256) := rfl

/-- Classification of `"bytes memory"`. -/
@[simp]
theorem classifyTypeIdentifier_bytes_memory :
    classifyTypeIdentifier "bytes memory" = .dynamicBytes false .memory := rfl

/-- Classification of `"string calldata"`. -/
@[simp]
theorem classifyTypeIdentifier_string_calldata :
    classifyTypeIdentifier "string calldata" = .dynamicBytes true .calldata := rfl

/-- `"uint256"` classifies as a value type. -/
@[simp]
theorem isValueType_classifyTypeIdentifier_uint256 :
    isValueType (classifyTypeIdentifier "uint256") = true := rfl

/-- `"address"` classifies as a value type. -/
@[simp]
theorem isValueType_classifyTypeIdentifier_address :
    isValueType (classifyTypeIdentifier "address") = true := rfl

/-- `"bytes32"` classifies as a value type. -/
@[simp]
theorem isValueType_classifyTypeIdentifier_bytes32 :
    isValueType (classifyTypeIdentifier "bytes32") = true := rfl

/-- `"bytes memory"` classifies as a dynamic ABI type. -/
@[simp]
theorem isDynamicAbiType_classifyTypeIdentifier_bytes_memory :
    isDynamicAbiType (classifyTypeIdentifier "bytes memory") = true := rfl

/-- Parameter lowering of classified `"uint256"`. -/
@[simp]
theorem toParamType?_classifyTypeIdentifier_uint256 :
    (classifyTypeIdentifier "uint256").toParamType? = some .uint256 := rfl

/-- Parameter lowering of classified `"address"`. -/
@[simp]
theorem toParamType?_classifyTypeIdentifier_address :
    (classifyTypeIdentifier "address").toParamType? = some .address := rfl

/-- Parameter lowering of classified `"bytes32"`. -/
@[simp]
theorem toParamType?_classifyTypeIdentifier_bytes32 :
    (classifyTypeIdentifier "bytes32").toParamType? = some .bytes32 := rfl

end Compiler.CompilationModel.SolidityImport
