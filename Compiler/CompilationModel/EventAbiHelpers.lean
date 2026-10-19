import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def indexedDynamicArrayElemSupported (elemTy : ParamType) : Bool :=
  !eventIsDynamicType elemTy &&
    eventHeadWordSize elemTy > 0

def normalizeEventWord (ty : ParamType) (expr : YulExpr) : YulExpr :=
  match ty with
  | ParamType.uint8 => YulExpr.call "and" [expr, YulExpr.lit 255]
  | ParamType.uint16 => YulExpr.call "and" [expr, YulExpr.lit 65535]
  | ParamType.uintN bits =>
      YulExpr.call "and" [expr, YulExpr.lit (2 ^ bits - 1)]
  | ParamType.intN bits =>
      YulExpr.call "signextend" [YulExpr.lit (bits / 8 - 1), expr]
  | ParamType.bytesN bytes =>
      YulExpr.call "and" [expr,
        YulExpr.lit ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))]
  | ParamType.address => YulExpr.call "and" [expr, YulExpr.hex addressMask]
  | ParamType.bool => yulToBool expr
  | ParamType.newtypeOf _ baseType => normalizeEventWord baseType expr
  | _ => expr

mutual
  def staticCompositeLeaves (baseName : String) (ty : ParamType) :
      List (ParamType × YulExpr) :=
    match ty with
    | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _
    | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        [(ty, YulExpr.ident baseName)]
    | ParamType.fixedArray elemTy n =>
        (List.range n).flatMap fun i =>
          staticCompositeLeaves s!"{baseName}_{i}" elemTy
    | ParamType.tuple elemTys =>
        staticCompositeLeavesTuple baseName elemTys 0
    | _ => []
  termination_by sizeOf ty
  decreasing_by all_goals simp_wf; all_goals omega

  def staticCompositeLeavesTuple (baseName : String) (tys : List ParamType) (idx : Nat) :
      List (ParamType × YulExpr) :=
    match tys with
    | [] => []
    | elemTy :: rest =>
        staticCompositeLeaves s!"{baseName}_{idx}" elemTy ++
          staticCompositeLeavesTuple baseName rest (idx + 1)
  termination_by sizeOf tys
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  def staticCompositeLeafTypeOffsets
      (baseOffset : Nat) (ty : ParamType) : List (Nat × ParamType) :=
    match ty with
    | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _
    | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        [(baseOffset, ty)]
    | ParamType.fixedArray elemTy n =>
        (List.range n).flatMap fun i =>
          staticCompositeLeafTypeOffsets (baseOffset + i * eventHeadWordSize elemTy) elemTy
    | ParamType.tuple elemTys =>
        staticCompositeLeafTypeOffsetsTuple elemTys baseOffset
    | _ => []
  termination_by sizeOf ty
  decreasing_by all_goals simp_wf; all_goals omega

  def staticCompositeLeafTypeOffsetsTuple
      (remaining : List ParamType) (curOffset : Nat) : List (Nat × ParamType) :=
    match remaining with
    | [] => []
    | elemTy :: rest =>
        staticCompositeLeafTypeOffsets curOffset elemTy ++
          staticCompositeLeafTypeOffsetsTuple rest (curOffset + eventHeadWordSize elemTy)
  termination_by sizeOf remaining
  decreasing_by all_goals simp_wf; all_goals omega
end

def indexedDynamicBaseOffsetExpr (dynamicSource : DynamicDataSource) (paramName : String) : YulExpr :=
  match dynamicSource with
  | .calldata => YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{paramName}_offset"]
  | .memory => YulExpr.ident s!"{paramName}_offset"

mutual
  def compileIndexedInPlaceEncoding
      (dynamicSource : DynamicDataSource) (ty : ParamType)
      (srcBase dstBase : YulExpr) (stem : String) :
      Except String (List YulStmt × YulExpr) := do
    match ty with
    | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _
    | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        let loaded := dynamicWordLoad dynamicSource srcBase
        pure ([
          YulStmt.exprStmt (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
        ], YulExpr.lit 32)
    | ParamType.bytes | ParamType.string =>
        let lenName := s!"{stem}_len"
        let paddedName := s!"{stem}_padded"
        pure ([
          YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
        ] ++ dynamicCopyData dynamicSource
          dstBase
          (YulExpr.call "add" [srcBase, YulExpr.lit 32])
          (YulExpr.ident lenName) ++ [
          YulStmt.let_ paddedName (YulExpr.call "and" [
            YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
            YulExpr.call "not" [YulExpr.lit 31]
          ]),
          YulStmt.exprStmt (YulExpr.call "mstore" [
            YulExpr.call "add" [dstBase, YulExpr.ident lenName],
            YulExpr.lit 0
          ])
        ], YulExpr.ident paddedName)
    | ParamType.array elemTy =>
        let lenName := s!"{stem}_arr_len"
        let dataBaseName := s!"{stem}_arr_data"
        let loopIndexName := s!"{stem}_arr_i"
        let outLenName := s!"{stem}_arr_out_len"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let elemDstName := s!"{stem}_arr_elem_dst"
        let initStmts := [
          YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
          YulStmt.let_ dataBaseName (YulExpr.call "add" [srcBase, YulExpr.lit 32]),
          YulStmt.let_ outLenName (YulExpr.lit 0)
        ]
        let elemSrcExpr :=
          if eventIsDynamicType elemTy then
            let relName := s!"{stem}_arr_elem_rel"
            let relDecl := YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              YulExpr.ident dataBaseName,
              YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
            ]))
            let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
              YulExpr.ident dataBaseName,
              YulExpr.ident relName
            ])
            ([relDecl, srcDecl], YulExpr.ident elemSrcName)
          else
            let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
              YulExpr.ident dataBaseName,
              YulExpr.call "mul"
                [YulExpr.ident loopIndexName, YulExpr.lit (eventHeadWordSize elemTy)]
            ])
            ([srcDecl], YulExpr.ident elemSrcName)
        let (elemEncodeStmts, elemEncodedLen) ←
          compileIndexedInPlaceEncoding dynamicSource elemTy (elemSrcExpr.2)
            (YulExpr.ident elemDstName) s!"{stem}_arr_elem"
        let loopBody :=
          elemSrcExpr.1 ++ [
            YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
          ] ++ elemEncodeStmts ++ [
            YulStmt.assign outLenName
              (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
          ]
        pure (initStmts ++ [
          YulStmt.for_
            [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
            (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
            [YulStmt.assign loopIndexName
              (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
            loopBody
        ], YulExpr.ident outLenName)
    | ParamType.fixedArray elemTy n =>
        let outLenName := s!"{stem}_fixed_out_len"
        let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
        let fixedStmts ←
          compileIndexedInPlaceEncodingFixed dynamicSource elemTy n srcBase dstBase stem
            outLenName 0
        pure (initStmts ++ fixedStmts, YulExpr.ident outLenName)
    | ParamType.tuple elemTys =>
        let outLenName := s!"{stem}_tuple_out_len"
        let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
        let tupleStmts ←
          compileIndexedInPlaceEncodingTuple dynamicSource elemTys srcBase dstBase stem
            outLenName 0 0
        pure (initStmts ++ tupleStmts, YulExpr.ident outLenName)
    | ParamType.adt _ maxFields =>
        -- ADTs: ABI-encode as (uint8 tag, uint256 field0, ..., uint256 fieldN)
        let tagLoaded := dynamicWordLoad dynamicSource srcBase
        let tagStore := YulStmt.exprStmt (YulExpr.call "mstore" [
          dstBase, YulExpr.call "and" [tagLoaded, YulExpr.lit 0xFF]
        ])
        let fieldStores := (List.range maxFields).map fun i =>
          let srcOff := YulExpr.call "add" [srcBase, YulExpr.lit ((i + 1) * 32)]
          let dstOff := YulExpr.call "add" [dstBase, YulExpr.lit ((i + 1) * 32)]
          YulStmt.exprStmt (YulExpr.call "mstore" [dstOff, dynamicWordLoad dynamicSource srcOff])
        let totalBytes := 32 * (1 + maxFields)
        pure (tagStore :: fieldStores, YulExpr.lit totalBytes)
    | ParamType.newtypeOf _ baseType =>
        -- Newtypes erased to base type (#1727 Step 3b)
        compileIndexedInPlaceEncoding dynamicSource baseType srcBase dstBase stem
  termination_by (2 * sizeOf ty + 1, 0)
  decreasing_by all_goals simp_wf; all_goals omega

  def compileIndexedInPlaceEncodingFixed
      (dynamicSource : DynamicDataSource) (elemTy : ParamType) (n : Nat)
      (srcBase dstBase : YulExpr) (stem outLenName : String) (i : Nat) :
      Except String (List YulStmt) := do
    if _h : i < n then
      let elemSrcName := s!"{stem}_fixed_elem_src_{i}"
      let elemDstName := s!"{stem}_fixed_elem_dst_{i}"
      let srcStmts :=
        if eventIsDynamicType elemTy then
          let relName := s!"{stem}_fixed_elem_rel_{i}"
          [
            YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              srcBase, YulExpr.lit (i * 32)
            ])),
            YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
          ]
        else
          [YulStmt.let_ elemSrcName (YulExpr.call "add" [
            srcBase, YulExpr.lit (i * eventHeadWordSize elemTy)
          ])]
      let elemDstStmt :=
        YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
      let (elemEncodeStmts, elemEncodedLen) ←
        compileIndexedInPlaceEncoding dynamicSource elemTy
          (YulExpr.ident elemSrcName)
          (YulExpr.ident elemDstName)
          s!"{stem}_fixed_elem_{i}"
      let rest ←
        compileIndexedInPlaceEncodingFixed dynamicSource elemTy n srcBase dstBase stem
          outLenName (i + 1)
      pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
        YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
      ] ++ rest)
    else
      pure []
  termination_by (2 * sizeOf elemTy + 1, n - i)
  decreasing_by all_goals simp_wf; all_goals omega

  def compileIndexedInPlaceEncodingTuple
      (dynamicSource : DynamicDataSource) (remaining : List ParamType)
      (srcBase dstBase : YulExpr) (stem outLenName : String) (elemIdx headOffset : Nat) :
      Except String (List YulStmt) := do
    match remaining with
    | [] => pure []
    | elemTy :: rest =>
        let elemSrcName := s!"{stem}_tuple_elem_src_{elemIdx}"
        let elemDstName := s!"{stem}_tuple_elem_dst_{elemIdx}"
        let srcStmts :=
          if eventIsDynamicType elemTy then
            let relName := s!"{stem}_tuple_elem_rel_{elemIdx}"
            [
              YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                srcBase, YulExpr.lit headOffset
              ])),
              YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
            ]
          else
            [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
        let elemDstStmt :=
          YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
        let (elemEncodeStmts, elemEncodedLen) ←
          compileIndexedInPlaceEncoding dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.ident elemDstName)
            s!"{stem}_tuple_elem_{elemIdx}"
        let restStmts ←
          compileIndexedInPlaceEncodingTuple dynamicSource rest srcBase dstBase stem outLenName
            (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
        pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
          YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
        ] ++ restStmts)
  termination_by (2 * sizeOf remaining, 0)
  decreasing_by all_goals simp_wf; all_goals omega
end

@[simp] theorem staticCompositeLeaves_uint256 (prefix_ : String) :
    staticCompositeLeaves prefix_ .uint256 = [(.uint256, YulExpr.ident prefix_)] := by
  unfold staticCompositeLeaves; rfl

@[simp] theorem staticCompositeLeaves_address (prefix_ : String) :
    staticCompositeLeaves prefix_ .address = [(.address, YulExpr.ident prefix_)] := by
  unfold staticCompositeLeaves; rfl

@[simp] theorem staticCompositeLeaves_bool (prefix_ : String) :
    staticCompositeLeaves prefix_ .bool = [(.bool, YulExpr.ident prefix_)] := by
  unfold staticCompositeLeaves; rfl

@[simp] theorem staticCompositeLeaves_bytes32 (prefix_ : String) :
    staticCompositeLeaves prefix_ .bytes32 = [(.bytes32, YulExpr.ident prefix_)] := by
  unfold staticCompositeLeaves; rfl

@[simp] theorem staticCompositeLeaves_tuple (prefix_ : String) (elemTys : List ParamType) :
    staticCompositeLeaves prefix_ (.tuple elemTys) =
      staticCompositeLeavesTuple prefix_ elemTys 0 := by
  unfold staticCompositeLeaves; rfl

@[simp] theorem staticCompositeLeaves_fixedArray (prefix_ : String) (elemTy : ParamType) (n : Nat) :
    staticCompositeLeaves prefix_ (.fixedArray elemTy n) =
      (List.range n).flatMap (fun idx => staticCompositeLeaves s!"{prefix_}_{idx}" elemTy) := by
  conv => lhs; unfold staticCompositeLeaves

@[simp] theorem compileIndexedInPlaceEncoding_uint256
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .uint256 srcBase dstBase stem =
      .ok ([YulStmt.exprStmt (YulExpr.call "mstore"
        [dstBase, normalizeEventWord .uint256 (dynamicWordLoad dynamicSource srcBase)])],
        YulExpr.lit 32) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_address
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .address srcBase dstBase stem =
      .ok ([YulStmt.exprStmt (YulExpr.call "mstore"
        [dstBase, normalizeEventWord .address (dynamicWordLoad dynamicSource srcBase)])],
        YulExpr.lit 32) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_bool
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .bool srcBase dstBase stem =
      .ok ([YulStmt.exprStmt (YulExpr.call "mstore"
        [dstBase, normalizeEventWord .bool (dynamicWordLoad dynamicSource srcBase)])],
        YulExpr.lit 32) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_bytes32
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .bytes32 srcBase dstBase stem =
      .ok ([YulStmt.exprStmt (YulExpr.call "mstore"
        [dstBase, normalizeEventWord .bytes32 (dynamicWordLoad dynamicSource srcBase)])],
        YulExpr.lit 32) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_bytes
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .bytes srcBase dstBase stem =
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      .ok ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      ] ++ dynamicCopyData dynamicSource dstBase
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [dstBase, YulExpr.ident lenName],
          YulExpr.lit 0
        ])
      ], YulExpr.ident paddedName) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_string
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource .string srcBase dstBase stem =
      compileIndexedInPlaceEncoding dynamicSource .bytes srcBase dstBase stem := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_fixedArray
    (dynamicSource : DynamicDataSource) (elemTy : ParamType) (n : Nat)
    (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource (.fixedArray elemTy n) srcBase dstBase stem = (do
      let outLenName := s!"{stem}_fixed_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let fixedStmts ←
        compileIndexedInPlaceEncodingFixed dynamicSource elemTy n srcBase dstBase stem outLenName 0
      pure (initStmts ++ fixedStmts, YulExpr.ident outLenName)) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_tuple
    (dynamicSource : DynamicDataSource) (elemTys : List ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource (.tuple elemTys) srcBase dstBase stem = (do
      let outLenName := s!"{stem}_tuple_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let tupleStmts ←
        compileIndexedInPlaceEncodingTuple dynamicSource elemTys srcBase dstBase stem outLenName 0 0
      pure (initStmts ++ tupleStmts, YulExpr.ident outLenName)) := by
  unfold compileIndexedInPlaceEncoding; rfl

@[simp] theorem compileIndexedInPlaceEncoding_newtypeOf
    (dynamicSource : DynamicDataSource) (name : String) (baseType : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    compileIndexedInPlaceEncoding dynamicSource (.newtypeOf name baseType) srcBase dstBase stem =
      compileIndexedInPlaceEncoding dynamicSource baseType srcBase dstBase stem := by
  conv => lhs; unfold compileIndexedInPlaceEncoding

@[simp] theorem compileIndexedInPlaceEncodingTuple_nil
    (dynamicSource : DynamicDataSource) (srcBase dstBase : YulExpr)
    (stem outLenName : String) (elemIdx headOffset : Nat) :
    compileIndexedInPlaceEncodingTuple dynamicSource [] srcBase dstBase
      stem outLenName elemIdx headOffset = .ok [] := by
  unfold compileIndexedInPlaceEncodingTuple; rfl

@[simp] theorem compileIndexedInPlaceEncodingFixed_ge
    (dynamicSource : DynamicDataSource) (elemTy : ParamType) (n : Nat)
    (srcBase dstBase : YulExpr) (stem outLenName : String) (i : Nat)
    (h : ¬ i < n) :
    compileIndexedInPlaceEncodingFixed dynamicSource elemTy n srcBase dstBase
      stem outLenName i = .ok [] := by
  unfold compileIndexedInPlaceEncodingFixed
  simp [h]; rfl

end Compiler.CompilationModel
