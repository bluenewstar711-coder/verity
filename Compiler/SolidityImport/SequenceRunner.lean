import Compiler.SolidityImport.TransactionAccess
import Compiler.Hex
import Compiler.Keccak.Sponge
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Lean.Data.Json

/-! JSON bridge for the Denote sequence adapter. Input arguments are complete
word-aligned source ABI payloads, decoded using the function binding policy.
Unsupported observations fail instead of supplying synthetic values. -/
namespace Compiler.CompilationModel.SolidityImport.SequenceRunner
open Lean Denote Transactions Verity.Core

private def word (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected decimal model word"
  unless n < 2^256 do throw "model word exceeds uint256"
  return n

private def getWord (j : Json) (key : String) : Except String Nat := do
  word (← j.getObjVal? key)

private def hexBytes (bytes : List UInt8) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte =>
    [Compiler.Hex.hexDigit (byte.toNat / 16), Compiler.Hex.hexDigit (byte.toNat % 16)])

private def hexWord (n : Nat) : String := hexBytes (wordBytes n)
private def hexAddress (n : Nat) : String := hexBytes ((wordBytes n).drop 12)

/-- Scalar ABI cleanup matching the compiler's event-word normalization. -/
private def eventWord (ty : ParamType) (value : Nat) : Except String Nat := do
  match ty with
  | .uint256 | .bytes32 => pure (value % 2^256)
  | .uint8 => pure (value % 2^8)
  | .uint16 => pure (value % 2^16)
  | .uintN bits =>
      unless 0 < bits && bits ≤ 256 && bits % 8 == 0 do throw "invalid event integer width"
      pure (value % 2^bits)
  | .address => pure (value % 2^160)
  | .bool => pure (if value == 0 then 0 else 1)
  | _ => throw "unsupported event observation parameter type"

/-- Exact scalar event encoding from actual Denote emissions and model declarations.
Denote's legacy eventless executor retains arguments in source order. -/
private def encodeEvent (account : Nat) (definitions : List EventDef)
    (event : Verity.Event) : Except String Json := do
  let [definition] := definitions.filter (·.name == event.name)
    | throw s!"observed event must resolve uniquely: {event.name}"
  unless event.indexedArgs.isEmpty do throw "unexpected pre-partitioned Denote event"
  unless definition.params.length == event.args.length do throw "event argument count differs"
  let pairs ← (definition.params.zip event.args).mapM fun (parameter, value) => do
    pure (parameter, ← eventWord parameter.ty value.val)
  let indexed := pairs.filter (fun p => p.1.kind == .indexed)
  unless indexed.length ≤ 3 do throw "event has more than three indexed parameters"
  let topic0 := hexBytes (KeccakEngine.keccak256_str (eventSignature definition)).data.toList
  let topics := topic0 :: indexed.map (fun p => hexWord p.2)
  let data := (pairs.filter (fun p => p.1.kind == .unindexed)).flatMap (fun p => wordBytes p.2)
  return Json.mkObj [("address", toJson (hexAddress account)),
    ("topics", toJson topics), ("data", toJson (hexBytes data))]

private def pair (j : Json) : Except String (Nat × Nat) := do
  match (← j.getArr?).toList with
  | [a, b] => return (← word a, ← word b)
  | _ => throw "expected pair of decimal words"

/-- Replay one pinned initial storage world through real Denote execution. -/
def execute (model : CompilationModel) (oracle : DenoteOracle) (input : Json) :
    Except String Json := do
  let account ← getWord input "account"
  unless account < 2^160 do throw "model account exceeds address width"
  let storage ← (← (← input.getObjVal? "storage").getArr?).toList.mapM pair
  unless (storage.map Prod.fst).eraseDups.length == storage.length do
    throw "duplicate initial model storage slot"
  let mut world := storage.foldl
    (fun current entry => current.writePhysicalSlot entry.1 (Uint256.ofNat entry.2))
    { Verity.defaultState with thisAddress := Address.ofNat account }
  let initialAccounts := (input.getObjVal? "accounts").toOption
  let mut configuredAccounts : List Nat := []
  if let some entries := initialAccounts then
    for entry in (← entries.getArr?) do
      let address ← getWord entry "address"
      unless address < 2^160 do throw "initial external account exceeds address width"
      if address == account then throw "external account metadata cannot replace the executing contract"
      if configuredAccounts.contains address then throw "duplicate initial external account"
      configuredAccounts := address :: configuredAccounts
      let nonce ← getWord entry "nonce"
      let balance ← getWord entry "balance"
      let code ← (← (← entry.getObjVal? "code").getArr?).toList.mapM fun byte => do
        let value ← word byte
        if bound : value < 256 then pure (⟨value, bound⟩ : Fin 256)
        else throw "initial code byte exceeds uint8"
      let slots ← (← (← entry.getObjVal? "storage").getArr?).toList.mapM pair
      unless (slots.map Prod.fst).eraseDups.length == slots.length do
        throw "duplicate initial external storage slot"
      if bound : nonce < 2^64 then
        let state : AccountState := { nonce := ⟨nonce, bound⟩, balance := Uint256.ofNat balance, code }
        let state := slots.foldl (fun current slot => current.writeStorage slot.1 (Uint256.ofNat slot.2)) state
        world := world.writeAccount (Address.ofNat address) state
      else throw "initial external nonce exceeds EIP-2681 bound"
  let externalFns := model.functions.filter fun fn =>
    !fn.isInternal && !isInteropEntrypointName fn.name
  let dispatch := externalFns.map fun fn =>
    (fn, (KeccakEngine.keccak256_selector (functionSignature fn)).toNat)
  unless (dispatch.map Prod.snd).eraseDups.length == dispatch.length do
    throw "ambiguous model function selectors"
  let transactions ← (← input.getObjVal? "transactions").getArr?
  let mut rows := #[]
  let mut ids : List String := []
  for transaction in transactions do
    let ident ← transaction.getObjValAs? String "id"
    if ident.isEmpty || ids.contains ident then throw "nonempty unique model transaction ids required"
    ids := ident :: ids
    let name ← transaction.getObjValAs? String "function"
    let candidates := externalFns.filter (·.name == name)
    let [fn] := candidates | throw s!"model function must resolve uniquely: {name}"
    let args ← (← (← transaction.getObjVal? "args").getArr?).toList.mapM word
    let selector ← getWord transaction "selector"
    unless selector < 2^32 do throw "model selector exceeds four bytes"
    let [selected] := dispatch.filter (fun entry => entry.2 == selector)
      | throw "source calldata selector does not resolve to a model function"
    unless selected.1.name == name do
      throw "source calldata selector differs from model function"
    let sender ← getWord transaction "sender"
    unless sender < 2^160 do throw "model sender exceeds address width"
    let target ← getWord transaction "target"
    unless target == account do throw "foreign model target not supported by scalar adapter"
    let value ← getWord transaction "value"
    unless value == 0 do throw "model adapter does not yet account for value transfers"
    let timestamp ← getWord transaction "timestamp"
    let number ← getWord transaction "blockNumber"
    let observed ← (← (← transaction.getObjVal? "observe").getArr?).toList.mapM pair
    unless observed.all (fun p => p.1 == account || configuredAccounts.contains p.1) do
      throw "external storage observation requires explicit initial metadata"
    let observedAccounts ← match (transaction.getObjVal? "observeAccounts").toOption with
      | none => pure []
      | some entries => (← entries.getArr?).toList.mapM word
    unless observedAccounts.eraseDups.length == observedAccounts.length do
      throw "duplicate external account observation"
    unless observedAccounts.all configuredAccounts.contains do
      throw "external account observation requires explicit initial metadata"
    let tx : DenoteTransaction :=
      { sender, txOrigin := sender, thisAddress := account, msgValue := value,
        blockTimestamp := timestamp, blockNumber := number, chainId := 31337,
        functionSelector := selector, args }
    let initial := beginTransaction (withTransactionContext world tx)
    let publicResult := denoteFunction oracle model fn tx initial
    let result : TracedFrameResult ←
      match bindExternalParams selector fn.bindingParams args with
      | none => pure ⟨⟨false, [], initial⟩, []⟩
      | some bindings =>
          executeTracedBody oracle (effectiveFields model) initial
            bindings fn.body model.events model.errors selector
    unless result.frame.success == publicResult.success do
      throw "traced execution status differs from public Denote"
    if publicResult.success then
      let returned := if publicResult.returnWords.isEmpty then publicResult.returnValue.toList
        else publicResult.returnWords
      unless result.frame.data == returned.flatMap wordBytes do
        throw "traced return data differs from public Denote"
    let emitted ← result.frame.world.events.mapM (encodeEvent account model.events)
    let touched ← result.touched.filterMapM fun key =>
      match key with
      | .slot slot => pure (some slot)
      | .transient _ => pure none
      | _ => throw "unencoded model storage key"
    let touched := touched.eraseDups
    let slots := (touched ++ (observed.filter (fun p => p.1 == account)).map Prod.snd).eraseDups
    let storageQueries := ((touched.map (fun slot => (account, slot))) ++ observed).eraseDups
    world := result.frame.world
    unless slots.all (fun slot => world.readSlot slot ==
        (world.accountWorld (Address.ofNat account)).storageAt slot) do
      throw "model flat/account storage observations are incoherent"
    let metadata := observedAccounts.map fun address =>
      let state := world.accountWorld (Address.ofNat address)
      Json.mkObj [("address", toJson (hexAddress address)), ("nonce", toJson (hexWord state.nonce.val)),
        ("balance", toJson (hexWord state.balance.val)),
        ("code", toJson (hexBytes (state.code.map (fun byte => UInt8.ofNat byte.val))))]
    rows := rows.push (Json.mkObj ([
      ("id", toJson ident), ("status", toJson (if result.frame.success then "ok" else "revert")),
      ("data", toJson (hexBytes result.frame.data)),
      ("touched", toJson (touched.map fun slot => [hexAddress account, hexWord slot])),
      ("storage", toJson (storageQueries.map fun query =>
        [hexAddress query.1, hexWord query.2,
          hexWord ((world.accountWorld (Address.ofNat query.1)).storageAt query.2).val])),
      ("events", toJson emitted)] ++
      (if observedAccounts.isEmpty then [] else [("accounts", toJson metadata)])))
  return Json.arr rows

/-- The generated model driver supplies the actual model and hash oracle. -/
def run (model : CompilationModel) (oracle : DenoteOracle) (args : List String) : IO UInt32 := do
  let [input, output] := args | throw (IO.userError "expected INPUT OUTPUT")
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let result ← IO.ofExcept (execute model oracle parsed)
  IO.FS.writeFile output (Json.compress result)
  return 0
end Compiler.CompilationModel.SolidityImport.SequenceRunner
