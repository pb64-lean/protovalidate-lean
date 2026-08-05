import Protobuf.Encoding
import SupportedCasesValid.bool

/-!
A deliberately small executor for the statically supported slice of the
protovalidate v1.2.2 conformance corpus.  The official runner speaks one
unframed protobuf request/response pair over stdin/stdout.  Keeping the
harness envelope decoder here (instead of translating the descriptor-heavy
harness proto) makes the dispatch table explicit and auditable.

This is not a dynamic protobuf implementation: every accepted `Any.type_url`
is listed in `runCase`, decoded as its generated Lean base type, and validated
by generated Lean code where the schema has an actual constraint.
-/

open Binary
open Protobuf Encoding

namespace Conformance

private def decodeMessage (bytes : ByteArray) : Except String Message :=
  (protoDecodeParseResultExcept (Get.run (getThe Message) bytes).toExcept).mapError toString

private def encodeMessage (msg : Message) : ByteArray :=
  Put.run (put msg)

private def requiredString (msg : Message) (field : Nat) : Except String String := do
  let value ← (msg.getString? field).mapError toString
  match value with
  | some value => pure value
  | none => throw s!"missing string field {field}"

private def bytesOrEmpty (msg : Message) (field : Nat) : Except String ByteArray := do
  let value ← (msg.getBytes? field).mapError toString
  pure (value.getD ByteArray.empty)

private def requiredMessage (msg : Message) (field : Nat) : Except String Message := do
  let value ← (msg.getMessage? field).mapError toString
  match value with
  | some value => pure value
  | none => throw s!"missing message field {field}"

private def stringValue (value : String) : ProtoVal :=
  .LEN value.toUTF8

private def messageValue (msg : Message) : ProtoVal :=
  .LEN (encodeMessage msg)

private def record (fieldNum : Nat) (value : ProtoVal) : Record :=
  { fieldNum, value }

private def fieldPathElement (number : Nat) (name : String) (fieldType : Nat) : Message :=
  { records := #[
      record 1 (.VARINT number),
      record 2 (stringValue name),
      record 3 (.VARINT fieldType),
    ] }

private def fieldPath (elements : Array Message) : Message :=
  { records := elements.map fun element => record 1 (messageValue element) }

private def boolConstViolation (violationMessage : String) : Message :=
  let valueField := fieldPath #[fieldPathElement 1 "val" 8]
  let ruleField := fieldPath #[
    fieldPathElement 13 "bool" 11,
    fieldPathElement 1 "const" 8,
  ]
  let violation : Message := { records := #[
    record 5 (messageValue valueField),
    record 6 (messageValue ruleField),
    record 2 (stringValue "bool.const"),
    record 3 (stringValue violationMessage),
  ] }
  -- TestResult.validation_error -> Violations.violations -> Violation.
  let violations : Message := { records := #[record 1 (messageValue violation)] }
  { records := #[record 2 (messageValue violations)] }

private def success : Message :=
  { records := #[record 1 (.VARINT 1)] }

private def compilationError (error : String) : Message :=
  { records := #[record 3 (stringValue error)] }

private def decodeError (typeName error : String) : Message :=
  compilationError s!"{typeName}: generated Lean decoder rejected the case: {error}"

private def runCase (typeUrl : String) (bytes : ByteArray) : Message :=
  match typeUrl with
  | "type.googleapis.com/buf.validate.conformance.cases.BoolNone" =>
      match buf.validate.conformance.cases.BoolNone.decode bytes with
      | .ok _ => success
      | .error error => decodeError "BoolNone" (toString error)
  | "type.googleapis.com/buf.validate.conformance.cases.BoolExample" =>
      match buf.validate.conformance.cases.BoolExample.decode bytes with
      | .ok _ => success
      | .error error => decodeError "BoolExample" (toString error)
  | "type.googleapis.com/buf.validate.conformance.cases.BoolConstTrue" =>
      match buf.validate.conformance.cases.BoolConstTrue.decode bytes with
      | .error error => decodeError "BoolConstTrue" (toString error)
      | .ok base =>
          match buf.validate.conformance.cases.Valid.BoolConstTrue.validate base with
          | .ok _ => success
          | .error violation => boolConstViolation violation.message
  | "type.googleapis.com/buf.validate.conformance.cases.BoolConstFalse" =>
      match buf.validate.conformance.cases.BoolConstFalse.decode bytes with
      | .error error => decodeError "BoolConstFalse" (toString error)
      | .ok base =>
          match buf.validate.conformance.cases.Valid.BoolConstFalse.validate base with
          | .ok _ => success
          | .error violation => boolConstViolation violation.message
  | unsupported =>
      compilationError s!"unsupported static conformance type: {unsupported}"

private def runEntry (entryBytes : ByteArray) : Except String Record := do
  let entry ← decodeMessage entryBytes
  let caseName ← requiredString entry 1
  let anyMessage ← requiredMessage entry 2
  let typeUrl ← requiredString anyMessage 1
  let value ← bytesOrEmpty anyMessage 2
  let result := runCase typeUrl value
  let resultEntry : Message := { records := #[
    record 1 (stringValue caseName),
    record 2 (messageValue result),
  ] }
  pure (record 1 (messageValue resultEntry))

private def execute (input : ByteArray) : Except String ByteArray := do
  let request ← decodeMessage input
  let mut results := #[]
  for candidate in request.getValuesOf 3 do
    let .LEN entryBytes := candidate
      | throw "TestConformanceRequest.cases contained a non-message value"
    results := results.push (← runEntry entryBytes)
  pure (encodeMessage { records := results })

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let input ← stdin.readBinToEnd
  match execute input with
  | .ok response =>
      stdout.write response
      stdout.flush
      pure 0
  | .error error =>
      stderr.putStrLn s!"protovalidate Lean conformance executor: {error}"
      pure 1

end Conformance

def main : IO UInt32 :=
  Conformance.main
