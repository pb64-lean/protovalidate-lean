module

/-!
Runtime support for `protoc-gen-lean-protovalidate` generated code.

Generated `validate` functions check each CEL rule with a decidable test and
either produce the refined (validated) message or the first `Violation`.
-/

@[expose] public section

namespace Protovalidate

/-- A failed rule, mirroring the essentials of protovalidate's `Violation`:
the offending field (empty for message-level rules), the rule id from the
CEL annotation, and its human-readable message (falling back to the CEL
expression when the annotation carries no message). -/
structure Violation where
  fieldPath : String := ""
  ruleId : String := ""
  message : String := ""
deriving Repr, DecidableEq, Inhabited

instance : ToString Violation where
  toString v :=
    let path := if v.fieldPath.isEmpty then "(message)" else v.fieldPath
    s!"{path}: {v.message} [{v.ruleId}]"

end Protovalidate
