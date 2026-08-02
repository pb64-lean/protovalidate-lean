# protovalidate/defs.bzl
"""Public API for protovalidate_lean (protovalidate refinement types for Lean).

    load("@protovalidate_lean//protovalidate:defs.bzl", "lean_protovalidate_library")

lean_protovalidate_library layers on rules_lean_grpc's lean_proto_library: the
base target generates the plain message types, and this rule generates (and
compiles) their validated variants — structures whose CEL-annotated fields are
Lean subtypes refining the base field types, with validate/toBase functions.
See README.md for the CEL → Lean mapping.
"""

load(":codegen.bzl", _lean_protovalidate_library = "lean_protovalidate_library")

lean_protovalidate_library = _lean_protovalidate_library
