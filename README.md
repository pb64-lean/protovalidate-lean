# protovalidate-lean

[![CI](https://github.com/pb64-lean/protovalidate-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/protovalidate-lean/actions/workflows/ci.yml) [![Assurance](https://github.com/pb64-lean/protovalidate-lean/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/protovalidate-lean/actions/workflows/assurance.yml)

Partial [protovalidate](https://github.com/bufbuild/protovalidate) support for
pure Lean 4, focused on CEL annotation support, consuming and extending
[rules_lean](../rules_lean) and [grpc-lean](../grpc-lean).

Rather than a procedural CEL evaluator, each CEL-annotated field gets a **Lean
subtype**: a refinement of the plain field type by the proposition the CEL
expression denotes. The proto rule

```proto
string name = 1 [(buf.validate.field).cel = {
  id: "name.len", expression: "this.size() <= 100 && this.startsWith('foo')"
}];
```

corresponds to the field type

```lean
{ x : String // x.size ≤ 100 ∧ x.startsWith "foo" }
```

The base types are exactly the types grpc-lean's protobuf codegen produces
(`Int32`/`Int64`/`UInt32`/`UInt64`, `Float`/`Float32`, `Bool`, `String`,
`ByteArray`, `Array α` for repeated, `Std.HashMap κ ν` for maps, `Option α`
for explicit presence, verbatim snake_case field names), and the proposition
is compositional at CEL granularity — the constraint a Lean author would have
written by hand, never an opaque "satisfies this CEL string" predicate.

## Full pipeline

```starlark
load("@rules_lean_grpc//:defs.bzl", "lean_proto_library")
load("@protovalidate_lean//protovalidate:defs.bzl", "lean_protovalidate_library")

proto_library(
    name = "shipping_proto",
    srcs = ["shipping.proto"],
    deps = ["@protovalidate//proto/protovalidate/buf/validate:validate_proto"],
)

lean_proto_library(name = "shipping_lean", proto = ":shipping_proto")

lean_protovalidate_library(
    name = "shipping_valid",
    proto = ":shipping_proto",
    lean_proto = ":shipping_lean",   # base types the refinements wrap
)
```

`lean_protovalidate_library` runs `protoc-gen-lean-protovalidate` (a Go protoc
plugin using `celtolean` as a library) and compiles its output against the
base types. For every message with protovalidate rules it emits, in a parallel
`<package>.Valid` namespace:

- a **structure** whose annotated fields are subtypes of the base field types
  and whose message-level rules are dependent Prop fields over the value
  fields;
- **`ValidPred : Base → Prop`**, the declarative validity predicate: a Prop
  structure with one field per rule conjunct, phrased over the *base* value;
- **`validate : Base → Except Protovalidate.Violation Valid`**, deciding each
  rule (an evidence-carrying `Decision (ValidPred b)` under the hood, so the
  proofs flow into the structure) or reporting the first violation with its
  rule id, plus a `Decidable (ValidPred b)` instance;
- kernel-checked **soundness/completeness theorems** tying the two together
  (see below);
- **`toBase : Valid → Base`**, forgetting refinements;
- **`decodeValid : ByteArray → Except String Valid`**, composing the base
  wire decoder with validation.

### Soundness and completeness theorems

Every generated message additionally carries `M.ValidPred : Base → Prop` — a
declarative Prop structure with one named field per rule conjunct (presence
conjuncts for `required` Option shapes, `∀ x, b.f = some x → …` for optional
rules, `∀ x ∈ b.f, Elem.ValidPred x` for repeated-message elements, nested
`ValidPred`s for embedded messages, and the message-level CEL Props) — and
kernel-checked theorems relating it to the procedural validator:

```lean
theorem M.validate_sound    : M.validate b = .ok v → M.ValidPred b
theorem M.validate_complete : M.ValidPred b → (M.validate b).isOk
theorem M.decodeValid_sound : M.decodeValid bytes = .ok v →
    ∃ b, Base.decode bytes = .ok b ∧ M.validate b = .ok v
```

The scheme: `M.checkPred b : Protovalidate.Decision (M.ValidPred b)` decides
the whole predicate at once — each step either extends the proof or refutes
it while reporting the first violation in protovalidate rule order — and
`validate` is its `Except` view, so the theorems are instances of two generic
`Decision` lemmas with no per-message proof search. Soundness hands back the
conjuncts over the *input* base value (`(M.validate_sound h).items_elems`),
which downstream code can project and rewrite along without re-running any
checks. `Test/PredSchemeTest.lean` keeps a hand-written mirror of the emission
scheme compiling, and the example's `lean_assurance_test` audits the generated
theorems' axiom closure (no `sorryAx`, standard axioms only) at compile time.

### Standard rules

The standard rule vocabulary lowers onto the same refinement machinery
(mostly by synthesizing the equivalent CEL; enum and element rules assemble
Lean directly):

- **numerics** (all 12 int/uint/float kinds): `const`, `lt/lte/gt/gte`
  (including protovalidate's inverted-range disjunction), `in`/`not_in`,
  `finite`;
- **string**: `const, len, min_len, max_len, len_bytes, min_bytes, max_bytes,
  pattern, prefix, suffix, contains, not_contains, in, not_in` and the
  well-known formats `email, hostname, ip, ipv4, ipv6, uri, uri_ref, address,
  uuid, tuuid, ip_with_prefixlen (+v4/v6), ip_prefix (+v4/v6),
  host_and_port`;
- **bytes**: `const, len, min_len, max_len, prefix, suffix, contains, in,
  not_in`;
- **bool**: `const`; **enum**: `const, defined_only, in, not_in` (as
  constructor tests on the generated open inductive, e.g.
  `¬(x matches .«Unknown.Value» _)`);
- **repeated**: `min_items, max_items, unique`, and scalar `items` rules as
  `∀ v ∈ x, …`; **map**: `min_pairs, max_pairs`, and scalar `keys`/`values`
  rules quantified over `x.keys`/`x.values`;
- **`required`**: explicit-presence fields are *unwrapped* — the validated
  field drops its `Option` (validate reports `required` on `none`, `toBase`
  re-wraps with `some`); implicit-presence fields gain a non-zero rule;
- **`ignore`**: `IGNORE_ALWAYS` drops the field's rules;
  `IGNORE_IF_ZERO_VALUE` becomes a zero-escape disjunct
  (`{ x : String // x.isEmpty ∨ (x.isEmail) }`) with a fast path in validate.

`string.pattern` regexes are gated at codegen time against the runtime
engine's own grammar (a Go port, plus RE2 validity) and `#guard`-checked at
Lean compile time, then decided at runtime by the pure-Lean engine in
`Protovalidate.Cel.Regex` (a Pike-VM NFA: classes, Perl classes, anchors,
alternation, bounded quantifiers; linear time, total). The `email/hostname/ip/uri/...` formats are
real implementations in `Protovalidate.Cel.Format` following protovalidate's
grammars. `timestamp('...')`/`duration('...')` literals fold to
`Cel.Timestamp.mk`/`Cel.Duration.mk` constants at codegen time, with RFC
3339/duration parsers and timestamp/duration arithmetic (`now - this <=
duration('24h')`) available at runtime.

From the example's generated code (`examples/shipping/`):

```lean
structure Order where
  /-- CEL: `this.size() == 8` (id.len); `this.startsWith('ord-') || ...` (id.prefix) -/
  id : { x : String // x.size = 8 ∧ (x.startsWith "ord-" ∨ x.startsWith "ORD-") }
  status : String
  tracking : Option String
  /-- CEL: `this.size() > 0` (items.nonempty) -/
  items : { x : Array shipping.v1.Valid.Item // x.size > 0 }
  /-- CEL: `this >= 0 && this % 100 == 0` (discount.range) -/
  discount_cents : Option { x : Int64 // x ≥ 0 ∧ x % 100 = 0 }
  labels : Std.HashMap String String
  payer : Option (shipping.v1.Valid.Order.payer_Type)  -- validated sum: customer_id min_len
  /-- CEL: `this.status == 'SHIPPED' ? has(this.tracking) : true` (order.tracking) -/
  order_tracking : status = "SHIPPED" → tracking.isSome
```

Note the composition rules visible above: message fields recursively use the
*validated* variant when they carry no field rules; repeated-message fields
with list rules refine the **array of validated elements** (structural rules
like `size()` compose with per-element validation); optional constrained
fields refine inside the `Option` (protovalidate evaluates rules only when
set); constrained oneofs use validated sums with refined constructor
payloads (unconstrained ones ride along as the base sum); message-level rules
become Props over the (refined) sibling fields — the CEL ternary idiom
`c ? p : true` lands as the implication `c → p`.

## cel2lean

The CEL → Lean expression converter, the core of the future codegen, usable
standalone:

```
$ bazel run //cmd/cel2lean -- 'this.size() <= 100 && !this.contains("bad")'
x.size ≤ 100 ∧ ¬Cel.contains x "bad"

$ bazel run //cmd/cel2lean -- -var s -json 'this == "" || this.isEmail()'
{"lean":"s = \"\" ∨ s.isEmail","var":"s","kind":"prop"}
```

It is written in Go around the **official cel-go parser** (with macro
expansion disabled, so `all`/`exists` arrive as calls and can be rendered as
binders). That choice anchors the hardest part — CEL grammar, escapes,
precedence, macro shapes — on the reference implementation; the translator
itself is a compact syntax-directed mapping (`celtolean/`). Go is a
codegen-time dependency only: nothing generated depends on Go at runtime, and
the eventual protoc plugin (which must read `buf.validate` descriptor
extensions) has first-class library support in Go.

### Pure CEL in, no FieldDescriptor

Translation consumes **only the CEL string** (plus a binder name). This works
because the output leans on Lean's own elaboration against the field's base
type:

- numeric literals stay polymorphic (`this >= 1` → `x ≥ 1` for any ordered
  numeric field);
- CEL functions map to dot-notation resolved by the receiver's type
  (`size()` → `.size`, `startsWith` → `.startsWith`);
- ill-typed CEL (wrong field names, mismatched types) becomes a Lean compile
  error in the generated code — deliberately deferred to the compiler.

Consequently the tool never generates the full subtype `def`; the codegen
layer will assemble `{ x : T // <emitted proposition> }` itself.

### Mapping

| CEL | Lean | note |
|---|---|---|
| `&&` `\|\|` `!` | `∧` `∨` `¬` | Props; `&&`/`\|\|` chains flattened |
| `==` `!=` | `=` `≠` | `↔` when an operand is itself propositional |
| `<` `<=` `>` `>=` | `<` `≤` `>` `≥` | |
| `e in c` | `e ∈ c` | list/array/map-key membership |
| `+ - * / %` | `+ - * / %` | `+` on strings/bytes/lists via `Add` shims; int/uint ops carry `Cel.addOk`-style overflow guards (see below) |
| `c ? p : true` | `c → p` | also `c ? p : false` → `c ∧ p`, `c ? true : p` → `c ∨ p` |
| `c ? a : b` | `if c then a else b` | decidable `ite` |
| `'lit'`, `b'lit'`, `123`, `1.5`, `null` | `"lit"`, `"lit".toUTF8`/`ByteArray.mk #[..]`, `123`, `1.5`, `none` | |
| `[1, 2]` / `{'k': v}` | `#[1, 2]` / `Std.HashMap.ofList [("k", v)]` | repeated fields are `Array` |
| `this` / `this.f` / `l[i]` | binder / `x.f` / guarded `(l[i]?).get h` | binder auto-renamed on collision; indexing guarded by `isSome` (CEL errors out of range) |
| `size(e)`, `e.size()` | `e.size` | `String.size`/`List.size` shims |
| `contains` | `Cel.contains e a` | typeclass: substring vs element vs subslice |
| `startsWith` `endsWith` | `.startsWith` `.endsWith` | + `ByteArray` shims |
| `matches` | `Cel.regexMatch e r` | pure-Lean RE2-subset engine (`Cel.Regex`); literal patterns gated at generation time + `#guard`ed at Lean compile time |
| `has(e.f)` | `e.f.isSome` | explicit-presence fields |
| `l.all(v, p)` / `l.exists(v, p)` | `∀ v ∈ l, p` / `∃ v ∈ l, p` | |
| `l.exists_one(v, p)` | `l.countP (fun v => p) = 1` | counts duplicates like CEL (not `∃!`) |
| `l.map(v, e)` / `l.filter(v, p)` | `l.map (fun v => e)` / `l.filter (fun v => p)` | Props `decide`-wrapped in Bool positions |
| `unique()` | `l.Nodup` | `Array.Nodup` shim, decidable |
| `isNan` `isInf` | `.isNaN` `.isInf`/`.isInfSign` | |
| `isEmail` `isHostname` `isUri` `isUriRef` `isIp` `isIpPrefix` `isHostAndPort` | `.isEmail` ... | real grammars in `Cel.Format` (RFC 5322 dot-atom, RFC 1034, RFC 4291, RFC 3986, CIDR) |
| `int() uint() double() bool()` | `Cel.toInt` ... | typeclass conversions |
| `string(e)` / `bytes(e)` / `dyn(e)` | `toString e` / `e.toUTF8` / `e` | |
| `timestamp() duration() now` | folded `Cel.Timestamp.mk s n` constants / `Cel.now` | literals fold at codegen; runtime RFC 3339 + duration parsers; `ts - ts`, `ts ± dur`, duration accessors |

Emitted propositions are **`Decidable`** end to end (asserted by the test
corpus), so runtime validation can construct subtype values by deciding the
refinement after decoding.

### Semantic notes

An erroring CEL rule is **not satisfied**; the translation encodes exactly
that (error ⇒ the proposition is false), so the kernel can never prove a
proposition whose CEL evaluation would have errored:

- **Integer division/modulo agree exactly with CEL.** grpc-lean maps proto
  ints to fixed-width `Int32`/`Int64` etc., whose Lean `/`/`%` truncate toward
  zero exactly like CEL's Go semantics. (Unbounded `Int` would not have
  matched — it uses Euclidean conventions.)
- **Overflow**: CEL integer arithmetic is 64-bit and errors on overflow.
  Every translated `+`/`-`/`*`/unary `-` on error-capable types carries a
  `Cel.addOk`/`subOk`/`mulOk`/`negOk` side-condition computing the exact
  result in unbounded `Int`/`Nat` and demanding the CEL domain, discharged as
  `if h : Cel.mulOk x 2 then … else False` — overflow falsifies the
  proposition. `Int64`/`UInt64` guards are CEL-exact; `Int32`/`UInt32` guards
  demand the 32-bit range (conservatively stricter than CEL's 64-bit
  intermediates — sound, never accepting what CEL rejects); `Nat` size
  arithmetic guards truncating subtraction. Constant arithmetic folds and
  range-checks at generation time (an always-erroring rule is rejected);
  concatenation and timestamp/duration arithmetic are total and unguarded.
- **Indexing**: CEL errors on an out-of-range index or missing map key, so
  `l[i]` / `m['k']` translate to `(l[i]?).get h` under a pending
  `(l[i]?).isSome` guard rather than a panicking `l[i]!`. Guards discharge at
  exactly the boundaries CEL's error absorption allows (`&&`/`||` operands,
  ternary branches, `all`/`exists` bodies — in positive polarity); in
  error-strict or negated contexts they float outward and close at the root,
  so `!x[0] > 5` on an empty array is *false*, matching CEL's error. The few
  shapes with no sound discharge point (index proofs inside
  `exists_one`/`map`/`filter` bodies or negated quantifier bodies) are
  source-located generation errors.
- **Enums work as ints**: the plugin resolves every `this` path against the
  descriptors, so enum-typed values (field rules, message-rule leaves,
  repeated/map element rules) render through the generated enum's `.toInt32`
  view, matching CEL's enum-as-int semantics. Standard enum rules keep their
  constructor-test form. (Enum values reached through *indexing* — an
  enum-valued `m['k']` compared to an int — still fail at Lean elaboration.)
- **Map selection sugar works**: `this.labels.priority` becomes guarded key
  indexing (missing key ⇒ false, CEL's error), and `has(this.labels.priority)`
  becomes key presence — at any path depth.
- Warnings (stderr / JSON) flag translations with caveats: `has()` presence
  semantics beyond `Option` fields, evaluation-time-dependent `now`,
  placeholder timestamp/duration types, free identifiers kept verbatim,
  non-literal regex patterns.
- `string(e)` uses `toString`, whose formatting may diverge from CEL's for
  floats. Numeric literals wider than a 32-bit field's type still elaborate
  by wrapping (a CEL type-checker would flag such rules).

## Codegen semantics and limitations

- Field rules apply to `this` = the field value: whole array/map for
  repeated/map fields, the unwrapped value for explicit-presence fields
  (checked only when present, matching protovalidate).
- Message rules may reference sibling fields (`this.f`) with CEL's value
  semantics, to any depth: heads go through generated per-field view
  functions (`(Order.featuredD featured)` — base-typed, default instance
  when unset), intermediate hops select the base codegen's `<field>D`
  getters (every non-final hop of a CEL path is message-typed), and final
  selects stay plain. `this.featured.dims.weight_grams <= 50000` lands as
  `(Order.featuredD featured).dimsD.weight_grams ≤ 50000`; `this.tracking`
  over an optional scalar reads as `(tracking.getD "")`. Refined plain
  fields become `f.val`, so the Prop states exactly what the structure
  carries. `has(this.f)` follows CEL's proto presence semantics per field: `isSome` for explicit presence, non-default for implicit scalars
  (`!f.isEmpty`, `f != 0`, non-zero enum case), non-empty for repeated/map,
  a case test (`o.any (· matches .member _)`, or `o matches .member _` for
  required oneofs) for oneof members, and `true` for `required` fields —
  so a message rule like `has(this.refund_iban) ? has(this.iban) : true`
  becomes an implication between case tests across oneofs. *Value* access to
  oneof members follows CEL's value-or-default semantics through generated
  `<member>_or_default` accessors (returning the base payload, the member
  type's zero value when the case is inactive): `this.iban.startsWith('DE')`
  on a required oneof lands as `method.iban_or_default.startsWith "DE"`.
  Paths through *nested* oneof members work too: base messages carry
  generated member getters (`m.iban` / `m.ibanD`, value-or-default), so
  `this.payment.store_credit_product.sku != 'banned'` lands as
  `(Order.paymentD payment).store_credit_productD.sku ≠ "banned"`. Nested
  `has()` delegates to generated `has_<field>`/`has_<member>` predicates
  encoding CEL's per-category semantics (case tests, `isSome`, non-empty,
  non-default), so `has(this.payment.cash_note) ? … : true` lands as
  `(Order.paymentD payment).has_cash_note → …`.
- Oneofs with constrained members generate a **validated sum type** whose
  constructors carry the refined payloads:
  `| iban : { x : String // x.size ≥ 15 ∧ x.size ≤ 34 } → Payment.method_Type`,
  with case-wise `validate`/`toBase`; unannotated message members embed the
  member type's validated variant. `(buf.validate.oneof).required` unwraps
  the `Option` (validate reports `required` on an unset oneof). `required` on
  an individual member is ignored with a note (the active case already
  implies presence). Unconstrained oneofs still ride along as the base sum.
  Every real oneof additionally gets per-member `<member>_or_default`
  accessors (on the validated sum, or extending the base sum's namespace for
  unconstrained oneofs), shaped to the field: bare-sum dot form for required
  oneofs, `Option`-taking otherwise.
- A message whose validated variant would be recursive (through validated
  message fields) is rejected at generation time — Lean structures cannot be
  recursive.
- Cross-target validated references work through `valid_deps` (paired with
  `proto_deps` on the base `lean_proto_library`): message fields typed by
  another target's protos use that target's validated variants, and
  violations surface through the embed. Map values always keep base types.
- Singular message fields with their own CEL rules refine the *base* message
  type (their CEL inspects base fields); element-wise validation composes
  automatically only for repeated-message fields.
- `google.protobuf.Timestamp`/`Duration` fields are supported end to end:
  grpc-lean maps their imports to the shared `Protobuf.WellKnown` module, and
  `Cel.Timestamp`/`Cel.Duration` *are* those generated types (comparisons,
  arithmetic, and `==` ignore unknown fields; propositional `=` on them is
  not decidable — use `==`/ordering in rules). Standard rules
  `timestamp.const/lt/lte/gt/gte` and
  `duration.const/lt/lte/gt/gte/in/not_in` lower like the numeric families;
  `lt_now`/`gt_now`/`within` are rejected (`Cel.now` is opaque — keep
  evaluation-time constraints outside the refinement).
- The regex engine rejects unsupported RE2 constructs (`(?i)` flags, `\b`,
  named classes) at parse time — such patterns would match nothing at
  runtime, which would be unsound under negation. Two layers prevent that
  for literal patterns: the generator gates every literal pattern through a
  Go port of the Lean engine's grammar (`celtolean.RegexAccepted`, stricter
  where RE2 and the engine would silently diverge: POSIX classes, octal
  escapes) with a source-located error, and every generated file carries a
  compile-time `#guard Cel.Regex.accepts "..."` per pattern, so a
  gate/engine disagreement fails the Lean build. Only *dynamic* patterns
  (`this.matches(this.other)`) can still reach the match-nothing fallback —
  flagged with a warning. `validate` reports the first violation (fieldPath,
  ruleId, message); `toBase` drops unknown fields.

## Layout

```
celtolean/            Go library: CEL AST → Lean expression (golden tests)
cmd/cel2lean/         CLI: single expression, -json, -batch corpus→Lean
cmd/protoc-gen-lean-protovalidate/  protoc plugin entry point
leanvalidate/         plugin codegen: descriptors + buf.validate rules → Lean
lean/Protovalidate/   Lean runtime (modules Protovalidate.Cel, .Runtime)
protovalidate/        Starlark API: lean_protovalidate_library (defs.bzl)
Test/                 corpus TSV + genrule compiling every translation with
                      Decidable assertions (build_test) + stand-in msg types
examples/shipping/    end-to-end pipeline example + runtime lean_test
```

(Lean sources sit under `lean/` — with the prefix stripped from module names —
because `Protovalidate/` would collide with the `protovalidate/` Starlark
package on case-insensitive filesystems.)

```
bazel test //...     # Go golden tests, corpus compile test, e2e runtime test
```

Note: grpc-lean's `protoc-gen-lean4` needed a small fix (imports emitted for
non-generated, option-only proto dependencies such as
`buf/validate/validate.proto`); it lives in grpc-lean commit
"protoc-gen-lean4: only import modules for generated dependencies".

## Remaining work

1. A conformance harness executing protovalidate's official test-suite data
   against generated validators (current coverage: unit batteries mirroring
   protovalidate library behavior plus the e2e examples).
2. Predefined (user-extension) rules; `(?i)` and `\b` in the regex engine;
   now-dependent rules (`timestamp.lt_now`/`within`), which need a
   validation-time story for `Cel.now`.
3. Residual conservative spots (sound, but stricter than CEL or late-failing):
   32-bit arithmetic guards demand the 32-bit range; error absorption under
   negation (`!(err && false)`) translates to failure; out-of-range literals
   against 32-bit fields wrap at elaboration; enum values reached through
   indexing lack the `.toInt32` view. Descriptor-aware literal range checks
   would close the last two.
