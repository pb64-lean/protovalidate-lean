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
`validate` is its `Except` view, so the theorems are instances of the generic
`Decision` lemmas with no per-message proof search. Soundness hands back the
conjuncts over the *input* base value (`(M.validate_sound h).items_elems`),
which downstream code can project and rewrite along without re-running any
checks. `Test/PredSchemeTest.lean` keeps a hand-written mirror of the emission
scheme compiling.

Five `lean_assurance_test` targets audit axiom closures at compile time (no
`sorryAx`, standard axioms only), covering both the instances and the scheme
they instantiate. Every generated example in the repo is audited:

| target | principal theorems |
|---|---|
| `//lean:runtime_assurance` | the generic `Decision` lemmas (`pred_of_toExcept_ok`, `toExcept_isOk`, `decodeThenValidate_sound`), the presence plumbing, `size_mapArray` — plus a scan of the whole `Protovalidate.Cel`/`Runtime` surface the generated propositions are stated over |
| `//lean:format_laws_assurance` | the `Cel.Format` recognizer laws (see [format assurance](#format-assurance-what-the-battery-does-and-does-not-say)), headed by `ipv4Value?_lt` |
| `//examples/shipping:shipping_valid_assurance` | `shipping.v1.Valid.{Order,Item}` (soundness, completeness, decode) and the validated `Order.payer_Type` sum |
| `//examples/shipping:inventory_valid_assurance` | `catalog.v1.Valid.{Product,Payment}` and the `Payment.method_Type` sum (standard rules, enums, element rules, validated oneof) |
| `//examples/common:money_valid_assurance` | `common.v1.Valid.Money` — the cross-target embed, audited at its source |

A repeated-message field's own rules are stated over the *validated* array
(`Protovalidate.mapArray b.f Elem.ofPred h.f_elems`), because those rules may
mention the element type's refinements. `Protovalidate.size_mapArray` moves
the structural ones back to `b.f` (`(mapArray …).size = xs.size`); it is a
propositional rewrite, not a definitional one, which is why the conjunct is
not phrased over `b.f` directly. `toBase` is likewise not a left inverse of
`ofPred` — it drops the base value's unknown wire fields — so message rules
traversing a validated field cannot be restated over the base value at all
(`Test/PredSchemeTest.lean` witnesses both facts).

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
engine's own grammar (a Go port, plus RE2 validity), then `#guard`-checked at
Lean compile time — both for acceptance and against a per-pattern battery of
RE2-labelled probe strings (see
[regex assurance](#regex-assurance-what-the-guards-do-and-do-not-say)) — and
decided at runtime by the pure-Lean engine in
`Protovalidate.Cel.Regex` (a Pike-VM NFA: classes, Perl classes, anchors,
alternation, bounded quantifiers; linear time, total). The
`email/hostname/ip/uri/...` formats are real implementations in
`Protovalidate.Cel.Format` following protovalidate's grammars, differentially
tested at Lean compile time against protovalidate's own conformance suite (see
[format assurance](#format-assurance-what-the-battery-does-and-does-not-say)).
`timestamp('...')`/`duration('...')` literals fold to
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
| `isEmail` `isHostname` `isUri` `isUriRef` `isIp` `isIpPrefix` `isHostAndPort` | `.isEmail` ... | real grammars in `Cel.Format` (HTML-standard email, RFC 1034, RFC 4291 + RFC 4007 zones, RFC 3986 + RFC 6874, CIDR) |
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
  proposition. Where the plugin resolves the operand's proto type (see
  *descriptor-aware numerics* below) the arithmetic is **lifted to CEL's own
  width** first — an `int32` field's `this * 100` emits `x.toInt64 * 100`
  under `Cel.mulOk x.toInt64 100` — so the guard is exactly CEL's condition
  and an intermediate outside the 32-bit range is not an overflow, matching
  CEL. Division and modulo widen too (fixing `int32Min / -1`, which wraps in
  `Int32` but not in CEL). Comprehension binders and indexed elements are typed
  too (see below), so this reaches inside `all`/`exists` bodies; only values
  with no proto type at all (free identifiers) fall back to the operand's own
  Lean type, where `Int32`/`UInt32` operands demand the 32-bit range —
  conservatively stricter than CEL, sound but not exact.
  `Nat` size arithmetic guards truncating subtraction. Constant arithmetic
  folds and range-checks at generation time (an always-erroring rule is
  rejected); concatenation and timestamp/duration arithmetic are total and
  unguarded.
- **Descriptor-aware numerics**: Lean silently wraps an out-of-range literal
  (`(3000000000 : Int32)` elaborates to `-1294967296`), so the plugin
  range-checks every numeric literal against the domain of the proto value it
  meets and **rejects the rule at generation time** with a source-located
  error naming the field's Lean type and bounds. This covers `this` in a
  scalar field rule, `this`-rooted select paths in message rules (including
  map-selection leaves and enum ints, which CEL compares as `int32`), and
  custom CEL on `repeated.items`/`map.keys`/`map.values` elements; it also
  rejects negative literals against unsigned fields. Literals meeting a
  *widened* arithmetic result are checked at 64-bit width instead, so
  `this * 10000 <= 5000000000` on an `int32` field is accepted — the product
  is `Int64`. The same typing makes mixed-width comparisons elaborate
  (`this.small < this.big` across `int32`/`int64` widens the narrower side).
- **Container elements are typed**: a path may descend into a container, so
  the value a comprehension binds (`this.all(v, …)` — a repeated field's
  elements, a map's keys) and the value indexing yields (`this.items[0]` — an
  element, a map's value) carry the same descriptor typing a named field does.
  Paths compose through binders, so `this.all(o, o.lots.all(n, n > 3e9))` is
  range-checked at the innermost element's type. This closes the last
  silent-wrap corner: only free identifiers now go untyped.
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
  view, matching CEL's enum-as-int semantics — including enum values a
  comprehension binds or indexing reaches (`this.tier_history[0] >= 1`), under
  the index guard. Standard enum rules keep their constructor-test form.
- **Map selection sugar works**: `this.labels.priority` becomes guarded key
  indexing (missing key ⇒ false, CEL's error), and `has(this.labels.priority)`
  becomes key presence — at any path depth.
- Warnings (stderr / JSON) flag translations with caveats: `has()` presence
  semantics beyond `Option` fields, evaluation-time-dependent `now`,
  placeholder timestamp/duration types, free identifiers kept verbatim,
  non-literal regex patterns.
- **`float` fields are compared at double precision**, as CEL does. A proto
  `float` is Lean `Float32`, but CEL converts it to a double before any numeric
  operation, so a typed `float` value is emitted as `x.toFloat` wherever it
  meets a literal, another numeric field, or arithmetic (`this <= 1.1` on a
  `float` field becomes `x.toFloat ≤ 1.1`). Widening Float32 → Float is exact,
  so this only removes a rounding: without it the literal would elaborate at
  `Float32` and `this == 1.1` would be *satisfiable* in Lean (by the `Float32`
  nearest 1.1) while being unsatisfiable in CEL — the kernel proving a
  proposition whose CEL evaluation is false. Standard `float.*` rules are left
  narrow deliberately: their bounds come from the descriptor and are already
  exactly `Float32` values, so the comparison cannot round either way. A
  `float`/`double` field comparison now elaborates too (the `float` side
  widens). What remains: `string(e)` uses `toString`, whose formatting may
  diverge from CEL's for floats.

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
  runtime, which would be unsound under negation. See
  [regex assurance](#regex-assurance-what-the-guards-do-and-do-not-say) for
  the layers that prevent it and their exact scope. `validate` reports the
  first violation (fieldPath, ruleId, message); `toBase` drops unknown
  fields.
- A field's rules are decided as one dependent-`if` chain drawing hypothesis
  names from a fixed 64-name pool; a field carrying more than 64 rules is a
  generation-time error rather than Lean with a captured binder.

### Regex assurance: what the guards do and do not say

`string.pattern` and CEL `matches` are decided at runtime by
`Protovalidate.Cel.Regex`, a pure-Lean Pike VM. It is *trusted code*: no
theorem relates it to a mathematical semantics of regular expressions. What
protects it is a generation-time gate plus two compile-time batteries, and it
is worth being exact about their reach.

**Enforced.** For every *literal* pattern:

1. `celtolean.RegexAccepted` (a hand-written Go port of the Lean engine's
   grammar) must accept it, and Go's RE2 (`regexp.Compile`) must accept it —
   a source-located generation error otherwise. The port is deliberately
   *stricter* where RE2 and the Lean parser would silently diverge (POSIX
   named classes, octal escapes, `[]-a]`).
2. The generated Lean file carries `#guard Cel.Regex.accepts "<pattern>"`.
   Lean evaluates it while elaborating the module, so if the Go gate accepted
   a pattern the Lean parser rejects, the build fails. This is what rules out
   the match-nothing fallback (and with it the unsoundness of
   `!this.matches(p)` degenerating to `true`).
3. A **differential battery** per pattern: probe strings walked out of the
   pattern's own RE2 syntax tree (the first and the last alternative, the
   minimum and one extra repetition, class representatives) plus
   perturbations of those, each labelled
   by Go's RE2 engine — the reference `matches` semantics — and emitted as
   `#guard Cel.regexMatch "<probe>" "<pattern>"` /
   `#guard !(Cel.regexMatch …)`. Lean re-decides every one at elaboration
   time, so a *language-level* disagreement between RE2 and the Lean engine on
   an emitted probe fails the build. Up to 10 probes per pattern; the same
   batteries are emitted for the `Test/cel_corpus.tsv` rows.

**Not enforced — do not read more into the guards than this.**

- The batteries are **differential testing, not equivalence**: agreement on
  finitely many probe strings does not prove `Cel.Regex` and RE2 accept the
  same language for that pattern, let alone in general. There is no
  equivalence theorem and none is claimed; the Go side is not formalized.
- `#guard` is *kernel evaluation of a closed Bool*, not a proof carried in any
  theorem's axiom closure. A generated `validate_sound` does not depend on it.
- Nothing above applies to *dynamic* patterns (`this.matches(this.other)`):
  they are unreachable at generation time, still fall back to matching nothing
  when unsupported, and are flagged with a warning.
- The Go gate being stricter than the Lean parser is unchecked (and harmless:
  it only rejects patterns the engine could have handled). Only the other
  direction — Go accepts, Lean rejects — is unsound, and that is exactly what
  guard 2 catches.

### Format assurance: what the battery does and does not say

`Protovalidate.Cel.Format` implements protovalidate's well-known string
formats (`email, hostname, address, ip, ipv4, ipv6, ip_prefix,
ip_with_prefixlen, host_and_port, uri, uri_ref`) as hand-written grammars.
Like the regex engine it is *trusted code*: no theorem relates it to the RFCs.

**Enforced.** `//Test:format_corpus_test` compiles `Test/format_corpus.tsv`
into a module of `#guard`s and Lean re-decides every one at elaboration time.
The corpus is **upstream protovalidate's own conformance suite** — the
`cases_is_*.go` / `cases_strings.go` expectations in the `protovalidate` bazel
module this build already depends on, which are normative for every
protovalidate runtime — extracted by `cmd/formatcorpus -extract` (a dev-time
step; the build only reads the TSV). 731 labelled inputs, covering the RFC
edge cases the suite exercises: trailing dots, all-digit labels, 63/64-char
labels, IPv6 zone identifiers, bracketed and zone-bearing hosts, IPvFuture,
percent-encoded UTF-8 in hosts, port ranges, leading zeros, uppercase hex,
IDN labels, empty parts. Each row is checked through the expression *codegen
emits* (`x.isIpPrefix 4 true`, the `isHostname || isIp` disjunction
`string.address` lowers to, the `Cel.regexMatch` calls `string.uuid` /
`string.tuuid` lower to), so a wrapper-level slip is caught too.

Standing this up found 19 disagreements, all of them bugs on this side — the
RFC 5322 dot-atom reading of `isEmail` (protovalidate uses the HTML living
standard's definition), a rejected DNS-root trailing dot, missing RFC 4007
zone identifiers, first- rather than last-separator splitting in
`isHostAndPort`, and missing IPvFuture / RFC 6874 zones / percent-encoded-UTF-8
checking in URI hosts. All are fixed; the corpus is what keeps them fixed.

**Not enforced — do not read more into the battery than this.**

- It is **differential testing against a finite corpus**, not a proof that
  `Cel.Format` implements the RFCs, and not a proof that it agrees with
  protovalidate on inputs the corpus does not contain. There is no equivalence
  theorem and none is claimed.
- `#guard` is kernel evaluation of a closed `Bool`, not a proof carried in any
  theorem's axiom closure — a generated `validate_sound` does not depend on it.
- The corpus is a **vendored snapshot**. It is only as current as the last
  `-extract` run; nothing in the build detects that upstream added cases.
- Formats protovalidate has that this repo does not lower at all (`ulid`,
  `well_known_regex`) are rejected at generation time, so they have no
  corpus rows.

**Proved, not sampled.** `Cel.Format`'s recognizer laws
(`lean/Protovalidate/Cel/FormatLaws.lean`, audited by
`//lean:format_laws_assurance`) carry the complementary kind of evidence —
properties holding for *every* input rather than for corpus points. The
load-bearing one is `ipv4Value?_lt`: the value an accepted IPv4 address denotes
really is below `2 ^ 32`, which is exactly what `isIpPrefix`'s host-bit masking
(`v % 2 ^ (32 - len)`) assumes. The others pin documented shape claims
(`ipv4Value?_length`, `isHostname_length`, `isPort_le`, `isIp_version` — only
versions 0/4/6 are ever accepted). The URI, email and IPv6 grammars carry no
such laws; they rest on the corpus alone.

## Layout

```
celtolean/            Go library: CEL AST → Lean expression (golden tests)
cmd/cel2lean/         CLI: single expression, -json, -batch corpus→Lean
cmd/protoc-gen-lean-protovalidate/  protoc plugin entry point
leanvalidate/         plugin codegen: descriptors + buf.validate rules → Lean
lean/Protovalidate/   Lean runtime (modules Protovalidate.Cel, .Runtime) plus
                      Cel/FormatLaws.lean (recognizer theorems, not runtime)
protovalidate/        Starlark API: lean_protovalidate_library (defs.bzl)
Test/                 corpus TSV + genrule compiling every translation with
                      Decidable assertions (build_test) + stand-in msg types.
                      A row's flags may carry `dom=<proto kind>` to supply the
                      descriptor typing the plugin would derive.
                      format_corpus.tsv holds protovalidate's conformance
                      expectations for the string formats (see format
                      assurance above).
cmd/formatcorpus/     extracts that corpus from an upstream protovalidate
                      checkout, and renders it as the Lean #guard battery
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
3. Residual conservative spots (sound, but stricter than CEL or late-failing).
   Descriptor-aware numerics — now reaching comprehension binders and indexed
   elements — closed the literal-wrapping hole and made arithmetic guards
   CEL-exact wherever a rule's value resolves to a proto type. What is left:
   - free identifiers carry no descriptor type, so their literals are
     unchecked and their 32-bit guards stay conservative;
   - error absorption under negation (`!(err && false)`) translates to
     failure;
   - index proofs inside `exists_one`/`map`/`filter` bodies and negated
     quantifier bodies have no sound discharge point and are rejected.
4. No formal relation between `Protovalidate.Cel.Regex` and RE2 beyond the
   per-pattern differential batteries (see
   [regex assurance](#regex-assurance-what-the-guards-do-and-do-not-say)), nor
   between `Cel.Format`'s grammars and their RFCs beyond the conformance
   battery and the IPv4/hostname/port recognizer laws (see
   [format assurance](#format-assurance-what-the-battery-does-and-does-not-say)).
   Both corpora are vendored snapshots of upstream references; the URI, email
   and IPv6 grammars carry no laws yet.
