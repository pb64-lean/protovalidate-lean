package celtolean

import (
	"strings"
	"testing"
)

func TestTranslate(t *testing.T) {
	tests := []struct {
		name     string
		cel      string
		want     string
		kind     string
		warnings int
	}{
		// -- protovalidate documentation-style constraints --------------------
		{"string_max_len", `this.size() <= 100`, `x.size ≤ 100`, "prop", 0},
		{"int_range", `this >= 1 && this <= 100`, `x ≥ 1 ∧ x ≤ 100`, "prop", 0},
		{"starts_with", `this.startsWith('foo')`, `x.startsWith "foo"`, "bool", 0},
		{"not_contains", `!this.contains('forbidden')`, `¬Cel.contains x "forbidden"`, "prop", 0},
		{"regex", `this.matches('^[a-z0-9]+$')`, `Cel.regexMatch x "^[a-z0-9]+$"`, "bool", 0},
		{"empty_or_email", `this == '' || this.isEmail()`, `x = "" ∨ x.isEmail`, "prop", 0},
		{"all_positive", `this.all(item, item.quantity > 0)`, `∀ item ∈ x, item.quantity > 0`, "prop", 0},
		{"enum_like_in", `this in [1, 2, 3]`, `x ∈ #[1, 2, 3]`, "prop", 0},
		{"global_size", `size(this) > 0`, `x.size > 0`, "prop", 0},
		{"presence", `has(this.tracking_number)`, `x.has_tracking_number`, "bool", 0},
		{"presence_nested", `has(this.a.b)`, `x.aD.has_b`, "bool", 0},
		{"presence_deep", `has(this.a.b.c)`, `x.aD.bD.has_c`, "bool", 0},
		{"cents", `(this.price % 100) == 0`, `x.price % 100 = 0`, "prop", 0},
		{"float_range", `this.discount >= 0.0 && this.discount <= 1.0`, `x.discount ≥ 0.0 ∧ x.discount ≤ 1.0`, "prop", 0},
		{"field_compare", `this.end_time > this.start_time`, `x.end_time > x.start_time`, "prop", 0},

		// -- ternary folding ---------------------------------------------------
		{"implication", `this.state == 'DELIVERED' ? has(this.tracking) : true`,
			`x.state = "DELIVERED" → x.has_tracking`, "prop", 0},
		{"implication_neq", `this.enabled == true ? this.url != '' : true`,
			`x.enabled = true → x.url ≠ ""`, "prop", 0},
		{"ternary_and", `this.a > 0 ? this.b > 0 : false`, `x.a > 0 ∧ x.b > 0`, "prop", 0},
		{"ternary_or", `this.a > 0 ? true : this.b > 0`, `x.a > 0 ∨ x.b > 0`, "prop", 0},
		{"ternary_general", `this.a > 0 ? this.b : this.c`, `if x.a > 0 then x.b else x.c`, "term", 0},
		{"ternary_nested", `this.a > 0 ? this.b > 0 : this.c > 0`,
			`if x.a > 0 then x.b > 0 else x.c > 0`, "prop", 0},

		// -- literals ----------------------------------------------------------
		{"uint_literal", `this != 0u`, `x ≠ 0`, "prop", 0},
		{"hex_literal", `this == 0x7B`, `x = 123`, "prop", 0},
		{"neg_bounds", `-1 <= this && this <= 1`, `-1 ≤ x ∧ x ≤ 1`, "prop", 0},
		{"neg_float", `this >= -90.0 && this <= 90.0`, `x ≥ -90.0 ∧ x ≤ 90.0`, "prop", 0},
		{"float_int_valued", `this < 1.5e3`, `x < 1500.0`, "prop", 0},
		{"float_small", `this < 1e-5`, `x < 1e-05`, "prop", 0},
		{"string_escapes", "this.contains(\"say \\\"hi\\\"\\n\")", `Cel.contains x "say \"hi\"\n"`, "bool", 0},
		{"string_unicode", `this.contains('é')`, `Cel.contains x "é"`, "bool", 0},
		{"bytes_text", `this == b'foo'`, `x = "foo".toUTF8`, "prop", 0},
		{"bytes_raw", `this == b'\xff\x00'`, `x = ByteArray.mk #[0xff, 0x00]`, "prop", 0},
		{"null_compare", `this != null`, `x ≠ none`, "prop", 0},
		{"bool_field_eq", `this.a == this.b`, `x.a = x.b`, "prop", 0},

		// -- operators and precedence -------------------------------------------
		{"prec_and_or", `this.a || this.b && this.c`, `x.a ∨ x.b ∧ x.c`, "prop", 0},
		{"prec_paren_or", `(this.a || this.b) && this.c`, `(x.a ∨ x.b) ∧ x.c`, "prop", 0},
		{"chain_and", `this.a && this.b && this.c`, `x.a ∧ x.b ∧ x.c`, "prop", 0},
		{"not_eq", `!(this == '')`, `¬x = ""`, "prop", 0},
		{"not_and", `!(this.a && this.b)`, `¬(x.a ∧ x.b)`, "prop", 0},
		{"arith", `this * 2 + 1 <= 100`,
			`(if h : Cel.mulOk x 2 then if h_1 : Cel.addOk (x * 2) 1 then x * 2 + 1 ≤ 100 else False else False)`, "prop", 0},
		{"arith_assoc", `this - (this / 2) * 2 == this % 2`,
			`(if h : Cel.mulOk (x / 2) 2 then if h_1 : Cel.subOk x (x / 2 * 2) then x - x / 2 * 2 = x % 2 else False else False)`, "prop", 0},
		{"sub_reassoc", `this - (this - 1) == 1`,
			`(if h : Cel.subOk x 1 then if h_1 : Cel.subOk x (x - 1) then x - (x - 1) = 1 else False else False)`, "prop", 0},
		{"concat", `this + '!' == 'hi!'`, `x + "!" = "hi!"`, "prop", 0},
		{"bool_of_bools_iff", `!this.a == this.b`, `¬x.a ↔ x.b`, "prop", 0},
		{"index", `this[0] > 5`, `(if h : (x[0]?).isSome then (x[0]?).get h > 5 else False)`, "prop", 0},
		{"map_key_in", `'k' in this.labels`, `"k" ∈ x.labels`, "prop", 0},
		{"map_index", `this.labels['env'] == 'prod'`,
			`(if h : (x.labels["env"]?).isSome then (x.labels["env"]?).get h = "prod" else False)`, "prop", 0},

		// -- macros --------------------------------------------------------------
		{"exists", `this.exists(v, v in [1, 2])`, `∃ v ∈ x, v ∈ #[1, 2]`, "prop", 0},
		{"exists_one", `this.exists_one(i, i > 0)`, `x.countP (fun i => decide (i > 0)) = 1`, "prop", 0},
		{"nested_all", `this.all(a, a.all(b, b > 0))`, `∀ a ∈ x, ∀ b ∈ a, b > 0`, "prop", 0},
		{"map_macro_eq", `this.map(v, v * 2) == [2, 4]`,
			`(if h_1 : (∀ v ∈ x, Cel.mulOk v 2) then x.map (fun v => v * 2) = #[2, 4] else False)`, "prop", 0},
		{"map_filter_macro", `this.map(v, v > 0, v * 2).size() > 0`,
			`(if h_1 : (∀ v ∈ x, Cel.mulOk v 2) then ((x.filter (fun v => decide (v > 0))).map (fun v => v * 2)).size > 0 else False)`, "prop", 0},
		{"filter_size", `this.filter(i, i > 0).size() == this.size()`,
			`(x.filter (fun i => decide (i > 0))).size = x.size`, "prop", 0},
		{"map_then_exists", `this.map(s, s.size()).exists(n, n > 10)`,
			`∃ n ∈ x.map (fun s => s.size), n > 10`, "prop", 0},
		{"all_over_bool_atom", `this.all(s, s.startsWith('a'))`, `∀ s ∈ x, s.startsWith "a"`, "prop", 0},

		// -- protovalidate extension functions -------------------------------------
		{"unique", `this.unique()`, `x.Nodup`, "prop", 0},
		{"is_nan", `this.isNan() || this >= 0.0`, `x.isNaN ∨ x ≥ 0.0`, "prop", 0},
		{"is_inf_sign", `!this.isInf(1)`, `¬x.isInfSign 1`, "prop", 0},
		{"is_ip_v4", `this.isIp(4)`, `x.isIp 4`, "bool", 0},
		{"is_ip_prefix_strict", `this.isIpPrefix(true)`, `x.isIpPrefix (strict := true)`, "bool", 0},
		{"is_ip_prefix_full", `this.isIpPrefix(4, true)`, `x.isIpPrefix 4 true`, "bool", 0},
		{"host_and_port", `this.isHostAndPort(true)`, `x.isHostAndPort true`, "bool", 0},
		{"hostname", `this.isHostname()`, `x.isHostname`, "bool", 0},

		// -- conversions and misc ----------------------------------------------------
		{"to_int", `int(this) < 100`, `Cel.toInt x < 100`, "prop", 0},
		{"to_string", `string(this.id) == 'a'`, `toString x.id = "a"`, "prop", 0},
		{"string_lt", `this < 'zzz'`, `x < "zzz"`, "prop", 0},
		{"dyn_passthrough", `dyn(this) == 1`, `x = 1`, "prop", 0},
		{"timestamp_folded", `this < timestamp('2030-01-01T00:00:00Z')`,
			`x < Cel.Timestamp.mk 1893456000 0`, "prop", 0},
		{"timestamp_pre_epoch", `this < timestamp('1969-12-31T23:59:59.5Z')`,
			`x < Cel.Timestamp.mk (-1) 500000000`, "prop", 0},
		{"duration_folded", `duration('1h') > duration('30m')`,
			`Cel.Duration.mk 3600 0 > Cel.Duration.mk 1800 0`, "prop", 0},
		{"duration_negative", `this <= duration('-1.5s')`,
			`x ≤ Cel.Duration.mk (-1) (-500000000)`, "prop", 0},
		{"ts_arith", `now - this <= duration('24h')`,
			`Cel.now - x ≤ Cel.Duration.mk 86400 0`, "prop", 1},
		{"now", `this < now`, `x < Cel.now`, "prop", 1},
		{"presence_or", `has(this.a) || has(this.b)`, `x.has_a ∨ x.has_b`, "prop", 0},
		{"map_literal", `this in {'a': 1, 'b': 2}`,
			`x ∈ Std.HashMap.ofList [("a", 1), ("b", 2)]`, "prop", 0},
		{"keyword_fields", `this.end > this.from`, `x.«end» > x.«from»`, "prop", 0},
		{"deep_chain", `this.a.b.c == 1`, `x.aD.bD.c = 1`, "prop", 0},
		{"deep_final_message", `this.a.b != null`, `x.aD.b ≠ none`, "prop", 0},
		{"deep_then_index", `this.a.items[0].c > 0`,
			`(if h : (x.aD.items[0]?).isSome then ((x.aD.items[0]?).get h).c > 0 else False)`, "prop", 0},
		{"deep_then_macro", `this.a.tags.all(t, t.size() > 0)`, `∀ t ∈ x.aD.tags, t.size > 0`, "prop", 0},
		{"free_ident", `min_len <= this.size()`, `min_len ≤ x.size`, "prop", 1},

		// -- CEL error semantics: guarded indexing and arithmetic ---------------
		// An out-of-range index / overflow errors in CEL, and an erroring rule
		// is not satisfied: the guarded dite is False exactly then.
		{"index_negated", `!(this[0] > 5)`,
			`(if h : (x[0]?).isSome then ¬(x[0]?).get h > 5 else False)`, "prop", 0},
		{"index_conjunct", `this[0] > 5 && this.size() == 1`,
			`(if h : (x[0]?).isSome then (x[0]?).get h > 5 else False) ∧ x.size = 1`, "prop", 0},
		{"index_disjunct_absorbs", `this[0] > 5 || true`,
			`(if h : (x[0]?).isSome then (x[0]?).get h > 5 else False) ∨ True`, "prop", 0},
		{"index_not_conjunction_floats", `!(this[0] > 5 && this.size() == 1)`,
			`(if h : (x[0]?).isSome then ¬((x[0]?).get h > 5 ∧ x.size = 1) else False)`, "prop", 0},
		{"index_in_implication_cond_floats", `this[0] > 5 ? this.size() == 1 : true`,
			`(if h : (x[0]?).isSome then (x[0]?).get h > 5 → x.size = 1 else False)`, "prop", 0},
		{"index_in_implication_branch", `this.size() == 1 ? this[0] > 5 : true`,
			`x.size = 1 → (if h : (x[0]?).isSome then (x[0]?).get h > 5 else False)`, "prop", 0},
		{"nested_index", `this[this[0]] == 1`,
			`(if h : (x[0]?).isSome then if h_1 : (x[(x[0]?).get h]?).isSome then (x[(x[0]?).get h]?).get h_1 = 1 else False else False)`,
			"prop", 0},
		{"all_body_index", `this.all(i, this[0] <= i)`,
			`∀ i ∈ x, (if h : (x[0]?).isSome then (x[0]?).get h ≤ i else False)`, "prop", 0},
		{"neg_guarded", `-this < 0`, `(if h : Cel.negOk x then -x < 0 else False)`, "prop", 0},
		{"neg_literal_plain", `this < -1 + 2`, `x < -1 + 2`, "prop", 0},
		{"uint_sub_guarded", `this - 1u >= 0u`,
			`(if h : Cel.subOk x 1 then x - 1 ≥ 0 else False)`, "prop", 0},
		{"size_arith_guarded", `this.size() - 1 <= 10`,
			`(if h : Cel.subOk x.size 1 then x.size - 1 ≤ 10 else False)`, "prop", 0},
		{"concat_unguarded", `this + 'a' + 'b' == 'ab'`, `x + "a" + "b" = "ab"`, "prop", 0},
		{"list_concat_unguarded", `this + [1] == [2, 1]`, `x + #[1] = #[2, 1]`, "prop", 0},
		{"const_arith_folds", `this == 2 + 3 * 4`, `x = 2 + 3 * 4`, "prop", 0},
		{"time_arith_unguarded", `now - this <= duration('24h')`,
			`Cel.now - x ≤ Cel.Duration.mk 86400 0`, "prop", 1},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := Translate(tt.cel, Options{})
			if err != nil {
				t.Fatalf("Translate(%q) error: %v", tt.cel, err)
			}
			if got.Lean != tt.want {
				t.Errorf("Translate(%q)\n  got:  %s\n  want: %s", tt.cel, got.Lean, tt.want)
			}
			if got.Kind != tt.kind {
				t.Errorf("Translate(%q) kind = %s, want %s", tt.cel, got.Kind, tt.kind)
			}
			if len(got.Warnings) != tt.warnings {
				t.Errorf("Translate(%q) warnings = %v, want %d", tt.cel, got.Warnings, tt.warnings)
			}
		})
	}
}

// The binder for `this` must dodge identifiers used in the expression, so a
// comprehension variable named like the binder cannot capture references to
// `this` in the body.
func TestVarCollision(t *testing.T) {
	got, err := Translate(`this.all(x, x < this.size())`, Options{})
	if err != nil {
		t.Fatal(err)
	}
	if got.Var != "x_1" {
		t.Errorf("Var = %q, want x_1", got.Var)
	}
	if want := `∀ x ∈ x_1, x < x_1.size`; got.Lean != want {
		t.Errorf("got %s, want %s", got.Lean, want)
	}
}

// A dotted Var is a fixed projection: `this` substitutes verbatim, and
// comprehension variables that would capture its root get renamed.
func TestDottedVar(t *testing.T) {
	got, err := Translate(`this.size() <= 10 && this.startsWith('a')`, Options{Var: "b.name"})
	if err != nil {
		t.Fatal(err)
	}
	if want := `b.name.size ≤ 10 ∧ b.name.startsWith "a"`; got.Lean != want {
		t.Errorf("got %s, want %s", got.Lean, want)
	}

	got, err = Translate(`this.all(b, b < b.size())`, Options{Var: "b.items"})
	if err != nil {
		t.Fatal(err)
	}
	// The CEL variable b shadows every b inside the body (CEL scoping), so the
	// renamed binder must be used for body references too — and the fixed
	// substitution b.items must stay untouched.
	if want := `∀ b_1 ∈ b.items, b_1 < b_1.size`; got.Lean != want {
		t.Errorf("got %s, want %s", got.Lean, want)
	}
}

// ThisFields mode states message-level rules over structure field bindings.
func TestThisFieldsMode(t *testing.T) {
	fields := map[string]ThisField{
		"age":      {Text: "age.val", Has: "age.val != 0"},
		"email":    {Text: "email", Has: "!email.isEmpty"},
		"tracking": {Text: "tracking", Has: "tracking.isSome"},
		"items":    {Text: "items", Has: "!items.isEmpty"},
		"payer":    {Text: "payer", Has: "payer.any (· matches .customer_id _)"},
	}
	tests := []struct {
		cel  string
		want string
	}{
		{`this.age >= 18 || this.email == ''`, `age.val ≥ 18 ∨ email = ""`},
		{`has(this.tracking) ? this.age > 0 : true`, `tracking.isSome → age.val > 0`},
		{`this.items.all(i, i > 0)`, `∀ i ∈ items, i > 0`},
		// deep paths: the head is the mapped base-typed view; intermediate
		// hops use the base codegen's value-or-default getters.
		{`this.items.a.b > 0`, `items.aD.b > 0`},
		{`has(this.email) && has(this.items)`, `!email.isEmpty ∧ !items.isEmpty`},
		{`has(this.payer) || has(this.age)`, `(payer.any (· matches .customer_id _)) ∨ (age.val != 0)`},
	}
	for _, tt := range tests {
		got, err := Translate(tt.cel, Options{ThisFields: fields})
		if err != nil {
			t.Fatalf("Translate(%q): %v", tt.cel, err)
		}
		if got.Lean != tt.want {
			t.Errorf("Translate(%q)\n  got:  %s\n  want: %s", tt.cel, got.Lean, tt.want)
		}
	}

	if _, err := Translate(`this.missing > 0`, Options{ThisFields: fields}); err == nil {
		t.Error("expected error for unmapped field")
	}
	if _, err := Translate(`size(this) > 0`, Options{ThisFields: fields}); err == nil {
		t.Error("expected error for bare `this` in message-field mode")
	}
}

func TestCustomVar(t *testing.T) {
	got, err := Translate(`this.size() <= 10`, Options{Var: "s"})
	if err != nil {
		t.Fatal(err)
	}
	if want := `s.size ≤ 10`; got.Lean != want {
		t.Errorf("got %s, want %s", got.Lean, want)
	}
}

// Path attributes: proto-descriptor knowledge routed in by the plugin.
func TestPathAttrs(t *testing.T) {
	attrs := map[string]PathAttr{
		"":              PathEnumInt, // used only by the enum rows below
		"tier":          PathEnumInt,
		"featured.tier": PathEnumInt,
		"labels":        PathMapSelect,
	}
	tests := []struct {
		cel  string
		want string
	}{
		{`this == 2`, `x.toInt32 = 2`},
		{`this.tier == 2 || this.tier == this.featured.tier`,
			`tier.toInt32 = 2 ∨ tier.toInt32 = (Order.featuredD featured).tier.toInt32`},
		{`this.labels.env == 'prod'`,
			`(if h : (labels["env"]?).isSome then (labels["env"]?).get h = "prod" else False)`},
		{`has(this.labels.env) ? this.tier == 1 : true`, `(labels["env"]?).isSome → tier.toInt32 = 1`},
	}
	fields := map[string]ThisField{
		"tier":     {Text: "tier"},
		"featured": {Text: "(Order.featuredD featured)"},
		"labels":   {Text: "labels"},
		"size":     {},
	}
	for _, tt := range tests {
		var opts Options
		if strings.Contains(tt.cel, "this.") {
			opts = Options{ThisFields: fields, PathAttrs: attrs}
		} else {
			opts = Options{PathAttrs: attrs}
		}
		got, err := Translate(tt.cel, opts)
		if err != nil {
			t.Fatalf("Translate(%q): %v", tt.cel, err)
		}
		if got.Lean != tt.want {
			t.Errorf("Translate(%q)\n  got:  %s\n  want: %s", tt.cel, got.Lean, tt.want)
		}
	}
}

// Numeric domains (descriptor-supplied) do two things the type-free
// translation cannot: they reject literals that Lean would silently wrap into
// the field's fixed-width type, and they lift 32-bit proto integers to the
// width CEL actually computes at, making the overflow guards CEL-exact.
func TestNumericDomainWidening(t *testing.T) {
	tests := []struct {
		name  string
		attrs map[string]PathAttr
		cel   string
		want  string
	}{
		// int32 arithmetic is CEL-exact after widening: the guard is the
		// 64-bit condition CEL itself applies, not the conservative 32-bit one.
		{"int32_mul", map[string]PathAttr{"": PathInt32}, `this * 100 <= 1000000`,
			`(if h : Cel.mulOk x.toInt64 100 then x.toInt64 * 100 ≤ 1000000 else False)`},
		// ... which also admits intermediates outside the 32-bit range, exactly
		// as CEL does.
		{"int32_wide_intermediate", map[string]PathAttr{"": PathInt32}, `this + 3000000000 > 0`,
			`(if h : Cel.addOk x.toInt64 3000000000 then x.toInt64 + 3000000000 > 0 else False)`},
		{"int32_div", map[string]PathAttr{"": PathInt32}, `this / 2 == 1`, `x.toInt64 / 2 = 1`},
		{"int32_neg", map[string]PathAttr{"": PathInt32}, `-this < 0`,
			`(if h : Cel.negOk x.toInt64 then -x.toInt64 < 0 else False)`},
		{"uint32_sub", map[string]PathAttr{"": PathUInt32}, `this - 1u >= 0u`,
			`(if h : Cel.subOk x.toUInt64 1 then x.toUInt64 - 1 ≥ 0 else False)`},
		{"enum_arith", map[string]PathAttr{"": PathEnumInt}, `this + 1 == 2`,
			`(if h : Cel.addOk x.toInt32.toInt64 1 then x.toInt32.toInt64 + 1 = 2 else False)`},
		// 64-bit fields are already at CEL width: unchanged.
		{"int64_mul", map[string]PathAttr{"": PathInt64}, `this * 100 <= 1000000`,
			`(if h : Cel.mulOk x 100 then x * 100 ≤ 1000000 else False)`},
		// No arithmetic: no widening, so the emitted proposition stays the one
		// a Lean author would write over the field's own type.
		{"int32_plain_compare", map[string]PathAttr{"": PathInt32}, `this > 3`, `x > 3`},
		// Floats stay at the field's own type: CEL double arithmetic cannot
		// error, so there is no guard to tighten (the ArithOk instance is
		// trivially true) and widening would only obscure the proposition.
		{"float_no_widen", map[string]PathAttr{"": PathFloat}, `this * 2.0 < 5.0`,
			`(if h : Cel.mulOk x 2.0 then x * 2.0 < 5.0 else False)`},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := Translate(tt.cel, Options{PathAttrs: tt.attrs})
			if err != nil {
				t.Fatalf("Translate(%q): %v", tt.cel, err)
			}
			if got.Lean != tt.want {
				t.Errorf("Translate(%q)\n  got:  %s\n  want: %s", tt.cel, got.Lean, tt.want)
			}
		})
	}

	// Comparing proto integers of different widths: CEL compares them
	// directly, so the narrower one is lifted to the wider Lean type.
	fields := map[string]ThisField{"small": {Text: "small"}, "big": {Text: "big"}, "n": {Text: "n"}}
	attrs := map[string]PathAttr{"small": PathInt32, "big": PathInt64, "n": PathUInt32}
	mixed := []struct{ cel, want string }{
		{`this.small < this.big`, `small.toInt64 < big`},
		{`this.big == this.small`, `big = small.toInt64`},
		{`this.small + 1 > this.big`,
			`(if h : Cel.addOk small.toInt64 1 then small.toInt64 + 1 > big else False)`},
		{`this.n * 2u > 100u`,
			`(if h : Cel.mulOk n.toUInt64 2 then n.toUInt64 * 2 > 100 else False)`},
	}
	for _, tt := range mixed {
		got, err := Translate(tt.cel, Options{ThisFields: fields, PathAttrs: attrs})
		if err != nil {
			t.Fatalf("Translate(%q): %v", tt.cel, err)
		}
		if got.Lean != tt.want {
			t.Errorf("Translate(%q)\n  got:  %s\n  want: %s", tt.cel, got.Lean, tt.want)
		}
	}
}

// Literals outside the annotated field's domain would elaborate by wrapping
// (Lean has no range check on `(3000000000 : Int32)`), so they are rejected at
// generation time.
func TestNumericDomainRejects(t *testing.T) {
	fields := map[string]ThisField{"stock": {Text: "stock"}, "batch": {Text: "batch"}}
	tests := []struct {
		name  string
		attrs map[string]PathAttr
		this  map[string]ThisField
		cel   string
		frag  string
	}{
		{"int32_gt", map[string]PathAttr{"": PathInt32}, nil, `this < 3000000000`,
			"literal 3000000000 is outside the domain of the int32 value"},
		{"int32_lt", map[string]PathAttr{"": PathInt32}, nil, `-3000000000 <= this`,
			"literal -3000000000 is outside the domain of the int32 value"},
		{"int32_eq", map[string]PathAttr{"": PathInt32}, nil, `this == 2147483648`,
			"outside the domain of the int32 value"},
		{"uint32_negative", map[string]PathAttr{"": PathUInt32}, nil, `this > -1`,
			"negative literal -1 cannot be represented by the unsigned uint32 field"},
		{"uint32_wide", map[string]PathAttr{"": PathUInt32}, nil, `this != 4294967296u`,
			"outside the domain of the uint32 value"},
		{"int64_uint_max", map[string]PathAttr{"": PathInt64}, nil, `this == 18446744073709551615u`,
			"outside the domain of the int64 value"},
		{"in_list", map[string]PathAttr{"": PathInt32}, nil, `this in [1, 2, 5000000000]`,
			"outside the domain of the int32 value"},
		{"float_overflow", map[string]PathAttr{"": PathFloat}, nil, `this < 1e40`,
			"outside the finite range of the `float` field's Lean type Float32"},
		{"message_rule_leaf", map[string]PathAttr{"stock": PathInt32}, fields,
			`this.stock < 3000000000`, "outside the domain of the int32 value"},
		{"message_rule_uint", map[string]PathAttr{"batch": PathUInt32}, fields,
			`this.batch == -5`, "negative literal -5"},
		// Map-selection leaves are typed too (`m.k` on a map<string, int32>).
		{"map_value_leaf", map[string]PathAttr{"": PathMapSelect, "counts": PathInt32}, nil,
			`this.counts > 3000000000`, "outside the domain of the int32 value"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			_, err := Translate(tt.cel, Options{ThisFields: tt.this, PathAttrs: tt.attrs})
			if err == nil {
				t.Fatalf("Translate(%q) succeeded, want error containing %q", tt.cel, tt.frag)
			}
			if !strings.Contains(err.Error(), tt.frag) {
				t.Errorf("Translate(%q) error = %v, want substring %q", tt.cel, err, tt.frag)
			}
		})
	}

	// Without descriptor knowledge nothing is rejected (the standalone
	// translator has no field type to check against).
	if _, err := Translate(`this < 3000000000`, Options{}); err != nil {
		t.Errorf("untyped translation should not range-check: %v", err)
	}
	// In-domain literals stay accepted, including at the boundaries.
	for _, ok := range []string{`this >= -2147483648`, `this <= 2147483647`, `this in [0, 1]`} {
		if _, err := Translate(ok, Options{PathAttrs: map[string]PathAttr{"": PathInt32}}); err != nil {
			t.Errorf("Translate(%q): unexpected error %v", ok, err)
		}
	}
}

// Literal regex patterns must be inside the Lean engine's subset and are
// reported for #guard emission.
func TestRegexGate(t *testing.T) {
	got, err := Translate(`this.matches('^a+$') && this.matches('^a+$') || this.matches('b')`, Options{})
	if err != nil {
		t.Fatal(err)
	}
	if want := []string{"^a+$", "b"}; len(got.Regexes) != 2 || got.Regexes[0] != want[0] || got.Regexes[1] != want[1] {
		t.Errorf("Regexes = %v, want %v", got.Regexes, want)
	}
	if _, err := Translate(`this.matches('(?i)abc')`, Options{}); err == nil ||
		!strings.Contains(err.Error(), "outside the supported RE2 subset") {
		t.Errorf("unsupported pattern: err = %v, want subset error", err)
	}
	res, err := Translate(`this.matches(this)`, Options{})
	if err != nil {
		t.Fatal(err)
	}
	if len(res.Warnings) != 1 || !strings.Contains(res.Warnings[0], "non-literal regex") {
		t.Errorf("non-literal pattern warnings = %v, want non-literal warning", res.Warnings)
	}
}

func TestTranslateErrors(t *testing.T) {
	tests := []struct {
		name string
		cel  string
		frag string // expected substring of the error
	}{
		{"unknown_function", `this.fooBar(1)`, `unsupported CEL function "fooBar"`},
		{"struct_literal", `Msg{a: 1} == this`, "message literal"},
		{"timestamp_accessor", `this.getSeconds() > 0`, "getSeconds"},
		{"parse_error", `this ==`, "Syntax error"},
		{"has_non_select", `has(this)`, "field selection"},
		{"macro_var", `this.all(a + 1, true)`, "iteration variable"},
		{"bad_regex", `this.matches('\\bword')`, "outside the supported RE2 subset"},
		{"const_overflow", `this == 9223372036854775807 + 1`, "overflows int64"},
		{"const_underflow", `this == 1u - 2u`, "overflows uint64"},
		{"index_in_filter_body", `this.filter(v, this[v] > 0).size() == 0`, "inside a filter() body"},
		{"index_in_negated_all", `!this.all(v, this[0] < v)`, "under a negation"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			_, err := Translate(tt.cel, Options{})
			if err == nil {
				t.Fatalf("Translate(%q) succeeded, want error containing %q", tt.cel, tt.frag)
			}
			if !strings.Contains(err.Error(), tt.frag) {
				t.Errorf("Translate(%q) error = %v, want substring %q", tt.cel, err, tt.frag)
			}
		})
	}
}
