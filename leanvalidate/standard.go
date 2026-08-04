package leanvalidate

// Lowering of protovalidate's standard rule vocabulary (string.min_len,
// int32.gt, repeated.items, ...) onto the same refinement machinery as custom
// CEL rules: most rules synthesize a CEL expression over `this` (translated
// per rendering context by celtolean), while enum rules and quantified
// element rules assemble Lean directly.

import (
	"fmt"
	"regexp"
	"sort"
	"strconv"
	"strings"

	validatepb "buf.build/gen/go/bufbuild/protovalidate/protocolbuffers/go/buf/validate"
	"google.golang.org/protobuf/compiler/protogen"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/types/descriptorpb"
	"google.golang.org/protobuf/types/known/durationpb"
	"google.golang.org/protobuf/types/known/timestamppb"

	"github.com/petersonbill64/protovalidate-lean/celtolean"
)

// loweredRule is one check on a field value: a CEL expression over `this`
// (custom rules and most standard rules) or a directly-assembled Lean
// proposition (enum rules, quantified element rules).
type loweredRule struct {
	id      string
	message string
	cel     string
	// direct renders the Lean proposition for a subject expression (an
	// atomic Lean term for the constrained value); used when cel is empty.
	direct func(fg *fileGen, subject string) (text string, prec int, err error)
	// idents are identifiers occurring in any embedded CEL (binder hygiene).
	idents map[string]bool
	// pathAttrs carries proto-descriptor knowledge (enum integer views, map
	// selection) for the rule's `this` paths; see pathattrs.go.
	pathAttrs map[string]celtolean.PathAttr
}

// fieldRuleSet is everything protovalidate says about one field.
type fieldRuleSet struct {
	rules []loweredRule
	// required: explicit-presence fields are unwrapped (Option removed);
	// implicit-presence fields gain a non-zero rule.
	required bool
	// ignoreZero (IGNORE_IF_ZERO_VALUE): all rules are skipped when the value
	// is its zero value, encoded as a zero-escape disjunct.
	ignoreZero bool
}

func (s fieldRuleSet) empty() bool { return len(s.rules) == 0 && !s.required }

// render evaluates a lowered rule against a subject expression.
func (fg *fileGen) renderRule(r loweredRule, subject string) (string, int, error) {
	if r.cel != "" {
		res, err := fg.translate(r.cel, celtolean.Options{Var: subject, PathAttrs: r.pathAttrs})
		if err != nil {
			return "", 0, fmt.Errorf("rule %q: %w", r.id, err)
		}
		return res.Lean, res.Prec, nil
	}
	return r.direct(fg, subject)
}

func celRule(id, message, cel string) (loweredRule, error) {
	idents, err := celtolean.Idents(cel)
	if err != nil {
		return loweredRule{}, fmt.Errorf("rule %q: invalid CEL %q: %w", id, cel, err)
	}
	return loweredRule{id: id, message: message, cel: cel, idents: idents}, nil
}

func mustCelRules(out *[]loweredRule, errp *error, id, message, cel string) {
	if *errp != nil {
		return
	}
	r, err := celRule(id, message, cel)
	if err != nil {
		*errp = err
		return
	}
	*out = append(*out, r)
}

// lowerFieldRules combines standard rules (protovalidate order) and custom
// CEL rules for one field.
func lowerFieldRules(fd *protogen.Field) (fieldRuleSet, error) {
	opts, ok := fd.Desc.Options().(*descriptorpb.FieldOptions)
	if !ok || opts == nil {
		return fieldRuleSet{}, nil
	}
	fr, ok := proto.GetExtension(opts, validatepb.E_Field).(*validatepb.FieldRules)
	if !ok || fr == nil {
		return fieldRuleSet{}, nil
	}
	if fr.GetIgnore() == validatepb.Ignore_IGNORE_ALWAYS {
		return fieldRuleSet{}, nil
	}
	set := fieldRuleSet{
		required:   fr.GetRequired(),
		ignoreZero: fr.GetIgnore() == validatepb.Ignore_IGNORE_IF_ZERO_VALUE,
	}
	std, err := lowerStandard(fd, fr)
	if err != nil {
		return set, err
	}
	set.rules = std
	for _, r := range withBareExpressions(fr.GetCel(), fr.GetCelExpression()) {
		lr, err := celRule(r.GetId(), r.GetMessage(), r.GetExpression())
		if err != nil {
			return set, err
		}
		if lr.pathAttrs, err = pathAttrsForField(fd.Desc, r.GetExpression()); err != nil {
			return set, fmt.Errorf("rule %q: %w", r.GetId(), err)
		}
		set.rules = append(set.rules, lr)
	}
	return set, nil
}

func lowerStandard(fd *protogen.Field, fr *validatepb.FieldRules) ([]loweredRule, error) {
	switch {
	case fr.GetString_() != nil:
		return lowerString(fr.GetString_())
	case fr.GetBytes() != nil:
		return lowerBytes(fr.GetBytes())
	case fr.GetBool() != nil:
		return lowerBool(fr.GetBool())
	case fr.GetEnum() != nil:
		return lowerEnum(fd, fr.GetEnum())
	case fr.GetRepeated() != nil:
		return lowerRepeated(fd, fr.GetRepeated())
	case fr.GetMap() != nil:
		return lowerMap(fd, fr.GetMap())
	case fr.GetFloat() != nil:
		r := fr.GetFloat()
		return lowerNumeric("float", floatLit(float64(r.GetConst())), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), floatLit(float64(pick32(r.GetLt(), r.GetLte(), r.HasLt()))),
			gtOf(r.HasGt(), r.HasGte()), floatLit(float64(pick32(r.GetGt(), r.GetGte(), r.HasGt()))),
			cmpFloat(float64(pick32(r.GetLt(), r.GetLte(), r.HasLt())), float64(pick32(r.GetGt(), r.GetGte(), r.HasGt()))),
			floatList32(r.GetIn()), floatList32(r.GetNotIn()), r.GetFinite())
	case fr.GetDouble() != nil:
		r := fr.GetDouble()
		return lowerNumeric("double", floatLit(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), floatLit(pick64(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), floatLit(pick64(r.GetGt(), r.GetGte(), r.HasGt())),
			cmpFloat(pick64(r.GetLt(), r.GetLte(), r.HasLt()), pick64(r.GetGt(), r.GetGte(), r.HasGt())),
			floatList64(r.GetIn()), floatList64(r.GetNotIn()), r.GetFinite())
	case fr.GetInt32() != nil:
		r := fr.GetInt32()
		return lowerIntRules("int32", int64(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), int64(pickI32(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), int64(pickI32(r.GetGt(), r.GetGte(), r.HasGt())),
			intList32(r.GetIn()), intList32(r.GetNotIn()))
	case fr.GetInt64() != nil:
		r := fr.GetInt64()
		return lowerIntRules("int64", r.GetConst(), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), pickI64(r.GetLt(), r.GetLte(), r.HasLt()),
			gtOf(r.HasGt(), r.HasGte()), pickI64(r.GetGt(), r.GetGte(), r.HasGt()),
			intList64(r.GetIn()), intList64(r.GetNotIn()))
	case fr.GetSint32() != nil:
		r := fr.GetSint32()
		return lowerIntRules("sint32", int64(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), int64(pickI32(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), int64(pickI32(r.GetGt(), r.GetGte(), r.HasGt())),
			intList32(r.GetIn()), intList32(r.GetNotIn()))
	case fr.GetSint64() != nil:
		r := fr.GetSint64()
		return lowerIntRules("sint64", r.GetConst(), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), pickI64(r.GetLt(), r.GetLte(), r.HasLt()),
			gtOf(r.HasGt(), r.HasGte()), pickI64(r.GetGt(), r.GetGte(), r.HasGt()),
			intList64(r.GetIn()), intList64(r.GetNotIn()))
	case fr.GetSfixed32() != nil:
		r := fr.GetSfixed32()
		return lowerIntRules("sfixed32", int64(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), int64(pickI32(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), int64(pickI32(r.GetGt(), r.GetGte(), r.HasGt())),
			intList32(r.GetIn()), intList32(r.GetNotIn()))
	case fr.GetSfixed64() != nil:
		r := fr.GetSfixed64()
		return lowerIntRules("sfixed64", r.GetConst(), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), pickI64(r.GetLt(), r.GetLte(), r.HasLt()),
			gtOf(r.HasGt(), r.HasGte()), pickI64(r.GetGt(), r.GetGte(), r.HasGt()),
			intList64(r.GetIn()), intList64(r.GetNotIn()))
	case fr.GetUint32() != nil:
		r := fr.GetUint32()
		return lowerUintRules("uint32", uint64(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), uint64(pickU32(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), uint64(pickU32(r.GetGt(), r.GetGte(), r.HasGt())),
			uintList32(r.GetIn()), uintList32(r.GetNotIn()))
	case fr.GetUint64() != nil:
		r := fr.GetUint64()
		return lowerUintRules("uint64", r.GetConst(), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), pickU64(r.GetLt(), r.GetLte(), r.HasLt()),
			gtOf(r.HasGt(), r.HasGte()), pickU64(r.GetGt(), r.GetGte(), r.HasGt()),
			uintList64(r.GetIn()), uintList64(r.GetNotIn()))
	case fr.GetFixed32() != nil:
		r := fr.GetFixed32()
		return lowerUintRules("fixed32", uint64(r.GetConst()), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), uint64(pickU32(r.GetLt(), r.GetLte(), r.HasLt())),
			gtOf(r.HasGt(), r.HasGte()), uint64(pickU32(r.GetGt(), r.GetGte(), r.HasGt())),
			uintList32(r.GetIn()), uintList32(r.GetNotIn()))
	case fr.GetFixed64() != nil:
		r := fr.GetFixed64()
		return lowerUintRules("fixed64", r.GetConst(), r.HasConst(),
			ltOf(r.HasLt(), r.HasLte()), pickU64(r.GetLt(), r.GetLte(), r.HasLt()),
			gtOf(r.HasGt(), r.HasGte()), pickU64(r.GetGt(), r.GetGte(), r.HasGt()),
			uintList64(r.GetIn()), uintList64(r.GetNotIn()))
	case fr.GetTimestamp() != nil:
		return lowerTimestamp(fr.GetTimestamp())
	case fr.GetDuration() != nil:
		return lowerDuration(fr.GetDuration())
	case fr.GetAny() != nil, fr.GetFieldMask() != nil:
		return nil, fmt.Errorf("any/field_mask standard rules are not supported")
	}
	return nil, nil
}

// -- timestamp / duration rules (well-known types) --------------------------------

func leanI64Arg(v int64) string {
	if v < 0 {
		return "(" + strconv.FormatInt(v, 10) + ")"
	}
	return strconv.FormatInt(v, 10)
}

func tsMk(t *timestamppb.Timestamp) string {
	return "Cel.Timestamp.mk " + leanI64Arg(t.GetSeconds()) + " " + leanI64Arg(int64(t.GetNanos()))
}

func durMk(d *durationpb.Duration) string {
	return "Cel.Duration.mk " + leanI64Arg(d.GetSeconds()) + " " + leanI64Arg(int64(d.GetNanos()))
}

// cmpSecNanos compares two (seconds, nanos) pairs lexicographically (valid
// for both protobuf conventions: timestamps normalize nanos non-negative,
// durations keep signs aligned).
func cmpSecNanos(s1 int64, n1 int32, s2 int64, n2 int32) int {
	switch {
	case s1 < s2 || (s1 == s2 && n1 < n2):
		return -1
	case s1 == s2 && n1 == n2:
		return 0
	default:
		return 1
	}
}

func directCmp(out *[]loweredRule, id, message, symbol, rhs string) {
	*out = append(*out, loweredRule{id: id, message: message,
		direct: func(_ *fileGen, subject string) (string, int, error) {
			return subject + " " + symbol + " " + rhs, 50, nil
		}})
}

// lowerTimeCmp implements the shared const/lt/lte/gt/gte semantics for
// timestamp/duration rules over a rendered constant, including the inverted
// range disjunction.
func lowerTimeCmp(prefix string, hasConst bool, constS string,
	ltK int, ltS string, gtK int, gtS string, cmpLtGt int) []loweredRule {
	var out []loweredRule
	if hasConst {
		out = append(out, loweredRule{id: prefix + ".const", message: "value must equal " + constS,
			direct: func(_ *fileGen, subject string) (string, int, error) {
				return subject + " == " + constS, 50, nil
			}})
	}
	ltOp := map[int]string{1: "<", 2: "≤"}
	gtOp := map[int]string{1: ">", 2: "≥"}
	switch {
	case ltK != 0 && gtK != 0 && cmpLtGt > 0:
		gs, ls, go_, lo := gtS, ltS, gtOp[gtK], ltOp[ltK]
		out = append(out, loweredRule{id: prefix + ".gt_lt",
			message: fmt.Sprintf("value must be %s %s and %s %s", go_, gs, lo, ls),
			direct: func(_ *fileGen, subject string) (string, int, error) {
				return subject + " " + go_ + " " + gs + " ∧ " + subject + " " + lo + " " + ls, 35, nil
			}})
	case ltK != 0 && gtK != 0:
		gs, ls, go_, lo := gtS, ltS, gtOp[gtK], ltOp[ltK]
		out = append(out, loweredRule{id: prefix + ".gt_lt_exclusive",
			message: fmt.Sprintf("value must be %s %s or %s %s", lo, ls, go_, gs),
			direct: func(_ *fileGen, subject string) (string, int, error) {
				return subject + " " + lo + " " + ls + " ∨ " + subject + " " + go_ + " " + gs, 30, nil
			}})
	case ltK == 1:
		directCmp(&out, prefix+".lt", "value must be < "+ltS, "<", ltS)
	case ltK == 2:
		directCmp(&out, prefix+".lte", "value must be ≤ "+ltS, "≤", ltS)
	case gtK == 1:
		directCmp(&out, prefix+".gt", "value must be > "+gtS, ">", gtS)
	case gtK == 2:
		directCmp(&out, prefix+".gte", "value must be ≥ "+gtS, "≥", gtS)
	}
	return out
}

func lowerTimestamp(r *validatepb.TimestampRules) ([]loweredRule, error) {
	if r.GetLtNow() || r.GetGtNow() || r.HasWithin() {
		return nil, fmt.Errorf("timestamp lt_now/gt_now/within are not supported: " +
			"Cel.now is opaque (no runtime value); keep evaluation-time constraints outside the refinement")
	}
	ltK, ltV := 0, (*timestamppb.Timestamp)(nil)
	if r.HasLt() {
		ltK, ltV = 1, r.GetLt()
	} else if r.HasLte() {
		ltK, ltV = 2, r.GetLte()
	}
	gtK, gtV := 0, (*timestamppb.Timestamp)(nil)
	if r.HasGt() {
		gtK, gtV = 1, r.GetGt()
	} else if r.HasGte() {
		gtK, gtV = 2, r.GetGte()
	}
	cmp := 0
	if ltK != 0 && gtK != 0 {
		cmp = cmpSecNanos(ltV.GetSeconds(), ltV.GetNanos(), gtV.GetSeconds(), gtV.GetNanos())
	}
	ltS, gtS := "", ""
	if ltV != nil {
		ltS = tsMk(ltV)
	}
	if gtV != nil {
		gtS = tsMk(gtV)
	}
	return lowerTimeCmp("timestamp", r.HasConst(), tsMk(r.GetConst()), ltK, ltS, gtK, gtS, cmp), nil
}

func lowerDuration(r *validatepb.DurationRules) ([]loweredRule, error) {
	ltK, ltV := 0, (*durationpb.Duration)(nil)
	if r.HasLt() {
		ltK, ltV = 1, r.GetLt()
	} else if r.HasLte() {
		ltK, ltV = 2, r.GetLte()
	}
	gtK, gtV := 0, (*durationpb.Duration)(nil)
	if r.HasGt() {
		gtK, gtV = 1, r.GetGt()
	} else if r.HasGte() {
		gtK, gtV = 2, r.GetGte()
	}
	cmp := 0
	if ltK != 0 && gtK != 0 {
		cmp = cmpSecNanos(ltV.GetSeconds(), ltV.GetNanos(), gtV.GetSeconds(), gtV.GetNanos())
	}
	ltS, gtS := "", ""
	if ltV != nil {
		ltS = durMk(ltV)
	}
	if gtV != nil {
		gtS = durMk(gtV)
	}
	out := lowerTimeCmp("duration", r.HasConst(), durMk(r.GetConst()), ltK, ltS, gtK, gtS, cmp)
	eqList := func(vals []*durationpb.Duration) func(string) (string, int) {
		return func(subject string) (string, int) {
			parts := make([]string, len(vals))
			for i, v := range vals {
				parts[i] = subject + " == " + durMk(v)
			}
			if len(parts) == 1 {
				return parts[0], 50
			}
			return strings.Join(parts, " ∨ "), 30
		}
	}
	if in := r.GetIn(); len(in) > 0 {
		render := eqList(in)
		out = append(out, loweredRule{id: "duration.in", message: "value must be in the allowed list",
			direct: func(_ *fileGen, subject string) (string, int, error) {
				t, p := render(subject)
				return t, p, nil
			}})
	}
	if notIn := r.GetNotIn(); len(notIn) > 0 {
		render := eqList(notIn)
		out = append(out, loweredRule{id: "duration.not_in", message: "value must not be in the disallowed list",
			direct: func(_ *fileGen, subject string) (string, int, error) {
				t, _ := render(subject)
				return "¬(" + t + ")", 40, nil
			}})
	}
	return out, nil
}

// -- literal formatting -------------------------------------------------------

func intLit(v int64) string   { return strconv.FormatInt(v, 10) }
func uintLit(v uint64) string { return strconv.FormatUint(v, 10) + "u" }

func floatLit(f float64) string {
	s := strconv.FormatFloat(f, 'g', -1, 64)
	if !strings.ContainsAny(s, ".e") {
		s += ".0"
	}
	return s
}

// celQuote renders a CEL double-quoted string literal.
func celQuote(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString(`\"`)
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\t':
			b.WriteString(`\t`)
		case '\r':
			b.WriteString(`\r`)
		default:
			if r < 0x20 {
				fmt.Fprintf(&b, `\x%02x`, r)
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

// celQuoteBytes renders a CEL bytes literal.
func celQuoteBytes(data []byte) string {
	var b strings.Builder
	b.WriteString(`b"`)
	for _, x := range data {
		switch {
		case x == '"':
			b.WriteString(`\"`)
		case x == '\\':
			b.WriteString(`\\`)
		case x >= 0x20 && x < 0x7f:
			b.WriteByte(x)
		default:
			fmt.Fprintf(&b, `\x%02x`, x)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func intList32(vs []int32) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = intLit(int64(v))
	}
	return out
}

func intList64(vs []int64) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = intLit(v)
	}
	return out
}

func uintList32(vs []uint32) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = uintLit(uint64(v))
	}
	return out
}

func uintList64(vs []uint64) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = uintLit(v)
	}
	return out
}

func floatList32(vs []float32) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = floatLit(float64(v))
	}
	return out
}

func floatList64(vs []float64) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = floatLit(v)
	}
	return out
}

func stringList(vs []string) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = celQuote(v)
	}
	return out
}

func bytesList(vs [][]byte) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = celQuoteBytes(v)
	}
	return out
}

// -- oneof pickers ------------------------------------------------------------

func ltOf(hasLt, hasLte bool) int {
	if hasLt {
		return 1
	}
	if hasLte {
		return 2
	}
	return 0
}

func gtOf(hasGt, hasGte bool) int { return ltOf(hasGt, hasGte) }

func pick32(lt, lte float32, isLt bool) float32 {
	if isLt {
		return lt
	}
	return lte
}

func pick64(lt, lte float64, isLt bool) float64 {
	if isLt {
		return lt
	}
	return lte
}

func pickI32(lt, lte int32, isLt bool) int32 {
	if isLt {
		return lt
	}
	return lte
}

func pickI64(lt, lte int64, isLt bool) int64 {
	if isLt {
		return lt
	}
	return lte
}

func pickU32(lt, lte uint32, isLt bool) uint32 {
	if isLt {
		return lt
	}
	return lte
}

func pickU64(lt, lte uint64, isLt bool) uint64 {
	if isLt {
		return lt
	}
	return lte
}

func cmpFloat(lt, gt float64) int {
	switch {
	case lt > gt:
		return 1
	case lt < gt:
		return -1
	default:
		return 0
	}
}

// -- numeric rules --------------------------------------------------------------

func lowerIntRules(prefix string, constV int64, hasConst bool, ltK int, ltV int64,
	gtK int, gtV int64, in, notIn []string) ([]loweredRule, error) {
	return lowerNumeric(prefix, intLit(constV), hasConst, ltK, intLit(ltV), gtK, intLit(gtV),
		cmpFloat(float64(ltV), float64(gtV)), in, notIn, false)
}

func lowerUintRules(prefix string, constV uint64, hasConst bool, ltK int, ltV uint64,
	gtK int, gtV uint64, in, notIn []string) ([]loweredRule, error) {
	cmp := 0
	if ltV > gtV {
		cmp = 1
	} else if ltV < gtV {
		cmp = -1
	}
	return lowerNumeric(prefix, uintLit(constV), hasConst, ltK, uintLit(ltV), gtK, uintLit(gtV),
		cmp, in, notIn, false)
}

// lowerNumeric implements protovalidate's shared numeric semantics, including
// the inverted-range disjunction when lt ≤ gt.
func lowerNumeric(prefix, constS string, hasConst bool, ltK int, ltS string,
	gtK int, gtS string, cmpLtGt int, in, notIn []string, finite bool) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	add := func(id, message, cel string) { mustCelRules(&out, &err, id, message, cel) }

	if hasConst {
		add(prefix+".const", "value must equal "+constS, "this == "+constS)
	}
	ltOp := map[int]string{1: "<", 2: "<="}
	gtOp := map[int]string{1: ">", 2: ">="}
	switch {
	case ltK != 0 && gtK != 0 && cmpLtGt > 0:
		add(prefix+".gt_lt", fmt.Sprintf("value must be %s %s and %s %s", gtOp[gtK], gtS, ltOp[ltK], ltS),
			fmt.Sprintf("this %s %s && this %s %s", gtOp[gtK], gtS, ltOp[ltK], ltS))
	case ltK != 0 && gtK != 0:
		add(prefix+".gt_lt_exclusive", fmt.Sprintf("value must be %s %s or %s %s", ltOp[ltK], ltS, gtOp[gtK], gtS),
			fmt.Sprintf("this %s %s || this %s %s", ltOp[ltK], ltS, gtOp[gtK], gtS))
	case ltK != 0:
		id := ".lt"
		if ltK == 2 {
			id = ".lte"
		}
		add(prefix+id, fmt.Sprintf("value must be %s %s", ltOp[ltK], ltS),
			fmt.Sprintf("this %s %s", ltOp[ltK], ltS))
	case gtK != 0:
		id := ".gt"
		if gtK == 2 {
			id = ".gte"
		}
		add(prefix+id, fmt.Sprintf("value must be %s %s", gtOp[gtK], gtS),
			fmt.Sprintf("this %s %s", gtOp[gtK], gtS))
	}
	if len(in) > 0 {
		add(prefix+".in", "value must be in the allowed list", "this in ["+strings.Join(in, ", ")+"]")
	}
	if len(notIn) > 0 {
		add(prefix+".not_in", "value must not be in the disallowed list", "!(this in ["+strings.Join(notIn, ", ")+"])")
	}
	if finite {
		add(prefix+".finite", "value must be finite", "!this.isNan() && !this.isInf()")
	}
	return out, err
}

// -- string rules ---------------------------------------------------------------

func lowerString(r *validatepb.StringRules) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	add := func(id, message, cel string) { mustCelRules(&out, &err, id, message, cel) }

	if r.HasConst() {
		add("string.const", "value must equal "+celQuote(r.GetConst()), "this == "+celQuote(r.GetConst()))
	}
	if r.HasLen() {
		add("string.len", fmt.Sprintf("value length must be %d characters", r.GetLen()),
			fmt.Sprintf("this.size() == %d", r.GetLen()))
	}
	if r.HasMinLen() {
		add("string.min_len", fmt.Sprintf("value length must be at least %d characters", r.GetMinLen()),
			fmt.Sprintf("this.size() >= %d", r.GetMinLen()))
	}
	if r.HasMaxLen() {
		add("string.max_len", fmt.Sprintf("value length must be at most %d characters", r.GetMaxLen()),
			fmt.Sprintf("this.size() <= %d", r.GetMaxLen()))
	}
	if r.HasLenBytes() {
		add("string.len_bytes", fmt.Sprintf("value length must be %d bytes", r.GetLenBytes()),
			fmt.Sprintf("bytes(this).size() == %d", r.GetLenBytes()))
	}
	if r.HasMinBytes() {
		add("string.min_bytes", fmt.Sprintf("value length must be at least %d bytes", r.GetMinBytes()),
			fmt.Sprintf("bytes(this).size() >= %d", r.GetMinBytes()))
	}
	if r.HasMaxBytes() {
		add("string.max_bytes", fmt.Sprintf("value length must be at most %d bytes", r.GetMaxBytes()),
			fmt.Sprintf("bytes(this).size() <= %d", r.GetMaxBytes()))
	}
	if r.HasPattern() {
		if _, rerr := regexp.Compile(r.GetPattern()); rerr != nil {
			return nil, fmt.Errorf("string.pattern: invalid RE2 pattern %q: %v", r.GetPattern(), rerr)
		}
		add("string.pattern", "value must match pattern "+celQuote(r.GetPattern()),
			"this.matches("+celQuote(r.GetPattern())+")")
	}
	if r.HasPrefix() {
		add("string.prefix", "value must start with "+celQuote(r.GetPrefix()),
			"this.startsWith("+celQuote(r.GetPrefix())+")")
	}
	if r.HasSuffix() {
		add("string.suffix", "value must end with "+celQuote(r.GetSuffix()),
			"this.endsWith("+celQuote(r.GetSuffix())+")")
	}
	if r.HasContains() {
		add("string.contains", "value must contain "+celQuote(r.GetContains()),
			"this.contains("+celQuote(r.GetContains())+")")
	}
	if r.HasNotContains() {
		add("string.not_contains", "value must not contain "+celQuote(r.GetNotContains()),
			"!this.contains("+celQuote(r.GetNotContains())+")")
	}
	if in := r.GetIn(); len(in) > 0 {
		add("string.in", "value must be in the allowed list", "this in ["+strings.Join(stringList(in), ", ")+"]")
	}
	if notIn := r.GetNotIn(); len(notIn) > 0 {
		add("string.not_in", "value must not be in the disallowed list",
			"!(this in ["+strings.Join(stringList(notIn), ", ")+"])")
	}

	const uuidPattern = "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
	const tuuidPattern = "^[0-9a-fA-F]{32}$"
	switch wk := r.GetWellKnown().(type) {
	case nil:
	case *validatepb.StringRules_Email:
		if wk.Email {
			add("string.email", "value must be a valid email address", "this.isEmail()")
		}
	case *validatepb.StringRules_Hostname:
		if wk.Hostname {
			add("string.hostname", "value must be a valid hostname", "this.isHostname()")
		}
	case *validatepb.StringRules_Ip:
		if wk.Ip {
			add("string.ip", "value must be a valid IP address", "this.isIp()")
		}
	case *validatepb.StringRules_Ipv4:
		if wk.Ipv4 {
			add("string.ipv4", "value must be a valid IPv4 address", "this.isIp(4)")
		}
	case *validatepb.StringRules_Ipv6:
		if wk.Ipv6 {
			add("string.ipv6", "value must be a valid IPv6 address", "this.isIp(6)")
		}
	case *validatepb.StringRules_Uri:
		if wk.Uri {
			add("string.uri", "value must be a valid URI", "this.isUri()")
		}
	case *validatepb.StringRules_UriRef:
		if wk.UriRef {
			add("string.uri_ref", "value must be a valid URI reference", "this.isUriRef()")
		}
	case *validatepb.StringRules_Address:
		if wk.Address {
			add("string.address", "value must be a valid hostname or IP address",
				"this.isHostname() || this.isIp()")
		}
	case *validatepb.StringRules_Uuid:
		if wk.Uuid {
			add("string.uuid", "value must be a valid UUID", "this.matches("+celQuote(uuidPattern)+")")
		}
	case *validatepb.StringRules_Tuuid:
		if wk.Tuuid {
			add("string.tuuid", "value must be a valid trimmed UUID", "this.matches("+celQuote(tuuidPattern)+")")
		}
	case *validatepb.StringRules_IpWithPrefixlen:
		if wk.IpWithPrefixlen {
			add("string.ip_with_prefixlen", "value must be a valid IP with prefix length", "this.isIpPrefix()")
		}
	case *validatepb.StringRules_Ipv4WithPrefixlen:
		if wk.Ipv4WithPrefixlen {
			add("string.ipv4_with_prefixlen", "value must be a valid IPv4 with prefix length", "this.isIpPrefix(4)")
		}
	case *validatepb.StringRules_Ipv6WithPrefixlen:
		if wk.Ipv6WithPrefixlen {
			add("string.ipv6_with_prefixlen", "value must be a valid IPv6 with prefix length", "this.isIpPrefix(6)")
		}
	case *validatepb.StringRules_IpPrefix:
		if wk.IpPrefix {
			add("string.ip_prefix", "value must be a valid IP prefix", "this.isIpPrefix(true)")
		}
	case *validatepb.StringRules_Ipv4Prefix:
		if wk.Ipv4Prefix {
			add("string.ipv4_prefix", "value must be a valid IPv4 prefix", "this.isIpPrefix(4, true)")
		}
	case *validatepb.StringRules_Ipv6Prefix:
		if wk.Ipv6Prefix {
			add("string.ipv6_prefix", "value must be a valid IPv6 prefix", "this.isIpPrefix(6, true)")
		}
	case *validatepb.StringRules_HostAndPort:
		if wk.HostAndPort {
			add("string.host_and_port", "value must be a valid host and port", "this.isHostAndPort(true)")
		}
	default:
		return nil, fmt.Errorf("unsupported string well-known rule %T", wk)
	}
	return out, err
}

// -- bytes rules -----------------------------------------------------------------

func lowerBytes(r *validatepb.BytesRules) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	add := func(id, message, cel string) { mustCelRules(&out, &err, id, message, cel) }

	if r.HasConst() {
		add("bytes.const", "value must equal the expected bytes", "this == "+celQuoteBytes(r.GetConst()))
	}
	if r.HasLen() {
		add("bytes.len", fmt.Sprintf("value length must be %d bytes", r.GetLen()),
			fmt.Sprintf("this.size() == %d", r.GetLen()))
	}
	if r.HasMinLen() {
		add("bytes.min_len", fmt.Sprintf("value length must be at least %d bytes", r.GetMinLen()),
			fmt.Sprintf("this.size() >= %d", r.GetMinLen()))
	}
	if r.HasMaxLen() {
		add("bytes.max_len", fmt.Sprintf("value length must be at most %d bytes", r.GetMaxLen()),
			fmt.Sprintf("this.size() <= %d", r.GetMaxLen()))
	}
	if r.HasPattern() {
		return nil, fmt.Errorf("bytes.pattern is not supported")
	}
	if r.HasPrefix() {
		add("bytes.prefix", "value must start with the expected bytes",
			"this.startsWith("+celQuoteBytes(r.GetPrefix())+")")
	}
	if r.HasSuffix() {
		add("bytes.suffix", "value must end with the expected bytes",
			"this.endsWith("+celQuoteBytes(r.GetSuffix())+")")
	}
	if r.HasContains() {
		add("bytes.contains", "value must contain the expected bytes",
			"this.contains("+celQuoteBytes(r.GetContains())+")")
	}
	if in := r.GetIn(); len(in) > 0 {
		add("bytes.in", "value must be in the allowed list", "this in ["+strings.Join(bytesList(in), ", ")+"]")
	}
	if notIn := r.GetNotIn(); len(notIn) > 0 {
		add("bytes.not_in", "value must not be in the disallowed list",
			"!(this in ["+strings.Join(bytesList(notIn), ", ")+"])")
	}
	if r.GetWellKnown() != nil {
		return nil, fmt.Errorf("bytes well-known rules (ip/ipv4/ipv6) are not supported")
	}
	return out, err
}

func lowerBool(r *validatepb.BoolRules) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	if r.HasConst() {
		mustCelRules(&out, &err, "bool.const", fmt.Sprintf("value must be %v", r.GetConst()),
			fmt.Sprintf("this == %v", r.GetConst()))
	}
	return out, err
}

// -- enum rules (direct Lean: enums are generated inductives) ---------------------

func enumCaseText(enum protoreflect.EnumDescriptor, number int32) string {
	if v := enum.Values().ByNumber(protoreflect.EnumNumber(number)); v != nil {
		return "." + celtolean.LeanIdent(string(v.Name()))
	}
	return fmt.Sprintf(".«Unknown.Value» %s", leanInt32Arg(number))
}

func leanInt32Arg(v int32) string {
	if v < 0 {
		return "(" + strconv.FormatInt(int64(v), 10) + ")"
	}
	return strconv.FormatInt(int64(v), 10)
}

func lowerEnum(fd *protogen.Field, r *validatepb.EnumRules) ([]loweredRule, error) {
	if fd.Enum == nil {
		return nil, fmt.Errorf("enum rules on non-enum field")
	}
	enum := fd.Enum.Desc
	var out []loweredRule
	direct := func(id, message string, render func(subject string) (string, int)) {
		out = append(out, loweredRule{id: id, message: message,
			direct: func(_ *fileGen, subject string) (string, int, error) {
				t, p := render(subject)
				return t, p, nil
			}})
	}
	if r.HasConst() {
		c := r.GetConst()
		direct("enum.const", "value must equal "+enumCaseText(enum, c), func(s string) (string, int) {
			return s + " == " + enumCaseText(enum, c), 50
		})
	}
	if r.GetDefinedOnly() {
		direct("enum.defined_only", "value must be a defined enum value", func(s string) (string, int) {
			return "¬(" + s + " matches .«Unknown.Value» _)", 40
		})
	}
	if in := r.GetIn(); len(in) > 0 {
		vals := append([]int32(nil), in...)
		direct("enum.in", "value must be in the allowed list", func(s string) (string, int) {
			parts := make([]string, len(vals))
			for i, v := range vals {
				parts[i] = s + " == " + enumCaseText(enum, v)
			}
			if len(parts) == 1 {
				return parts[0], 50
			}
			return strings.Join(parts, " ∨ "), 30
		})
	}
	if notIn := r.GetNotIn(); len(notIn) > 0 {
		vals := append([]int32(nil), notIn...)
		direct("enum.not_in", "value must not be in the disallowed list", func(s string) (string, int) {
			parts := make([]string, len(vals))
			for i, v := range vals {
				parts[i] = s + " == " + enumCaseText(enum, v)
			}
			return "¬(" + strings.Join(parts, " ∨ ") + ")", 40
		})
	}
	return out, nil
}

// -- repeated / map rules ----------------------------------------------------------

// quantified builds `∀ v ∈ <collection(subject)>, conj(inner rules on v)`.
func quantified(id, message string, inner []loweredRule, collection func(subject string) string) loweredRule {
	idents := map[string]bool{}
	for _, r := range inner {
		for k := range r.idents {
			idents[k] = true
		}
	}
	return loweredRule{
		id:      id,
		message: message,
		idents:  idents,
		direct: func(fg *fileGen, subject string) (string, int, error) {
			taken := map[string]bool{}
			for k := range idents {
				taken[k] = true
			}
			taken[strings.SplitN(subject, ".", 2)[0]] = true
			v := freshTaken("v", taken)
			parts := make([]string, 0, len(inner))
			for _, r := range inner {
				t, p, err := fg.renderRule(r, v)
				if err != nil {
					return "", 0, err
				}
				if len(inner) > 1 && p < precAndOperand {
					t = "(" + t + ")"
				}
				parts = append(parts, t)
			}
			return "∀ " + v + " ∈ " + collection(subject) + ", " + strings.Join(parts, " ∧ "), 5, nil
		},
	}
}

func innerIDs(rules []loweredRule) string {
	ids := make([]string, 0, len(rules))
	for _, r := range rules {
		ids = append(ids, r.id)
	}
	sort.Strings(ids)
	return strings.Join(ids, ", ")
}

func lowerRepeated(fd *protogen.Field, r *validatepb.RepeatedRules) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	add := func(id, message, cel string) { mustCelRules(&out, &err, id, message, cel) }

	if r.HasMinItems() {
		add("repeated.min_items", fmt.Sprintf("list must have at least %d items", r.GetMinItems()),
			fmt.Sprintf("this.size() >= %d", r.GetMinItems()))
	}
	if r.HasMaxItems() {
		add("repeated.max_items", fmt.Sprintf("list must have at most %d items", r.GetMaxItems()),
			fmt.Sprintf("this.size() <= %d", r.GetMaxItems()))
	}
	if r.GetUnique() {
		add("repeated.unique", "list items must be unique", "this.unique()")
	}
	if items := r.GetItems(); items != nil {
		if fd.Desc.Kind() == protoreflect.MessageKind {
			return nil, fmt.Errorf("repeated.items rules on message elements are not supported " +
				"(element messages validate through their own rules)")
		}
		inner, ierr := lowerItemRules(fd, fd.Desc, items)
		if ierr != nil {
			return nil, fmt.Errorf("repeated.items: %w", ierr)
		}
		if len(inner) > 0 {
			out = append(out, quantified("repeated.items",
				"every item must satisfy: "+innerIDs(inner), inner,
				func(s string) string { return s }))
		}
	}
	return out, err
}

func lowerMap(fd *protogen.Field, r *validatepb.MapRules) ([]loweredRule, error) {
	var out []loweredRule
	var err error
	add := func(id, message, cel string) { mustCelRules(&out, &err, id, message, cel) }

	if r.HasMinPairs() {
		add("map.min_pairs", fmt.Sprintf("map must have at least %d entries", r.GetMinPairs()),
			fmt.Sprintf("this.size() >= %d", r.GetMinPairs()))
	}
	if r.HasMaxPairs() {
		add("map.max_pairs", fmt.Sprintf("map must have at most %d entries", r.GetMaxPairs()),
			fmt.Sprintf("this.size() <= %d", r.GetMaxPairs()))
	}
	if keys := r.GetKeys(); keys != nil {
		inner, ierr := lowerItemRules(fd, fd.Desc.MapKey(), keys)
		if ierr != nil {
			return nil, fmt.Errorf("map.keys: %w", ierr)
		}
		if len(inner) > 0 {
			out = append(out, quantified("map.keys",
				"every key must satisfy: "+innerIDs(inner), inner,
				func(s string) string { return s + ".keys" }))
		}
	}
	if values := r.GetValues(); values != nil {
		if fd.Desc.MapValue().Kind() == protoreflect.MessageKind {
			return nil, fmt.Errorf("map.values rules on message values are not supported")
		}
		inner, ierr := lowerItemRules(fd, fd.Desc.MapValue(), values)
		if ierr != nil {
			return nil, fmt.Errorf("map.values: %w", ierr)
		}
		if len(inner) > 0 {
			out = append(out, quantified("map.values",
				"every value must satisfy: "+innerIDs(inner), inner,
				func(s string) string { return s + ".values" }))
		}
	}
	return out, err
}

// lowerItemRules lowers the element-level FieldRules of repeated.items /
// map.keys / map.values (standard scalar rules plus custom CEL over the
// element as `this`).
func lowerItemRules(fd *protogen.Field, elem protoreflect.FieldDescriptor, fr *validatepb.FieldRules) ([]loweredRule, error) {
	if fr.GetRepeated() != nil || fr.GetMap() != nil {
		return nil, fmt.Errorf("nested container rules are not supported")
	}
	rules, err := lowerStandard(fd, fr)
	if err != nil {
		return nil, err
	}
	for _, r := range withBareExpressions(fr.GetCel(), fr.GetCelExpression()) {
		lr, cerr := celRule(r.GetId(), r.GetMessage(), r.GetExpression())
		if cerr != nil {
			return nil, cerr
		}
		lr.pathAttrs = pathAttrsForElement(elem)
		rules = append(rules, lr)
	}
	return rules, nil
}
