package celtolean

import (
	"fmt"
	"strconv"
	"strings"
	"time"

	"github.com/google/cel-go/common/ast"
	"github.com/google/cel-go/common/types"
)

// function translates CEL standard-library and protovalidate-extension calls.
// Macros (all/exists/exists_one/map/filter/has) arrive here as plain calls
// because the parser runs without macro expansion.
func (t *translator) function(c ast.CallExpr) (piece, error) {
	fn := c.FunctionName()
	args := c.Args()

	// Comprehension macros: receiver.all(v, p) etc.
	switch fn {
	case "all", "exists", "exists_one", "existsOne", "map", "filter":
		if c.IsMemberFunction() {
			return t.macro(fn, c)
		}
	}

	// has(m.field): field presence.
	if fn == "has" && !c.IsMemberFunction() && len(args) == 1 {
		if args[0].Kind() != ast.SelectKind {
			return piece{}, fmt.Errorf("has() requires a field selection argument")
		}
		sel := args[0].AsSelect()
		if t.thisFields != nil && sel.Operand().Kind() == ast.IdentKind && sel.Operand().AsIdent() == "this" {
			// Message-field mode: the caller supplied the field's exact
			// presence semantics (Option, non-default, non-empty, oneof case).
			ref, ok := t.thisFields[sel.FieldName()]
			if !ok {
				return piece{}, fmt.Errorf("message rule references unknown field %q", sel.FieldName())
			}
			if ref.Has == "" {
				return piece{}, fmt.Errorf("has(this.%s) is not supported for this field", sel.FieldName())
			}
			text := ref.Has
			if strings.ContainsRune(text, ' ') {
				text = "(" + text + ")"
			}
			return piece{text: text, prec: precAtom, kind: kBool}, nil
		}
		// Elsewhere the target is a base-message field or oneof member:
		// presence delegates to the generated has_<field> predicate, which
		// encodes CEL's per-category semantics (case test, isSome, non-empty,
		// non-default). Intermediate path hops default-traverse as usual.
		var op piece
		var err error
		if sel.Operand().Kind() == ast.SelectKind {
			op, err = t.selectExpr(sel.Operand().AsSelect(), true)
		} else {
			op, err = t.expr(sel.Operand())
		}
		if err != nil {
			return piece{}, err
		}
		text := op.at(precApp+1) + "." + leanIdent("has_"+sel.FieldName())
		return piece{text: text, prec: precAtom, kind: kBool}, nil
	}

	// Normalize receiver style: size(e) ≡ e.size(), matches(s, re) ≡ s.matches(re),
	// and the global unary functions (type conversions etc.) all take their
	// sole argument as the receiver.
	globalUnary := map[string]bool{
		"size": true, "int": true, "uint": true, "double": true, "bool": true,
		"string": true, "bytes": true, "dyn": true, "timestamp": true, "duration": true,
	}
	recvExpr, restArgs := ast.Expr(nil), args
	if c.IsMemberFunction() {
		recvExpr = c.Target()
	} else if (globalUnary[fn] && len(args) == 1) || (fn == "matches" && len(args) == 2) {
		recvExpr, restArgs = args[0], args[1:]
	}
	if recvExpr == nil {
		return piece{}, t.unsupported(fn)
	}
	recv, err := t.expr(recvExpr)
	if err != nil {
		return piece{}, err
	}
	rest := make([]piece, len(restArgs))
	for i, a := range restArgs {
		if rest[i], err = t.expr(a); err != nil {
			return piece{}, err
		}
	}

	proj := func(field string, k kind) piece {
		return piece{text: recv.at(precApp+1) + "." + field, prec: precAtom, kind: k}
	}
	dotApp := func(field string, k kind, args ...piece) piece {
		parts := []string{recv.at(precApp+1) + "." + field}
		for _, a := range args {
			parts = append(parts, a.at(precApp+1))
		}
		return piece{text: strings.Join(parts, " "), prec: precApp, kind: k}
	}
	celApp := func(name string, k kind, args ...piece) piece {
		parts := []string{"Cel." + name, recv.at(precApp + 1)}
		for _, a := range args {
			parts = append(parts, a.at(precApp+1))
		}
		return piece{text: strings.Join(parts, " "), prec: precApp, kind: k}
	}

	switch {
	// -- CEL standard library ------------------------------------------------
	case fn == "size" && len(rest) == 0:
		// Uniform `.size` via dot notation; Protovalidate.Cel supplies
		// String.size and List.size, core covers Array/ByteArray/HashMap.
		return proj("size", kTerm), nil
	case fn == "contains" && len(rest) == 1:
		// String.contains is Char-based in core, so route through the
		// Cel.Contains typeclass (substring/element/subslice per base type).
		return celApp("contains", kBool, rest[0]), nil
	case fn == "startsWith" && len(rest) == 1:
		return dotApp("startsWith", kBool, rest[0]), nil
	case fn == "endsWith" && len(rest) == 1:
		return dotApp("endsWith", kBool, rest[0]), nil
	case fn == "matches" && len(rest) == 1:
		// RE2 matching has no Lean-core counterpart (and `matches` is a
		// reserved Lean token); Cel.regexMatch is the designated shim.
		return celApp("regexMatch", kBool, rest[0]), nil

	// -- Type conversions ----------------------------------------------------
	case fn == "int" && len(rest) == 0:
		return celApp("toInt", kTerm), nil
	case fn == "uint" && len(rest) == 0:
		return celApp("toUInt", kTerm), nil
	case fn == "double" && len(rest) == 0:
		return celApp("toDouble", kTerm), nil
	case fn == "bool" && len(rest) == 0:
		return celApp("toBool", kBool), nil
	case fn == "string" && len(rest) == 0:
		return piece{text: "toString " + recv.at(precApp+1), prec: precApp, kind: kTerm}, nil
	case fn == "bytes" && len(rest) == 0:
		return proj("toUTF8", kTerm), nil
	case fn == "dyn" && len(rest) == 0:
		return recv, nil
	case fn == "timestamp" && len(rest) == 0:
		// Fold literal arguments at translation time so the proposition
		// carries a computable constant rather than a runtime parse.
		if lit, ok := stringLiteral(recvExpr); ok {
			return foldTimestamp(lit)
		}
		t.warn("non-literal timestamp() argument: Cel.timestamp parses at evaluation time (invalid strings map to the zero timestamp)")
		return celApp("timestamp", kTerm), nil
	case fn == "duration" && len(rest) == 0:
		if lit, ok := stringLiteral(recvExpr); ok {
			return foldDuration(lit)
		}
		t.warn("non-literal duration() argument: Cel.duration parses at evaluation time (invalid strings map to the zero duration)")
		return celApp("duration", kTerm), nil

	// -- protovalidate extensions ---------------------------------------------
	case fn == "unique" && len(rest) == 0:
		// Pairwise distinctness is a Prop in Lean; Protovalidate.Cel defines
		// Array.Nodup (with a Decidable instance) mirroring core List.Nodup.
		return proj("Nodup", kProp), nil
	case fn == "isNan" && len(rest) == 0:
		return proj("isNaN", kBool), nil
	case fn == "isInf" && len(rest) == 0:
		return proj("isInf", kBool), nil
	case fn == "isInf" && len(rest) == 1:
		return dotApp("isInfSign", kBool, rest[0]), nil
	case fn == "isEmail" && len(rest) == 0:
		return proj("isEmail", kBool), nil
	case fn == "isHostname" && len(rest) == 0:
		return proj("isHostname", kBool), nil
	case fn == "isUri" && len(rest) == 0:
		return proj("isUri", kBool), nil
	case fn == "isUriRef" && len(rest) == 0:
		return proj("isUriRef", kBool), nil
	case fn == "isIp" && len(rest) <= 1:
		return dotApp("isIp", kBool, rest...), nil
	case fn == "isIpPrefix" && len(rest) <= 2:
		if len(rest) == 1 && rest[0].kind == kBool {
			// Single-bool overload isIpPrefix(strict); version stays default.
			named := piece{text: "(strict := " + rest[0].text + ")", prec: precAtom, kind: kBool}
			return dotApp("isIpPrefix", kBool, named), nil
		}
		return dotApp("isIpPrefix", kBool, rest...), nil
	case fn == "isHostAndPort" && len(rest) == 1:
		return dotApp("isHostAndPort", kBool, rest[0]), nil

	case strings.HasPrefix(fn, "get"): // getSeconds, getFullYear, ...
		return piece{}, fmt.Errorf("unsupported: timestamp/duration accessor %s() (pending well-known-type support)", fn)
	}

	return piece{}, t.unsupported(fn)
}

func stringLiteral(e ast.Expr) (string, bool) {
	if e == nil || e.Kind() != ast.LiteralKind {
		return "", false
	}
	if s, ok := e.AsLiteral().(types.String); ok {
		return string(s), true
	}
	return "", false
}

// leanIntArg renders a signed integer as an application argument (negative
// values need parentheses in argument position).
func leanIntArg(v int64) string {
	if v < 0 {
		return "(" + strconv.FormatInt(v, 10) + ")"
	}
	return strconv.FormatInt(v, 10)
}

func foldTimestamp(lit string) (piece, error) {
	ts, err := time.Parse(time.RFC3339Nano, lit)
	if err != nil {
		return piece{}, fmt.Errorf("invalid timestamp literal %q: %w", lit, err)
	}
	text := "Cel.Timestamp.mk " + leanIntArg(ts.Unix()) + " " + leanIntArg(int64(ts.Nanosecond()))
	return piece{text: text, prec: precApp, kind: kTerm}, nil
}

func foldDuration(lit string) (piece, error) {
	d, err := time.ParseDuration(lit)
	if err != nil {
		return piece{}, fmt.Errorf("invalid duration literal %q: %w", lit, err)
	}
	// CEL durations decompose into whole seconds plus same-sign nanos.
	secs := int64(d / time.Second)
	nanos := int64(d % time.Second)
	text := "Cel.Duration.mk " + leanIntArg(secs) + " " + leanIntArg(nanos)
	return piece{text: text, prec: precApp, kind: kTerm}, nil
}

func (t *translator) unsupported(fn string) error {
	return fmt.Errorf("unsupported CEL function %q (supported: size, contains, startsWith, endsWith, matches, "+
		"has, all, exists, exists_one, map, filter, in, int, uint, double, string, bytes, bool, dyn, "+
		"timestamp, duration, unique, isNan, isInf, isEmail, isHostname, isUri, isUriRef, isIp, isIpPrefix, isHostAndPort)", fn)
}

// macro renders the CEL comprehension macros against Lean's binder notation:
//
//	r.all(v, p)        ∀ v ∈ r, p
//	r.exists(v, p)     ∃ v ∈ r, p
//	r.exists_one(v, p) r.countP (fun v => p) = 1
//	r.map(v, e)        r.map (fun v => e)
//	r.map(v, p, e)     (r.filter (fun v => p)).map (fun v => e)
//	r.filter(v, p)     r.filter (fun v => p)
//
// exists_one deliberately avoids ∃! — CEL counts satisfying elements, so
// duplicates in the collection must count separately.
func (t *translator) macro(fn string, c ast.CallExpr) (piece, error) {
	args := c.Args()
	wantArgs := 2
	if fn == "map" && len(args) == 3 {
		wantArgs = 3
	}
	if len(args) != wantArgs {
		return piece{}, fmt.Errorf("%s() expects %d arguments, got %d", fn, wantArgs, len(args))
	}
	if args[0].Kind() != ast.IdentKind {
		return piece{}, fmt.Errorf("%s() iteration variable must be a simple identifier", fn)
	}
	v := args[0].AsIdent()

	recv, err := t.expr(c.Target())
	if err != nil {
		return piece{}, err
	}

	// The comprehension variable would capture the substitution for `this` if
	// it shares its (root) identifier — rename the comprehension variable,
	// since the substitution text is fixed by the caller.
	emitted := v
	if v == t.varRoot {
		emitted = freshName(v, t.used)
		t.used[emitted] = true
	}
	t.bound[v] = append(t.bound[v], emitted)
	defer func() { t.bound[v] = t.bound[v][:len(t.bound[v])-1] }()

	body := func(e ast.Expr, adapt func(piece) piece) (piece, error) {
		p, err := t.expr(e)
		if err != nil {
			return piece{}, err
		}
		return adapt(p), nil
	}
	lambda := func(p piece) string { return "(fun " + leanIdent(emitted) + " => " + p.text + ")" }

	switch fn {
	case "all", "exists":
		p, err := body(args[1], t.liftProp)
		if err != nil {
			return piece{}, err
		}
		q := "∀"
		if fn == "exists" {
			q = "∃"
		}
		return piece{
			text: q + " " + leanIdent(emitted) + " ∈ " + recv.at(precCmp+1) + ", " + p.text,
			prec: precLow,
			kind: kProp,
		}, nil
	case "exists_one", "existsOne":
		p, err := body(args[1], t.boolify)
		if err != nil {
			return piece{}, err
		}
		countP := piece{text: recv.at(precApp+1) + ".countP " + lambda(p), prec: precApp, kind: kTerm}
		return t.binary(cmpOp("="), countP, atom("1", kTerm)), nil
	case "filter":
		p, err := body(args[1], t.boolify)
		if err != nil {
			return piece{}, err
		}
		return piece{text: recv.at(precApp+1) + ".filter " + lambda(p), prec: precApp, kind: kTerm}, nil
	case "map":
		if len(args) == 3 {
			pred, err := body(args[1], t.boolify)
			if err != nil {
				return piece{}, err
			}
			mapped, err := body(args[2], func(p piece) piece { return p })
			if err != nil {
				return piece{}, err
			}
			filtered := piece{text: recv.at(precApp+1) + ".filter " + lambda(pred), prec: precApp, kind: kTerm}
			return piece{text: filtered.at(precApp+1) + ".map " + lambda(mapped), prec: precApp, kind: kTerm}, nil
		}
		mapped, err := body(args[1], func(p piece) piece { return p })
		if err != nil {
			return piece{}, err
		}
		return piece{text: recv.at(precApp+1) + ".map " + lambda(mapped), prec: precApp, kind: kTerm}, nil
	}
	return piece{}, t.unsupported(fn)
}
