// Package celtolean translates CEL expressions (as used by protovalidate
// custom constraints) into Lean 4 propositions suitable for subtype
// refinements: the CEL expression `this.size() <= 100` becomes the Lean
// proposition `x.size ≤ 100`, for use as `{ x : String // x.size ≤ 100 }`.
//
// Design notes:
//
//   - Parsing uses the official cel-go parser with macro expansion disabled,
//     so `l.all(i, p)` arrives as an ordinary call and can be rendered as the
//     idiomatic `∀ i ∈ l, p` rather than a comprehension loop.
//   - Translation is purely syntactic: no FieldDescriptor or type information
//     is consumed. Numeric literals are left polymorphic, functions are mapped
//     to dot-notation (resolved by Lean against the field's actual type), and
//     ill-typed CEL (e.g. wrong field names) surfaces as a Lean compile error
//     in the generated code rather than a translation error.
//   - The emitted proposition is compositional at CEL granularity: CEL
//     operators map to the corresponding Lean connectives/relations, and CEL
//     library calls map to the equivalent Lean function on the base type
//     (with small shims from Protovalidate.Cel where core Lean lacks a
//     counterpart, e.g. Cel.matches).
//
// Base types follow grpc-lean's protobuf codegen: Int32/Int64/UInt32/UInt64,
// Float/Float32, Bool, String, ByteArray, Array α for repeated,
// Std.HashMap κ ν for maps, Option α for explicit-presence fields, and
// generated inductives/structures for enums/messages with verbatim snake_case
// field names. Notably the fixed-width integer types make Lean's / and %
// agree exactly with CEL's Go semantics (truncation toward zero).
package celtolean

import (
	"errors"
	"fmt"
	"sort"
	"strconv"
	"strings"

	"github.com/google/cel-go/common"
	"github.com/google/cel-go/common/ast"
	"github.com/google/cel-go/common/operators"
	"github.com/google/cel-go/common/types"
	"github.com/google/cel-go/parser"
)

// Options configures a translation.
type Options struct {
	// Var is the Lean expression substituted for the CEL identifier `this`.
	// Defaults to "x". A simple identifier is treated as a renameable binder:
	// if the expression itself uses the chosen name (e.g. a comprehension
	// variable), a fresh name x_1, x_2, ... is picked instead. A dotted
	// projection (e.g. "b.name", as used by codegen for field constraints
	// checked against a message binding) is fixed; comprehension variables
	// that would capture its root identifier are renamed instead.
	Var string

	// ThisFields switches to message/struct-field mode: `this` may only occur
	// as the operand of a field selection (or has(this.f)), and `this.f` is
	// replaced by the mapped Lean text (e.g. "name" → "name.val" for a
	// subtype-typed sibling field). Used to state message-level CEL rules as
	// structure proof fields and validate-time conditions over field
	// bindings. Selecting a field absent from the map is an error, as is any
	// other use of `this`.
	ThisFields map[string]ThisField
}

// ThisField describes how a message field is reachable in ThisFields mode.
type ThisField struct {
	// Text is the Lean expression for the field's value (atomic, e.g.
	// "name.val").
	Text string
	// Has is the Bool-valued Lean expression deciding CEL has(this.f) for
	// the field, encoding the field's actual presence semantics (isSome,
	// non-default, non-empty, oneof case test). Empty means has() is not
	// supported for the field.
	Has string
}

// Result is a translated expression.
type Result struct {
	// Lean is the emitted Lean expression.
	Lean string `json:"lean"`
	// Var is the binder name actually used for `this` (post collision-avoidance).
	Var string `json:"var"`
	// Kind is "prop", "bool", or "term". Both "prop" and "bool" are valid
	// subtype refinement bodies (Bool coerces to Prop); "term" means the CEL
	// expression was not boolean-valued.
	Kind string `json:"kind"`
	// Prec is the Lean precedence of the expression's outermost syntax;
	// callers embedding the text as an operand (e.g. conjoining several rule
	// translations with ∧) parenthesize when Prec is below the slot minimum.
	Prec int `json:"prec"`
	// Warnings notes semantic caveats of the translation (presence semantics
	// of has(), time-dependence of now, placeholder timestamp types, ...).
	Warnings []string `json:"warnings,omitempty"`
}

// Translate converts a CEL expression to a Lean proposition.
func Translate(cel string, opts Options) (*Result, error) {
	root, err := parseCEL(cel)
	if err != nil {
		return nil, err
	}
	used := map[string]bool{}
	collectIdents(root, used)

	varName := opts.Var
	if varName == "" {
		varName = "x"
	}
	if !strings.Contains(varName, ".") {
		// Renameable binder: dodge every identifier in the expression.
		varName = freshName(varName, used)
	}
	t := &translator{
		varName:    varName,
		varRoot:    strings.SplitN(varName, ".", 2)[0],
		thisFields: opts.ThisFields,
		used:       used,
		bound:      map[string][]string{},
		warned:     map[string]bool{},
	}
	p, err := t.expr(root)
	if err != nil {
		return nil, err
	}
	sort.Strings(t.warnings)
	return &Result{Lean: p.text, Var: t.varName, Kind: p.kind.String(), Prec: p.prec, Warnings: t.warnings}, nil
}

// freshName returns base if unused, else the first unused base_1, base_2, ...
func freshName(base string, used map[string]bool) string {
	name := base
	for i := 1; used[name]; i++ {
		name = fmt.Sprintf("%s_%d", base, i)
	}
	return name
}

func parseCEL(src string) (ast.Expr, error) {
	// No macro option: has/all/exists/exists_one/map/filter stay ordinary
	// calls instead of being expanded into fold comprehensions.
	p, err := parser.NewParser()
	if err != nil {
		return nil, err
	}
	parsed, iss := p.Parse(common.NewTextSource(src))
	if iss != nil && len(iss.GetErrors()) > 0 {
		return nil, errors.New(iss.ToDisplayString())
	}
	return parsed.Expr(), nil
}

func collectIdents(e ast.Expr, out map[string]bool) {
	switch e.Kind() {
	case ast.IdentKind:
		out[e.AsIdent()] = true
	case ast.SelectKind:
		collectIdents(e.AsSelect().Operand(), out)
	case ast.CallKind:
		c := e.AsCall()
		if c.IsMemberFunction() {
			collectIdents(c.Target(), out)
		}
		for _, a := range c.Args() {
			collectIdents(a, out)
		}
	case ast.ListKind:
		for _, el := range e.AsList().Elements() {
			collectIdents(el, out)
		}
	case ast.MapKind:
		for _, entry := range e.AsMap().Entries() {
			me := entry.AsMapEntry()
			collectIdents(me.Key(), out)
			collectIdents(me.Value(), out)
		}
	case ast.StructKind:
		for _, f := range e.AsStruct().Fields() {
			collectIdents(f.AsStructField().Value(), out)
		}
	case ast.ComprehensionKind:
		co := e.AsComprehension()
		collectIdents(co.IterRange(), out)
		collectIdents(co.AccuInit(), out)
		collectIdents(co.LoopCondition(), out)
		collectIdents(co.LoopStep(), out)
		collectIdents(co.Result(), out)
	}
}

type translator struct {
	varName    string
	varRoot    string               // first component of varName (capture avoidance)
	thisFields map[string]ThisField // non-nil: message/struct-field mode
	used       map[string]bool      // identifiers occurring in the expression
	// bound maps a CEL comprehension variable in scope to the Lean name it is
	// emitted as (renamed when it would capture varRoot); a stack per name
	// handles shadowing.
	bound    map[string][]string
	warnings []string
	warned   map[string]bool
}

func (t *translator) warn(msg string) {
	if !t.warned[msg] {
		t.warned[msg] = true
		t.warnings = append(t.warnings, msg)
	}
}

// liftProp adapts a fragment for a position that requires a Prop. Bool
// fragments are left as-is (Lean coerces Bool to Prop), except literal
// true/false which read better as True/False. Terms pass through untouched:
// if the CEL was ill-typed, the Lean compiler reports it downstream.
func (t *translator) liftProp(p piece) piece {
	if p.kind == kBool && p.boolLit != nil {
		if *p.boolLit {
			return atom("True", kProp)
		}
		return atom("False", kProp)
	}
	p.kind = kProp
	return p
}

// boolify adapts a fragment for a position that requires a Bool (predicate
// bodies of countP/filter). Props are wrapped in decide (all emitted atoms
// are Decidable).
func (t *translator) boolify(p piece) piece {
	if p.kind == kProp {
		return piece{text: "decide " + p.at(precApp+1), prec: precApp, kind: kBool}
	}
	return p
}

func (t *translator) expr(e ast.Expr) (piece, error) {
	switch e.Kind() {
	case ast.LiteralKind:
		return t.literal(e)
	case ast.IdentKind:
		return t.ident(e.AsIdent())
	case ast.SelectKind:
		return t.selectExpr(e.AsSelect(), false)
	case ast.CallKind:
		return t.call(e.AsCall())
	case ast.ListKind:
		return t.list(e.AsList())
	case ast.MapKind:
		return t.mapLit(e.AsMap())
	case ast.StructKind:
		return piece{}, fmt.Errorf("unsupported: message literal %s{...}", e.AsStruct().TypeName())
	case ast.ComprehensionKind:
		return piece{}, errors.New("unsupported: bare comprehension expression")
	default:
		return piece{}, fmt.Errorf("unsupported CEL expression kind %v", e.Kind())
	}
}

func (t *translator) literal(e ast.Expr) (piece, error) {
	switch v := e.AsLiteral().(type) {
	case types.Bool:
		b := bool(v)
		return piece{text: strconv.FormatBool(b), prec: precAtom, kind: kBool, boolLit: &b}, nil
	case types.Int:
		return atom(strconv.FormatInt(int64(v), 10), kTerm), nil
	case types.Uint:
		return atom(strconv.FormatUint(uint64(v), 10), kTerm), nil
	case types.Double:
		return atom(leanFloat(float64(v)), kTerm), nil
	case types.String:
		return atom(leanString(string(v)), kTerm), nil
	case types.Bytes:
		return leanBytes([]byte(v)), nil
	case types.Null:
		return atom("none", kTerm), nil
	default:
		return piece{}, fmt.Errorf("unsupported literal %v", e.AsLiteral())
	}
}

func (t *translator) ident(name string) (piece, error) {
	switch {
	case name == "this":
		if t.thisFields != nil {
			return piece{}, errors.New("in message-field mode `this` may only appear as a field selection (this.field)")
		}
		if strings.Contains(t.varName, ".") {
			// Pre-rendered projection like "b.name": atomic, emitted verbatim.
			return atom(t.varName, kTerm), nil
		}
		return atom(leanIdent(t.varName), kTerm), nil
	case len(t.bound[name]) > 0:
		return atom(leanIdent(t.bound[name][len(t.bound[name])-1]), kTerm), nil
	case name == "now":
		t.warn("`now` maps to Cel.now: the refinement becomes evaluation-time dependent; " +
			"consider keeping such constraints outside the subtype")
		return atom("Cel.now", kTerm), nil
	default:
		t.warn(fmt.Sprintf("free identifier %q kept verbatim; it must resolve in the Lean context of the generated code", name))
		return atom(leanIdent(name), kTerm), nil
	}
}

// selectExpr renders a field selection. deeper marks selections whose result
// is immediately selected again: in CEL every non-final hop of a path is
// message-typed, and the base codegen represents message fields as Option
// with a generated value-or-default getter (`subD`), so intermediate hops
// select the getter — giving chains CEL's default-instance traversal
// semantics (`this.a.b.c` → `x.aD.bD.c`).
func (t *translator) selectExpr(sel ast.SelectExpr, deeper bool) (piece, error) {
	var text string
	if t.thisFields != nil && sel.Operand().Kind() == ast.IdentKind && sel.Operand().AsIdent() == "this" {
		// Head of a message-rule path: the mapped text is already the field's
		// base-typed CEL value, so no getter applies regardless of depth.
		mapped, ok := t.thisFields[sel.FieldName()]
		if !ok {
			return piece{}, fmt.Errorf("message rule references unknown field %q", sel.FieldName())
		}
		if mapped.Text == "" {
			return piece{}, fmt.Errorf("message rule accesses the value of field %q, which has no direct Lean counterpart (oneof member); only has(this.%s) is supported", sel.FieldName(), sel.FieldName())
		}
		text = mapped.Text
	} else {
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
		field := sel.FieldName()
		if deeper {
			field += "D"
		}
		text = op.at(precApp+1) + "." + leanIdent(field)
	}
	if sel.IsTestOnly() {
		// Unreachable with macros disabled, but translate faithfully.
		return t.presence(piece{text: text, prec: precAtom, kind: kTerm}), nil
	}
	return piece{text: text, prec: precAtom, kind: kTerm}, nil
}

func (t *translator) presence(fieldSel piece) piece {
	t.warn("has(...) maps to Option.isSome: valid for explicit-presence fields (optional/message/oneof member); " +
		"CEL defines different presence semantics for repeated/map/implicit-presence fields")
	return piece{text: fieldSel.at(precApp+1) + ".isSome", prec: precAtom, kind: kBool}
}

func (t *translator) list(l ast.ListExpr) (piece, error) {
	// Emit Array literals: grpc-lean maps repeated fields to Array, so
	// list-typed comparisons and memberships line up.
	parts := make([]string, 0, len(l.Elements()))
	for _, el := range l.Elements() {
		p, err := t.expr(el)
		if err != nil {
			return piece{}, err
		}
		parts = append(parts, p.text)
	}
	return atom("#["+strings.Join(parts, ", ")+"]", kTerm), nil
}

func (t *translator) mapLit(m ast.MapExpr) (piece, error) {
	parts := make([]string, 0, len(m.Entries()))
	for _, entry := range m.Entries() {
		me := entry.AsMapEntry()
		k, err := t.expr(me.Key())
		if err != nil {
			return piece{}, err
		}
		v, err := t.expr(me.Value())
		if err != nil {
			return piece{}, err
		}
		parts = append(parts, "("+k.text+", "+v.text+")")
	}
	return piece{
		text: "Std.HashMap.ofList [" + strings.Join(parts, ", ") + "]",
		prec: precApp,
		kind: kTerm,
	}, nil
}

// binOp describes a Lean infix operator.
type binOp struct {
	symbol   string
	prec     int
	leftMin  int
	rightMin int
	operand  func(*translator, piece) piece // lifting applied to operands
	result   kind
}

var (
	opAnd = binOp{"∧", precAnd, precAnd + 1, precAnd, (*translator).liftProp, kProp}
	opOr  = binOp{"∨", precOr, precOr + 1, precOr, (*translator).liftProp, kProp}
)

func cmpOp(symbol string) binOp {
	return binOp{symbol, precCmp, precCmp + 1, precCmp + 1, nil, kProp}
}

func arithOp(symbol string) binOp {
	// infixl: right operand needs the next level.
	prec := precMul
	if symbol == "+" || symbol == "-" {
		prec = precAdd
	}
	return binOp{symbol, prec, prec, prec + 1, nil, kTerm}
}

func (t *translator) binary(op binOp, l, r piece) piece {
	if op.operand != nil {
		l, r = op.operand(t, l), op.operand(t, r)
	}
	return piece{
		text: l.at(op.leftMin) + " " + op.symbol + " " + r.at(op.rightMin),
		prec: op.prec,
		kind: op.result,
	}
}

// flatten collects the operand spine of a left-associated &&/|| chain so it
// can be emitted as the natural n-ary `a ∧ b ∧ c` (Lean's ∧/∨ are right
// associative; conjunction is associative so re-association is sound).
func flatten(fn string, e ast.Expr, out *[]ast.Expr) {
	if e.Kind() == ast.CallKind {
		c := e.AsCall()
		if c.FunctionName() == fn && !c.IsMemberFunction() && len(c.Args()) == 2 {
			flatten(fn, c.Args()[0], out)
			flatten(fn, c.Args()[1], out)
			return
		}
	}
	*out = append(*out, e)
}

func (t *translator) logicalChain(fn string, op binOp, c ast.CallExpr) (piece, error) {
	var operands []ast.Expr
	flatten(fn, c.Args()[0], &operands)
	flatten(fn, c.Args()[1], &operands)
	parts := make([]string, 0, len(operands))
	for _, o := range operands {
		p, err := t.expr(o)
		if err != nil {
			return piece{}, err
		}
		// leftMin is the stricter side; using it for every operand of the
		// chain is safe for an associative operator.
		parts = append(parts, t.liftProp(p).at(op.leftMin))
	}
	return piece{text: strings.Join(parts, " "+op.symbol+" "), prec: op.prec, kind: kProp}, nil
}

func (t *translator) call(c ast.CallExpr) (piece, error) {
	fn := c.FunctionName()
	args := c.Args()

	switch fn {
	case operators.LogicalAnd:
		return t.logicalChain(fn, opAnd, c)
	case operators.LogicalOr:
		return t.logicalChain(fn, opOr, c)
	case operators.LogicalNot:
		p, err := t.expr(args[0])
		if err != nil {
			return piece{}, err
		}
		p = t.liftProp(p)
		return piece{text: "¬" + p.at(precNot), prec: precNot, kind: kProp}, nil
	case operators.Negate:
		p, err := t.expr(args[0])
		if err != nil {
			return piece{}, err
		}
		return piece{text: "-" + p.at(precNeg), prec: precNeg, kind: kTerm}, nil
	case operators.Equals, operators.NotEquals:
		return t.equality(fn, args)
	case operators.Less:
		return t.binaryArgs(cmpOp("<"), args)
	case operators.LessEquals:
		return t.binaryArgs(cmpOp("≤"), args)
	case operators.Greater:
		return t.binaryArgs(cmpOp(">"), args)
	case operators.GreaterEquals:
		return t.binaryArgs(cmpOp("≥"), args)
	case operators.In, operators.OldIn:
		return t.binaryArgs(cmpOp("∈"), args)
	case operators.Add:
		return t.binaryArgs(arithOp("+"), args)
	case operators.Subtract:
		return t.binaryArgs(arithOp("-"), args)
	case operators.Multiply:
		return t.binaryArgs(arithOp("*"), args)
	case operators.Divide:
		return t.binaryArgs(arithOp("/"), args)
	case operators.Modulo:
		return t.binaryArgs(arithOp("%"), args)
	case operators.Index:
		return t.index(args)
	case operators.Conditional:
		return t.conditional(args)
	case operators.OptIndex, operators.OptSelect:
		return piece{}, fmt.Errorf("unsupported: CEL optional syntax (%s)", fn)
	}

	return t.function(c)
}

func (t *translator) binaryArgs(op binOp, args []ast.Expr) (piece, error) {
	l, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	r, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	return t.binary(op, l, r), nil
}

// equality renders ==/!=. When an operand is itself a proposition (e.g. the
// CEL bool-of-bools `(a == b) == c`), propositional equality would not
// type-check against a Bool operand, so ↔ is used instead.
func (t *translator) equality(fn string, args []ast.Expr) (piece, error) {
	l, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	r, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	if l.kind == kProp || r.kind == kProp {
		l, r = t.liftProp(l), t.liftProp(r)
		iff := piece{text: l.at(precIff+1) + " ↔ " + r.at(precIff+1), prec: precIff, kind: kProp}
		if fn == operators.NotEquals {
			return piece{text: "¬(" + iff.text + ")", prec: precNot, kind: kProp}, nil
		}
		return iff, nil
	}
	symbol := "="
	if fn == operators.NotEquals {
		symbol = "≠"
	}
	return t.binary(cmpOp(symbol), l, r), nil
}

func (t *translator) index(args []ast.Expr) (piece, error) {
	recv, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	idx, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	// `!` (panicking) indexing: CEL indexing is a runtime error out of range;
	// inside a Prop the default value keeps the proposition total.
	return piece{text: recv.at(precApp+1) + "[" + idx.text + "]!", prec: precAtom, kind: kTerm}, nil
}

// boolLitArg reports whether e is the literal true/false, and which.
func boolLitArg(e ast.Expr) (value, ok bool) {
	if e.Kind() != ast.LiteralKind {
		return false, false
	}
	if b, isBool := e.AsLiteral().(types.Bool); isBool {
		return bool(b), true
	}
	return false, false
}

// conditional renders the CEL ternary. The protovalidate idioms
// `c ? p : true`, `c ? true : p`, and `c ? p : false` are folded into the
// propositions a Lean author would write (c → p, c ∨ p, c ∧ p); the general
// case stays a (decidable) if-then-else.
func (t *translator) conditional(args []ast.Expr) (piece, error) {
	cond, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	cond = t.liftProp(cond)

	if v, ok := boolLitArg(args[2]); ok {
		branch, err := t.expr(args[1])
		if err != nil {
			return piece{}, err
		}
		branch = t.liftProp(branch)
		if v {
			return piece{
				text: cond.at(precArrow+1) + " → " + branch.at(precArrow),
				prec: precArrow,
				kind: kProp,
			}, nil
		}
		return t.binary(opAnd, cond, branch), nil
	}
	if v, ok := boolLitArg(args[1]); ok && v {
		branch, err := t.expr(args[2])
		if err != nil {
			return piece{}, err
		}
		return t.binary(opOr, cond, t.liftProp(branch)), nil
	}

	a, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	b, err := t.expr(args[2])
	if err != nil {
		return piece{}, err
	}
	resKind := kTerm
	switch {
	case a.kind == kProp || b.kind == kProp:
		a, b = t.liftProp(a), t.liftProp(b)
		resKind = kProp
	case a.kind == kBool && b.kind == kBool:
		resKind = kBool
	}
	return piece{
		text: "if " + cond.text + " then " + a.text + " else " + b.text,
		prec: precLow,
		kind: resKind,
	}, nil
}
