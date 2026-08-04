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
	"math"
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

	// PathAttrs supplies proto-descriptor knowledge for select paths rooted
	// at `this` (dotted CEL paths, "" denoting `this` itself), letting the
	// otherwise type-free translation handle constructs whose Lean rendering
	// depends on the proto type: enum-typed values (CEL treats them as ints;
	// the generated inductive needs its `.toInt32` view), map selection sugar
	// (`m.key`, which must become guarded indexing), and the numeric domains
	// that make literal range checking and CEL-exact arithmetic possible
	// (see domain.go).
	PathAttrs map[string]PathAttr
}

// PathAttr classifies a select path for PathAttrs.
type PathAttr int

const (
	// PathEnumInt marks an enum-typed value: the emitted text gains the
	// generated enum's `.toInt32` view, matching CEL's enum-as-int semantics.
	PathEnumInt PathAttr = iota + 1
	// PathMapSelect marks a map-typed value: CEL selection sugar on it
	// (`m.key`) is emitted as guarded indexing `m["key"]` (CEL errors on a
	// missing key, so the guard makes the proposition false).
	PathMapSelect
	// The numeric domains: the proto scalar kind of the value, which fixes
	// the Lean type its literals elaborate against and the width CEL
	// arithmetic on it must be performed at.
	PathInt32  // int32, sint32, sfixed32
	PathInt64  // int64, sint64, sfixed64
	PathUInt32 // uint32, fixed32
	PathUInt64 // uint64, fixed64
	PathFloat  // float  (Lean Float32)
	PathDouble // double (Lean Float)
)

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
	// Regexes lists the literal regex patterns occurring in the expression
	// (each already vetted by RegexAccepted); codegen emits a compile-time
	// `#guard Cel.Regex.accepts "..."` per pattern so the Lean build fails if
	// the runtime engine would not accept it.
	Regexes []string `json:"regexes,omitempty"`
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
		pathAttrs:  opts.PathAttrs,
		used:       used,
		bound:      map[string][]string{},
		warned:     map[string]bool{},
		regexes:    map[string]bool{},
	}
	p, err := t.expr(root)
	if err != nil {
		return nil, err
	}
	if len(p.guards) > 0 {
		if p.kind == kTerm {
			return nil, errors.New("expression with indexing/arithmetic guards must be boolean-valued")
		}
		// Remaining guards close at the root: a CEL evaluation error anywhere
		// they cover makes the whole rule unsatisfied.
		p = t.closeGuards(p)
	}
	sort.Strings(t.warnings)
	regexes := make([]string, 0, len(t.regexes))
	for re := range t.regexes {
		regexes = append(regexes, re)
	}
	sort.Strings(regexes)
	return &Result{Lean: p.text, Var: t.varName, Kind: p.kind.String(), Prec: p.prec, Regexes: regexes, Warnings: t.warnings}, nil
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
	pathAttrs  map[string]PathAttr  // proto typing knowledge for `this` paths
	used       map[string]bool      // identifiers occurring in the expression
	// bound maps a CEL comprehension variable in scope to the Lean name it is
	// emitted as (renamed when it would capture varRoot); a stack per name
	// handles shadowing.
	bound    map[string][]string
	warnings []string
	warned   map[string]bool
	regexes  map[string]bool // literal regex patterns (for #guard emission)
	// negDepth > 0 inside error-strict, non-monotone contexts (under !, an
	// (in)equality of propositions, ...): guard-closing at ∧/∨ operands and
	// ternary branches is disabled there — guards float outward instead — so
	// a CEL evaluation error can never be absorbed by a surrounding negation.
	negDepth int
}

func (t *translator) warn(msg string) {
	if !t.warned[msg] {
		t.warned[msg] = true
		t.warnings = append(t.warnings, msg)
	}
}

// newGuard allocates an error-guard with a fresh hypothesis name.
func (t *translator) newGuard(cond string) guard {
	hyp := freshName("h", t.used)
	t.used[hyp] = true
	return guard{hyp: hyp, cond: cond}
}

// closeGuards discharges a fragment's pending guards as nested dependent
// if-then-else: `(if h : g₁ then … P … else False)`. The guarded proposition
// is False whenever CEL evaluation of the covered subterms would error
// (out-of-range index, missing map key, arithmetic overflow) — matching
// CEL's error ⇒ rule-not-satisfied — and equals P exactly otherwise. The
// hypotheses stay in scope for the guarded text (getElem proofs).
func (t *translator) closeGuards(p piece) piece {
	if len(p.guards) == 0 {
		return p
	}
	text := t.liftProp(p).text
	for i := len(p.guards) - 1; i >= 0; i-- {
		g := p.guards[i]
		text = "if " + g.hyp + " : " + g.cond + " then " + text + " else False"
	}
	return piece{text: "(" + text + ")", prec: precAtom, kind: kProp}
}

// closeGuardsPositive discharges guards only in positive polarity; in
// non-monotone contexts they float to an enclosing positive position (at the
// latest, the root).
func (t *translator) closeGuardsPositive(p piece) piece {
	if t.negDepth > 0 {
		return p
	}
	return t.closeGuards(p)
}

func mergeGuards(ps ...piece) []guard {
	var out []guard
	for _, p := range ps {
		out = append(out, p.guards...)
	}
	return out
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
		return piece{text: "decide " + p.at(precApp+1), prec: precApp, kind: kBool, guards: p.guards}
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
		p := atom(strconv.FormatInt(int64(v), 10), kTerm)
		if int64(v) < 0 {
			p.prec = precNeg // "-1" needs parens in argument position
		}
		p.num = &constNum{kind: constInt, i: int64(v)}
		return p, nil
	case types.Uint:
		p := atom(strconv.FormatUint(uint64(v), 10), kTerm)
		p.num = &constNum{kind: constUint, u: uint64(v)}
		return p, nil
	case types.Double:
		p := atom(leanFloat(float64(v)), kTerm)
		if float64(v) < 0 {
			p.prec = precNeg
		}
		p.num = &constNum{kind: constDouble, d: float64(v)}
		return p, nil
	case types.String:
		p := atom(leanString(string(v)), kTerm)
		p.noArithErr = true // string concat cannot error
		return p, nil
	case types.Bytes:
		p := leanBytes([]byte(v))
		p.noArithErr = true
		return p, nil
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
		var p piece
		if strings.Contains(t.varName, ".") {
			// Pre-rendered projection like "b.name": atomic, emitted verbatim.
			p = atom(t.varName, kTerm)
		} else {
			p = atom(leanIdent(t.varName), kTerm)
		}
		// Descriptor knowledge about `this` itself: the enum integer view and
		// the numeric domain driving literal range checks / arithmetic width.
		return t.applyPathAttr(p, "", true), nil
	case len(t.bound[name]) > 0:
		return atom(leanIdent(t.bound[name][len(t.bound[name])-1]), kTerm), nil
	case name == "now":
		t.warn("`now` maps to Cel.now: the refinement becomes evaluation-time dependent; " +
			"consider keeping such constraints outside the subtype")
		p := atom("Cel.now", kTerm)
		p.noArithErr = true // the time model's arithmetic is total
		return p, nil
	default:
		t.warn(fmt.Sprintf("free identifier %q kept verbatim; it must resolve in the Lean context of the generated code", name))
		return atom(leanIdent(name), kTerm), nil
	}
}

// celPath renders the dotted CEL path of a select chain rooted at `this`
// ("" for `this` itself); ok is false for other shapes.
func celPath(e ast.Expr) (string, bool) {
	switch e.Kind() {
	case ast.IdentKind:
		if e.AsIdent() == "this" {
			return "", true
		}
	case ast.SelectKind:
		s := e.AsSelect()
		if p, ok := celPath(s.Operand()); ok {
			if p == "" {
				return s.FieldName(), true
			}
			return p + "." + s.FieldName(), true
		}
	}
	return "", false
}

// selectExpr renders a field selection. deeper marks selections whose result
// is immediately selected again: in CEL every non-final hop of a path is
// message-typed, and the base codegen represents message fields as Option
// with a generated value-or-default getter (`subD`), so intermediate hops
// select the getter — giving chains CEL's default-instance traversal
// semantics (`this.a.b.c` → `x.aD.bD.c`).
func (t *translator) selectExpr(sel ast.SelectExpr, deeper bool) (piece, error) {
	operandPath, onPath := celPath(sel.Operand())
	ownPath := ""
	if onPath {
		if operandPath == "" {
			ownPath = sel.FieldName()
		} else {
			ownPath = operandPath + "." + sel.FieldName()
		}
	}

	// Map selection sugar: `m.key` on a map-typed operand is CEL for
	// `m['key']` — emit guarded indexing (a missing key is a CEL error).
	if onPath && t.pathAttrs[operandPath] == PathMapSelect {
		op, err := t.selectOperand(sel, false)
		if err != nil {
			return piece{}, err
		}
		p := t.guardedIndex(op, leanString(sel.FieldName()))
		return t.applyPathAttr(p, ownPath, onPath), nil
	}

	var p piece
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
		p = piece{text: mapped.Text, prec: precAtom, kind: kTerm}
	} else {
		op, err := t.selectOperand(sel, true)
		if err != nil {
			return piece{}, err
		}
		field := sel.FieldName()
		if deeper {
			field += "D"
		}
		p = piece{text: op.at(precApp+1) + "." + leanIdent(field), prec: precAtom, kind: kTerm, guards: op.guards}
	}
	p = t.applyPathAttr(p, ownPath, onPath)
	if sel.IsTestOnly() {
		// Unreachable with macros disabled, but translate faithfully.
		return t.presence(p), nil
	}
	return p, nil
}

// selectOperand translates the operand of a field selection (recursing with
// the intermediate-hop getter convention when it is itself a selection).
func (t *translator) selectOperand(sel ast.SelectExpr, deeper bool) (piece, error) {
	if sel.Operand().Kind() == ast.SelectKind {
		return t.selectExpr(sel.Operand().AsSelect(), deeper)
	}
	return t.expr(sel.Operand())
}

// applyPathAttr rewrites a rendered path value per its proto-derived
// attribute: the enum integer view, and the numeric domain (attached to the
// fragment, not rendered) that literal range checking and arithmetic widening
// consume. known is false when the fragment is not a `this`-rooted path.
func (t *translator) applyPathAttr(p piece, path string, known bool) piece {
	if !known {
		return p
	}
	attr, ok := t.pathAttrs[path]
	if !ok {
		return p
	}
	if attr == PathEnumInt {
		p = piece{text: p.at(precApp+1) + ".toInt32", prec: precAtom, kind: kTerm, guards: p.guards}
	}
	if d := attr.domain(); d != nil {
		p.dom = d
	}
	return p
}

// guardedIndex renders indexing with CEL's error semantics: the element via
// `getElem?`/`Option.get` under a pending isSome guard, so an out-of-range
// index or missing key falsifies the enclosing guarded proposition.
func (t *translator) guardedIndex(recv piece, idxText string) piece {
	optText := "(" + recv.at(precApp+1) + "[" + idxText + "]?)"
	g := t.newGuard(optText + ".isSome")
	g.dependent = true
	return piece{
		text:   optText + ".get " + g.hyp,
		prec:   precApp,
		kind:   kTerm,
		guards: append(append([]guard{}, recv.guards...), g),
	}
}

func (t *translator) presence(fieldSel piece) piece {
	t.warn("has(...) maps to Option.isSome: valid for explicit-presence fields (optional/message/oneof member); " +
		"CEL defines different presence semantics for repeated/map/implicit-presence fields")
	return piece{text: fieldSel.at(precApp+1) + ".isSome", prec: precAtom, kind: kBool, guards: fieldSel.guards}
}

func (t *translator) list(l ast.ListExpr) (piece, error) {
	// Emit Array literals: grpc-lean maps repeated fields to Array, so
	// list-typed comparisons and memberships line up.
	parts := make([]string, 0, len(l.Elements()))
	var guards []guard
	var nums []*constNum
	for _, el := range l.Elements() {
		p, err := t.expr(el)
		if err != nil {
			return piece{}, err
		}
		parts = append(parts, p.text)
		guards = append(guards, p.guards...)
		if p.num != nil {
			nums = append(nums, p.num)
		}
	}
	out := atom("#["+strings.Join(parts, ", ")+"]", kTerm)
	out.guards = guards
	out.nums = nums
	out.noArithErr = true // list concatenation cannot error
	return out, nil
}

func (t *translator) mapLit(m ast.MapExpr) (piece, error) {
	parts := make([]string, 0, len(m.Entries()))
	var guards []guard
	var keyNums []*constNum
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
		guards = append(guards, k.guards...)
		guards = append(guards, v.guards...)
		if k.num != nil {
			// `e in {…}` tests key membership, so the keys are what a typed
			// left operand's domain must accept.
			keyNums = append(keyNums, k.num)
		}
	}
	return piece{
		text:       "Std.HashMap.ofList [" + strings.Join(parts, ", ") + "]",
		prec:       precApp,
		kind:       kTerm,
		guards:     guards,
		nums:       keyNums,
		noArithErr: true,
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
		text:   l.at(op.leftMin) + " " + op.symbol + " " + r.at(op.rightMin),
		prec:   op.prec,
		kind:   op.result,
		guards: mergeGuards(l, r),
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
	var guards []guard
	for _, o := range operands {
		p, err := t.expr(o)
		if err != nil {
			return piece{}, err
		}
		// CEL's &&/|| absorb evaluation errors of one operand when the other
		// decides the result; discharging each operand's guards inside its
		// own conjunct/disjunct reproduces exactly that (in positive
		// polarity — under a negation the guards float outward instead).
		p = t.closeGuardsPositive(p)
		guards = append(guards, p.guards...)
		// leftMin is the stricter side; using it for every operand of the
		// chain is safe for an associative operator.
		parts = append(parts, t.liftProp(p).at(op.leftMin))
	}
	return piece{text: strings.Join(parts, " "+op.symbol+" "), prec: op.prec, kind: kProp, guards: guards}, nil
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
		// CEL `!` is error-strict: an evaluation error inside the operand
		// must fail the rule, so guard-closing is disabled underneath and
		// the guards close outside the negation.
		t.negDepth++
		p, err := t.expr(args[0])
		t.negDepth--
		if err != nil {
			return piece{}, err
		}
		guards := p.guards
		p = t.liftProp(p)
		return piece{text: "¬" + p.at(precNot), prec: precNot, kind: kProp, guards: guards}, nil
	case operators.Negate:
		return t.negate(args[0])
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
		return t.arith(arithOp("+"), "addOk", args)
	case operators.Subtract:
		return t.arith(arithOp("-"), "subOk", args)
	case operators.Multiply:
		return t.arith(arithOp("*"), "mulOk", args)
	case operators.Divide:
		return t.arith(arithOp("/"), "", args)
	case operators.Modulo:
		return t.arith(arithOp("%"), "", args)
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
	// Descriptor-aware checks: a literal outside the typed operand's domain
	// would silently wrap at elaboration, and two proto integers of different
	// widths only unify once the narrower one is lifted to CEL's width.
	if err := t.checkLiterals(l, r); err != nil {
		return piece{}, err
	}
	l, r = t.unifyWidth(l, r)
	return t.binary(op, l, r), nil
}

// arith renders +/-/*/(/)/(%) with CEL's overflow-error semantics: constant
// operands fold and range-check in Go; otherwise (okFn non-empty) a
// Cel.addOk/subOk/mulOk guard is attached, so an evaluation that would
// overflow in CEL falsifies the guarded proposition. Operands that cannot
// produce arithmetic errors (string/bytes/list/map literals,
// timestamp/duration constants, now) skip the guard — concatenation and the
// time model are total. Division and modulo agree with CEL in range and need
// no guard, but do take part in widening.
//
// Widening: CEL performs *all* integer arithmetic at 64 bits, so a 32-bit
// proto field whose domain the plugin supplied is lifted to its CEL width
// first (`x.toInt64`). That makes both the result and the emitted guard
// CEL-exact, instead of the conservative 32-bit condition the untyped
// translation has to assume.
func (t *translator) arith(op binOp, okFn string, args []ast.Expr) (piece, error) {
	l, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	r, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	l, r = t.widen(l), t.widen(r)
	if err := t.checkLiterals(l, r); err != nil {
		return piece{}, err
	}
	out := t.binary(op, l, r)
	out.dom = arithDom(l, r)
	switch {
	case okFn == "":
		// Division/modulo: no CEL error to guard (the fixed-width Lean
		// operators truncate toward zero exactly like CEL).
	case l.num != nil && r.num != nil:
		// Constant arithmetic: range-check the folded value here (there is
		// no typed operand to anchor an ArithOk guard). Mixed const domains
		// are a CEL type error; leave those for the checker downstream.
		num, err := foldConstArith(op.symbol, l.num, r.num)
		if err != nil {
			return piece{}, fmt.Errorf("%v in %q", err, l.text+" "+op.symbol+" "+r.text)
		}
		out.num = num
	case l.noArithErr || r.noArithErr:
		out.noArithErr = true
	default:
		g := t.newGuard("Cel." + okFn + " " + l.at(precApp+1) + " " + r.at(precApp+1))
		out.guards = append(out.guards, g)
	}
	return out, nil
}

// foldConstArith evaluates constant integer/uint arithmetic in the CEL
// domain, rejecting overflow at generation time (CEL would error on every
// evaluation, so the rule could never be satisfied). Doubles never error.
func foldConstArith(symbol string, l, r *constNum) (*constNum, error) {
	if l.kind != r.kind {
		return nil, nil // mixed domains: a CEL type error, not our problem
	}
	switch l.kind {
	case constDouble:
		return &constNum{kind: constDouble}, nil
	case constInt:
		var v int64
		var ok bool
		switch symbol {
		case "+":
			v = l.i + r.i
			ok = (r.i >= 0) == (v >= l.i)
		case "-":
			v = l.i - r.i
			ok = (r.i >= 0) == (v <= l.i)
		case "*":
			v = l.i * r.i
			ok = l.i == 0 ||
				((l.i != -1 || r.i != math.MinInt64) && (r.i != -1 || l.i != math.MinInt64) && v/l.i == r.i)
		}
		if !ok {
			return nil, errors.New("constant arithmetic overflows int64 (CEL errors on every evaluation)")
		}
		return &constNum{kind: constInt, i: v}, nil
	case constUint:
		var v uint64
		var ok bool
		switch symbol {
		case "+":
			v = l.u + r.u
			ok = v >= l.u
		case "-":
			v = l.u - r.u
			ok = r.u <= l.u
		case "*":
			v = l.u * r.u
			ok = l.u == 0 || v/l.u == r.u
		}
		if !ok {
			return nil, errors.New("constant arithmetic overflows uint64 (CEL errors on every evaluation)")
		}
		return &constNum{kind: constUint, u: v}, nil
	}
	return nil, nil
}

// negate renders CEL unary minus. Negated numeric literals stay plain
// (constant, cannot overflow except -(min int64), which cel-go folds into the
// literal); other operands gain a Cel.negOk guard.
func (t *translator) negate(arg ast.Expr) (piece, error) {
	p, err := t.expr(arg)
	if err != nil {
		return piece{}, err
	}
	p = t.widen(p) // CEL negates at 64-bit width
	out := piece{text: "-" + p.at(precNeg), prec: precNeg, kind: kTerm, guards: p.guards, dom: p.dom}
	switch {
	case p.num != nil:
		switch p.num.kind {
		case constInt:
			if p.num.i == math.MinInt64 {
				return piece{}, errors.New("constant negation overflows int64 (CEL errors on every evaluation)")
			}
			out.num = &constNum{kind: constInt, i: -p.num.i}
		case constDouble:
			out.num = &constNum{kind: constDouble}
		case constUint:
			// CEL has no unary minus on uint (type error); pass through.
		}
	case p.noArithErr:
		out.noArithErr = true
	default:
		g := t.newGuard("Cel.negOk " + p.at(precApp+1))
		out.guards = append(out.guards, g)
	}
	return out, nil
}

// equality renders ==/!=. When an operand is itself a proposition (e.g. the
// CEL bool-of-bools `(a == b) == c`), propositional equality would not
// type-check against a Bool operand, so ↔ is used instead. Equality is
// error-strict and (for props) non-monotone, so operand guards float outward
// rather than closing inside.
func (t *translator) equality(fn string, args []ast.Expr) (piece, error) {
	t.negDepth++
	l, lerr := t.expr(args[0])
	r, rerr := t.expr(args[1])
	t.negDepth--
	if lerr != nil {
		return piece{}, lerr
	}
	if rerr != nil {
		return piece{}, rerr
	}
	if err := t.checkLiterals(l, r); err != nil {
		return piece{}, err
	}
	l, r = t.unifyWidth(l, r)
	if l.kind == kProp || r.kind == kProp {
		guards := mergeGuards(l, r)
		l, r = t.liftProp(l), t.liftProp(r)
		iff := piece{text: l.at(precIff+1) + " ↔ " + r.at(precIff+1), prec: precIff, kind: kProp, guards: guards}
		if fn == operators.NotEquals {
			return piece{text: "¬(" + iff.text + ")", prec: precNot, kind: kProp, guards: guards}, nil
		}
		return iff, nil
	}
	symbol := "="
	if fn == operators.NotEquals {
		symbol = "≠"
	}
	return t.binary(cmpOp(symbol), l, r), nil
}

// index renders CEL indexing (array position or map key) with CEL's
// error-on-missing semantics via a pending isSome guard.
func (t *translator) index(args []ast.Expr) (piece, error) {
	recv, err := t.expr(args[0])
	if err != nil {
		return piece{}, err
	}
	idx, err := t.expr(args[1])
	if err != nil {
		return piece{}, err
	}
	recv.guards = mergeGuards(recv, idx)
	return t.guardedIndex(recv, idx.text), nil
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
//
// Error guards: the ternary is strict in its condition (an erroring condition
// errors the whole ternary), so condition guards float outward; each branch
// is only evaluated when taken, so branch guards close per-branch (in
// positive polarity).
func (t *translator) conditional(args []ast.Expr) (piece, error) {
	t.negDepth++ // condition guards must not close inside the condition
	cond, err := t.expr(args[0])
	t.negDepth--
	if err != nil {
		return piece{}, err
	}
	cond = t.liftProp(cond)

	if v, ok := boolLitArg(args[2]); ok {
		branch, err := t.expr(args[1])
		if err != nil {
			return piece{}, err
		}
		branch = t.liftProp(t.closeGuardsPositive(branch))
		if v {
			return piece{
				text:   cond.at(precArrow+1) + " → " + branch.at(precArrow),
				prec:   precArrow,
				kind:   kProp,
				guards: mergeGuards(cond, branch),
			}, nil
		}
		return t.binary(opAnd, cond, branch), nil
	}
	if v, ok := boolLitArg(args[1]); ok && v {
		branch, err := t.expr(args[2])
		if err != nil {
			return piece{}, err
		}
		return t.binary(opOr, cond, t.liftProp(t.closeGuardsPositive(branch))), nil
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
		a, b = t.liftProp(t.closeGuardsPositive(a)), t.liftProp(t.closeGuardsPositive(b))
		resKind = kProp
	case a.kind == kBool && b.kind == kBool:
		resKind = kBool
	default:
		// Both branches are values: they must elaborate at one Lean type.
		a, b = t.unifyWidth(a, b)
	}
	return piece{
		text: "if " + cond.text + " then " + a.text + " else " + b.text,
		prec: precLow,
		kind: resKind,
		dom:  arithDom(a, b),
		// Term/Bool branch guards float (conservative: both branches must be
		// error-free); Prop branch guards were closed per-branch above.
		guards: mergeGuards(cond, a, b),
	}, nil
}
