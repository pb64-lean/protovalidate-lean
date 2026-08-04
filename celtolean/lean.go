package celtolean

import (
	"fmt"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// kind classifies the Lean type of a translated fragment. CEL is dynamically
// typed at parse time; we track only the bool/Prop distinction that matters
// for producing idiomatic Lean (∧/∨/¬/=/if live in Prop, library functions
// like String.startsWith return Bool and coerce).
type kind int

const (
	kTerm kind = iota // any non-boolean value (numbers, strings, collections, ...)
	kBool             // Lean Bool
	kProp             // Lean Prop
)

func (k kind) String() string {
	switch k {
	case kBool:
		return "bool"
	case kProp:
		return "prop"
	default:
		return "term"
	}
}

// Lean parser precedences for the notation we emit. A fragment records the
// precedence of its outermost syntax; parents parenthesize any child whose
// precedence is below the slot's minimum.
const (
	precLow   = 5    // if-then-else, ∀/∃ binders: parenthesize whenever embedded
	precIff   = 20   // ↔ (operands ≥ 21)
	precArrow = 25   // → infixr (left ≥ 26)
	precOr    = 30   // ∨ infixr (left ≥ 31)
	precAnd   = 35   // ∧ infixr (left ≥ 36)
	precNot   = 40   // ¬ prefix (operand ≥ 40)
	precCmp   = 50   // = ≠ < ≤ > ≥ ∈ (operands ≥ 51)
	precAdd   = 65   // + - infixl (right ≥ 66)
	precMul   = 70   // * / % infixl (right ≥ 71)
	precNeg   = 75   // prefix - (operand ≥ 75; binds tighter than *)
	precApp   = 1022 // function application (args must be atomic)
	precAtom  = 1024 // identifiers, literals, projections, bracketed forms
)

// guard is a pending error side-condition: cond must hold (as a hypothesis
// named hyp, kept in scope for dependent uses like getElem proofs) for the
// guarded fragment to be CEL-evaluable without error. Guards are discharged
// as `if hyp : cond then … else False` at the translation points where CEL's
// error semantics demand it (see translator.closeGuards).
type guard struct {
	hyp  string
	cond string
	// dependent guards bind a hypothesis the guarded text needs to elaborate
	// (getElem proofs); they cannot be relocated. Non-dependent guards
	// (arithmetic side-conditions) may be hoisted out of binder bodies as
	// quantified definedness conditions.
	dependent bool
}

// constKind is the CEL literal domain of a constant numeric expression.
type constKind int

const (
	constInt constKind = iota
	constUint
	constDouble
)

// constNum marks a piece as a compile-time numeric constant (literals and
// arithmetic over them). Constant arithmetic is range-checked in Go — the
// emitted text stays a polymorphic literal expression — because an
// ArithOk-guarded form over literals alone would have no type anchor.
type constNum struct {
	kind constKind
	i    int64
	u    uint64
	d    float64
}

// piece is a translated fragment of Lean syntax.
type piece struct {
	text string
	prec int
	kind kind
	// boolLit is set for the CEL literals `true`/`false` so they can be
	// rendered as the propositions True/False when a Prop is required.
	boolLit *bool
	// guards are pending error side-conditions (bounds, overflow) not yet
	// discharged; they propagate to enclosing fragments.
	guards []guard
	// num is set for constant numeric expressions (Go-side range checking).
	num *constNum
	// nums holds the constant elements of a list/map literal, so `this in
	// [1, 2, 3]` can range-check them against the receiver's domain.
	nums []*constNum
	// dom is the proto-derived numeric domain of the fragment, when known
	// (Options.PathAttrs); it drives literal range checking and the widening
	// of 32-bit arithmetic to CEL's width. See domain.go.
	dom *numDom
	// noArithErr marks operands whose CEL arithmetic cannot error (string/
	// bytes/list/map literals, folded timestamp/duration constants, now):
	// arithmetic on them is emitted unguarded.
	noArithErr bool
}

func atom(text string, k kind) piece { return piece{text: text, prec: precAtom, kind: k} }
func (p piece) at(min int) string {
	if p.prec < min {
		return "(" + p.text + ")"
	}
	return p.text
}

// leanKeywords are identifiers that need «guillemet» quoting when they appear
// as variable or field names. CEL identifiers are [a-zA-Z_][a-zA-Z0-9_]* so
// they are lexically valid Lean identifiers except for reserved words.
var leanKeywords = map[string]bool{
	"abbrev": true, "at": true, "attribute": true, "axiom": true, "by": true,
	"calc": true, "class": true, "def": true, "deriving": true, "do": true,
	"else": true, "end": true, "example": true, "exists": true, "extends": true,
	"from": true, "fun": true, "have": true, "if": true, "import": true,
	"in": true, "inductive": true, "instance": true, "lemma": true, "let": true,
	"macro": true, "match": true, "matches": true, "meta": true, "mutual": true, "namespace": true,
	"notation": true, "opaque": true, "open": true, "partial": true, "private": true,
	"protected": true, "public": true, "rec": true, "section": true, "show": true,
	"sorry": true, "structure": true, "syntax": true, "then": true, "theorem": true,
	"this": true, "universe": true, "unsafe": true, "variable": true, "where": true,
	"with": true,
}

// leanIdent renders a CEL identifier or field name as Lean, quoting reserved words.
func leanIdent(name string) string {
	if leanKeywords[name] {
		return "«" + name + "»"
	}
	return name
}

// leanString renders s as a Lean string literal. Printable characters
// (including non-ASCII) are kept verbatim — Lean sources are UTF-8 — while
// control characters use escapes.
func leanString(s string) string {
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
			if r < 0x20 || r == 0x7f {
				b.WriteString(fmt.Sprintf(`\u%04x`, r))
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

// leanBytes renders a CEL bytes literal. Text-like payloads read naturally as
// a string with .toUTF8; arbitrary bytes fall back to an explicit ByteArray.
func leanBytes(data []byte) piece {
	if utf8.Valid(data) && printableText(string(data)) {
		return piece{text: leanString(string(data)) + ".toUTF8", prec: precAtom, kind: kTerm}
	}
	var b strings.Builder
	b.WriteString("ByteArray.mk #[")
	for i, x := range data {
		if i > 0 {
			b.WriteString(", ")
		}
		fmt.Fprintf(&b, "0x%02x", x)
	}
	b.WriteString("]")
	return piece{text: b.String(), prec: precApp, kind: kTerm}
}

func printableText(s string) bool {
	for _, r := range s {
		if r < 0x20 || r == 0x7f || !unicode.IsPrint(r) {
			return false
		}
	}
	return true
}

// leanFloat renders a CEL double literal in Lean-compatible scientific/decimal
// notation, always keeping it visibly a float (so it elaborates via
// OfScientific rather than as a polymorphic Nat literal).
func leanFloat(f float64) string {
	s := strconv.FormatFloat(f, 'g', -1, 64)
	s = strings.ReplaceAll(s, "e+", "e")
	if !strings.ContainsAny(s, ".e") {
		s += ".0"
	}
	return s
}
