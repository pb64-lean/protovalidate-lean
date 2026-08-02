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

// piece is a translated fragment of Lean syntax.
type piece struct {
	text string
	prec int
	kind kind
	// boolLit is set for the CEL literals `true`/`false` so they can be
	// rendered as the propositions True/False when a Prop is required.
	boolLit *bool
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
