package celtolean

import "testing"

// TestRegexAccepted mirrors the `re acc:` battery in Test/RuntimeTest.lean
// (which asserts Cel.Regex.accepts on the same patterns) — keep both lists in
// sync. The Go gate may only be stricter than the Lean parser, never looser:
// anything accepted here must parse in Lean (the generated #guard verifies).
func TestRegexAccepted(t *testing.T) {
	accepted := []string{
		"",
		"abc",
		"^[a-z][a-z0-9-]*$",
		"^[a-z0-9_.\\-]+$",
		"\\d\\D\\w\\W\\s\\S",
		"\\x41\\x{1F600}",
		"a{2}b{3,}c{4,5}",
		"(?:ab|cd)+(e|f)?",
		"a{b",
		"[]a]",
		"[a-]",
		"[-a]",
		"[a-z-_]",
		"a*?b+?c??",
		"^wgt-[0-9]{4,}$",
		"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$",
		"\\.\\*\\(\\)\\[\\]\\{\\}\\|\\^\\$\\\\",
		"\\n\\t\\r\\f\\v\\a\\0",
		"héllo wörld",
		"(a|)",
	}
	rejected := []string{
		"(?i)x",              // flags
		"\\bx",               // word boundary
		"(?P<n>x)",           // named group
		"(?=x)",              // lookahead
		"[[:alpha:]]",        // POSIX class (semantic divergence)
		"a{513}",             // bound too large
		"a{3,2}",             // inverted bounds
		"a{2",                // unterminated repetition (Lean rejects)
		"[abc",               // unterminated class
		"(ab",                // unterminated group
		"ab)",                // stray paren
		"ab\\",               // trailing backslash
		"\\q",                // unsupported escape
		"\\p{L}",             // unicode class
		"\\1",                // backreference-shaped escape
		"\\012",              // octal escape (semantic divergence)
		"*a",                 // quantifier without operand
		"a**",                // RE2 rejects nested repetition
		"[]-a]",              // ']' as range start (semantic divergence)
		"\\x{110000}",        // beyond max scalar
		"\\x{}z",             // RE2 rejects the empty brace escape
		"[a-\\d]",            // predicate as range endpoint
	}
	for _, pat := range accepted {
		if err := RegexAccepted(pat); err != nil {
			t.Errorf("RegexAccepted(%q) = %v, want accept", pat, err)
		}
	}
	for _, pat := range rejected {
		if err := RegexAccepted(pat); err == nil {
			t.Errorf("RegexAccepted(%q) accepted, want reject", pat)
		}
	}
}
