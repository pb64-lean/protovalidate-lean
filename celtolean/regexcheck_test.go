package celtolean

import (
	"regexp"
	"testing"
)

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

// Every accepted pattern must yield a differential battery whose labels are
// exactly RE2's answers (codegen emits them as `#guard Cel.regexMatch …`, so
// the Lean engine re-decides them at compile time). The battery must contain
// at least one positive point for a satisfiable pattern, or it would certify
// nothing.
func TestRegexProbes(t *testing.T) {
	patterns := []string{
		"", "abc", "^[a-z][a-z0-9-]*$", "^[a-z_]+$", "^(cat|dog)$",
		"^wgt-[0-9]{4,}$", "\\d\\w", "(?:ab|cd)+(e|f)?", "^\\+?[0-9]{7,15}$",
		"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}$", "a{2}b{3,}c{4,5}",
	}
	for _, pat := range patterns {
		re := regexp.MustCompile(pat)
		probes := RegexProbes(pat)
		if len(probes) == 0 {
			t.Errorf("RegexProbes(%q) produced no probes", pat)
			continue
		}
		if len(probes) > maxProbes {
			t.Errorf("RegexProbes(%q) produced %d probes, want <= %d", pat, len(probes), maxProbes)
		}
		positives, seen := 0, map[string]bool{}
		for _, p := range probes {
			if want := re.MatchString(p.Input); p.Match != want {
				t.Errorf("RegexProbes(%q) labelled %q as %v, RE2 says %v", pat, p.Input, p.Match, want)
			}
			if seen[p.Input] {
				t.Errorf("RegexProbes(%q) repeated probe %q", pat, p.Input)
			}
			seen[p.Input] = true
			if p.Match {
				positives++
			}
		}
		if positives == 0 {
			t.Errorf("RegexProbes(%q) has no matching probe; the battery certifies nothing positive", pat)
		}
	}
	// An unparsable pattern yields nothing (the acceptance gate reports it).
	if got := RegexProbes("[a-"); got != nil {
		t.Errorf("RegexProbes on an invalid pattern = %v, want nil", got)
	}
}
