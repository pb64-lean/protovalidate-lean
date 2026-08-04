package celtolean

// regexprobe.go turns the generator's *belief* about a literal pattern into
// something the Lean build actually checks.
//
// RegexAccepted (regexcheck.go) only certifies that a pattern is inside the
// Lean engine's grammar; it makes no claim about the language the pattern
// denotes, and the Go port is not formalized. So agreement between the two
// engines rests on review plus mirrored test batteries — for the patterns
// those batteries happen to contain.
//
// RegexProbes narrows that gap per generated pattern: it derives probe strings
// from the pattern's own RE2 syntax tree, labels each with Go's RE2 engine
// (the reference `matches` semantics), and lets codegen emit the labels as
// `#guard Cel.regexMatch …` lines. Every emitted probe is then re-decided by
// the Lean engine at compile time, so a language-level disagreement between
// RE2 and `Cel.Regex` on that pattern fails the build.
//
// This is differential testing, not equivalence: agreement on finitely many
// probe strings does not prove the languages coincide (see README).

import (
	"regexp"
	"regexp/syntax"
	"sort"
	"strings"
)

// RegexProbe is one differential test point: Match is what Go's RE2 engine
// answers for `Input =~ pattern` (protovalidate's `matches` is a partial
// match, i.e. an unanchored search).
type RegexProbe struct {
	Input string `json:"input"`
	Match bool   `json:"match"`
}

// maxProbes bounds the emitted guards per pattern (each one runs the Lean
// Pike VM at elaboration time).
const maxProbes = 10

// maxProbeLen drops probe strings long enough to make elaboration costly
// (patterns like `a{512}` generate them).
const maxProbeLen = 96

// RegexProbes derives probe strings for a literal pattern and labels them with
// Go's RE2 engine. The pattern must already have passed RegexAccepted; an
// unparsable pattern yields no probes (the acceptance gate reports it).
func RegexProbes(pattern string) []RegexProbe {
	re, err := regexp.Compile(pattern)
	if err != nil {
		return nil
	}
	tree, err := syntax.Parse(pattern, syntax.Perl)
	if err != nil {
		return nil
	}
	tree = tree.Simplify()

	seen := map[string]bool{}
	var inputs []string
	add := func(s string) {
		if seen[s] || len([]rune(s)) > maxProbeLen {
			return
		}
		seen[s] = true
		inputs = append(inputs, s)
	}

	// Witnesses walked out of the pattern itself: the "small" one takes the
	// first alternative and the fewest repetitions, the "wide" one the last
	// alternative and one repetition, so both branches of an alternation and
	// both sides of a `?`/`*` are exercised.
	small := witness(tree, false)
	wide := witness(tree, true)
	add(small)
	add(wide)
	// Perturbations: an anchored pattern rejects these, an unanchored one may
	// not — either way RE2 decides the expected answer.
	for _, w := range []string{small, wide} {
		if w == "" {
			continue
		}
		add(w + "!")
		add("!" + w)
		add(strings.ToUpper(w))
		rs := []rune(w)
		add(string(rs[1:]))
	}
	// A fixed floor so even a trivial pattern gets a couple of points.
	for _, s := range []string{"", "a", "0", "-"} {
		add(s)
	}

	if len(inputs) > maxProbes {
		inputs = inputs[:maxProbes]
	}
	sort.Strings(inputs)
	probes := make([]RegexProbe, 0, len(inputs))
	for _, in := range inputs {
		probes = append(probes, RegexProbe{Input: in, Match: re.MatchString(in)})
	}
	return probes
}

// witness walks an RE2 syntax tree to a string the pattern plausibly matches.
// wide picks the last alternative and one repetition where the narrow walk
// picks the first and the fewest; neither is guaranteed to match (RE2 labels
// the result), but both traverse the whole structure.
func witness(r *syntax.Regexp, wide bool) string {
	if r == nil {
		return ""
	}
	switch r.Op {
	case syntax.OpLiteral:
		return string(r.Rune)
	case syntax.OpCharClass:
		return string(classRune(r.Rune))
	case syntax.OpAnyChar, syntax.OpAnyCharNotNL:
		return "a"
	case syntax.OpCapture:
		return witness(r.Sub[0], wide)
	case syntax.OpConcat:
		var b strings.Builder
		for _, s := range r.Sub {
			b.WriteString(witness(s, wide))
		}
		return b.String()
	case syntax.OpAlternate:
		if len(r.Sub) == 0 {
			return ""
		}
		if wide {
			return witness(r.Sub[len(r.Sub)-1], wide)
		}
		return witness(r.Sub[0], wide)
	case syntax.OpStar, syntax.OpQuest:
		if wide {
			return witness(r.Sub[0], wide)
		}
		return ""
	case syntax.OpPlus:
		return witness(r.Sub[0], wide)
	case syntax.OpRepeat:
		unit := witness(r.Sub[0], wide)
		n := r.Min
		if wide && r.Max > r.Min {
			n = r.Min + 1
		}
		if n <= 0 {
			return ""
		}
		if len(unit)*n > maxProbeLen {
			return strings.Repeat(unit, 1)
		}
		return strings.Repeat(unit, n)
	}
	// Anchors, empty matches and word boundaries contribute nothing.
	return ""
}

// classRune picks a readable representative of a character class: a printable
// ASCII rune when the class has one, else the class's first rune.
func classRune(ranges []rune) rune {
	for i := 0; i+1 < len(ranges); i += 2 {
		lo, hi := ranges[i], ranges[i+1]
		for _, pref := range []rune{'a', 'A', '0', '-', '_', '.'} {
			if pref >= lo && pref <= hi {
				return pref
			}
		}
		if lo >= 0x20 && lo < 0x7f {
			return lo
		}
	}
	if len(ranges) > 0 {
		return ranges[0]
	}
	return 'a'
}
