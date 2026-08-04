package celtolean

// regexcheck.go is a faithful Go port of the pattern grammar of the Lean
// runtime regex engine (lean/Protovalidate/Cel/Regex.lean, namespace
// Cel.Regex.Parser). The Lean parser is the reference: a pattern accepted
// here MUST be accepted by the Lean engine, or the generated
// `#guard Cel.Regex.accepts "..."` fails the Lean build (the backstop).
//
// The gate exists because Go's RE2 accepts a superset of the Lean engine
// ((?i) flags, \b, named classes, ...). A pattern outside the Lean subset
// would compile fine under an RE2-only check and then MATCH NOTHING at
// runtime — which is acceptance-unsound under negation (`!x.matches(...)`
// would degenerate to true). RegexAccepted rejects such patterns at
// generation time with a source-located error.
//
// Two deliberate divergences make this gate *stricter* than the Lean parser
// (strictness is sound; the Lean guard still verifies acceptance):
//
//   - POSIX named classes ("[[:alpha:]]"): the Lean parser reads them as
//     literal characters while RE2 gives them class semantics — a silent
//     semantic divergence, so they are rejected here.
//   - Callers additionally require RE2 validity (regexp.Compile): a pattern
//     the Lean parser tolerates but RE2 rejects (e.g. "a**") would error in
//     CEL — and an erroring rule is never satisfied — while the Lean engine
//     would happily match.

import (
	"fmt"
	"regexp"
	"unicode"
)

// RegexAccepted reports whether pattern is inside the RE2 subset the Lean
// runtime engine supports (and free of known semantic divergences). A nil
// error means the pattern parses in the Lean engine with RE2 semantics.
func RegexAccepted(pattern string) error {
	if _, err := regexp.Compile(pattern); err != nil {
		return fmt.Errorf("invalid RE2 pattern: %v", err)
	}
	p := &reParser{rs: []rune(pattern)}
	if err := p.parseAlt(); err != nil {
		return err
	}
	if p.pos != len(p.rs) {
		return fmt.Errorf("unexpected ')'")
	}
	return nil
}

type reParser struct {
	rs  []rune
	pos int
}

func (p *reParser) peek(i int) (rune, bool) {
	if p.pos+i < len(p.rs) {
		return p.rs[p.pos+i], true
	}
	return 0, false
}

// escKind classifies an escape: a concrete character (usable as a range
// endpoint) or a character-class predicate (\d, \w, ...).
type escKind int

const (
	escChar escKind = iota
	escPred
)

func hexVal(c rune) (int, bool) {
	switch {
	case c >= '0' && c <= '9':
		return int(c - '0'), true
	case c >= 'a' && c <= 'f':
		return int(c-'a') + 10, true
	case c >= 'A' && c <= 'F':
		return int(c-'A') + 10, true
	}
	return 0, false
}

func isValidChar(n int) bool {
	return n < 0xd800 || (0xdfff < n && n < 0x110000)
}

// escape consumes an escape sequence (after the backslash), mirroring
// Parser.escape.
func (p *reParser) escape() (escKind, error) {
	c, ok := p.peek(0)
	if !ok {
		return 0, fmt.Errorf("trailing backslash")
	}
	p.pos++
	switch c {
	case 'd', 'D', 'w', 'W', 's', 'S':
		return escPred, nil
	case '0':
		// The Lean parser reads \0 as NUL and any following digits as
		// literals; RE2 reads multi-digit octal (\012 = \n). Reject the
		// divergent shape.
		if c1, ok := p.peek(0); ok && c1 >= '0' && c1 <= '9' {
			return 0, fmt.Errorf("unsupported octal escape")
		}
		return escChar, nil
	case 'n', 't', 'r', 'f', 'v', 'a':
		return escChar, nil
	case 'x':
		if c1, ok := p.peek(0); ok && c1 == '{' {
			p.pos++
			n, digits := 0, 0
			for {
				ch, ok := p.peek(0)
				if !ok {
					return 0, fmt.Errorf("unterminated \\x{...} escape")
				}
				if ch == '}' {
					p.pos++
					break
				}
				v, isHex := hexVal(ch)
				if !isHex {
					return 0, fmt.Errorf("invalid \\x{...} escape")
				}
				if n < 0x110000 {
					n = n*16 + v
				}
				digits++
				p.pos++
			}
			_ = digits // zero digits fold to 0 (NUL), matching the Lean parser
			if !isValidChar(n) {
				return 0, fmt.Errorf("invalid \\x{...} escape")
			}
			return escChar, nil
		}
		h1, ok1 := p.peek(0)
		h2, ok2 := p.peek(1)
		if !ok1 || !ok2 {
			return 0, fmt.Errorf("truncated \\x escape")
		}
		v1, hex1 := hexVal(h1)
		v2, hex2 := hexVal(h2)
		if !hex1 || !hex2 {
			return 0, fmt.Errorf("invalid \\xHH escape")
		}
		_ = v1
		_ = v2
		p.pos += 2
		return escChar, nil
	default:
		if unicode.IsLetter(c) || unicode.IsDigit(c) {
			return 0, fmt.Errorf("unsupported escape \\%c", c)
		}
		return escChar, nil
	}
}

// classItems mirrors Parser.classItems/classRange: the interior of a
// character class after '[' and an optional '^'. first admits ']' as a
// literal.
func (p *reParser) classItems(first bool) error {
	for {
		c, ok := p.peek(0)
		if !ok {
			return fmt.Errorf("unterminated character class")
		}
		switch {
		case c == ']' && !first:
			p.pos++
			return nil
		case c == ']': // first position: a literal in the Lean parser
			// RE2 would let this literal start a range ("[]-a]"); the Lean
			// parser would not — reject the divergent shape.
			if c1, ok := p.peek(1); ok && c1 == '-' {
				if c2, ok := p.peek(2); ok && c2 != ']' {
					return fmt.Errorf("unsupported ']' as range start")
				}
			}
			p.pos++
		case c == '[':
			// The Lean parser reads '[' as a literal inside a class; RE2 would
			// read "[:name:]" as a POSIX class — reject the divergence.
			if c1, ok := p.peek(1); ok && c1 == ':' {
				return fmt.Errorf("unsupported POSIX named class")
			}
			p.pos++
			if err := p.classRange(); err != nil {
				return err
			}
		case c == '\\':
			p.pos++
			kind, err := p.escape()
			if err != nil {
				return err
			}
			if kind == escChar {
				if err := p.classRange(); err != nil {
					return err
				}
			}
		default:
			p.pos++
			if err := p.classRange(); err != nil {
				return err
			}
		}
		first = false
	}
}

// classRange mirrors Parser.classRange: after a literal class element, either
// the high end of a range or nothing.
func (p *reParser) classRange() error {
	c, ok := p.peek(0)
	if !ok || c != '-' {
		return nil
	}
	c1, ok1 := p.peek(1)
	if !ok1 {
		return nil // "[a-" fails later as unterminated
	}
	switch c1 {
	case ']':
		// Trailing '-' is a literal; leave it for classItems.
		return nil
	case '\\':
		p.pos += 2
		kind, err := p.escape()
		if err != nil {
			return err
		}
		if kind == escPred {
			return fmt.Errorf("invalid range endpoint")
		}
		return nil
	default:
		p.pos += 2
		return nil
	}
}

func (p *reParser) parseClass() error {
	if c, ok := p.peek(0); ok && c == '^' {
		p.pos++
	}
	return p.classItems(true)
}

func (p *reParser) parseAlt() error {
	if err := p.parseConcat(); err != nil {
		return err
	}
	for {
		c, ok := p.peek(0)
		if !ok || c != '|' {
			return nil
		}
		p.pos++
		if err := p.parseConcat(); err != nil {
			return err
		}
	}
}

func (p *reParser) parseConcat() error {
	for {
		c, ok := p.peek(0)
		if !ok || c == '|' || c == ')' {
			return nil
		}
		if err := p.parseRepeat(); err != nil {
			return err
		}
	}
}

func (p *reParser) parseRepeat() error {
	if err := p.parseAtom(); err != nil {
		return err
	}
	return p.quantify()
}

// quantify mirrors Parser.quantify: any run of * + ? {n} {n,} {n,m}, each
// optionally followed by a non-greedy '?', bounds capped at 512.
func (p *reParser) quantify() error {
	const maxBound = 512
	for {
		c, ok := p.peek(0)
		if !ok {
			return nil
		}
		switch c {
		case '*', '+', '?':
			p.pos++
			p.nonGreedy()
		case '{':
			n, digits, next := p.scanNat(p.pos + 1)
			if digits == 0 {
				return nil // '{' without bounds is a literal, handled by parseAtom next round
			}
			if c1, ok := p.at(next); ok && c1 == '}' {
				if n > maxBound {
					return fmt.Errorf("repetition bound too large")
				}
				p.pos = next + 1
				p.nonGreedy()
				continue
			}
			c1, ok := p.at(next)
			if !ok || c1 != ',' {
				return fmt.Errorf("unterminated repetition")
			}
			next++
			if c2, ok := p.at(next); ok && c2 == '}' {
				if n > maxBound {
					return fmt.Errorf("repetition bound too large")
				}
				p.pos = next + 1
				p.nonGreedy()
				continue
			}
			m, _, next2 := p.scanNat(next)
			if c2, ok := p.at(next2); !ok || c2 != '}' {
				return fmt.Errorf("unterminated repetition")
			}
			if m > maxBound || m < n {
				return fmt.Errorf("invalid repetition bounds")
			}
			p.pos = next2 + 1
			p.nonGreedy()
		default:
			return nil
		}
	}
}

func (p *reParser) nonGreedy() {
	if c, ok := p.peek(0); ok && c == '?' {
		p.pos++
	}
}

func (p *reParser) at(i int) (rune, bool) {
	if i < len(p.rs) {
		return p.rs[i], true
	}
	return 0, false
}

// scanNat reads a digit run starting at i, returning the (capped) value, the
// number of digits, and the index after the run.
func (p *reParser) scanNat(i int) (val, digits, next int) {
	for i < len(p.rs) && p.rs[i] >= '0' && p.rs[i] <= '9' {
		if val < 1<<20 {
			val = val*10 + int(p.rs[i]-'0')
		}
		digits++
		i++
	}
	return val, digits, i
}

func (p *reParser) parseAtom() error {
	c, ok := p.peek(0)
	if !ok {
		return fmt.Errorf("expected atom")
	}
	switch c {
	case '(':
		p.pos++
		if c1, ok := p.peek(0); ok && c1 == '?' {
			if c2, ok := p.peek(1); ok && c2 == ':' {
				p.pos += 2
			} else {
				return fmt.Errorf("unsupported (?...) group")
			}
		}
		if err := p.parseAlt(); err != nil {
			return err
		}
		if c1, ok := p.peek(0); !ok || c1 != ')' {
			return fmt.Errorf("unterminated group")
		}
		p.pos++
		return nil
	case '[':
		p.pos++
		return p.parseClass()
	case '\\':
		p.pos++
		_, err := p.escape()
		return err
	case '*', '+', '?':
		return fmt.Errorf("quantifier without operand")
	default: // includes '.', '^', '$' and ordinary characters
		p.pos++
		return nil
	}
}
