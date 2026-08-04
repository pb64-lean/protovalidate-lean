package celtolean

// formatprobe.go is the `Cel.Format` counterpart of regexprobe.go.
//
// `Protovalidate.Cel.Format` hand-implements protovalidate's well-known string
// formats (email, hostname, ip, uri, ...) from their RFC grammars. Nothing in
// the pipeline cross-checks those grammars against protovalidate, so a
// divergence would be silent — the same failure mode the regex battery exists
// to prevent.
//
// The oracle here is upstream protovalidate's own **conformance suite**
// (`tools/protovalidate-conformance/internal/cases/cases_is_*.go` and
// `cases_strings.go` in the `protovalidate` module this build already depends
// on): the normative, implementation-independent expectations every
// protovalidate runtime must satisfy. cmd/formatcorpus extracts them into
// Test/format_corpus.tsv; the same tool renders each row as a `#guard` the
// Lean engine re-decides at elaboration time, so a disagreement with
// protovalidate on any extracted case fails the build.
//
// This is differential testing against a finite corpus, not a proof that
// `Cel.Format` implements the RFCs or agrees with protovalidate everywhere
// (see README).

import (
	"bufio"
	"fmt"
	"io"
	"strconv"
	"strings"
)

// UUIDPattern and TUUIDPattern are the regexes protovalidate's `string.uuid` /
// `string.tuuid` rules denote. They live here so the corpus battery and the
// rule lowering (leanvalidate) cannot drift apart.
const (
	UUIDPattern  = "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
	TUUIDPattern = "^[0-9a-fA-F]{32}$"
)

// FormatProbe is one differential test point: Accept is what protovalidate's
// conformance suite requires for Input under Format.
type FormatProbe struct {
	// Format is a fully-applied format predicate written as
	// `name[:arg]*`, mirroring the CEL call it stands for: `email`,
	// `ip:4`, `ip_prefix:6:true`, `host_and_port:false`, ... See FormatCall.
	Format string
	Input  string
	Accept bool
	// Case is the upstream conformance case name, kept for provenance so a
	// failing guard points back at the case that labelled it.
	Case string
}

// FormatNames lists the format vocabulary (the `name` part of a Format key).
var FormatNames = []string{
	"address", "email", "host_and_port", "hostname", "ip", "ip_prefix",
	"tuuid", "uri", "uri_ref", "uuid",
}

// FormatCall renders the Lean Bool expression deciding `format` on `input`.
//
// The expressions are exactly what codegen emits: the `String.*` wrappers for
// the CEL library functions (so an argument-order slip in a wrapper is caught
// too), the `isHostname || isIp` disjunction `string.address` lowers to, and
// the `Cel.regexMatch` calls `string.uuid` / `string.tuuid` lower to.
func FormatCall(format, input string) (string, error) {
	lit := leanString(input)
	parts := strings.Split(format, ":")
	name, args := parts[0], parts[1:]
	arity := func(n int) error {
		if len(args) != n {
			return fmt.Errorf("format %q: want %d argument(s), got %d", format, n, len(args))
		}
		return nil
	}
	intArg := func(a string) error {
		if _, err := strconv.Atoi(a); err != nil {
			return fmt.Errorf("format %q: %q is not an integer version", format, a)
		}
		return nil
	}
	boolArg := func(a string) error {
		if a != "true" && a != "false" {
			return fmt.Errorf("format %q: %q is not a bool", format, a)
		}
		return nil
	}
	switch name {
	case "email", "hostname", "uri", "uri_ref":
		if err := arity(0); err != nil {
			return "", err
		}
		return lit + "." + map[string]string{
			"email": "isEmail", "hostname": "isHostname",
			"uri": "isUri", "uri_ref": "isUriRef",
		}[name], nil
	case "address":
		// What `string.address` lowers to: a hostname or an IP address.
		if err := arity(0); err != nil {
			return "", err
		}
		return "(" + lit + ".isHostname || " + lit + ".isIp)", nil
	case "ip":
		switch len(args) {
		case 0:
			return lit + ".isIp", nil
		case 1:
			if err := intArg(args[0]); err != nil {
				return "", err
			}
			return lit + ".isIp " + args[0], nil
		}
		return "", fmt.Errorf("format %q: isIp takes at most one argument", format)
	case "ip_prefix":
		switch len(args) {
		case 0:
			return lit + ".isIpPrefix", nil
		case 1:
			// CEL overloads a lone bool as `strict`, keeping version at 0.
			if args[0] == "true" || args[0] == "false" {
				return lit + ".isIpPrefix 0 " + args[0], nil
			}
			if err := intArg(args[0]); err != nil {
				return "", err
			}
			return lit + ".isIpPrefix " + args[0], nil
		case 2:
			if err := intArg(args[0]); err != nil {
				return "", err
			}
			if err := boolArg(args[1]); err != nil {
				return "", err
			}
			return lit + ".isIpPrefix " + args[0] + " " + args[1], nil
		}
		return "", fmt.Errorf("format %q: isIpPrefix takes at most two arguments", format)
	case "host_and_port":
		if err := arity(1); err != nil {
			return "", err
		}
		if err := boolArg(args[0]); err != nil {
			return "", err
		}
		return lit + ".isHostAndPort " + args[0], nil
	case "uuid", "tuuid":
		if err := arity(0); err != nil {
			return "", err
		}
		pattern := UUIDPattern
		if name == "tuuid" {
			pattern = TUUIDPattern
		}
		return "Cel.regexMatch " + lit + " " + leanString(pattern), nil
	}
	return "", fmt.Errorf("unknown format %q (known: %s)", format, strings.Join(FormatNames, ", "))
}

// FormatProbeGuard renders one probe as a compile-time `#guard`: the Lean
// engine must answer exactly what protovalidate's conformance suite requires.
func FormatProbeGuard(p FormatProbe) (string, error) {
	call, err := FormatCall(p.Format, p.Input)
	if err != nil {
		return "", err
	}
	if p.Accept {
		return "#guard " + call, nil
	}
	return "#guard !(" + call + ")", nil
}

// WriteFormatCorpus renders probes as the corpus TSV: format, expected
// acceptance, the input as a Go-quoted literal (so leading/trailing space,
// tabs and non-ASCII survive a line-oriented format), and the upstream case
// name.
func WriteFormatCorpus(w io.Writer, probes []FormatProbe) error {
	for _, p := range probes {
		if _, err := FormatCall(p.Format, p.Input); err != nil {
			return err
		}
		if _, err := fmt.Fprintf(w, "%s\t%t\t%s\t%s\n",
			p.Format, p.Accept, strconv.Quote(p.Input), p.Case); err != nil {
			return err
		}
	}
	return nil
}

// ParseFormatCorpus reads the TSV written by WriteFormatCorpus. Blank lines
// and `#` comments are ignored.
func ParseFormatCorpus(r io.Reader) ([]FormatProbe, error) {
	var out []FormatProbe
	sc := bufio.NewScanner(r)
	sc.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	for line := 1; sc.Scan(); line++ {
		text := sc.Text()
		if strings.TrimSpace(text) == "" || strings.HasPrefix(text, "#") {
			continue
		}
		fields := strings.Split(text, "\t")
		if len(fields) != 4 {
			return nil, fmt.Errorf("line %d: want 4 tab-separated fields, got %d", line, len(fields))
		}
		accept, err := strconv.ParseBool(fields[1])
		if err != nil {
			return nil, fmt.Errorf("line %d: bad acceptance %q: %w", line, fields[1], err)
		}
		input, err := strconv.Unquote(fields[2])
		if err != nil {
			return nil, fmt.Errorf("line %d: bad input literal %q: %w", line, fields[2], err)
		}
		p := FormatProbe{Format: fields[0], Input: input, Accept: accept, Case: fields[3]}
		if _, err := FormatCall(p.Format, p.Input); err != nil {
			return nil, fmt.Errorf("line %d: %w", line, err)
		}
		out = append(out, p)
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	return out, nil
}
