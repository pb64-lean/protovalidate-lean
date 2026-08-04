package celtolean

// Helpers exported for the protoc plugin (protoc-gen-lean-protovalidate),
// which composes emitted expressions into full declarations and needs the
// same lexical conventions the translator uses.

import "github.com/google/cel-go/common/ast"

// LeanIdent renders a proto-derived name component as a Lean identifier,
// guillemet-quoting reserved words.
func LeanIdent(name string) string { return leanIdent(name) }

// LeanString renders s as a Lean string literal.
func LeanString(s string) string { return leanString(s) }

// Idents parses a CEL expression and returns every identifier occurring in
// it (free identifiers and comprehension variables alike). Codegen uses this
// to choose binder names that can neither collide nor capture.
func Idents(cel string) (map[string]bool, error) {
	root, err := parseCEL(cel)
	if err != nil {
		return nil, err
	}
	out := map[string]bool{}
	collectIdents(root, out)
	return out, nil
}

// SelectPaths parses a CEL expression and returns every dotted field path
// rooted at `this` occurring in it (full chains; walking a chain visits its
// prefixes). The plugin resolves these against the proto descriptors to build
// Options.PathAttrs (enum integer views, map selection sugar).
func SelectPaths(cel string) (map[string]bool, error) {
	root, err := parseCEL(cel)
	if err != nil {
		return nil, err
	}
	out := map[string]bool{}
	collectSelectPaths(root, out)
	return out, nil
}

func collectSelectPaths(e ast.Expr, out map[string]bool) {
	if e.Kind() == ast.SelectKind {
		if p, ok := celPath(e); ok && p != "" {
			out[p] = true
		}
	}
	switch e.Kind() {
	case ast.SelectKind:
		collectSelectPaths(e.AsSelect().Operand(), out)
	case ast.CallKind:
		c := e.AsCall()
		if c.IsMemberFunction() {
			collectSelectPaths(c.Target(), out)
		}
		for _, a := range c.Args() {
			collectSelectPaths(a, out)
		}
	case ast.ListKind:
		for _, el := range e.AsList().Elements() {
			collectSelectPaths(el, out)
		}
	case ast.MapKind:
		for _, entry := range e.AsMap().Entries() {
			me := entry.AsMapEntry()
			collectSelectPaths(me.Key(), out)
			collectSelectPaths(me.Value(), out)
		}
	case ast.StructKind:
		for _, f := range e.AsStruct().Fields() {
			collectSelectPaths(f.AsStructField().Value(), out)
		}
	case ast.ComprehensionKind:
		co := e.AsComprehension()
		collectSelectPaths(co.IterRange(), out)
		collectSelectPaths(co.AccuInit(), out)
		collectSelectPaths(co.LoopCondition(), out)
		collectSelectPaths(co.LoopStep(), out)
		collectSelectPaths(co.Result(), out)
	}
}
