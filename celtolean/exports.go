package celtolean

// Helpers exported for the protoc plugin (protoc-gen-lean-protovalidate),
// which composes emitted expressions into full declarations and needs the
// same lexical conventions the translator uses.

import (
	"github.com/google/cel-go/common/ast"
	"github.com/google/cel-go/common/operators"
)

// LeanIdent renders a proto-derived name component as a Lean identifier,
// guillemet-quoting reserved words.
func LeanIdent(name string) string { return leanIdent(name) }

// LeanString renders s as a Lean string literal.
func LeanString(s string) string { return leanString(s) }

// PathAttrForKind resolves a proto scalar-kind name ("int32", "uint64",
// "float", "enum", ...) to the PathAttr carrying its numeric domain. The
// corpus driver uses it to state a row's field type the way the plugin's
// descriptor walk would.
func PathAttrForKind(name string) (PathAttr, bool) {
	a, ok := map[string]PathAttr{
		"enum":     PathEnumInt,
		"int32":    PathInt32,
		"sint32":   PathInt32,
		"sfixed32": PathInt32,
		"int64":    PathInt64,
		"sint64":   PathInt64,
		"sfixed64": PathInt64,
		"uint32":   PathUInt32,
		"fixed32":  PathUInt32,
		"uint64":   PathUInt64,
		"fixed64":  PathUInt64,
		"float":    PathFloat,
		"double":   PathDouble,
	}[name]
	return a, ok
}

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
// prefixes), including the container descents `IterElem`/`IndexElem` name:
// a comprehension binder and an indexed element are values the plugin must
// type too. The plugin resolves these against the proto descriptors to build
// Options.PathAttrs (enum integer views, map selection sugar, numeric
// domains).
func SelectPaths(cel string) (map[string]bool, error) {
	root, err := parseCEL(cel)
	if err != nil {
		return nil, err
	}
	out := map[string]bool{}
	collectSelectPaths(root, map[string]string{}, out)
	return out, nil
}

// collectSelectPaths walks e under `env`, which maps comprehension variables
// in scope to the path of the value they range over.
func collectSelectPaths(e ast.Expr, env map[string]string, out map[string]bool) {
	lookup := func(name string) (string, bool) { p, ok := env[name]; return p, ok }
	record := func(x ast.Expr) {
		if p, ok := celPath(x, lookup); ok && p != "" {
			out[p] = true
		}
	}
	switch e.Kind() {
	case ast.SelectKind:
		record(e)
	case ast.CallKind:
		c := e.AsCall()
		// Indexing yields a value whose type the plugin must supply.
		if !c.IsMemberFunction() && c.FunctionName() == operators.Index && len(c.Args()) == 2 {
			record(e)
		}
		// A comprehension binds its variable to the receiver's elements; walk
		// the body with that binding so paths through it resolve.
		if v, recv, body, ok := comprehension(c); ok {
			collectSelectPaths(recv, env, out)
			inner := env
			if p, known := celPath(recv, lookup); known {
				elem := IterElem(p)
				out[elem] = true
				inner = make(map[string]string, len(env)+1)
				for k, val := range env {
					inner[k] = val
				}
				inner[v] = elem
			} else if _, shadowed := env[v]; shadowed {
				inner = make(map[string]string, len(env))
				for k, val := range env {
					inner[k] = val
				}
				delete(inner, v)
			}
			for _, a := range body {
				collectSelectPaths(a, inner, out)
			}
			return
		}
	}
	switch e.Kind() {
	case ast.SelectKind:
		collectSelectPaths(e.AsSelect().Operand(), env, out)
	case ast.CallKind:
		c := e.AsCall()
		if c.IsMemberFunction() {
			collectSelectPaths(c.Target(), env, out)
		}
		for _, a := range c.Args() {
			collectSelectPaths(a, env, out)
		}
	case ast.ListKind:
		for _, el := range e.AsList().Elements() {
			collectSelectPaths(el, env, out)
		}
	case ast.MapKind:
		for _, entry := range e.AsMap().Entries() {
			me := entry.AsMapEntry()
			collectSelectPaths(me.Key(), env, out)
			collectSelectPaths(me.Value(), env, out)
		}
	case ast.StructKind:
		for _, f := range e.AsStruct().Fields() {
			collectSelectPaths(f.AsStructField().Value(), env, out)
		}
	case ast.ComprehensionKind:
		co := e.AsComprehension()
		collectSelectPaths(co.IterRange(), env, out)
		collectSelectPaths(co.AccuInit(), env, out)
		collectSelectPaths(co.LoopCondition(), env, out)
		collectSelectPaths(co.LoopStep(), env, out)
		collectSelectPaths(co.Result(), env, out)
	}
}

// comprehension recognizes the CEL macros that bind an iteration variable
// (parsed as ordinary calls, since macro expansion is disabled), returning the
// variable, the receiver it ranges over, and the sub-expressions in its scope.
func comprehension(c ast.CallExpr) (v string, recv ast.Expr, body []ast.Expr, ok bool) {
	if !c.IsMemberFunction() {
		return "", nil, nil, false
	}
	switch c.FunctionName() {
	case "all", "exists", "exists_one", "existsOne", "filter":
		if len(c.Args()) != 2 {
			return "", nil, nil, false
		}
	case "map":
		if len(c.Args()) != 2 && len(c.Args()) != 3 {
			return "", nil, nil, false
		}
	default:
		return "", nil, nil, false
	}
	args := c.Args()
	if args[0].Kind() != ast.IdentKind {
		return "", nil, nil, false
	}
	return args[0].AsIdent(), c.Target(), args[1:], true
}
