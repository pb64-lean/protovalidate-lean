package celtolean

// Helpers exported for the protoc plugin (protoc-gen-lean-protovalidate),
// which composes emitted expressions into full declarations and needs the
// same lexical conventions the translator uses.

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
