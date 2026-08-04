package leanvalidate

// Path-attribute resolution: the celtolean translation is deliberately
// type-free, but several constructs need proto-descriptor knowledge to render
// soundly — enum-typed values (CEL compares enums as ints; the generated
// inductive needs its .toInt32 view), map selection sugar (m.key must become
// guarded indexing), and the numeric domain of scalar values (which fixes the
// Lean type a literal elaborates against, and the width CEL arithmetic is
// performed at). The plugin resolves every `this`-rooted select path of a rule
// against the descriptors and hands the classification to the translator via
// celtolean.Options.PathAttrs.
//
// Unknown field names along a path are left unclassified: heads are already
// rejected (ThisFields) or surface as Lean elaboration errors on the base
// types, exactly as before. Selecting *through* an enum-typed field is
// impossible in CEL and rejected here with a source-located error.

import (
	"fmt"
	"sort"
	"strings"

	"google.golang.org/protobuf/reflect/protoreflect"

	"github.com/petersonbill64/protovalidate-lean/celtolean"
)

// pathAttrsForMessage classifies the select paths of a message-level rule.
func pathAttrsForMessage(msg protoreflect.MessageDescriptor, cel string) (map[string]celtolean.PathAttr, error) {
	paths, err := celtolean.SelectPaths(cel)
	if err != nil {
		return nil, err
	}
	return resolvePaths(paths, resolveNode{msg: msg})
}

// pathAttrsForField classifies `this` (and any deeper selects) for a
// field-level rule: this denotes the field value.
func pathAttrsForField(fd protoreflect.FieldDescriptor, cel string) (map[string]celtolean.PathAttr, error) {
	paths, err := celtolean.SelectPaths(cel)
	if err != nil {
		return nil, err
	}
	switch {
	case fd.IsMap():
		attrs, err := resolvePaths(paths, resolveNode{container: fd})
		if err != nil {
			return nil, err
		}
		if attrs == nil {
			attrs = map[string]celtolean.PathAttr{}
		}
		attrs[""] = celtolean.PathMapSelect
		return attrs, nil
	case fd.IsList():
		// Selects on a list value are a CEL type error, but its elements are
		// reachable through comprehensions and indexing.
		return resolvePaths(paths, resolveNode{container: fd})
	case fd.Kind() == protoreflect.EnumKind:
		if len(paths) > 0 {
			return nil, fmt.Errorf("cannot select fields of the enum-typed value `this`")
		}
		return map[string]celtolean.PathAttr{"": celtolean.PathEnumInt}, nil
	case fd.Kind() == protoreflect.MessageKind || fd.Kind() == protoreflect.GroupKind:
		return resolvePaths(paths, resolveNode{msg: fd.Message()})
	default:
		if a, ok := numericAttr[fd.Kind()]; ok {
			return map[string]celtolean.PathAttr{"": a}, nil
		}
		return nil, nil
	}
}

// pathAttrsForElement classifies `this` for element-level rules
// (repeated.items / map.keys / map.values custom CEL).
func pathAttrsForElement(elem protoreflect.FieldDescriptor) map[string]celtolean.PathAttr {
	if elem == nil {
		return nil
	}
	if elem.Kind() == protoreflect.EnumKind {
		return map[string]celtolean.PathAttr{"": celtolean.PathEnumInt}
	}
	if a, ok := numericAttr[elem.Kind()]; ok {
		return map[string]celtolean.PathAttr{"": a}
	}
	return nil
}

// numericAttr maps a proto scalar kind to the numeric domain the translator
// range-checks literals against (and widens 32-bit arithmetic out of).
var numericAttr = map[protoreflect.Kind]celtolean.PathAttr{
	protoreflect.Int32Kind:    celtolean.PathInt32,
	protoreflect.Sint32Kind:   celtolean.PathInt32,
	protoreflect.Sfixed32Kind: celtolean.PathInt32,
	protoreflect.Int64Kind:    celtolean.PathInt64,
	protoreflect.Sint64Kind:   celtolean.PathInt64,
	protoreflect.Sfixed64Kind: celtolean.PathInt64,
	protoreflect.Uint32Kind:   celtolean.PathUInt32,
	protoreflect.Fixed32Kind:  celtolean.PathUInt32,
	protoreflect.Uint64Kind:   celtolean.PathUInt64,
	protoreflect.Fixed64Kind:  celtolean.PathUInt64,
	protoreflect.FloatKind:    celtolean.PathFloat,
	protoreflect.DoubleKind:   celtolean.PathDouble,
}

// resolveNode is a position while walking a path: either a message, or a
// container field (a repeated field, or a map — whose next path component is
// a literal key, `[]` for its keys, or `[*]` for its values).
type resolveNode struct {
	msg       protoreflect.MessageDescriptor
	container protoreflect.FieldDescriptor
}

// pathComps splits a path into components: field names / map keys, plus the
// container descents `[]` (iteration element) and `[*]` (index result), which
// attach without a dot (`items[].qty`).
func pathComps(p string) []string {
	var out []string
	for i := 0; i < len(p); {
		switch p[i] {
		case '.':
			i++
		case '[':
			j := strings.IndexByte(p[i:], ']')
			if j < 0 {
				return append(out, p[i:])
			}
			out = append(out, p[i:i+j+1])
			i += j + 1
		default:
			j := strings.IndexAny(p[i:], ".[")
			if j < 0 {
				return append(out, p[i:])
			}
			out = append(out, p[i:i+j])
			i += j
		}
	}
	return out
}

// joinPath appends a component to a path prefix the way celtolean spells it.
func joinPath(prefix, comp string) string {
	if strings.HasPrefix(comp, "[") {
		return prefix + comp
	}
	if prefix == "" {
		return comp
	}
	return prefix + "." + comp
}

// stepValue classifies the value a field descriptor denotes and returns the
// position to continue the walk from. asElement views a repeated field as one
// of its elements (reached through `[]` / `[*]`) rather than as the container.
func stepValue(fd protoreflect.FieldDescriptor, asElement bool) (celtolean.PathAttr, resolveNode) {
	if !asElement && fd.IsMap() {
		return celtolean.PathMapSelect, resolveNode{container: fd}
	}
	if !asElement && fd.IsList() {
		return 0, resolveNode{container: fd}
	}
	switch fd.Kind() {
	case protoreflect.MessageKind, protoreflect.GroupKind:
		return 0, resolveNode{msg: fd.Message()}
	case protoreflect.EnumKind:
		return celtolean.PathEnumInt, resolveNode{}
	default:
		return numericAttr[fd.Kind()], resolveNode{}
	}
}

func resolvePaths(paths map[string]bool, start resolveNode) (map[string]celtolean.PathAttr, error) {
	if len(paths) == 0 {
		return nil, nil
	}
	sorted := make([]string, 0, len(paths))
	for p := range paths {
		sorted = append(sorted, p)
	}
	sort.Strings(sorted)

	attrs := map[string]celtolean.PathAttr{}
	for _, path := range sorted {
		comps := pathComps(path)
		node := start
		prefix := ""
		for i, comp := range comps {
			last := i == len(comps)-1
			withComp := joinPath(prefix, comp)

			// The field descriptor of the value this component denotes.
			var fd protoreflect.FieldDescriptor
			asElement := false
			switch {
			case node.container != nil:
				c := node.container
				switch {
				case comp == "[]":
					// Iteration: a repeated field's elements, a map's keys.
					if c.IsMap() {
						fd = c.MapKey()
					} else {
						fd, asElement = c, true
					}
				case comp == "[*]":
					// Indexing: a repeated field's elements, a map's values.
					if c.IsMap() {
						fd = c.MapValue()
					} else {
						fd, asElement = c, true
					}
				case c.IsMap():
					fd = c.MapValue() // selection sugar: comp is a literal key
				}
			case node.msg != nil && !strings.HasPrefix(comp, "["):
				fd = node.msg.Fields().ByName(protoreflect.Name(comp))
			}
			if fd == nil {
				// Unknown field, or a descent CEL itself rejects (indexing a
				// message, selecting a field of a list). Left unclassified:
				// head checks and Lean elaboration cover those.
				break
			}

			attr, next := stepValue(fd, asElement)
			if attr == celtolean.PathEnumInt && !last {
				return nil, fmt.Errorf("path this.%s selects through the enum-typed field %q", path, comp)
			}
			// Map fields are marked wherever they occur (the selection sugar
			// fires on intermediate hops); everything else only as a leaf.
			if attr != 0 && (last || attr == celtolean.PathMapSelect) {
				attrs[withComp] = attr
			}
			if next.msg == nil && next.container == nil && !last {
				break // scalar leaf selected further: CEL type error
			}
			node = next
			prefix = withComp
		}
	}
	if len(attrs) == 0 {
		return nil, nil
	}
	return attrs, nil
}
