package leanvalidate

// Path-attribute resolution: the celtolean translation is deliberately
// type-free, but two constructs need proto-descriptor knowledge to render
// soundly — enum-typed values (CEL compares enums as ints; the generated
// inductive needs its .toInt32 view) and map selection sugar (m.key must
// become guarded indexing). The plugin resolves every `this`-rooted select
// path of a rule against the descriptors and hands the classification to the
// translator via celtolean.Options.PathAttrs.
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
		attrs, err := resolvePaths(paths, resolveNode{mapVal: fd.MapValue()})
		if err != nil {
			return nil, err
		}
		if attrs == nil {
			attrs = map[string]celtolean.PathAttr{}
		}
		attrs[""] = celtolean.PathMapSelect
		return attrs, nil
	case fd.IsList():
		return nil, nil // selects on a list value are a CEL type error
	case fd.Kind() == protoreflect.EnumKind:
		if len(paths) > 0 {
			return nil, fmt.Errorf("cannot select fields of the enum-typed value `this`")
		}
		return map[string]celtolean.PathAttr{"": celtolean.PathEnumInt}, nil
	case fd.Kind() == protoreflect.MessageKind || fd.Kind() == protoreflect.GroupKind:
		return resolvePaths(paths, resolveNode{msg: fd.Message()})
	default:
		return nil, nil
	}
}

// pathAttrsForElement classifies `this` for element-level rules
// (repeated.items / map.keys / map.values custom CEL).
func pathAttrsForElement(elem protoreflect.FieldDescriptor) map[string]celtolean.PathAttr {
	if elem != nil && elem.Kind() == protoreflect.EnumKind {
		return map[string]celtolean.PathAttr{"": celtolean.PathEnumInt}
	}
	return nil
}

// resolveNode is a position while walking a path: either a message, or the
// value slot of a map (the next path component is a literal key).
type resolveNode struct {
	msg    protoreflect.MessageDescriptor
	mapVal protoreflect.FieldDescriptor
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
		comps := strings.Split(path, ".")
		node := start
		prefix := ""
		for i, comp := range comps {
			withComp := comp
			if prefix != "" {
				withComp = prefix + "." + comp
			}
			last := i == len(comps)-1

			if node.mapVal != nil {
				// comp is a map key; the value type continues the walk.
				vd := node.mapVal
				node = resolveNode{}
				switch vd.Kind() {
				case protoreflect.MessageKind, protoreflect.GroupKind:
					node = resolveNode{msg: vd.Message()}
				case protoreflect.EnumKind:
					if last {
						attrs[withComp] = celtolean.PathEnumInt
					}
				}
				if node.msg == nil && !last {
					break // scalar map value selected further: CEL type error
				}
				prefix = withComp
				continue
			}
			if node.msg == nil {
				break
			}
			f := node.msg.Fields().ByName(protoreflect.Name(comp))
			if f == nil {
				break // unknown field: handled by head checks / Lean elaboration
			}
			node = resolveNode{}
			switch {
			case f.IsMap():
				attrs[withComp] = celtolean.PathMapSelect
				if !last {
					node = resolveNode{mapVal: f.MapValue()}
				}
			case f.IsList():
				if !last {
					// selecting through a list value: CEL type error
				}
			case f.Kind() == protoreflect.EnumKind:
				if last {
					attrs[withComp] = celtolean.PathEnumInt
				} else {
					return nil, fmt.Errorf("path this.%s selects through the enum-typed field %q", path, comp)
				}
			case f.Kind() == protoreflect.MessageKind || f.Kind() == protoreflect.GroupKind:
				node = resolveNode{msg: f.Message()}
			}
			if node.msg == nil && node.mapVal == nil && !last {
				break
			}
			prefix = withComp
		}
	}
	if len(attrs) == 0 {
		return nil, nil
	}
	return attrs, nil
}
