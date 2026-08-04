package celtolean

// Numeric domains: descriptor-derived typing knowledge for `this`-rooted
// paths.
//
// The translation is otherwise type-free, which is sound for everything the
// Lean elaborator can check — except numeric *literals*, which Lean happily
// wraps into the field's fixed-width type (`(3000000000 : Int32)` elaborates
// to -1294967296), and 32-bit arithmetic, which CEL performs in 64 bits while
// Lean's Int32/UInt32 operators wrap.
//
// When the plugin knows a path's proto kind it routes the domain in through
// Options.PathAttrs, and this file supplies the two things that knowledge buys:
//
//   - rangeCheck: a literal outside the domain it will elaborate against is a
//     generation-time error rather than a silently wrapped constant;
//   - widen: proto int32/uint32 values entering arithmetic are lifted to their
//     CEL width (`x.toInt64`), so the Cel.addOk/subOk/mulOk guard is the exact
//     64-bit CEL condition rather than the conservative 32-bit one.

import "fmt"

// numDom is the numeric domain of a proto-typed value: the Lean type its
// occurrences elaborate at, plus the CEL-visible width.
type numDom struct {
	lean     string // Lean type name (for diagnostics)
	proto    string // proto kind family (for diagnostics)
	bits     int
	unsigned bool
	float    bool
}

var (
	domI32 = &numDom{lean: "Int32", proto: "int32", bits: 32}
	domI64 = &numDom{lean: "Int64", proto: "int64", bits: 64}
	domU32 = &numDom{lean: "UInt32", proto: "uint32", bits: 32, unsigned: true}
	domU64 = &numDom{lean: "UInt64", proto: "uint64", bits: 64, unsigned: true}
	domF32 = &numDom{lean: "Float32", proto: "float", bits: 32, float: true}
	domF64 = &numDom{lean: "Float", proto: "double", bits: 64, float: true}
)

// domain is the numeric domain a path attribute implies (nil when the
// attribute carries no numeric typing). Enum-typed values are compared as
// integers through the generated `.toInt32` view, so they inherit Int32.
func (a PathAttr) domain() *numDom {
	switch a {
	case PathEnumInt:
		return domI32
	case PathInt32:
		return domI32
	case PathInt64:
		return domI64
	case PathUInt32:
		return domU32
	case PathUInt64:
		return domU64
	case PathFloat:
		return domF32
	case PathDouble:
		return domF64
	}
	return nil
}

// maxFloat32 is the largest finite Float32; a double literal beyond it rounds
// to an infinity when elaborated against a `float` field.
const maxFloat32 = 3.4028234663852886e+38

func (d *numDom) minInt() int64 {
	if d.unsigned {
		return 0
	}
	return -1 << (d.bits - 1)
}

func (d *numDom) maxInt() int64 {
	if d.unsigned {
		if d.bits >= 64 {
			return -1 // unused: callers compare unsigned values via maxUint
		}
		return int64(1)<<d.bits - 1
	}
	return int64(1)<<(d.bits-1) - 1
}

func (d *numDom) maxUint() uint64 {
	if d.unsigned {
		if d.bits >= 64 {
			return ^uint64(0)
		}
		return uint64(1)<<d.bits - 1
	}
	return uint64(d.maxInt())
}

// accepts reports whether a CEL numeric literal elaborates faithfully against
// this domain. CEL evaluates the comparison at its own (64-bit / double)
// width; Lean elaborates the literal *at the field's type*, so anything
// outside the domain would silently wrap.
func (d *numDom) accepts(n *constNum) error {
	if d == nil || n == nil {
		return nil
	}
	switch n.kind {
	case constInt:
		if d.float {
			return nil // int literal against a float field: widened exactly
		}
		if n.i < 0 && d.unsigned {
			return fmt.Errorf("negative literal %d cannot be represented by the unsigned %s field "+
				"(Lean would elaborate it as %s, wrapping to a large positive value)", n.i, d.proto, d.lean)
		}
		if n.i < d.minInt() || (n.i >= 0 && uint64(n.i) > d.maxUint()) {
			return d.outOfRange(fmt.Sprintf("%d", n.i))
		}
	case constUint:
		if d.float {
			return nil
		}
		if n.u > d.maxUint() {
			return d.outOfRange(fmt.Sprintf("%du", n.u))
		}
	case constDouble:
		if !d.float {
			return nil // double literal against an int field: a CEL type error
		}
		if d.bits == 32 && (n.d > maxFloat32 || n.d < -maxFloat32) {
			return fmt.Errorf("literal %g is outside the finite range of the `float` field's Lean type Float32 "+
				"(±%g); it would elaborate to an infinity, while CEL compares in double precision", n.d, maxFloat32)
		}
	}
	return nil
}

func (d *numDom) outOfRange(lit string) error {
	if d.unsigned {
		return fmt.Errorf("literal %s is outside the domain of the %s value it is used with "+
			"(%s: 0 … %d); CEL compares at 64-bit width, but Lean elaborates the literal at the field's "+
			"type, where it would wrap", lit, d.proto, d.lean, d.maxUint())
	}
	return fmt.Errorf("literal %s is outside the domain of the %s value it is used with "+
		"(%s: %d … %d); CEL compares at 64-bit width, but Lean elaborates the literal at the field's "+
		"type, where it would wrap", lit, d.proto, d.lean, d.minInt(), d.maxInt())
}

// widen lifts a 32-bit proto integer to the width CEL actually computes at, so
// arithmetic on it (and its overflow guard) is CEL-exact instead of
// conservatively 32-bit. Values already at CEL width, floats and untyped
// fragments pass through.
func (t *translator) widen(p piece) piece {
	d := p.dom
	if d == nil || d.float || d.bits != 32 {
		return p
	}
	conv, to := ".toInt64", domI64
	if d.unsigned {
		conv, to = ".toUInt64", domU64
	}
	return piece{
		text:       p.at(precApp+1) + conv,
		prec:       precAtom,
		kind:       p.kind,
		guards:     p.guards,
		noArithErr: p.noArithErr,
		dom:        to,
	}
}

// unifyWidth makes two comparable proto integers elaborate at a common Lean
// type by widening the narrower one (CEL compares int32 and int64 fields
// directly; Lean's fixed-width types would not unify). Mixed signedness is a
// Lean type error either way and is left alone.
func (t *translator) unifyWidth(l, r piece) (piece, piece) {
	if l.dom == nil || r.dom == nil || l.dom == r.dom {
		return l, r
	}
	if l.dom.float != r.dom.float || l.dom.unsigned != r.dom.unsigned {
		return l, r
	}
	if l.dom.float {
		return l, r
	}
	if l.dom.bits < r.dom.bits {
		return t.widen(l), r
	}
	if r.dom.bits < l.dom.bits {
		return l, t.widen(r)
	}
	return l, r
}

// arithDom is the domain of an arithmetic result: the operands' common domain
// (a literal operand carries none and inherits the other's), or unknown when
// they disagree.
func arithDom(l, r piece) *numDom {
	switch {
	case l.dom == nil:
		return r.dom
	case r.dom == nil:
		return l.dom
	case l.dom == r.dom:
		return l.dom
	}
	return nil
}

// checkLiterals rejects numeric literals that fall outside the domain of the
// typed operand they meet. Both directions are checked (`this < 3e9` and
// `3e9 < this`), as are list/map literals on the right of `in`.
func (t *translator) checkLiterals(l, r piece) error {
	for _, pair := range [2][2]piece{{l, r}, {r, l}} {
		v, lit := pair[0], pair[1]
		if v.dom == nil {
			continue
		}
		if err := v.dom.accepts(lit.num); err != nil {
			return err
		}
		for _, n := range lit.nums {
			if err := v.dom.accepts(n); err != nil {
				return err
			}
		}
	}
	return nil
}
