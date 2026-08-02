module

public import Protovalidate.Cel.Regex
public import Protovalidate.Cel.Format
public import Protovalidate.Cel.Time

/-!
Runtime shims backing the Lean expressions emitted by `cel2lean`.

The translator maps CEL operators and library calls onto core Lean wherever a
counterpart exists (`&&` → `∧`, `size()` → `.size`, `startsWith` →
`String.startsWith`, ...). This module supplies the remainder:

* dot-notation extensions where core Lean lacks the CEL name for a base type
  (`String.size`, `Array.Nodup`, `ByteArray.startsWith`, `String.isEmail`, ...);
* `Add` instances mirroring CEL's overloaded `+` (string/list/bytes concat);
* the `Cel` namespace for functions with no dot-notation home: the
  `Cel.Contains` typeclass (CEL `contains` is substring on strings but element
  on lists, and `String.contains` in core is `Char`-based), `Cel.regexMatch`
  (backed by the engine in `Protovalidate.Cel.Regex`), the type conversions,
  and `Cel.Timestamp`/`Cel.Duration` from `Protovalidate.Cel.Time`.
-/

@[expose] public section

/-! ## Dot-notation extensions on core types -/

/-- CEL `size(string)`: the number of Unicode code points (= `String.length`). -/
def String.size (s : String) : Nat := s.length

/-- CEL `size(list)` for `List` (repeated fields are `Array`, covered by core
`Array.size`; this covers list results of intermediate expressions). -/
def List.size (l : List α) : Nat := l.length

/-- CEL `unique()` as the proposition a Lean author would state: pairwise
distinctness of the elements. Mirrors core `List.Nodup` for `Array`
(grpc-lean maps repeated fields to `Array`). -/
def Array.Nodup (xs : Array α) : Prop := xs.toList.Nodup

instance [DecidableEq α] (xs : Array α) : Decidable xs.Nodup :=
  inferInstanceAs (Decidable xs.toList.Nodup)

/-- protovalidate extends CEL `startsWith` to bytes. -/
def ByteArray.startsWith (b pre : ByteArray) : Bool :=
  decide (pre.size ≤ b.size) && b.extract 0 pre.size == pre

/-- protovalidate extends CEL `endsWith` to bytes. -/
def ByteArray.endsWith (b suf : ByteArray) : Bool :=
  decide (suf.size ≤ b.size) && b.extract (b.size - suf.size) b.size == suf

/-- CEL `isInf(sign)`: infinity check restricted by sign (0 matches either). -/
def Float.isInfSign (x : Float) (sign : Int) : Bool :=
  if sign > 0 then x.isInf && decide (x > 0)
  else if sign < 0 then x.isInf && decide (x < 0)
  else x.isInf

/-- CEL `isInf(sign)` for `float` fields (`Float32`). -/
def Float32.isInfSign (x : Float32) (sign : Int) : Bool :=
  if sign > 0 then x.isInf && decide (x > 0)
  else if sign < 0 then x.isInf && decide (x < 0)
  else x.isInf

/-! ## CEL `+` overloads absent from core Lean

CEL `+` concatenates strings, bytes, and lists; Lean core spells these `++`.
Providing homogeneous `Add` instances keeps the translation uniform
(`this + '!'` emits `x + "!"`) and lets the `binop%` elaborator unify literal
element types (`x + #[1]`). -/

instance : Add String := ⟨(· ++ ·)⟩
instance : Add ByteArray := ⟨(· ++ ·)⟩
instance : Add (List α) := ⟨(· ++ ·)⟩
instance : Add (Array α) := ⟨(· ++ ·)⟩

namespace Cel

/-! ## contains -/

/-- CEL `contains` dispatch: substring on `String`/`ByteArray` (protovalidate
extension), element containment on collections. -/
class Contains (γ : Type u) (α : Type v) where
  contains : γ → α → Bool

def contains [Contains γ α] (c : γ) (x : α) : Bool := Contains.contains c x

instance : Contains String String where
  -- splitOn yields > 1 piece iff the (non-empty) pattern occurs.
  contains s pat := pat.isEmpty || (s.splitOn pat).length != 1

instance [BEq α] : Contains (List α) α where
  contains l x := l.contains x

instance [BEq α] : Contains (Array α) α where
  contains l x := l.contains x

instance : Contains ByteArray ByteArray where
  contains h n :=
    n.size == 0 ||
      (decide (n.size ≤ h.size) &&
        (List.range (h.size - n.size + 1)).any fun i => h.extract i (i + n.size) == n)

/-! ## Type conversions (CEL `int()`, `uint()`, `double()`, `bool()`)

CEL's conversions error at runtime on overflow or malformed input; these total
functions wrap (fixed-width conversions) or default (string parses), which is
the usual price of embedding them in propositions. -/

class ToInt (α : Type u) where
  toInt : α → Int64

def toInt [ToInt α] (a : α) : Int64 := ToInt.toInt a

instance : ToInt Int64 := ⟨id⟩
instance : ToInt Int32 := ⟨Int32.toInt64⟩
instance : ToInt UInt32 := ⟨fun x => x.toUInt64.toInt64⟩
instance : ToInt UInt64 := ⟨UInt64.toInt64⟩
instance : ToInt Float := ⟨Float.toInt64⟩
instance : ToInt String := ⟨fun s => (s.toInt? |>.map (Int64.ofInt)).getD 0⟩

class ToUInt (α : Type u) where
  toUInt : α → UInt64

def toUInt [ToUInt α] (a : α) : UInt64 := ToUInt.toUInt a

instance : ToUInt UInt64 := ⟨id⟩
instance : ToUInt UInt32 := ⟨UInt32.toUInt64⟩
instance : ToUInt Int32 := ⟨fun x => x.toInt64.toUInt64⟩
instance : ToUInt Int64 := ⟨Int64.toUInt64⟩
instance : ToUInt Float := ⟨Float.toUInt64⟩

class ToDouble (α : Type u) where
  toDouble : α → Float

def toDouble [ToDouble α] (a : α) : Float := ToDouble.toDouble a

instance : ToDouble Float := ⟨id⟩
instance : ToDouble Float32 := ⟨Float32.toFloat⟩
instance : ToDouble Int32 := ⟨fun x => x.toInt64.toFloat⟩
instance : ToDouble Int64 := ⟨Int64.toFloat⟩
instance : ToDouble UInt32 := ⟨fun x => x.toUInt64.toFloat⟩
instance : ToDouble UInt64 := ⟨UInt64.toFloat⟩

class ToBool (α : Type u) where
  toBool : α → Bool

def toBool [ToBool α] (a : α) : Bool := ToBool.toBool a

instance : ToBool Bool := ⟨id⟩
instance : ToBool String :=
  ⟨fun s => s == "1" || s == "t" || s == "true" || s == "TRUE" || s == "True"⟩

end Cel

/-! ## protovalidate string predicates (dot notation)

`this.isEmail()` emits `x.isEmail`, so the names live in the `String`
namespace; implementations follow protovalidate's grammars
(`Protovalidate.Cel.Format`). -/

def String.isEmail (s : String) : Bool := Cel.Format.isEmail s
def String.isHostname (s : String) : Bool := Cel.Format.isHostname s
def String.isUri (s : String) : Bool := Cel.Format.isUri s
def String.isUriRef (s : String) : Bool := Cel.Format.isUriRef s
def String.isIp (s : String) (version : Int := 0) : Bool := Cel.Format.isIp s version
def String.isIpPrefix (s : String) (version : Int := 0) (strict : Bool := false) : Bool :=
  Cel.Format.isIpPrefix s version strict
def String.isHostAndPort (s : String) (portRequired : Bool) : Bool :=
  Cel.Format.isHostAndPort s portRequired
