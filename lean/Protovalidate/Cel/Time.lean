module

public import Protobuf.WellKnown

/-!
Timestamps and durations for CEL propositions.

`Cel.Timestamp`/`Cel.Duration` are the grpc-lean generated well-known types
(`google.protobuf.Timestamp`/`Duration` from `Protobuf.WellKnown`), so CEL
rules on WKT-typed message fields and folded `timestamp('...')` literals
refine the same types the base codegen puts in message structures.

Conventions follow `google.protobuf`: timestamps carry seconds since the Unix
epoch with non-negative nanos in `[0, 10^9)` (seconds floored); durations
carry seconds and nanos with matching signs (truncated toward zero).
Comparisons and arithmetic are exact over total nanoseconds and ignore
unknown fields, as does `==` (`BEq`); propositional equality on these
structures is not decidable (they carry an unknown-field map), so prefer
`==`/ordering in rules.

`cel2lean` folds literal `timestamp('...')`/`duration('...')` arguments into
`.mk` constants at codegen time; the parsers here back the non-literal
runtime path (`Cel.timestamp`/`Cel.duration`, defaulting to zero on invalid
input) and can be used directly via the `Option`-returning variants.
-/

@[expose] public section

namespace Cel

/-- CEL's timestamp type: the generated well-known type. -/
abbrev Timestamp := _root_.google.protobuf.Timestamp

/-- CEL's duration type: the generated well-known type. -/
abbrev Duration := _root_.google.protobuf.Duration

/-- Constructor used by folded `timestamp('...')` literals. -/
def Timestamp.mk (seconds : Int64) (nanos : Int32) : Timestamp :=
  { seconds := seconds, nanos := nanos }

/-- Constructor used by folded `duration('...')` literals. -/
def Duration.mk (seconds : Int64) (nanos : Int32) : Duration :=
  { seconds := seconds, nanos := nanos }

end Cel

namespace google.protobuf

def Timestamp.toTotalNanos (t : Timestamp) : Int :=
  t.seconds.toInt * 1000000000 + t.nanos.toInt

/-- Seconds floored, nanos normalized into `[0, 10^9)` (protobuf convention). -/
def Timestamp.ofTotalNanos (n : Int) : Timestamp :=
  { seconds := Int64.ofInt (n / 1000000000), nanos := Int32.ofInt (n % 1000000000) }

instance : LT Timestamp := ⟨fun a b => a.toTotalNanos < b.toTotalNanos⟩
instance : LE Timestamp := ⟨fun a b => a.toTotalNanos ≤ b.toTotalNanos⟩
instance (a b : Timestamp) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toTotalNanos < b.toTotalNanos))
instance (a b : Timestamp) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toTotalNanos ≤ b.toTotalNanos))

/-- Value equality on the represented instant (unknown fields ignored). -/
instance : BEq Timestamp := ⟨fun a b => a.toTotalNanos == b.toTotalNanos⟩

def Duration.toTotalNanos (d : Duration) : Int :=
  d.seconds.toInt * 1000000000 + d.nanos.toInt

/-- Seconds truncated toward zero, nanos with the same sign (protobuf
convention). -/
def Duration.ofTotalNanos (n : Int) : Duration :=
  { seconds := Int64.ofInt (n.tdiv 1000000000), nanos := Int32.ofInt (n.tmod 1000000000) }

instance : LT Duration := ⟨fun a b => a.toTotalNanos < b.toTotalNanos⟩
instance : LE Duration := ⟨fun a b => a.toTotalNanos ≤ b.toTotalNanos⟩
instance (a b : Duration) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toTotalNanos < b.toTotalNanos))
instance (a b : Duration) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toTotalNanos ≤ b.toTotalNanos))

/-- Value equality on the represented span (unknown fields ignored). -/
instance : BEq Duration := ⟨fun a b => a.toTotalNanos == b.toTotalNanos⟩

/-- CEL `duration.getSeconds()`: whole seconds (truncated toward zero). -/
def Duration.getSeconds (d : Duration) : Int64 := d.seconds

/-- CEL `duration.getMilliseconds()`: total milliseconds. -/
def Duration.getMilliseconds (d : Duration) : Int64 := Int64.ofInt (d.toTotalNanos.tdiv 1000000)

/-- CEL `duration.getMinutes()`: total minutes. -/
def Duration.getMinutes (d : Duration) : Int64 := Int64.ofInt (d.toTotalNanos.tdiv 60000000000)

/-- CEL `duration.getHours()`: total hours. -/
def Duration.getHours (d : Duration) : Int64 := Int64.ofInt (d.toTotalNanos.tdiv 3600000000000)

/-! CEL arithmetic: `ts - ts = duration`, `ts ± duration`, `duration ± duration`. -/

instance : HSub Timestamp Timestamp Duration :=
  ⟨fun a b => Duration.ofTotalNanos (a.toTotalNanos - b.toTotalNanos)⟩
instance : HAdd Timestamp Duration Timestamp :=
  ⟨fun t d => Timestamp.ofTotalNanos (t.toTotalNanos + d.toTotalNanos)⟩
instance : HAdd Duration Timestamp Timestamp :=
  ⟨fun d t => Timestamp.ofTotalNanos (t.toTotalNanos + d.toTotalNanos)⟩
instance : HSub Timestamp Duration Timestamp :=
  ⟨fun t d => Timestamp.ofTotalNanos (t.toTotalNanos - d.toTotalNanos)⟩
instance : Add Duration := ⟨fun a b => Duration.ofTotalNanos (a.toTotalNanos + b.toTotalNanos)⟩
instance : Sub Duration := ⟨fun a b => Duration.ofTotalNanos (a.toTotalNanos - b.toTotalNanos)⟩
instance : Neg Duration := ⟨fun d => Duration.ofTotalNanos (-d.toTotalNanos)⟩

end google.protobuf

namespace Cel

/-! ## Parsing -/

namespace Time.Internal

def takeDigits (cs : List Char) (n : Nat) : Option (Nat × List Char) := do
  let ds := cs.take n
  if ds.length != n || !ds.all Char.isDigit then none
  else some (ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0, cs.drop n)

def expect (cs : List Char) (c : Char) : Option (List Char) :=
  match cs with
  | c' :: rest => if c' == c then some rest else none
  | [] => none

def isLeap (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 1 => 31 | 3 => 31 | 5 => 31 | 7 => 31 | 8 => 31 | 10 => 31 | 12 => 31
  | 4 => 30 | 6 => 30 | 9 => 30 | 11 => 30
  | 2 => if isLeap y then 29 else 28
  | _ => 0

/-- Days since 1970-01-01 for a civil date (Howard Hinnant's algorithm,
using Lean's floor division). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp := (Int.ofNat m + 9) % 12
  let doy := (153 * mp + 2) / 5 + Int.ofNat d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Fractional seconds: up to nine digits, right-padded to nanoseconds. -/
def takeFraction (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none
  else
    let significant := ds.take 9
    let value := significant.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    let scale := 10 ^ (9 - significant.length)
    some (value * scale, cs.drop ds.length)

def offset? (cs : List Char) : Option Int := do
  match cs with
  | ['Z'] | ['z'] => some 0
  | sign :: rest =>
    let signum : Int ← if sign == '+' then some 1 else if sign == '-' then some (-1) else none
    let (h, rest) ← takeDigits rest 2
    let rest ← expect rest ':'
    let (mi, rest) ← takeDigits rest 2
    if !rest.isEmpty || h > 23 || mi > 59 then none
    else some (signum * (Int.ofNat h * 3600 + Int.ofNat mi * 60))
  | [] => none

def durationUnitNanos (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | 'n' :: 's' :: rest => some (1, rest)
  | 'u' :: 's' :: rest => some (1000, rest)
  | 'µ' :: 's' :: rest => some (1000, rest)
  | 'm' :: 's' :: rest => some (1000000, rest)
  | 'm' :: rest => some (60000000000, rest)
  | 's' :: rest => some (1000000000, rest)
  | 'h' :: rest => some (3600000000000, rest)
  | _ => none

end Time.Internal

open Time.Internal in
/-- Parse an RFC 3339 timestamp (`YYYY-MM-DDTHH:MM:SS[.fff...](Z|±HH:MM)`). -/
def Timestamp.parse? (s : String) : Option Timestamp := do
  let cs := s.toList
  let (y, cs) ← takeDigits cs 4
  let cs ← expect cs '-'
  let (mo, cs) ← takeDigits cs 2
  let cs ← expect cs '-'
  let (d, cs) ← takeDigits cs 2
  let cs ← match cs with
    | c :: rest => if c == 'T' || c == 't' then pure rest else none
    | [] => none
  let (h, cs) ← takeDigits cs 2
  let cs ← expect cs ':'
  let (mi, cs) ← takeDigits cs 2
  let cs ← expect cs ':'
  let (sec, cs) ← takeDigits cs 2
  let (nanos, cs) ← match cs with
    | '.' :: rest => takeFraction rest
    | _ => some (0, cs)
  let off ← offset? cs
  if mo < 1 || mo > 12 || d < 1 || d > daysInMonth y mo || h > 23 || mi > 59 || sec > 59 then
    none
  else
    let days := daysFromCivil (Int.ofNat y) mo d
    let secs := days * 86400 + Int.ofNat h * 3600 + Int.ofNat mi * 60 + Int.ofNat sec - off
    some { seconds := Int64.ofInt secs, nanos := Int32.ofInt (Int.ofNat nanos) }

/-- CEL `timestamp(string)`. Invalid input maps to the zero timestamp (the
total-function embedding; prefer `Timestamp.parse?` when failure matters). -/
def timestamp (s : String) : Timestamp := (Timestamp.parse? s).getD default

open Time.Internal in
/-- Parse a CEL/Go duration string (`"1h2m3.5s"`, `"-300ms"`, ...). -/
def Duration.parse? (s : String) : Option Duration := do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  if cs.isEmpty then none else
  let rec segments (cs : List Char) (acc : Nat) (fuel : Nat) : Option Nat := do
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if cs.isEmpty then some acc else
      let ds := cs.takeWhile Char.isDigit
      if ds.isEmpty then none else
      let whole := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      let cs := cs.drop ds.length
      let (fracDigits, cs) := match cs with
        | '.' :: rest =>
          let fs := rest.takeWhile Char.isDigit
          (fs, rest.drop fs.length)
        | _ => ([], cs)
      let (unit, cs) ← durationUnitNanos cs
      let fracValue := fracDigits.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      let fracNanos := fracValue * unit / 10 ^ fracDigits.length
      segments cs (acc + whole * unit + fracNanos) fuel
  let total ← segments cs 0 (cs.length + 1)
  let n : Int := if neg then -(Int.ofNat total) else Int.ofNat total
  some (google.protobuf.Duration.ofTotalNanos n)

/-- CEL `duration(string)`. Invalid input maps to the zero duration. -/
def duration (s : String) : Duration := (Duration.parse? s).getD default

/-- protovalidate's `now` variable. A refinement mentioning `now` is
evaluation-time dependent; the codegen layer decides whether such constraints
belong in the subtype at all. -/
opaque now : Timestamp

end Cel
