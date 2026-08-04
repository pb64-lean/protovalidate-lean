import Std
import Protovalidate.Cel

/-!
Runtime semantics of the Cel shims: the regex engine, protovalidate's
string-format grammars, and timestamp/duration parsing and arithmetic.
Expectations mirror protovalidate's own library behavior.
-/

open Cel

def failures : IO.Ref (List String) → String → Bool → Bool → IO Unit :=
  fun ref label got want => do
    if got != want then ref.modify (label :: ·)

/-!
Guarded-translation shapes exactly as the generator emits them: propositions
over *runtime* values (function parameters), decided via the dependent-`ite`
`Decidable` instance. An out-of-range index, missing key, or overflowing
arithmetic must falsify the proposition — including under negation.
-/

def guardIdx (a : Array Int32) : Bool :=
  decide (if h : (a[0]?).isSome then (a[0]?).get h > 5 else False)

def guardIdxNeg (a : Array Int32) : Bool :=
  decide (if h : (a[0]?).isSome then ¬((a[0]?).get h > 5) else False)

def guardKey (m : Std.HashMap String String) : Bool :=
  decide (if h : (m["env"]?).isSome then (m["env"]?).get h = "prod" else False)

def guardKeyNe (m : Std.HashMap String String) : Bool :=
  decide (if h : (m["env"]?).isSome then (m["env"]?).get h ≠ "prod" else False)

def guardAdd (x : Int64) : Bool :=
  decide (if h : Cel.addOk x 1 then x + 1 > 0 else False)

def guardMul (x : Int64) : Bool :=
  decide (if h : Cel.mulOk x 2 then x * 2 = 42 else False)

def main : IO Unit := do
  let bad ← IO.mkRef ([] : List String)
  let ck := failures bad

  -- regex (Cel.regexMatch = RE2 PartialMatch semantics)
  ck "re: search" (regexMatch "hello world" "world") true
  ck "re: anchored" (regexMatch "say hello" "^hello") false
  ck "re: class" (regexMatch "user_42" "^[a-z0-9_]+$") true
  ck "re: class neg" (regexMatch "User_42" "^[a-z0-9_]+$") false
  ck "re: perl" (regexMatch "a1 b2" "\\w\\d\\s\\w\\d") true
  ck "re: alt" (regexMatch "dog" "^(cat|dog)$") true
  ck "re: bound" (regexMatch "aaa" "^a{2,3}$") true
  ck "re: bound over" (regexMatch "aaaa" "^a{2,3}$") false
  ck "re: dot no nl" (regexMatch "a\n" "^a.$") false
  ck "re: uuid" (regexMatch "550e8400-e29b-41d4-a716-446655440000"
    "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$") true
  ck "re: pathological terminates" (regexMatch "aaaaaaaaaaaaaaaaaaaac" "(a*)*b$") false
  ck "re: invalid pattern" (regexMatch "x" "(?i)x") false

  -- regex acceptance (mirrors the Go subset check in celtolean/regexcheck.go;
  -- keep this list in sync with TestRegexAccepted)
  ck "re acc: literal" (Cel.Regex.accepts "abc") true
  ck "re acc: class range esc" (Cel.Regex.accepts "^[a-z0-9_.\\-]+$") true
  ck "re acc: perl classes" (Cel.Regex.accepts "\\d\\D\\w\\W\\s\\S") true
  ck "re acc: hex escapes" (Cel.Regex.accepts "\\x41\\x{1F600}") true
  ck "re acc: bounds" (Cel.Regex.accepts "a{2}b{3,}c{4,5}") true
  ck "re acc: groups alt" (Cel.Regex.accepts "(?:ab|cd)+(e|f)?") true
  ck "re acc: literal brace" (Cel.Regex.accepts "a{b") true
  ck "re acc: class lead bracket" (Cel.Regex.accepts "[]a]") true
  ck "re acc: trailing dash" (Cel.Regex.accepts "[a-]") true
  ck "re acc: flags" (Cel.Regex.accepts "(?i)x") false
  ck "re acc: word boundary" (Cel.Regex.accepts "\\bx") false
  ck "re acc: named group" (Cel.Regex.accepts "(?P<n>x)") false
  -- The Lean parser reads "[[:alpha:]]" as literal chars; RE2 reads a POSIX
  -- class. The Go gate rejects POSIX classes so the divergence cannot ship.
  ck "re acc: posix class parses as chars" (Cel.Regex.accepts "[[:alpha:]]") true
  ck "re acc: big bound" (Cel.Regex.accepts "a{513}") false
  ck "re acc: bad bounds" (Cel.Regex.accepts "a{3,2}") false
  ck "re acc: unterminated class" (Cel.Regex.accepts "[abc") false
  ck "re acc: unterminated group" (Cel.Regex.accepts "(ab") false
  ck "re acc: stray paren" (Cel.Regex.accepts "ab)") false
  ck "re acc: trailing backslash" (Cel.Regex.accepts "ab\\") false
  ck "re acc: bad escape" (Cel.Regex.accepts "\\q") false
  ck "re acc: lone quantifier" (Cel.Regex.accepts "*a") false

  -- CEL arithmetic error side-conditions (overflow ⇒ rule fails)
  ck "arith: i64 add max" (Cel.addOk (9223372036854775807 : Int64) 1) false
  ck "arith: i64 add ok" (Cel.addOk (9223372036854775806 : Int64) 1) true
  ck "arith: i64 sub min" (Cel.subOk (-9223372036854775808 : Int64) 1) false
  ck "arith: i64 mul over" (Cel.mulOk (4611686018427387904 : Int64) 2) false
  ck "arith: i64 neg min" (Cel.negOk (-9223372036854775808 : Int64)) false
  ck "arith: i64 neg ok" (Cel.negOk (-9223372036854775807 : Int64)) true
  ck "arith: u64 sub under" (Cel.subOk (0 : UInt64) 1) false
  ck "arith: u64 add max" (Cel.addOk (18446744073709551615 : UInt64) 1) false
  ck "arith: u64 mul ok" (Cel.mulOk (3 : UInt64) 5) true
  ck "arith: i32 mul over" (Cel.mulOk (2000000000 : Int32) 2) false
  ck "arith: i32 add ok" (Cel.addOk (2147483646 : Int32) 1) true
  ck "arith: u32 add over" (Cel.addOk (4294967295 : UInt32) 1) false
  ck "arith: nat sub under" (Cel.subOk (0 : Nat) 1) false
  ck "arith: nat sub ok" (Cel.subOk (1 : Nat) 1) true
  ck "arith: string concat total" (Cel.addOk "a" "b") true

  -- guarded translations decide with CEL error semantics: an out-of-range
  -- index or overflowing arithmetic falsifies the guarded proposition
  ck "guard: index in range" (guardIdx #[7, 8]) true
  ck "guard: index oob fails" (guardIdx #[]) false
  ck "guard: index oob fails under negation" (guardIdxNeg #[]) false
  ck "guard: index negation in range" (guardIdxNeg #[3]) true
  ck "guard: map key present" (guardKey (Std.HashMap.ofList [("env", "prod")])) true
  ck "guard: map key missing fails" (guardKey (Std.HashMap.ofList [])) false
  ck "guard: map key missing fails under ne" (guardKeyNe (Std.HashMap.ofList [])) false
  ck "guard: overflow falsifies" (guardAdd 9223372036854775807) false
  ck "guard: in-range arithmetic exact" (guardMul 21) true

  -- hostnames / emails
  ck "hostname" "example.com".isHostname true
  ck "hostname trailing dot" "example.com.".isHostname false
  ck "hostname hyphens" "-bad.com".isHostname false
  ck "hostname numeric tld" "abc.123".isHostname false
  ck "email" "simple@example.com".isEmail true
  ck "email plus" "x+y_z@sub.example.com".isEmail true
  ck "email no at" "no-at-sign".isEmail false
  ck "email dot lead" ".lead@example.com".isEmail false
  ck "email bad domain" "a@-bad.com".isEmail false

  -- ips / prefixes / host-and-port
  ck "ipv4" ("192.168.0.1".isIp 4) true
  ck "ipv4 leading zero" ("01.2.3.4".isIp 4) false
  ck "ipv6 compressed" ("2001:db8::8a2e:370:7334".isIp 6) true
  ck "ipv6 v4 tail" ("::ffff:192.168.0.1".isIp 6) true
  ck "ipv6 double comp" ("1::2::3".isIp 6) false
  ck "ip any" ("::1".isIp) true
  ck "prefix strict ok" ("192.168.0.0/24".isIpPrefix 4 true) true
  ck "prefix strict host bits" ("192.168.0.1/24".isIpPrefix 4 true) false
  ck "prefix loose" ("192.168.0.1/24".isIpPrefix 4 false) true
  ck "prefix len over" ("10.0.0.0/33".isIpPrefix 4 false) false
  ck "hostport" ("example.com:8080".isHostAndPort true) true
  ck "hostport required" ("example.com".isHostAndPort true) false
  ck "hostport v6" ("[::1]:80".isHostAndPort true) true
  ck "hostport big port" ("example.com:99999".isHostAndPort true) false

  -- uris
  ck "uri" "https://example.com/path?q=1#frag".isUri true
  ck "uri urn" "urn:isbn:0451450523".isUri true
  ck "uri relative not abs" "//host/path".isUri false
  ck "uri bad pct" "https://example.com/%zz".isUri false
  ck "uriref relative" "./relative/path".isUriRef true
  ck "uriref frag" "#frag".isUriRef true
  ck "uriref space" "a b".isUriRef false

  -- time
  ck "ts parse" ((Timestamp.parse? "2030-01-01T00:00:00Z").map (·.seconds) == some 1893456000) true
  ck "ts offset" ((Timestamp.parse? "2024-02-29T12:30:45.123456789+05:30").map (·.seconds) == some 1709190045) true
  ck "ts not leap" (Timestamp.parse? "2023-02-29T00:00:00Z").isSome false
  ck "dur parse" ((Duration.parse? "1h2m3.5s").map (fun d => (d.seconds, d.nanos)) == some (3723, 500000000)) true
  ck "dur negative" ((Duration.parse? "-300ms").map (·.nanos) == some (-300000000)) true
  ck "ts sub" ((timestamp "2030-01-02T00:00:00Z" - timestamp "2030-01-01T00:00:00Z") == duration "24h") true
  ck "ts add" ((timestamp "2030-01-01T00:00:00Z" + duration "48h") == timestamp "2030-01-03T00:00:00Z") true
  ck "dur total hours" ((duration "26h30m").getHours == 26) true

  -- refinement-style props decide at runtime
  ck "decide prop" (decide (Cel.contains "hello world" "lo w" ∧ "a@b.co".isEmail)) true

  let failed ← bad.get
  if failed.isEmpty then
    IO.println "all runtime assertions passed"
  else do
    for f in failed do IO.eprintln s!"FAIL {f}"
    throw (IO.userError s!"{failed.length} runtime assertions failed")
