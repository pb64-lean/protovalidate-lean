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
