module

/-!
protovalidate's string-format predicates (email, hostname, IP, URI, ...),
following the grammars its CEL extensions implement. All checks are
ASCII-oriented, matching protovalidate (no IDN support).
-/

@[expose] public section

namespace Cel.Format

/-! ## Hostnames (RFC 1034 preferred syntax, protovalidate profile) -/

def isHostnameLabel (label : String) : Bool :=
  let cs := label.toList
  label.length ≥ 1 && label.length ≤ 63 &&
    cs.all (fun c => c.isAlphanum || c == '-') &&
    !label.startsWith "-" && !label.endsWith "-"

/-- Hostname: ≤253 chars, dot-separated labels of ≤63 alphanumeric/hyphen
chars without leading/trailing hyphens, a single optional trailing dot (the
DNS root), and a non-numeric right-most label.

The length bound counts the trailing dot, matching protovalidate (whose prose
says "excluding the optional trailing dot" but whose check does not). -/
def isHostname (s : String) : Bool :=
  s.length ≤ 253 &&
    let str := if s.endsWith "." then (s.dropEnd 1).toString else s
    let labels := str.splitOn "."
    labels.all isHostnameLabel &&
      match labels.getLast? with
      | some last => !last.toList.all Char.isDigit
      | none => false

/-! ## IP addresses -/

/-- Strict IPv4 octet: 1-3 digits, no leading zeros, ≤ 255. -/
def ipv4Octet? (part : String) : Option Nat :=
  let cs := part.toList
  if cs.isEmpty || cs.length > 3 || !cs.all Char.isDigit then none
  else if cs.length > 1 && cs.head? == some '0' then none
  else
    let v := cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    if v ≤ 255 then some v else none

/-- IPv4 as a 32-bit value. -/
def ipv4Value? (s : String) : Option Nat := do
  let parts := s.splitOn "."
  if parts.length != 4 then none
  else
    parts.foldlM (fun acc p => (ipv4Octet? p).map (acc * 256 + ·)) 0

def isIpv4 (s : String) : Bool := (ipv4Value? s).isSome

def hexGroup? (part : String) : Option Nat :=
  let cs := part.toList
  if cs.isEmpty || cs.length > 4 then none
  else
    cs.foldlM
      (fun acc c =>
        if c.isDigit then some (acc * 16 + (c.toNat - 48))
        else if 'a' ≤ c && c ≤ 'f' then some (acc * 16 + c.toNat - 87)
        else if 'A' ≤ c && c ≤ 'F' then some (acc * 16 + c.toNat - 55)
        else none)
      0

/-- Groups of an uncompressed IPv6 piece; a trailing IPv4 tail counts as two
groups. `none` on any invalid group. -/
def ipv6Groups? (piece : String) : Option (List Nat) := do
  if piece.isEmpty then some []
  else
    let parts := piece.splitOn ":"
    let rec walk : List String → Option (List Nat)
      | [] => some []
      | [last] =>
        if (last.splitOn "." |>.length) == 4 then do
          let v ← ipv4Value? last
          some [v / 65536, v % 65536]
        else do
          some [← hexGroup? last]
      | p :: rest => do
        let g ← hexGroup? p
        let gs ← walk rest
        some (g :: gs)
    walk parts

/-- IPv6 as a 128-bit value (RFC 4291 text form, one `::` compression,
optional embedded IPv4 tail, no zone). -/
def ipv6Value? (s : String) : Option Nat := do
  let joined (gs : List Nat) : Nat := gs.foldl (fun acc g => acc * 65536 + g) 0
  match s.splitOn "::" with
  | [only] => do
    let gs ← ipv6Groups? only
    if gs.length == 8 then some (joined gs) else none
  | [l, r] => do
    let ls ← ipv6Groups? l
    let rs ← ipv6Groups? r
    if ls.length + rs.length ≥ 8 then none
    else some (joined ls * 2 ^ (16 * (8 - ls.length)) + joined rs)
  | _ => none

/-- IPv6 in RFC 4291 text form, *without* a zone identifier. This is the form
an address prefix and a URI IP-literal admit. -/
def isIpv6Addr (s : String) : Bool := (ipv6Value? s).isSome

/-- Strip an optional RFC 4007 zone identifier (`fe80::1%en0`). protovalidate
permits any non-empty zone string; a `%` with nothing after it is invalid, and
so is a `%` inside what would otherwise be the address (the zone runs to the
end of the string). -/
def stripZoneId (s : String) : Option String :=
  match s.toList.findIdx? (· == '%') with
  | none => some s
  | some i => if i + 1 < s.length then some (String.ofList (s.toList.take i)) else none

/-- IPv6 as CEL's `isIp(…, 6)` accepts it: RFC 4291 text form with an optional
RFC 4007 zone identifier. -/
def isIpv6 (s : String) : Bool :=
  match stripZoneId s with
  | none => false
  | some addr => isIpv6Addr addr

def isIp (s : String) (version : Int := 0) : Bool :=
  if version == 4 then isIpv4 s
  else if version == 6 then isIpv6 s
  else if version == 0 then isIpv4 s || isIpv6 s
  else false

/-- CIDR prefix: `ip/len`, decimal length without leading zeros and within
the family's bit width; strict additionally requires all host bits clear. -/
def isIpPrefix (s : String) (version : Int := 0) (strict : Bool := false) : Bool :=
  match s.splitOn "/" with
  | [ip, lenS] =>
    let lenOk :=
      let cs := lenS.toList
      !cs.isEmpty && cs.all Char.isDigit && (cs.length == 1 || cs.head? != some '0')
    if !lenOk then false
    else
      let len := lenS.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
      let check (bits : Nat) (value : Option Nat) : Bool :=
        match value with
        | none => false
        | some v =>
          len ≤ bits && (!strict || v % 2 ^ (bits - len) == 0)
      match version with
      | 4 => check 32 (ipv4Value? ip)
      | 6 => check 128 (ipv6Value? ip)
      | 0 =>
        (if isIpv4 ip then check 32 (ipv4Value? ip) else check 128 (ipv6Value? ip))
      | _ => false
  | _ => false

/-! ## Email (HTML living standard, as protovalidate defines it) -/

/-- Local-part character. protovalidate follows the HTML standard's email
definition, which willfully deviates from RFC 5322: the local part is
`[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+`, so `.` is an ordinary character (leading,
trailing and repeated dots are all accepted), there is no quoted form, and
there is no length limit on either part or on the address as a whole. -/
def isEmailLocalChar (c : Char) : Bool :=
  c.isAlphanum ||
    c == '.' || c == '!' || c == '#' || c == '$' || c == '%' || c == '&' ||
    c == '\'' || c == '*' || c == '+' || c == '-' || c == '/' || c == '=' ||
    c == '?' || c == '^' || c == '_' || c == '`' || c == '{' || c == '|' ||
    c == '}' || c == '~'

/-- Domain label of an email address: 1–63 alphanumerics and hyphens starting
and ending with an alphanumeric. Unlike `isHostname`'s labels there is no
trailing-dot form and an all-digit right-most label is allowed. -/
def isEmailDomainLabel (label : String) : Bool :=
  let cs := label.toList
  1 ≤ cs.length && cs.length ≤ 63 &&
    cs.all (fun c => c.isAlphanum || c == '-') &&
    cs.head?.elim false Char.isAlphanum &&
    cs.getLast?.elim false Char.isAlphanum

/-- Email: `local@domain`, exactly one `@` (it is in neither character set). -/
def isEmail (s : String) : Bool :=
  match s.splitOn "@" with
  | [localPart, domain] =>
    !localPart.isEmpty && localPart.toList.all isEmailLocalChar &&
      (domain.splitOn ".").all isEmailDomainLabel
  | _ => false

/-! ## Host and port -/

def isPort (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.all Char.isDigit && (cs.length == 1 || cs.head? != some '0') &&
    cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 ≤ 65535

/-- Code-point index of the last occurrence of `c` in `s`. -/
def lastIndexOf? (s : String) (c : Char) : Option Nat :=
  let cs := s.toList
  (cs.reverse.findIdx? (· == c)).map (fun i => cs.length - 1 - i)

/-- `host[:port]` where host is a hostname, IPv4, or bracketed IPv6.

Both separators are located from the *right*, as protovalidate does: the
bracketed form ends at the last `]` and the port begins at the last `:`. That
is observable — in `[::0%00]]` the zone identifier swallows the first `]`. -/
def isHostAndPort (s : String) (portRequired : Bool) : Bool :=
  if s.isEmpty then false
  else
    let cs := s.toList
    let colon? := lastIndexOf? s ':'
    if s.startsWith "[" then
      match lastIndexOf? s ']' with
      | none => false
      | some e =>
        let inner := String.ofList ((cs.take e).drop 1)
        if e + 1 == cs.length then !portRequired && isIpv6 inner
        else if colon? == some (e + 1) then
          isIpv6 inner && isPort (String.ofList (cs.drop (e + 2)))
        else false
    else
      match colon? with
      | none => !portRequired && (isHostname s || isIpv4 s)
      | some i =>
        let host := String.ofList (cs.take i)
        (isHostname host || isIpv4 host) && isPort (String.ofList (cs.drop (i + 1)))

/-! ## URIs (RFC 3986) -/

def isUnreserved (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

def isSubDelim (c : Char) : Bool :=
  c == '!' || c == '$' || c == '&' || c == '\'' || c == '(' || c == ')' ||
    c == '*' || c == '+' || c == ',' || c == ';' || c == '='

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Validate a run of characters allowing pct-encoding: every char satisfies
`ok`, or begins a valid `%HH` triple. -/
def pctOk (ok : Char → Bool) : List Char → Bool
  | [] => true
  | '%' :: h1 :: h2 :: rest => isHexDigit h1 && isHexDigit h2 && pctOk ok rest
  | '%' :: _ => false
  | c :: rest => ok c && pctOk ok rest

def isPchar (c : Char) : Bool := isUnreserved c || isSubDelim c || c == ':' || c == '@'

/-! ### Percent-encoded hosts must encode UTF-8

RFC 3986: "URI producing applications must not use percent-encoding in host
unless it is used to represent a UTF-8 character sequence." protovalidate
enforces this, so `foo%c3x%96` (a truncated two-byte sequence) is not a valid
host even though every triple is syntactically well-formed. -/

def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55
  else 0

/-- Percent-decode to bytes. Non-`%` characters are ASCII here (everything else
is rejected by the host character classes), so a code point is a byte. -/
def pctDecode : List Char → List UInt8
  | [] => []
  | '%' :: h1 :: h2 :: rest => (hexValue h1 * 16 + hexValue h2).toUInt8 :: pctDecode rest
  | c :: rest => c.toNat.toUInt8 :: pctDecode rest

/-- UTF-8 continuation byte. -/
def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- Well-formed UTF-8 (RFC 3629): no overlong encodings, no surrogates,
nothing above U+10FFFF — what Go's `utf8.Valid` accepts. -/
def utf8Valid : List UInt8 → Bool
  | [] => true
  | b0 :: rest =>
    if b0 ≤ 0x7f then utf8Valid rest
    else if 0xc2 ≤ b0 && b0 ≤ 0xdf then
      match rest with
      | b1 :: rest' => isCont b1 && utf8Valid rest'
      | [] => false
    else if 0xe0 ≤ b0 && b0 ≤ 0xef then
      match rest with
      | b1 :: b2 :: rest' =>
        -- E0 excludes overlongs (A0..BF), ED excludes surrogates (80..9F).
        let lo : UInt8 := if b0 == 0xe0 then 0xa0 else 0x80
        let hi : UInt8 := if b0 == 0xed then 0x9f else 0xbf
        lo ≤ b1 && b1 ≤ hi && isCont b2 && utf8Valid rest'
      | _ => false
    else if 0xf0 ≤ b0 && b0 ≤ 0xf4 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        -- F0 excludes overlongs (90..BF), F4 caps at U+10FFFF (80..8F).
        let lo : UInt8 := if b0 == 0xf0 then 0x90 else 0x80
        let hi : UInt8 := if b0 == 0xf4 then 0x8f else 0xbf
        lo ≤ b1 && b1 ≤ hi && isCont b2 && isCont b3 && utf8Valid rest'
      | _ => false
    else false

def isSchemeOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => c.isAlpha && rest.all (fun x => x.isAlphanum || x == '+' || x == '-' || x == '.')

def isUserinfoOk (s : String) : Bool :=
  pctOk (fun c => isUnreserved c || isSubDelim c || c == ':') s.toList

/-- `IPvFuture = "v" 1*HEXDIG "." 1*( unreserved / sub-delims / ":" )`. -/
def isIpvFuture (s : String) : Bool :=
  match s.toList with
  | 'v' :: rest =>
    let hex := rest.takeWhile isHexDigit
    match rest.dropWhile isHexDigit with
    | '.' :: body =>
      !hex.isEmpty && !body.isEmpty &&
        body.all (fun c => isUnreserved c || isSubDelim c || c == ':')
    | _ => false
  | _ => false

/-- `ZoneID = 1*( unreserved / pct-encoded )` (RFC 6874). -/
def isZoneId (s : String) : Bool := !s.isEmpty && pctOk isUnreserved s.toList

/-- `IPv6addrz = IPv6address "%25" ZoneID` (RFC 6874). Inside a URI the zone
separator is percent-encoded, unlike the bare `%` `isIp` accepts; the address
part holds no `%`, so the first one starts the zone. -/
def isIpv6Addrz (s : String) : Bool :=
  let cs := s.toList
  match cs.findIdx? (· == '%') with
  | none => false
  | some i =>
    match cs.drop i with
    | '%' :: '2' :: '5' :: zone =>
      isIpv6Addr (String.ofList (cs.take i)) && isZoneId (String.ofList zone)
    | _ => false

/-- reg-name / IP-literal / IPv4 host of an authority. -/
def isUriHost (s : String) : Bool :=
  (if s.startsWith "[" && s.endsWith "]" then
      -- IP-literal = "[" ( IPv6address / IPv6addrz / IPvFuture ) "]"
      let inner := ((s.drop 1).toString.dropEnd 1).toString
      isIpv6Addr inner || isIpv6Addrz inner || isIpvFuture inner
    else
      pctOk (fun c => isUnreserved c || isSubDelim c) s.toList) &&
    (!s.toList.contains '%' || utf8Valid (pctDecode s.toList))

def isAuthorityOk (s : String) : Bool :=
  -- userinfo@ split at the LAST '@' (userinfo may contain none, host cannot
  -- contain '@').
  let (userinfo?, hostport) :=
    match s.splitOn "@" with
    | [hp] => (none, hp)
    | parts =>
      let host := parts.getLast!
      (some (String.intercalate "@" (parts.dropLast)), host)
  let uiOk := match userinfo? with
    | some ui => isUserinfoOk ui
    | none => true
  let hostOk :=
    if hostport.startsWith "[" then
      match hostport.splitOn "]" with
      | [inner, rest] =>
        isUriHost (inner ++ "]") &&
          (rest.isEmpty || rest.startsWith ":" && (rest.drop 1).toString.toList.all Char.isDigit)
      | _ => false
    else
      match hostport.splitOn ":" with
      | [host] => isUriHost host
      | [host, port] => isUriHost host && port.toList.all Char.isDigit
      | _ => false
  uiOk && hostOk

def isSegmentOk (s : String) : Bool := pctOk isPchar s.toList

/-- path-abempty: segments after an authority (each may be empty). -/
def isPathAbemptyOk (s : String) : Bool :=
  s.isEmpty || (s.startsWith "/" && ((s.drop 1).toString.splitOn "/").all isSegmentOk)

def isQueryOk (s : String) : Bool :=
  pctOk (fun c => isPchar c || c == '/' || c == '?') s.toList

/-- Split off `#fragment` and `?query` (in that order), validating both. -/
def splitQueryFragment (s : String) : Option String :=
  let (beforeFrag, fragOk) :=
    match s.splitOn "#" with
    | [x] => (x, true)
    | x :: rest => (x, isQueryOk (String.intercalate "#" rest) && !(String.intercalate "#" rest).toList.contains '#')
    | [] => ("", false)
  if !fragOk then none
  else
    match beforeFrag.splitOn "?" with
    | [x] => some x
    | x :: rest => if isQueryOk (String.intercalate "?" rest) then some x else none
    | [] => none

/-- hier-part / relative-part: authority + path, or standalone path. -/
def isHierOk (s : String) (allowColonInFirstSegment : Bool) : Bool :=
  if s.startsWith "//" then
    let rest := (s.drop 2).toString
    match rest.toList.findIdx? (· == '/') with
    | some i =>
      let auth := String.ofList (rest.toList.take i)
      let path := String.ofList (rest.toList.drop i)
      isAuthorityOk auth && isPathAbemptyOk path
    | none => isAuthorityOk rest
  else if s.isEmpty then true
  else
    let segs := s.splitOn "/"
    segs.all isSegmentOk &&
      (allowColonInFirstSegment ||
        match segs with
        | first :: _ => !first.toList.contains ':'
        | [] => true)

/-- RFC 3986 absolute URI (scheme required; fragment allowed, matching
protovalidate). -/
def isUri (s : String) : Bool :=
  match splitQueryFragment s with
  | none => false
  | some beforeQuery =>
    match beforeQuery.splitOn ":" with
    | scheme :: rest =>
      !rest.isEmpty && isSchemeOk scheme &&
        isHierOk (String.intercalate ":" rest) true
    | [] => false

/-- RFC 3986 URI-reference: a URI or a relative reference. -/
def isUriRef (s : String) : Bool :=
  isUri s ||
    match splitQueryFragment s with
    | none => false
    | some beforeQuery => isHierOk beforeQuery false

end Cel.Format
