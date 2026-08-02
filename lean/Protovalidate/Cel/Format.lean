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
chars without leading/trailing hyphens, no trailing dot, and a non-numeric
final label. -/
def isHostname (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 253 &&
    let labels := s.splitOn "."
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

def isIpv6 (s : String) : Bool := (ipv6Value? s).isSome

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

/-! ## Email (RFC 5322 addr-spec, dot-atom form only) -/

def isAtext (c : Char) : Bool :=
  c.isAlphanum ||
    c == '!' || c == '#' || c == '$' || c == '%' || c == '&' || c == '\'' ||
    c == '*' || c == '+' || c == '-' || c == '/' || c == '=' || c == '?' ||
    c == '^' || c == '_' || c == '`' || c == '{' || c == '|' || c == '}' ||
    c == '~'

def isDotAtom (s : String) : Bool :=
  let atoms := s.splitOn "."
  !s.isEmpty && atoms.all (fun a => !a.isEmpty && a.toList.all isAtext)

/-- Email: `local@domain` with a dot-atom local part (≤64 chars, no quoting)
and a hostname domain; ≤254 chars overall. -/
def isEmail (s : String) : Bool :=
  s.length ≤ 254 &&
    match s.splitOn "@" with
    | [localPart, domain] => localPart.length ≤ 64 && isDotAtom localPart && isHostname domain
    | _ => false

/-! ## Host and port -/

def isPort (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.all Char.isDigit && (cs.length == 1 || cs.head? != some '0') &&
    cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 ≤ 65535

/-- `host[:port]` where host is a hostname, IPv4, or bracketed IPv6. -/
def isHostAndPort (s : String) (portRequired : Bool) : Bool :=
  if s.startsWith "[" then
    match s.splitOn "]" with
    | [inner, rest] =>
      let ip := (inner.drop 1).toString
      isIpv6 ip &&
        (rest.isEmpty && !portRequired ||
          rest.startsWith ":" && isPort (rest.drop 1).toString)
    | _ => false
  else
    match s.splitOn ":" with
    | [host] => !portRequired && (isHostname host || isIpv4 host)
    | [host, port] => (isHostname host || isIpv4 host) && isPort port
    | _ => false

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

def isSchemeOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => c.isAlpha && rest.all (fun x => x.isAlphanum || x == '+' || x == '-' || x == '.')

def isUserinfoOk (s : String) : Bool :=
  pctOk (fun c => isUnreserved c || isSubDelim c || c == ':') s.toList

/-- reg-name / IP-literal / IPv4 host of an authority. -/
def isUriHost (s : String) : Bool :=
  if s.startsWith "[" && s.endsWith "]" then
    let inner := ((s.drop 1).toString.dropEnd 1).toString
    -- IP-literal: IPv6 (or IPvFuture, which we do not support).
    isIpv6 inner
  else
    pctOk (fun c => isUnreserved c || isSubDelim c) s.toList

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
