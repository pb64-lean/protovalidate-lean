module

/-!
A small regular-expression engine backing CEL `matches` (`Cel.regexMatch`).

Scope: the RE2 subset that validation patterns use — literals, `.`, character
classes with ranges/negation/Perl classes (`\d \w \s` and complements),
escapes (`\n \t \r \f \v \xHH \x{...}` and escaped punctuation), anchors
`^`/`$` (whole-text), alternation, (non-)capturing groups, and quantifiers
`* + ? {n} {n,} {n,m}` (greediness is irrelevant for match existence).
Unsupported RE2 features (backreferences don't exist in RE2; `(?i)` flags,
`\b`, named classes) are parse errors.

Semantics: unanchored search (protovalidate's `matches` is RE2
`PartialMatch`), decided by a Pike-style NFA simulation — no backtracking, so
matching is linear in `|input| × |program|` and total.
-/

public section

namespace Cel.Regex

inductive Ast where
  | epsilon
  | char (p : Char → Bool)
  | concat (a b : Ast)
  | alt (a b : Ast)
  | star (a : Ast)
  | assertStart
  | assertEnd

/-- Compiled instruction; `next` fields are absolute program indices. -/
inductive Inst where
  | char (p : Char → Bool) (next : Nat)
  | split (a b : Nat)
  | assertStart (next : Nat)
  | assertEnd (next : Nat)
  | done
deriving Inhabited

abbrev Prog := Array Inst

/-! ## Pattern parser -/

namespace Parser

def charLE (a b : Char) : Bool := decide (a ≤ b)

def digitP (c : Char) : Bool := c.isDigit
def wordP (c : Char) : Bool := c.isAlphanum || c == '_'
/-- RE2 `\s`: `[\t\n\f\r ]`. -/
def spaceP (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexChar? (ds : List Char) : Option Char := do
  let n ← ds.foldlM (fun acc c => (hexVal? c).map (acc * 16 + ·)) 0
  if n.isValidChar then some (Char.ofNat n) else none

/-- An escape denotes either a concrete character (usable in ranges) or a
character-class predicate. -/
inductive Esc where
  | char (c : Char)
  | pred (p : Char → Bool)

def escape : List Char → Except String (Esc × List Char)
  | [] => .error "trailing backslash"
  | c :: rest =>
    match c with
    | 'd' => .ok (.pred digitP, rest)
    | 'D' => .ok (.pred (!digitP ·), rest)
    | 'w' => .ok (.pred wordP, rest)
    | 'W' => .ok (.pred (!wordP ·), rest)
    | 's' => .ok (.pred spaceP, rest)
    | 'S' => .ok (.pred (!spaceP ·), rest)
    | 'n' => .ok (.char '\n', rest)
    | 't' => .ok (.char '\t', rest)
    | 'r' => .ok (.char '\r', rest)
    | 'f' => .ok (.char '\x0c', rest)
    | 'v' => .ok (.char '\x0b', rest)
    | 'a' => .ok (.char '\x07', rest)
    | '0' => .ok (.char '\x00', rest)
    | 'x' =>
      match rest with
      | '{' :: more =>
        let ds := more.takeWhile (· != '}')
        match more.drop ds.length with
        | '}' :: after =>
          match hexChar? ds with
          | some ch => .ok (.char ch, after)
          | none => .error "invalid \\x{...} escape"
        | _ => .error "unterminated \\x{...} escape"
      | h1 :: h2 :: after =>
        match hexChar? [h1, h2] with
        | some ch => .ok (.char ch, after)
        | none => .error "invalid \\xHH escape"
      | _ => .error "truncated \\x escape"
    | _ =>
      if c.isAlphanum then .error s!"unsupported escape \\{c}"
      else .ok (.char c, rest)

mutual

/-- Items of a character class; `first` admits `]` as a literal. -/
partial def classItems (cs : List Char) (first : Bool) (acc : List (Char → Bool)) :
    Except String (List (Char → Bool) × List Char) := do
  match cs with
  | [] => .error "unterminated character class"
  | ']' :: rest =>
    if first then classItems rest false ((· == ']') :: acc)
    else .ok (acc, rest)
  | '\\' :: esc =>
    match ← escape esc with
    | (.pred p, r) => classItems r false (p :: acc)
    | (.char lo, r) => classRange lo r acc
  | c :: rest => classRange c rest acc

/-- After a literal class element: either the low end of a range or a lone
character. -/
partial def classRange (lo : Char) (cs : List Char) (acc : List (Char → Bool)) :
    Except String (List (Char → Bool) × List Char) := do
  match cs with
  | '-' :: ']' :: rest =>
    -- Trailing '-' is a literal.
    classItems (']' :: rest) false ((· == '-') :: (· == lo) :: acc)
  | '-' :: '\\' :: esc =>
    match ← escape esc with
    | (.char hi, r) => classItems r false ((fun ch => charLE lo ch && charLE ch hi) :: acc)
    | (.pred _, _) => .error "invalid range endpoint"
  | '-' :: hi :: rest => classItems rest false ((fun ch => charLE lo ch && charLE ch hi) :: acc)
  | _ => classItems cs false ((· == lo) :: acc)

end

/-- Parse the interior of a character class (after `[`), producing its
predicate. -/
partial def parseClass (cs : List Char) : Except String ((Char → Bool) × List Char) := do
  let (neg, cs) := match cs with
    | '^' :: rest => (true, rest)
    | _ => (false, cs)
  let (preds, rest) ← classItems cs true []
  let base := fun ch => preds.any (· ch)
  .ok ((if neg then (fun ch => !base ch) else base), rest)

def repeatN (a : Ast) : Nat → Ast
  | 0 => .epsilon
  | 1 => a
  | n + 1 => .concat a (repeatN a n)

def optChain (a : Ast) : Nat → Ast
  | 0 => .epsilon
  | n + 1 => .alt (.concat a (optChain a n)) .epsilon

def natOf (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

mutual

partial def parseAlt (cs : List Char) : Except String (Ast × List Char) := do
  let (a, cs) ← parseConcat cs
  match cs with
  | '|' :: rest =>
    let (b, rest) ← parseAlt rest
    .ok (.alt a b, rest)
  | _ => .ok (a, cs)

partial def parseConcat (cs : List Char) : Except String (Ast × List Char) := do
  match cs with
  | [] | '|' :: _ | ')' :: _ => .ok (.epsilon, cs)
  | _ =>
    let (a, cs) ← parseRepeat cs
    let (b, cs) ← parseConcat cs
    match b with
    | .epsilon => .ok (a, cs)
    | _ => .ok (.concat a b, cs)

partial def parseRepeat (cs : List Char) : Except String (Ast × List Char) := do
  let (a, cs) ← parseAtom cs
  quantify a cs

partial def quantify (a : Ast) (cs : List Char) : Except String (Ast × List Char) := do
  let nonGreedy : List Char → List Char
    | '?' :: rest => rest
    | rest => rest
  match cs with
  | '*' :: rest => quantify (.star a) (nonGreedy rest)
  | '+' :: rest => quantify (.concat a (.star a)) (nonGreedy rest)
  | '?' :: rest => quantify (.alt a .epsilon) (nonGreedy rest)
  | '{' :: rest =>
    let lo := rest.takeWhile Char.isDigit
    if lo.isEmpty then .ok (a, cs)  -- RE2: `{` without bounds is a literal, handled by parseAtom next round
    else
      let n := natOf lo
      match rest.drop lo.length with
      | '}' :: r2 =>
        if n > 512 then .error "repetition bound too large" else
        quantify (repeatN a n) (nonGreedy r2)
      | ',' :: '}' :: r2 =>
        if n > 512 then .error "repetition bound too large" else
        quantify (.concat (repeatN a n) (.star a)) (nonGreedy r2)
      | ',' :: r2 =>
        let hi := r2.takeWhile Char.isDigit
        match r2.drop hi.length with
        | '}' :: r3 =>
          let m := natOf hi
          if m > 512 || m < n then .error "invalid repetition bounds" else
          quantify (.concat (repeatN a n) (optChain a (m - n))) (nonGreedy r3)
        | _ => .error "unterminated repetition"
      | _ => .error "unterminated repetition"
  | _ => .ok (a, cs)

partial def parseAtom (cs : List Char) : Except String (Ast × List Char) := do
  match cs with
  | [] => .error "expected atom"
  | '(' :: rest =>
    let rest ← match rest with
      | '?' :: ':' :: r => pure r
      | '?' :: _ => .error "unsupported (?...) group"
      | r => pure r
    let (a, rest) ← parseAlt rest
    match rest with
    | ')' :: r2 => .ok (a, r2)
    | _ => .error "unterminated group"
  | '[' :: rest =>
    let (p, rest) ← parseClass rest
    .ok (.char p, rest)
  | '\\' :: rest =>
    match ← escape rest with
    | (.char ch, r) => .ok (.char (· == ch), r)
    | (.pred p, r) => .ok (.char p, r)
  | '.' :: rest => .ok (.char (· != '\n'), rest)
  | '^' :: rest => .ok (.assertStart, rest)
  | '$' :: rest => .ok (.assertEnd, rest)
  | '*' :: _ | '+' :: _ | '?' :: _ => .error "quantifier without operand"
  | c :: rest => .ok (.char (· == c), rest)

end

def parse (pattern : String) : Except String Ast := do
  let (a, rest) ← parseAlt pattern.toList
  if rest.isEmpty then .ok a else .error "unexpected ')'"

end Parser

/-! ## Compiler -/

private def emit (i : Inst) : StateM Prog Nat := fun prog =>
  (prog.size, prog.push i)

private def patch (idx : Nat) (i : Inst) : StateM Prog Unit := fun prog =>
  ((), prog.set! idx i)

private def compileNode : Ast → Nat → StateM Prog Nat
  | .epsilon, next => pure next
  | .char p, next => emit (.char p next)
  | .concat a b, next => do
    let eb ← compileNode b next
    compileNode a eb
  | .alt a b, next => do
    let ea ← compileNode a next
    let eb ← compileNode b next
    emit (.split ea eb)
  | .star a, next => do
    let s ← emit (.split 0 0)
    let ea ← compileNode a s
    patch s (.split ea next)
    pure s
  | .assertStart, next => emit (.assertStart next)
  | .assertEnd, next => emit (.assertEnd next)

def compileAst (a : Ast) : Prog × Nat :=
  let (entry, prog) := (do
    let d ← emit .done
    compileNode a d : StateM Prog Nat).run #[]
  (prog, entry)

def compile (pattern : String) : Except String (Prog × Nat) := do
  return compileAst (← Parser.parse pattern)

/-! ## Pike VM -/

/-- ε-closure of `pc` into `seen`, evaluating position assertions at `pos`.
Fuel bounds ε-cycles (`(a*)*`); the visited set makes extra fuel harmless. -/
def add (prog : Prog) (pos len : Nat) : Nat → Array Bool → Nat → Array Bool
  | 0, seen, _ => seen
  | fuel + 1, seen, pc =>
    if seen.getD pc true then seen
    else
      let seen := seen.set! pc true
      match prog.getD pc .done with
      | .split a b => add prog pos len fuel (add prog pos len fuel seen a) b
      | .assertStart n => if pos == 0 then add prog pos len fuel seen n else seen
      | .assertEnd n => if pos == len then add prog pos len fuel seen n else seen
      | _ => seen

def hasDone (prog : Prog) (set : Array Bool) : Bool :=
  (List.range prog.size).any fun pc =>
    set.getD pc false && (prog.getD pc (.split 0 0) matches .done)

private def emptySet (n : Nat) : Array Bool :=
  (List.range n).foldl (fun a _ => a.push false) (Array.emptyWithCapacity n)

private def step (prog : Prog) (entry len : Nat) : List Char → Nat → Array Bool → Bool
  | [], _, _ => false
  | c :: rest, pos, set =>
    let fuel := prog.size + 1
    let stepped := (List.range prog.size).foldl (init := emptySet prog.size) fun acc pc =>
      if set.getD pc false then
        match prog.getD pc .done with
        | .char p n => if p c then add prog (pos + 1) len fuel acc n else acc
        | _ => acc
      else acc
    -- Unanchored search: a fresh attempt may start at every position.
    let stepped := add prog (pos + 1) len fuel stepped entry
    if hasDone prog stepped then true else step prog entry len rest (pos + 1) stepped

def search (prog : Prog) (entry : Nat) (s : String) : Bool :=
  let cs := s.toList
  let len := cs.length
  let fuel := prog.size + 1
  let start := add prog 0 len fuel (emptySet prog.size) entry
  hasDone prog start || step prog entry len cs 0 start

end Cel.Regex

/-- CEL `matches` (RE2 `PartialMatch`): unanchored regular-expression search.
Patterns that fail to parse (or use unsupported constructs) match nothing;
`protoc-gen-lean-protovalidate` validates literal patterns at codegen time. -/
def Cel.regexMatch (s : String) (re : String) : Bool :=
  match Cel.Regex.compile re with
  | .ok (prog, entry) => Cel.Regex.search prog entry s
  | .error _ => false
