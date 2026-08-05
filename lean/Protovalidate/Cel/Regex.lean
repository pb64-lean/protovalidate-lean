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

/- A successful parser result carries the fact that its unconsumed input is a
suffix of the input it was given.  `Progress` additionally records strict
consumption.  These witnesses are erased at runtime, but make every recursive
call below visibly well-founded without an arbitrary fuel limit. -/
private structure Parsed (α : Type) (input : List Char) where
  value : α
  rest : List Char
  suffix : rest <:+ input

private structure Progress (α : Type) (input : List Char) extends Parsed α input where
  shorter : rest.length < input.length

private def suffixRefl (xs : List Char) : xs <:+ xs := ⟨[], rfl⟩
private def suffixTail (x : Char) (xs : List Char) : xs <:+ x :: xs := ⟨[x], rfl⟩

private def Parsed.toPair (p : Parsed α input) : α × List Char := (p.value, p.rest)

private def Parsed.weaken (p : Parsed α middle) (h : middle <:+ input) : Parsed α input :=
  { value := p.value, rest := p.rest, suffix := p.suffix.trans h }

private def Progress.thenParsed (p : Progress α input) (q : Parsed β p.rest) :
    Progress β input :=
  { value := q.value
    rest := q.rest
    suffix := q.suffix.trans p.suffix
    shorter := Nat.lt_of_le_of_lt q.suffix.length_le p.shorter }

private def dropNonGreedy : (cs : List Char) → Parsed Unit cs
  | '?' :: rest => { value := (), rest, suffix := suffixTail '?' rest }
  | rest => { value := (), rest, suffix := suffixRefl rest }

private def stripClassNegation : (cs : List Char) → Parsed Bool cs
  | '^' :: rest => { value := true, rest, suffix := suffixTail '^' rest }
  | rest => { value := false, rest, suffix := suffixRefl rest }

private def escapeCore : (cs : List Char) → Except String (Parsed Esc cs)
  | [] => .error "trailing backslash"
  | 'd' :: rest => .ok { value := .pred digitP, rest, suffix := suffixTail 'd' rest }
  | 'D' :: rest => .ok { value := .pred (!digitP ·), rest, suffix := suffixTail 'D' rest }
  | 'w' :: rest => .ok { value := .pred wordP, rest, suffix := suffixTail 'w' rest }
  | 'W' :: rest => .ok { value := .pred (!wordP ·), rest, suffix := suffixTail 'W' rest }
  | 's' :: rest => .ok { value := .pred spaceP, rest, suffix := suffixTail 's' rest }
  | 'S' :: rest => .ok { value := .pred (!spaceP ·), rest, suffix := suffixTail 'S' rest }
  | 'n' :: rest => .ok { value := .char '\n', rest, suffix := suffixTail 'n' rest }
  | 't' :: rest => .ok { value := .char '\t', rest, suffix := suffixTail 't' rest }
  | 'r' :: rest => .ok { value := .char '\r', rest, suffix := suffixTail 'r' rest }
  | 'f' :: rest => .ok { value := .char '\x0c', rest, suffix := suffixTail 'f' rest }
  | 'v' :: rest => .ok { value := .char '\x0b', rest, suffix := suffixTail 'v' rest }
  | 'a' :: rest => .ok { value := .char '\x07', rest, suffix := suffixTail 'a' rest }
  | '0' :: rest => .ok { value := .char '\x00', rest, suffix := suffixTail '0' rest }
  | 'x' :: rest =>
      match rest with
      | '{' :: more =>
        let ds := more.takeWhile (· != '}')
        match hdrop : more.drop ds.length with
        | '}' :: after =>
          match hexChar? ds with
          | some ch =>
            have h₁ : after <:+ more.drop ds.length := by
              rw [hdrop]
              exact suffixTail '}' after
            have h₂ : more.drop ds.length <:+ more := List.drop_suffix _ _
            .ok {
              value := .char ch
              rest := after
              suffix := h₁.trans (h₂.trans ((suffixTail '{' more).trans
                (suffixTail 'x' ('{' :: more))))
            }
          | none => .error "invalid \\x{...} escape"
        | _ => .error "unterminated \\x{...} escape"
      | h1 :: h2 :: after =>
        match hexChar? [h1, h2] with
        | some ch => .ok {
            value := .char ch
            rest := after
            suffix := (suffixTail h2 after).trans
              ((suffixTail h1 (h2 :: after)).trans (suffixTail 'x' (h1 :: h2 :: after)))
          }
        | none => .error "invalid \\xHH escape"
      | _ => .error "truncated \\x escape"
  | c :: rest =>
      if c.isAlphanum then .error s!"unsupported escape \\{c}"
      else .ok { value := .char c, rest, suffix := suffixTail c rest }

def escape (cs : List Char) : Except String (Esc × List Char) :=
  (escapeCore cs).map Parsed.toPair

/-- Items of a character class; `first` admits `]` as a literal. -/
private def classItemsCore : (cs : List Char) → (first : Bool) →
    (acc : List (Char → Bool)) → Except String (Parsed (List (Char → Bool)) cs)
  | [], _, _ => .error "unterminated character class"
  | ']' :: rest, first, acc => do
    if first then
      have hlt : rest.length < (']' :: rest).length := by simp
      let p ← classItemsCore rest false ((· == ']') :: acc)
      pure (p.weaken (suffixTail ']' rest))
    else
      .ok { value := acc, rest, suffix := suffixTail ']' rest }
  | '\\' :: esc, _, acc => do
    let e ← escapeCore esc
    match e.value with
    | .pred p =>
      have hlt : e.rest.length < ('\\' :: esc).length :=
        Nat.lt_of_le_of_lt e.suffix.length_le (by simp)
      let q ← classItemsCore e.rest false (p :: acc)
      pure (q.weaken (e.suffix.trans (suffixTail '\\' esc)))
    | .char lo =>
      match hrest : e.rest with
      | '-' :: ']' :: rest =>
        have hlt : (']' :: rest).length < ('\\' :: esc).length := by
          have he := e.suffix.length_le
          simp only [List.length_cons] at he ⊢
          simp only [hrest, List.length_cons] at he
          omega
        let q ← classItemsCore (']' :: rest) false ((· == '-') :: (· == lo) :: acc)
        have hs : ']' :: rest <:+ e.rest := by rw [hrest]; exact suffixTail '-' (']' :: rest)
        pure (q.weaken (hs.trans (e.suffix.trans (suffixTail '\\' esc))))
      | '-' :: '\\' :: esc2 =>
        let hi ← escapeCore esc2
        match hi.value with
        | .char ch =>
          have hs : esc2 <:+ e.rest := by
            rw [hrest]
            exact (suffixTail '\\' esc2).trans (suffixTail '-' ('\\' :: esc2))
          have hlt : hi.rest.length < ('\\' :: esc).length := by
            have he := e.suffix.length_le
            have hh := hi.suffix.length_le
            have hslen := hs.length_le
            simp only [List.length_cons] at he hslen ⊢
            omega
          let q ← classItemsCore hi.rest false
            ((fun c => charLE lo c && charLE c ch) :: acc)
          pure (q.weaken (hi.suffix.trans (hs.trans (e.suffix.trans (suffixTail '\\' esc)))))
        | .pred _ => .error "invalid range endpoint"
      | '-' :: hi :: rest =>
        have hlt : rest.length < ('\\' :: esc).length := by
          have he := e.suffix.length_le
          simp only [hrest, List.length_cons] at he
          simp only [List.length_cons]
          omega
        let q ← classItemsCore rest false ((fun c => charLE lo c && charLE c hi) :: acc)
        have hs : rest <:+ e.rest := by
          rw [hrest]
          exact (suffixTail hi rest).trans (suffixTail '-' (hi :: rest))
        pure (q.weaken (hs.trans (e.suffix.trans (suffixTail '\\' esc))))
      | _ =>
        have hlt : e.rest.length < ('\\' :: esc).length :=
          Nat.lt_of_le_of_lt e.suffix.length_le (by simp)
        let q ← classItemsCore e.rest false ((· == lo) :: acc)
        pure (q.weaken (e.suffix.trans (suffixTail '\\' esc)))
  | lo :: rest, _, acc => do
    match rest with
    | '-' :: ']' :: tail =>
      have hlt : (']' :: tail).length < (lo :: '-' :: ']' :: tail).length := by simp
      let q ← classItemsCore (']' :: tail) false ((· == '-') :: (· == lo) :: acc)
      pure (q.weaken ((suffixTail '-' (']' :: tail)).trans
        (suffixTail lo ('-' :: ']' :: tail))))
    | '-' :: '\\' :: esc =>
      let hi ← escapeCore esc
      match hi.value with
      | .char ch =>
        have hlt : hi.rest.length < (lo :: '-' :: '\\' :: esc).length := by
          have hh := hi.suffix.length_le
          simp only [List.length_cons] at hh ⊢
          omega
        let q ← classItemsCore hi.rest false
          ((fun c => charLE lo c && charLE c ch) :: acc)
        pure (q.weaken (hi.suffix.trans
          ((suffixTail '\\' esc).trans ((suffixTail '-' ('\\' :: esc)).trans
            (suffixTail lo ('-' :: '\\' :: esc))))))
      | .pred _ => .error "invalid range endpoint"
    | '-' :: hi :: tail =>
      have hlt : tail.length < (lo :: '-' :: hi :: tail).length := by
        simp only [List.length_cons]
        omega
      let q ← classItemsCore tail false ((fun c => charLE lo c && charLE c hi) :: acc)
      pure (q.weaken ((suffixTail hi tail).trans
        ((suffixTail '-' (hi :: tail)).trans (suffixTail lo ('-' :: hi :: tail)))))
    | other =>
      have hlt : other.length < (lo :: other).length := by simp
      let q ← classItemsCore other false ((· == lo) :: acc)
      pure (q.weaken (suffixTail lo other))
  termination_by cs _ _ => cs.length
  decreasing_by all_goals assumption

def classItems (cs : List Char) (first : Bool) (acc : List (Char → Bool)) :
    Except String (List (Char → Bool) × List Char) :=
  (classItemsCore cs first acc).map Parsed.toPair

/-- After a literal class element: either the low end of a range or a lone
character. -/
def classRange (lo : Char) (cs : List Char) (acc : List (Char → Bool)) :
    Except String (List (Char → Bool) × List Char) := do
  match cs with
  | '-' :: ']' :: rest =>
    classItems (']' :: rest) false ((· == '-') :: (· == lo) :: acc)
  | '-' :: '\\' :: esc =>
    match ← escape esc with
    | (.char hi, r) => classItems r false ((fun ch => charLE lo ch && charLE ch hi) :: acc)
    | (.pred _, _) => .error "invalid range endpoint"
  | '-' :: hi :: rest => classItems rest false ((fun ch => charLE lo ch && charLE ch hi) :: acc)
  | _ => classItems cs false ((· == lo) :: acc)

/-- Parse the interior of a character class (after `[`), producing its
predicate. -/
private def parseClassCore (cs : List Char) :
    Except String (Parsed (Char → Bool) cs) := do
  let head := stripClassNegation cs
  let items ← classItemsCore head.rest true []
  let base := fun ch => items.value.any (· ch)
  .ok {
    value := if head.value then (fun ch => !base ch) else base
    rest := items.rest
    suffix := items.suffix.trans head.suffix
  }

def parseClass (cs : List Char) : Except String ((Char → Bool) × List Char) :=
  (parseClassCore cs).map Parsed.toPair

def repeatN (a : Ast) : Nat → Ast
  | 0 => .epsilon
  | 1 => a
  | n + 1 => .concat a (repeatN a n)

def optChain (a : Ast) : Nat → Ast
  | 0 => .epsilon
  | n + 1 => .alt (.concat a (optChain a n)) .epsilon

def natOf (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

private def quantifyCore (a : Ast) : (cs : List Char) → Except String (Parsed Ast cs)
  | '*' :: rest => do
    let ng := dropNonGreedy rest
    have hlt : ng.rest.length < ('*' :: rest).length :=
      Nat.lt_of_le_of_lt ng.suffix.length_le (by simp)
    let q ← quantifyCore (.star a) ng.rest
    pure (q.weaken (ng.suffix.trans (suffixTail '*' rest)))
  | '+' :: rest => do
    let ng := dropNonGreedy rest
    have hlt : ng.rest.length < ('+' :: rest).length :=
      Nat.lt_of_le_of_lt ng.suffix.length_le (by simp)
    let q ← quantifyCore (.concat a (.star a)) ng.rest
    pure (q.weaken (ng.suffix.trans (suffixTail '+' rest)))
  | '?' :: rest => do
    let ng := dropNonGreedy rest
    have hlt : ng.rest.length < ('?' :: rest).length :=
      Nat.lt_of_le_of_lt ng.suffix.length_le (by simp)
    let q ← quantifyCore (.alt a .epsilon) ng.rest
    pure (q.weaken (ng.suffix.trans (suffixTail '?' rest)))
  | '{' :: rest => do
    let lo := rest.takeWhile Char.isDigit
    if lo.isEmpty then
      .ok { value := a, rest := '{' :: rest, suffix := suffixRefl ('{' :: rest) }
    else
      let n := natOf lo
      match hdrop : rest.drop lo.length with
      | '}' :: r2 =>
        if n > 512 then .error "repetition bound too large" else
        let ng := dropNonGreedy r2
        have hs : r2 <:+ rest := by
          have hd : rest.drop lo.length <:+ rest := List.drop_suffix _ _
          have ht : r2 <:+ rest.drop lo.length := by rw [hdrop]; exact suffixTail '}' r2
          exact ht.trans hd
        have hlt : ng.rest.length < ('{' :: rest).length :=
          Nat.lt_of_le_of_lt (ng.suffix.trans hs).length_le (by simp)
        let q ← quantifyCore (repeatN a n) ng.rest
        pure (q.weaken (ng.suffix.trans (hs.trans (suffixTail '{' rest))))
      | ',' :: '}' :: r2 =>
        if n > 512 then .error "repetition bound too large" else
        let ng := dropNonGreedy r2
        have hs : r2 <:+ rest := by
          have hd : rest.drop lo.length <:+ rest := List.drop_suffix _ _
          have ht : r2 <:+ rest.drop lo.length := by
            rw [hdrop]
            exact (suffixTail '}' r2).trans (suffixTail ',' ('}' :: r2))
          exact ht.trans hd
        have hlt : ng.rest.length < ('{' :: rest).length :=
          Nat.lt_of_le_of_lt (ng.suffix.trans hs).length_le (by simp)
        let q ← quantifyCore (.concat (repeatN a n) (.star a)) ng.rest
        pure (q.weaken (ng.suffix.trans (hs.trans (suffixTail '{' rest))))
      | ',' :: r2 =>
        let hi := r2.takeWhile Char.isDigit
        match hhi : r2.drop hi.length with
        | '}' :: r3 =>
          let m := natOf hi
          if m > 512 || m < n then .error "invalid repetition bounds" else
          let ng := dropNonGreedy r3
          have hs : r3 <:+ rest := by
            have hd₁ : rest.drop lo.length <:+ rest := List.drop_suffix _ _
            have hr2 : r2 <:+ rest.drop lo.length := by rw [hdrop]; exact suffixTail ',' r2
            have hd₂ : r2.drop hi.length <:+ r2 := List.drop_suffix _ _
            have hr3 : r3 <:+ r2.drop hi.length := by rw [hhi]; exact suffixTail '}' r3
            exact hr3.trans (hd₂.trans (hr2.trans hd₁))
          have hlt : ng.rest.length < ('{' :: rest).length :=
            Nat.lt_of_le_of_lt (ng.suffix.trans hs).length_le (by simp)
          let q ← quantifyCore (.concat (repeatN a n) (optChain a (m - n))) ng.rest
          pure (q.weaken (ng.suffix.trans (hs.trans (suffixTail '{' rest))))
        | _ => .error "unterminated repetition"
      | _ => .error "unterminated repetition"
  | cs => .ok { value := a, rest := cs, suffix := suffixRefl cs }
  termination_by cs => cs.length
  decreasing_by all_goals assumption

def quantify (a : Ast) (cs : List Char) : Except String (Ast × List Char) :=
  (quantifyCore a cs).map Parsed.toPair

mutual

private def parseAltCore (cs : List Char) : Except String (Parsed Ast cs) := do
  let p ← parseConcatCore cs
  match hrest : p.rest with
  | '|' :: rest =>
    have hlt : 4 * rest.length + 3 < 4 * cs.length + 3 := by
      have hp := p.suffix.length_le
      simp only [hrest, List.length_cons] at hp
      omega
    let q ← parseAltCore rest
    have hs : rest <:+ p.rest := by rw [hrest]; exact suffixTail '|' rest
    .ok {
      value := .alt p.value q.value
      rest := q.rest
      suffix := q.suffix.trans (hs.trans p.suffix)
    }
  | _ => .ok p
  termination_by 4 * cs.length + 3
  decreasing_by all_goals first | assumption | omega

private def parseConcatCore : (cs : List Char) → Except String (Parsed Ast cs)
  | [] => .ok { value := .epsilon, rest := [], suffix := suffixRefl [] }
  | '|' :: rest => .ok {
      value := .epsilon, rest := '|' :: rest, suffix := suffixRefl ('|' :: rest) }
  | ')' :: rest => .ok {
      value := .epsilon, rest := ')' :: rest, suffix := suffixRefl (')' :: rest) }
  | cs => do
    let p ← parseRepeatCore cs
    have hlt : 4 * p.rest.length + 2 < 4 * cs.length + 2 := by
      have hp := p.shorter
      omega
    let q ← parseConcatCore p.rest
    .ok {
      value := match q.value with | .epsilon => p.value | _ => .concat p.value q.value
      rest := q.rest
      suffix := q.suffix.trans p.suffix
    }
  termination_by cs => 4 * cs.length + 2
  decreasing_by all_goals first | assumption | omega

private def parseRepeatCore (cs : List Char) : Except String (Progress Ast cs) := do
  let p ← parseAtomCore cs
  let q ← quantifyCore p.value p.rest
  pure (p.thenParsed q)
  termination_by 4 * cs.length + 1
  decreasing_by all_goals omega

private def parseAtomCore : (cs : List Char) → Except String (Progress Ast cs)
  | [] => .error "expected atom"
  | '(' :: rest => do
    let group ← (match rest with
      | '?' :: ':' :: r => pure {
          value := (), rest := r,
          suffix := (suffixTail ':' r).trans (suffixTail '?' (':' :: r))
        }
      | '?' :: _ => .error "unsupported (?...) group"
      | r => pure { value := (), rest := r, suffix := suffixRefl r } :
        Except String (Parsed Unit rest))
    have hlt : 4 * group.rest.length + 3 < 4 * ('(' :: rest).length := by
      have hg := group.suffix.length_le
      simp only [List.length_cons]
      omega
    let p ← parseAltCore group.rest
    match hclose : p.rest with
    | ')' :: r2 =>
      have hs : r2 <:+ p.rest := by rw [hclose]; exact suffixTail ')' r2
      have hall : r2 <:+ '(' :: rest :=
        hs.trans (p.suffix.trans (group.suffix.trans (suffixTail '(' rest)))
      .ok {
        value := p.value
        rest := r2
        suffix := hall
        shorter := by
          have := (hs.trans (p.suffix.trans group.suffix)).length_le
          simp only [List.length_cons]
          omega
      }
    | _ => .error "unterminated group"
  | '[' :: rest => do
    let p ← parseClassCore rest
    .ok {
      value := .char p.value
      rest := p.rest
      suffix := p.suffix.trans (suffixTail '[' rest)
      shorter := Nat.lt_of_le_of_lt p.suffix.length_le (by simp)
    }
  | '\\' :: rest => do
    let p ← escapeCore rest
    .ok {
      value := match p.value with | .char ch => .char (· == ch) | .pred pred => .char pred
      rest := p.rest
      suffix := p.suffix.trans (suffixTail '\\' rest)
      shorter := Nat.lt_of_le_of_lt p.suffix.length_le (by simp)
    }
  | '.' :: rest => .ok {
      value := .char (· != '\n'), rest, suffix := suffixTail '.' rest, shorter := by simp }
  | '^' :: rest => .ok {
      value := .assertStart, rest, suffix := suffixTail '^' rest, shorter := by simp }
  | '$' :: rest => .ok {
      value := .assertEnd, rest, suffix := suffixTail '$' rest, shorter := by simp }
  | '*' :: _ | '+' :: _ | '?' :: _ => .error "quantifier without operand"
  | c :: rest => .ok {
      value := .char (· == c), rest, suffix := suffixTail c rest, shorter := by simp }
  termination_by cs => 4 * cs.length
  decreasing_by all_goals first | assumption | omega

end

def parseAlt (cs : List Char) : Except String (Ast × List Char) :=
  (parseAltCore cs).map Parsed.toPair

def parseConcat (cs : List Char) : Except String (Ast × List Char) :=
  (parseConcatCore cs).map Parsed.toPair

def parseRepeat (cs : List Char) : Except String (Ast × List Char) :=
  (parseRepeatCore cs).map fun p => (p.value, p.rest)

def parseAtom (cs : List Char) : Except String (Ast × List Char) :=
  (parseAtomCore cs).map fun p => (p.value, p.rest)

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

/-- Acceptance check for the supported RE2 subset: `true` iff `pattern` parses
in this engine. Generated code emits a `#guard Cel.Regex.accepts "..."` for
every literal pattern, so a pattern outside the subset fails the Lean build
instead of silently matching nothing (which would be unsound under negation:
`!matches(...)` would degenerate to `true`). -/
def Cel.Regex.accepts (pattern : String) : Bool :=
  (Cel.Regex.compile pattern).isOk

-- The acceptance check must agree with the engine on representative patterns;
-- the Go generator ports this grammar (celtolean/regexcheck.go) and its tests
-- mirror these expectations.
#guard Cel.Regex.accepts "^[a-z][a-z0-9-]*$"
#guard Cel.Regex.accepts "^(cat|dog)$"
#guard Cel.Regex.accepts "^a{2,3}\\d\\w\\s$"
#guard !Cel.Regex.accepts "(?i)x"
#guard !Cel.Regex.accepts "\\bword"
#guard !Cel.Regex.accepts "(?P<name>a)"
#guard !Cel.Regex.accepts "a{1000}"
#guard !Cel.Regex.accepts "[a-"

/-- Checked CEL `matches` (RE2 `PartialMatch`): an unanchored search that keeps
an unsupported pattern distinct from a valid pattern with no match. -/
def Cel.regexMatchChecked (s : String) (re : String) : Except String Bool := do
  let (prog, entry) ← Cel.Regex.compile re
  pure (Cel.Regex.search prog entry s)

/-- Boolean CEL `matches` used by generated validation predicates.
Patterns that fail to parse (or use unsupported constructs) match nothing;
literal patterns are rejected at codegen time (Go subset check) and guarded at
Lean compile time (`Cel.Regex.accepts`), while generated dynamic patterns are
rejected outright. Direct callers with an untrusted pattern should use
`Cel.regexMatchChecked` so a parse error cannot be mistaken for `false`. -/
def Cel.regexMatch (s : String) (re : String) : Bool :=
  match Cel.regexMatchChecked s re with
  | .ok matched => matched
  | .error _ => false

#guard match Cel.regexMatchChecked "admin" "^admin$" with
  | .ok true => true
  | _ => false
#guard match Cel.regexMatchChecked "admin" "(?i)admin" with
  | .error _ => true
  | .ok _ => false
