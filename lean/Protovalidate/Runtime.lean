module

/-!
Runtime support for `protoc-gen-lean-protovalidate` generated code.

Generated `validate` functions check each CEL rule with a decidable test and
either produce the refined (validated) message or the first `Violation`.
-/

@[expose] public section

namespace Protovalidate

/-- A failed rule, mirroring the essentials of protovalidate's `Violation`:
the offending field (empty for message-level rules), the rule id from the
CEL annotation, and its human-readable message (falling back to the CEL
expression when the annotation carries no message). -/
structure Violation where
  fieldPath : String := ""
  ruleId : String := ""
  message : String := ""
deriving Repr, DecidableEq, Inhabited

instance : ToString Violation where
  toString v :=
    let path := if v.fieldPath.isEmpty then "(message)" else v.fieldPath
    s!"{path}: {v.message} [{v.ruleId}]"

/-!
## Decision: evidence-carrying validation

Generated `M.checkPred` functions decide the message's declarative predicate
`M.ValidPred` wholesale: a `Decision (M.ValidPred b)` is either a proof of
every rule or a refutation together with the *first* violation in protovalidate
rule order. `M.validate` is the `Except` view of that decision, which makes the
generated soundness/completeness theorems instances of the two generic lemmas
below — no per-message proof search.
-/

/-- Outcome of deciding a proposition `p` (a generated `ValidPred`): a proof,
or a refutation carrying the first failing rule's `Violation`. -/
inductive Decision (p : Prop) where
  | ok (h : p)
  | fail (hn : ¬p) (violation : Violation)

namespace Decision

/-- The `Except` view: build the validated value from the proof, or report the
violation. Generated `validate` is `(checkPred b).toExcept (ofPred b)`. -/
def toExcept {p : Prop} {α : Type u} (d : Decision p) (mk : p → α) : Except Violation α :=
  match d with
  | .ok h => .ok (mk h)
  | .fail _ v => .error v

/-- The decision procedure a `Decision` induces (the generated `Decidable`
instances for `ValidPred`). -/
def toDecidable {p : Prop} (d : Decision p) : Decidable p :=
  match d with
  | .ok h => .isTrue h
  | .fail hn _ => .isFalse hn

/-- Success of the `Except` view certifies the predicate: the generic form of
every generated `validate_sound`. -/
theorem pred_of_toExcept_ok {p : Prop} {α : Type u} {d : Decision p} {mk : p → α} {v : α}
    (h : d.toExcept mk = .ok v) : p := by
  cases d with
  | ok hp => exact hp
  | fail hn viol => simp [toExcept] at h

/-- The predicate guarantees success of the `Except` view: the generic form of
every generated `validate_complete`. -/
theorem toExcept_isOk {p : Prop} {α : Type u} {d : Decision p} {mk : p → α}
    (hp : p) : (d.toExcept mk).isOk := by
  cases d with
  | ok _ => rfl
  | fail hn _ => exact absurd hp hn

/-- Chain one field's decision into the whole message's: `proj` recovers the
field's conjunct from the message predicate (for the failure direction), and
`rest` continues with the field's proof in scope. -/
def step {q p : Prop} (d : Decision q) (proj : p → q) (rest : q → Decision p) : Decision p :=
  match d with
  | .ok h => rest h
  | .fail hn v => .fail (fun hp => hn (proj hp)) v

/-- Transport a decision along a propositional equivalence. -/
def imp {q p : Prop} (d : Decision q) (f : q → p) (g : p → q) : Decision p :=
  match d with
  | .ok h => .ok (f h)
  | .fail hn v => .fail (fun hp => hn (g hp)) v

end Decision

/-!
## Option and Array plumbing

Generated `ValidPred` states rules on presence fields as
`∀ x, b.f = some x → …` and on repeated fields as `∀ x ∈ b.f, …`; these
helpers convert between the match-equation form used while checking and that
quantified form, and build the refined values from the proofs.
-/

/-- Vacuous presence-rule proof for the `none` branch (the match motive
generalizes the scrutinee, so the branch sees `none = some x`). -/
theorem someHolds_none {α} {p : α → Prop} : ∀ x, (none : Option α) = some x → p x :=
  fun _ hx => nomatch hx

/-- Presence-rule proof for the `some` branch from the payload's proof. -/
theorem someHolds_self {α} {p : α → Prop} {v : α} (hv : p v) :
    ∀ x, some v = some x → p x := by
  intro x hx
  cases hx
  exact hv

theorem not_isSome_none {α} : ¬ (none : Option α).isSome :=
  fun h => nomatch h

/-- The value of a required presence field (match-based; proofs erase). -/
def getSome {α} : (o : Option α) → o.isSome → α
  | some v, _ => v

/-- Refine a present optional value by the proved rules. -/
def subtypeOption {α} {p : α → Prop} : (o : Option α) → (∀ x, o = some x → p x) →
    Option { x : α // p x }
  | none, _ => none
  | some v, hp => some ⟨v, hp v rfl⟩

/-- Unwrap and refine a required field by the proved rules. -/
def subtypeRequired {α} {p : α → Prop} : (o : Option α) → o.isSome → (∀ x, o = some x → p x) →
    { x : α // p x }
  | some v, _, hp => ⟨v, hp v rfl⟩

/-- Map a proof-taking constructor (a generated `ofPred`) over a present
optional value. -/
def mapOption {α} {β : Type u} {p : α → Prop} : (o : Option α) → ((x : α) → p x → β) →
    (∀ x, o = some x → p x) → Option β
  | none, _, _ => none
  | some v, mk, hp => some (mk v (hp v rfl))

/-- Map a proof-taking constructor over a required field's value. -/
def mapRequired {α} {β : Type u} {p : α → Prop} : (o : Option α) → ((x : α) → p x → β) →
    o.isSome → (∀ x, o = some x → p x) → β
  | some v, mk, _, hp => mk v (hp v rfl)

/-- Map a proof-taking constructor over every element of an array. -/
def mapArray {α} {β : Type u} {p : α → Prop} (xs : Array α) (mk : (x : α) → p x → β)
    (hp : ∀ x, x ∈ xs → p x) : Array β :=
  xs.attach.map fun ⟨x, hx⟩ => mk x (hp x hx)

/-- `mapArray` preserves length: validating a repeated field's elements neither
drops nor duplicates any.

A generated `ValidPred` states a repeated-message field's *own* rules over the
validated array (`mapArray b.f Elem.ofPred h.f_elems`), because those rules may
mention the element type's refinements. This is the bridge back to the base
array for the structural ones: `(validate_sound h).f : (mapArray …).size > 0`
rewrites to `b.f.size > 0` with `size_mapArray`. It is a propositional
rewrite, not a definitional one — `Array.map` is not length-transparent for a
variable array — which is why the conjunct is not phrased over `b.f` directly. -/
@[simp] theorem size_mapArray {α} {β : Type u} {p : α → Prop} (xs : Array α)
    (mk : (x : α) → p x → β) (hp : ∀ x, x ∈ xs → p x) :
    (mapArray xs mk hp).size = xs.size := by
  simp [mapArray]

/-- Decide `p` for every element of a list, reporting the first failure. -/
def checkList {α} {p : α → Prop} (check : (x : α) → Decision (p x)) :
    (l : List α) → Decision (∀ x, x ∈ l → p x)
  | [] => .ok fun _ hx => nomatch hx
  | x :: t =>
    match check x with
    | .fail hn v => .fail (fun hall => hn (hall x List.mem_cons_self)) v
    | .ok hx =>
      match checkList check t with
      | .ok ht => .ok fun y hy =>
          match List.mem_cons.mp hy with
          | .inl he => he ▸ hx
          | .inr hm => ht y hm
      | .fail hn v => .fail (fun hall => hn fun y hy => hall y (List.mem_cons_of_mem x hy)) v

/-- Decide `p` for every element of an array (repeated message fields),
reporting the first failing element's violation. -/
def checkArray {α} {p : α → Prop} (check : (x : α) → Decision (p x)) (xs : Array α) :
    Decision (∀ x, x ∈ xs → p x) :=
  (checkList check xs.toList).imp
    (fun h x hx => h x (Array.mem_toList_iff.mpr hx))
    (fun h x hx => h x (Array.mem_toList_iff.mp hx))

/-!
## decode ∘ validate
-/

/-- Decode the wire format, then validate: the body of every generated
`decodeValid`. -/
def decodeThenValidate {ε : Type u} {α β : Type v} [ToString ε]
    (dec : ByteArray → Except ε α) (val : α → Except Violation β)
    (bytes : ByteArray) : Except String β :=
  match dec bytes with
  | .error e => .error (toString e)
  | .ok m =>
    match val m with
    | .error e => .error (toString e)
    | .ok v => .ok v

/-- Success of `decodeThenValidate` factors through a successful decode and a
successful validate: the generic form of every generated `decodeValid_sound`. -/
theorem decodeThenValidate_sound {ε : Type u} {α β : Type v} [ToString ε]
    {dec : ByteArray → Except ε α} {val : α → Except Violation β}
    {bytes : ByteArray} {v : β}
    (h : decodeThenValidate dec val bytes = .ok v) :
    ∃ m, dec bytes = .ok m ∧ val m = .ok v := by
  unfold decodeThenValidate at h
  split at h
  next e hd => simp at h
  next m hd =>
    split at h
    next e hv => simp at h
    next w hv => cases h; exact ⟨m, hd, hv⟩

end Protovalidate
