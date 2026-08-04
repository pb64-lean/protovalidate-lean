import Protovalidate.Runtime

/-!
Hand-written mirror of the generator's Phase-6 emission scheme, exercised
against stand-in message types. Every declaration shape here corresponds 1:1
to what `protoc-gen-lean-protovalidate` emits:

* `M.ValidPred`  — dependent Prop structure over the base value: one field per
  rule conjunct (presence, per-field rules, nested-message predicates), with
  message-level rules phrased over views of the *constructed* validated fields;
* `M.checkPred`  — a `Protovalidate.Decision (M.ValidPred b)` built by chaining
  per-field decisions with `Decision.step`;
* `M.ofPred`     — total constructor of the validated structure from the proof;
* `M.validate`   — `(checkPred b).toExcept (ofPred b)`;
* theorems       — instances of the generic Decision lemmas.

If this file compiles and its runtime assertions pass, every elaboration
assumption the generator relies on (dependent Prop-structure fields,
proof-irrelevant transfer in `ofPred`, `step`'s projection glue) holds.
-/

structure BItem where
  sku : String := ""
  quantity : Int := 0
  -- stands in for the base codegen's «Unknown.Fields» (dropped by toBase)
  unknownStub : Nat := 0

inductive BPayer where
  | customer (s : String)
  | account (s : String)

structure BOrder where
  id : String := ""
  status : String := ""
  tracking : Option String := none
  note : String := ""
  items : Array BItem := #[]
  discount : Option Int := none
  featured : Option BItem := none
  owner : Option String := none
  payer : Option BPayer := none

namespace Valid

/-! ### Item: plain constrained fields -/

structure Item.ValidPred (b : BItem) : Prop where
  sku : b.sku.length ≥ 3 ∧ b.sku.length ≤ 32
  quantity : b.quantity > 0

structure Item where
  sku : { x : String // x.length ≥ 3 ∧ x.length ≤ 32 }
  quantity : { x : Int // x > 0 }

def Item.checkPred (b : BItem) : Protovalidate.Decision (Item.ValidPred b) :=
  Protovalidate.Decision.step (q := b.sku.length ≥ 3 ∧ b.sku.length ≤ 32)
    (if h0 : b.sku.length ≥ 3 then
      if h1 : b.sku.length ≤ 32 then
        .ok ⟨h0, h1⟩
      else .fail (fun hc => h1 hc.2) { fieldPath := "sku", ruleId := "sku.max", message := "too long" }
    else .fail (fun hc => h0 hc.1) { fieldPath := "sku", ruleId := "sku.min", message := "too short" })
    (fun hh => hh.sku)
    fun h_sku =>
  Protovalidate.Decision.step (q := b.quantity > 0)
    (if h0 : b.quantity > 0 then .ok h0
     else .fail (fun hc => h0 hc) { fieldPath := "quantity", ruleId := "q.pos", message := "must be positive" })
    (fun hh => hh.quantity)
    fun h_quantity =>
  .ok ⟨h_sku, h_quantity⟩

def Item.ofPred (b : BItem) (h : Item.ValidPred b) : Item :=
  { sku := ⟨b.sku, h.sku⟩, quantity := ⟨b.quantity, h.quantity⟩ }

def Item.validate (b : BItem) : Except Protovalidate.Violation Item :=
  (Item.checkPred b).toExcept (Item.ofPred b)

def Item.toBase (v : Item) : BItem :=
  { sku := v.sku.val, quantity := v.quantity.val }

instance Item.instDecidableValidPred : (b : BItem) → Decidable (Item.ValidPred b) :=
  fun b => (Item.checkPred b).toDecidable

theorem Item.validate_sound {b : BItem} {v : Item} (h : Item.validate b = .ok v) :
    Item.ValidPred b :=
  Protovalidate.Decision.pred_of_toExcept_ok h

theorem Item.validate_complete {b : BItem} (h : Item.ValidPred b) : (Item.validate b).isOk :=
  Protovalidate.Decision.toExcept_isOk h

/-! ### payer: constrained oneof sum -/

inductive Order.payer_Type where
  | customer : { x : String // x.length ≥ 3 } → Order.payer_Type
  | account : String → Order.payer_Type

def Order.payer_Type.ValidPred : BPayer → Prop
  | .customer x => x.length ≥ 3
  | .account _ => True

def Order.payer_Type.checkPred : (b : BPayer) → Protovalidate.Decision (Order.payer_Type.ValidPred b)
  | .customer x =>
    if h0 : x.length ≥ 3 then .ok h0
    else .fail (fun hc => h0 hc) { fieldPath := "customer", ruleId := "c.min", message := "short" }
  | .account _ => .ok True.intro

def Order.payer_Type.ofPred : (b : BPayer) → Order.payer_Type.ValidPred b → Order.payer_Type
  | .customer x, h => .customer ⟨x, h⟩
  | .account x, _ => .account x

def Order.payer_Type.validate (b : BPayer) : Except Protovalidate.Violation Order.payer_Type :=
  (Order.payer_Type.checkPred b).toExcept (Order.payer_Type.ofPred b)

def Order.payer_Type.toBase : Order.payer_Type → BPayer
  | .customer x => .customer x.val
  | .account x => .account x

instance Order.payer_Type.instDecidableValidPred :
    (b : BPayer) → Decidable (Order.payer_Type.ValidPred b) :=
  fun b => (Order.payer_Type.checkPred b).toDecidable

theorem Order.payer_Type.validate_sound {b : BPayer} {v : Order.payer_Type}
    (h : Order.payer_Type.validate b = .ok v) : Order.payer_Type.ValidPred b :=
  Protovalidate.Decision.pred_of_toExcept_ok h

def Order.payer_Type.customer_or_default : Option Order.payer_Type → String
  | some (.customer v) => v.val
  | _ => ""

/-! ### Order: every remaining shape -/

def Order.featuredD (featured : Option Item) : BItem :=
  (featured.map Item.toBase).getD {}

structure Order.ValidPred (b : BOrder) : Prop where
  id : b.id.length = 8
  note : b.note.isEmpty ∨ (b.note.length ≥ 3)
  items_elems : ∀ x ∈ b.items, Item.ValidPred x
  items : (Protovalidate.mapArray b.items Item.ofPred items_elems).size > 0
  discount : ∀ x, b.discount = some x → (x ≥ 0 ∧ x % 100 = 0)
  featured : ∀ x, b.featured = some x → Item.ValidPred x
  owner_present : b.owner.isSome
  owner : ∀ x, b.owner = some x → (x.length ≥ 2)
  payer : ∀ x, b.payer = some x → Order.payer_Type.ValidPred x
  order_tracking : b.status = "SHIPPED" → b.tracking.isSome
  order_featured_not_banned :
    (Order.featuredD (Protovalidate.mapOption b.featured Item.ofPred featured)).sku ≠ "banned"
  order_payer_len :
    (Order.payer_Type.customer_or_default
      (Protovalidate.mapOption b.payer Order.payer_Type.ofPred payer)).length ≤ 20
  order_owner_first :
    (Protovalidate.subtypeRequired b.owner owner_present owner).val ≠ "root"

structure Order where
  id : { x : String // x.length = 8 }
  status : String
  tracking : Option String
  note : { x : String // x.isEmpty ∨ (x.length ≥ 3) }
  items : { x : Array Item // x.size > 0 }
  discount : Option { x : Int // x ≥ 0 ∧ x % 100 = 0 }
  featured : Option Item
  owner : { x : String // x.length ≥ 2 }
  payer : Option Order.payer_Type
  order_tracking : status = "SHIPPED" → tracking.isSome
  order_featured_not_banned : (Order.featuredD featured).sku ≠ "banned"
  order_payer_len : (Order.payer_Type.customer_or_default payer).length ≤ 20
  order_owner_first : owner.val ≠ "root"

def Order.checkPred (b : BOrder) : Protovalidate.Decision (Order.ValidPred b) :=
  Protovalidate.Decision.step (q := b.id.length = 8)
    (if h0 : b.id.length = 8 then .ok h0
     else .fail (fun hc => h0 hc) { fieldPath := "id", ruleId := "id.len", message := "len" })
    (fun hh => hh.id) fun h_id =>
  Protovalidate.Decision.step (q := b.note.isEmpty ∨ (b.note.length ≥ 3))
    (if h_z : b.note.isEmpty then .ok (Or.inl h_z)
     else
       if h0 : b.note.length ≥ 3 then .ok (Or.inr h0)
       else .fail (fun hc => hc.elim h_z (fun hcc => h0 hcc))
         { fieldPath := "note", ruleId := "note.min", message := "short note" })
    (fun hh => hh.note) fun h_note =>
  Protovalidate.Decision.step (q := ∀ x ∈ b.items, Item.ValidPred x)
    (Protovalidate.checkArray Item.checkPred b.items)
    (fun hh => hh.items_elems) fun h_items_elems =>
  Protovalidate.Decision.step
    (q := (Protovalidate.mapArray b.items Item.ofPred h_items_elems).size > 0)
    (if h0 : (Protovalidate.mapArray b.items Item.ofPred h_items_elems).size > 0 then .ok h0
     else .fail (fun hc => h0 hc) { fieldPath := "items", ruleId := "items.nonempty", message := "empty" })
    (fun hh => hh.items) fun h_items =>
  Protovalidate.Decision.step (q := ∀ x, b.discount = some x → (x ≥ 0 ∧ x % 100 = 0))
    (match b.discount with
     | none => .ok Protovalidate.someHolds_none
     | some v =>
       if h0 : v ≥ 0 then
         if h1 : v % 100 = 0 then .ok (Protovalidate.someHolds_self ⟨h0, h1⟩)
         else .fail (fun hc => h1 (hc v rfl).2)
           { fieldPath := "discount", ruleId := "d.mod", message := "mod" }
       else .fail (fun hc => h0 (hc v rfl).1)
         { fieldPath := "discount", ruleId := "d.pos", message := "neg" })
    (fun hh => hh.discount) fun h_discount =>
  Protovalidate.Decision.step (q := ∀ x, b.featured = some x → Item.ValidPred x)
    (match b.featured with
     | none => .ok Protovalidate.someHolds_none
     | some v =>
       (Item.checkPred v).imp Protovalidate.someHolds_self (fun hq => hq v rfl))
    (fun hh => hh.featured) fun h_featured =>
  Protovalidate.Decision.step (q := b.owner.isSome ∧ (∀ x, b.owner = some x → (x.length ≥ 2)))
    (match b.owner with
     | none => .fail (fun hc => Protovalidate.not_isSome_none hc.1)
         { fieldPath := "owner", ruleId := "required", message := "value is required" }
     | some v =>
       if h0 : v.length ≥ 2 then
         .ok ⟨rfl, Protovalidate.someHolds_self h0⟩
       else .fail (fun hc => h0 (hc.2 v rfl))
         { fieldPath := "owner", ruleId := "o.min", message := "short owner" })
    (fun hh => ⟨hh.owner_present, hh.owner⟩) fun ⟨h_owner_present, h_owner⟩ =>
  Protovalidate.Decision.step (q := ∀ x, b.payer = some x → Order.payer_Type.ValidPred x)
    (match b.payer with
     | none => .ok Protovalidate.someHolds_none
     | some v =>
       (Order.payer_Type.checkPred v).imp Protovalidate.someHolds_self (fun hq => hq v rfl))
    (fun hh => hh.payer) fun h_payer =>
  if h_order_tracking : b.status = "SHIPPED" → b.tracking.isSome then
    if h_order_featured_not_banned :
        (Order.featuredD (Protovalidate.mapOption b.featured Item.ofPred h_featured)).sku ≠ "banned" then
      if h_order_payer_len :
          (Order.payer_Type.customer_or_default
            (Protovalidate.mapOption b.payer Order.payer_Type.ofPred h_payer)).length ≤ 20 then
        if h_order_owner_first :
            (Protovalidate.subtypeRequired b.owner h_owner_present h_owner).val ≠ "root" then
          .ok ⟨h_id, h_note, h_items_elems, h_items, h_discount, h_featured, h_owner_present,
               h_owner, h_payer, h_order_tracking, h_order_featured_not_banned,
               h_order_payer_len, h_order_owner_first⟩
        else .fail (fun hh => h_order_owner_first hh.order_owner_first)
          { fieldPath := "", ruleId := "order.owner_first", message := "root owner" }
      else .fail (fun hh => h_order_payer_len hh.order_payer_len)
        { fieldPath := "", ruleId := "order.payer_len", message := "payer too long" }
    else .fail (fun hh => h_order_featured_not_banned hh.order_featured_not_banned)
      { fieldPath := "", ruleId := "order.featured_not_banned", message := "banned" }
  else .fail (fun hh => h_order_tracking hh.order_tracking)
    { fieldPath := "", ruleId := "order.tracking", message := "tracking required" }

def Order.ofPred (b : BOrder) (h : Order.ValidPred b) : Order :=
  { id := ⟨b.id, h.id⟩
    status := b.status
    tracking := b.tracking
    note := ⟨b.note, h.note⟩
    items := ⟨Protovalidate.mapArray b.items Item.ofPred h.items_elems, h.items⟩
    discount := Protovalidate.subtypeOption b.discount h.discount
    featured := Protovalidate.mapOption b.featured Item.ofPred h.featured
    owner := Protovalidate.subtypeRequired b.owner h.owner_present h.owner
    payer := Protovalidate.mapOption b.payer Order.payer_Type.ofPred h.payer
    order_tracking := h.order_tracking
    order_featured_not_banned := h.order_featured_not_banned
    order_payer_len := h.order_payer_len
    order_owner_first := h.order_owner_first }

def Order.validate (b : BOrder) : Except Protovalidate.Violation Order :=
  (Order.checkPred b).toExcept (Order.ofPred b)

instance Order.instDecidableValidPred : (b : BOrder) → Decidable (Order.ValidPred b) :=
  fun b => (Order.checkPred b).toDecidable

theorem Order.validate_sound {b : BOrder} {v : Order} (h : Order.validate b = .ok v) :
    Order.ValidPred b :=
  Protovalidate.Decision.pred_of_toExcept_ok h

theorem Order.validate_complete {b : BOrder} (h : Order.ValidPred b) : (Order.validate b).isOk :=
  Protovalidate.Decision.toExcept_isOk h

end Valid

/-! ### The theorems are usable downstream -/

example {b : BOrder} {v : Valid.Order} (h : Valid.Order.validate b = .ok v) :
    Valid.Order.ValidPred b :=
  Valid.Order.validate_sound h

example {b : BOrder} (h : Valid.Order.ValidPred b) : (Valid.Order.validate b).isOk :=
  Valid.Order.validate_complete h

-- Soundness gives the field conjuncts back over the *input* value.
example {b : BOrder} {v : Valid.Order} (h : Valid.Order.validate b = .ok v) :
    ∀ x, b.owner = some x → x.length ≥ 2 :=
  (Valid.Order.validate_sound h).owner

/-! ### Runtime assertions -/

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectId (r : Except Protovalidate.Violation α) (id : String) (label : String) : IO Unit := do
  let ok := match r with
    | .error e => e.ruleId == id
    | .ok _ => id == ""
  unless ok do
    let got := match r with
      | .error e => toString e
      | .ok _ => "ok"
    throw (IO.userError s!"{label}: expected {id}, got {got}")

def goodItem : BItem := { sku := "widget", quantity := 2, unknownStub := 7 }

def goodOrder : BOrder :=
  { id := "ord-1234", status := "NEW", items := #[goodItem],
    discount := some 500, featured := some goodItem, owner := some "bill",
    payer := some (.customer "acme") }

def main : IO Unit := do
  -- success path and construction
  match Valid.Order.validate goodOrder with
  | .error e => throw (IO.userError s!"good order: {e}")
  | .ok v => do
    expect (v.id.val == "ord-1234") "id kept"
    expect (v.items.val.size == 1) "items mapped"
    expect ((v.items.val.map (·.sku.val)) == #["widget"]) "element kept"
    expect (v.owner.val == "bill") "owner unwrapped"
    expect ((v.featured.map (·.quantity.val)) == some 2) "featured mapped"

  -- the Decidable instance runs checkPred
  expect (decide (Valid.Item.ValidPred goodItem)) "decide good item"
  expect (!decide (Valid.Item.ValidPred { goodItem with quantity := 0 })) "decide bad item"
  expect (decide (Valid.Order.ValidPred goodOrder)) "decide good order"
  expect (!decide (Valid.Order.ValidPred { goodOrder with owner := none })) "decide bad order"

  -- first-violation order matches the rule order
  expectId (Valid.Order.validate { goodOrder with id := "nope", owner := none }) "id.len" "id first"
  expectId (Valid.Order.validate { goodOrder with note := "ab" }) "note.min" "ignore-zero escape"
  expectId (Valid.Order.validate { goodOrder with note := "" }) "" "zero note skips"
  expectId (Valid.Order.validate { goodOrder with items := #[{ goodItem with sku := "x" }] })
    "sku.min" "element violation propagates"
  expectId (Valid.Order.validate { goodOrder with items := #[] }) "items.nonempty" "list rule"
  expectId (Valid.Order.validate { goodOrder with discount := some 3 }) "d.mod" "option rule"
  expectId (Valid.Order.validate { goodOrder with owner := none }) "required" "required"
  expectId (Valid.Order.validate { goodOrder with owner := some "x" }) "o.min" "required rule"
  expectId (Valid.Order.validate { goodOrder with payer := some (.customer "ab") }) "c.min" "oneof rule"
  expectId (Valid.Order.validate { goodOrder with status := "SHIPPED" }) "order.tracking" "message rule"
  expectId (Valid.Order.validate { goodOrder with featured := some { goodItem with sku := "banned" } })
    "order.featured_not_banned" "message rule over view"
  expectId (Valid.Order.validate { goodOrder with owner := some "root" })
    "order.owner_first" "message rule over required view"

  IO.println "all pred-scheme assertions passed"
