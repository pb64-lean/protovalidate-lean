import ShippingLean.shipping
import ShippingValid.shipping
import Protovalidate.Runtime

/-!
Runtime behavior of the generated refinement types: `validate` decides the
CEL rules on plain (decoded) messages, producing the refined structure whose
types carry the constraints, and `toBase` forgets them again.
-/

open shipping.v1

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectOk (result : Except Protovalidate.Violation α) (msg : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError s!"{msg}: unexpected violation {e}")

def expectViolation (result : Except Protovalidate.Violation α) (ruleId : String) (msg : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{msg}: expected violation {ruleId}, got ok")
  | .error e => expect (e.ruleId == ruleId) s!"{msg}: expected {ruleId}, got {e}"

def goodItem : Item := { sku := "widget", quantity := 2 }

def goodOrder : Order :=
  { id := "ord-1234"
    status := "NEW"
    items := #[goodItem]
    discount_cents := some 500 }

def main : IO Unit := do
  -- Field rules on a nested message.
  let vItem ← expectOk (Valid.Item.validate goodItem) "good item"
  expect (vItem.sku.val == "widget") "item sku roundtrip"
  expectViolation (Valid.Item.validate { goodItem with sku := "ab" }) "sku.format" "short sku"
  expectViolation (Valid.Item.validate { goodItem with quantity := 0 }) "quantity.positive" "zero quantity"

  -- Field rules, multi-rule fields, Option fields, repeated message fields.
  let v ← expectOk (Valid.Order.validate goodOrder) "good order"
  expect (v.id.val == "ord-1234") "order id"
  expect (v.items.val.size == 1) "validated items count"
  expect (v.toBase.id == goodOrder.id) "toBase id"
  expect ((v.toBase.items.map (·.sku)) == #["widget"]) "toBase items"

  expectViolation (Valid.Order.validate { goodOrder with id := "ord-12345" }) "id.len" "long id"
  expectViolation (Valid.Order.validate { goodOrder with id := "xrd-1234" }) "id.prefix" "bad prefix"
  expectViolation (Valid.Order.validate { goodOrder with items := #[] }) "items.nonempty" "no items"
  expectViolation (Valid.Order.validate { goodOrder with items := #[{ goodItem with sku := "x" }] })
    "sku.format" "invalid nested item"
  expectViolation (Valid.Order.validate { goodOrder with discount_cents := some 150 })
    "discount.range" "odd discount"
  let noDiscount ← expectOk (Valid.Order.validate { goodOrder with discount_cents := none }) "absent optional"
  expect noDiscount.discount_cents.isNone "absent optional stays none"

  -- Message-level rule: SHIPPED requires tracking (CEL ternary as implication).
  expectViolation (Valid.Order.validate { goodOrder with status := "SHIPPED" })
    "order.tracking" "shipped without tracking"
  let shipped ← expectOk
    (Valid.Order.validate { goodOrder with status := "SHIPPED", tracking := some "TN123" })
    "shipped with tracking"
  expect shipped.tracking.isSome "tracking kept"

  -- Arithmetic with CEL overflow semantics: quantity * 100 computed in the
  -- CEL domain — an in-range violation and a 32-bit overflow both fail.
  expectViolation (Valid.Item.validate { goodItem with quantity := 10001 })
    "quantity.capacity" "over capacity"
  expectViolation (Valid.Item.validate { goodItem with quantity := 30000000 })
    "quantity.capacity" "capacity overflow guard"

  -- Map selection sugar: this.labels.priority is guarded key access.
  expectViolation
    (Valid.Order.validate { goodOrder with labels := Std.HashMap.ofList [("priority", "mid")] })
    "order.priority_label" "bad priority label"
  let prio ← expectOk
    (Valid.Order.validate { goodOrder with labels := Std.HashMap.ofList [("priority", "high")] })
    "good priority label"
  expect (prio.labels.contains "priority") "labels kept"
  discard <| expectOk (Valid.Order.validate { goodOrder with labels := Std.HashMap.ofList [("env", "prod")] })
    "absent priority key skips the rule"

  -- Indexing in a message rule: this.items[0] under an isSome guard.
  expectViolation
    (Valid.Order.validate { goodOrder with items := #[{ goodItem with quantity := 1001 }] })
    "order.first_item_qty" "first item too large"
  discard <| expectOk
    (Valid.Order.validate { goodOrder with items := #[{ goodItem with quantity := 999 }, goodItem] })
    "first item in range"

  IO.println "all shipping_valid assertions passed"
