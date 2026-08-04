import ShippingLean.inventory
import ShippingLean.shipping
import ShippingValid.inventory
import ShippingValid.shipping
import Protovalidate.Runtime

/-!
Runtime behavior of the standard-rule vocabulary: string/numeric/bytes/enum
rules, ignore-zero escapes, required (both the Option-unwrapping and the
non-zero forms), quantified repeated/map rules, decodeValid, and cross-file
validated references (shipping.Order embeds catalog.Product).
-/

open catalog.v1

def goodProduct : Product :=
  { sku := "widget-9", region := "us", stock := 5, price_cents := 100,
    batch := 2, rating := 4.5, checksum := ByteArray.mk #[0x89, 0x50, 1, 2],
    tier := .PREMIUM, tags := #["home", "garden"],
    attrs := Std.HashMap.ofList [("color", "red")], owner := some "bill",
    published := true, contact := "" }

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectOk (result : Except Protovalidate.Violation α) (msg : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError s!"{msg}: unexpected violation {e}")

def expectId (r : Except Protovalidate.Violation α) (id : String) (label : String) : IO Unit := do
  let ok := match r with
    | .error e => e.ruleId == id
    | .ok _ => id == ""
  unless ok do
    let got := match r with
      | .error e => toString e
      | .ok _ => "ok"
    let want := if id == "" then "ok" else id
    throw (IO.userError s!"{label}: expected {want}, got {got}")

def main : IO Unit := do
  -- the valid product validates, unwraps required owner, and roundtrips
  let v ← match Valid.Product.validate goodProduct with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"good product: {e}")
  unless v.owner.val == "bill" do throw (IO.userError "owner unwrap")
  unless v.toBase.owner == some "bill" do throw (IO.userError "toBase rewrap")

  -- standard rules, one violation each
  expectId (Valid.Product.validate { goodProduct with sku := "X" }) "string.min_len" "min_len"
  expectId (Valid.Product.validate { goodProduct with sku := "Bad-CAPS" }) "string.pattern" "pattern"
  expectId (Valid.Product.validate { goodProduct with contact := "not-an-email" }) "string.email" "email"
  expectId (Valid.Product.validate { goodProduct with contact := "" }) "" "email ignore-zero escape"
  expectId (Valid.Product.validate { goodProduct with region := "mars" }) "string.in" "in"
  expectId (Valid.Product.validate { goodProduct with stock := -1 }) "int32.gt_lt" "int range"
  expectId (Valid.Product.validate { goodProduct with price_cents := 0 }) "required" "required non-zero"
  expectId (Valid.Product.validate { goodProduct with rating := 9.0 }) "double.gt_lt" "float range"
  expectId (Valid.Product.validate { goodProduct with published := false }) "" "bool ignore-zero escape"
  expectId (Valid.Product.validate { goodProduct with checksum := ByteArray.mk #[1, 2, 3, 4] }) "bytes.prefix" "bytes prefix"
  expectId (Valid.Product.validate { goodProduct with tier := .LEGACY }) "enum.not_in" "enum not_in"
  expectId (Valid.Product.validate { goodProduct with tier := .«Unknown.Value» 42 }) "enum.defined_only" "enum defined_only"
  expectId (Valid.Product.validate { goodProduct with tier := .TIER_UNSPECIFIED }) "tier.assigned" "enum custom cel (as int)"
  expectId (Valid.Product.validate { goodProduct with tags := #[] }) "repeated.min_items" "min_items"
  expectId (Valid.Product.validate { goodProduct with tags := #["a"] }) "repeated.items" "items"
  expectId (Valid.Product.validate { goodProduct with tags := #["home", "home"] }) "repeated.unique" "unique"
  expectId (Valid.Product.validate { goodProduct with attrs := Std.HashMap.ofList [("BAD", "x")] }) "map.keys" "map keys"
  expectId (Valid.Product.validate { goodProduct with attrs := Std.HashMap.ofList [("k", "")] }) "map.values" "map values"
  expectId (Valid.Product.validate { goodProduct with owner := none }) "required" "required option"
  expectId (Valid.Product.validate { goodProduct with owner := some "x" }) "string.min_len" "owner min_len"
  expectId (Valid.Product.validate { goodProduct with homepage := some "not a uri" }) "string.uri" "uri"

  -- encode → decodeValid roundtrip
  let base := v.toBase
  match base.encode with
  | .error e => throw (IO.userError s!"encode: {e}")
  | .ok bs =>
    match Valid.Product.decodeValid bs with
    | .ok v2 => unless v2.sku.val == "widget-9" do throw (IO.userError "decodeValid roundtrip")
    | .error e => throw (IO.userError s!"decodeValid: {e}")

  -- cross-file validated reference: Order embeds Valid.Product
  let order : shipping.v1.Order :=
    { id := "ord-1234", status := "NEW",
      items := #[{ sku := "widget", quantity := 2 }],
      featured := some goodProduct }
  match shipping.v1.Valid.Order.validate order with
  | .ok vo =>
    match vo.featured with
    | some fp => unless fp.sku.val == "widget-9" do throw (IO.userError "featured sku")
    | none => throw (IO.userError "featured missing")
  | .error e => throw (IO.userError s!"order with featured: {e}")
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with sku := "X" } })
    "string.min_len" "violation surfaces through cross-file embed"

  -- cross-TARGET validated reference: Order embeds common.v1.Valid.Money
  let priced := { order with total := some ({ currency := "USD", amount_cents := 995 } : common.v1.Money) }
  match shipping.v1.Valid.Order.validate priced with
  | .ok vo =>
    match vo.total with
    | some m => unless m.currency.val == "USD" do throw (IO.userError "money currency")
    | none => throw (IO.userError "total missing")
  | .error e => throw (IO.userError s!"order with total: {e}")
  expectId (shipping.v1.Valid.Order.validate
    { order with total := some { currency := "US", amount_cents := 1 } })
    "string.len" "violation surfaces through cross-target embed"
  expectId (shipping.v1.Valid.Order.validate
    { order with total := some { currency := "USD", amount_cents := -1 } })
    "int64.gte" "money amount"

  -- validated oneof sums: required, member rules, nested validated payloads
  expectId (Valid.Payment.validate {}) "required" "oneof required"
  expectId (Valid.Payment.validate { method := some (.iban "short") }) "string.min_len" "oneof member rule"
  expectId (Valid.Payment.validate { method := some (.store_credit_product { goodProduct with sku := "Bad-CAPS" }) })
    "string.pattern" "oneof nested payload rule"
  let pay ← expectOk (Valid.Payment.validate { method := some (.iban "DE89370400440532013000") }) "good payment"
  match pay.method with
  | .iban i => expect (i.val.startsWith "DE") "iban payload"
  | _ => throw (IO.userError "wrong oneof case")
  match pay.toBase.method with
  | some (.iban s) => expect (s == "DE89370400440532013000") "oneof toBase roundtrip"
  | _ => throw (IO.userError "oneof toBase case")
  expectId (Valid.Payment.validate { method := some (.cash_note "iou") }) "" "unconstrained member"

  -- member value access in message rules (CEL value-or-default semantics)
  expectId (Valid.Payment.validate { method := some (.iban "GB82WEST12345698765432") })
    "payment.iban_country" "member value access (required oneof)"
  expectId (Valid.Payment.validate
    { method := some (.cash_note "x"), receipt := some (.email_to "not-an-email") })
    "payment.receipt_email" "member value access (base sum accessor)"
  expectId (Valid.Payment.validate
    { method := some (.cash_note "x"), receipt := some (.email_to "a@example.com") })
    "" "receipt email ok"
  expectId (Valid.Payment.validate
    { method := some (.cash_note "x"), receipt := some (.sms_to "+123") })
    "" "sms receipt skips email rule"
  expectId (shipping.v1.Valid.Order.validate
    { order with payer := some (.customer_id "abcdefghijklmnopqrstu") })
    "order.payer_len" "member value access (optional constrained oneof)"

  -- member rules on a non-required oneof (Order.payer)
  expectId (shipping.v1.Valid.Order.validate { order with payer := some (.customer_id "ab") })
    "string.min_len" "payer member rule"
  let paid ← expectOk (shipping.v1.Valid.Order.validate { order with payer := some (.customer_id "abc") }) "payer ok"
  expect (paid.toBase.payer.isSome) "payer toBase"

  -- message rules traversing nested validated / optional fields (CEL
  -- value-or-default semantics: unset reads as the default instance)
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with sku := "banned" } })
    "order.featured_not_banned" "nested valid value access"
  expectId (shipping.v1.Valid.Order.validate
    { order with total := some { currency := "USD", amount_cents := 2000000 } })
    "order.total_cap" "cross-target nested value access"
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with dims := some { weight_grams := 60000 } } })
    "order.featured_weight" "deep traversal (two message hops)"
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with dims := some { weight_grams := 100 } } })
    "" "deep traversal in range"
  expectId (shipping.v1.Valid.Order.validate { order with tracking := some "TN" })
    "order.tracking_len" "optional scalar value access"
  expectId (shipping.v1.Valid.Order.validate { order with tracking := some "TN123" })
    "" "tracking long enough"
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with tier := .BASIC } })
    "order.featured_tier" "enum leaf in message rule"

  -- nested oneof member access in message rules (final and intermediate hops)
  expectId (shipping.v1.Valid.Order.validate
    { order with payment := some { method := some (.cash_note "iou-void") } })
    "order.payment_note" "nested member final select"
  expectId (shipping.v1.Valid.Order.validate
    { order with payment := some { method := some (.store_credit_product { goodProduct with sku := "banned" }) } })
    "order.payment_credit_sku" "nested member intermediate hop"
  expectId (shipping.v1.Valid.Order.validate
    { order with payment := some { method := some (.iban "DE89370400440532013000") } })
    "" "payment defaults pass member rules"

  -- has() on nested members and nested implicit-presence fields
  expectId (shipping.v1.Valid.Order.validate
    { order with payment := some { method := some (.cash_note "ab") } })
    "order.payment_note_len" "nested member has() guard"
  expectId (shipping.v1.Valid.Order.validate
    { order with payment := some { method := some (.cash_note "credit") } })
    "" "nested member has() satisfied"
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with contact := "a@b.co" } })
    "order.featured_contact_domain" "nested implicit-scalar has() guard"
  expectId (shipping.v1.Valid.Order.validate
    { order with featured := some { goodProduct with contact := "x@example.com" } })
    "" "nested implicit-scalar has() satisfied"

  -- well-known-type field with timestamp rules (gte 2000-01-01)
  expectId (shipping.v1.Valid.Order.validate
    { order with created_at := some (Cel.Timestamp.mk 1893456000 0) })
    "" "created_at in range"
  expectId (shipping.v1.Valid.Order.validate
    { order with created_at := some (Cel.Timestamp.mk 0 0) })
    "timestamp.gte" "created_at before 2000"
  expectId (shipping.v1.Valid.Order.validate order) "" "created_at absent"

  IO.println "all inventory_valid assertions passed"
