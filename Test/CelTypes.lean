module

/-!
Hand-written stand-ins for grpc-lean-generated message structures, giving the
CEL corpus message-level expressions (`this.field` selects, `has(...)`)
something to elaborate against. Shapes follow the grpc-lean protobuf codegen
conventions: verbatim snake_case field names, `Option` for explicit-presence
fields, fixed-width scalars.
-/

@[expose] public section

namespace CelTest

structure Shipment where
  state : String
  tracking : Option String
  a : Option Int32
  b : Option Int32

/-- Presence predicates mirroring the base codegen's generated `has_<field>`. -/
def Shipment.has_tracking (s : Shipment) : Bool := s.tracking.isSome
def Shipment.has_a (s : Shipment) : Bool := s.a.isSome
def Shipment.has_b (s : Shipment) : Bool := s.b.isSome

structure Range where
  start_time : Int64
  end_time : Int64

/-- Proto field names that collide with Lean keywords arrive guillemet-quoted. -/
structure Weird where
  «end» : Int32
  «from» : Int32

structure Order where
  enabled : Bool
  url : String

structure Flags where
  a : Int32
  b : Int32
  c : Int32

end CelTest
