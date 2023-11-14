module Util.Relation

open Spec.Ubool

let relation_t (a: Type) (b: Type) = a -> b -> GTot bool

let relation_is_one_to_one (#a: Type) (#b: Type) (relation: relation_t a b) : ubool =
  forall x1 y1 x2 y2. relation x1 y1 /\ relation x2 y2 ==> (x1 == x2 <==> y1 == y2)

let one_to_one_relation_t (a: Type) (b: Type) = relation: (a -> b -> GTot bool){relation_is_one_to_one relation}
