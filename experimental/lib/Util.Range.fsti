module Util.Range

open Spec.Ubool

let rec for_all_range (n: nat) (f: (i: nat{i < n}) -> GTot bool) : GTot bool =
  if n = 0 then true else (f (n - 1) && for_all_range (n - 1) f)

let rec for_all_range_ubool (n: nat) (f: (i: nat{i < n}) -> GTot ubool) : GTot ubool =
  if n = 0 then True else (f (n - 1) /\ for_all_range_ubool (n - 1) f)

val for_all_range_equivalent_to_forall (n: nat) (f: (i: nat{i < n}) -> GTot bool)
  : Lemma (ensures for_all_range n f <==> (forall (i: nat). i < n ==> f i))
          [SMTPat (for_all_range n f)]

val for_all_range_ubool_equivalent_to_forall (n: nat) (f: (i: nat{i < n}) -> GTot ubool)
  : Lemma (ensures for_all_range_ubool n f <==> (forall (i: nat). i < n ==> f i))
          [SMTPat (for_all_range_ubool n f)]
