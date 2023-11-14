module Util.Range

let rec for_all_range_equivalent_to_forall (n: nat) (f: (i: nat{i < n}) -> GTot bool)
  (* see .fsti file for spec *) =
  if n = 0 then
    ()
  else
    for_all_range_equivalent_to_forall (n - 1) f

let rec for_all_range_ubool_equivalent_to_forall (n: nat) (f: (i: nat{i < n}) -> GTot ubool)
  (* see .fsti file for spec *) =
  if n = 0 then
    ()
  else
    for_all_range_ubool_equivalent_to_forall (n - 1) f
