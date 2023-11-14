module Spec.Logic

let implies (b1: bool) (b2: bool) : bool =
  (not b1) || b2
