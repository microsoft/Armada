module Util.Logic

open Spec.Logic
open Spec.Ubool

let simpler_indefinite_description (#a: Type) ($p: a -> ubool) : Ghost a
  (requires exists x. p x)
  (ensures  fun x -> p x) =
  let p': a -> prop = fun x -> squash (p x) in
  FStar.IndefiniteDescription.indefinite_description_ghost a p'

let indefinite_description_two (#a: Type) (#b: Type) (p: (a -> b -> ubool)) : Ghost (a * b)
  (requires exists x y. p x y)
  (ensures  fun xy -> let x, y = xy in p x y) =
  let p': (a * b) -> prop = fun xy -> squash (let x, y = xy in p x y) in
  eliminate exists x' y'. p x' y'
  returns exists xy. p' xy
  with _. (assert (let x, y = (x', y') in p x y));
  FStar.IndefiniteDescription.indefinite_description_ghost (a * b) p'

let indefinite_description_three (#a: Type) (#b: Type) (#c: Type) (p: (a -> b -> c -> ubool)) : Ghost (a * b * c)
  (requires exists x y z. p x y z)
  (ensures  fun xyz -> let x, y, z = xyz in p x y z) =
  let p': (a * b * c) -> prop = fun xyz -> squash (let x, y, z = xyz in p x y z) in
  eliminate exists x' y' z'. p x' y' z'
  returns exists xyz. p' xyz
  with _. (assert (let x, y, z = (x', y', z') in p x y z));
  FStar.IndefiniteDescription.indefinite_description_ghost (a * b * c) p'
