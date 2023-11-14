module Spec.Ubool

type ubool = Type0 // not-necessarily-decidable boolean

let u2b (u: ubool) : GTot bool =
  FStar.IndefiniteDescription.strong_excluded_middle u

let eqb (#a: Type) (x: a) (y: a) =
  u2b (x == y)

let neqb (#a: Type) (x: a) (y: a) =
  not (eqb x y)
