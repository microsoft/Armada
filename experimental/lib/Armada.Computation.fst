module Armada.Computation

noeq type conditional_computation_t (ty: Type) =
  | ComputationImpossible: conditional_computation_t ty
  | ComputationUndefined: conditional_computation_t ty
  | ComputationProduces: (result: ty) -> conditional_computation_t ty

unfold let return (#a: Type) (x: a) : GTot (conditional_computation_t a) = ComputationProduces x

unfold let (let?) (#a: Type) (#b: Type) (m: conditional_computation_t a) (f: a -> GTot (conditional_computation_t b))
  : GTot (conditional_computation_t b) =
  match m with
  | ComputationImpossible -> ComputationImpossible
  | ComputationUndefined -> ComputationUndefined
  | ComputationProduces x -> f x

let otherwise (#a: Type) (inhabitance: a) (m: conditional_computation_t a)
  : GTot a =
  match m with
  | ComputationProduces b -> b
  | _ -> inhabitance

(*
let test1 (x: int) (y: int) : GTot (conditional_computation_t int) =
  if y = 0 then
    ComputationUndefined
  else
    return (x / y)
    
let test2 (x: int) (y: int) (z: int) : GTot (conditional_computation_t int) =
  let? xy = test1 x y in
  test1 xy z

let test3 () : Lemma (True) =
  assert (test2 1 0 0 == ComputationUndefined);
  assert (test2 1 3 0 == ComputationUndefined);
  assert (test2 1 0 3 == ComputationUndefined);
  assert (test2 12 2 3 == return 2)

let test4 (x: int) : GTot (conditional_computation_t unit) =
  if x = 0 then
    ComputationImpossible
  else
    return ()

let test5 (x: int) (y: int) : GTot (conditional_computation_t int) =
  let? _ = test4 x in
  return (x + y)

let test6 () : Lemma (True) =
  assert (test5 0 4 == ComputationImpossible)
*)
