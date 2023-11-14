module Util.Seq

open FStar.Sequence.Ambient
open FStar.Sequence.Base

let rec map (#a: Type) (#b: Type) (f: a -> GTot b) (s: seq a) : GTot (s': seq b{map_correct f s s'}) (decreases rank s) =
  if length s = 0 then
    empty
  else
    append (singleton (f (index s 0))) (map f (drop s 1))

let rec map_refine (#a: Type) (#b: Type) (#p: a -> Type0)
                   ($f: (x:a { p x } -> GTot b)) //the $ allows type inference at the call site to infer p
                   (s:seq a {forall x. contains s x ==> p x })
  : GTot (s': seq b{length s = length s' /\ (forall (i:nat). i < length s ==> p (index s i) /\ index s' i == f (index s i))})
    (decreases rank s)
  = if length s = 0 then
      empty
    else
      let hd = index s 0 in
      let tl = drop s 1 in
      assert (rank tl << rank s);
      append (singleton (f hd)) (map_refine f tl)

let rec function_to_sequence (#ty: Type) (n: nat) (f: (i: nat{i < n}) -> GTot ty) =
  (* see .fsti file for spec *)
  if n = 0 then
    empty
  else
    let s_prev = function_to_sequence (n - 1) f in
    build s_prev (f (n - 1))

let rec seq_to_list (#ty: Type) (s: seq ty)
  : GTot (lst: list ty{  FStar.List.Tot.length lst = length s
                       /\ (forall (i: nat). i < length s ==> FStar.List.Tot.index lst i == index s i)})
    (decreases rank s) =
  if length s = 0 then
    []
  else
    (index s 0) :: seq_to_list (drop s 1)

let rec build_equivalent_to_append (#ty: Type) (s: seq ty) (v: ty)
  : Lemma (ensures seq_to_list (build s v) == FStar.List.Tot.append (seq_to_list s) [v])
          (decreases rank s) =
  let lst = seq_to_list s in
  match lst with
  | [] -> ()
  | hd :: tl -> build_equivalent_to_append (drop s 1) v

let rec exists_seq_implies_specific_helper
  (#ty: Type)
  (f: ty -> GTot bool)
  (s: seq ty)
  (pos: nat{exists_in_seq_after_pos f s pos})
  : GTot (x: ty{contains s x /\ f x})
    (decreases length s - pos) =
  if f (index s pos) then
    index s pos
  else
    exists_seq_implies_specific_helper f s (pos + 1)

let exists_seq_implies_specific (#ty: Type) (f: ty -> GTot bool) (s: seq ty{exists_seq f s})
  : GTot (x: ty{contains s x /\ f x}) =
  exists_seq_implies_specific_helper f s 0

let rec exists_implies_exists_seq_helper (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (x: ty) (pos: nat)
  : Lemma (requires   contains s x
                    /\ f x
                    /\ pos < length s
                    /\ (forall (i: nat). i < pos ==> ~(f (index s i))))
          (ensures  exists_in_seq_after_pos f s pos)
          (decreases length s - pos) =
  if f (index s pos) then
    ()
  else
    exists_implies_exists_seq_helper f s x (pos + 1)

let exists_implies_exists_seq (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (x: ty)
  : Lemma (requires contains s x /\ f x)
          (ensures  exists_seq f s) =
  exists_implies_exists_seq_helper f s x 0

let exists_seq_equivalent_to_exists_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty)
  : Lemma (exists_seq f s <==> exists_seq_ubool f s) =
  introduce exists_seq f s ==> exists_seq_ubool f s
  with _. (
    introduce exists x. (contains s x /\ f x)
    with (exists_seq_implies_specific f s)
    and ()
  );
  introduce exists_seq_ubool f s ==> exists_seq f s
  with _. (
    eliminate exists x. contains s x /\ f x
    returns exists_seq f s
    with _. (exists_implies_exists_seq f s x)
  )

let rec for_all_seq_implies_specific_helper (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (x: ty) (pos: nat)
  : Lemma (requires   for_all_seq_after_pos f s pos
                    /\ contains s x
                    /\ pos < length s
                    /\ (forall (i: nat). i < pos ==> ~(x == (index s i))))
          (ensures  f x)
          (decreases length s - pos) =
  if eqb x (index s pos) then
    ()
  else
    for_all_seq_implies_specific_helper f s x (pos + 1)

let for_all_seq_implies_specific (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (x: ty)
  : Lemma (requires for_all_seq f s /\ contains s x)
          (ensures  f x)
          (decreases rank s) =
  for_all_seq_implies_specific_helper f s x 0

let rec for_all_seq_equivalent_to_forall_helper (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (pos: nat)
  : Lemma (requires forall x. contains s x ==> f x)
          (ensures  for_all_seq_after_pos f s pos)
          (decreases length s - pos) =
  if pos < length s then (
    assert (f (index s pos));
    for_all_seq_equivalent_to_forall_helper f s (pos + 1)
  )
  else
    ()

let for_all_seq_equivalent_to_forall_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty)
  : Lemma (ensures for_all_seq f s <==> for_all_seq_ubool f s)
          (decreases rank s) =
  introduce for_all_seq f s ==> for_all_seq_ubool f s
  with _. (
    introduce forall x. contains s x ==> f x
    with (
      introduce _ ==> _
      with _. for_all_seq_implies_specific f s x
    )
  );
  introduce for_all_seq_ubool f s ==> for_all_seq f s
  with _.
    for_all_seq_equivalent_to_forall_helper f s 0

let seq_contains_to_index (#ty: Type) (s: seq ty) (x: ty)
  : Ghost nat
  (requires contains s x)
  (ensures  fun idx -> idx < length s /\ index s idx == x) =
  FStar.IndefiniteDescription.indefinite_description_ghost nat (fun idx -> idx < length s /\ index s idx == x)

let rec seq_to_list_drop_equals_tail (#ty: Type) (s: seq ty)
  : Lemma (requires length s > 0)
          (ensures  Cons?.tl (seq_to_list s) == seq_to_list (drop s 1))
          (decreases length s) =
  if length s = 1 then
    ()
  else
    seq_to_list_drop_equals_tail (drop s 1)
