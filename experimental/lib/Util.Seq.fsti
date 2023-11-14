module Util.Seq

//open FStar.Sequence.Ambient
open FStar.Sequence.Base
open Spec.Ubool

let map_correct (#a: Type) (#b: Type) (f: a -> GTot b) (s: seq a) (s': seq b) : ubool =
    length s' = length s
  /\ (forall (i: nat{i < length s}). index s' i == f (index s i))

val map (#a: Type) (#b: Type) (f: a -> GTot b) (s: seq a) : GTot (s': seq b{map_correct f s s'})

val map_refine (#a: Type) (#b: Type) (#p: a -> Type0)
               ($f: (x:a { p x } -> GTot b)) //the $ allows type inference at the call site to infer p
               (s:seq a {forall x. contains s x ==> p x })
  : GTot (s': seq b{length s = length s' /\ (forall (i:nat). i < length s ==> p (index s i) /\ index s' i == f (index s i))})

let function_to_sequence_correct (#ty: Type) (n: nat) (f: (i: nat{i < n}) -> GTot ty) (s: seq ty) : ubool =
    length s = n
  /\ (forall (i: nat{i < n}). index s i == f i)

val function_to_sequence (#ty: Type) (n: nat) (f: (i: nat{i < n}) -> GTot ty)
  : GTot (s: seq ty{function_to_sequence_correct n f s})

val seq_to_list (#ty: Type) (s: seq ty)
  : GTot (lst: list ty{  FStar.List.Tot.length lst = length s
                       /\ (forall (i: nat). i < length s ==> FStar.List.Tot.index lst i == index s i)})

val build_equivalent_to_append (#ty: Type) (s: seq ty) (v: ty)
  : Lemma (ensures seq_to_list (build s v) == FStar.List.Tot.append (seq_to_list s) [v])

let exists_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty) : GTot ubool =
  exists x. contains s x /\ f x

let rec exists_in_seq_after_pos (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (pos: nat)
  : GTot bool (decreases length s - pos) =
  if pos < length s then
    f (index s pos) || exists_in_seq_after_pos f s (pos + 1)
  else
    false

let exists_seq (#ty: Type) (f: ty -> GTot bool) (s: seq ty) : GTot bool =
  exists_in_seq_after_pos f s 0

val exists_seq_implies_specific (#ty: Type) (f: ty -> GTot bool) (s: seq ty{exists_seq f s})
  : GTot (x: ty{contains s x /\ f x})

val exists_seq_equivalent_to_exists_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty)
  : Lemma (ensures exists_seq f s <==> exists_seq_ubool f s)

let for_all_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty) : GTot ubool =
  forall x. contains s x ==> f x

let rec for_all_seq_after_pos (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (pos: nat)
  : GTot bool (decreases length s - pos) =
  if pos < length s then
    f (index s pos) && for_all_seq_after_pos f s (pos + 1)
  else
    true

let for_all_seq (#ty: Type) (f: ty -> GTot bool) (s: seq ty) : GTot bool =
  for_all_seq_after_pos f s 0

val for_all_seq_implies_specific (#ty: Type) (f: ty -> GTot bool) (s: seq ty) (x: ty)
  : Lemma (requires for_all_seq f s /\ contains s x)
          (ensures  f x)

val for_all_seq_equivalent_to_forall_seq_ubool (#ty: Type) (f: ty -> GTot bool) (s: seq ty)
  : Lemma (ensures for_all_seq f s <==> for_all_seq_ubool f s)

val seq_contains_to_index (#ty: Type) (s: seq ty) (x: ty)
  : Ghost nat
  (requires contains s x)
  (ensures  fun idx -> idx < length s /\ index s idx == x)

val seq_to_list_drop_equals_tail (#ty: Type) (s: seq ty)
  : Lemma (requires length s > 0)
          (ensures  Cons?.tl (seq_to_list s) == seq_to_list (drop s 1))

