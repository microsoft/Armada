module Util.ImmutableArray

open FStar.ImmutableArray
open Spec.List
open Spec.Ubool
open Util.List
open Util.Nth
open Util.Range

let array_t = FStar.ImmutableArray.t
let array_len = FStar.ImmutableArray.length
let array_index = FStar.ImmutableArray.index
let list_to_array = FStar.ImmutableArray.of_list
let array_to_list = FStar.ImmutableArray.to_list

let array_nth (#ty: Type) (a: array_t ty) (i: nat) : option ty =
  if i >= array_len a then
    None
  else
    Some (array_index a i)

let rec array_offset_matches_list
  (#ty: Type)
  (a: array_t ty)
  (len: nat{len = array_len a})
  (offset: nat)
  (l: list ty)
  : GTot bool (decreases l) =
  match l with
  | [] -> len = offset
  | hd :: tl -> len > offset && eqb hd (array_index a offset) && array_offset_matches_list a len (offset + 1) tl

let array_matches_list (#ty: Type) (a: array_t ty) (l: list ty) : GTot bool =
  array_offset_matches_list a (array_len a) 0 l

val array_matches_list_implies_length_equivalent (#ty: Type) (a: array_t ty) (l: list ty)
  : Lemma (requires array_matches_list a l)
          (ensures  array_len a = list_len l)

val array_matches_list_implies_nth_equivalent (#ty: Type) (a: array_t ty) (l: list ty) (n: nat)
  : Lemma (requires array_matches_list a l)
          (ensures  array_nth a n == list_nth l n)

val array_matches_list_implies_index_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat{n < array_len a})
  : Lemma (requires array_matches_list a l)
          (ensures  n < list_len l /\ array_index a n == list_index l n)

val list_to_array_implies_array_matches_list
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  : Lemma (requires a == list_to_array l)
          (ensures  array_matches_list a l)

val array_to_list_implies_array_matches_list
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  : Lemma (requires l == array_to_list a)
          (ensures  array_matches_list a l)

val list_to_array_implies_length_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  : Lemma (requires a == list_to_array l)
          (ensures  array_len a = list_len l)

val list_to_array_implies_nth_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat)
  : Lemma (requires a == list_to_array l)
          (ensures  array_nth a n == list_nth l n)

val list_to_array_implies_index_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat{n < array_len a})
  : Lemma (requires a == list_to_array l)
          (ensures  n < list_len l /\ array_index a n == list_index l n)

let for_all_array (#ty: Type) (f: ty -> GTot bool) (a: array_t ty) =
  for_all_range (array_len a) (fun i -> f (array_index a i))

let for_all_array_ubool (#ty: Type) (f: ty -> GTot ubool) (a: array_t ty) =
  for_all_range_ubool (array_len a) (fun i -> f (array_index a i))

let for_all_array_enumerated (#ty: Type) (f: nat -> ty -> GTot bool) (a: array_t ty) =
  for_all_range (array_len a) (fun i -> f i (array_index a i))

let for_all_array_enumerated_ubool (#ty: Type) (f: nat -> ty -> GTot ubool) (a: array_t ty) =
  for_all_range_ubool (array_len a) (fun i -> f i (array_index a i))

let arrays_correspond
  (#ty1: Type)
  (#ty2: Type)
  (correspondence: ty1 -> ty2 -> GTot bool)
  (a1: array_t ty1)
  (a2: array_t ty2)
  : GTot bool =
     array_len a1 = array_len a2
  && for_all_range (array_len a1) (fun i -> correspondence (array_index a1 i) (array_index a2 i))

let arrays_correspond_ubool
  (#ty1: Type)
  (#ty2: Type)
  (correspondence: ty1 -> ty2 -> GTot ubool)
  (a1: array_t ty1)
  (a2: array_t ty2)
  : GTot ubool =
     array_len a1 = array_len a2
  /\ for_all_range_ubool (array_len a1) (fun i -> correspondence (array_index a1 i) (array_index a2 i))

let rec find_in_array_offset
  (#ty: Type)
  (a: array_t ty)
  (offset: nat)
  (x: ty)
  : GTot (result: option nat{
            match result with
            | None ->   (forall (i: nat).{:pattern array_index a i} offset <= i /\ i < array_len a ==> ~(array_index a i == x))
                     /\ (forall (i: nat).{:pattern array_nth a i} offset <= i ==> ~(array_nth a i == Some x))
            | Some i -> i < array_len a /\ array_index a i == x /\ array_nth a i == Some x})
    (decreases array_len a - offset) =
  if offset >= array_len a then
    None
  else if eqb (array_index a offset) x then
    Some offset
  else
    find_in_array_offset a (offset + 1) x

let find_in_array
  (#ty: Type)
  (a: array_t ty)
  (x: ty)
  : GTot (result: option nat{
            match result with
            | None ->   (forall (i: nat).{:pattern array_index a i} i < array_len a ==> ~(array_index a i == x))
                     /\ (forall (i: nat).{:pattern array_nth a i} ~(array_nth a i == Some x))
            | Some i -> i < array_len a /\ array_index a i == x /\ array_nth a i == Some x}) =
  find_in_array_offset a 0 x

let array_elements_unique
  (#ty: eqtype)
  (a: array_t ty)
  : GTot bool =
  for_all_range (array_len a) (fun i -> for_all_range i (fun j -> array_index a i <> array_index a j))

let array_elements_unique_ubool
  (#ty: Type)
  (a: array_t ty)
  : GTot ubool =
  for_all_range_ubool (array_len a) (fun i -> for_all_range_ubool i (fun j -> ~(array_index a i == array_index a j)))

val array_elements_unique_implication
  (#ty: eqtype)
  (a: array_t ty)
  : Lemma (requires array_elements_unique a)
          (ensures    (forall (i: nat) (j: nat).{:pattern array_index a i; array_index a j}
                        i < array_len a /\ j < array_len a /\ i <> j ==> array_index a i <> array_index a j)
                    /\ (forall (i: nat) (j: nat).{:pattern array_nth a i; array_nth a j}
                         i <> j /\ array_nth a i = array_nth a j ==> None? (array_nth a i)))

val array_elements_unique_ubool_implication
  (#ty: Type)
  (a: array_t ty)
  : Lemma (requires array_elements_unique_ubool a)
          (ensures    (forall (i: nat) (j: nat).{:pattern array_index a i; array_index a j}
                        i < array_len a /\ j < array_len a /\ i <> j ==> ~(array_index a i == array_index a j))
                    /\ (forall (i: nat) (j: nat).{:pattern array_nth a i; array_nth a j}
                         i <> j /\ array_nth a i == array_nth a j ==> None? (array_nth a i)))

let arrays_correspond_specific_index
  (#ty1: Type)
  (#ty2: Type)
  (correspondence: ty1 -> ty2 -> GTot bool)
  (a1: array_t ty1)
  (a2: array_t ty2{arrays_correspond correspondence a1 a2})
  (idx: nat{idx < array_len a1})
  : Lemma (ensures correspondence (array_index a1 idx) (array_index a2 idx)) =
  ()
