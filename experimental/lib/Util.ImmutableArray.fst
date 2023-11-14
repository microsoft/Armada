module Util.ImmutableArray

open Spec.List
open Util.List
open Util.Range

let rec array_offset_matches_list_implies_length_equivalent
  (#ty: Type)
  (a: array_t ty)
  (len: nat{len = array_len a})
  (offset: nat)
  (l: list ty)
  : Lemma (requires array_offset_matches_list a len offset l)
          (ensures  array_len a = offset + list_len l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
      array_offset_matches_list_implies_length_equivalent a len (offset + 1) tl

let array_matches_list_implies_length_equivalent (#ty: Type) (a: array_t ty) (l: list ty)
  (* see .fsti file for spec *) =
  array_offset_matches_list_implies_length_equivalent a (array_len a) 0 l

let rec array_offset_matches_list_implies_nth_equivalent
  (#ty: Type)
  (a: array_t ty)
  (len: nat{len = array_len a})
  (offset: nat)
  (l: list ty)
  (n: nat)
  : Lemma (requires array_offset_matches_list a len offset l /\ n >= offset)
          (ensures  array_nth a n == list_nth l (n - offset))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
      if n = offset then
        ()
      else
        array_offset_matches_list_implies_nth_equivalent a len (offset + 1) tl n

let array_matches_list_implies_nth_equivalent (#ty: Type) (a: array_t ty) (l: list ty) (n: nat)
  (* see .fsti file for spec *) =
  array_offset_matches_list_implies_nth_equivalent a (array_len a) 0 l n

let rec array_offset_matches_list_implies_index_equivalent
  (#ty: Type)
  (a: array_t ty)
  (len: nat{len = array_len a})
  (offset: nat)
  (l: list ty)
  (n: nat{n < len})
  : Lemma (requires array_offset_matches_list a len offset l /\ n >= offset /\ len = offset + list_len l)
          (ensures  array_index a n == list_index l (n - offset))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
      if n = offset then
        ()
      else
        array_offset_matches_list_implies_index_equivalent a len (offset + 1) tl n

let array_matches_list_implies_index_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat{n < array_len a})
  (* see .fsti file for spec *) =
  array_matches_list_implies_length_equivalent a l;
  array_offset_matches_list_implies_index_equivalent a (array_len a) 0 l n

let rec indices_match_implies_array_offset_matches_list
  (#ty: Type)
  (a: array_t ty)
  (len: nat{len = array_len a})
  (offset: nat)
  (l: list ty)
  : Lemma (requires   offset + list_len l = len
                    /\ (forall (i: nat{i >= offset /\ i < array_len a}). array_index a i == list_index l (i - offset)))
          (ensures  array_offset_matches_list a len offset l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
      indices_match_implies_array_offset_matches_list a len (offset + 1) tl

let indices_match_implies_array_matches_list
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  : Lemma (requires   list_len l = array_len a
                    /\ (forall (i: nat{i < array_len a}). array_index a i == FStar.List.Tot.index l i))
          (ensures  array_matches_list a l) =
  indices_match_implies_array_offset_matches_list a (array_len a) 0 l

let list_to_array_implies_array_matches_list
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (* see .fsti file for spec *) =
  to_list_of_list l;
  length_spec a;
  introduce forall (i: nat{i < array_len a}). array_index a i == list_index l i
  with (
    index_spec a i
  );
  indices_match_implies_array_matches_list a l

let array_to_list_implies_array_matches_list
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (* see .fsti file for spec *) =
  length_spec a;
  assert (list_len l = array_len a);
  introduce forall (i: nat{i < list_len l}). array_index a i == list_index l i
  with (
    index_spec a i
  );
  indices_match_implies_array_matches_list a l

let list_to_array_implies_length_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (* see .fsti file for spec *) =
  list_to_array_implies_array_matches_list a l;
  array_matches_list_implies_length_equivalent a l

let list_to_array_implies_nth_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat)
  (* see .fsti file for spec *) =
  list_to_array_implies_array_matches_list a l;
  array_matches_list_implies_nth_equivalent a l n

let list_to_array_implies_index_equivalent
  (#ty: Type)
  (a: array_t ty)
  (l: list ty)
  (n: nat{n < array_len a})
  (* see .fsti file for spec *) =
  list_to_array_implies_array_matches_list a l;
  array_matches_list_implies_index_equivalent a l n

let array_elements_unique_implication
  (#ty: eqtype)
  (a: array_t ty)
  (* see .fsti file for spec *) =
  introduce forall (i: nat) (j: nat). i < array_len a /\ j < array_len a /\ i <> j ==> array_index a i <> array_index a j
  with introduce i < array_len a /\ j < array_len a /\ i <> j ==> array_index a i <> array_index a j
  with _. (
    if i < j then
      assert (for_all_range j (fun k -> array_index a j <> array_index a k))
    else
      assert (for_all_range i (fun k -> array_index a i <> array_index a k))
  )

let array_elements_unique_ubool_implication
  (#ty: Type)
  (a: array_t ty)
  (* see .fsti file for spec *) =
  introduce forall (i: nat) (j: nat). i < array_len a /\ j < array_len a /\ i <> j ==> ~(array_index a i == array_index a j)
  with introduce _ ==> _
  with _. (
    if i < j then
      assert (for_all_range_ubool j (fun k -> ~(array_index a j == array_index a k)))
    else
      assert (for_all_range_ubool i (fun k -> ~(array_index a i == array_index a k)))
  )
