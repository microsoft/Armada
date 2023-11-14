module Util.Nth

open FStar.List.Tot
open Spec.List
open Spec.Ubool
open Util.List

let list_nth = nth

let rec nth_vs_length (#a: Type) (l: list a) (n: nat)
  : Lemma (ensures (n < (length l)) <==> Some? (nth l n))
  = match l with
    | [] -> ()
    | hd :: tl -> if n = 0 then () else nth_vs_length tl (n - 1)

let rec nth_implies_contains (#a: eqtype) (l: list a) (n: nat) (x: a)
  : Lemma
  (requires nth l n == Some x)
  (ensures  list_contains x l)
  = match l with
    | [] -> ()
    | hd :: tl -> if n = 0 then () else nth_implies_contains tl (n - 1) x

let rec nth_implies_contains_ubool (#a: Type) (l: list a) (n: nat) (x: a)
  : Lemma
  (requires nth l n == Some x)
  (ensures  contains_ubool x l)
  = match l with
    | [] -> ()
    | hd :: tl -> if n = 0 then () else nth_implies_contains_ubool tl (n - 1) x

let rec index_implies_contains (#a: eqtype) (l: list a) (n: nat{n < length l}) (x: a)
  : Lemma
  (requires index l n == x)
  (ensures  list_contains x l)
  = match l with
    | [] -> ()
    | hd :: tl -> if n = 0 then () else index_implies_contains tl (n - 1) x

let rec index_implies_contains_ubool (#a: Type) (l: list a) (n: nat{n < length l}) (x: a)
  : Lemma
  (requires index l n == x)
  (ensures  contains_ubool x l)
  = match l with
    | [] -> ()
    | hd :: tl -> if n = 0 then () else index_implies_contains_ubool tl (n - 1) x

let rec contains_to_index (#a: Type) (x: a) (l: list a)
  : Ghost nat
  (requires contains_ubool x l)
  (ensures  fun n -> n < length l /\ nth l n == Some x /\ index l n == x) =
  if eqb (hd l) x then 0 else 1 + contains_to_index x (tl l)

let rec lists_correspond_implies_index_matches
  (#a: Type)
  (#b: Type)
  (correspondence_relation: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  (n: nat)
  : Lemma
  (requires lists_correspond correspondence_relation l1 l2)
  (ensures  (match nth l1 n with
             | None -> None? (nth l2 n)
             | Some x -> Some? (nth l2 n) /\ correspondence_relation x (Some?.v (nth l2 n)))) =
  if n = 0 then
    ()
  else
    match l1 with
    | [] -> ()
    | hd :: tl -> lists_correspond_implies_index_matches correspondence_relation tl (Cons?.tl l2) (n - 1)

let rec lists_correspond_ubool_implies_index_matches
  (#a: Type)
  (#b: Type)
  (correspondence_relation: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b)
  (n: nat)
  : Lemma
  (requires lists_correspond_ubool correspondence_relation l1 l2)
  (ensures  (match nth l1 n with
             | None -> None? (nth l2 n)
             | Some x -> Some? (nth l2 n) /\ correspondence_relation x (Some?.v (nth l2 n)))) =
  if n = 0 then
    ()
  else
    match l1 with
    | [] -> ()
    | hd :: tl -> lists_correspond_ubool_implies_index_matches correspondence_relation tl (Cons?.tl l2) (n - 1)

let rec establish_lists_correspond_from_index_correspondence
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   list_len l1 = list_len l2
                    /\ (forall (i: nat). i < list_len l1 ==> correspondence (list_index l1 i) (list_index l2 i)))
          (ensures  lists_correspond correspondence l1 l2) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 ->
     match l2 with
     | [] -> ()
     | hd2 :: tl2 ->
        introduce forall (i: nat). i < list_len tl1 ==> correspondence (list_index tl1 i) (list_index tl2 i)
        with introduce _ ==> _
        with _. (
          assert (list_index tl1 i == list_index l1 (i + 1));
          assert (list_index tl2 i == list_index l2 (i + 1))
        );
        establish_lists_correspond_from_index_correspondence correspondence tl1 tl2

let rec establish_lists_correspond_ubool_from_index_correspondence
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   list_len l1 = list_len l2
                    /\ (forall (i: nat). i < list_len l1 ==> correspondence (list_index l1 i) (list_index l2 i)))
          (ensures  lists_correspond_ubool correspondence l1 l2) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 ->
     match l2 with
     | [] -> ()
     | hd2 :: tl2 ->
        introduce forall (i: nat). i < list_len tl1 ==> correspondence (list_index tl1 i) (list_index tl2 i)
        with introduce _ ==> _
        with _. (
          assert (list_index tl1 i == list_index l1 (i + 1));
          assert (list_index tl2 i == list_index l2 (i + 1))
        );
        establish_lists_correspond_ubool_from_index_correspondence correspondence tl1 tl2

let rec equivalent_to_nth_offset
  (#a: Type)
  (offset: nat)
  (l: list a)
  (f: nat -> a)
  : GTot bool
  (decreases l)
  = match l with
    | [] -> true
    | hd :: tl -> eqb (f offset) hd && (equivalent_to_nth_offset (offset + 1) tl f)

let equivalent_to_nth (#a: Type) (l: list a) (f: nat -> a) : GTot bool
  = equivalent_to_nth_offset 0 l f

let rec equivalent_to_nth_offset_implies_matches_index
  (#a: Type)
  (offset: nat)
  (l: list a)
  (f: nat -> a)
  (n: nat) : Lemma
  (requires equivalent_to_nth_offset offset l f /\ n < length l)
  (ensures  nth l n == Some (f (n + offset)))
  (decreases n)
  = match l with
    | [] -> ()
    | hd :: tl ->
       if n = 0 then ()
       else equivalent_to_nth_offset_implies_matches_index (offset + 1) tl f (n - 1)

let equivalent_to_nth_implies_matches_index
  (#a: Type) (l: list a) (f: nat -> a) (n: nat) : Lemma
  (requires equivalent_to_nth l f /\ n < length l)
  (ensures  nth l n == Some (f n))
  = equivalent_to_nth_offset_implies_matches_index 0 l f n

let rec equivalent_to_index_offset
  (#a: Type)
  (offset: nat)
  (l: list a)
  (f: (n: nat{n < length l + offset} -> a))
  : GTot bool
  (decreases l)
  = match l with
    | [] -> true
    | hd :: tl -> eqb (f offset) hd && (equivalent_to_index_offset (offset + 1) tl f)

let equivalent_to_index (#a: Type) (l: list a) (f: (n: nat{n < length l}) -> a) : GTot bool
  = equivalent_to_index_offset 0 l f

let rec equivalent_to_index_offset_implies_matches_index
  (#a: Type)
  (offset: nat)
  (l: list a)
  (f: (n: nat{n < length l + offset} -> a))
  (n: nat) : Lemma
  (requires equivalent_to_index_offset offset l f /\ n < length l)
  (ensures  index l n == f (n + offset))
  (decreases n)
  = match l with
    | [] -> ()
    | hd :: tl ->
       if n = 0 then ()
       else equivalent_to_index_offset_implies_matches_index (offset + 1) tl f (n - 1)

let equivalent_to_index_implies_matches_index
  (#a: Type) (l: list a) (f: (n: nat{n < length l}) -> a) (n: nat) : Lemma
  (requires equivalent_to_index l f /\ n < length l)
  (ensures  index l n == f n)
  = equivalent_to_index_offset_implies_matches_index 0 l f n

let rec nth_matches_index (#a: Type) (l: list a) (n: nat)
  : Lemma (requires n < length l)
          (ensures  nth l n == Some (index l n)) =
  match l with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else nth_matches_index tl (n - 1)

noeq type fast_list_t (a: Type) = {
  len: nat;
  lookup: nat -> a;
}

let fast_list_equivalent_to_list (#a:Type) (f: fast_list_t a) (l: list a) : GTot bool =
     f.len = length l
  && equivalent_to_nth l f.lookup

let fast_list_lookup_valid (#a: Type) (f: fast_list_t a) (l: list a) (n: nat)
  : Lemma (requires fast_list_equivalent_to_list f l /\ n < f.len)
          (ensures  index l n == f.lookup n)
          [SMTPat   (fast_list_equivalent_to_list f l); SMTPat (f.lookup n)] =
  equivalent_to_nth_implies_matches_index l f.lookup n;
  nth_matches_index l n

let fast_nth (#a: Type) (f: fast_list_t a) (n: nat) : option a =
  if n < f.len then Some (f.lookup n) else None

let fast_nth_equivalent_to_nth (#a: Type) (f: fast_list_t a) (l: list a) (n: nat)
  : Lemma (requires fast_list_equivalent_to_list f l)
          (ensures  fast_nth f n == nth l n) =
  if n < f.len then
    equivalent_to_nth_implies_matches_index l f.lookup n
  else
    nth_vs_length l n

let fast_nth_equivalent_to_nth_always (#a: Type) (f: fast_list_t a) (l: list a)
  : Lemma (requires fast_list_equivalent_to_list f l)
          (ensures  forall n.{:pattern fast_nth f n} fast_nth f n == nth l n) =
  introduce forall n. fast_nth f n == nth l n
  with fast_nth_equivalent_to_nth f l n
