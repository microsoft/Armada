module Util.List

open FStar.Calc
open FStar.Classical.Sugar
open FStar.List.Tot
open Spec.List
open Spec.Ubool
open Util.Logic

let list_index = FStar.List.Tot.index
let list_map = FStar.List.Tot.map
let list_append = FStar.List.Tot.append

let rec for_all_ghost (#a: Type) (f: a -> GTot bool) (l: list a) : GTot bool =
  match l with
  | [] -> true
  | hd :: tl -> f hd && for_all_ghost f tl

let rec for_all_ubool (#a: Type) (f: a -> GTot ubool) (l: list a) : GTot ubool =
  match l with
  | [] -> True
  | hd :: tl -> f hd /\ for_all_ubool f tl

let rec exists_ghost (#a: Type) (f: a -> GTot bool) (l: list a) : GTot bool =
  match l with
  | [] -> false
  | hd :: tl -> f hd || exists_ghost f tl

let rec exists_ubool (#a: Type) (f: a -> GTot ubool) (l: list a) : GTot ubool =
  match l with
  | [] -> False
  | hd :: tl -> f hd \/ exists_ubool f tl

let rec map_ghost (#a: Type) (#b: Type) (f: a -> GTot b) (l: list a) : GTot (list b) =
  match l with
  | [] -> []
  | hd :: tl -> (f hd) :: map_ghost f tl

let rec for_all_ghost_equivalent_to_forall (#a: Type) (f: a -> GTot bool) (l: list a)
  : Lemma (for_all_ghost f l <==> (forall x. contains_ubool x l ==> f x))
           [SMTPat (for_all_ghost f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_ghost_equivalent_to_forall f tl

let rec for_all_ghost_equivalent_to_forall_eqtype (#a: eqtype) (f: a -> GTot bool) (l: list a)
  : Lemma (for_all_ghost f l <==> (forall x. list_contains x l ==> f x))
           [SMTPat (for_all_ghost f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_ghost_equivalent_to_forall_eqtype f tl

let for_all_ghost_specific_case (#a: Type) (f: a -> GTot bool) (l: list a) (x: a)
  : Lemma (requires for_all_ghost f l /\ contains_ubool x l)
          (ensures f x) =
  for_all_ghost_equivalent_to_forall f l

let for_all_ghost_specific_case_eqtype (#a: eqtype) (f: a -> GTot bool) (l: list a) (x: a)
  : Lemma (requires for_all_ghost f l /\ list_contains x l)
          (ensures f x) =
  for_all_ghost_equivalent_to_forall_eqtype f l

let contains_all (#a: Type) (xs: list a) (ys: list a) : GTot ubool =
  for_all_ubool (fun (x: a) -> contains_ubool x ys) xs

let rec list_contains_last (#a: Type) (l: list a)
  : Lemma (requires Cons? l)
          (ensures  contains_ubool (last l) l) =
  match l with
  | [x] -> ()
  | hd :: tl -> list_contains_last tl

let rec contains_equivalent_to_contains_ubool (#a: eqtype) (x: a) (l: list a)
  : Lemma (ensures  contains x l <==> contains_ubool x l) =
  match l with
  | [] -> ()
  | hd :: tl -> if hd = x then () else contains_equivalent_to_contains_ubool x tl

let rec for_all_ubool_equivalent_to_forall (#a: Type) (f: a -> GTot ubool) (l: list a)
  : Lemma (for_all_ubool f l <==> (forall x. contains_ubool x l ==> f x))
           [SMTPat (for_all_ubool f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_ubool_equivalent_to_forall f tl

let rec for_all_ubool_equivalent_to_forall_eqtype (#a: eqtype) (f: a -> GTot ubool) (l: list a)
  : Lemma (for_all_ubool f l <==> (forall x. list_contains x l ==> f x))
           [SMTPat (for_all_ubool f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_ubool_equivalent_to_forall_eqtype f tl

let for_all_ubool_specific_case (#a: Type) (f: a -> GTot ubool) (l: list a) (x: a)
  : Lemma (requires for_all_ubool f l /\ contains_ubool x l)
          (ensures  f x) =
  for_all_ubool_equivalent_to_forall f l

let rec filter_ghost (#a: Type) (f: a -> GTot bool) (l: list a) : GTot (m: list a{forall x. contains_ubool x m ==> f x}) =
  match l with
  | [] -> []
  | hd :: tl -> if f hd then hd :: filter_ghost f tl else filter_ghost f tl

let rec contains_implies_filter_or_unfiltered (#a: Type) (f: a -> GTot bool) (l: list a) (x: a)
  : Lemma (requires contains_ubool x l)
          (ensures  contains_ubool x (filter_ghost f l) \/ ~ (f x)) =
  match l with
  | [] -> ()
  | hd :: tl -> if eqb x hd then () else contains_implies_filter_or_unfiltered f tl x

let rec implication_of_contains_and_for_all (#a: eqtype) (f: a -> GTot bool) (x: a) (l: list a)
  : Lemma (requires list_contains x l /\ for_all_ghost f l)
          (ensures  f x) =
  match l with
  | [] -> ()
  | hd :: tl -> if x = hd then () else implication_of_contains_and_for_all f x tl

let rec implication_of_contains_ubool_and_for_all (#a: Type) (f: a -> GTot bool) (x: a) (l: list a)
  : Lemma (requires contains_ubool x l /\ for_all_ghost f l)
          (ensures  f x) =
  match l with
  | [] -> ()
  | hd :: tl -> if eqb x hd then () else implication_of_contains_ubool_and_for_all f x tl

let rec for_all_implication
  (#a: Type)
  (#property1: a -> GTot bool)
  (#property2: a -> GTot bool)
  ($property_implication: (x: a) -> Lemma (requires property1 x) (ensures property2 x))
  (l: list a)
  : Lemma
  (requires for_all_ghost property1 l)
  (ensures  for_all_ghost property2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> property_implication hd; for_all_implication property_implication tl

let rec for_all_ubool_implication
  (#a: Type)
  (#property1: a -> GTot ubool)
  (#property2: a -> GTot ubool)
  ($property_implication: (x: a) -> Lemma (requires property1 x) (ensures property2 x))
  (l: list a)
  : Lemma
  (requires for_all_ubool property1 l)
  (ensures  for_all_ubool property2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> property_implication hd; for_all_ubool_implication property_implication tl

let rec for_all_equivalent
  (#a: Type)
  (#property1: a -> GTot bool)
  (#property2: a -> GTot bool)
  ($property_equivalent: (x: a) -> Lemma (property1 x = property2 x))
  (l: list a)
  : Lemma (for_all_ghost property1 l = for_all_ghost property2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> property_equivalent hd; for_all_equivalent property_equivalent tl

let rec for_all_ubool_equivalent
  (#a: Type)
  (#property1: a -> GTot ubool)
  (#property2: a -> GTot ubool)
  ($property_equivalent: (x: a) -> Lemma (property1 x == property2 x))
  (l: list a)
  : Lemma (for_all_ubool property1 l == for_all_ubool property2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> property_equivalent hd; for_all_ubool_equivalent property_equivalent tl

let rec lists_correspond
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  : GTot bool =
  match l1 with
  | [] -> Nil? l2
  | hd1 :: tl1 ->
      match l2 with
      | [] -> false
      | hd2 :: tl2 -> correspondence hd1 hd2 && lists_correspond correspondence tl1 tl2

let rec lists_correspond_implies_lengths_match
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  : Lemma
  (requires lists_correspond #a #b correspondence l1 l2)
  (ensures  length l1 = length l2) =
  match l1 with
  | [] -> ()
  | hd :: tl -> lists_correspond_implies_lengths_match correspondence tl (Cons?.tl l2)

let rec lists_correspond_implies_weaker_correspondence
  (#a: Type)
  (#b: Type)
  (stronger_correspondence: a -> b -> GTot bool)
  (weaker_correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  (stronger_implies_weaker: (x: a) -> (y: b) ->
    Lemma (requires stronger_correspondence x y) (ensures weaker_correspondence x y))
  : Lemma
  (requires lists_correspond stronger_correspondence l1 l2)
  (ensures  lists_correspond weaker_correspondence l1 l2) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 ->
      match l2 with
      | [] -> ()
      | hd2 :: tl2 ->
          stronger_implies_weaker hd1 hd2;
          lists_correspond_implies_weaker_correspondence
            stronger_correspondence weaker_correspondence tl1 tl2 stronger_implies_weaker

let rec get_correspondent_from_lists_correspond
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b{lists_correspond correspondence l1 l2})
  (x: a{contains_ubool x l1})
  : GTot (y:b{correspondence x y /\ contains_ubool y l2}) =
  match l1 with
  | [] -> assert(false)
  | hd1 :: tl1 ->
     match l2 with
     | [] -> assert(false)
     | hd2 :: tl2 ->
        if eqb hd1 x then
          hd2
        else
          get_correspondent_from_lists_correspond correspondence tl1 tl2 x

let rec get_correspondent_from_lists_correspond_doubly
  (#a: Type)
  (#b: Type)
  (correspondence1: a -> b -> GTot bool)
  (correspondence2: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b{lists_correspond correspondence1 l1 l2 /\ lists_correspond correspondence2 l1 l2})
  (x: a{contains_ubool x l1})
  : GTot (y:b{correspondence1 x y /\ correspondence2 x y /\ contains_ubool y l2}) =
  match l1 with
  | [] -> assert(false)
  | hd1 :: tl1 ->
     match l2 with
     | [] -> assert(false)
     | hd2 :: tl2 ->
        if eqb hd1 x then
          hd2
        else
          get_correspondent_from_lists_correspond_doubly correspondence1 correspondence2 tl1 tl2 x

let rec lists_correspond_ubool
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b)
  : GTot ubool =
  match l1 with
  | [] -> Nil? l2
  | hd1 :: tl1 ->
      match l2 with
      | [] -> false
      | hd2 :: tl2 -> correspondence hd1 hd2 /\ lists_correspond_ubool correspondence tl1 tl2

let rec lists_correspond_ubool_implies_lengths_match
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b)
  : Lemma
  (requires lists_correspond_ubool #a #b correspondence l1 l2)
  (ensures  length l1 = length l2) =
  match l1 with
  | [] -> ()
  | hd :: tl -> lists_correspond_ubool_implies_lengths_match correspondence tl (Cons?.tl l2)

let rec lists_correspond_ubool_implies_weaker_correspondence
  (#a: Type)
  (#b: Type)
  (stronger_correspondence: a -> b -> GTot ubool)
  (weaker_correspondence: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b)
  (stronger_implies_weaker: (x: a) -> (y: b) ->
    Lemma (requires stronger_correspondence x y) (ensures weaker_correspondence x y))
  : Lemma
  (requires lists_correspond_ubool stronger_correspondence l1 l2)
  (ensures  lists_correspond_ubool weaker_correspondence l1 l2) =
  match l1 with
  | [] -> ()
  | hd1 :: tl1 ->
      match l2 with
      | [] -> ()
      | hd2 :: tl2 ->
          stronger_implies_weaker hd1 hd2;
          lists_correspond_ubool_implies_weaker_correspondence
            stronger_correspondence weaker_correspondence tl1 tl2 stronger_implies_weaker

let rec get_correspondent_from_lists_correspond_ubool
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot ubool)
  (l1: list a)
  (l2: list b{lists_correspond_ubool correspondence l1 l2})
  (x: a{contains_ubool x l1})
  : GTot (y:b{correspondence x y /\ contains_ubool y l2}) =
  match l1 with
  | [] -> assert(false)
  | hd1 :: tl1 ->
     match l2 with
     | [] -> assert(false)
     | hd2 :: tl2 ->
        if eqb hd1 x then
          hd2
        else
          get_correspondent_from_lists_correspond_ubool correspondence tl1 tl2 x

let rec exists_correspondent
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (l1: list a)
  (l2: list b)
  : GTot bool =
  match l1, l2 with
  | hd1 :: tl1, hd2 :: tl2 -> correspondence hd1 hd2 || exists_correspondent correspondence tl1 tl2
  | _ -> false

let rec list_is_map_of_list (#a: Type) (#b: Type) (map_fun: a -> GTot b) (l1: list a) (l2: list b)
  : GTot bool =
  match l1 with
  | [] -> Nil? l2
  | hd1 :: tl1 ->
      match l2 with
      | [] -> false
      | hd2 :: tl2 -> u2b (hd2 == map_fun hd1) && list_is_map_of_list map_fun tl1 tl2

let rec if_list_is_map_of_list_then_mapped_element_in_list
  (#a: Type)
  (#b: Type)
  (map_fun: a -> GTot b)
  (l1: list a)
  (l2: list b)
  (x: a)
  : Lemma (requires contains_ubool x l1 /\ list_is_map_of_list map_fun l1 l2)
          (ensures  contains_ubool (map_fun x) l2) =
  match l1 with
  | [] -> assert False
  | hd1 :: tl1 ->
     match l2 with
     | [] -> assert False
     | hd2 :: tl2 ->
         eliminate x == hd1 \/ ~(x == hd1)
         returns  contains_ubool (map_fun x) l2
         with case_eq_hd1. assert (hd2 == map_fun x)
         and  case_ne_hd1. if_list_is_map_of_list_then_mapped_element_in_list map_fun tl1 tl2 x

let rec list_is_prefix_of_list_reflexive (#a: Type) (l1: list a)
  : Lemma (ensures list_is_prefix_of_list l1 l1) =
  match l1 with
  | [] -> ()
  | hd :: tl -> list_is_prefix_of_list_reflexive tl

let rec append_preserves_for_all
  (#a: Type)
  (property: a -> GTot bool)
  (l1: list a)
  (l2: list a)
  : Lemma
  (requires for_all_ghost property l1 /\ for_all_ghost property l2)
  (ensures  for_all_ghost property (append l1 l2)) =
  match l1 with
  | [] -> ()
  | hd :: tl -> append_preserves_for_all property tl l2

let rec append_preserves_for_all_ubool
  (#a: Type)
  (property: a -> GTot ubool)
  (l1: list a)
  (l2: list a)
  : Lemma
  (requires for_all_ubool property l1 /\ for_all_ubool property l2)
  (ensures  for_all_ubool property (append l1 l2)) =
  match l1 with
  | [] -> ()
  | hd :: tl -> append_preserves_for_all_ubool property tl l2

let rec flatten_preserves_for_all
  (#a: Type)
  (property: a -> GTot bool)
  (l: list (list a))
  : Lemma
  (requires for_all_ghost (fun sublist -> for_all_ghost property sublist) l)
  (ensures  for_all_ghost property (flatten l)) =
  match l with
  | [] -> ()
  | first_sublist :: remaining_sublists ->
     flatten_preserves_for_all property remaining_sublists;
     append_preserves_for_all property first_sublist (flatten remaining_sublists)

let rec flatten_preserves_for_all_ubool
  (#a: Type)
  (property: a -> GTot ubool)
  (l: list (list a))
  : Lemma
  (requires for_all_ubool (fun sublist -> for_all_ubool property sublist) l)
  (ensures  for_all_ubool property (flatten l)) =
  match l with
  | [] -> ()
  | first_sublist :: remaining_sublists ->
     flatten_preserves_for_all_ubool property remaining_sublists;
     append_preserves_for_all_ubool property first_sublist (flatten remaining_sublists)

let rec append_nil_is_identity (#a: Type) (l: list a) : Lemma (append l Nil == l) =
  match l with
  | [] -> ()
  | hd :: tl -> append_nil_is_identity tl

let rec append_commutes_with_map (#a: Type) (#b: Type) (f: a -> GTot b) (l1: list a) (l2: list a)
  : Lemma (append (map_ghost f l1) (map_ghost f l2) == map_ghost f (append l1 l2)) =
  match l1 with
  | [] -> ()
  | hd :: tl -> append_commutes_with_map f tl l2

let rec contains_ubool_append (#a: Type) (x: a) (l1: list a) (l2: list a)
  : Lemma (ensures  contains_ubool x l1 \/ contains_ubool x l2 <==> contains_ubool x (append l1 l2)) =
  match l1 with
  | [] -> ()
  | hd :: tl -> if eqb x hd then () else contains_ubool_append x tl l2

let rec flatten_commutes_with_map (#a: Type) (#b: Type) (f: a -> GTot b) (l: list (list a))
  : Lemma (flatten (map_ghost (fun (sublist: list a) -> map_ghost f sublist) l) == map_ghost f (flatten l)) =
  match l with
  | [] -> ()
  | hd :: tl ->
     flatten_commutes_with_map f tl;
     append_commutes_with_map f hd (flatten tl)

let rec for_all_map (#a: Type) (#b: Type) (f: a -> GTot b) (p1: b -> GTot bool) (p2: a -> GTot bool) (l: list a)
  : Lemma
  (requires p2 == (fun x -> p1 (f x)))
  (ensures  for_all_ghost p1 (map_ghost f l) = for_all_ghost p2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_map f p1 p2 tl

let rec for_all_ubool_map (#a: Type) (#b: Type) (f: a -> GTot b) (p1: b -> GTot ubool) (p2: a -> GTot ubool) (l: list a)
  : Lemma
  (requires p2 == (fun x -> p1 (f x)))
  (ensures  for_all_ubool p1 (map_ghost f l) == for_all_ubool p2 l) =
  match l with
  | [] -> ()
  | hd :: tl -> for_all_ubool_map f p1 p2 tl

let rec map_ghost_maps_last (#a: Type) (#b: Type) (f: a -> GTot b) (l: list a)
  : Lemma (requires Cons? l)
          (ensures  last (map_ghost f l) == f (last l)) =
  match l with
  | [last_element] -> ()
  | first_element :: remaining_elements -> map_ghost_maps_last f remaining_elements

let rec lemma_splitAt_fst_length (#a: Type) (n: nat) (l: list a) :
  Lemma
    (requires (n <= length l))
    (ensures  (length (fst (splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n - 1) l'

let rec for_all_range (n: nat) (f: (i: nat{i < n}) -> GTot bool) : GTot bool =
  if n = 0 then
    true
  else (
    f (n - 1) && for_all_range (n - 1) f
  )

let rec for_all_range_equivalent_to_forall (n: nat) (f: (i: nat{i < n}) -> GTot bool)
  : Lemma (for_all_range n f <==> (forall (i: nat). i < n ==> f i)) =
  if n = 0 then
    ()
  else
    for_all_range_equivalent_to_forall (n - 1) f

let rec exists_ghost_equivalent_to_exists (#a: Type) (f: a -> GTot bool) (l: list a)
  : Lemma (exists_ghost f l <==> (exists x. f x /\ contains_ubool x l))
          [SMTPat (exists_ghost f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> exists_ghost_equivalent_to_exists f tl

let rec exists_ubool_equivalent_to_exists (#a: Type) (f: a -> GTot ubool) (l: list a)
  : Lemma (exists_ubool f l <==> (exists x. f x /\ contains_ubool x l))
          [SMTPat (exists_ubool f l)] =
  match l with
  | [] -> ()
  | hd :: tl -> exists_ubool_equivalent_to_exists f tl

let exists_ghost_to_witness (#a: Type) (f: a -> GTot bool) (l: list a{exists_ghost f l})
  : GTot (x: a{f x /\ contains_ubool x l}) =
  exists_ghost_equivalent_to_exists f l;
  simpler_indefinite_description (fun x -> f x /\ contains_ubool x l)

let exists_ubool_to_witness (#a: Type) (f: a -> GTot ubool) (l: list a{exists_ubool f l})
  : GTot (x: a{f x /\ contains_ubool x l}) =
  exists_ubool_equivalent_to_exists f l;
  simpler_indefinite_description (fun x -> f x /\ contains_ubool x l)

let rec contains_ubool_to_index (#a: Type) (x: a) (l: list a{contains_ubool x l})
  : GTot (i: nat{i < length l /\ index l i == x}) =
  match l with
  | [] -> false_elim ()
  | hd :: tl -> if eqb x hd then 0 else 1 + contains_ubool_to_index x tl

let rec index_to_contains_ubool (#a: Type) (l: list a) (n: nat{n < length l})
  : Lemma (contains_ubool (index l n) l) =
  match l with
  | [] -> false_elim ()
  | hd :: tl -> if n = 0 then () else index_to_contains_ubool tl (n - 1)

let rec map_preserves_lists_correspond
  (#a: Type)
  (#b: Type)
  (#c: Type)
  (correspondence1: a -> b -> GTot bool)
  (correspondence2: a -> c -> GTot bool)
  (f: b -> GTot c)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   lists_correspond correspondence1 l1 l2
                    /\ (forall x y. correspondence1 x y ==> correspondence2 x (f y)))
          (ensures  lists_correspond correspondence2 l1 (map_ghost f l2)) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 ->
     map_preserves_lists_correspond correspondence1 correspondence2 f tl1 tl2

let rec map_preserves_lists_correspond_ubool
  (#a: Type)
  (#b: Type)
  (#c: Type)
  (correspondence1: a -> b -> GTot ubool)
  (correspondence2: a -> c -> GTot ubool)
  (f: b -> GTot c)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   lists_correspond_ubool correspondence1 l1 l2
                    /\ (forall x y. correspondence1 x y ==> correspondence2 x (f y)))
          (ensures  lists_correspond_ubool correspondence2 l1 (map_ghost f l2)) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 ->
     map_preserves_lists_correspond_ubool correspondence1 correspondence2 f tl1 tl2

let rec map_ghost_contains
  (#a: eqtype)
  (#b: eqtype)
  (f: a -> GTot b)
  (l: list a)
  (x: a)
  : Lemma (requires list_contains x l)
          (ensures  list_contains (f x) (map_ghost f l)) =
  match l with
  | [] -> ()
  | hd :: tl -> if x = hd then () else map_ghost_contains f tl x

let rec map_ghost_contains_ubool
  (#a: Type)
  (#b: Type)
  (f: a -> GTot b)
  (l: list a)
  (x: a)
  : Lemma (requires contains_ubool x l)
          (ensures  contains_ubool (f x) (map_ghost f l)) =
  match l with
  | [] -> ()
  | hd :: tl -> if eqb x hd then () else map_ghost_contains_ubool f tl x

let rec reverse_map_element_of_map_ghost
  (#a: Type)
  (#b: Type)
  (f: a -> GTot b)
  (l: list a)
  (y: b{contains_ubool y (map_ghost f l)})
  : GTot (x: a{contains_ubool x l /\ y == f x}) =
  match l with
  | [] -> false_elim ()
  | hd :: tl -> if eqb y (f hd) then hd else reverse_map_element_of_map_ghost f tl y

let rec map_ghost_preserves_length
  (#a: Type)
  (#b: Type)
  (f: a -> GTot b)
  (l: list a)
  : Lemma (ensures length (map_ghost f l) = length l) =
  match l with
  | [] -> ()
  | hd :: tl -> map_ghost_preserves_length f tl

let rec map_ghost_maps_index
  (#a: Type)
  (#b: Type)
  (f: a -> GTot b)
  (l: list a)
  (i: nat)
  : Lemma (requires i < length l \/ i < length (map_ghost f l))
          (ensures    i < length l
                    /\ i < length (map_ghost f l)
                    /\ index (map_ghost f l) i == f (index l i)) =
  match l with
  | [] -> false_elim ()
  | hd :: tl -> if i = 0 then () else map_ghost_maps_index f tl (i - 1)

let rec lists_correspond_implies_map_ghost
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  (f: a -> GTot b)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   lists_correspond correspondence l1 l2
                    /\ (forall x y. correspondence x y ==> y == f x))
          (ensures  l2 == map_ghost f l1) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 -> lists_correspond_implies_map_ghost correspondence f tl1 tl2
  | _, _ -> false_elim ()

let rec lists_correspond_ubool_implies_map_ghost
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot ubool)
  (f: a -> GTot b)
  (l1: list a)
  (l2: list b)
  : Lemma (requires   lists_correspond_ubool correspondence l1 l2
                    /\ (forall x y. correspondence x y ==> y == f x))
          (ensures  l2 == map_ghost f l1) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 -> lists_correspond_ubool_implies_map_ghost correspondence f tl1 tl2
  | _, _ -> false_elim ()

let empty_lists_correspond
  (#a: Type)
  (#b: Type)
  (correspondence: a -> b -> GTot bool)
  : Lemma (ensures lists_correspond correspondence [] []) =
  ()
