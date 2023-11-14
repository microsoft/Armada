module Spec.List

open FStar.Calc
open FStar.List.Tot
open Spec.Ubool

let list_len = length
let list_contains = mem
let contains_ubool = memP

let rec list_is_prefix_of_list (#a: Type) (l1: list a) (l2: list a) : GTot bool =
  match l1 with
  | [] -> true
  | hd1 :: tl1 ->
      match l2 with
      | [] -> false
      | hd2 :: tl2 -> eqb hd1 hd2 && list_is_prefix_of_list tl1 tl2
