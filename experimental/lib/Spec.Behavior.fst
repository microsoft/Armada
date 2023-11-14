module Spec.Behavior

open Spec.Ubool

type behavior_t (a: Type) = list a
type refinement_relation_t (low_state_t high_state_t: Type) = low_state_t -> high_state_t -> GTot ubool
noeq type spec_t (state_t: Type) = { init: state_t -> GTot ubool; next: state_t -> state_t -> GTot ubool }

let rec behavior_refines_behavior
  (#low_state_t: Type)
  (#high_state_t: Type)
  (lb: behavior_t low_state_t)
  (hb: behavior_t high_state_t)
  (rr: refinement_relation_t low_state_t high_state_t)
  : GTot ubool =
  match lb with
  | [] -> Nil? hb
  | lstate :: ltail ->
    match hb with
    | [] -> false
    | hstate :: htail ->
      rr lstate hstate /\
      (  behavior_refines_behavior ltail htail rr // neither behavior stutters at the beginning
       \/ behavior_refines_behavior ltail hb rr  // behavior #1 stutters at the beginning
       \/ behavior_refines_behavior lb htail rr) // behavior #2 stutters at the beginning

let rec behavior_satisfies_next
  (#state_t: Type)
  (b: behavior_t state_t)
  (next: state_t -> state_t -> GTot ubool)
  : GTot ubool =
  match b with
  | [] -> True
  | [s] -> True
  | s1 :: s2 :: tl -> next s1 s2 /\ behavior_satisfies_next (s2 :: tl) next

let behavior_satisfies_spec
  (#state_t: Type)
  (behavior: behavior_t state_t)
  (spec: spec_t state_t)
  : GTot ubool =
  match behavior with
  | [] -> False
  | s1 :: _ -> spec.init s1 /\ behavior_satisfies_next behavior spec.next

let spec_refines_spec
  (#low_state_t: Type)
  (#high_state_t: Type)
  (lspec: spec_t low_state_t)
  (hspec: spec_t high_state_t)
  (rr: refinement_relation_t low_state_t high_state_t)  
  : ubool =
  forall (lb: behavior_t low_state_t).
    behavior_satisfies_spec lb lspec
    ==> (exists (hb: behavior_t high_state_t). behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb rr)
