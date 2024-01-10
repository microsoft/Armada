module Strategies.AtomicToRegular

open Armada.Action
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open Spec.Behavior
open FStar.List.Tot
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Util.Behavior
open Util.List
open Util.Nth

let steps_then_steps_computation
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps1: list sem.step_t)
  (steps2: list sem.step_t)
  (s: sem.state_t)
  : GTot (option sem.state_t) =
  match steps_computation_generic sem actor starts_atomic_block false steps1 s with
  | None -> None
  | Some s' -> steps_computation_generic sem actor false ends_atomic_block steps2 s'

let rec steps_then_steps_computation_equivalent_to_append_compute
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps1: list sem.step_t)
  (steps2: list sem.step_t)
  (s: sem.state_t)
  : Lemma
  (requires Cons? steps1 /\ Cons? steps2)
  (ensures  steps_then_steps_computation sem actor starts_atomic_block ends_atomic_block steps1 steps2 s ==
            steps_computation_generic sem actor starts_atomic_block ends_atomic_block (append steps1 steps2) s)
  (decreases steps1) =
  match steps1 with
  | [last_step] -> ()
  | first_step :: remaining_steps ->
      (match step_computation_generic sem actor starts_atomic_block false first_step s with
       | None -> ()
       | Some s' -> steps_then_steps_computation_equivalent_to_append_compute sem actor
                     false ends_atomic_block remaining_steps steps2 s')

let rec list_of_list_of_steps_computation
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list (list sem.step_t))
  (s: sem.state_t)
  : GTot (option sem.state_t)
      (decreases steps) =
  match steps with
  | [] -> None
  | [last_step] -> steps_computation_generic sem actor starts_atomic_block ends_atomic_block last_step s
  | first_step :: remaining_steps ->
      (match steps_computation_generic sem actor starts_atomic_block false first_step s with
       | None -> None
       | Some s' -> list_of_list_of_steps_computation sem actor false ends_atomic_block remaining_steps s')

let rec successful_generic_atomic_step_computation_equivalent_to_list_of_list_of_steps_computation
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list (list sem.step_t))
  (s: sem.state_t)
  (s': sem.state_t)
  : Lemma (requires Some? (steps_computation_generic (make_atomic_semantics sem) actor starts_atomic_block
                             ends_atomic_block steps s))
          (ensures  steps_computation_generic (make_atomic_semantics sem) actor starts_atomic_block
                      ends_atomic_block steps s ==
                        list_of_list_of_steps_computation sem actor starts_atomic_block ends_atomic_block steps s)
          (decreases steps) =
  match steps with
  | [] -> ()
  | [last_atomic_step] -> ()
  | first_step :: remaining_steps ->
      let s_mid = Some?.v (steps_computation_generic sem actor starts_atomic_block false first_step s) in
      successful_generic_atomic_step_computation_equivalent_to_list_of_list_of_steps_computation sem actor false
        ends_atomic_block remaining_steps s_mid s'

let successful_atomic_step_computation_equivalent_to_list_of_list_of_steps_computation
  (sem: semantics_t)
  (transition: transition_t (make_atomic_semantics sem))
  (s: sem.state_t)
  (s': sem.state_t)
  : Lemma (requires next_transition_generic (make_atomic_semantics sem) transition s s')
          (ensures  steps_computation_generic (make_atomic_semantics sem) transition.actor true true
                      transition.steps s ==
                      list_of_list_of_steps_computation sem transition.actor true true transition.steps s)
          (decreases transition.steps) =
  successful_generic_atomic_step_computation_equivalent_to_list_of_list_of_steps_computation sem transition.actor
    true true transition.steps s s'

let rec flatten_steps_preserves_eval_result
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (flattened_steps: list sem.step_t)
  (unflattened_steps: list (list sem.step_t))
  (s: sem.state_t)
  : Lemma
  (requires   flattened_steps == flatten unflattened_steps
            /\ (forall steps. contains_ubool steps unflattened_steps ==> Cons? steps)
            /\ Some? (list_of_list_of_steps_computation sem actor starts_atomic_block ends_atomic_block
                       unflattened_steps s))
  (ensures  (steps_computation_generic sem actor starts_atomic_block ends_atomic_block flattened_steps s) ==
            (list_of_list_of_steps_computation sem actor starts_atomic_block ends_atomic_block unflattened_steps s))
  (decreases unflattened_steps) =
  match unflattened_steps with
  | [] -> ()
  | [last_atomic_step] -> append_nil_is_identity last_atomic_step
  | first_atomic_step :: remaining_unflattened_steps ->
     let remaining_steps = flatten remaining_unflattened_steps in
     assert (contains_ubool first_atomic_step unflattened_steps);
     steps_then_steps_computation_equivalent_to_append_compute sem actor starts_atomic_block ends_atomic_block
       first_atomic_step remaining_steps s;
     (match steps_computation_generic sem actor starts_atomic_block false first_atomic_step s with
      | None -> ()
      | Some s' -> flatten_steps_preserves_eval_result sem actor false ends_atomic_block remaining_steps
                    remaining_unflattened_steps s')

let rec atomic_steps_computation_implies_nonempty_steps
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (atomic_steps: list (list sem.step_t))
  (s: sem.state_t)
  : Lemma (requires Some? (list_of_list_of_steps_computation sem actor starts_atomic_block ends_atomic_block
                             atomic_steps s))
          (ensures  forall atomic_step. contains_ubool atomic_step atomic_steps ==> Cons? atomic_step)
          (decreases atomic_steps) =
  match atomic_steps with
  | [last_atomic_step] -> ()
  | first_atomic_step :: remaining_atomic_steps ->
      let s' = Some?.v (steps_computation_generic sem actor starts_atomic_block false first_atomic_step s) in
      atomic_steps_computation_implies_nonempty_steps sem actor false ends_atomic_block remaining_atomic_steps s'

let flatten_transition_preserves_next_transition
  (sem: semantics_t)
  (ltr: transition_t (make_atomic_semantics sem))
  (htr: transition_t sem)
  (s: sem.state_t)
  (s': sem.state_t)
  : Lemma
  (requires   htr.steps == flatten ltr.steps
            /\ next_transition_generic (make_atomic_semantics sem) ltr s s'
            /\ htr.actor == ltr.actor)
  (ensures  next_transition_generic sem htr s s') =
  let atomic_sem = make_atomic_semantics sem in
  let unflattened_steps = ltr.steps in
  successful_atomic_step_computation_equivalent_to_list_of_list_of_steps_computation sem ltr s s';
  atomic_steps_computation_implies_nonempty_steps sem ltr.actor true true unflattened_steps s;
  flatten_steps_preserves_eval_result sem ltr.actor true true htr.steps unflattened_steps s

let rec indices_correspond_implies_program_containment
  (sem: semantics_t)
  (indices: list nat)
  (atomic_action: list sem.action_t)
  (regular_actions: list sem.action_t)
  : Lemma
  (requires 
    (let index_and_action_corr = (fun index -> fun action -> (nth regular_actions index) == (Some action)) in
     lists_correspond_ubool index_and_action_corr indices atomic_action))
  (ensures forall action. contains_ubool action atomic_action ==> contains_ubool action regular_actions) =
  match atomic_action with
  | [] -> ()
  | first_action :: remaining_actions ->
     nth_implies_contains_ubool regular_actions (hd indices) first_action;
     indices_correspond_implies_program_containment sem (tl indices) remaining_actions regular_actions

let expanding_atomic_action_preserves_program_containment
  (ar: atomic_refines_regular_relation_t)
  (atomic_step: list ar.sem.step_t)
  : Lemma
  (requires contains_ubool (map_ghost ar.sem.step_to_action_f atomic_step) ar.lprog.actions)
  (ensures  for_all_ubool (program_contains_action_of_step_generic ar.sem ar.hprog) atomic_step) =
  let sem = ar.sem in
  let regular_actions = ar.hprog.actions in
  let atomic_actions = ar.lprog.actions in
  let atomic_action = map_ghost ar.sem.step_to_action_f atomic_step in
  let atomic_index = contains_to_index atomic_action atomic_actions in
  let index_and_action_corr = fun index -> fun action -> (nth regular_actions index) == (Some action) in
  let indices_and_actions_corr =
    fun indices -> fun atomic_action -> lists_correspond_ubool index_and_action_corr indices atomic_action in
  let step_to_action = sem.step_to_action_f in
  ar.atomic_to_regular_map_valid ();
  assert (valid_atomic_to_regular_map sem atomic_actions regular_actions ar.atomic_to_regular_map ==
          lists_correspond_ubool indices_and_actions_corr ar.atomic_to_regular_map atomic_actions)
    by FStar.Tactics.V2.trefl ();
  lists_correspond_ubool_implies_index_matches
    indices_and_actions_corr ar.atomic_to_regular_map atomic_actions atomic_index;
  let indices = Some?.v (nth ar.atomic_to_regular_map atomic_index) in
  indices_correspond_implies_program_containment sem indices atomic_action regular_actions;
  introduce forall step. contains_ubool step atomic_step ==> program_contains_action_of_step_generic ar.sem ar.hprog step
  with introduce _ ==> _
  with _. (
    let p = fun action -> contains_ubool action regular_actions in
    assert (for_all_ubool p (map_ghost step_to_action atomic_step));
    map_ghost_contains_ubool step_to_action atomic_step step
  )

let flatten_transition_preserves_program_containment
  (ar: atomic_refines_regular_relation_t)
  (latomic_steps: list (list ar.sem.step_t))
  (hsteps: list ar.sem.step_t)
  : Lemma
  (requires   hsteps == flatten latomic_steps
            /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ar.sem) ar.lprog)
                latomic_steps)
  (ensures  for_all_ubool (program_contains_action_of_step_generic ar.sem ar.hprog) hsteps) =
  let property0 = program_contains_action_of_step_generic ar.sem ar.hprog in
  let property1 = program_contains_action_of_step_generic (make_atomic_semantics ar.sem) ar.lprog in
  let property2 = (fun atomic_step -> (for_all_ubool property0 atomic_step)) in
  let property_implication (latomic_step: list ar.sem.step_t)
    : Lemma (requires property1 latomic_step) (ensures property2 latomic_step) =
    (expanding_atomic_action_preserves_program_containment ar latomic_step) in
  for_all_ubool_implication property_implication latomic_steps;
  flatten_preserves_for_all_ubool property0 latomic_steps

let atomic_refines_regular_relation_implies_spec_next
  (ar: atomic_refines_regular_relation_t)
  (s s': ar.sem.state_t)
  : Lemma (requires (semantics_to_spec (make_atomic_semantics ar.sem) ar.lprog).next s s')
          (ensures  (semantics_to_spec ar.sem ar.hprog).next s s') =
  let sem = ar.sem in
  let atomic_sem = make_atomic_semantics sem in
  eliminate exists ltr. next_program_generic atomic_sem ar.lprog ltr s s'
  returns (semantics_to_spec sem ar.hprog).next s s'
  with ltr_satisfies_next_program.
    let lsteps = ltr.steps in
    let hsteps: list sem.step_t = flatten lsteps in
    let atomic_actions = ar.lprog.actions in
    flatten_transition_preserves_program_containment ar ltr.steps hsteps;
    let htr: transition_t sem = make_transition sem ltr.actor hsteps in
    let lactions = map_ghost (map_ghost sem.step_to_action_f) lsteps in
    let property1 = fun atomic_step -> contains_ubool (map_ghost sem.step_to_action_f atomic_step) atomic_actions in
    assert (for_all_ubool (program_contains_action_of_step_generic atomic_sem ar.lprog) lsteps);
    assert (program_contains_action_of_step_generic atomic_sem ar.lprog == property1) by FStar.Tactics.V2.trefl();
    assert (for_all_ubool property1 lsteps);
    let property2 = fun atomic_action -> contains_ubool atomic_action atomic_actions in
    for_all_ubool_map
      (map_ghost sem.step_to_action_f)
      property2
      (fun atomic_step -> contains_ubool (map_ghost sem.step_to_action_f atomic_step) atomic_actions)
      lsteps;
    assert (for_all_ubool property2 lactions);
    flatten_transition_preserves_next_transition sem ltr htr s s';
    introduce exists htr. next_program_generic sem ar.hprog htr s s'
    with htr and ()

let rec atomic_refines_regular_relation_implies_behavior_satisfies_hspec_next
  (ar: atomic_refines_regular_relation_t)
  (b: behavior_t ar.sem.state_t) :
  Lemma (requires behavior_satisfies_next b (semantics_to_spec (make_atomic_semantics ar.sem) ar.lprog).next)
        (ensures  behavior_satisfies_next b (semantics_to_spec ar.sem ar.hprog).next) =
  match b with
  | [] -> ()
  | [state] -> ()
  | state1 :: state2 :: tl ->
      atomic_refines_regular_relation_implies_spec_next ar state1 state2;
      atomic_refines_regular_relation_implies_behavior_satisfies_hspec_next ar (state2 :: tl)

let atomic_refines_regular_relation_implies_behavior_satisfies_hspec
  (ar: atomic_refines_regular_relation_t)
  (b: behavior_t ar.sem.state_t) :
  Lemma (requires behavior_satisfies_spec b (semantics_to_spec (make_atomic_semantics ar.sem) ar.lprog))
        (ensures  behavior_satisfies_spec b (semantics_to_spec ar.sem ar.hprog)) =
  match b with
  | [] -> ()
  | state1 :: _ ->
     ar.init_implies_init state1;
     atomic_refines_regular_relation_implies_behavior_satisfies_hspec_next ar b

let atomic_refines_regular_relation_implies_refinement (ar: atomic_refines_regular_relation_t)
  (* see .fsti file for spec *) =
  let lspec = semantics_to_spec (make_atomic_semantics ar.sem) ar.lprog in
  let hspec = semantics_to_spec ar.sem ar.hprog in
  let lem (b: behavior_t ar.sem.state_t) : Lemma
    (requires behavior_satisfies_spec b lspec)
    (ensures  behavior_satisfies_spec b hspec /\ behavior_refines_behavior b b eq2)
    [SMTPat (behavior_satisfies_spec b lspec)]
    = (atomic_refines_regular_relation_implies_behavior_satisfies_hspec ar b;
       refinement_relation_reflexive_implies_behavior_refines_itself b eq2) in
  ()
