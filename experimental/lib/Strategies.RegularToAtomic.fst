module Strategies.RegularToAtomic

open Armada.Action
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Util.Behavior
open Util.List
open Util.Logic
open Util.Nth

let all_threads_breaking
  (ra: regular_refines_atomic_relation_t)
  (s: ra.sem.state_t)
  : GTot ubool =
  forall actor. ra.is_breaking_state s actor

let all_threads_breaking_except
  (ra: regular_refines_atomic_relation_t)
  (s: ra.sem.state_t)
  (actor: ra.sem.actor_t)
  : GTot ubool =
  forall other_actor. actor <> other_actor ==> ra.is_breaking_state s other_actor

#push-options "--z3rlimit 10"

let rec convert_hsteps_and_path_and_lsteps_to_hsteps
  (ra: regular_refines_atomic_relation_t)
  (actor: ra.sem.actor_t)
  (s0: ra.sem.state_t)
  (hsteps: list (make_atomic_semantics ra.sem).step_t)
  (s1: ra.sem.state_t)
  (lpath_steps: list ra.sem.step_t)
  (atomic_path_info: atomic_path_info_t ra.sem)
  (s2: ra.sem.state_t)
  (lsteps: list ra.sem.step_t)
  (s3: ra.sem.state_t
    {  (if Nil? hsteps then
          s1 == s0
        else
            Some s1 == steps_computation_generic (make_atomic_semantics ra.sem) actor true false hsteps s0
          /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps)
     /\ ra.is_breaking_state s1 actor
     /\ contains_ubool atomic_path_info ra.atomic_path_infos
     /\ not atomic_path_info.breaking
     /\ map_ghost ra.sem.step_to_action_f lpath_steps == atomic_path_info.path
     /\ Some s2 == steps_computation_generic ra.sem actor (Nil? hsteps) false lpath_steps s1
     /\ for_all_ubool (program_contains_action_of_step_generic ra.sem ra.lprog) lsteps
     /\ Some s3 == steps_computation_generic ra.sem actor false true lsteps s2})
  : GTot (hsteps': list (make_atomic_semantics ra.sem).step_t
    {  Some s3 == steps_computation_generic (make_atomic_semantics ra.sem) actor true true hsteps' s0
     /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps'})
    (decreases lsteps) =
  match lsteps with
  | first_step :: remaining_steps ->
      let first_action = ra.sem.step_to_action_f first_step in
      let starts_atomic_block = Nil? hsteps in
      let ends_atomic_block = Nil? remaining_steps in
      assert (Some? (steps_computation_generic ra.sem actor starts_atomic_block false lpath_steps s1));
      ra.path_successors_complete_proof atomic_path_info actor starts_atomic_block ends_atomic_block lpath_steps
        first_step s1;
      assert (action_among_successors ra.sem first_action atomic_path_info.successors);
      let successor: (successor_info_t ra.sem) =
         simpler_indefinite_description
           (fun (successor: successor_info_t ra.sem) ->
              contains_ubool successor atomic_path_info.successors /\ successor.action == first_action) in
      ra.path_successors_match_path_infos_proof atomic_path_info successor;
      let next_atomic_path_info = index ra.atomic_path_infos successor.path_index in
      index_implies_contains_ubool ra.atomic_path_infos successor.path_index next_atomic_path_info;
      let hstep = append lpath_steps [first_step] in
      append_one_extends_steps_computation_generic ra.sem actor starts_atomic_block ends_atomic_block
        lpath_steps first_step s1;
      let s_mid = Some?.v (steps_computation_generic ra.sem actor starts_atomic_block ends_atomic_block hstep s1) in
      assert (Some s_mid == step_computation_generic ra.sem actor false ends_atomic_block first_step s2);
      if ends_atomic_block then
        ra.actions_break_if_last_in_transition_proof actor false first_step s2
      else
        ();
      append_commutes_with_map ra.sem.step_to_action_f lpath_steps [first_step];
      ra.path_breaking_correct_proof next_atomic_path_info actor starts_atomic_block ends_atomic_block hstep s1;
      if next_atomic_path_info.breaking then (
        let hsteps' = append hsteps [hstep] in
        assert (next_atomic_path_info.breaking = ra.is_breaking_state s_mid actor);
        ra.path_atomic_indices_correct_proof next_atomic_path_info;
        index_implies_contains_ubool ra.hprog.actions next_atomic_path_info.atomic_action_index
          next_atomic_path_info.path;
        if Cons? hsteps then
          append_one_extends_steps_computation_generic (make_atomic_semantics ra.sem) actor true
            ends_atomic_block hsteps hstep s0
        else
          ();
        append_preserves_for_all_ubool
          (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps [hstep];
        if Nil? remaining_steps then
          hsteps'
        else
          convert_hsteps_and_lsteps_to_hsteps ra actor s0 hsteps' s_mid remaining_steps s3
      )
      else
        convert_hsteps_and_path_and_lsteps_to_hsteps ra actor s0 hsteps s1 hstep next_atomic_path_info s_mid remaining_steps s3

and convert_hsteps_and_lsteps_to_hsteps
  (ra: regular_refines_atomic_relation_t)
  (actor: ra.sem.actor_t)
  (s0: ra.sem.state_t)
  (hsteps: list (make_atomic_semantics ra.sem).step_t)
  (s1: ra.sem.state_t)
  (lsteps: list ra.sem.step_t)
  (s2: ra.sem.state_t
    {  (if Nil? hsteps then
            s1 == s0
        else
            Some s1 == steps_computation_generic (make_atomic_semantics ra.sem) actor true false hsteps s0
          /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps)
     /\ ra.is_breaking_state s1 actor
     /\ for_all_ubool (program_contains_action_of_step_generic ra.sem ra.lprog) lsteps
     /\ Some s2 == steps_computation_generic ra.sem actor (Nil? hsteps) true lsteps s1})
  : GTot (hsteps': list (make_atomic_semantics ra.sem).step_t
    {  Some s2 == steps_computation_generic (make_atomic_semantics ra.sem) actor true true hsteps' s0
     /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps'})
    (decreases lsteps) =
  match lsteps with
  | first_step :: remaining_steps ->
      let first_action = ra.sem.step_to_action_f first_step in
      let starts_atomic_block = Nil? hsteps in
      let ends_atomic_block = Nil? remaining_steps in
      ra.starting_successors_complete_proof actor starts_atomic_block ends_atomic_block first_step s1;
      assert (action_among_successors ra.sem first_action ra.starting_successors);
      let successor: (successor_info_t ra.sem) =
         simpler_indefinite_description
           (fun (successor: successor_info_t ra.sem) ->
              contains_ubool successor ra.starting_successors /\ successor.action == first_action) in
      ra.starting_successors_match_path_infos_proof successor;
      let atomic_path_info = index ra.atomic_path_infos successor.path_index in
      index_implies_contains_ubool ra.atomic_path_infos successor.path_index atomic_path_info;
      let s_mid = (Some?.v (steps_computation_generic ra.sem actor starts_atomic_block ends_atomic_block
                              [first_step] s1)) in
      if ends_atomic_block then
        ra.actions_break_if_last_in_transition_proof actor starts_atomic_block first_step s1
      else
        ();
      ra.path_breaking_correct_proof atomic_path_info actor starts_atomic_block ends_atomic_block [first_step] s1;
      if atomic_path_info.breaking then (
        let hstep: list ra.sem.step_t = [first_step] in
        let hsteps' = append hsteps [hstep] in
        if Cons? hsteps then
          append_one_extends_steps_computation_generic (make_atomic_semantics ra.sem) actor true
            ends_atomic_block hsteps hstep s0
        else
          ();
        assert (atomic_path_info.breaking = ra.is_breaking_state s_mid actor);
        ra.path_atomic_indices_correct_proof atomic_path_info;
        index_implies_contains_ubool ra.hprog.actions atomic_path_info.atomic_action_index atomic_path_info.path;
        append_preserves_for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog)
          hsteps [hstep];
        if Nil? remaining_steps then
          hsteps'
        else
          convert_hsteps_and_lsteps_to_hsteps ra actor s0 hsteps' s_mid remaining_steps s2
      )
      else
        convert_hsteps_and_path_and_lsteps_to_hsteps ra actor s0 hsteps s1 [first_step] atomic_path_info s_mid
          remaining_steps s2

#pop-options

let convert_lsteps_to_hsteps
  (ra: regular_refines_atomic_relation_t)
  (actor: ra.sem.actor_t)
  (s: ra.sem.state_t{ra.is_breaking_state s actor})
  (lsteps: list ra.sem.step_t{for_all_ubool (program_contains_action_of_step_generic ra.sem ra.lprog) lsteps})
  (s': ra.sem.state_t{Some s' == steps_computation_generic ra.sem actor true true lsteps s})
  : GTot (hsteps: list (make_atomic_semantics ra.sem).step_t
      {  Some s' == steps_computation_generic (make_atomic_semantics ra.sem) actor true true hsteps s
       /\ for_all_ubool (program_contains_action_of_step_generic (make_atomic_semantics ra.sem) ra.hprog) hsteps}) =
  convert_hsteps_and_lsteps_to_hsteps ra actor s [] s lsteps s'

let rec last_in_transition_steps_preserve_all_threads_breaking
  (ra: regular_refines_atomic_relation_t)
  (actor: ra.sem.actor_t)
  (starts_atomic_block: bool)
  (s: ra.sem.state_t)
  (steps: list ra.sem.step_t)
  (s': ra.sem.state_t)
  : Lemma
    (requires   all_threads_breaking_except ra s actor
              /\ for_all_ubool (program_contains_action_of_step_generic ra.sem ra.lprog) steps
              /\ Some s' == steps_computation_generic ra.sem actor starts_atomic_block true steps s
              /\ (starts_atomic_block ==> ra.is_breaking_state s actor))
    (ensures  all_threads_breaking ra s')
    (decreases steps) =
  match steps with
  | [last_step] ->
     ra.actions_break_if_last_in_transition_proof actor starts_atomic_block last_step s;
     ra.actions_dont_unbreak_other_actors_proof actor starts_atomic_block true last_step s
  | first_step :: remaining_steps ->
      ra.actions_dont_unbreak_other_actors_proof actor starts_atomic_block false first_step s;
      let s_mid = (Some?.v (step_computation_generic ra.sem actor starts_atomic_block false first_step s)) in
      last_in_transition_steps_preserve_all_threads_breaking ra actor false s_mid remaining_steps s'

let regular_refines_atomic_relation_implies_spec_next
  (ra: regular_refines_atomic_relation_t)
  (s s': ra.sem.state_t)
  : Lemma (requires all_threads_breaking ra s /\ (semantics_to_spec ra.sem ra.lprog).next s s')
          (ensures    all_threads_breaking ra s'
                    /\ (semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog).next s s') =
  let sem = ra.sem in
  let atomic_sem = make_atomic_semantics sem in
  eliminate exists ltr. next_program_generic sem ra.lprog ltr s s'
  returns all_threads_breaking ra s' /\ (semantics_to_spec atomic_sem ra.hprog).next s s'
  with ltr_satisfies_next_program.
    let hsteps = convert_lsteps_to_hsteps ra ltr.actor s ltr.steps s' in
    let htr = { actor = (ltr.actor <: atomic_sem.actor_t); steps = hsteps } in
    last_in_transition_steps_preserve_all_threads_breaking ra ltr.actor true s ltr.steps s'

let rec regular_refines_atomic_relation_implies_behavior_satisfies_hspec_next
  (ra: regular_refines_atomic_relation_t)
  (b: behavior_t ra.sem.state_t)
  : Lemma (requires   Cons? b
                    /\ all_threads_breaking ra (Cons?.hd b) 
                    /\ behavior_satisfies_next b (semantics_to_spec ra.sem ra.lprog).next)
          (ensures  behavior_satisfies_next b (semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog).next) =
  match b with
  | [] -> ()
  | [state] -> ()
  | state1 :: state2 :: tl ->
      regular_refines_atomic_relation_implies_spec_next ra state1 state2;
      regular_refines_atomic_relation_implies_behavior_satisfies_hspec_next ra (state2 :: tl)

let regular_refines_atomic_relation_implies_behavior_satisfies_hspec
  (ra: regular_refines_atomic_relation_t)
  (b: behavior_t ra.sem.state_t)
  : Lemma (requires   behavior_satisfies_spec b (semantics_to_spec ra.sem ra.lprog)
                    /\ all_threads_breaking ra (Cons?.hd b))
          (ensures  behavior_satisfies_spec b (semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog)) =
  ra.init_implies_init_proof (Cons?.hd b);
  regular_refines_atomic_relation_implies_behavior_satisfies_hspec_next ra b

let regular_refines_atomic_relation_implies_refinement (ra: regular_refines_atomic_relation_t)
  (* see .fsti file for spec *) =
  let lspec = semantics_to_spec ra.sem ra.lprog in
  let hspec = semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog in
  let lem (b: behavior_t ra.sem.state_t) : Lemma
    (requires behavior_satisfies_spec b lspec)
    (ensures  behavior_satisfies_spec b hspec /\ behavior_refines_behavior b b eq2)
    [SMTPat (behavior_satisfies_spec b lspec)]
    = (ra.init_breaks_all_actors_proof (Cons?.hd b);
       regular_refines_atomic_relation_implies_behavior_satisfies_hspec ra b;
       refinement_relation_reflexive_implies_behavior_refines_itself b eq2) in
  ()
