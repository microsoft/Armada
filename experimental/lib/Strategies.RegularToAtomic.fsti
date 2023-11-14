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
open Util.List
open Util.Nth

noeq type successor_info_t (sem: semantics_t) = {
  action: sem.action_t;
  path_index: nat;
}

noeq type atomic_path_info_t (sem: semantics_t) = {
  path: list sem.action_t;
  breaking: bool;
  // For a path that terminates in a break state, the index of the atomic action corresponding to it:
  atomic_action_index: nat;
  // For a path that doesn't terminate in a break state, the successor info for all the atomic paths that succeed it.
  successors: list (successor_info_t sem);
}

let action_among_successors
  (sem: semantics_t)
  (action: sem.action_t)
  (successors: list (successor_info_t sem))
  : GTot ubool =
  exists successor. contains_ubool successor successors /\ successor.action == action

noeq type regular_refines_atomic_relation_t = {
  sem: semantics_t;
  lprog: program_t sem;
  hprog: program_t (make_atomic_semantics sem);
  is_breaking_state: sem.state_t -> sem.actor_t -> GTot bool;
  starting_successors: list (successor_info_t sem);
  atomic_path_infos: list (atomic_path_info_t sem);

  starting_successors_match_path_infos_proof:
    (successor: successor_info_t sem{contains_ubool successor starting_successors}) ->
    squash (  successor.path_index < length atomic_path_infos
            /\ (index atomic_path_infos successor.path_index).path == [successor.action]);

  path_successors_match_path_infos_proof:
    (atomic_path_info: atomic_path_info_t sem) ->
    (successor: successor_info_t sem{
        contains_ubool atomic_path_info atomic_path_infos
      /\ contains_ubool successor atomic_path_info.successors}) ->
    squash (   successor.path_index < length atomic_path_infos
            /\ (index atomic_path_infos successor.path_index).path == append atomic_path_info.path
                 [successor.action]);

  path_breaking_correct_proof:
    (atomic_path_info: atomic_path_info_t sem) ->
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (steps: list sem.step_t) ->
    (s: sem.state_t{
        contains_ubool atomic_path_info atomic_path_infos
      /\ (map_ghost sem.step_to_action_f steps) == atomic_path_info.path
      /\ Some? (steps_computation_generic sem actor starts_atomic_block ends_atomic_block steps s)
      /\ (starts_atomic_block ==> is_breaking_state s actor)}) ->
    squash (let s' = Some?.v (steps_computation_generic sem actor starts_atomic_block ends_atomic_block
                                steps s) in
            (atomic_path_info.breaking = is_breaking_state s' actor));

  path_atomic_indices_correct_proof:
    (atomic_path_info: atomic_path_info_t sem{
         contains_ubool atomic_path_info atomic_path_infos
       /\ atomic_path_info.breaking}) ->
    squash (  atomic_path_info.atomic_action_index < length hprog.actions
            /\ index hprog.actions atomic_path_info.atomic_action_index == atomic_path_info.path);

  starting_successors_complete_proof:
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (step: sem.step_t) ->
    (s: sem.state_t{
        contains_ubool (sem.step_to_action_f step) lprog.actions
      /\ is_breaking_state s actor
      /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)}) ->
    squash (action_among_successors sem (sem.step_to_action_f step) starting_successors);

  path_successors_complete_proof:
    (atomic_path_info: atomic_path_info_t sem) ->
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (steps: list sem.step_t) ->
    (step: sem.step_t) ->
    (s: sem.state_t{
        contains_ubool atomic_path_info atomic_path_infos
      /\ map_ghost sem.step_to_action_f steps == atomic_path_info.path
      /\ contains_ubool (sem.step_to_action_f step) lprog.actions
      /\ not atomic_path_info.breaking
      /\ (match steps_computation_generic sem actor starts_atomic_block false steps s with
         | None -> False
         | Some s' -> Some? (step_computation_generic sem actor false ends_atomic_block step s'))}) ->
    squash (action_among_successors sem (sem.step_to_action_f step) atomic_path_info.successors);

  actions_dont_unbreak_other_actors_proof:
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (step: sem.step_t) ->
    (s: sem.state_t{
      let action = sem.step_to_action_f step in
         contains_ubool action lprog.actions
      /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)}) ->
    squash (let s' = Some?.v (step_computation_generic sem actor starts_atomic_block
                                ends_atomic_block step s) in
            forall other_actor. is_breaking_state s other_actor /\ actor <> other_actor ==>
                             is_breaking_state s' other_actor);

  actions_break_if_last_in_transition_proof:
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (step: sem.step_t) ->
    (s: sem.state_t{
        contains_ubool (sem.step_to_action_f step) lprog.actions
      /\ Some? (step_computation_generic sem actor starts_atomic_block true step s)
      /\ (starts_atomic_block ==> is_breaking_state s actor)}) ->
    squash (let s' = Some?.v (step_computation_generic sem actor starts_atomic_block true step s) in
            is_breaking_state s' actor);

  init_breaks_all_actors_proof: (s: sem.state_t{lprog.init_f s}) -> squash (forall actor. is_breaking_state s actor);

  init_implies_init_proof: (s: sem.state_t{lprog.init_f s}) -> squash (hprog.init_f s);
}

val regular_refines_atomic_relation_implies_refinement (ra: regular_refines_atomic_relation_t)
  : Lemma (ensures (spec_refines_spec
                    (semantics_to_spec ra.sem ra.lprog)
                    (semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog)
                    eq2))
