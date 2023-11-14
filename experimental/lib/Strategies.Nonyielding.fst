module Strategies.Nonyielding

open Armada.Action
open Armada.Base
open Armada.Statement
open Armada.Transition
open Spec.List
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List

let action_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: pc_t -> GTot bool)
  (action: Armada.Action.t)
  : GTot bool =
  let ps = action.program_statement in
  (match ps.start_pc with
   | None -> ps.starts_atomic_block && ps.ends_atomic_block
   | Some pc -> ps.starts_atomic_block = not (is_nonyielding_pc pc))
  &&
  (match program_statement_to_ending_thread_state ps with
   | ThreadStateRunning -> ps.ends_atomic_block && None? ps.start_pc
   | ThreadStateAtPC pc -> ps.ends_atomic_block = not (is_nonyielding_pc pc)
   | ThreadStateNotRunning status -> ps.ends_atomic_block
   | ThreadStateProcessStopped stop_reason -> ps.ends_atomic_block)
  &&
  (match ps.statement with
   | CreateThreadStatement _ initial_pc _ _ _ _ _ -> not (is_nonyielding_pc initial_pc)
   | _ -> true)

let efficient_is_yielding_pc
  (is_nonyielding_pc: array_t bool)
  (pc: nat)
  : GTot bool =
  match array_nth is_nonyielding_pc pc with
  | Some b -> not b
  | None -> false

let efficient_is_nonyielding_pc
  (is_nonyielding_pc: array_t bool)
  (pc: nat)
  : GTot bool =
  match array_nth is_nonyielding_pc pc with
  | Some b -> b
  | None -> false

let efficient_action_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: array_t bool)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  let ps = action.program_statement in
  (match pc_indices.start_pc_index with
   | None -> ps.starts_atomic_block && ps.ends_atomic_block
   | Some pc -> ps.starts_atomic_block = efficient_is_yielding_pc is_nonyielding_pc pc)
  &&
  (match efficient_program_statement_to_ending_thread_state ps pc_indices with
   | EfficientThreadStateRunning -> ps.ends_atomic_block && None? pc_indices.start_pc_index
   | EfficientThreadStateAtPC pc -> ps.ends_atomic_block = efficient_is_yielding_pc is_nonyielding_pc pc
   | EfficientThreadStateNotRunning status -> ps.ends_atomic_block
   | EfficientThreadStateProcessStopped stop_reason -> ps.ends_atomic_block)
  &&
  (match pc_indices.create_thread_initial_pc_index with
   | Some initial_pc -> efficient_is_yielding_pc is_nonyielding_pc initial_pc
   | None -> true)

let each_action_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actions: list Armada.Action.t)
  : GTot bool =
  for_all_ghost (action_consistent_with_is_nonyielding_pc is_nonyielding_pc) actions

let efficient_each_action_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: array_t bool)
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : GTot bool =
  lists_correspond
    (fun action pc_indices -> efficient_action_consistent_with_is_nonyielding_pc is_nonyielding_pc action pc_indices)
    actions pc_indices_list

let each_action_list_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actions_list: list (list Armada.Action.t))
  : GTot bool =
  for_all_ghost (each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc) actions_list

let efficient_each_action_list_consistent_with_is_nonyielding_pc
  (is_nonyielding_pc: array_t bool)
  (actions_array: array_t (list Armada.Action.t))
  (pc_indices_array: array_t (list statement_pc_indices_t))
  : GTot bool =
  arrays_correspond
    (fun actions pc_indices_list ->
      efficient_each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc actions pc_indices_list)
    actions_array pc_indices_array

let action_ends_atomic_block_if_necessary
  (action: Armada.Action.t)
  : GTot bool =
  match program_statement_to_ending_thread_state action.program_statement with
  | ThreadStateRunning -> action.program_statement.ends_atomic_block
  | ThreadStateAtPC pc -> true
  | ThreadStateNotRunning _ -> action.program_statement.ends_atomic_block
  | ThreadStateProcessStopped _ -> action.program_statement.ends_atomic_block

let each_action_ends_atomic_block_if_necessary
  (actions: list Armada.Action.t)
  : GTot bool =
  for_all_ghost action_ends_atomic_block_if_necessary actions

let each_action_list_ends_atomic_block_if_necessary
  (actions_list: list (list Armada.Action.t))
  : GTot bool =
  for_all_ghost each_action_ends_atomic_block_if_necessary actions_list

let rec action_list_doesnt_internally_yield
  (actions: list Armada.Action.t)
  : GTot bool (decreases actions) =
  match actions with
  | [] -> true
  | [action] -> true
  | first_action :: second_action :: remaining_actions ->
         not first_action.program_statement.ends_atomic_block
      && not second_action.program_statement.starts_atomic_block
      && first_action.ok
      && action_list_doesnt_internally_yield (second_action :: remaining_actions)

let each_action_list_doesnt_internally_yield
  (actions_list: list (list Armada.Action.t))
  : GTot bool =
  for_all_ghost action_list_doesnt_internally_yield actions_list

let rec consecutive_actions_end_and_start_with_same_pc
  (actions: list Armada.Action.t)
  : GTot bool =
  match actions with
  | [] -> true
  | [action] -> true
  | first_action :: second_action :: remaining_actions ->
         first_action.program_statement.end_pc = second_action.program_statement.start_pc
      && Some? first_action.program_statement.end_pc
      && consecutive_actions_end_and_start_with_same_pc (second_action :: remaining_actions)

let each_action_list_has_consecutive_actions_end_and_start_with_same_pc
  (actions_list: list (list Armada.Action.t))
  : GTot bool =
  for_all_ghost consecutive_actions_end_and_start_with_same_pc actions_list

let actions_start_atomic_block
  (actions: list Armada.Action.t)
  : GTot bool =
  match actions with
  | [] -> false
  | action :: _ -> action.program_statement.starts_atomic_block

let rec actions_end_atomic_block
  (actions: list Armada.Action.t)
  : GTot bool =
  match actions with
  | [] -> false
  | [action] -> action.program_statement.ends_atomic_block || not action.ok
  | first_action :: remaining_actions -> actions_end_atomic_block remaining_actions

let do_actions_start_and_end_atomic_block
  (actions: list Armada.Action.t)
  : GTot (bool * bool) =
  (actions_start_atomic_block actions, actions_end_atomic_block actions)

let rec steps_computation_implies_start_and_end_atomic_block
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires Some? (steps_computation_generic armada_semantics actor starts_atomic_block ends_atomic_block
                             steps s))
          (ensures  (let actions = map_ghost armada_step_to_action steps in
                       actions_start_atomic_block actions = starts_atomic_block
                     /\ actions_end_atomic_block actions = ends_atomic_block))
          (decreases steps) =
  match steps with
  | [] -> ()
  | [last_step] -> ()
  | first_step :: remaining_steps ->
      (match step_computation_generic armada_semantics actor starts_atomic_block false first_step s with
       | Some s' ->
          steps_computation_implies_start_and_end_atomic_block actor false ends_atomic_block
            remaining_steps s')
