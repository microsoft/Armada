module Strategies.Breaking

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

let action_breaks
  (is_breaking_pc: pc_t -> GTot bool)
  (action: Armada.Action.t)
  : GTot bool =
    (not action.ok)
  || (match program_statement_to_ending_thread_state action.program_statement with
     | ThreadStateRunning -> false
     | ThreadStateAtPC pc -> is_breaking_pc pc
     | ThreadStateNotRunning status -> true
     | ThreadStateProcessStopped stop_reason -> true)

let action_only_creates_breaking_threads
  (is_breaking_pc: pc_t -> GTot bool)
  (action: Armada.Action.t)
  : GTot bool =
  match action.program_statement.statement with
  | CreateThreadStatement _ initial_pc _ _ _ _ _ -> is_breaking_pc initial_pc
  | _ -> true

let rec actions_end_with_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actions: list Armada.Action.t)
  : GTot bool =
  match actions with
  | [] -> false
  | [last_action] ->
         action_only_creates_breaking_threads is_breaking_pc last_action
      && action_breaks is_breaking_pc last_action
  | first_action :: remaining_actions ->
         action_only_creates_breaking_threads is_breaking_pc first_action
      && actions_end_with_all_threads_breaking is_breaking_pc remaining_actions

let actions_are_propagate (actions: list Armada.Action.t) : GTot bool =
  match actions with
  | [action] ->
      (let ps = action.program_statement in
       match ps.statement with
       | PropagateWriteMessageStatement -> None? ps.start_pc && None? ps.end_pc
       | _ -> false)
  | _ -> false

let actions_maintain_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actions: list Armada.Action.t)
  : GTot bool =
    actions_end_with_all_threads_breaking is_breaking_pc actions
  || actions_are_propagate actions

let each_action_list_maintains_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actions_list: list (list Armada.Action.t))
  : GTot bool =
  for_all_ghost (actions_maintain_all_threads_breaking is_breaking_pc) actions_list

let efficient_is_breaking_pc
  (is_breaking_pc: array_t bool)
  (pc: nat)
  : GTot bool =
  match array_nth is_breaking_pc pc with
  | Some b -> b
  | None -> false

let efficient_action_breaks
  (is_breaking_pc: array_t bool)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
    (not action.ok)
  || (match efficient_program_statement_to_ending_thread_state action.program_statement pc_indices with
     | EfficientThreadStateRunning -> false
     | EfficientThreadStateAtPC pc -> efficient_is_breaking_pc is_breaking_pc pc
     | EfficientThreadStateNotRunning status -> true
     | EfficientThreadStateProcessStopped stop_reason -> true)

let efficient_action_only_creates_breaking_threads
  (is_breaking_pc: array_t bool)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  match pc_indices.create_thread_initial_pc_index with
  | Some pc -> efficient_is_breaking_pc is_breaking_pc pc
  | _ -> true

let rec efficient_actions_end_with_all_threads_breaking
  (is_breaking_pc: array_t bool)
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : GTot bool =
  match actions, pc_indices_list with
  | [], [] -> false
  | [last_action], [last_pc_indices] ->
         efficient_action_only_creates_breaking_threads is_breaking_pc last_pc_indices
      && efficient_action_breaks is_breaking_pc last_action last_pc_indices
  | first_action :: remaining_actions, first_pc_indices :: remaining_pc_indices ->
         efficient_action_only_creates_breaking_threads is_breaking_pc first_pc_indices
      && efficient_actions_end_with_all_threads_breaking is_breaking_pc remaining_actions remaining_pc_indices
  | _, _ -> false

let efficient_actions_maintain_all_threads_breaking
  (is_breaking_pc: array_t bool)
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : GTot bool =
    efficient_actions_end_with_all_threads_breaking is_breaking_pc actions pc_indices_list
  || actions_are_propagate actions

let efficient_each_action_list_maintains_all_threads_breaking
  (is_breaking_pc: array_t bool)
  (actions_array: array_t (list Armada.Action.t))
  (pc_indices_array: array_t (list statement_pc_indices_t))
  : GTot bool =
  arrays_correspond (efficient_actions_maintain_all_threads_breaking is_breaking_pc) actions_array pc_indices_array
