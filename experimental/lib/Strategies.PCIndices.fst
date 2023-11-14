module Strategies.PCIndices

open Armada.Action
open Armada.Base
open Armada.Statement
open Spec.Ubool
open Util.ImmutableArray
open Util.List
open Util.Relation

type statement_pc_indices_t = {
  start_pc_index: option nat;
  end_pc_index: option nat;
  create_thread_initial_pc_index: option nat;
  method_call_return_pc_index: option nat;
}

let pc_matches_pc_index
  (pcs: array_t pc_t)
  (pc: pc_t)
  (n: nat)
  : GTot bool =
  n < array_len pcs && pc = array_index pcs n

let optional_pc_matches_optional_pc_index
  (pcs: array_t pc_t)
  (optional_pc: option pc_t)
  (optional_index: option nat)
  : GTot bool =
  match optional_pc, optional_index with
  | None, None -> true
  | Some pc, Some n -> pc_matches_pc_index pcs pc n
  | _, _ -> false

let program_statement_corresponds_to_statement_pc_indices
  (pcs: array_t pc_t)
  (ps: program_statement_t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
     optional_pc_matches_optional_pc_index pcs ps.start_pc pc_indices.start_pc_index
  && optional_pc_matches_optional_pc_index pcs ps.end_pc pc_indices.end_pc_index
  && (match ps.statement with
      | CreateThreadStatement _ initial_pc _ _ _ _ _ ->
          optional_pc_matches_optional_pc_index pcs (Some initial_pc) pc_indices.create_thread_initial_pc_index
      | _ -> None? pc_indices.create_thread_initial_pc_index)
  && (match ps.statement with
      | MethodCallStatement _ return_pc _ _ _ _ ->
          optional_pc_matches_optional_pc_index pcs (Some return_pc) pc_indices.method_call_return_pc_index
      | _ -> None? pc_indices.method_call_return_pc_index)

let action_corresponds_to_statement_pc_indices
  (pcs: array_t pc_t)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  program_statement_corresponds_to_statement_pc_indices pcs action.program_statement pc_indices

let actions_correspond_to_statement_pc_indices
  (pcs: array_t pc_t)
  (actions: array_t Armada.Action.t)
  (pc_indices_array: array_t statement_pc_indices_t)
  : GTot bool =
  arrays_correspond (action_corresponds_to_statement_pc_indices pcs) actions pc_indices_array

let action_list_corresponds_to_statement_pc_indices_list
  (pcs: array_t pc_t)
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : GTot bool =
  lists_correspond (action_corresponds_to_statement_pc_indices pcs) actions pc_indices_list

let actions_array_corresponds_to_statement_pc_indices_array
  (pcs: array_t pc_t)
  (actions: array_t (list Armada.Action.t))
  (pc_indices_array: array_t (list statement_pc_indices_t))
  : GTot bool =
  arrays_correspond (action_list_corresponds_to_statement_pc_indices_list pcs) actions pc_indices_array
