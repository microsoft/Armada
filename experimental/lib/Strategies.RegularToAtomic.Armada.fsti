module Strategies.RegularToAtomic.Armada

open Armada.Action
open Armada.Base
open Armada.Program
open Armada.Statement
open Armada.Thread
open Armada.Type
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Map
open Spec.Ubool
open Strategies.Atomic
open Strategies.PCIndices
open Strategies.RegularToAtomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List
open Util.Nth
open Util.Range

type armada_successor_info_t = {
  action_index: nat;
  path_index: nat;
}

type armada_atomic_path_info_t = {
  path: list nat;
  atomic_action_index_or_successors: either nat (list armada_successor_info_t);
}

let armada_is_breaking_optional_pc
  (pc_index_breaking: array_t bool)
  (optional_pc_index: option nat)
  : GTot bool =
  match optional_pc_index with
  | Some pc_index -> if pc_index < array_len pc_index_breaking then array_index pc_index_breaking pc_index else true
  | None -> true

let armada_pc_breaking_correct_specific
  (pc_index_breaking: array_t bool)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  let ps = action.program_statement in
     armada_is_breaking_optional_pc pc_index_breaking pc_indices.start_pc_index = ps.starts_atomic_block
  && armada_is_breaking_optional_pc pc_index_breaking pc_indices.end_pc_index = ps.ends_atomic_block
  && (implies (None? ps.end_pc) (armada_is_breaking_optional_pc pc_index_breaking pc_indices.start_pc_index))

let armada_pc_breaking_correct
  (actions_array: array_t Armada.Action.t)
  (pc_indices_array: array_t statement_pc_indices_t)
  (pc_index_breaking: array_t bool)
  : GTot bool =
  arrays_correspond (armada_pc_breaking_correct_specific pc_index_breaking) actions_array pc_indices_array

let armada_created_threads_initially_breaking_specific
  (pc_index_breaking: array_t bool)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  armada_is_breaking_optional_pc pc_index_breaking pc_indices.create_thread_initial_pc_index

let armada_created_threads_initially_breaking
  (pc_index_breaking: array_t bool)
  (pc_indices_array: array_t statement_pc_indices_t)
  : GTot bool =
  for_all_array (armada_created_threads_initially_breaking_specific pc_index_breaking) pc_indices_array

let armada_actions_starting_at_pc_correct_specific
  (action_indices_starting_at_no_pc: list nat)
  (action_indices_starting_at_pc_index: array_t (list nat))
  (action_index: nat)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
  match pc_indices.start_pc_index with
  | None -> list_contains action_index action_indices_starting_at_no_pc
  | Some pc_index ->
         pc_index < array_len action_indices_starting_at_pc_index
      && list_contains action_index (array_index action_indices_starting_at_pc_index pc_index)

let armada_actions_starting_at_pc_correct
  (action_indices_starting_at_no_pc: list nat)
  (action_indices_starting_at_pc_index: array_t (list nat))
  (pc_indices_array: array_t statement_pc_indices_t)
  : GTot bool =
  for_all_array_enumerated
    (armada_actions_starting_at_pc_correct_specific action_indices_starting_at_no_pc
      action_indices_starting_at_pc_index)
    pc_indices_array

let armada_singleton_path_matches_path_infos_specific
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  (action_index: nat)
  (optional_path_index: option nat)
  : GTot bool =
  match optional_path_index with
  | Some singleton_path_index ->
         singleton_path_index < array_len atomic_path_infos
      && (array_index atomic_path_infos singleton_path_index).path = [action_index]
  | None -> true

let armada_singleton_path_indices_match_path_infos
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  (singleton_path_indices: array_t (option nat))
  : GTot bool =
  for_all_array_enumerated
    (armada_singleton_path_matches_path_infos_specific atomic_path_infos)
    singleton_path_indices

let armada_path_successor_matches_path_info
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  (atomic_path_info: armada_atomic_path_info_t)
  (successor: armada_successor_info_t)
  : GTot bool =
     successor.path_index < array_len atomic_path_infos
  && (array_index atomic_path_infos successor.path_index).path
     = (append atomic_path_info.path [successor.action_index])

let armada_path_successors_match_path_infos_specific
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot bool =
  match atomic_path_info.atomic_action_index_or_successors with
  | Inl atomic_action_index -> true
  | Inr successors ->
    for_all_ghost (armada_path_successor_matches_path_info atomic_path_infos atomic_path_info) successors

let armada_path_successors_match_path_infos
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  : GTot bool =
  for_all_array (armada_path_successors_match_path_infos_specific atomic_path_infos) atomic_path_infos

let armada_is_breaking_action
  (pc_index_breaking: array_t bool)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : GTot bool =
    not action.ok
  || armada_is_breaking_optional_pc pc_index_breaking pc_indices.end_pc_index
  || (match action.program_statement.statement with
     | AssertFalseStatement _
     | TerminateProcessStatement _
     | TerminateThreadStatement _
     | MethodCallStatement _ _ _ _ _ true -> true
     | _ -> false)

let armada_path_breaking_correct_specific
  (pc_index_breaking: array_t bool)
  (actions_array: array_t Armada.Action.t)
  (pc_indices_array: array_t statement_pc_indices_t)
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot bool =
     Cons? atomic_path_info.path
  && (let action_index = last atomic_path_info.path in
         action_index < array_len actions_array
      && action_index < array_len pc_indices_array
      && (Inl? atomic_path_info.atomic_action_index_or_successors) =
           armada_is_breaking_action pc_index_breaking (array_index actions_array action_index)
             (array_index pc_indices_array action_index))

let armada_path_breaking_correct
  (pc_index_breaking: array_t bool)
  (actions_array: array_t Armada.Action.t)
  (pc_indices_array: array_t statement_pc_indices_t)
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  : GTot bool =
  for_all_array (armada_path_breaking_correct_specific pc_index_breaking actions_array pc_indices_array)
    atomic_path_infos

let armada_path_entry_correct
  (actions_array: array_t Armada.Action.t)
  (action_index: nat)
  (action: Armada.Action.t)
  : GTot ubool =
  array_nth actions_array action_index == Some action

let armada_path_atomic_index_correct
  (lprog_actions_array: array_t Armada.Action.t)
  (hprog_actions_array: array_t (list Armada.Action.t))
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot ubool =
  match atomic_path_info.atomic_action_index_or_successors with
  | Inl atomic_action_index ->
         atomic_action_index < array_len hprog_actions_array
      /\ lists_correspond_ubool (armada_path_entry_correct lprog_actions_array) atomic_path_info.path
           (array_index hprog_actions_array atomic_action_index)
  | Inr successors -> true

let armada_path_atomic_indices_correct
  (lprog_actions_array: array_t Armada.Action.t)
  (hprog_actions_array: array_t (list Armada.Action.t))
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  : GTot ubool =
  for_all_array_ubool (armada_path_atomic_index_correct lprog_actions_array hprog_actions_array) atomic_path_infos

let armada_path_actions_in_lprog_specific
  (num_actions: nat)
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot bool =
  for_all_ghost (fun (action_index: nat) -> action_index < num_actions) atomic_path_info.path

let armada_path_actions_in_lprog
  (num_actions: nat)
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  : GTot bool =
  for_all_array (armada_path_actions_in_lprog_specific num_actions) atomic_path_infos

let singleton_path_indices_reflect_action
  (pc_index_breaking: array_t bool)
  (pc_indices: statement_pc_indices_t)
  (singleton_path_index: option nat)
  : GTot bool =
  implies
    (armada_is_breaking_optional_pc pc_index_breaking pc_indices.start_pc_index)
    (Some? singleton_path_index)

let singleton_path_indices_complete
  (pc_index_breaking: array_t bool)
  (pc_indices_array: array_t statement_pc_indices_t)
  (singleton_path_indices: array_t (option nat))
  : GTot bool =
  arrays_correspond (singleton_path_indices_reflect_action pc_index_breaking) pc_indices_array singleton_path_indices

let armada_successors_include_action_index
  (successors: list armada_successor_info_t)
  (action_index: nat)
  : GTot bool =
  exists_ghost (fun successor -> successor.action_index = action_index) successors

let armada_path_successors_complete_specific
  (action_indices_starting_at_pc_index: array_t (list nat))
  (pc_indices_array: array_t statement_pc_indices_t)
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot bool =
  match atomic_path_info.atomic_action_index_or_successors with
  | Inl atomic_action_index -> true
  | Inr successors ->
         length atomic_path_info.path > 0
      && (let final_action_index = last atomic_path_info.path in
             final_action_index < array_len pc_indices_array
          && (match (array_index pc_indices_array final_action_index).end_pc_index with
              | None -> false
              | Some end_pc_index ->
                     end_pc_index < array_len action_indices_starting_at_pc_index
                  && (let action_indices = array_index action_indices_starting_at_pc_index end_pc_index in
                      for_all_ghost (armada_successors_include_action_index successors) action_indices)))

let armada_path_successors_complete
  (action_indices_starting_at_pc_index: array_t (list nat))
  (pc_indices_array: array_t statement_pc_indices_t)
  (atomic_path_infos: array_t armada_atomic_path_info_t)
  : GTot bool =
  for_all_array (armada_path_successors_complete_specific action_indices_starting_at_pc_index pc_indices_array)
    atomic_path_infos

let armada_main_start_pc_breaking
  (main_start_pc: pc_t)
  (lpcs: array_t pc_t)
  (lprog_main_start_pc_index: nat)
  (pc_index_breaking: array_t bool)
  : GTot bool =
     array_nth lpcs lprog_main_start_pc_index = Some main_start_pc
  && lprog_main_start_pc_index < array_len pc_index_breaking
  && array_index pc_index_breaking lprog_main_start_pc_index = true

noeq type armada_refines_atomic_witness_t = {
  pc_index_breaking: array_t bool;
  pc_indices_array: array_t statement_pc_indices_t;
  action_indices_starting_at_no_pc: list nat;
  action_indices_starting_at_pc_index: array_t (list nat);
  atomic_path_infos: array_t armada_atomic_path_info_t;
  singleton_path_indices: array_t (option nat);
  lpcs: array_t pc_t;
  lprog_main_start_pc_index: nat;
  lprog_actions_array: array_t Armada.Action.t;
  hprog_actions_array: array_t (list Armada.Action.t);
}

let armada_refines_atomic_witness_valid
  (lprog: Armada.Program.t)
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (aw: armada_refines_atomic_witness_t)
  : GTot ubool =
     armada_actions_starting_at_pc_correct aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index
       aw.pc_indices_array
  /\ armada_singleton_path_indices_match_path_infos aw.atomic_path_infos aw.singleton_path_indices
  /\ armada_path_successors_match_path_infos aw.atomic_path_infos
  /\ array_len aw.pc_index_breaking = array_len aw.lpcs
  /\ armada_path_breaking_correct aw.pc_index_breaking aw.lprog_actions_array aw.pc_indices_array aw.atomic_path_infos
  /\ armada_path_atomic_indices_correct aw.lprog_actions_array aw.hprog_actions_array aw.atomic_path_infos
  /\ armada_path_actions_in_lprog (array_len aw.lprog_actions_array) aw.atomic_path_infos
  /\ singleton_path_indices_complete aw.pc_index_breaking aw.pc_indices_array aw.singleton_path_indices
  /\ armada_path_successors_complete aw.action_indices_starting_at_pc_index aw.pc_indices_array aw.atomic_path_infos
  /\ armada_created_threads_initially_breaking aw.pc_index_breaking aw.pc_indices_array
  /\ armada_pc_breaking_correct aw.lprog_actions_array aw.pc_indices_array aw.pc_index_breaking
  /\ armada_main_start_pc_breaking lprog.main_start_pc aw.lpcs aw.lprog_main_start_pc_index aw.pc_index_breaking
  /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array
  /\ array_elements_unique_ubool aw.lpcs

val armada_refines_atomic_witness_valid_implies_refinement
  (lprog: Armada.Program.t)
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_refines_atomic_witness_valid lprog hprog aw
                    /\ hprog.init_f == init_program lprog
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements)
                    /\ aw.hprog_actions_array == list_to_array hprog.actions)
          (ensures  (spec_refines_spec
                      (program_to_spec lprog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hprog)
                      eq2))
