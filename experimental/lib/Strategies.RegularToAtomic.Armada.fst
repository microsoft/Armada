module Strategies.RegularToAtomic.Armada

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Step
open Armada.Transition
open Strategies.ArmadaStatement.Status
open Strategies.RegularToAtomic
open Strategies.RegularToAtomic.Armada.Helper
open Strategies.Semantics.Armada
open Util.Behavior
open Util.List
open Util.Logic
open Util.Nth

let default_action: Armada.Action.t = {
  ok = true;
  program_statement = {
    start_pc = None;
    end_pc = None;
    starts_atomic_block = true;
    ends_atomic_block = true;
    statement = PropagateWriteMessageStatement;
  }
}

let armada_pc_index_and_pc_breaking
  (lpcs: array_t pc_t)
  (pc_index_breaking: array_t bool)
  (pc: pc_t)
  (pc_index: nat)
  : GTot bool =
     pc_index < array_len lpcs
  && pc_index < array_len pc_index_breaking
  && array_index lpcs pc_index = pc
  && array_index pc_index_breaking pc_index = true

let armada_pc_index_breaking_to_pc_breaking
  (lpcs: array_t pc_t)
  (pc_index_breaking: array_t bool)
  (pc: pc_t)
  : GTot bool =
  u2b (exists (pc_index: nat). armada_pc_index_and_pc_breaking lpcs pc_index_breaking pc pc_index)

let select_action_from_array
  (actions_array: array_t Armada.Action.t)
  (i: nat)
  : GTot Armada.Action.t =
  if i < array_len actions_array then array_index actions_array i else default_action

let armada_successor_info_to_successor_info
  (lprog_actions_array: array_t Armada.Action.t)
  (successor: armada_successor_info_t)
  : GTot (successor_info_t armada_semantics) =
  {
    action = select_action_from_array lprog_actions_array successor.action_index;
    path_index = successor.path_index;
  }

let rec singleton_path_indices_offset_to_starting_successors
  (lprog_actions_array: array_t Armada.Action.t)
  (singleton_path_indices: array_t (option nat))
  (offset: nat)
  : GTot (list (successor_info_t armada_semantics))
    (decreases array_len singleton_path_indices - offset) =
  if offset >= array_len singleton_path_indices || offset >= array_len lprog_actions_array then
    []
  else
    let remaining_starting_successors =
      singleton_path_indices_offset_to_starting_successors lprog_actions_array singleton_path_indices (offset + 1) in
    match array_index singleton_path_indices offset with
    | None -> remaining_starting_successors
    | Some path_index ->
        let armada_successor: armada_successor_info_t = { action_index = offset; path_index = path_index; } in
        let starting_successor = armada_successor_info_to_successor_info lprog_actions_array armada_successor in
        starting_successor :: remaining_starting_successors

let singleton_path_indices_to_starting_successors
  (lprog_actions_array: array_t Armada.Action.t)
  (singleton_path_indices: array_t (option nat))
  : GTot (list (successor_info_t armada_semantics)) =
  singleton_path_indices_offset_to_starting_successors lprog_actions_array singleton_path_indices 0

let armada_actions_starting_at_pc_to_actions_starting_at_pc
  (lprog_actions_array: array_t Armada.Action.t)
  (lpcs: array_t pc_t)
  (action_indices_starting_at_no_pc: list nat)
  (action_indices_starting_at_pc_index: array_t (list nat))
  (optional_pc: option pc_t)
  : GTot (list Armada.Action.t) =
  match optional_pc with
  | None -> map_ghost (select_action_from_array lprog_actions_array) action_indices_starting_at_no_pc
  | Some pc ->
      (match find_in_array lpcs pc with
       | None -> []
       | Some idx ->
          (match array_nth action_indices_starting_at_pc_index idx with
           | None -> []
           | Some action_indices -> map_ghost (select_action_from_array lprog_actions_array) action_indices))

let armada_atomic_path_info_to_atomic_path_info
  (lprog_actions_array: array_t Armada.Action.t)
  (atomic_path_info: armada_atomic_path_info_t)
  : GTot (atomic_path_info_t armada_semantics) =
  let path = map_ghost (select_action_from_array lprog_actions_array) atomic_path_info.path in
  match atomic_path_info.atomic_action_index_or_successors with
  | Inl atomic_action_index ->
     {
       path = path;
       breaking = true;
       atomic_action_index = atomic_action_index;
       successors = [];
     }
  | Inr successors ->
     {
       path = path;
       breaking = false;
       atomic_action_index = 0;
       successors = map_ghost (armada_successor_info_to_successor_info lprog_actions_array) successors;
     }

#push-options "--z3rlimit 30"

let actions_starting_at_pc_correct_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_actions_starting_at_pc_correct aw.action_indices_starting_at_no_pc
                        aw.action_indices_starting_at_pc_index aw.pc_indices_array
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements)
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array
                    /\ array_elements_unique_ubool aw.lpcs)
          (ensures  (let actions_starting_at_pc =
                       armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
                         aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
                     actions_starting_at_pc_correct lprog actions_starting_at_pc)) =
  let actions_starting_at_pc =
    armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
      aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
  introduce forall action. contains_ubool action (all_actions lprog.program_statements) ==>
                      contains_ubool action (actions_starting_at_pc action.program_statement.start_pc)
  with introduce _ ==> _
  with _. (
    let action_index = contains_ubool_to_index action (all_actions lprog.program_statements) in
    assert (array_index aw.lprog_actions_array action_index == action);
    let pc_indices = array_index aw.pc_indices_array action_index in
    assert (armada_actions_starting_at_pc_correct_specific aw.action_indices_starting_at_no_pc
              aw.action_indices_starting_at_pc_index action_index pc_indices);
    assert (action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices);
    match pc_indices.start_pc_index with
    | None ->
        contains_equivalent_to_contains_ubool action_index aw.action_indices_starting_at_no_pc;
        map_ghost_contains_ubool (select_action_from_array aw.lprog_actions_array)
          aw.action_indices_starting_at_no_pc action_index
    | Some pc_index ->
       let start_pc = Some?.v action.program_statement.start_pc in
       array_elements_unique_ubool_implication aw.lpcs;
       assert (find_in_array aw.lpcs start_pc == Some pc_index);
       contains_equivalent_to_contains_ubool action_index
         (array_index aw.action_indices_starting_at_pc_index pc_index);
       map_ghost_contains_ubool (select_action_from_array aw.lprog_actions_array)
         (array_index aw.action_indices_starting_at_pc_index pc_index) action_index
  )

#pop-options

let rec starting_successor_to_singleton_path_index
  (lprog_actions_array: array_t Armada.Action.t)
  (singleton_path_indices: array_t (option nat))
  (offset: nat)
  (successor: successor_info_t armada_semantics{
    contains_ubool successor (singleton_path_indices_offset_to_starting_successors
                               lprog_actions_array singleton_path_indices offset)})
  : GTot (action_index: nat{   action_index < array_len lprog_actions_array
                           /\ action_index < array_len singleton_path_indices
                           /\ successor.action == array_index lprog_actions_array action_index
                           /\ array_index singleton_path_indices action_index = Some successor.path_index})
    (decreases array_len singleton_path_indices - offset) =
  if offset >= array_len singleton_path_indices || offset >= array_len lprog_actions_array then
    false_elim ()
  else
    match array_index singleton_path_indices offset with
    | None -> starting_successor_to_singleton_path_index lprog_actions_array singleton_path_indices (offset + 1)
               successor
    | Some path_index ->
        let armada_successor: armada_successor_info_t = { action_index = offset; path_index = path_index; } in
        let starting_successor = armada_successor_info_to_successor_info lprog_actions_array armada_successor in
        if eqb starting_successor successor then
          offset
        else
          starting_successor_to_singleton_path_index lprog_actions_array singleton_path_indices (offset + 1)
             successor

let starting_successors_match_path_infos_lemma
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_singleton_path_indices_match_path_infos aw.atomic_path_infos
                        aw.singleton_path_indices)
          (ensures  (let starting_successors =
                       singleton_path_indices_to_starting_successors aw.lprog_actions_array
                         aw.singleton_path_indices in
                     let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     starting_successors_match_path_infos starting_successors atomic_path_infos)) =
  let starting_successors = singleton_path_indices_to_starting_successors aw.lprog_actions_array
                              aw.singleton_path_indices in
  let atomic_path_infos = map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                            (array_to_list aw.atomic_path_infos) in
  introduce forall successor. contains_ubool successor starting_successors ==>
                         starting_successors_match_path_infos_specific starting_successors atomic_path_infos successor
  with introduce _ ==> _
  with _. (
    let action_index = starting_successor_to_singleton_path_index aw.lprog_actions_array aw.singleton_path_indices 0
                        successor in
    assert (armada_singleton_path_matches_path_infos_specific aw.atomic_path_infos action_index
             (Some successor.path_index));
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) successor.path_index
  )

let path_successors_match_path_infos_lemma
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires armada_path_successors_match_path_infos aw.atomic_path_infos)
          (ensures  (let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     path_successors_match_path_infos atomic_path_infos)) =
  let atomic_path_infos = map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                           (array_to_list aw.atomic_path_infos) in
  introduce forall atomic_path_info. contains_ubool atomic_path_info atomic_path_infos ==>
                                path_successors_match_path_infos_specific atomic_path_infos atomic_path_info
  with introduce contains_ubool atomic_path_info atomic_path_infos ==>
                   path_successors_match_path_infos_specific atomic_path_infos atomic_path_info
  with _. (
    let path_index = contains_ubool_to_index atomic_path_info atomic_path_infos in
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) path_index;
    let armada_atomic_path_info = array_index aw.atomic_path_infos path_index in
    assert (armada_path_successors_match_path_infos_specific aw.atomic_path_infos armada_atomic_path_info);
    introduce forall successor. contains_ubool successor atomic_path_info.successors ==>
                           path_successor_matches_path_info atomic_path_infos atomic_path_info successor
    with introduce _ ==> _
    with _. (
      let armada_successor = reverse_map_element_of_map_ghost
                               (armada_successor_info_to_successor_info aw.lprog_actions_array)
                               (Inr?.v armada_atomic_path_info.atomic_action_index_or_successors) successor in
      assert (armada_path_successor_matches_path_info aw.atomic_path_infos armada_atomic_path_info armada_successor);
      assert (successor == armada_successor_info_to_successor_info aw.lprog_actions_array armada_successor);
      map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
        (array_to_list aw.atomic_path_infos) successor.path_index;
      append_commutes_with_map (select_action_from_array aw.lprog_actions_array) armada_atomic_path_info.path
        [armada_successor.action_index]
    )
  )

let armada_is_breaking_action_implies_is_breaking_armada_action
  (aw: armada_refines_atomic_witness_t)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires   action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices
                    /\ array_elements_unique_ubool aw.lpcs
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs)
          (ensures  (let pc_breaking =
                       armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     armada_is_breaking_action aw.pc_index_breaking action pc_indices =
                       is_breaking_armada_action pc_breaking action)) =
  array_elements_unique_ubool_implication aw.lpcs

let pc_matches_pc_index_implies_pc_breaking_matches
  (aw: armada_refines_atomic_witness_t)
  (pc: pc_t)
  (pc_index: nat)
  : Lemma (requires   pc_matches_pc_index aw.lpcs pc pc_index
                    /\ armada_pc_breaking_correct aw.lprog_actions_array aw.pc_indices_array aw.pc_index_breaking
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs
                    /\ array_elements_unique_ubool aw.lpcs)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     pc_breaking pc = array_index aw.pc_index_breaking pc_index)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  array_elements_unique_ubool_implication aw.lpcs

let optional_pc_matches_optional_pc_index_implies_is_breaking_optional_pc_matches
  (aw: armada_refines_atomic_witness_t)
  (optional_pc: option pc_t)
  (optional_pc_index: option nat)
  : Lemma (requires   optional_pc_matches_optional_pc_index aw.lpcs optional_pc optional_pc_index
                    /\ armada_pc_breaking_correct aw.lprog_actions_array aw.pc_indices_array aw.pc_index_breaking
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs
                    /\ array_elements_unique_ubool aw.lpcs)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     is_breaking_optional_pc pc_breaking optional_pc =
                       armada_is_breaking_optional_pc aw.pc_index_breaking optional_pc_index)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  array_elements_unique_ubool_implication aw.lpcs;
  match optional_pc, optional_pc_index with
  | None, None -> ()
  | Some pc, Some pc_index ->
      pc_matches_pc_index_implies_pc_breaking_matches aw pc pc_index
  | _, _ -> false_elim ()

#push-options "--z3rlimit 20"

let path_breaking_correct_lemma
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_path_breaking_correct aw.pc_index_breaking aw.lprog_actions_array aw.pc_indices_array
                        aw.atomic_path_infos
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array
                    /\ array_elements_unique_ubool aw.lpcs
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     path_breaking_correct pc_breaking atomic_path_infos)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  let atomic_path_infos =
    map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) in
  introduce forall atomic_path_info. contains_ubool atomic_path_info atomic_path_infos ==>
                                path_breaking_correct_specific pc_breaking atomic_path_info
  with introduce _ ==> _
  with _. (
    let path_index = contains_ubool_to_index atomic_path_info atomic_path_infos in
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) path_index;
    let armada_atomic_path_info = array_index aw.atomic_path_infos path_index in
    assert (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array armada_atomic_path_info ==
              atomic_path_info);
    assert (Cons? atomic_path_info.path);
    assert (atomic_path_info.path == map_ghost (select_action_from_array aw.lprog_actions_array)
                                       armada_atomic_path_info.path);
    assert (atomic_path_info.breaking = Inl? armada_atomic_path_info.atomic_action_index_or_successors);
    assert (armada_path_breaking_correct_specific aw.pc_index_breaking aw.lprog_actions_array aw.pc_indices_array
              armada_atomic_path_info);
    let action_index = last armada_atomic_path_info.path in
    assert (atomic_path_info.breaking =
              armada_is_breaking_action aw.pc_index_breaking (array_index aw.lprog_actions_array action_index)
               (array_index aw.pc_indices_array action_index));
    let pc_indices = array_index aw.pc_indices_array action_index in
    let action = array_index aw.lprog_actions_array action_index in
    map_ghost_maps_last (select_action_from_array aw.lprog_actions_array) armada_atomic_path_info.path;
    assert (action == last atomic_path_info.path);
    assert (action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices);
    assert (atomic_path_info.breaking = armada_is_breaking_action aw.pc_index_breaking action pc_indices);
    armada_is_breaking_action_implies_is_breaking_armada_action aw action pc_indices;
    assert (atomic_path_info.breaking = is_breaking_armada_action pc_breaking (last atomic_path_info.path))
  )

let path_atomic_indices_correct_lemma
  (lprog: Armada.Program.t)
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_path_atomic_indices_correct aw.lprog_actions_array aw.hprog_actions_array
                        aw.atomic_path_infos
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements)
                    /\ aw.hprog_actions_array == list_to_array hprog.actions)
          (ensures  (let hprog_actions = hprog.actions in
                     let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     path_atomic_indices_correct hprog_actions atomic_path_infos)) =
  let hprog_actions = hprog.actions in
  let atomic_path_infos =
    map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) in
  introduce forall atomic_path_info. contains_ubool atomic_path_info atomic_path_infos /\ atomic_path_info.breaking ==>
                                  atomic_path_info.atomic_action_index < length hprog_actions
                                /\ atomic_path_info.path == (index hprog_actions atomic_path_info.atomic_action_index)
  with introduce _ ==> _
  with _. (
    let path_index = contains_ubool_to_index atomic_path_info atomic_path_infos in
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) path_index;
    let armada_atomic_path_info = array_index aw.atomic_path_infos path_index in
    assert (armada_path_atomic_index_correct aw.lprog_actions_array aw.hprog_actions_array armada_atomic_path_info);
    let atomic_action_index = Inl?.v armada_atomic_path_info.atomic_action_index_or_successors in
    let atomic_action = array_index aw.hprog_actions_array atomic_action_index in
    assert (lists_correspond_ubool (armada_path_entry_correct aw.lprog_actions_array) armada_atomic_path_info.path
              atomic_action);
    assert (atomic_action == index hprog_actions atomic_path_info.atomic_action_index);
    assert (lists_correspond_ubool (armada_path_entry_correct aw.lprog_actions_array) armada_atomic_path_info.path
              (index hprog_actions atomic_path_info.atomic_action_index));
    lists_correspond_ubool_implies_map_ghost (armada_path_entry_correct aw.lprog_actions_array)
      (select_action_from_array aw.lprog_actions_array) armada_atomic_path_info.path
      (index hprog_actions atomic_path_info.atomic_action_index)
  )

#pop-options

let path_actions_in_lprog_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_path_actions_in_lprog (array_len aw.lprog_actions_array) aw.atomic_path_infos
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements))
          (ensures  (let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     path_actions_in_lprog lprog atomic_path_infos)) =
  let atomic_path_infos =
    map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) in
  introduce forall atomic_path_info. contains_ubool atomic_path_info atomic_path_infos ==>
                                path_actions_in_lprog_specific lprog atomic_path_info
  with introduce contains_ubool atomic_path_info atomic_path_infos ==>
                 path_actions_in_lprog_specific lprog atomic_path_info
  with _. (
    let path_index = contains_ubool_to_index atomic_path_info atomic_path_infos in
    let num_actions = array_len aw.lprog_actions_array in
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) path_index;
    let armada_atomic_path_info = array_index aw.atomic_path_infos path_index in
    assert (armada_path_actions_in_lprog_specific num_actions armada_atomic_path_info);
    assert (for_all_ghost (fun (action_index: nat) -> action_index < num_actions) armada_atomic_path_info.path);
    introduce forall action. contains_ubool action atomic_path_info.path ==>
                        path_action_in_lprog lprog action
    with introduce _ ==> _
    with _. (
      let action_index: nat = reverse_map_element_of_map_ghost (select_action_from_array aw.lprog_actions_array)
                              armada_atomic_path_info.path action in
      index_to_contains_ubool (all_actions lprog.program_statements) action_index;
      all_actions_has_all_actions action lprog.program_statements
    )
  )

let rec singleton_path_index_to_starting_successor
  (lprog_actions_array: array_t Armada.Action.t)
  (singleton_path_indices: array_t (option nat))
  (offset: nat)
  (action_index: nat{   action_index < array_len lprog_actions_array
                    /\ action_index < array_len singleton_path_indices
                    /\ action_index >= offset
                    /\ Some? (array_index singleton_path_indices action_index)})
  : GTot (successor: successor_info_t armada_semantics{
               successor.action == array_index lprog_actions_array action_index
             /\ contains_ubool successor (singleton_path_indices_offset_to_starting_successors
                                           lprog_actions_array singleton_path_indices offset)})
    (decreases array_len singleton_path_indices - offset) =
  if action_index > offset then
    singleton_path_index_to_starting_successor lprog_actions_array singleton_path_indices (offset + 1)
      action_index
  else
    match array_index singleton_path_indices offset with
    | None -> false_elim ()
    | Some path_index ->
        let action = array_index lprog_actions_array action_index in
        let starting_successor = { action = action; path_index = path_index; } in
        starting_successor

let starting_successors_complete_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   singleton_path_indices_complete aw.pc_index_breaking aw.pc_indices_array
                        aw.singleton_path_indices
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs
                    /\ array_elements_unique_ubool aw.lpcs
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements))
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     let starting_successors = singleton_path_indices_to_starting_successors aw.lprog_actions_array
                                                 aw.singleton_path_indices in
                     starting_successors_complete lprog pc_breaking starting_successors)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  let starting_successors = singleton_path_indices_to_starting_successors aw.lprog_actions_array
                              aw.singleton_path_indices in
  introduce forall action. contains_ubool action (all_actions lprog.program_statements) ==>
                      starting_successors_reflect_action pc_breaking starting_successors action
  with introduce _ ==> _
  with _. (
    let action_index = contains_ubool_to_index action (all_actions lprog.program_statements) in
    assert (array_index aw.lprog_actions_array action_index == action);
    let pc_indices = array_index aw.pc_indices_array action_index in
    assert (action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices);
    let singleton_path_index = array_index aw.singleton_path_indices action_index in
    assert (singleton_path_indices_reflect_action aw.pc_index_breaking pc_indices singleton_path_index);
    assert (optional_pc_matches_optional_pc_index aw.lpcs action.program_statement.start_pc
              pc_indices.start_pc_index);
    if is_breaking_optional_pc pc_breaking action.program_statement.start_pc then
      match action.program_statement.start_pc with
      | Some pc ->
          assert (armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking pc);
          let pc_index = simpler_indefinite_description (fun (pc_index: nat) ->
                           armada_pc_index_and_pc_breaking aw.lpcs aw.pc_index_breaking pc pc_index) in
          assert (pc_breaking pc);
          array_elements_unique_ubool_implication aw.lpcs;
          assert (pc_index = Some?.v pc_indices.start_pc_index);
          assert (armada_is_breaking_optional_pc aw.pc_index_breaking pc_indices.start_pc_index);
          let singleton_path_index = array_index aw.singleton_path_indices action_index in
          let successor = singleton_path_index_to_starting_successor aw.lprog_actions_array
                            aw.singleton_path_indices 0 action_index in
          assert (contains_ubool successor starting_successors);
          assert (successors_include_action starting_successors action)
      | None ->
          assert (armada_is_breaking_optional_pc aw.pc_index_breaking pc_indices.start_pc_index);
          let singleton_path_index = array_index aw.singleton_path_indices action_index in
          let successor = singleton_path_index_to_starting_successor aw.lprog_actions_array
                            aw.singleton_path_indices 0 action_index in
          assert (contains_ubool successor starting_successors);
          assert (successors_include_action starting_successors action)
    else
      ()
  )

let path_successors_complete_lemma_helper
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  (pc: pc_t)
  (pc_index: nat)
  (armada_successors: list armada_successor_info_t)
  (action: Armada.Action.t)
  : Lemma (requires   array_elements_unique_ubool aw.lpcs
                    /\ pc_matches_pc_index aw.lpcs pc pc_index
                    /\ pc_index < array_len aw.action_indices_starting_at_pc_index
                    /\ (let actions_starting_at_pc =
                         armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
                           aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
                       let action_indices = array_index aw.action_indices_starting_at_pc_index pc_index in
                       let actions = actions_starting_at_pc (Some pc) in
                         for_all_ghost (armada_successors_include_action_index armada_successors)
                           action_indices
                       /\ contains_ubool action actions))
          (ensures (let successors = map_ghost (armada_successor_info_to_successor_info aw.lprog_actions_array)
                                       armada_successors in
                    successors_include_action successors action)) =
  let successors = map_ghost (armada_successor_info_to_successor_info aw.lprog_actions_array) armada_successors in
  let actions_starting_at_pc =
    armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
      aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
  let action_indices = array_index aw.action_indices_starting_at_pc_index pc_index in
  let actions = actions_starting_at_pc (Some pc) in
  match find_in_array aw.lpcs pc with
  | None -> false_elim ()
  | Some idx ->
      array_elements_unique_ubool_implication aw.lpcs;
      assert (idx == pc_index);
      assert (actions == map_ghost (select_action_from_array aw.lprog_actions_array) action_indices);
      let action_index =
        reverse_map_element_of_map_ghost (select_action_from_array aw.lprog_actions_array) action_indices action in
      assert (action == select_action_from_array aw.lprog_actions_array action_index);
      assert (contains_ubool action_index action_indices);
      assert (armada_successors_include_action_index armada_successors action_index);
      let armada_successor =
        exists_ghost_to_witness (fun successor -> successor.action_index = action_index) armada_successors in
      let successor = armada_successor_info_to_successor_info aw.lprog_actions_array armada_successor in
      map_ghost_contains_ubool (armada_successor_info_to_successor_info aw.lprog_actions_array) armada_successors
        armada_successor;
      assert (contains_ubool successor successors);
      assert (action_matches_successor action successor)

#push-options "--z3rlimit 10"

let path_successors_complete_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_path_successors_complete aw.action_indices_starting_at_pc_index aw.pc_indices_array
                        aw.atomic_path_infos
                    /\ array_elements_unique_ubool aw.lpcs
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array)
          (ensures  (let actions_starting_at_pc =
                       armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
                         aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
                     let atomic_path_infos =
                       map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
                         (array_to_list aw.atomic_path_infos) in
                     path_successors_complete actions_starting_at_pc atomic_path_infos)) =
  let actions_starting_at_pc =
    armada_actions_starting_at_pc_to_actions_starting_at_pc aw.lprog_actions_array aw.lpcs
      aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index in
  let atomic_path_infos =
    map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
     (array_to_list aw.atomic_path_infos) in
  introduce forall atomic_path_info. contains_ubool atomic_path_info atomic_path_infos ==>
                                path_successors_complete_specific actions_starting_at_pc atomic_path_info
  with introduce contains_ubool atomic_path_info atomic_path_infos ==>
                 path_successors_complete_specific actions_starting_at_pc atomic_path_info
  with _. (
    let path_index = contains_ubool_to_index atomic_path_info atomic_path_infos in
    map_ghost_maps_index (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos) path_index;
    let armada_atomic_path_info = array_index aw.atomic_path_infos path_index in
    assert (armada_path_successors_complete_specific aw.action_indices_starting_at_pc_index aw.pc_indices_array
              armada_atomic_path_info);
    assert (atomic_path_info == armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array
              armada_atomic_path_info);
    if not atomic_path_info.breaking then (
       let final_action_index = last armada_atomic_path_info.path in
       let final_pc_indices = array_index aw.pc_indices_array final_action_index in
       let end_pc_index = Some?.v final_pc_indices.end_pc_index in
       let action_indices = array_index aw.action_indices_starting_at_pc_index end_pc_index in
       let final_action = array_index aw.lprog_actions_array final_action_index in
       assert (action_corresponds_to_statement_pc_indices aw.lpcs final_action final_pc_indices);
       map_ghost_maps_last (select_action_from_array aw.lprog_actions_array) armada_atomic_path_info.path;
       assert (final_action == last atomic_path_info.path);
       let end_pc = Some?.v final_action.program_statement.end_pc in
       let actions = actions_starting_at_pc (final_action.program_statement.end_pc) in
       introduce forall action. contains_ubool action actions ==>
                           successors_include_action atomic_path_info.successors action
       with introduce _ ==> _
       with _. (
         let successors = Inr?.v armada_atomic_path_info.atomic_action_index_or_successors in
         path_successors_complete_lemma_helper lprog aw end_pc end_pc_index successors action
       )
    )
    else
      ()
  )

let created_threads_initially_breaking_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_created_threads_initially_breaking aw.pc_index_breaking aw.pc_indices_array
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements)
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     created_threads_initially_breaking lprog pc_breaking)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  introduce forall ps. contains_ubool ps lprog.program_statements ==>
                  created_threads_initially_breaking_specific pc_breaking ps
  with introduce _ ==> _
  with _. (
    match ps.statement with
    | CreateThreadStatement _ initial_pc _ _ _ _ _ ->
        let action = { ok = true; program_statement = ps; } in
        all_actions_has_all_actions action lprog.program_statements;
        let action_index = contains_ubool_to_index action (all_actions lprog.program_statements) in
        assert (action == array_index aw.lprog_actions_array action_index);
        let pc_indices = array_index aw.pc_indices_array action_index in
        assert (armada_created_threads_initially_breaking_specific aw.pc_index_breaking pc_indices);
        assert (action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices);
        assert (pc_breaking initial_pc)
    | _ -> ()
  )

#pop-options

let pc_breaking_correct_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires   armada_pc_breaking_correct aw.lprog_actions_array aw.pc_indices_array aw.pc_index_breaking
                    /\ aw.lprog_actions_array == list_to_array (all_actions lprog.program_statements)
                    /\ array_len aw.pc_index_breaking = array_len aw.lpcs
                    /\ array_elements_unique_ubool aw.lpcs
                    /\ actions_correspond_to_statement_pc_indices aw.lpcs aw.lprog_actions_array aw.pc_indices_array)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     pc_breaking_correct lprog pc_breaking)) =
  let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
  introduce forall ps. contains_ubool ps lprog.program_statements ==> pc_breaking_correct_specific pc_breaking ps
  with introduce _ ==> _
  with _. (
    let action = { ok = true; program_statement = ps; } in
    all_actions_has_all_actions action lprog.program_statements;
    let action_index = contains_ubool_to_index action (all_actions lprog.program_statements) in
    assert (action == array_index aw.lprog_actions_array action_index);
    let pc_indices = array_index aw.pc_indices_array action_index in
    assert (armada_pc_breaking_correct_specific aw.pc_index_breaking action pc_indices);
    assert (action_corresponds_to_statement_pc_indices aw.lpcs action pc_indices);
    optional_pc_matches_optional_pc_index_implies_is_breaking_optional_pc_matches aw ps.start_pc
      pc_indices.start_pc_index;
    optional_pc_matches_optional_pc_index_implies_is_breaking_optional_pc_matches aw ps.end_pc
      pc_indices.end_pc_index
  )

let main_start_pc_breaking_lemma
  (lprog: Armada.Program.t)
  (aw: armada_refines_atomic_witness_t)
  : Lemma (requires armada_main_start_pc_breaking lprog.main_start_pc aw.lpcs aw.lprog_main_start_pc_index
                      aw.pc_index_breaking)
          (ensures  (let pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking in
                     pc_breaking lprog.main_start_pc)) =
  ()

let armada_refines_atomic_witness_valid_implies_refinement
  (lprog: Armada.Program.t)
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (aw: armada_refines_atomic_witness_t)
  (* see .fsti file for spec *) =
  let aa: armada_refines_atomic_relation_t = {
    lprog = lprog;
    hprog = hprog;
    pc_breaking = armada_pc_index_breaking_to_pc_breaking aw.lpcs aw.pc_index_breaking;
    actions_starting_at_pc = armada_actions_starting_at_pc_to_actions_starting_at_pc
      aw.lprog_actions_array aw.lpcs aw.action_indices_starting_at_no_pc aw.action_indices_starting_at_pc_index;
    starting_successors = singleton_path_indices_to_starting_successors aw.lprog_actions_array
      aw.singleton_path_indices;
    atomic_path_infos = map_ghost (armada_atomic_path_info_to_atomic_path_info aw.lprog_actions_array)
      (array_to_list aw.atomic_path_infos);
    actions_starting_at_pc_correct_proof = (fun _ -> actions_starting_at_pc_correct_lemma lprog aw);
    starting_successors_match_path_infos_proof = (fun _ -> starting_successors_match_path_infos_lemma aw);
    path_successors_match_path_infos_proof = (fun _ -> path_successors_match_path_infos_lemma aw);
    path_breaking_correct_proof = (fun _ -> path_breaking_correct_lemma aw);
    path_atomic_indices_correct_proof = (fun _ -> path_atomic_indices_correct_lemma lprog hprog aw);
    path_actions_in_lprog_proof = (fun _ -> path_actions_in_lprog_lemma lprog aw);
    starting_successors_complete_proof = (fun _ -> starting_successors_complete_lemma lprog aw);
    path_successors_complete_proof = (fun _ -> path_successors_complete_lemma lprog aw);
    created_threads_initially_breaking_proof = (fun _ -> created_threads_initially_breaking_lemma lprog aw);
    pc_breaking_correct_proof = (fun _ -> pc_breaking_correct_lemma lprog aw);
    main_start_pc_breaking_proof = (fun _ -> main_start_pc_breaking_lemma lprog aw);
    inits_identical_proof = (fun _ -> ());
  } in
  armada_refines_atomic_relation_implies_refinement aa
