module Strategies.VarHiding.Efficient

open Armada.Action
open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Strategies.VarHiding.Inefficient
open Strategies.VarHiding.Relation
open Util.ImmutableArray
open Util.List
open Util.Nth
open Util.Range
open Util.Relation

let default_pc: pc_t = ""

let make_pc_index_to_pc
  (pcs: array_t pc_t)
  (idx: nat)
  : GTot pc_t =
  match array_nth pcs idx with
  | None -> default_pc
  | Some pc -> pc

let make_pc_indices_to_pcs
  (pcs: array_t pc_t)
  (pc_indices: list nat)
  : GTot (list pc_t) =
  map_ghost (make_pc_index_to_pc pcs) pc_indices

let make_lpc_to_hpc
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (lpc: pc_t)
  : GTot pc_t =
  match find_in_array lpcs lpc with
  | None -> default_pc
  | Some lpc_index ->
      let hpc_index = array_index lpc_to_hpc lpc_index in
      make_pc_index_to_pc hpcs hpc_index

let rec make_return_pcs_offset
  (pcs: array_t pc_t)
  (is_return_pc: array_t bool{array_len is_return_pc = array_len pcs})
  (offset: nat{offset <= array_len pcs})
  : GTot (list pc_t) (decreases array_len pcs - offset) =
  if offset = array_len pcs then
    []
  else if array_index is_return_pc offset = true then
    (array_index pcs offset) :: make_return_pcs_offset pcs is_return_pc (offset + 1)
  else
    make_return_pcs_offset pcs is_return_pc (offset + 1)

let make_return_pcs
  (pcs: array_t pc_t)
  (is_return_pc: array_t bool{array_len is_return_pc = array_len pcs})
  : GTot (list pc_t) =
  make_return_pcs_offset pcs is_return_pc 0

let make_is_nonyielding_pc
  (pcs: array_t pc_t)
  (is_nonyielding_pc: array_t bool{array_len is_nonyielding_pc = array_len pcs})
  (pc: pc_t)
  : GTot bool =
  match find_in_array pcs pc with
  | None -> false
  | Some idx -> array_index is_nonyielding_pc idx

let convert_efficient_thread_state
  (pcs: array_t pc_t)
  (ts: efficient_thread_state_t)
  : GTot thread_state_t =
  match ts with
  | EfficientThreadStateRunning -> ThreadStateRunning
  | EfficientThreadStateAtPC pc -> ThreadStateAtPC (make_pc_index_to_pc pcs pc)
  | EfficientThreadStateNotRunning status -> ThreadStateNotRunning status
  | EfficientThreadStateProcessStopped stop_reason -> ThreadStateProcessStopped stop_reason

let array_to_list_contains_array_nth_ambient
  (pcs: array_t pc_t)
  (idx: nat)
  : Lemma (requires Some? (array_nth pcs idx))
          (ensures  list_contains (Some?.v (array_nth pcs idx)) (array_to_list pcs))
          [SMTPat  (Some? (array_nth pcs idx))] =
  match array_nth pcs idx with
  | Some pc ->
      array_to_list_implies_array_matches_list pcs (array_to_list pcs);        
      array_matches_list_implies_nth_equivalent pcs (array_to_list pcs) idx;
      nth_implies_contains (array_to_list pcs) idx pc

let optional_pc_matches_optional_pc_index_ambient
  (pcs: array_t pc_t)
  (optional_pc: option pc_t)
  (optional_index: option nat)
  : Lemma (requires optional_pc_matches_optional_pc_index pcs optional_pc optional_index)
          (ensures  (match optional_pc with
                     | None -> True
                     | Some pc -> list_contains pc (array_to_list pcs)))
          [SMTPat (optional_pc_matches_optional_pc_index pcs optional_pc optional_index)] =
  match optional_pc, optional_index with
  | Some pc, Some idx ->
      array_to_list_implies_array_matches_list pcs (array_to_list pcs);
      array_matches_list_implies_index_equivalent pcs (array_to_list pcs) idx;
      index_implies_contains (array_to_list pcs) idx pc
  | _, _ -> ()

let find_in_array_inverts_index
  (pcs: array_t pc_t)
  (idx: nat)
  : Lemma (requires   Some? (array_nth pcs idx)
                    /\ array_elements_unique pcs)
          (ensures  find_in_array pcs (array_index pcs idx) = Some idx)
          [SMTPat   (find_in_array pcs (array_index pcs idx))] =
  array_elements_unique_implication pcs

let make_pc_indices_to_pcs_contains_pc_implies_pc_indices_contains_index
  (pcs: array_t pc_t)
  (pc_indices: list nat)
  (pc: pc_t)
  (idx: nat)
  : Lemma (requires   list_contains pc (make_pc_indices_to_pcs pcs pc_indices)
                    /\ array_nth pcs idx = Some pc
                    /\ array_elements_unique pcs
                    /\ (forall (idx: nat). list_contains idx pc_indices ==> idx < array_len pcs))
          (ensures  list_contains idx pc_indices) =
  let idx' = reverse_map_element_of_map_ghost (make_pc_index_to_pc pcs) pc_indices pc in
  array_elements_unique_implication pcs;
  assert (idx' = idx)

let rec make_return_pcs_offset_contains_return_pc
  (pcs: array_t pc_t)
  (is_return_pc: array_t bool{array_len is_return_pc = array_len pcs})
  (offset: nat{offset <= array_len pcs})
  (idx: nat{offset <= idx /\ idx < array_len pcs})
  : Lemma (requires array_index is_return_pc idx = true)
          (ensures  list_contains (array_index pcs idx) (make_return_pcs_offset pcs is_return_pc offset))
          (decreases idx - offset) =
  if offset = array_len pcs then
    false_elim ()
  else if idx = offset && array_index is_return_pc offset = true then
    ()
  else
    make_return_pcs_offset_contains_return_pc pcs is_return_pc (offset + 1) idx

let make_return_pcs_contains_return_pc
  (pcs: array_t pc_t)
  (is_return_pc: array_t bool{array_len is_return_pc = array_len pcs})
  (idx: nat{idx < array_len is_return_pc})
  : Lemma (requires array_index is_return_pc idx = true)
          (ensures  list_contains (array_index pcs idx) (make_return_pcs pcs is_return_pc)) =
  make_return_pcs_offset_contains_return_pc pcs is_return_pc 0 idx

let lpc_hpc_relation_facts
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  : Lemma (requires array_elements_unique lpcs)
          (ensures  (let index_relation = efficient_lh_pc_relation lpc_to_hpc in
                     let index_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
                     let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
                     let pc_relation = lpc_hpc_pc_relation inefficient_lpc_to_hpc in
                     let pc_return_relation = lpc_hpc_pc_return_relation inefficient_lpc_to_hpc
                                                inefficient_return_lpcs in
                     forall (lidx: nat) (hidx: nat). lidx < array_len lpcs /\ hidx < array_len hpcs ==>
                         (let lpc = array_index lpcs lidx in
                          let hpc = array_index hpcs hidx in
                            (index_relation lidx hidx ==> pc_relation lpc hpc)
                          /\ (index_return_relation lidx hidx ==> pc_return_relation lpc hpc)))) =
  let index_relation = efficient_lh_pc_relation lpc_to_hpc in
  let index_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let pc_relation = lpc_hpc_pc_relation inefficient_lpc_to_hpc in
  let pc_return_relation = lpc_hpc_pc_return_relation inefficient_lpc_to_hpc inefficient_return_lpcs in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  introduce forall (lidx: nat) (hidx: nat). lidx < array_len lpcs /\ hidx < array_len hpcs ==>
                         (let lpc = array_index lpcs lidx in
                          let hpc = array_index hpcs hidx in
                            (index_relation lidx hidx ==> pc_relation lpc hpc)
                          /\ (index_return_relation lidx hidx ==> pc_return_relation lpc hpc))
  with introduce _ ==> _
  with _. (
    let lpc = array_index lpcs lidx in
    let hpc = array_index hpcs hidx in
    introduce index_relation lidx hidx ==> pc_relation lpc hpc
    with _. (
      assert (array_nth lpc_to_hpc lidx = Some hidx);
      assert (find_in_array lpcs lpc = Some lidx);
      assert (array_index lpc_to_hpc lidx = hidx);
      assert (make_pc_index_to_pc hpcs hidx = hpc);
      assert (inefficient_lpc_to_hpc lpc = hpc)
    );
    introduce index_return_relation lidx hidx ==> pc_return_relation lpc hpc
    with _. (
      assert (array_nth lpc_to_hpc lidx = Some hidx);
      assert (array_nth is_return_lpc lidx = Some true);
      assert (find_in_array lpcs lpc = Some lidx);
      assert (array_index lpc_to_hpc lidx = hidx);
      assert (make_pc_index_to_pc hpcs hidx = hpc);
      assert (inefficient_lpc_to_hpc lpc = hpc);
      make_return_pcs_contains_return_pc lpcs is_return_lpc lidx;
      assert (list_contains lpc inefficient_return_lpcs)
    )
  )

let program_inits_match_except_global_variables_lemma
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (which_initializers_are_hidings: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  (lprog_main_start_pc_index: nat)
  (hprog_main_start_pc_index: nat)
  : Lemma (requires   efficient_program_inits_match_except_global_variables vs lpcs hpcs lpc_to_hpc
                        which_initializers_are_hidings lprog hprog lprog_main_start_pc_index hprog_main_start_pc_index
                    /\ array_elements_unique lpcs)
          (ensures    program_inits_match_except_global_variables vs (make_lpc_to_hpc lpcs hpcs lpc_to_hpc)
                        which_initializers_are_hidings lprog hprog
                    /\ (make_lpc_to_hpc lpcs hpcs lpc_to_hpc) lprog.main_start_pc = hprog.main_start_pc) =
  array_elements_unique_implication lpcs

let rec get_index_of_pc_among_return_pcs_offset
  (lpcs: array_t pc_t)
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (offset: nat{offset <= array_len lpcs})
  (pc: pc_t)
  : Ghost nat
  (requires list_contains pc (make_return_pcs_offset lpcs is_return_lpc offset))
  (ensures fun idx -> idx < array_len lpcs /\ array_index lpcs idx = pc /\ array_index is_return_lpc idx = true)
  (decreases array_len lpcs - offset) =
  if offset = array_len lpcs then
    false_elim ()
  else if array_index is_return_lpc offset = true then (
    if array_index lpcs offset = pc then
      offset
    else
      get_index_of_pc_among_return_pcs_offset lpcs is_return_lpc (offset + 1) pc
  )
  else
    get_index_of_pc_among_return_pcs_offset lpcs is_return_lpc (offset + 1) pc

let get_index_of_pc_among_return_pcs
  (lpcs: array_t pc_t)
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (pc: pc_t)
  : Ghost nat
  (requires list_contains pc (make_return_pcs lpcs is_return_lpc))
  (ensures  fun idx -> idx < array_len lpcs /\ array_index lpcs idx = pc /\ array_index is_return_lpc idx = true) =
  get_index_of_pc_among_return_pcs_offset lpcs is_return_lpc 0 pc

let apply_efficient_return_lpcs_unique
  (num_lpcs: nat)
  (lpc_to_lpc: array_t nat)
  (is_return_lpc: array_t bool)
  (lpc1: nat)
  (lpc2: nat)
  : Lemma (requires   efficient_return_lpcs_unique num_lpcs lpc_to_lpc is_return_lpc
                    /\ lpc1 < num_lpcs
                    /\ lpc2 < num_lpcs
                    /\ array_nth is_return_lpc lpc1 = Some true
                    /\ array_nth is_return_lpc lpc2 = Some true
                    /\ array_nth lpc_to_lpc lpc1 = array_nth lpc_to_lpc lpc2)
          (ensures  lpc1 = lpc2) =
  assert (efficient_return_lpcs_unique_inner1 num_lpcs lpc_to_lpc is_return_lpc lpc1);
  assert (efficient_return_lpcs_unique_inner2 lpc_to_lpc is_return_lpc lpc1 lpc2)

#push-options "--z3rlimit 10"

let return_pcs_unique_lemma
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  : Lemma (requires   efficient_return_lpcs_unique (array_len lpcs) lpc_to_hpc is_return_lpc
                    /\ efficient_lpc_to_hpc_contains_valid_indices (array_len hpcs) lpc_to_hpc
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  return_pcs_unique (make_lpc_to_hpc lpcs hpcs lpc_to_hpc) (make_return_pcs lpcs is_return_lpc)) =
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  introduce forall lpc1. list_contains lpc1 inefficient_return_lpcs ==>
              return_pcs_unique_inner1 inefficient_lpc_to_hpc inefficient_return_lpcs lpc1
  with introduce list_contains lpc1 inefficient_return_lpcs ==>
                   return_pcs_unique_inner1 inefficient_lpc_to_hpc inefficient_return_lpcs lpc1
  with _. introduce forall lpc2. list_contains lpc2 inefficient_return_lpcs ==>
                      return_pcs_unique_inner2 inefficient_lpc_to_hpc inefficient_return_lpcs lpc1 lpc2
  with introduce list_contains lpc2 inefficient_return_lpcs ==>
                   return_pcs_unique_inner2 inefficient_lpc_to_hpc inefficient_return_lpcs lpc1 lpc2
  with _. introduce inefficient_lpc_to_hpc lpc1 = inefficient_lpc_to_hpc lpc2 ==> lpc1 = lpc2
  with _. (
    let lpc_index1 = get_index_of_pc_among_return_pcs lpcs is_return_lpc lpc1 in
    let lpc_index2 = get_index_of_pc_among_return_pcs lpcs is_return_lpc lpc2 in
    assert (lpc_index1 < array_len lpcs);
    assert (Some? (array_nth lpc_to_hpc lpc_index1));
    assert (array_nth is_return_lpc lpc_index1 = Some true);
    assert (lpc_index2 < array_len lpcs);
    assert (Some? (array_nth lpc_to_hpc lpc_index2));
    assert (array_nth is_return_lpc lpc_index2 = Some true);
    array_elements_unique_implication lpcs;
    assert (find_in_array lpcs lpc1 = Some lpc_index1);
    assert (find_in_array lpcs lpc2 = Some lpc_index2);
    let hpc_index1 = array_index lpc_to_hpc lpc_index1 in
    let hpc_index2 = array_index lpc_to_hpc lpc_index2 in
    assert (inefficient_lpc_to_hpc lpc1 = make_pc_index_to_pc hpcs hpc_index1);
    assert (inefficient_lpc_to_hpc lpc2 = make_pc_index_to_pc hpcs hpc_index2);
    assert (make_pc_index_to_pc hpcs hpc_index1 = make_pc_index_to_pc hpcs hpc_index2);
    array_elements_unique_implication hpcs;
    assert (hpc_index1 < array_len hpcs);
    assert (hpc_index2 < array_len hpcs);
    assert (hpc_index1 = hpc_index2);
    assert (array_nth lpc_to_hpc lpc_index1 = array_nth lpc_to_hpc lpc_index2);
    apply_efficient_return_lpcs_unique (array_len lpcs) lpc_to_hpc is_return_lpc lpc_index1 lpc_index2
  )

let each_action_list_consistent_with_is_nonyielding_pc_helper
  (pcs: array_t pc_t)
  (is_nonyielding_pc: array_t bool{array_len is_nonyielding_pc = array_len pcs})
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires   efficient_action_consistent_with_is_nonyielding_pc is_nonyielding_pc action pc_indices
                    /\ action_corresponds_to_statement_pc_indices pcs action pc_indices
                    /\ array_elements_unique pcs)
          (ensures  action_consistent_with_is_nonyielding_pc (make_is_nonyielding_pc pcs is_nonyielding_pc) action) =
  ()

#pop-options

let each_action_list_consistent_with_is_nonyielding_pc_lemma
  (pcs: array_t pc_t)
  (is_nonyielding_pc: array_t bool{array_len is_nonyielding_pc = array_len pcs})
  (actions_list: list (list Armada.Action.t))
  (pc_indices_array: array_t (list statement_pc_indices_t))
  : Lemma (requires   efficient_each_action_list_consistent_with_is_nonyielding_pc is_nonyielding_pc
                        (list_to_array actions_list) pc_indices_array
                    /\ actions_array_corresponds_to_statement_pc_indices_array pcs (list_to_array actions_list)
                        pc_indices_array
                    /\ array_elements_unique pcs)
          (ensures each_action_list_consistent_with_is_nonyielding_pc (make_is_nonyielding_pc pcs is_nonyielding_pc)
                     actions_list) =
  let inefficient_is_nonyielding_pc = make_is_nonyielding_pc pcs is_nonyielding_pc in
  introduce forall actions. contains_ubool actions actions_list ==>
               each_action_consistent_with_is_nonyielding_pc inefficient_is_nonyielding_pc actions
  with introduce contains_ubool actions actions_list ==>
                   each_action_consistent_with_is_nonyielding_pc inefficient_is_nonyielding_pc actions
  with _. introduce forall action. contains_ubool action actions ==>
                      action_consistent_with_is_nonyielding_pc inefficient_is_nonyielding_pc action
  with introduce contains_ubool action actions ==>
                   action_consistent_with_is_nonyielding_pc inefficient_is_nonyielding_pc action
  with _. (
    let idx = contains_ubool_to_index actions actions_list in
    let pc_indices_list = array_index pc_indices_array idx in
    arrays_correspond_specific_index (action_list_corresponds_to_statement_pc_indices_list pcs)
      (list_to_array actions_list) pc_indices_array idx;
    assert (action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list);
    assert (efficient_each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc actions pc_indices_list);
    let pc_indices = get_correspondent_from_lists_correspond_doubly
      (fun action pc_indices -> efficient_action_consistent_with_is_nonyielding_pc is_nonyielding_pc action pc_indices)
      (action_corresponds_to_statement_pc_indices pcs)
      actions pc_indices_list action in
    assert (efficient_action_consistent_with_is_nonyielding_pc is_nonyielding_pc action pc_indices);
    assert (action_corresponds_to_statement_pc_indices pcs action pc_indices);
    each_action_list_consistent_with_is_nonyielding_pc_helper pcs is_nonyielding_pc action pc_indices;
    assert (action_consistent_with_is_nonyielding_pc inefficient_is_nonyielding_pc action)
  )

let efficient_laction_corresponds_to_haction_preservation
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (laction: Armada.Action.t)
  (haction: Armada.Action.t)
  (lpc_indices: statement_pc_indices_t)
  (hpc_indices: statement_pc_indices_t)
  : Lemma (requires (let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
                     let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
                       efficient_laction_corresponds_to_haction vs pc_relation pc_return_relation laction haction
                         lpc_indices hpc_indices
                     /\ action_corresponds_to_statement_pc_indices lpcs laction lpc_indices
                     /\ action_corresponds_to_statement_pc_indices hpcs haction hpc_indices
                     /\ array_elements_unique lpcs))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
                     laction_corresponds_to_haction vs inefficient_lpc_to_hpc inefficient_return_lpcs laction
                       haction)) =
  let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
  let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let lps, hps = laction.program_statement, haction.program_statement in
  let relation = lpc_hpc_pc_relation inefficient_lpc_to_hpc in
  let return_relation = lpc_hpc_pc_return_relation inefficient_lpc_to_hpc inefficient_return_lpcs in
  assert (efficient_program_statements_match_per_pc_relation pc_relation pc_return_relation lps hps lpc_indices
            hpc_indices);
  lpc_hpc_relation_facts lpcs hpcs lpc_to_hpc is_return_lpc;
  efficient_program_statements_match_per_pc_relation_implies_program_statements_match_per_pc_relation lpcs hpcs
    pc_relation pc_return_relation relation return_relation lps hps lpc_indices hpc_indices;
  assert (program_statements_match_per_pc_relation relation return_relation lps hps)

let efficient_thread_states_match_per_pc_relation_implies_thread_states_match_per_pc_relation
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (lts: efficient_thread_state_t)
  (hts: efficient_thread_state_t)
  : Lemma (requires (let index_relation = efficient_lh_pc_relation lpc_to_hpc in
                       efficient_thread_states_match_per_pc_relation index_relation lts hts
                     /\ array_elements_unique lpcs))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let pc_relation = lpc_hpc_pc_relation inefficient_lpc_to_hpc in
                     thread_states_match_per_pc_relation pc_relation
                       (convert_efficient_thread_state lpcs lts)
                       (convert_efficient_thread_state hpcs hts)))
          [SMTPat (thread_states_match_per_pc_relation (lpc_hpc_pc_relation (make_lpc_to_hpc lpcs hpcs lpc_to_hpc))
                    (convert_efficient_thread_state lpcs lts) (convert_efficient_thread_state hpcs hts))] =
  ()

let invert_make_pc_indices_to_pcs
  (pcs: array_t pc_t)
  (pc_indices: list nat{forall idx. list_contains idx pc_indices ==> idx < array_len pcs})
  (pc: pc_t{list_contains pc (make_pc_indices_to_pcs pcs pc_indices)})
  : GTot (idx: nat{list_contains idx pc_indices /\ array_nth pcs idx = Some pc}) =
  reverse_map_element_of_map_ghost (make_pc_index_to_pc pcs) pc_indices pc

let efficient_action_to_starting_thread_state_matches
  (pcs: array_t pc_t)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires action_corresponds_to_statement_pc_indices pcs action pc_indices)
          (ensures  action_to_starting_thread_state action = convert_efficient_thread_state pcs
                      (efficient_action_to_starting_thread_state pc_indices))
          [SMTPat (action_to_starting_thread_state action);
           SMTPat (action_corresponds_to_statement_pc_indices pcs action pc_indices)] =
  ()

let efficient_action_to_ending_thread_state_matches
  (pcs: array_t pc_t)
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires action_corresponds_to_statement_pc_indices pcs action pc_indices)
          (ensures  action_to_ending_thread_state action = convert_efficient_thread_state pcs
                      (efficient_action_to_ending_thread_state action pc_indices))
          [SMTPat  (action_to_ending_thread_state action);
           SMTPat  (action_corresponds_to_statement_pc_indices pcs action pc_indices)] =
  ()

let rec efficient_actions_to_ending_thread_state_matches
  (pcs: array_t pc_t)
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : Lemma (requires action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list)
          (ensures  actions_to_ending_thread_state actions = convert_efficient_thread_state pcs
                      (efficient_actions_to_ending_thread_state actions pc_indices_list))
          (decreases actions)
          [SMTPat  (actions_to_ending_thread_state actions);
           SMTPat  (action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list)] =
  match actions, pc_indices_list with
  | [], _ -> ()
  | [action], [pc_indices] -> ()
  | first_action :: remaining_actions, first_pc_indices :: remaining_pc_indices ->
      efficient_actions_to_ending_thread_state_matches pcs remaining_actions remaining_pc_indices
  | _, _ -> false_elim ()

let rec efficient_lactions_all_hidden_preservation
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (lstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (lactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  : Lemma (requires (  efficient_lactions_all_hidden vs lpc_to_hpc lstart_state lend_state lactions lpc_indices
                     /\ action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices
                     /\ array_elements_unique lpcs))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
                     let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
                     lactions_all_hidden vs inefficient_lpc_to_hpc inefficient_lstart_state inefficient_lend_state
                       lactions))
          (decreases lactions) =
  let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
  let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
  match lactions, lpc_indices with
  | [], [] -> ()
  | first_laction :: remaining_lactions, first_lpc_indices :: remaining_lpc_indices ->
      efficient_lactions_all_hidden_preservation vs lpcs hpcs lpc_to_hpc
        (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
        lend_state remaining_lactions remaining_lpc_indices;
      assert (match inefficient_lstart_state, action_to_ending_thread_state first_laction with
              | ThreadStateAtPC lpc1, ThreadStateAtPC lpc2 -> inefficient_lpc_to_hpc lpc1 = inefficient_lpc_to_hpc lpc2
              | _, _ -> False)

let rec efficient_lactions_correspond_to_hactions_preservation
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (lstart_state: efficient_thread_state_t)
  (hstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (hend_state: efficient_thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : Lemma (requires (let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
                     let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
                       efficient_lactions_correspond_to_hactions vs pc_relation pc_return_relation
                         lstart_state hstart_state lend_state hend_state which_actions_hidden lactions hactions
                         lpc_indices hpc_indices
                     /\ action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices
                     /\ action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices
                     /\ array_elements_unique lpcs
                     /\ array_elements_unique hpcs))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
                     let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
                     let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
                     let inefficient_hstart_state = convert_efficient_thread_state hpcs hstart_state in
                     let inefficient_hend_state = convert_efficient_thread_state hpcs hend_state in
                     lactions_correspond_to_hactions vs inefficient_lpc_to_hpc inefficient_return_lpcs
                       inefficient_lstart_state inefficient_hstart_state inefficient_lend_state
                       inefficient_hend_state which_actions_hidden lactions hactions))
          (decreases lactions) =
  let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
  let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
  let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
  let inefficient_hstart_state = convert_efficient_thread_state hpcs hstart_state in
  let inefficient_hend_state = convert_efficient_thread_state hpcs hend_state in
  let relation = fun lpc hpc -> inefficient_lpc_to_hpc lpc = hpc in
  lpc_hpc_relation_facts lpcs hpcs lpc_to_hpc is_return_lpc;
  match which_actions_hidden, lactions, hactions, lpc_indices, hpc_indices with
  | [], [], [], [], [] -> ()
  | false :: remaining_which_actions_hidden, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lpc_indices :: remaining_lpc_indices, first_hpc_indices :: remaining_hpc_indices ->
      efficient_laction_corresponds_to_haction_preservation vs lpcs hpcs lpc_to_hpc is_return_lpc
        first_laction first_haction first_lpc_indices first_hpc_indices;
      efficient_lactions_correspond_to_hactions_preservation vs lpcs hpcs lpc_to_hpc is_return_lpc
        (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
        (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
        lend_state hend_state remaining_which_actions_hidden remaining_lactions remaining_hactions
        remaining_lpc_indices remaining_hpc_indices
  | true :: remaining_which_actions_hidden, first_laction :: remaining_lactions, _,
      first_lpc_indices :: remaining_lpc_indices, _ ->
      efficient_lactions_correspond_to_hactions_preservation vs lpcs hpcs lpc_to_hpc is_return_lpc
        (efficient_action_to_ending_thread_state first_laction first_lpc_indices) hstart_state
        lend_state hend_state remaining_which_actions_hidden remaining_lactions hactions remaining_lpc_indices
        hpc_indices
  | _, _, _, _, _ -> false_elim ()

#push-options "--z3rlimit 30"

let efficient_corresponding_hactions_info_correct_inner_preservation
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (latomic_actions: list (list Armada.Action.t))
  (hatomic_actions: list (list Armada.Action.t))
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv)
    {array_len corresponding_hactions_info = list_len latomic_actions})
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (correspondence: ltoh_correspondence_t vs tds inv)
  (laction_idx: nat{laction_idx < list_len latomic_actions})
  : Lemma (requires (let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
                     let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
                       efficient_corresponding_hactions_info_correct_inner vs tds inv (list_to_array latomic_actions)
                         (list_to_array hatomic_actions) corresponding_hactions_info lpc_indices_array
                         hpc_indices_array lpc_to_hpc pc_relation pc_return_relation laction_idx
                     /\ efficient_lpc_to_hpc_contains_valid_indices (array_len hpcs) lpc_to_hpc
                     /\ array_elements_unique lpcs
                     /\ array_elements_unique hpcs
                     /\ actions_array_corresponds_to_statement_pc_indices_array lpcs (list_to_array latomic_actions)
                         lpc_indices_array
                     /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                         hpc_indices_array
                     /\ array_nth corresponding_hactions_info laction_idx == Some correspondence))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                     let inefficient_hpcs = array_to_list hpcs in
                     let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
                     let lactions = list_index latomic_actions laction_idx in
                     lactions_correspond_to_hactions_per_correspondence vs tds inv inefficient_lpc_to_hpc
                       inefficient_return_lpcs hatomic_actions lactions correspondence)) =
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let latomic_actions_array = list_to_array latomic_actions in
  let hatomic_actions_array = list_to_array hatomic_actions in
  let ltoh_info = array_index corresponding_hactions_info laction_idx in
  list_to_array_implies_index_equivalent latomic_actions_array latomic_actions laction_idx;
  assert (list_index latomic_actions laction_idx == array_index latomic_actions_array laction_idx);
  let lactions = array_index latomic_actions_array laction_idx in
  let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
  let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
  assert (efficient_corresponding_hactions_info_correct_inner vs tds inv latomic_actions_array
            hatomic_actions_array corresponding_hactions_info
            lpc_indices_array hpc_indices_array lpc_to_hpc pc_relation pc_return_relation laction_idx);
  let lpc_indices = array_index lpc_indices_array laction_idx in
  assert (action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices);
  match array_index corresponding_hactions_info laction_idx with
  | CorrespondenceHidden ->
      let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
      let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
      assert (actions_start_atomic_block lactions = actions_end_atomic_block lactions);
      efficient_lactions_all_hidden_preservation vs lpcs hpcs lpc_to_hpc
        lstart_state lend_state lactions lpc_indices
  | CorrespondencePropagate hidx ->
      list_to_array_implies_nth_equivalent hatomic_actions_array hatomic_actions hidx
  | CorrespondenceNormal hidx which_actions_hidden ->
      list_to_array_implies_nth_equivalent hatomic_actions_array hatomic_actions hidx;
      (match array_nth hatomic_actions_array hidx, array_nth hpc_indices_array hidx with
       | Some hactions, Some hpc_indices ->
           assert (action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices);
           let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
           let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
           let hstart_state = efficient_action_to_starting_thread_state (Cons?.hd hpc_indices) in
           let hend_state = efficient_actions_to_ending_thread_state hactions hpc_indices in
           efficient_lactions_correspond_to_hactions_preservation vs lpcs hpcs lpc_to_hpc is_return_lpc
             lstart_state hstart_state lend_state hend_state which_actions_hidden lactions hactions lpc_indices
             hpc_indices;
           assert (lactions_correspond_to_hactions_per_correspondence vs tds inv inefficient_lpc_to_hpc
                     inefficient_return_lpcs hatomic_actions lactions correspondence))
  | CorrespondenceImpossibleConstantAssignmentFailure ->
      ()
  | CorrespondenceImpossibleStatementFailure ps proof ->
      ()

#pop-options
#push-options "--z3rlimit 10"

let corresponding_hactions_info_correct_lemma
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (latomic_actions: list (list Armada.Action.t))
  (hatomic_actions: list (list Armada.Action.t))
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat{array_len lpc_to_hpc = array_len lpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (is_return_lpc: array_t bool{array_len is_return_lpc = array_len lpcs})
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv)
    {array_len corresponding_hactions_info = list_len latomic_actions})
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  : Lemma (requires   efficient_corresponding_hactions_info_correct vs tds inv (list_to_array latomic_actions)
                        (list_to_array hatomic_actions) lpc_to_hpc is_return_lpc
                        corresponding_hactions_info lpc_indices_array hpc_indices_array
                    /\ efficient_lpc_to_hpc_contains_valid_indices (array_len hpcs) lpc_to_hpc
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs
                    /\ actions_array_corresponds_to_statement_pc_indices_array lpcs (list_to_array latomic_actions)
                        lpc_indices_array
                    /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                        hpc_indices_array
                    /\ array_len corresponding_hactions_info = array_len (list_to_array latomic_actions))
          (ensures  (let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
                     let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                     let inefficient_hpcs = array_to_list hpcs in
                     let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
                     lists_correspond_ubool
                       (lactions_correspond_to_hactions_per_correspondence vs tds inv inefficient_lpc_to_hpc
                          inefficient_return_lpcs hatomic_actions)
                       latomic_actions (array_to_list corresponding_hactions_info))) =
  let inefficient_lpc_to_hpc = make_lpc_to_hpc lpcs hpcs lpc_to_hpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_return_lpcs = make_return_pcs lpcs is_return_lpc in
  let latomic_actions_array = list_to_array latomic_actions in
  let hatomic_actions_array = list_to_array hatomic_actions in
  list_to_array_implies_length_equivalent latomic_actions_array latomic_actions;
  assert (list_len latomic_actions = array_len corresponding_hactions_info);
  introduce forall laction_idx. laction_idx < list_len latomic_actions ==>
               lactions_correspond_to_hactions_per_correspondence vs tds inv inefficient_lpc_to_hpc
                 inefficient_return_lpcs hatomic_actions
                 (list_index latomic_actions laction_idx)
                 (array_index corresponding_hactions_info laction_idx)
  with introduce _ ==> _
  with _. (
    let ltoh_info = array_index corresponding_hactions_info laction_idx in
    list_to_array_implies_index_equivalent latomic_actions_array latomic_actions laction_idx;
    assert (list_index latomic_actions laction_idx == array_index latomic_actions_array laction_idx);
    let lactions = array_index latomic_actions_array laction_idx in
    let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
    let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
    assert (efficient_corresponding_hactions_info_correct_inner vs tds inv latomic_actions_array
              hatomic_actions_array corresponding_hactions_info
              lpc_indices_array hpc_indices_array lpc_to_hpc pc_relation pc_return_relation laction_idx);
    let lpc_indices = array_index lpc_indices_array laction_idx in
    let hactions_info = array_index corresponding_hactions_info laction_idx in
    assert (efficient_lactions_correspond_to_hactions_per_correspondence vs tds inv lpc_to_hpc pc_relation
              pc_return_relation hatomic_actions_array hpc_indices_array lactions lpc_indices
              hactions_info);
    let correspondence = array_index corresponding_hactions_info laction_idx in
    efficient_corresponding_hactions_info_correct_inner_preservation vs tds inv latomic_actions hatomic_actions
      lpcs hpcs lpc_to_hpc is_nonyielding_lpc is_return_lpc
      corresponding_hactions_info lpc_indices_array hpc_indices_array correspondence
      laction_idx
  );
  establish_lists_correspond_ubool_from_index_correspondence
    (lactions_correspond_to_hactions_per_correspondence vs tds inv inefficient_lpc_to_hpc inefficient_return_lpcs
       hatomic_actions)
    latomic_actions (array_to_list corresponding_hactions_info)

#pop-options

let efficient_var_hiding_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (evw: efficient_var_hiding_witness_t)
  (* see .fsti file for spec *) =
  let vw: inefficient_var_hiding_witness_t = {
    lprog = evw.lprog;
    hprog = evw.hprog;
    vs = evw.vs;
    tds = evw.tds;
    inv = evw.inv;
    which_initializers_are_hidings = evw.which_initializers_are_hidings;
    lpc_to_hpc = make_lpc_to_hpc evw.lpcs evw.hpcs evw.lpc_to_hpc;
    return_lpcs = make_return_pcs evw.lpcs evw.is_return_lpc;
    is_nonyielding_lpc = make_is_nonyielding_pc evw.lpcs evw.is_nonyielding_lpc;
    is_nonyielding_hpc = make_is_nonyielding_pc evw.hpcs evw.is_nonyielding_hpc;
    corresponding_hactions_info = array_to_list evw.corresponding_hactions_info;
  } in
  program_inits_match_except_global_variables_lemma evw.vs evw.lpcs evw.hpcs evw.lpc_to_hpc
    evw.which_initializers_are_hidings evw.lprog evw.hprog evw.lprog_main_start_pc_index evw.hprog_main_start_pc_index;
  assert (vw.lpc_to_hpc vw.lprog.main_start_pc = vw.hprog.main_start_pc);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers);
  assert (every_variable_appears_among_initializers vw.lprog.global_initializers vw.vs vw.tds);
  return_pcs_unique_lemma evw.lpcs evw.hpcs evw.lpc_to_hpc evw.is_return_lpc;
  assert (return_pcs_unique vw.lpc_to_hpc vw.return_lpcs);
  each_action_list_consistent_with_is_nonyielding_pc_lemma evw.lpcs evw.is_nonyielding_lpc latomic_prog.actions
    evw.lpc_indices_array;
  assert (each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc latomic_prog.actions);
  each_action_list_consistent_with_is_nonyielding_pc_lemma evw.hpcs evw.is_nonyielding_hpc hatomic_prog.actions
    evw.hpc_indices_array;
  assert (each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc hatomic_prog.actions);
  assert (each_action_list_doesnt_internally_yield latomic_prog.actions);
  assert (each_action_list_doesnt_internally_yield hatomic_prog.actions);
  corresponding_hactions_info_correct_lemma evw.vs evw.tds evw.inv latomic_prog.actions hatomic_prog.actions
    evw.lpcs evw.hpcs evw.lpc_to_hpc evw.is_nonyielding_lpc
    evw.is_return_lpc evw.corresponding_hactions_info evw.lpc_indices_array evw.hpc_indices_array;
  assert (lists_correspond_ubool
           (lactions_correspond_to_hactions_per_correspondence vw.vs vw.tds vw.inv vw.lpc_to_hpc vw.return_lpcs
              hatomic_prog.actions)
           latomic_prog.actions vw.corresponding_hactions_info);
  assert (inefficient_var_hiding_witness_valid latomic_prog hatomic_prog vw);
  inefficient_var_hiding_witness_valid_implies_refinement latomic_prog hatomic_prog vw
