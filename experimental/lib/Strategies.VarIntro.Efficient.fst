module Strategies.VarIntro.Efficient

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
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Inefficient
open Strategies.VarIntro.Relation
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

let make_hpc_to_lpc
  (hpcs: array_t pc_t)
  (lpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (hpc: pc_t)
  : GTot pc_t =
  match find_in_array hpcs hpc with
  | None -> default_pc
  | Some hpc_index ->
      let lpc_index = array_index hpc_to_lpc hpc_index in
      make_pc_index_to_pc lpcs lpc_index

let make_lpc_to_hpcs
  (hpcs: array_t pc_t)
  (lpcs: array_t pc_t)
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  (lpc: pc_t)
  : GTot (list pc_t) =
  match find_in_array lpcs lpc with
  | None -> []
  | Some lpc_index ->
      let hpc_indices = array_index lpc_to_hpcs lpc_index in
      make_pc_indices_to_pcs hpcs hpc_indices

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

let make_is_breaking_pc
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (pc: pc_t)
  : GTot bool =
  match find_in_array pcs pc with
  | None -> false
  | Some idx -> array_index is_breaking_pc idx

let make_hpc_info
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpcs: array_t pc_t)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (hpc: pc_t)
  : GTot (hpc_info_t vs tds inv) =
  match find_in_array hpcs hpc with
  | None -> HPCInfoNormal
  | Some hpc_index ->
      (match array_index hpc_info hpc_index with
       | EfficientHPCInfoNormal -> HPCInfoNormal
       | EfficientHPCInfoIntroduced idx end_pc introduction_succeeds_witnesses progress ->
           HPCInfoIntroduced idx (make_pc_index_to_pc hpcs end_pc) introduction_succeeds_witnesses progress)

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
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  : Lemma (requires array_elements_unique hpcs)
          (ensures  (let index_relation = efficient_hl_pc_relation hpc_to_lpc in
                     let index_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
                     let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
                     let pc_relation = lpc_hpc_pc_relation inefficient_hpc_to_lpc in
                     let pc_return_relation = lpc_hpc_pc_return_relation inefficient_hpc_to_lpc
                                                inefficient_return_hpcs in
                     forall (lidx: nat) (hidx: nat). lidx < array_len lpcs /\ hidx < array_len hpcs ==>
                         (let lpc = array_index lpcs lidx in
                          let hpc = array_index hpcs hidx in
                            (index_relation lidx hidx ==> pc_relation lpc hpc)
                          /\ (index_return_relation lidx hidx ==> pc_return_relation lpc hpc)))) =
  let index_relation = efficient_hl_pc_relation hpc_to_lpc in
  let index_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let pc_relation = lpc_hpc_pc_relation inefficient_hpc_to_lpc in
  let pc_return_relation = lpc_hpc_pc_return_relation inefficient_hpc_to_lpc inefficient_return_hpcs in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
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
      assert (array_nth hpc_to_lpc hidx = Some lidx);
      assert (find_in_array hpcs hpc = Some hidx);
      assert (array_index hpc_to_lpc hidx = lidx);
      assert (make_pc_index_to_pc lpcs lidx = lpc);
      assert (inefficient_hpc_to_lpc hpc = lpc)
    );
    introduce index_return_relation lidx hidx ==> pc_return_relation lpc hpc
    with _. (
      assert (array_nth hpc_to_lpc hidx = Some lidx);
      assert (array_nth is_return_hpc hidx = Some true);
      assert (find_in_array hpcs hpc = Some hidx);
      assert (array_index hpc_to_lpc hidx = lidx);
      assert (make_pc_index_to_pc lpcs lidx = lpc);
      assert (inefficient_hpc_to_lpc hpc = lpc);
      make_return_pcs_contains_return_pc hpcs is_return_hpc hidx;
      assert (list_contains hpc inefficient_return_hpcs)
    )
  )

let program_inits_match_except_global_variables_lemma
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (which_initializers_are_intros: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  (lprog_main_start_pc_index: nat)
  (hprog_main_start_pc_index: nat)
  : Lemma (requires   efficient_program_inits_match_except_global_variables vs lpcs hpcs hpc_to_lpc
                        which_initializers_are_intros lprog hprog lprog_main_start_pc_index hprog_main_start_pc_index
                    /\ array_elements_unique hpcs)
          (ensures    program_inits_match_except_global_variables vs (make_hpc_to_lpc hpcs lpcs hpc_to_lpc)
                        which_initializers_are_intros lprog hprog
                    /\ (make_hpc_to_lpc hpcs lpcs hpc_to_lpc) hprog.main_start_pc = lprog.main_start_pc) =
  array_elements_unique_implication hpcs

let hstart_pc_among_hpcs_lemma
  (hpcs: array_t pc_t)
  (hprog: Armada.Program.t)
  (hprog_main_start_pc_index: nat)
  : Lemma (requires  array_nth hpcs hprog_main_start_pc_index = Some hprog.main_start_pc)
          (ensures   list_contains hprog.main_start_pc (array_to_list hpcs)) =
  ()

let pcs_contain_new_pcs_of_action_lemma
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hprog_actions_array: array_t (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (hpcs: array_t pc_t)
  : Lemma (requires   hprog_actions_array == list_to_array hatomic_prog.actions
                    /\ actions_array_corresponds_to_statement_pc_indices_array hpcs hprog_actions_array
                        hpc_indices_array)
          (ensures  for_all_ghost (for_all_ghost (pcs_contain_new_pcs_of_action (array_to_list hpcs)))
                      hatomic_prog.actions) =
  let hpc_list = array_to_list hpcs in
  introduce forall actions. contains_ubool actions hatomic_prog.actions ==>
               (forall action. contains_ubool action actions ==> pcs_contain_new_pcs_of_action hpc_list action)
  with introduce contains_ubool actions hatomic_prog.actions ==>
                   (forall action. contains_ubool action actions ==> pcs_contain_new_pcs_of_action hpc_list action)
  with _. introduce forall action. contains_ubool action actions ==> pcs_contain_new_pcs_of_action hpc_list action
  with introduce contains_ubool action actions ==> pcs_contain_new_pcs_of_action hpc_list action
  with _. (
    let actions_idx = contains_ubool_to_index actions hatomic_prog.actions in
    let hactions = array_index hprog_actions_array actions_idx in
    let hpc_indices_list = array_index hpc_indices_array actions_idx in
    assert (action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices_list);
    let hpc_indices = get_correspondent_from_lists_correspond (action_corresponds_to_statement_pc_indices hpcs)
      hactions hpc_indices_list action in
    assert (action_corresponds_to_statement_pc_indices hpcs action hpc_indices)
  )

#push-options "--z3rlimit 10"

let every_hpc_appears_among_lpc_to_hpcs_lemma
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  : Lemma (requires   efficient_hpc_among_hpc_to_lpc_to_hpcs (array_len hpcs) hpc_to_lpc lpc_to_hpcs
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  every_hpc_appears_among_lpc_to_hpcs (make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs)
                      (make_hpc_to_lpc hpcs lpcs hpc_to_lpc) (array_to_list hpcs)) =
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
  introduce forall hpc. list_contains hpc inefficient_hpcs ==>
                     list_contains hpc (inefficient_lpc_to_hpcs (inefficient_hpc_to_lpc hpc))
  with introduce list_contains hpc inefficient_hpcs ==>
                   list_contains hpc (inefficient_lpc_to_hpcs (inefficient_hpc_to_lpc hpc))
  with _. (
    let hpc_index = contains_to_index hpc inefficient_hpcs in
    assert (array_nth hpcs hpc_index = Some hpc);
    let lpc_index = array_index hpc_to_lpc hpc_index in
    let lpc = array_index lpcs lpc_index in
    let hpc_indices = array_index lpc_to_hpcs lpc_index in
    assert (list_contains hpc_index hpc_indices);
    assert (find_in_array hpcs hpc = Some hpc_index);
    assert (inefficient_hpc_to_lpc hpc = lpc);
    let inefficient_hpcs = inefficient_lpc_to_hpcs lpc in
    assert (inefficient_hpcs = make_pc_indices_to_pcs hpcs hpc_indices);
    map_ghost_contains (make_pc_index_to_pc hpcs) hpc_indices hpc_index;
    assert (list_contains (make_pc_index_to_pc hpcs hpc_index) inefficient_hpcs);
    assert (make_pc_index_to_pc hpcs hpc_index = hpc)
  )

#pop-options

let rec get_index_of_pc_among_return_pcs_offset
  (hpcs: array_t pc_t)
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (offset: nat{offset <= array_len hpcs})
  (pc: pc_t)
  : Ghost nat
  (requires list_contains pc (make_return_pcs_offset hpcs is_return_hpc offset))
  (ensures fun idx -> idx < array_len hpcs /\ array_index hpcs idx = pc /\ array_index is_return_hpc idx = true)
  (decreases array_len hpcs - offset) =
  if offset = array_len hpcs then
    false_elim ()
  else if array_index is_return_hpc offset = true then (
    if array_index hpcs offset = pc then
      offset
    else
      get_index_of_pc_among_return_pcs_offset hpcs is_return_hpc (offset + 1) pc
  )
  else
    get_index_of_pc_among_return_pcs_offset hpcs is_return_hpc (offset + 1) pc

let get_index_of_pc_among_return_pcs
  (hpcs: array_t pc_t)
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (pc: pc_t)
  : Ghost nat
  (requires list_contains pc (make_return_pcs hpcs is_return_hpc))
  (ensures  fun idx -> idx < array_len hpcs /\ array_index hpcs idx = pc /\ array_index is_return_hpc idx = true) =
  get_index_of_pc_among_return_pcs_offset hpcs is_return_hpc 0 pc

let apply_efficient_return_hpcs_unique
  (num_hpcs: nat)
  (hpc_to_lpc: array_t nat)
  (is_return_hpc: array_t bool)
  (hpc1: nat)
  (hpc2: nat)
  : Lemma (requires   efficient_return_hpcs_unique num_hpcs hpc_to_lpc is_return_hpc
                    /\ hpc1 < num_hpcs
                    /\ hpc2 < num_hpcs
                    /\ array_nth is_return_hpc hpc1 = Some true
                    /\ array_nth is_return_hpc hpc2 = Some true
                    /\ array_nth hpc_to_lpc hpc1 = array_nth hpc_to_lpc hpc2)
          (ensures  hpc1 = hpc2) =
  assert (efficient_return_hpcs_unique_inner1 num_hpcs hpc_to_lpc is_return_hpc hpc1);
  assert (efficient_return_hpcs_unique_inner2 hpc_to_lpc is_return_hpc hpc1 hpc2)

#push-options "--z3rlimit 10"

let return_pcs_unique_lemma
  (hpcs: array_t pc_t)
  (lpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  : Lemma (requires    efficient_return_hpcs_unique (array_len hpcs) hpc_to_lpc is_return_hpc
                    /\ efficient_hpc_among_hpc_to_lpc_to_hpcs (array_len hpcs) hpc_to_lpc lpc_to_hpcs
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  return_pcs_unique (make_hpc_to_lpc hpcs lpcs hpc_to_lpc) (make_return_pcs hpcs is_return_hpc)) =
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  introduce forall hpc1. list_contains hpc1 inefficient_return_hpcs ==>
              return_pcs_unique_inner1 inefficient_hpc_to_lpc inefficient_return_hpcs hpc1
  with introduce list_contains hpc1 inefficient_return_hpcs ==>
                   return_pcs_unique_inner1 inefficient_hpc_to_lpc inefficient_return_hpcs hpc1
  with _. introduce forall hpc2. list_contains hpc2 inefficient_return_hpcs ==>
                      return_pcs_unique_inner2 inefficient_hpc_to_lpc inefficient_return_hpcs hpc1 hpc2
  with introduce list_contains hpc2 inefficient_return_hpcs ==>
                   return_pcs_unique_inner2 inefficient_hpc_to_lpc inefficient_return_hpcs hpc1 hpc2
  with _. introduce inefficient_hpc_to_lpc hpc1 = inefficient_hpc_to_lpc hpc2 ==> hpc1 = hpc2
  with _. (
    let hpc_index1 = get_index_of_pc_among_return_pcs hpcs is_return_hpc hpc1 in
    let hpc_index2 = get_index_of_pc_among_return_pcs hpcs is_return_hpc hpc2 in
    assert (hpc_index1 < array_len hpcs);
    assert (Some? (array_nth hpc_to_lpc hpc_index1));
    assert (array_nth is_return_hpc hpc_index1 = Some true);
    assert (hpc_index2 < array_len hpcs);
    assert (Some? (array_nth hpc_to_lpc hpc_index2));
    assert (array_nth is_return_hpc hpc_index2 = Some true);
    array_elements_unique_implication hpcs;
    assert (find_in_array hpcs hpc1 = Some hpc_index1);
    assert (find_in_array hpcs hpc2 = Some hpc_index2);
    let lpc_index1 = array_index hpc_to_lpc hpc_index1 in
    let lpc_index2 = array_index hpc_to_lpc hpc_index2 in
    assert (inefficient_hpc_to_lpc hpc1 = make_pc_index_to_pc lpcs lpc_index1);
    assert (inefficient_hpc_to_lpc hpc2 = make_pc_index_to_pc lpcs lpc_index2);
    assert (make_pc_index_to_pc lpcs lpc_index1 = make_pc_index_to_pc lpcs lpc_index2);
    array_elements_unique_implication lpcs;
    assert (lpc_index1 < array_len lpcs);
    assert (lpc_index2 < array_len lpcs);
    assert (lpc_index1 = lpc_index2);
    assert (array_nth hpc_to_lpc hpc_index1 = array_nth hpc_to_lpc hpc_index2);
    apply_efficient_return_hpcs_unique (array_len hpcs) hpc_to_lpc is_return_hpc hpc_index1 hpc_index2
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

let efficient_action_breaks_implies_action_breaks
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires   efficient_action_breaks is_breaking_pc action pc_indices
                    /\ action_corresponds_to_statement_pc_indices pcs action pc_indices
                    /\ array_elements_unique pcs)
          (ensures  action_breaks (make_is_breaking_pc pcs is_breaking_pc) action) =
  ()

let efficient_action_only_creates_breaking_threads_implies_action_only_creates_breaking_threads
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : Lemma (requires   efficient_action_only_creates_breaking_threads is_breaking_pc pc_indices
                    /\ action_corresponds_to_statement_pc_indices pcs action pc_indices
                    /\ array_elements_unique pcs)
          (ensures  action_only_creates_breaking_threads (make_is_breaking_pc pcs is_breaking_pc) action) =
  ()

let rec efficient_actions_end_with_all_threads_breaking_implies_actions_end_with_all_threads_breaking
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : Lemma (requires   efficient_actions_end_with_all_threads_breaking is_breaking_pc actions pc_indices_list
                    /\ action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list
                    /\ array_elements_unique pcs)
          (ensures  actions_end_with_all_threads_breaking (make_is_breaking_pc pcs is_breaking_pc) actions) =
  match actions, pc_indices_list with
  | [], [] -> false_elim ()
  | [last_action], [last_pc_indices] ->
      efficient_action_only_creates_breaking_threads_implies_action_only_creates_breaking_threads
        pcs is_breaking_pc last_action last_pc_indices;
      efficient_action_breaks_implies_action_breaks pcs is_breaking_pc last_action last_pc_indices
  | first_action :: remaining_actions, first_pc_indices :: remaining_pc_indices ->
      efficient_action_only_creates_breaking_threads_implies_action_only_creates_breaking_threads
        pcs is_breaking_pc first_action first_pc_indices;
      efficient_actions_end_with_all_threads_breaking_implies_actions_end_with_all_threads_breaking
        pcs is_breaking_pc remaining_actions remaining_pc_indices
  | _, _ -> false_elim ()

let efficient_actions_maintain_all_threads_breaking_implies_actions_maintain_all_threads_breaking
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : Lemma (requires   efficient_actions_maintain_all_threads_breaking is_breaking_pc actions pc_indices_list
                    /\ action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list
                    /\ array_elements_unique pcs)
          (ensures  actions_maintain_all_threads_breaking (make_is_breaking_pc pcs is_breaking_pc) actions) =
  if efficient_actions_end_with_all_threads_breaking is_breaking_pc actions pc_indices_list then
    efficient_actions_end_with_all_threads_breaking_implies_actions_end_with_all_threads_breaking
      pcs is_breaking_pc actions pc_indices_list
  else
    ()

let each_action_list_maintains_all_threads_breaking_lemma
  (pcs: array_t pc_t)
  (is_breaking_pc: array_t bool{array_len is_breaking_pc = array_len pcs})
  (actions_list: list (list Armada.Action.t))
  (pc_indices_array: array_t (list statement_pc_indices_t))
  : Lemma (requires   efficient_each_action_list_maintains_all_threads_breaking is_breaking_pc
                        (list_to_array actions_list) pc_indices_array
                    /\ actions_array_corresponds_to_statement_pc_indices_array pcs (list_to_array actions_list)
                        pc_indices_array
                    /\ array_elements_unique pcs)
          (ensures each_action_list_maintains_all_threads_breaking (make_is_breaking_pc pcs is_breaking_pc)
                     actions_list) =
  let inefficient_is_breaking_pc = make_is_breaking_pc pcs is_breaking_pc in
  introduce forall actions. contains_ubool actions actions_list ==>
               actions_maintain_all_threads_breaking inefficient_is_breaking_pc actions
  with introduce contains_ubool actions actions_list ==>
                   actions_maintain_all_threads_breaking inefficient_is_breaking_pc actions
  with _. (
    let idx = contains_ubool_to_index actions actions_list in
    let pc_indices_list = array_index pc_indices_array idx in
    arrays_correspond_specific_index (action_list_corresponds_to_statement_pc_indices_list pcs)
      (list_to_array actions_list) pc_indices_array idx;
    assert (action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices_list);
    assert (efficient_actions_maintain_all_threads_breaking is_breaking_pc actions pc_indices_list);
    efficient_actions_maintain_all_threads_breaking_implies_actions_maintain_all_threads_breaking
      pcs is_breaking_pc actions pc_indices_list
  )

let rec efficient_hactions_introducible_implies_hactions_introducible
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (hstart_pc: nat)
  (hend_pc: nat)
  (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv))
  (actions: list Armada.Action.t)
  (pc_indices: list statement_pc_indices_t)
  : Lemma (requires   efficient_hactions_introducible vs tds inv hpc_to_lpc hstart_pc hend_pc
                        introduction_succeeds_witnesses actions pc_indices
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs
                    /\ action_list_corresponds_to_statement_pc_indices_list hpcs actions pc_indices)
          (ensures  (let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
                     let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                     let inefficient_hpcs = array_to_list hpcs in
                     hactions_introducible vs tds inv inefficient_hpc_to_lpc (make_pc_index_to_pc hpcs hstart_pc)
                       (make_pc_index_to_pc hpcs hend_pc) introduction_succeeds_witnesses actions))
          (decreases introduction_succeeds_witnesses) =
  match introduction_succeeds_witnesses, actions, pc_indices with
  | [], [], [] -> ()
  | first_witness :: remaining_introduction_succeeds_witnesses, first_action :: remaining_actions,
      first_pc_indices :: remaining_pc_indices ->
      assert (find_in_array hpcs (make_pc_index_to_pc hpcs hend_pc) = Some hend_pc);
      assert (find_in_array hpcs (make_pc_index_to_pc hpcs hstart_pc) = Some hstart_pc);
      efficient_hactions_introducible_implies_hactions_introducible vs tds inv lpcs hpcs hpc_info hpc_to_lpc
        is_nonyielding_lpc
        (EfficientThreadStateAtPC?.pc (efficient_action_to_ending_thread_state first_action first_pc_indices))
        hend_pc remaining_introduction_succeeds_witnesses remaining_actions remaining_pc_indices
  | _, _, _ -> ()

#push-options "--z3rlimit 10"

let efficient_introduced_atomic_action_makes_progress_implies_introduced_atomic_action_makes_progress
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hatomic_actions: list (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (hpc: nat{hpc < array_len hpcs})
  (idx: nat)
  (end_pc: nat)
  (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv))
  (progress: nat)
  (hactions: list Armada.Action.t)
  (hpc_indices: list statement_pc_indices_t)
  (lpc: nat)
  (lpc_nonyielding: bool)
  : Lemma (requires   efficient_introduced_atomic_action_makes_progress vs tds inv (list_to_array hatomic_actions)
                        hpc_indices_array hpc_info hpc_to_lpc is_nonyielding_lpc hpc
                    /\ action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs
                    /\ array_nth (list_to_array hatomic_actions) idx == Some hactions
                    /\ array_nth hpc_indices_array idx == Some hpc_indices
                    /\ array_nth hpc_to_lpc hpc = Some lpc
                    /\ array_nth is_nonyielding_lpc lpc = Some lpc_nonyielding
                    /\ efficient_hactions_introducible vs tds inv hpc_to_lpc hpc end_pc
                        introduction_succeeds_witnesses hactions hpc_indices
                    /\ actions_start_atomic_block hactions = not lpc_nonyielding
                    /\ actions_end_atomic_block hactions = not lpc_nonyielding
                    /\ (match array_nth hpc_info end_pc with
                       | Some EfficientHPCInfoNormal -> True
                       | Some (EfficientHPCInfoIntroduced _ _ _ progress') -> progress' < progress))
          (ensures (let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
                    let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                    let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                    let inefficient_hpcs = array_to_list hpcs in
                    let inefficient_hpc = array_index hpcs hpc in
                    let hatomic_actions_array = list_to_array hatomic_actions in
                    let lpc = inefficient_hpc_to_lpc inefficient_hpc in
                    let lpc_yielding = not (inefficient_is_nonyielding_lpc lpc) in
                    let inefficient_end_pc = make_pc_index_to_pc hpcs end_pc in
                    let hpc_indices = array_index hpc_indices_array idx in
                    let lpc = array_index hpc_to_lpc hpc in
                    let lpc_nonyielding = array_index is_nonyielding_lpc lpc in
                    let inefficient_end_pc = array_index hpcs end_pc in
                       hactions_introducible vs tds inv inefficient_hpc_to_lpc inefficient_hpc inefficient_end_pc
                         introduction_succeeds_witnesses hactions
                    /\ actions_start_atomic_block hactions = lpc_yielding
                    /\ actions_end_atomic_block hactions = lpc_yielding
                    /\ (match inefficient_hpc_info inefficient_end_pc with
                       | HPCInfoNormal -> True
                       | HPCInfoIntroduced _ _ _ progress' -> progress' < progress))) =
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_hpc = array_index hpcs hpc in
  let hatomic_actions_array = list_to_array hatomic_actions in
  let lpc = inefficient_hpc_to_lpc inefficient_hpc in
  let lpc_yielding = not (inefficient_is_nonyielding_lpc lpc) in
  let inefficient_end_pc = make_pc_index_to_pc hpcs end_pc in
  let hpc_indices = array_index hpc_indices_array idx in
  let lpc = array_index hpc_to_lpc hpc in
  let lpc_nonyielding = array_index is_nonyielding_lpc lpc in
  let inefficient_end_pc = array_index hpcs end_pc in
  assert (efficient_hactions_introducible vs tds inv hpc_to_lpc hpc end_pc introduction_succeeds_witnesses hactions
            hpc_indices);
  assert (actions_start_atomic_block hactions = not lpc_nonyielding);
  assert (actions_end_atomic_block hactions = not lpc_nonyielding);
  assert (match array_nth hpc_info end_pc with
          | Some EfficientHPCInfoNormal -> True
          | Some (EfficientHPCInfoIntroduced _ _ _ progress') -> progress' < progress);
  assert (find_in_array hpcs inefficient_end_pc = Some end_pc);
  assert (make_pc_index_to_pc hpcs end_pc = inefficient_end_pc);
  assert (find_in_array lpcs (inefficient_hpc_to_lpc inefficient_hpc) = Some lpc);
  efficient_hactions_introducible_implies_hactions_introducible vs tds inv lpcs hpcs hpc_info hpc_to_lpc
    is_nonyielding_lpc hpc end_pc introduction_succeeds_witnesses hactions hpc_indices

let introduced_atomic_action_makes_progress_helper
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hatomic_actions: list (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (hpc: nat{hpc < array_len hpcs})
  : Lemma (requires   efficient_introduced_atomic_action_makes_progress vs tds inv (list_to_array hatomic_actions)
                        hpc_indices_array hpc_info hpc_to_lpc is_nonyielding_lpc hpc
                    /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                        hpc_indices_array 
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  introduced_atomic_action_makes_progress vs tds inv hatomic_actions
                      (make_hpc_info vs tds inv hpcs hpc_info) (make_hpc_to_lpc hpcs lpcs hpc_to_lpc)
                      (make_is_nonyielding_pc lpcs is_nonyielding_lpc) (array_index hpcs hpc)) =
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_hpc = array_index hpcs hpc in
  let hatomic_actions_array = list_to_array hatomic_actions in
  assert (array_index hpcs hpc = inefficient_hpc);
  assert (find_in_array hpcs inefficient_hpc == Some hpc);
  match array_index hpc_info hpc with
  | EfficientHPCInfoNormal -> ()
  | EfficientHPCInfoIntroduced idx end_pc introduction_succeeds_witnesses progress ->
      assert (find_in_array hpcs inefficient_hpc = Some hpc);
      assert (inefficient_hpc_info inefficient_hpc ==
                HPCInfoIntroduced idx (make_pc_index_to_pc hpcs end_pc) introduction_succeeds_witnesses progress);
      (match array_nth hatomic_actions_array idx, array_nth hpc_indices_array idx with
       | Some hactions, Some hpc_indices ->
           list_to_array_implies_nth_equivalent hatomic_actions_array hatomic_actions idx;
           assert (list_nth hatomic_actions idx == Some hactions);
           arrays_correspond_specific_index (action_list_corresponds_to_statement_pc_indices_list hpcs)
             hatomic_actions_array hpc_indices_array idx;
           assert (action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices);
           (match array_nth hpc_to_lpc hpc with
            | Some lpc ->
                (match array_nth is_nonyielding_lpc lpc with
                 | Some lpc_nonyielding ->
                     assert (efficient_hactions_introducible vs tds inv hpc_to_lpc hpc end_pc
                               introduction_succeeds_witnesses hactions hpc_indices);
                     assert (actions_start_atomic_block hactions = not lpc_nonyielding);
                     assert (actions_end_atomic_block hactions = not lpc_nonyielding);
                     assert (match array_nth hpc_info end_pc with
                             | Some EfficientHPCInfoNormal -> True
                             | Some (EfficientHPCInfoIntroduced _ _ _ progress') -> progress' < progress);
                     efficient_introduced_atomic_action_makes_progress_implies_introduced_atomic_action_makes_progress
                       lpcs hpcs vs tds inv hatomic_actions hpc_indices_array hpc_info hpc_to_lpc is_nonyielding_lpc hpc
                       idx end_pc introduction_succeeds_witnesses progress hactions hpc_indices lpc lpc_nonyielding)))

#pop-options

let introduced_atomic_action_makes_progress_lemma
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hatomic_actions: list (list Armada.Action.t))
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  : Lemma (requires   for_all_range_ubool (array_len hpcs)
                        (efficient_introduced_atomic_action_makes_progress vs tds inv (list_to_array hatomic_actions)
                          hpc_indices_array hpc_info hpc_to_lpc is_nonyielding_lpc)
                    /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                        hpc_indices_array
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  for_all_ubool
                      (introduced_atomic_action_makes_progress vs tds inv hatomic_actions
                        (make_hpc_info vs tds inv hpcs hpc_info) (make_hpc_to_lpc hpcs lpcs hpc_to_lpc)
                        (make_is_nonyielding_pc lpcs is_nonyielding_lpc))
                      (array_to_list hpcs)) =
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_hpcs = array_to_list hpcs in
  introduce forall inefficient_hpc. list_contains inefficient_hpc inefficient_hpcs ==>
               introduced_atomic_action_makes_progress vs tds inv hatomic_actions inefficient_hpc_info
                 inefficient_hpc_to_lpc inefficient_is_nonyielding_lpc inefficient_hpc
  with introduce list_contains inefficient_hpc inefficient_hpcs ==>
                   introduced_atomic_action_makes_progress vs tds inv hatomic_actions inefficient_hpc_info
                     inefficient_hpc_to_lpc inefficient_is_nonyielding_lpc inefficient_hpc
  with _. (
    let hpc = contains_to_index inefficient_hpc inefficient_hpcs in
    let hatomic_actions_array = list_to_array hatomic_actions in
    assert (efficient_introduced_atomic_action_makes_progress vs tds inv hatomic_actions_array
              hpc_indices_array hpc_info hpc_to_lpc is_nonyielding_lpc hpc);
    assert (array_index hpcs hpc = inefficient_hpc);
    assert (find_in_array hpcs inefficient_hpc == Some hpc);
    introduced_atomic_action_makes_progress_helper lpcs hpcs vs tds inv hatomic_actions hpc_indices_array
      hpc_info hpc_to_lpc is_nonyielding_lpc hpc
   )

let efficient_laction_corresponds_to_haction_preservation
  (vs: list var_id_t)
  (tds: list object_td_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (laction: Armada.Action.t)
  (haction: Armada.Action.t)
  (lpc_indices: statement_pc_indices_t)
  (hpc_indices: statement_pc_indices_t)
  : Lemma (requires (let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
                     let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
                       efficient_laction_corresponds_to_haction vs pc_relation pc_return_relation laction haction
                         lpc_indices hpc_indices
                     /\ action_corresponds_to_statement_pc_indices lpcs laction lpc_indices
                     /\ action_corresponds_to_statement_pc_indices hpcs haction hpc_indices
                     /\ array_elements_unique hpcs))
          (ensures  (let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
                     laction_corresponds_to_haction vs inefficient_hpc_to_lpc inefficient_return_hpcs laction
                       haction)) =
  let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
  let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let lps, hps = laction.program_statement, haction.program_statement in
  let relation = lpc_hpc_pc_relation inefficient_hpc_to_lpc in
  let return_relation = lpc_hpc_pc_return_relation inefficient_hpc_to_lpc inefficient_return_hpcs in
  assert (efficient_program_statements_match_per_pc_relation pc_relation pc_return_relation lps hps lpc_indices
            hpc_indices);
  lpc_hpc_relation_facts lpcs hpcs hpc_to_lpc is_return_hpc;
  efficient_program_statements_match_per_pc_relation_implies_program_statements_match_per_pc_relation lpcs hpcs
    pc_relation pc_return_relation relation return_relation lps hps lpc_indices hpc_indices;
  assert (program_statements_match_per_pc_relation relation return_relation lps hps)

let efficient_thread_states_match_per_pc_relation_implies_thread_states_match_per_pc_relation
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (lts: efficient_thread_state_t)
  (hts: efficient_thread_state_t)
  : Lemma (requires (let index_relation = efficient_hl_pc_relation hpc_to_lpc in
                       efficient_thread_states_match_per_pc_relation index_relation lts hts
                     /\ array_elements_unique hpcs))
          (ensures  (let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let pc_relation = lpc_hpc_pc_relation inefficient_hpc_to_lpc in
                     thread_states_match_per_pc_relation pc_relation
                       (convert_efficient_thread_state lpcs lts)
                       (convert_efficient_thread_state hpcs hts)))
          [SMTPat (thread_states_match_per_pc_relation (lpc_hpc_pc_relation (make_hpc_to_lpc hpcs lpcs hpc_to_lpc))
                    (convert_efficient_thread_state lpcs lts) (convert_efficient_thread_state hpcs hts))] =
  ()

let efficient_start_pc_of_actions_preservation
  (pcs: array_t pc_t)
  (actions: list Armada.Action.t)
  (pc_indices: list statement_pc_indices_t)
  : Lemma (requires action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices)
          (ensures  (let oidx = efficient_start_pc_of_actions pc_indices in
                     let opc = start_pc_of_actions actions in
                     match oidx, opc with
                     | None, None -> True
                     | Some idx, Some pc -> Some pc = array_nth pcs idx
                     | _, _ -> False))
          [SMTPat (start_pc_of_actions actions);
           SMTPat (action_list_corresponds_to_statement_pc_indices_list pcs actions pc_indices)] =
  ()

let invert_make_pc_indices_to_pcs
  (pcs: array_t pc_t)
  (pc_indices: list nat{forall idx. list_contains idx pc_indices ==> idx < array_len pcs})
  (pc: pc_t{list_contains pc (make_pc_indices_to_pcs pcs pc_indices)})
  : GTot (idx: nat{list_contains idx pc_indices /\ array_nth pcs idx = Some pc}) =
  reverse_map_element_of_map_ghost (make_pc_index_to_pc pcs) pc_indices pc

let invert_make_lpc_to_hpcs
  (hpcs: array_t pc_t)
  (lpcs: array_t pc_t)
  (lpc_to_hpcs: array_t (list nat){
       array_len lpc_to_hpcs = array_len lpcs
     /\ efficient_lpc_to_hpcs_contain_valid_indices (array_len hpcs) lpc_to_hpcs})
  (lpc: pc_t)
  (hpc: pc_t{list_contains hpc (make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs lpc)})
  : GTot (idx: nat{array_nth hpcs idx = Some hpc}) =
  match find_in_array lpcs lpc with
  | None -> false_elim ()
  | Some lpc_index ->
     let hpc_indices = array_index lpc_to_hpcs lpc_index in
     assert (list_contains hpc (make_pc_indices_to_pcs hpcs hpc_indices));
     invert_make_pc_indices_to_pcs hpcs hpc_indices hpc

#push-options "--z3rlimit 20"

let efficient_laction_haction_correspondence_complete_preservation
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  (is_breaking_hpc: array_t bool{array_len is_breaking_hpc = array_len hpcs})
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : Lemma (requires   efficient_laction_haction_correspondence_complete vs tds inv lpc_to_hpcs is_breaking_hpc
                        hpc_info lpc_indices hpc_indices
                    /\ action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices
                    /\ action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices
                    /\ efficient_lpc_to_hpcs_contain_valid_indices (array_len hpcs) lpc_to_hpcs
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs)
          (ensures  (let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
                     let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
                     let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
                     laction_haction_correspondence_complete vs tds inv inefficient_lpc_to_hpcs
                       inefficient_is_breaking_hpc inefficient_hpc_info lactions hactions)) =
  let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
  let opt_start_lpc = start_pc_of_actions lactions in
  let opt_start_hpc = start_pc_of_actions hactions in
  match opt_start_lpc, opt_start_hpc with
  | None, None -> ()
  | Some start_lpc, Some start_hpc ->
      introduce forall hpc. list_contains hpc (inefficient_lpc_to_hpcs start_lpc) ==>
                       laction_haction_correspondence_complete_inner vs tds inv inefficient_is_breaking_hpc
                         inefficient_hpc_info start_hpc hpc
      with introduce _ ==> _
      with _. (
        match efficient_start_pc_of_actions lpc_indices, efficient_start_pc_of_actions hpc_indices with
        | Some start_lpc_index, Some start_hpc_index ->
            let hpc_index = invert_make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs start_lpc hpc in
            (match array_nth lpc_to_hpcs start_lpc_index with
             | Some indices ->
                 assert (inefficient_lpc_to_hpcs start_lpc == make_pc_indices_to_pcs hpcs indices);
                 make_pc_indices_to_pcs_contains_pc_implies_pc_indices_contains_index hpcs indices hpc hpc_index)
      )
  | _, _ -> ()

#pop-options

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

let rec efficient_lactions_correspond_to_hactions_preservation
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (lstart_state: efficient_thread_state_t)
  (hstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (hend_state: efficient_thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : Lemma (requires (let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
                     let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
                       efficient_lactions_correspond_to_hactions vs tds inv pc_relation pc_return_relation
                         lstart_state hstart_state lend_state hend_state mapper lactions hactions
                         lpc_indices hpc_indices
                     /\ action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices
                     /\ action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices
                     /\ array_elements_unique lpcs
                     /\ array_elements_unique hpcs))
          (ensures  (let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
                     let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
                     let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
                     let inefficient_hstart_state = convert_efficient_thread_state hpcs hstart_state in
                     let inefficient_hend_state = convert_efficient_thread_state hpcs hend_state in
                     lactions_correspond_to_hactions vs tds inv inefficient_hpc_to_lpc inefficient_return_hpcs
                       inefficient_lstart_state inefficient_hstart_state inefficient_lend_state
                       inefficient_hend_state mapper lactions hactions))
          (decreases hactions) =
  let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
  let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let inefficient_lstart_state = convert_efficient_thread_state lpcs lstart_state in
  let inefficient_lend_state = convert_efficient_thread_state lpcs lend_state in
  let inefficient_hstart_state = convert_efficient_thread_state hpcs hstart_state in
  let inefficient_hend_state = convert_efficient_thread_state hpcs hend_state in
  let relation = fun lpc hpc -> inefficient_hpc_to_lpc hpc = lpc in
  lpc_hpc_relation_facts lpcs hpcs hpc_to_lpc is_return_hpc;
  match mapper, lactions, hactions, lpc_indices, hpc_indices with
  | [], [], [], [], [] -> ()
  | MapperMatching :: remaining_mapper, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lpc_indices :: remaining_lpc_indices, first_hpc_indices :: remaining_hpc_indices ->
      efficient_laction_corresponds_to_haction_preservation vs tds lpcs hpcs hpc_to_lpc is_return_hpc
        first_laction first_haction first_lpc_indices first_hpc_indices;
      efficient_lactions_correspond_to_hactions_preservation vs tds inv lpcs hpcs hpc_to_lpc is_return_hpc
        (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
        (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
        lend_state hend_state remaining_mapper remaining_lactions remaining_hactions
        remaining_lpc_indices remaining_hpc_indices
  | MapperIntroduced witness :: remaining_mapper, _, first_haction :: remaining_hactions, _,
      first_hpc_indices :: remaining_hpc_indices ->
      efficient_lactions_correspond_to_hactions_preservation vs tds inv lpcs hpcs hpc_to_lpc is_return_hpc
        lstart_state (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
        lend_state hend_state remaining_mapper lactions remaining_hactions lpc_indices
        remaining_hpc_indices
  | _, _, _, _, _ -> false_elim ()

#push-options "--z3rlimit 20"

let efficient_corresponding_hactions_info_correct_inner_preservation
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (latomic_actions: list (list Armada.Action.t))
  (hatomic_actions: list (list Armada.Action.t))
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (is_breaking_hpc: array_t bool{array_len is_breaking_hpc = array_len hpcs})
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv)
    {array_len corresponding_hactions_info = list_len latomic_actions})
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (correspondence: ltoh_correspondence_t vs tds inv)
  (laction_idx: nat{laction_idx < list_len latomic_actions})
  : Lemma (requires (let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
                     let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
                       efficient_corresponding_hactions_info_correct_inner vs tds inv (list_to_array latomic_actions)
                         (list_to_array hatomic_actions) lpc_to_hpcs is_breaking_hpc hpc_info
                         corresponding_hactions_info lpc_indices_array hpc_indices_array pc_relation
                         pc_return_relation laction_idx
                     /\ efficient_lpc_to_hpcs_contain_valid_indices (array_len hpcs) lpc_to_hpcs
                     /\ array_elements_unique lpcs
                     /\ array_elements_unique hpcs
                     /\ actions_array_corresponds_to_statement_pc_indices_array lpcs (list_to_array latomic_actions)
                         lpc_indices_array
                     /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                         hpc_indices_array
                     /\ array_nth corresponding_hactions_info laction_idx == Some correspondence))
          (ensures  (let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
                     let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                     let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
                     let inefficient_hpcs = array_to_list hpcs in
                     let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
                     let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
                     let lactions = list_index latomic_actions laction_idx in
                     lactions_correspond_to_hactions_per_correspondence vs tds inv
                       inefficient_hpc_to_lpc inefficient_lpc_to_hpcs inefficient_return_hpcs
                       inefficient_is_breaking_hpc inefficient_hpc_info hatomic_actions lactions
                       correspondence)) =
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
  let latomic_actions_array = list_to_array latomic_actions in
  let hatomic_actions_array = list_to_array hatomic_actions in
  let ltoh_info = array_index corresponding_hactions_info laction_idx in
  list_to_array_implies_index_equivalent latomic_actions_array latomic_actions laction_idx;
  assert (list_index latomic_actions laction_idx == array_index latomic_actions_array laction_idx);
  let lactions = array_index latomic_actions_array laction_idx in
  let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
  let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
  assert (efficient_corresponding_hactions_info_correct_inner vs tds inv latomic_actions_array
            hatomic_actions_array lpc_to_hpcs is_breaking_hpc hpc_info corresponding_hactions_info
            lpc_indices_array hpc_indices_array pc_relation pc_return_relation laction_idx);
  let lpc_indices = array_index lpc_indices_array laction_idx in
  assert (action_list_corresponds_to_statement_pc_indices_list lpcs lactions lpc_indices);
  let correspondence = array_index corresponding_hactions_info laction_idx in
  match correspondence with
  | CorrespondencePropagate hidx ->
      list_to_array_implies_nth_equivalent hatomic_actions_array hatomic_actions hidx;
      let hactions = array_index hatomic_actions_array hidx in
      assert (Some hactions == list_nth hatomic_actions hidx)
  | CorrespondenceNormal hidx mapper ->
      list_to_array_implies_nth_equivalent hatomic_actions_array hatomic_actions hidx;
      (match array_nth hatomic_actions_array hidx, array_nth hpc_indices_array hidx with
       | Some hactions, Some hpc_indices ->
           assert (Some hactions == list_nth hatomic_actions hidx);
           assert (action_list_corresponds_to_statement_pc_indices_list hpcs hactions hpc_indices);
           let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
           let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
           let hstart_state = efficient_action_to_starting_thread_state (Cons?.hd hpc_indices) in
           let hend_state = efficient_actions_to_ending_thread_state hactions hpc_indices in
           assert (do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions);
           efficient_lactions_correspond_to_hactions_preservation vs tds inv lpcs hpcs hpc_to_lpc is_return_hpc
             lstart_state hstart_state lend_state hend_state
             mapper lactions hactions lpc_indices hpc_indices;
           efficient_laction_haction_correspondence_complete_preservation vs tds inv lpcs hpcs lpc_to_hpcs
             is_breaking_hpc hpc_info lactions hactions lpc_indices hpc_indices;
           assert (lactions_correspond_to_hactions_per_correspondence vs tds inv
                     inefficient_hpc_to_lpc inefficient_lpc_to_hpcs inefficient_return_hpcs
                     inefficient_is_breaking_hpc inefficient_hpc_info hatomic_actions lactions
                     correspondence))

let corresponding_hactions_info_correct_lemma
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (latomic_actions: list (list Armada.Action.t))
  (hatomic_actions: list (list Armada.Action.t))
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat{array_len hpc_to_lpc = array_len hpcs})
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv){array_len hpc_info = array_len hpcs})
  (is_nonyielding_lpc: array_t bool{array_len is_nonyielding_lpc = array_len lpcs})
  (is_breaking_hpc: array_t bool{array_len is_breaking_hpc = array_len hpcs})
  (lpc_to_hpcs: array_t (list nat){array_len lpc_to_hpcs = array_len lpcs})
  (is_return_hpc: array_t bool{array_len is_return_hpc = array_len hpcs})
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv)
    {array_len corresponding_hactions_info = list_len latomic_actions})
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  : Lemma (requires   efficient_corresponding_hactions_info_correct vs tds inv (list_to_array latomic_actions)
                        (list_to_array hatomic_actions) hpc_to_lpc lpc_to_hpcs is_return_hpc is_breaking_hpc
                        hpc_info corresponding_hactions_info lpc_indices_array hpc_indices_array
                    /\ efficient_lpc_to_hpcs_contain_valid_indices (array_len hpcs) lpc_to_hpcs
                    /\ array_elements_unique lpcs
                    /\ array_elements_unique hpcs
                    /\ actions_array_corresponds_to_statement_pc_indices_array lpcs (list_to_array latomic_actions)
                        lpc_indices_array
                    /\ actions_array_corresponds_to_statement_pc_indices_array hpcs (list_to_array hatomic_actions)
                        hpc_indices_array
                    /\ array_len corresponding_hactions_info = array_len (list_to_array latomic_actions))
          (ensures  (let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
                     let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
                     let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
                     let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
                     let inefficient_hpcs = array_to_list hpcs in
                     let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
                     let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
                     lists_correspond_ubool
                       (lactions_correspond_to_hactions_per_correspondence vs tds inv
                          inefficient_hpc_to_lpc inefficient_lpc_to_hpcs inefficient_return_hpcs
                          inefficient_is_breaking_hpc inefficient_hpc_info hatomic_actions)
                       latomic_actions (array_to_list corresponding_hactions_info))) =
  let inefficient_hpc_info = make_hpc_info vs tds inv hpcs hpc_info in
  let inefficient_hpc_to_lpc = make_hpc_to_lpc hpcs lpcs hpc_to_lpc in
  let inefficient_is_nonyielding_lpc = make_is_nonyielding_pc lpcs is_nonyielding_lpc in
  let inefficient_is_breaking_hpc = make_is_breaking_pc hpcs is_breaking_hpc in
  let inefficient_hpcs = array_to_list hpcs in
  let inefficient_return_hpcs = make_return_pcs hpcs is_return_hpc in
  let inefficient_lpc_to_hpcs = make_lpc_to_hpcs hpcs lpcs lpc_to_hpcs in
  let inefficient_corresponding_hactions_info = array_to_list corresponding_hactions_info in
  let latomic_actions_array = list_to_array latomic_actions in
  let hatomic_actions_array = list_to_array hatomic_actions in
  list_to_array_implies_length_equivalent latomic_actions_array latomic_actions;
  assert (list_len latomic_actions = array_len corresponding_hactions_info);
  introduce forall laction_idx. laction_idx < list_len latomic_actions ==>
               lactions_correspond_to_hactions_per_correspondence vs tds inv
                 inefficient_hpc_to_lpc inefficient_lpc_to_hpcs inefficient_return_hpcs
                 inefficient_is_breaking_hpc inefficient_hpc_info hatomic_actions
                 (list_index latomic_actions laction_idx)
                 (list_index inefficient_corresponding_hactions_info laction_idx)
  with introduce _ ==> _
  with _. (
    let ltoh_info = array_index corresponding_hactions_info laction_idx in
    list_to_array_implies_index_equivalent latomic_actions_array latomic_actions laction_idx;
    assert (list_index latomic_actions laction_idx == array_index latomic_actions_array laction_idx);
    let lactions = array_index latomic_actions_array laction_idx in
    let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
    let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
    assert (efficient_corresponding_hactions_info_correct_inner vs tds inv latomic_actions_array
              hatomic_actions_array lpc_to_hpcs is_breaking_hpc hpc_info corresponding_hactions_info
              lpc_indices_array hpc_indices_array pc_relation pc_return_relation laction_idx);
    let lpc_indices = array_index lpc_indices_array laction_idx in
    let hactions_info = array_index corresponding_hactions_info laction_idx in
    assert (efficient_lactions_correspond_to_hactions_per_correspondence vs tds inv pc_relation pc_return_relation
              lpc_to_hpcs is_breaking_hpc hpc_info hatomic_actions_array hpc_indices_array lactions lpc_indices
              hactions_info);
    let correspondence = array_index corresponding_hactions_info laction_idx in
    efficient_corresponding_hactions_info_correct_inner_preservation vs tds inv latomic_actions hatomic_actions
      lpcs hpcs hpc_to_lpc hpc_info is_nonyielding_lpc is_breaking_hpc lpc_to_hpcs is_return_hpc
      corresponding_hactions_info lpc_indices_array hpc_indices_array correspondence laction_idx
  );
  establish_lists_correspond_ubool_from_index_correspondence
    (lactions_correspond_to_hactions_per_correspondence vs tds inv
       inefficient_hpc_to_lpc inefficient_lpc_to_hpcs inefficient_return_hpcs
       inefficient_is_breaking_hpc inefficient_hpc_info hatomic_actions)
    latomic_actions inefficient_corresponding_hactions_info

#pop-options

let efficient_var_intro_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (evw: efficient_var_intro_witness_t)
  (* see .fsti file for spec *) =
  let vw: var_intro_witness_t = {
    lprog = evw.lprog;
    hprog = evw.hprog;
    vs = evw.vs;
    tds = evw.tds;
    inv = evw.inv;
    which_initializers_are_intros = evw.which_initializers_are_intros;
    hpc_to_lpc = make_hpc_to_lpc evw.hpcs evw.lpcs evw.hpc_to_lpc;
    lpc_to_hpcs = make_lpc_to_hpcs evw.hpcs evw.lpcs evw.lpc_to_hpcs;
    return_hpcs = make_return_pcs evw.hpcs evw.is_return_hpc;
    is_nonyielding_lpc = make_is_nonyielding_pc evw.lpcs evw.is_nonyielding_lpc;
    is_nonyielding_hpc = make_is_nonyielding_pc evw.hpcs evw.is_nonyielding_hpc;
    is_breaking_hpc = make_is_breaking_pc evw.hpcs evw.is_breaking_hpc;
    hpcs = array_to_list evw.hpcs;
    hpc_info = make_hpc_info evw.vs evw.tds evw.inv evw.hpcs evw.hpc_info;
    corresponding_hactions_info = array_to_list evw.corresponding_hactions_info;
  } in
  program_inits_match_except_global_variables_lemma evw.vs evw.lpcs evw.hpcs evw.hpc_to_lpc
    evw.which_initializers_are_intros evw.lprog evw.hprog evw.lprog_main_start_pc_index evw.hprog_main_start_pc_index;
  assert (vw.is_breaking_hpc vw.hprog.main_start_pc);
  assert (initializers_with_same_variable_id_match vw.hprog.global_initializers);
  assert (vw.hpc_to_lpc vw.hprog.main_start_pc = vw.lprog.main_start_pc);
  hstart_pc_among_hpcs_lemma evw.hpcs evw.hprog evw.hprog_main_start_pc_index;
  assert (list_contains vw.hprog.main_start_pc vw.hpcs);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers);
  assert (global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers);
  assert (every_variable_appears_among_initializers vw.hprog.global_initializers vw.vs vw.tds);
  pcs_contain_new_pcs_of_action_lemma hatomic_prog evw.hprog_actions_array evw.hpc_indices_array evw.hpcs;
  assert (for_all_ghost (for_all_ghost (pcs_contain_new_pcs_of_action vw.hpcs)) hatomic_prog.actions);
  every_hpc_appears_among_lpc_to_hpcs_lemma evw.lpcs evw.hpcs evw.hpc_to_lpc evw.lpc_to_hpcs;
  assert (every_hpc_appears_among_lpc_to_hpcs vw.lpc_to_hpcs vw.hpc_to_lpc vw.hpcs);
  return_pcs_unique_lemma evw.hpcs evw.lpcs evw.hpc_to_lpc evw.is_return_hpc evw.lpc_to_hpcs;
  assert (return_pcs_unique vw.hpc_to_lpc vw.return_hpcs);
  each_action_list_consistent_with_is_nonyielding_pc_lemma evw.lpcs evw.is_nonyielding_lpc latomic_prog.actions
    evw.lpc_indices_array;
  assert (each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc latomic_prog.actions);
  each_action_list_consistent_with_is_nonyielding_pc_lemma evw.hpcs evw.is_nonyielding_hpc hatomic_prog.actions
    evw.hpc_indices_array;
  assert (each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc hatomic_prog.actions);
  each_action_list_maintains_all_threads_breaking_lemma evw.hpcs evw.is_breaking_hpc hatomic_prog.actions
    evw.hpc_indices_array;
  assert (each_action_list_maintains_all_threads_breaking vw.is_breaking_hpc hatomic_prog.actions);
  assert (each_action_list_doesnt_internally_yield latomic_prog.actions);
  assert (each_action_list_doesnt_internally_yield hatomic_prog.actions);
  introduced_atomic_action_makes_progress_lemma evw.vs evw.tds evw.inv hatomic_prog.actions evw.lpcs evw.hpcs
    evw.hpc_to_lpc evw.hpc_info evw.is_nonyielding_lpc evw.lpc_to_hpcs evw.is_return_hpc evw.hpc_indices_array;
  assert (for_all_ubool (introduced_atomic_action_makes_progress vw.vs vw.tds vw.inv hatomic_prog.actions
                          vw.hpc_info vw.hpc_to_lpc vw.is_nonyielding_lpc) vw.hpcs);
  corresponding_hactions_info_correct_lemma evw.vs evw.tds evw.inv latomic_prog.actions hatomic_prog.actions
    evw.lpcs evw.hpcs evw.hpc_to_lpc evw.hpc_info evw.is_nonyielding_lpc evw.is_breaking_hpc evw.lpc_to_hpcs
    evw.is_return_hpc evw.corresponding_hactions_info evw.lpc_indices_array evw.hpc_indices_array;
  assert (lists_correspond_ubool
           (lactions_correspond_to_hactions_per_correspondence vw.vs vw.tds vw.inv
              vw.hpc_to_lpc vw.lpc_to_hpcs vw.return_hpcs vw.is_breaking_hpc vw.hpc_info hatomic_prog.actions)
           latomic_prog.actions vw.corresponding_hactions_info);
  assert (var_intro_witness_valid latomic_prog hatomic_prog vw);
  var_intro_witness_valid_implies_refinement latomic_prog hatomic_prog vw
