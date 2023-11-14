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
open Strategies.ArmadaStatement.Propagate
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Util.ImmutableArray
open Util.List
open Util.Nth
open Util.Range
open Util.Relation

let efficient_program_inits_match_except_global_variables
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (lpc_to_hpc: array_t nat)
  (which_initializers_are_hidings: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  (lprog_main_start_pc: nat)
  (hprog_main_start_pc: nat)
  : GTot ubool =
    lprog.main_method_id = hprog.main_method_id
  /\ array_nth lpc_to_hpc lprog_main_start_pc = Some hprog_main_start_pc
  /\ array_nth lpcs lprog_main_start_pc = Some lprog.main_start_pc
  /\ array_nth hpcs hprog_main_start_pc = Some hprog.main_start_pc
  /\ initializers_match_except_global_variables vs which_initializers_are_hidings
       lprog.global_initializers hprog.global_initializers
  /\ lprog.main_stack_initializers == hprog.main_stack_initializers

let efficient_lpc_to_hpc_contains_valid_indices
  (num_hpcs: nat)
  (lpc_to_hpc: array_t nat)
  : GTot bool =
  for_all_array (fun (hidx: nat) -> hidx < num_hpcs) lpc_to_hpc

let efficient_lh_pc_relation (lpc_to_hpc: array_t nat) : GTot (relation_t nat nat) =
  fun lidx hidx -> array_nth lpc_to_hpc lidx = Some hidx

let efficient_lh_pc_return_relation (lpc_to_hpc: array_t nat) (is_return_lpc: array_t bool) : GTot (relation_t nat nat) =
  fun lidx hidx -> array_nth lpc_to_hpc lidx = Some hidx && array_nth is_return_lpc lidx = Some true

let rec efficient_lactions_all_hidden
  (vs: list var_id_t)
  (lpc_to_hpc: array_t nat)
  (lstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (lactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  : GTot ubool
  (decreases lactions) =
  match lactions, lpc_indices with
  | [], [] -> lend_state = lstart_state
  | first_laction :: remaining_lactions, first_lpc_indices :: remaining_lpc_indices ->
         efficient_action_to_starting_thread_state first_lpc_indices = lstart_state
      /\ (match lstart_state, efficient_action_to_ending_thread_state first_laction first_lpc_indices with
         | EfficientThreadStateAtPC lpc1, EfficientThreadStateAtPC lpc2 ->
             array_nth lpc_to_hpc lpc1 = array_nth lpc_to_hpc lpc2
         | _, _ -> False)
      /\ statement_updates_gvars vs first_laction.program_statement.statement
      /\ efficient_lactions_all_hidden vs lpc_to_hpc
           (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
           lend_state remaining_lactions remaining_lpc_indices
  | _, _ -> False

let efficient_laction_corresponds_to_haction
  (vs: list var_id_t)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (laction: Armada.Action.t)
  (haction: Armada.Action.t)
  (lpc_indices: statement_pc_indices_t)
  (hpc_indices: statement_pc_indices_t)
  : GTot ubool =
  let lps, hps = laction.program_statement, haction.program_statement in
    statement_effect_independent_of_global_variables vs lps.statement
  /\ efficient_program_statements_match_per_pc_relation pc_relation pc_return_relation lps hps lpc_indices hpc_indices

let rec efficient_lactions_correspond_to_hactions
  (vs: list var_id_t)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (lstart_state: efficient_thread_state_t)
  (hstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (hend_state: efficient_thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : GTot ubool
  (decreases lactions) =
  match which_actions_hidden, lactions, hactions, lpc_indices, hpc_indices with
  | [], [], [], [], [] ->
        lend_state = lstart_state
      /\ hend_state = hstart_state
  | false :: remaining_which_actions_hidden, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lpc_indices :: remaining_lpc_indices, first_hpc_indices :: remaining_hpc_indices ->
        efficient_laction_corresponds_to_haction vs pc_relation pc_return_relation first_laction first_haction
          first_lpc_indices first_hpc_indices
      /\ efficient_action_to_starting_thread_state first_lpc_indices = lstart_state
      /\ efficient_action_to_starting_thread_state first_hpc_indices = hstart_state
      /\ EfficientThreadStateAtPC? lstart_state
      /\ EfficientThreadStateAtPC? hstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation lstart_state hstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation
          (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
          (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
      /\ efficient_lactions_correspond_to_hactions vs pc_relation pc_return_relation
          (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
          (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
          lend_state hend_state remaining_which_actions_hidden remaining_lactions remaining_hactions
          remaining_lpc_indices remaining_hpc_indices
  | true :: remaining_which_actions_hidden, first_laction :: remaining_lactions, _,
      first_lpc_indices :: remaining_lpc_indices, _ ->
        efficient_action_to_starting_thread_state first_lpc_indices = lstart_state
      /\ EfficientThreadStateAtPC? lstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation lstart_state hstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation
          (efficient_action_to_ending_thread_state first_laction first_lpc_indices) hstart_state
      /\ statement_updates_gvars vs first_laction.program_statement.statement
      /\ efficient_lactions_correspond_to_hactions vs pc_relation pc_return_relation
           (efficient_action_to_ending_thread_state first_laction first_lpc_indices) hstart_state lend_state hend_state
           remaining_which_actions_hidden remaining_lactions hactions remaining_lpc_indices hpc_indices
  | _, _, _, _, _ -> False

let efficient_lactions_correspond_to_hactions_per_correspondence
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpc_to_hpc: array_t nat)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (hatomic_actions_array: array_t (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (lactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (correspondence: ltoh_correspondence_t vs tds inv)
  : GTot ubool =
  match correspondence with
  | CorrespondenceHidden ->
        Cons? lactions
      /\ Cons? lpc_indices
      /\ actions_start_atomic_block lactions = actions_end_atomic_block lactions
      /\ (let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
         let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
         efficient_lactions_all_hidden vs lpc_to_hpc lstart_state lend_state lactions lpc_indices)
  | CorrespondencePropagate hidx ->
        Cons? lactions
      /\ (Cons?.hd lactions).program_statement == propagate_program_statement
      /\ array_nth hatomic_actions_array hidx == Some lactions
  | CorrespondenceNormal hidx which_actions_hidden ->
      (match array_nth hatomic_actions_array hidx, array_nth hpc_indices_array hidx with
       | Some hactions, Some hpc_indices ->
             Cons? lactions
           /\ Cons? lpc_indices
           /\ Cons? hactions
           /\ Cons? hpc_indices
           /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
           /\ (let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
              let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
              let hstart_state = efficient_action_to_starting_thread_state (Cons?.hd hpc_indices) in
              let hend_state = efficient_actions_to_ending_thread_state hactions hpc_indices in
              efficient_lactions_correspond_to_hactions vs pc_relation pc_return_relation lstart_state hstart_state
               lend_state hend_state which_actions_hidden lactions hactions lpc_indices hpc_indices)
       | _, _ -> False)
  | CorrespondenceImpossibleConstantAssignmentFailure ->
        Cons? lactions
      /\ ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement)
      /\ lactions_fail_final_statement_updating_gvars_using_constant vs tds lactions
  | CorrespondenceImpossibleStatementFailure ps proof ->
        Cons? lactions
      /\ ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement)
      /\ lactions_fail_specific_final_statement ps lactions

let efficient_return_lpcs_unique_inner2
  (lpc_to_hpc: array_t nat)
  (is_return_lpc: array_t bool)
  (lpc1: nat)
  (lpc2: nat)
  : GTot bool =
   implies (   array_nth is_return_lpc lpc2 = Some true
            && array_nth lpc_to_hpc lpc1 = array_nth lpc_to_hpc lpc2)
           (lpc1 = lpc2)

let efficient_return_lpcs_unique_inner1
  (num_lpcs: nat)
  (lpc_to_hpc: array_t nat)
  (is_return_lpc: array_t bool)
  (lpc1: nat)
  : GTot bool =
  implies (array_nth is_return_lpc lpc1 = Some true)
          (for_all_range num_lpcs (efficient_return_lpcs_unique_inner2 lpc_to_hpc is_return_lpc lpc1))

let efficient_return_lpcs_unique
  (num_lpcs: nat)
  (lpc_to_hpc: array_t nat)
  (is_return_lpc: array_t bool)
  : GTot bool =
  for_all_range num_lpcs (efficient_return_lpcs_unique_inner1 num_lpcs lpc_to_hpc is_return_lpc)

let efficient_corresponding_hactions_info_correct_inner
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lprog_actions_array: array_t (list Armada.Action.t))
  (hprog_actions_array: array_t (list Armada.Action.t))
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv))
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (lpc_to_hpc: array_t nat)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (idx: nat)
  : GTot ubool =
  match array_nth lprog_actions_array idx, array_nth lpc_indices_array idx,
          array_nth corresponding_hactions_info idx with
  | Some lactions, Some lpc_indices, Some hactions_info ->
      efficient_lactions_correspond_to_hactions_per_correspondence vs tds inv lpc_to_hpc pc_relation pc_return_relation
        hprog_actions_array hpc_indices_array lactions lpc_indices hactions_info
  | _, _, _ -> False

let efficient_corresponding_hactions_info_correct
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lprog_actions_array: array_t (list Armada.Action.t))
  (hprog_actions_array: array_t (list Armada.Action.t))
  (lpc_to_hpc: array_t nat)
  (is_return_lpc: array_t bool)
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv))
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  : GTot ubool =
  let pc_relation = efficient_lh_pc_relation lpc_to_hpc in
  let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in
  for_all_range_ubool (array_len lprog_actions_array)
    (efficient_corresponding_hactions_info_correct_inner vs tds inv lprog_actions_array hprog_actions_array
       corresponding_hactions_info lpc_indices_array hpc_indices_array lpc_to_hpc pc_relation
       pc_return_relation)

noeq type efficient_var_hiding_witness_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  lprog_actions_array: array_t (list Armada.Action.t);
  hprog_actions_array: array_t (list Armada.Action.t);
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_hidings: list bool;
  lpcs: array_t pc_t;
  hpcs: array_t pc_t;
  lpc_to_hpc: array_t nat;
  is_return_lpc: array_t bool;
  is_nonyielding_lpc: array_t bool;
  is_nonyielding_hpc: array_t bool;
  corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv);
  lprog_main_start_pc_index: nat;
  hprog_main_start_pc_index: nat;
  lpc_indices_array: array_t (list statement_pc_indices_t);
  hpc_indices_array: array_t (list statement_pc_indices_t);
}

let efficient_var_hiding_witness_valid
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: efficient_var_hiding_witness_t)
  : GTot ubool =
    array_len vw.lpc_to_hpc = array_len vw.lpcs
  /\ array_len vw.is_return_lpc = array_len vw.lpcs
  /\ array_len vw.is_nonyielding_lpc = array_len vw.lpcs
  /\ array_len vw.is_nonyielding_hpc = array_len vw.hpcs
  /\ array_len vw.corresponding_hactions_info = array_len vw.lprog_actions_array
  /\ array_len vw.lpc_indices_array = array_len vw.lprog_actions_array
  /\ array_len vw.hpc_indices_array = array_len vw.hprog_actions_array
  /\ array_elements_unique vw.lpcs
  /\ array_elements_unique vw.hpcs
  /\ efficient_program_inits_match_except_global_variables vw.vs vw.lpcs vw.hpcs vw.lpc_to_hpc
      vw.which_initializers_are_hidings vw.lprog vw.hprog vw.lprog_main_start_pc_index vw.hprog_main_start_pc_index
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers
  /\ every_variable_appears_among_initializers vw.lprog.global_initializers vw.vs vw.tds
  /\ actions_array_corresponds_to_statement_pc_indices_array vw.lpcs vw.lprog_actions_array vw.lpc_indices_array
  /\ actions_array_corresponds_to_statement_pc_indices_array vw.hpcs vw.hprog_actions_array vw.hpc_indices_array
  /\ efficient_lpc_to_hpc_contains_valid_indices (array_len vw.hpcs) vw.lpc_to_hpc
  /\ efficient_return_lpcs_unique (array_len vw.lpcs) vw.lpc_to_hpc vw.is_return_lpc
  /\ efficient_each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc vw.lprog_actions_array
      vw.lpc_indices_array
  /\ efficient_each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc vw.hprog_actions_array
      vw.hpc_indices_array
  /\ each_action_list_doesnt_internally_yield latomic_prog.actions
  /\ each_action_list_doesnt_internally_yield hatomic_prog.actions
  /\ each_action_list_ends_atomic_block_if_necessary hatomic_prog.actions
  /\ efficient_corresponding_hactions_info_correct vw.vs vw.tds vw.inv vw.lprog_actions_array vw.hprog_actions_array
      vw.lpc_to_hpc vw.is_return_lpc vw.corresponding_hactions_info vw.lpc_indices_array vw.hpc_indices_array

val efficient_var_hiding_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (evw: efficient_var_hiding_witness_t)
  : Lemma (requires   efficient_var_hiding_witness_valid latomic_prog hatomic_prog evw
                    /\ is_armada_substep_invariant latomic_prog evw.inv
                    /\ latomic_prog.init_f == init_program evw.lprog
                    /\ hatomic_prog.init_f == init_program evw.hprog
                    /\ evw.lprog_actions_array == list_to_array latomic_prog.actions
                    /\ evw.hprog_actions_array == list_to_array hatomic_prog.actions)
          (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hatomic_prog)
                      refinement_requirement))
