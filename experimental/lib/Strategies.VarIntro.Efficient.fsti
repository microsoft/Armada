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
open Strategies.ArmadaStatement.Propagate
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Util.ImmutableArray
open Util.List
open Util.Nth
open Util.Range
open Util.Relation

noeq type efficient_hpc_info_t (vs: list var_id_t) (tds: list object_td_t) (inv: invariant_t Armada.State.t) =
  | EfficientHPCInfoNormal: efficient_hpc_info_t vs tds inv
  | EfficientHPCInfoIntroduced:
      (idx: nat) ->
      (end_pc: nat) ->
      (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv)) ->
      (progress: nat) ->
      efficient_hpc_info_t vs tds inv

let efficient_program_inits_match_except_global_variables
  (vs: list var_id_t)
  (lpcs: array_t pc_t)
  (hpcs: array_t pc_t)
  (hpc_to_lpc: array_t nat)
  (which_initializers_are_intros: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  (lprog_main_start_pc: nat)
  (hprog_main_start_pc: nat)
  : GTot ubool =
    lprog.main_method_id = hprog.main_method_id
  /\ array_nth hpc_to_lpc hprog_main_start_pc = Some lprog_main_start_pc
  /\ array_nth lpcs lprog_main_start_pc = Some lprog.main_start_pc
  /\ array_nth hpcs hprog_main_start_pc = Some hprog.main_start_pc
  /\ initializers_match_except_global_variables vs which_initializers_are_intros
       lprog.global_initializers hprog.global_initializers
  /\ lprog.main_stack_initializers == hprog.main_stack_initializers

let efficient_lpc_to_hpcs_contain_valid_indices
  (num_hpcs: nat)
  (lpc_to_hpcs: array_t (list nat))
  : GTot bool =
  for_all_array (for_all_ghost (fun (idx: nat) -> idx < num_hpcs)) lpc_to_hpcs

let efficient_start_pc_of_actions (pc_indices_list: list statement_pc_indices_t) : GTot (option nat) =
  match pc_indices_list with
  | [] -> None
  | pc_indices :: _ -> pc_indices.start_pc_index

let efficient_hl_pc_relation (hpc_to_lpc: array_t nat) : GTot (relation_t nat nat) =
  fun lidx hidx -> array_nth hpc_to_lpc hidx = Some lidx

let efficient_hl_pc_return_relation (hpc_to_lpc: array_t nat) (is_return_hpc: array_t bool) : GTot (relation_t nat nat) =
  fun lidx hidx -> array_nth hpc_to_lpc hidx = Some lidx && array_nth is_return_hpc hidx = Some true

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
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (lstart_state: efficient_thread_state_t)
  (hstart_state: efficient_thread_state_t)
  (lend_state: efficient_thread_state_t)
  (hend_state: efficient_thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : GTot ubool
  (decreases hactions) =
  match mapper, lactions, hactions, lpc_indices, hpc_indices with
  | [], [], [], [], [] ->
        lend_state = lstart_state
      /\ hend_state = hstart_state
  | MapperMatching :: remaining_mapper, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lpc_indices :: remaining_lpc_indices, first_hpc_indices :: remaining_hpc_indices ->
        efficient_laction_corresponds_to_haction vs pc_relation pc_return_relation first_laction first_haction
          first_lpc_indices first_hpc_indices
      /\ efficient_action_to_starting_thread_state first_lpc_indices = lstart_state
      /\ efficient_action_to_starting_thread_state first_hpc_indices = hstart_state
      /\ EfficientThreadStateAtPC? lstart_state
      /\ EfficientThreadStateAtPC? hstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation
          (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
          (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
      /\ efficient_lactions_correspond_to_hactions vs tds inv pc_relation pc_return_relation
          (efficient_action_to_ending_thread_state first_laction first_lpc_indices)
          (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
          lend_state hend_state remaining_mapper remaining_lactions remaining_hactions
          remaining_lpc_indices remaining_hpc_indices
  | MapperIntroduced witness :: remaining_mapper, _, first_haction :: remaining_hactions, _,
      first_hpc_indices :: remaining_hpc_indices ->
        first_haction.ok
      /\ efficient_action_to_starting_thread_state first_hpc_indices = hstart_state
      /\ efficient_thread_states_match_per_pc_relation pc_relation lstart_state
          (efficient_action_to_ending_thread_state first_haction first_hpc_indices)
      /\ valid_introduction_succeeds_witness vs tds inv first_haction.program_statement witness
      /\ statement_updates_gvars vs first_haction.program_statement.statement
      /\ efficient_lactions_correspond_to_hactions vs tds inv pc_relation pc_return_relation lstart_state
           (efficient_action_to_ending_thread_state first_haction first_hpc_indices) lend_state hend_state
           remaining_mapper lactions remaining_hactions lpc_indices remaining_hpc_indices
  | _, _, _, _, _ -> False

let efficient_laction_haction_correspondence_complete_inner
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (is_breaking_hpc: array_t bool)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (start_hpc: nat)
  (hpc: nat)
  : GTot bool =
    hpc = start_hpc
  || array_nth is_breaking_hpc hpc = Some false
  || (match array_nth hpc_info hpc with
     | Some (EfficientHPCInfoIntroduced _ _ _ _) -> true
     | _ -> false)

let efficient_laction_haction_correspondence_complete
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpc_to_hpcs: array_t (list nat))
  (is_breaking_hpc: array_t bool)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (lpc_indices: list statement_pc_indices_t)
  (hpc_indices: list statement_pc_indices_t)
  : GTot bool =
  let opt_start_lpc = efficient_start_pc_of_actions lpc_indices in
  let opt_start_hpc = efficient_start_pc_of_actions hpc_indices in
  match opt_start_lpc, opt_start_hpc with
  | None, None -> true
  | Some start_lpc, Some start_hpc ->
      (match array_nth lpc_to_hpcs start_lpc with
       | None -> false
       | Some hpcs ->
           for_all_ghost
             (efficient_laction_haction_correspondence_complete_inner vs tds inv is_breaking_hpc hpc_info start_hpc)
             hpcs)
  | _, _ -> false

let rec efficient_hactions_introducible
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpc_to_lpc: array_t nat)
  (hstart_pc: nat)
  (hend_pc: nat)
  (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv))
  (actions: list Armada.Action.t)
  (pc_indices: list statement_pc_indices_t)
  : GTot ubool
  (decreases introduction_succeeds_witnesses) =
  match introduction_succeeds_witnesses, actions, pc_indices with
  | [], [], [] -> hstart_pc = hend_pc
  | first_witness :: remaining_introduction_succeeds_witnesses, first_action :: remaining_actions,
      first_pc_indices :: remaining_pc_indices ->
        first_action.ok
      /\ efficient_action_to_starting_thread_state first_pc_indices = EfficientThreadStateAtPC hstart_pc
      /\ EfficientThreadStateAtPC? (efficient_action_to_ending_thread_state first_action first_pc_indices)
      /\ hstart_pc < array_len hpc_to_lpc
      /\ array_nth hpc_to_lpc hstart_pc = array_nth hpc_to_lpc hend_pc
      /\ valid_introduction_succeeds_witness vs tds inv first_action.program_statement first_witness
      /\ statement_updates_gvars vs first_action.program_statement.statement
      /\ efficient_hactions_introducible vs tds inv hpc_to_lpc
           (EfficientThreadStateAtPC?.pc (efficient_action_to_ending_thread_state first_action first_pc_indices))
           hend_pc remaining_introduction_succeeds_witnesses remaining_actions remaining_pc_indices
  | _, _, _ -> False

let efficient_introduced_atomic_action_makes_progress
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hatomic_actions_array: array_t (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (hpc_to_lpc: array_t nat)
  (is_nonyielding_lpc: array_t bool)
  (hpc: nat)
  : GTot ubool =
  match array_nth hpc_info hpc with
  | None -> False
  | Some EfficientHPCInfoNormal -> True
  | Some (EfficientHPCInfoIntroduced idx end_pc introduction_succeeds_witnesses progress) ->
      (match array_nth hatomic_actions_array idx, array_nth hpc_indices_array idx with
       | Some hactions, Some hpc_indices ->
           (match array_nth hpc_to_lpc hpc with
            | None -> False
            | Some lpc ->
                (match array_nth is_nonyielding_lpc lpc with
                 | None -> False
                 | Some lpc_nonyielding ->
                       efficient_hactions_introducible vs tds inv hpc_to_lpc hpc end_pc introduction_succeeds_witnesses
                         hactions hpc_indices
                     /\ actions_start_atomic_block hactions = not lpc_nonyielding
                     /\ actions_end_atomic_block hactions = not lpc_nonyielding
                     /\ (match array_nth hpc_info end_pc with
                        | None -> False
                        | Some EfficientHPCInfoNormal -> True
                        | Some (EfficientHPCInfoIntroduced _ _ _ progress') -> progress' < progress)))
       | _, _ -> False)

let efficient_lactions_correspond_to_hactions_per_correspondence
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (lpc_to_hpcs: array_t (list nat))
  (is_breaking_hpc: array_t bool)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (hatomic_actions_array: array_t (list Armada.Action.t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (lactions: list Armada.Action.t)
  (lpc_indices: list statement_pc_indices_t)
  (correspondence: ltoh_correspondence_t vs tds inv)
  : GTot ubool =
  match correspondence with
  | CorrespondencePropagate hidx ->
        Cons? lactions
      /\ (Cons?.hd lactions).program_statement == propagate_program_statement
      /\ array_nth hatomic_actions_array hidx == Some lactions
  | CorrespondenceNormal hidx mapper ->
      (match array_nth hatomic_actions_array hidx, array_nth hpc_indices_array hidx with
       | Some hactions, Some hpc_indices ->
             Cons? lactions
           /\ Cons? lpc_indices
           /\ Cons? hactions
           /\ Cons? hpc_indices
           /\ (let lstart_state = efficient_action_to_starting_thread_state (Cons?.hd lpc_indices) in
              let lend_state = efficient_actions_to_ending_thread_state lactions lpc_indices in
              let hstart_state = efficient_action_to_starting_thread_state (Cons?.hd hpc_indices) in
              let hend_state = efficient_actions_to_ending_thread_state hactions hpc_indices in
                do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
              /\ efficient_lactions_correspond_to_hactions vs tds inv pc_relation pc_return_relation
                   lstart_state hstart_state lend_state hend_state
                   mapper lactions hactions lpc_indices hpc_indices
              /\ efficient_laction_haction_correspondence_complete vs tds inv lpc_to_hpcs is_breaking_hpc hpc_info
                  lpc_indices hpc_indices)
       | _, _ -> False)

let efficient_hpc_among_hpc_to_lpc_to_hpcs
  (num_hpcs: nat)
  (hpc_to_lpc: array_t nat)
  (lpc_to_hpcs: array_t (list nat))
  : GTot bool =
  for_all_range num_hpcs
    (fun hpc -> (match array_nth hpc_to_lpc hpc with
              | None -> false
              | Some lpc ->
                 (match array_nth lpc_to_hpcs lpc with
                  | None -> false
                  | Some hpcs -> list_contains hpc hpcs)))

let efficient_return_hpcs_unique_inner2
  (hpc_to_lpc: array_t nat)
  (is_return_hpc: array_t bool)
  (hpc1: nat)
  (hpc2: nat)
  : GTot bool =
   implies (   array_nth is_return_hpc hpc2 = Some true
            && array_nth hpc_to_lpc hpc1 = array_nth hpc_to_lpc hpc2)
           (hpc1 = hpc2)

let efficient_return_hpcs_unique_inner1
  (num_hpcs: nat)
  (hpc_to_lpc: array_t nat)
  (is_return_hpc: array_t bool)
  (hpc1: nat)
  : GTot bool =
  implies (array_nth is_return_hpc hpc1 = Some true)
          (for_all_range num_hpcs (efficient_return_hpcs_unique_inner2 hpc_to_lpc is_return_hpc hpc1))

let efficient_return_hpcs_unique
  (num_hpcs: nat)
  (hpc_to_lpc: array_t nat)
  (is_return_hpc: array_t bool)
  : GTot bool =
  for_all_range num_hpcs (efficient_return_hpcs_unique_inner1 num_hpcs hpc_to_lpc is_return_hpc)

let efficient_corresponding_hactions_info_correct_inner
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lprog_actions_array: array_t (list Armada.Action.t))
  (hprog_actions_array: array_t (list Armada.Action.t))
  (lpc_to_hpcs: array_t (list nat))
  (is_breaking_hpc: array_t bool)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv))
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  (pc_relation: relation_t nat nat)
  (pc_return_relation: relation_t nat nat)
  (idx: nat)
  : GTot ubool =
  match array_nth lprog_actions_array idx, array_nth lpc_indices_array idx,
          array_nth corresponding_hactions_info idx with
  | Some lactions, Some lpc_indices, Some hactions_info ->
      efficient_lactions_correspond_to_hactions_per_correspondence vs tds inv pc_relation pc_return_relation
        lpc_to_hpcs is_breaking_hpc hpc_info hprog_actions_array hpc_indices_array lactions lpc_indices
        hactions_info
  | _, _, _ -> False

let efficient_corresponding_hactions_info_correct
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lprog_actions_array: array_t (list Armada.Action.t))
  (hprog_actions_array: array_t (list Armada.Action.t))
  (hpc_to_lpc: array_t nat)
  (lpc_to_hpcs: array_t (list nat))
  (is_return_hpc: array_t bool)
  (is_breaking_hpc: array_t bool)
  (hpc_info: array_t (efficient_hpc_info_t vs tds inv))
  (corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv))
  (lpc_indices_array: array_t (list statement_pc_indices_t))
  (hpc_indices_array: array_t (list statement_pc_indices_t))
  : GTot ubool =
  let pc_relation = efficient_hl_pc_relation hpc_to_lpc in
  let pc_return_relation = efficient_hl_pc_return_relation hpc_to_lpc is_return_hpc in
  for_all_range_ubool (array_len lprog_actions_array)
    (efficient_corresponding_hactions_info_correct_inner vs tds inv lprog_actions_array hprog_actions_array lpc_to_hpcs
       is_breaking_hpc hpc_info corresponding_hactions_info lpc_indices_array hpc_indices_array pc_relation
       pc_return_relation)

noeq type efficient_var_intro_witness_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  lprog_actions_array: array_t (list Armada.Action.t);
  hprog_actions_array: array_t (list Armada.Action.t);
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_intros: list bool;
  lpcs: array_t pc_t;
  hpcs: array_t pc_t;
  hpc_to_lpc: array_t nat;
  lpc_to_hpcs: array_t (list nat);
  is_return_hpc: array_t bool;
  is_nonyielding_lpc: array_t bool;
  is_nonyielding_hpc: array_t bool;
  is_breaking_hpc: array_t bool;
  hpc_info: array_t (efficient_hpc_info_t vs tds inv);
  corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds inv);
  lprog_main_start_pc_index: nat;
  hprog_main_start_pc_index: nat;
  lpc_indices_array: array_t (list statement_pc_indices_t);
  hpc_indices_array: array_t (list statement_pc_indices_t);
}

let efficient_var_intro_witness_valid
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: efficient_var_intro_witness_t)
  : GTot ubool =
    array_len vw.hpc_to_lpc = array_len vw.hpcs
  /\ array_len vw.lpc_to_hpcs = array_len vw.lpcs
  /\ array_len vw.is_return_hpc = array_len vw.hpcs
  /\ array_len vw.is_nonyielding_lpc = array_len vw.lpcs
  /\ array_len vw.is_nonyielding_hpc = array_len vw.hpcs
  /\ array_len vw.is_breaking_hpc = array_len vw.hpcs
  /\ array_len vw.hpc_info = array_len vw.hpcs
  /\ array_len vw.corresponding_hactions_info = array_len vw.lprog_actions_array
  /\ array_len vw.lpc_indices_array = array_len vw.lprog_actions_array
  /\ array_len vw.hpc_indices_array = array_len vw.hprog_actions_array
  /\ array_elements_unique vw.lpcs
  /\ array_elements_unique vw.hpcs
  /\ efficient_program_inits_match_except_global_variables vw.vs vw.lpcs vw.hpcs vw.hpc_to_lpc
      vw.which_initializers_are_intros vw.lprog vw.hprog vw.lprog_main_start_pc_index vw.hprog_main_start_pc_index
  /\ array_nth vw.is_breaking_hpc vw.hprog_main_start_pc_index = Some true
  /\ initializers_with_same_variable_id_match vw.hprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers
  /\ every_variable_appears_among_initializers vw.hprog.global_initializers vw.vs vw.tds
  /\ actions_array_corresponds_to_statement_pc_indices_array vw.lpcs vw.lprog_actions_array vw.lpc_indices_array
  /\ actions_array_corresponds_to_statement_pc_indices_array vw.hpcs vw.hprog_actions_array vw.hpc_indices_array
  /\ efficient_lpc_to_hpcs_contain_valid_indices (array_len vw.hpcs) vw.lpc_to_hpcs
  /\ efficient_hpc_among_hpc_to_lpc_to_hpcs (array_len vw.hpcs) vw.hpc_to_lpc vw.lpc_to_hpcs
  /\ efficient_return_hpcs_unique (array_len vw.hpcs) vw.hpc_to_lpc vw.is_return_hpc
  /\ efficient_each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc vw.lprog_actions_array
      vw.lpc_indices_array
  /\ efficient_each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc vw.hprog_actions_array
      vw.hpc_indices_array
  /\ efficient_each_action_list_maintains_all_threads_breaking vw.is_breaking_hpc vw.hprog_actions_array
      vw.hpc_indices_array
  /\ each_action_list_doesnt_internally_yield latomic_prog.actions
  /\ each_action_list_doesnt_internally_yield hatomic_prog.actions
  /\ for_all_range_ubool (array_len vw.hpcs)
      (efficient_introduced_atomic_action_makes_progress vw.vs vw.tds vw.inv vw.hprog_actions_array
         vw.hpc_indices_array vw.hpc_info vw.hpc_to_lpc vw.is_nonyielding_lpc)
  /\ efficient_corresponding_hactions_info_correct vw.vs vw.tds vw.inv vw.lprog_actions_array vw.hprog_actions_array
      vw.hpc_to_lpc vw.lpc_to_hpcs vw.is_return_hpc vw.is_breaking_hpc vw.hpc_info vw.corresponding_hactions_info
      vw.lpc_indices_array vw.hpc_indices_array

val efficient_var_intro_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (evw: efficient_var_intro_witness_t)
  : Lemma (requires   efficient_var_intro_witness_valid latomic_prog hatomic_prog evw
                    /\ is_armada_substep_invariant hatomic_prog evw.inv
                    /\ latomic_prog.init_f == init_program evw.lprog
                    /\ hatomic_prog.init_f == init_program evw.hprog
                    /\ evw.lprog_actions_array == list_to_array latomic_prog.actions
                    /\ evw.hprog_actions_array == list_to_array hatomic_prog.actions)
          (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hatomic_prog)
                      refinement_requirement))
