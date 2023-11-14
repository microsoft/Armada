module Strategies.VarHiding.Defs

open Armada.Action
open Armada.Base
open Armada.Computation
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
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.List
open Util.Nth
open Util.Relation

type program_statement_succeeds_proof_t
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (ps: program_statement_t) =
  (actor: tid_t) ->
  (nd: nondeterminism_t) ->
  (s: Armada.State.t{
      inv s
    /\ all_gvars_have_types s.mem vs tds
    /\ NotStopped? s.stop_reason
    /\ ThreadStatusRunning? (s.threads actor).status
    /\ ps.start_pc = Some (s.threads actor).pc}) ->
  squash (not (ComputationUndefined? (statement_computation actor nd (Some?.v ps.start_pc) ps.end_pc ps.statement s)))

noeq type ltoh_correspondence_t
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t) =
  | CorrespondenceHidden: ltoh_correspondence_t vs tds inv
  | CorrespondencePropagate: (hidx: nat) -> ltoh_correspondence_t vs tds inv
  | CorrespondenceNormal: (hidx: nat) -> (which_actions_hidden: list bool) -> ltoh_correspondence_t vs tds inv
  | CorrespondenceImpossibleConstantAssignmentFailure: ltoh_correspondence_t vs tds inv
  | CorrespondenceImpossibleStatementFailure:
      (ps: program_statement_t) ->
      (proof: program_statement_succeeds_proof_t vs tds inv ps) ->
      ltoh_correspondence_t vs tds inv

let variable_among_gvars (mem: Armada.Memory.t) (v: var_id_t) : GTot bool =
  let root_id = RootIdGlobal v in
  let root = mem root_id in
  RootGlobal? root

let all_variables_among_gvars (mem: Armada.Memory.t) (vs: list var_id_t) : GTot bool =
  for_all_ghost (variable_among_gvars mem) vs

let rec initializers_match_except_global_variables
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  : GTot ubool =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> True
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
        list_contains first_linit.var_id vs
      /\ initializers_match_except_global_variables vs remaining_which_are_hidings remaining_linits hinits
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
        not (list_contains first_hinit.var_id vs)
      /\ first_linit == first_hinit
      /\ initializers_match_except_global_variables vs remaining_which_are_hidings remaining_linits remaining_hinits
  | _, _, _ -> False

let initializer_value_to_td (init: initializer_value_t) : GTot object_td_t =
  match init with
  | InitializerArbitrary td -> td
  | InitializerSpecific value -> object_value_to_td value

let initializer_matches_variable_and_td
  (v: var_id_t)
  (td: object_td_t)
  (init: initializer_t)
  : GTot ubool =
    init.var_id = v
  /\ initializer_value_to_td init.iv == td

let every_variable_appears_among_initializers
  (inits: list initializer_t)
  (vs: list var_id_t)
  (tds: list object_td_t)
  : GTot ubool =
  lists_correspond_ubool
    (fun v td -> exists_ubool (initializer_matches_variable_and_td v td) inits)
    vs
    tds

let program_inits_match_except_global_variables
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (which_initializers_are_hidings: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  : GTot ubool =
     lprog.main_method_id = hprog.main_method_id
  /\ hprog.main_start_pc = lpc_to_hpc lprog.main_start_pc
  /\ initializers_match_except_global_variables vs which_initializers_are_hidings
       lprog.global_initializers hprog.global_initializers
  /\ lprog.main_stack_initializers == hprog.main_stack_initializers

let lpc_hpc_pc_relation
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (lpc: pc_t)
  (hpc: pc_t)
  : GTot bool =
  lpc_to_hpc lpc = hpc

let lpc_hpc_pc_return_relation
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (lpc: pc_t)
  (hpc: pc_t)
  : GTot bool =
  list_contains lpc return_lpcs && lpc_to_hpc lpc = hpc

let rec lactions_all_hidden
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (lstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (lactions: list Armada.Action.t)
  : GTot ubool
  (decreases lactions) =
  match lactions with
  | [] -> lend_state = lstart_state
  | first_laction :: remaining_lactions ->
         action_to_starting_thread_state first_laction = lstart_state
      /\ (match lstart_state, action_to_ending_thread_state first_laction with
         | ThreadStateAtPC lpc1, ThreadStateAtPC lpc2 -> lpc_to_hpc lpc1 = lpc_to_hpc lpc2
         | _, _ -> False)
      /\ statement_updates_gvars vs first_laction.program_statement.statement
      /\ lactions_all_hidden vs lpc_to_hpc (action_to_ending_thread_state first_laction) 
           lend_state remaining_lactions

let laction_corresponds_to_haction
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (laction: Armada.Action.t)
  (haction: Armada.Action.t)
  : GTot ubool =
  let lps, hps = laction.program_statement, haction.program_statement in
  let relation = lpc_hpc_pc_relation lpc_to_hpc in
  let return_relation = lpc_hpc_pc_return_relation lpc_to_hpc return_lpcs in
    statement_effect_independent_of_global_variables vs lps.statement
  /\ program_statements_match_per_pc_relation relation return_relation lps hps

let rec lactions_correspond_to_hactions
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  : GTot ubool
  (decreases lactions) =
  let relation = lpc_hpc_pc_relation lpc_to_hpc in
  match which_actions_hidden, lactions, hactions with
  | [], [], [] ->
        lend_state = lstart_state
      /\ hend_state = hstart_state
  | false :: remaining_which_actions_hidden, first_laction :: remaining_lactions, first_haction :: remaining_hactions ->
         laction_corresponds_to_haction vs lpc_to_hpc return_lpcs first_laction first_haction
      /\ action_to_starting_thread_state first_laction = lstart_state
      /\ action_to_starting_thread_state first_haction = hstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ ThreadStateAtPC? hstart_state
      /\ thread_states_match_per_pc_relation relation lstart_state hstart_state
      /\ thread_states_match_per_pc_relation relation (action_to_ending_thread_state first_laction)
           (action_to_ending_thread_state first_haction)
      /\ lactions_correspond_to_hactions vs lpc_to_hpc return_lpcs
           (action_to_ending_thread_state first_laction) (action_to_ending_thread_state first_haction)
           lend_state hend_state remaining_which_actions_hidden remaining_lactions remaining_hactions
  | true :: remaining_which_actions_hidden, first_laction :: remaining_lactions, _ ->
         action_to_starting_thread_state first_laction = lstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ thread_states_match_per_pc_relation relation lstart_state hstart_state
      /\ thread_states_match_per_pc_relation relation (action_to_ending_thread_state first_laction) hstart_state
      /\ statement_updates_gvars vs first_laction.program_statement.statement
      /\ lactions_correspond_to_hactions vs lpc_to_hpc return_lpcs (action_to_ending_thread_state first_laction) 
           hstart_state lend_state hend_state remaining_which_actions_hidden remaining_lactions hactions
  | _, _, _ -> False

let rec lactions_fail_final_statement_updating_gvars_using_constant
  (vs: list var_id_t)
  (tds: list object_td_t)
  (actions: list Armada.Action.t{Cons? actions})
  : GTot ubool =
  match actions with
  | [action] ->
        not action.ok
      /\ statement_updates_gvars_using_constant vs tds action.program_statement.statement
  | first_action :: remaining_actions ->
      lactions_fail_final_statement_updating_gvars_using_constant vs tds remaining_actions

let rec lactions_fail_specific_final_statement
  (ps: program_statement_t)
  (actions: list Armada.Action.t{Cons? actions})
  : GTot ubool =
  let start_state = action_to_starting_thread_state (Cons?.hd actions) in
  match actions with
  | [action] ->
        not action.ok
      /\ Some? ps.start_pc
      /\ start_state = ThreadStateAtPC (Some?.v ps.start_pc)
      /\ action.program_statement == ps
  | first_action :: remaining_actions ->
        action_to_ending_thread_state first_action = action_to_starting_thread_state (Cons?.hd remaining_actions)
      /\ lactions_fail_specific_final_statement ps remaining_actions

let lactions_correspond_to_hactions_per_correspondence
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (hatomic_actions: list (list Armada.Action.t))
  (lactions: list Armada.Action.t)
  (correspondence: (ltoh_correspondence_t vs tds inv))
  : GTot ubool =
  match correspondence with
  | CorrespondenceHidden ->
        Cons? lactions
      /\ actions_start_atomic_block lactions = actions_end_atomic_block lactions
      /\ (let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
         let lend_state = actions_to_ending_thread_state lactions in
         lactions_all_hidden vs lpc_to_hpc lstart_state lend_state lactions)
  | CorrespondencePropagate hidx ->
        Cons? lactions
      /\ (Cons?.hd lactions).program_statement == propagate_program_statement
      /\ list_nth hatomic_actions hidx == Some lactions
  | CorrespondenceNormal hidx which_actions_hidden ->
      (match list_nth hatomic_actions hidx with
       | Some hactions ->
             Cons? lactions
           /\ Cons? hactions
           /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
           /\ (let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
              let lend_state = actions_to_ending_thread_state lactions in
              let hstart_state = action_to_starting_thread_state (Cons?.hd hactions) in
              let hend_state = actions_to_ending_thread_state hactions in
              lactions_correspond_to_hactions vs lpc_to_hpc return_lpcs lstart_state hstart_state lend_state
                hend_state which_actions_hidden lactions hactions)
       | None -> False)
  | CorrespondenceImpossibleConstantAssignmentFailure ->
        Cons? lactions
      /\ ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement)
      /\ lactions_fail_final_statement_updating_gvars_using_constant vs tds lactions
  | CorrespondenceImpossibleStatementFailure ps proof ->
        Cons? lactions
      /\ ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement)
      /\ lactions_fail_specific_final_statement ps lactions

let return_pcs_unique_inner2
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (lpc1: pc_t)
  (lpc2: pc_t)
  : GTot bool =
  implies (lpc_to_hpc lpc1 = lpc_to_hpc lpc2) (lpc1 = lpc2)

let return_pcs_unique_inner1
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (lpc1: pc_t)
  : GTot bool =
  for_all_ghost (return_pcs_unique_inner2 lpc_to_hpc return_lpcs lpc1) return_lpcs

let return_pcs_unique
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  : GTot bool =
  for_all_ghost (return_pcs_unique_inner1 lpc_to_hpc return_lpcs) return_lpcs

noeq type var_hiding_relation_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  latomic_prog: program_t (make_atomic_semantics armada_semantics);
  hatomic_prog: program_t (make_atomic_semantics armada_semantics);
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_hidings: list bool;
  lpc_to_hpc: pc_t -> GTot pc_t;
  return_lpcs: list pc_t;
  is_nonyielding_lpc: pc_t -> GTot bool;
  is_nonyielding_hpc: pc_t -> GTot bool;
  corresponding_hactions_info: list (ltoh_correspondence_t vs tds inv);

  inv_is_substep_invariant_proof: unit ->
    squash (is_armada_substep_invariant latomic_prog inv);

  atomic_inits_match_regular_inits_proof: unit ->
    squash (latomic_prog.init_f == init_program lprog /\ hatomic_prog.init_f == init_program hprog);

  program_inits_match_except_global_variables_proof: unit ->
    squash (program_inits_match_except_global_variables vs lpc_to_hpc which_initializers_are_hidings lprog hprog);

  initial_pcs_correspond_proof: unit -> squash (lpc_to_hpc lprog.main_start_pc = hprog.main_start_pc);

  global_variables_unaddressed_in_initializers_proof: unit ->
    squash (  global_variables_unaddressed_in_initializers vs lprog.global_initializers
            /\ global_variables_unaddressed_in_initializers vs hprog.global_initializers
            /\ global_variables_unaddressed_in_initializers vs lprog.main_stack_initializers
            /\ global_variables_unaddressed_in_initializers vs hprog.main_stack_initializers);

  all_introduced_global_variables_initialized_proof: unit ->
    squash (every_variable_appears_among_initializers lprog.global_initializers vs tds);

  return_pcs_unique_proof: unit ->
    squash (return_pcs_unique lpc_to_hpc return_lpcs);

  lactions_consistent_with_is_nonyielding_pc_proof: unit ->
    squash (each_action_list_consistent_with_is_nonyielding_pc is_nonyielding_lpc latomic_prog.actions);

  hactions_consistent_with_is_nonyielding_pc_proof: unit ->
    squash (each_action_list_consistent_with_is_nonyielding_pc is_nonyielding_hpc hatomic_prog.actions);

  each_laction_doesnt_internally_yield_proof: unit ->
    squash (each_action_list_doesnt_internally_yield latomic_prog.actions);

  each_haction_doesnt_internally_yield_proof: unit ->
    squash (each_action_list_doesnt_internally_yield hatomic_prog.actions);

  each_haction_ends_atomic_block_if_necessary_proof: unit ->
    squash (each_action_list_ends_atomic_block_if_necessary hatomic_prog.actions);

  corresponding_hactions_correspond_proof: unit ->
    squash (lists_correspond_ubool
              (lactions_correspond_to_hactions_per_correspondence vs tds inv lpc_to_hpc return_lpcs
                 hatomic_prog.actions)
              latomic_prog.actions corresponding_hactions_info);
}
