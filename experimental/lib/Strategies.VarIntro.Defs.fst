module Strategies.VarIntro.Defs

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
open FStar.List.Tot.Base
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaStatement.Propagate
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.GlobalVars
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
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
  (s: Armada.State.t{
      inv s
    /\ all_gvars_have_types s.mem vs tds
    /\ NotStopped? s.stop_reason
    /\ ThreadStatusRunning? (s.threads actor).status
    /\ ps.start_pc = Some (s.threads actor).pc}) ->
  squash (ComputationProduces? (statement_computation actor [] (Some?.v ps.start_pc) ps.end_pc ps.statement s))

noeq type introduction_succeeds_witness_t
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t) =
  | IntroductionSucceedsBecauseItAssignsConstant: introduction_succeeds_witness_t vs tds inv
  | IntroductionSucceedsProof:
      (ps: program_statement_t) ->
      (proof: program_statement_succeeds_proof_t vs tds inv ps) -> introduction_succeeds_witness_t vs tds inv

noeq type haction_mapper_t (vs: list var_id_t) (tds: list object_td_t) (inv: invariant_t Armada.State.t) =
  | MapperMatching: haction_mapper_t vs tds inv
  | MapperIntroduced:
      (introduction_succeeds_witness: introduction_succeeds_witness_t vs tds inv) -> haction_mapper_t vs tds inv

noeq type ltoh_correspondence_t (vs: list var_id_t) (tds: list object_td_t) (inv: invariant_t Armada.State.t) = 
  | CorrespondencePropagate: (hidx: nat) -> ltoh_correspondence_t vs tds inv
  | CorrespondenceNormal: (hidx: nat) -> (mapper: list (haction_mapper_t vs tds inv)) -> ltoh_correspondence_t vs tds inv

noeq type hpc_info_t (vs: list var_id_t) (tds: list object_td_t) (inv: invariant_t Armada.State.t) =
  | HPCInfoNormal: hpc_info_t vs tds inv
  | HPCInfoIntroduced:
      (idx: nat) ->
      (end_pc: pc_t) ->
      (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv)) ->
      (progress: nat) ->
      hpc_info_t vs tds inv

let initializer_ok_for_var_intro
  (init: initializer_t)
  : GTot bool =
     not init.weakly_consistent
  && (match init.iv with
      | InitializerSpecific value ->
          (match value with
           | ObjectValuePrimitive _ -> true
           | ObjectValueAbstract _ _ -> true
           | _ -> false)
      | _ -> false)

let rec initializers_match_except_global_variables
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  : GTot ubool =
  match which_are_intros, linits, hinits with
  | [], [], [] -> True
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
         list_contains first_hinit.var_id vs
      /\ initializer_ok_for_var_intro first_hinit
      /\ initializers_match_except_global_variables vs remaining_which_are_intros linits remaining_hinits
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
         not (list_contains first_hinit.var_id vs)
      /\ first_linit == first_hinit
      /\ initializers_match_except_global_variables vs remaining_which_are_intros remaining_linits remaining_hinits
  | _, _, _ -> False

let initializers_match_if_same_variable_id
  (init1: initializer_t)
  (init2: initializer_t)
  : GTot ubool =
  init1.var_id = init2.var_id ==> init1 == init2

let initializers_with_same_variable_id_match
  (inits: list initializer_t)
  : GTot ubool =
  for_all_ubool (fun init1 ->
    for_all_ubool (fun init2 -> initializers_match_if_same_variable_id init1 init2) inits
  ) inits

let program_inits_match_except_global_variables
  (vs: list var_id_t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (which_initializers_are_intros: list bool)
  (lprog: Armada.Program.t)
  (hprog: Armada.Program.t)
  : GTot ubool =
    lprog.main_method_id = hprog.main_method_id
  /\ lprog.main_start_pc = hpc_to_lpc hprog.main_start_pc
  /\ initializers_match_except_global_variables vs which_initializers_are_intros
       lprog.global_initializers hprog.global_initializers
  /\ lprog.main_stack_initializers == hprog.main_stack_initializers

let start_pc_of_actions (actions: list Armada.Action.t) : GTot (option pc_t) =
  match actions with
  | [] -> None
  | action :: _ -> action.program_statement.start_pc

let pcs_contain_new_pcs_of_action
  (pcs: list pc_t)
  (action: Armada.Action.t)
  : GTot bool =
  let ps = action.program_statement in
  (match ps.end_pc with
  | Some pc -> list_contains pc pcs
  | None -> true)
  &&
  (match ps.statement with
   | CreateThreadStatement method_id initial_pc _ _ _ _ _ -> list_contains initial_pc pcs
   | _ -> true)

let lpc_hpc_pc_relation
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (lpc: pc_t)
  (hpc: pc_t)
  : GTot bool =
  hpc_to_lpc hpc = lpc

let lpc_hpc_pc_return_relation
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (lpc: pc_t)
  (hpc: pc_t)
  : GTot bool =
  list_contains hpc return_hpcs && hpc_to_lpc hpc = lpc

let valid_introduction_succeeds_witness
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (ps: program_statement_t)
  (witness: introduction_succeeds_witness_t vs tds inv)
  : GTot ubool =
  match witness with
  | IntroductionSucceedsBecauseItAssignsConstant -> statement_updates_gvars_using_constant vs tds ps.statement
  | IntroductionSucceedsProof ps' _ -> ps' == ps

let laction_corresponds_to_haction
  (vs: list var_id_t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (laction: Armada.Action.t)
  (haction: Armada.Action.t)
  : GTot ubool =
  let lps, hps = laction.program_statement, haction.program_statement in
  let relation = lpc_hpc_pc_relation hpc_to_lpc in
  let return_relation = lpc_hpc_pc_return_relation hpc_to_lpc return_hpcs in
    statement_effect_independent_of_global_variables vs lps.statement
  /\ program_statements_match_per_pc_relation relation return_relation lps hps

let rec lactions_correspond_to_hactions
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  : GTot ubool
  (decreases hactions) =
  let relation = lpc_hpc_pc_relation hpc_to_lpc in
  match mapper, lactions, hactions with
  | [], [], [] ->
        lend_state = lstart_state
      /\ hend_state = hstart_state
  | MapperMatching :: remaining_mapper, first_laction :: remaining_lactions, first_haction :: remaining_hactions ->
         laction_corresponds_to_haction vs hpc_to_lpc return_hpcs first_laction first_haction
      /\ action_to_starting_thread_state first_laction = lstart_state
      /\ action_to_starting_thread_state first_haction = hstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ ThreadStateAtPC? hstart_state
      /\ thread_states_match_per_pc_relation relation
           (action_to_ending_thread_state first_laction) (action_to_ending_thread_state first_haction)
      /\ lactions_correspond_to_hactions vs tds inv hpc_to_lpc return_hpcs
           (action_to_ending_thread_state first_laction) (action_to_ending_thread_state first_haction)
           lend_state hend_state remaining_mapper remaining_lactions remaining_hactions
  | MapperIntroduced witness :: remaining_mapper, _, first_haction :: remaining_hactions ->
        first_haction.ok
      /\ valid_introduction_succeeds_witness vs tds inv first_haction.program_statement witness
      /\ action_to_starting_thread_state first_haction = hstart_state
      /\ thread_states_match_per_pc_relation relation lstart_state (action_to_ending_thread_state first_haction)
      /\ statement_updates_gvars vs first_haction.program_statement.statement
      /\ lactions_correspond_to_hactions vs tds inv hpc_to_lpc return_hpcs lstart_state
           (action_to_ending_thread_state first_haction) lend_state hend_state
           remaining_mapper lactions remaining_hactions
  | _, _, _ -> False

let laction_haction_correspondence_complete_inner
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (is_breaking_hpc: pc_t -> GTot bool)
  (hpc_info: pc_t -> GTot (hpc_info_t vs tds inv))
  (start_hpc: pc_t)
  (hpc: pc_t)
  : GTot bool =
    hpc = start_hpc
  || (not (is_breaking_hpc hpc))
  || HPCInfoIntroduced? (hpc_info hpc)

let laction_haction_correspondence_complete
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (lpc_to_hpcs: pc_t -> GTot (list pc_t))
  (is_breaking_hpc: pc_t -> GTot bool)
  (hpc_info: pc_t -> GTot (hpc_info_t vs tds inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  : GTot bool =
  let opt_start_lpc = start_pc_of_actions lactions in
  let opt_start_hpc = start_pc_of_actions hactions in
  match opt_start_lpc, opt_start_hpc with
  | None, None -> true
  | Some start_lpc, Some start_hpc ->
      for_all_ghost
        (laction_haction_correspondence_complete_inner vs tds inv is_breaking_hpc hpc_info start_hpc)
        (lpc_to_hpcs start_lpc)
  | _, _ -> false

let rec hactions_introducible
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (hstart_pc: pc_t)
  (hend_pc: pc_t)
  (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vs tds inv))
  (actions: list Armada.Action.t)
  : GTot ubool
  (decreases introduction_succeeds_witnesses) =
  match introduction_succeeds_witnesses, actions with
  | [], [] -> hstart_pc = hend_pc
  | first_witness :: remaining_introduction_succeeds_witnesses, first_action :: remaining_actions ->
        first_action.ok
      /\ action_to_starting_thread_state first_action = ThreadStateAtPC hstart_pc
      /\ ThreadStateAtPC? (action_to_ending_thread_state first_action)
      /\ hpc_to_lpc hstart_pc = hpc_to_lpc hend_pc
      /\ valid_introduction_succeeds_witness vs tds inv first_action.program_statement first_witness
      /\ statement_updates_gvars vs first_action.program_statement.statement
      /\ hactions_introducible vs tds inv hpc_to_lpc
           (ThreadStateAtPC?.pc (action_to_ending_thread_state first_action))
           hend_pc remaining_introduction_succeeds_witnesses remaining_actions
  | _, _ -> False

let introduced_atomic_action_makes_progress
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hatomic_actions: list (list Armada.Action.t))
  (hpc_info: pc_t -> GTot (hpc_info_t vs tds inv))
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (is_nonyielding_lpc: pc_t -> GTot bool)
  (hpc: pc_t)
  : GTot ubool =
  match hpc_info hpc with
  | HPCInfoNormal -> True
  | HPCInfoIntroduced idx end_pc introduction_succeeds_witnesses progress ->
      (match nth hatomic_actions idx with
       | Some hactions ->
           let lpc = hpc_to_lpc hpc in
           let lpc_yielding = not (is_nonyielding_lpc lpc) in
             hactions_introducible vs tds inv hpc_to_lpc hpc end_pc introduction_succeeds_witnesses hactions
           /\ actions_start_atomic_block hactions = lpc_yielding
           /\ actions_end_atomic_block hactions = lpc_yielding
           /\ (match hpc_info end_pc with
              | HPCInfoNormal -> true
              | HPCInfoIntroduced _ _ _ progress' -> progress' < progress)
       | None -> False)

let lactions_correspond_to_hactions_per_correspondence
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (lpc_to_hpcs: pc_t -> GTot (list pc_t))
  (return_hpcs: list pc_t)
  (is_breaking_hpc: pc_t -> GTot bool)
  (hpc_info: pc_t -> GTot (hpc_info_t vs tds inv))
  (hatomic_actions: list (list Armada.Action.t))
  (lactions: list Armada.Action.t)
  (correspondence: ltoh_correspondence_t vs tds inv)
  : GTot ubool =
  match correspondence with
  | CorrespondencePropagate hidx ->
        Cons? lactions
      /\ (Cons?.hd lactions).program_statement == propagate_program_statement
      /\ list_nth hatomic_actions hidx == Some lactions
  | CorrespondenceNormal hidx mapper ->
      (match nth hatomic_actions hidx with
       | Some hactions ->
             Cons? lactions
           /\ Cons? hactions
           /\ (let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
              let lend_state = actions_to_ending_thread_state lactions in
              let hstart_state = action_to_starting_thread_state (Cons?.hd hactions) in
              let hend_state = actions_to_ending_thread_state hactions in
                 do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
              /\ lactions_correspond_to_hactions vs tds inv hpc_to_lpc return_hpcs lstart_state
                   hstart_state lend_state hend_state mapper lactions hactions
              /\ laction_haction_correspondence_complete vs tds inv lpc_to_hpcs is_breaking_hpc hpc_info lactions
                  hactions)
       | None -> False)

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

let every_hpc_appears_among_lpc_to_hpcs
  (lpc_to_hpcs: pc_t -> GTot (list pc_t))
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (hpcs: list pc_t)
  : GTot bool =
  for_all_ghost (fun hpc -> list_contains hpc (lpc_to_hpcs (hpc_to_lpc hpc))) hpcs

let return_pcs_unique_inner2
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (hpc1: pc_t)
  (hpc2: pc_t)
  : GTot bool =
  implies (hpc_to_lpc hpc1 = hpc_to_lpc hpc2) (hpc1 = hpc2)

let return_pcs_unique_inner1
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (hpc1: pc_t)
  : GTot bool =
  for_all_ghost (return_pcs_unique_inner2 hpc_to_lpc return_hpcs hpc1) return_hpcs

let return_pcs_unique
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  : GTot bool =
  for_all_ghost (return_pcs_unique_inner1 hpc_to_lpc return_hpcs) return_hpcs

noeq type var_intro_relation_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  latomic_prog: program_t (make_atomic_semantics armada_semantics);
  hatomic_prog: program_t (make_atomic_semantics armada_semantics);
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_intros: list bool;
  hpc_to_lpc: pc_t -> GTot pc_t;
  lpc_to_hpcs: pc_t -> GTot (list pc_t);
  return_hpcs: list pc_t;
  is_nonyielding_lpc: pc_t -> GTot bool;
  is_nonyielding_hpc: pc_t -> GTot bool;
  is_breaking_hpc: pc_t -> GTot bool;
  hpcs: list pc_t;
  hpc_info: pc_t -> GTot (hpc_info_t vs tds inv);
  corresponding_hactions_info: list (ltoh_correspondence_t vs tds inv);

  inv_is_substep_invariant_proof: unit ->
    squash (is_armada_substep_invariant hatomic_prog inv);

  atomic_inits_match_regular_inits_proof: unit ->
    squash (latomic_prog.init_f == init_program lprog /\ hatomic_prog.init_f == init_program hprog);

  program_inits_match_except_global_variables_proof: unit ->
    squash (program_inits_match_except_global_variables vs hpc_to_lpc which_initializers_are_intros lprog hprog);

  hinitializers_with_same_variable_id_match_proof: unit ->
    squash (initializers_with_same_variable_id_match hprog.global_initializers);

  initial_pc_in_pcs_proof: unit ->
    squash (list_contains hprog.main_start_pc hpcs);

  initial_pc_breaking_proof: unit ->
    squash (is_breaking_hpc hprog.main_start_pc);

  initial_pcs_correspond_proof: unit -> squash (hpc_to_lpc hprog.main_start_pc = lprog.main_start_pc);

  global_variables_unaddressed_in_initializers_proof: unit ->
    squash (  global_variables_unaddressed_in_initializers vs lprog.global_initializers
            /\ global_variables_unaddressed_in_initializers vs hprog.global_initializers
            /\ global_variables_unaddressed_in_initializers vs lprog.main_stack_initializers
            /\ global_variables_unaddressed_in_initializers vs hprog.main_stack_initializers);

  all_introduced_global_variables_initialized_proof: unit ->
    squash (every_variable_appears_among_initializers hprog.global_initializers vs tds);

  hpcs_complete_proof: unit ->
    squash (for_all_ghost (for_all_ghost (pcs_contain_new_pcs_of_action hpcs)) hatomic_prog.actions);

  lpc_to_hpcs_consistent_with_hpc_to_lpc_proof: unit ->
    squash (every_hpc_appears_among_lpc_to_hpcs lpc_to_hpcs hpc_to_lpc hpcs);

  return_pcs_unique_proof: unit ->
    squash (return_pcs_unique hpc_to_lpc return_hpcs);

  lactions_consistent_with_is_nonyielding_pc_proof: unit ->
    squash (each_action_list_consistent_with_is_nonyielding_pc is_nonyielding_lpc latomic_prog.actions);

  hactions_consistent_with_is_nonyielding_pc_proof: unit ->
    squash (each_action_list_consistent_with_is_nonyielding_pc is_nonyielding_hpc hatomic_prog.actions);

  hactions_end_in_breaking_pc_proof: unit ->
    squash (each_action_list_maintains_all_threads_breaking is_breaking_hpc hatomic_prog.actions);

  each_laction_doesnt_internally_yield_proof: unit ->
    squash (each_action_list_doesnt_internally_yield latomic_prog.actions);

  each_haction_doesnt_internally_yield_proof: unit ->
    squash (each_action_list_doesnt_internally_yield hatomic_prog.actions);

  introduced_atomic_actions_make_progress_proof: unit ->
    squash (for_all_ubool (introduced_atomic_action_makes_progress vs tds inv hatomic_prog.actions
                             hpc_info hpc_to_lpc is_nonyielding_lpc) hpcs);

  corresponding_hactions_correspond_proof: unit ->
    squash (lists_correspond_ubool
              (lactions_correspond_to_hactions_per_correspondence vs tds inv
                 hpc_to_lpc lpc_to_hpcs return_hpcs is_breaking_hpc hpc_info hatomic_prog.actions)
              latomic_prog.actions corresponding_hactions_info);
}
