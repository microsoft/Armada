module Strategies.VarHiding.Relation

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Step
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open FStar.Sequence.Ambient
open FStar.Sequence.Base
open FStar.WellFoundedRelation
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.GlobalVars
open Strategies.GlobalVars.Init
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Strategies.VarHiding.Helpers
open Strategies.VarHiding.Initialization
open Strategies.VarHiding.Invariant
open Strategies.VarHiding.Propagate
open Util.List
open Util.Nth
open Util.Seq

#push-options "--z3rlimit 40"

let executing_matching_steps_maintains_invariant
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (lstarts_atomic_block: bool)
  (hstarts_atomic_block: bool)
  (lends_atomic_block: bool)
  (hends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstep: Armada.Step.t)
  (hstep: Armada.Step.t)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires 
            (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
               var_hiding_lh_relation vr () ls hs
             /\ Some? (step_computation actor lstarts_atomic_block lends_atomic_block lstep ls)
             /\ contains_ubool lstep.action containing_latomic_action
             /\ contains_ubool containing_latomic_action vr.latomic_prog.actions
             /\ lstep_corresponds_to_hstep vr.vs pc_relation lstep hstep
             /\ action_to_starting_thread_state lstep.action = lstart_state
             /\ action_to_starting_thread_state hstep.action = hstart_state
             /\ action_to_ending_thread_state lstep.action = lend_state
             /\ action_to_ending_thread_state hstep.action = hend_state
             /\ ThreadStateAtPC? lstart_state
             /\ ThreadStateAtPC? hstart_state
             /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
             /\ thread_states_match_per_pc_relation pc_relation.relation lend_state hend_state
             /\ lstarts_atomic_block = lstep.action.program_statement.starts_atomic_block
             /\ hstarts_atomic_block = hstep.action.program_statement.starts_atomic_block
             /\ lends_atomic_block = (lstep.action.program_statement.ends_atomic_block || not lstep.action.ok)
             /\ hends_atomic_block = (hstep.action.program_statement.ends_atomic_block || not hstep.action.ok)
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state))
    (ensures  (match step_computation actor lstarts_atomic_block lends_atomic_block lstep ls,
                     step_computation actor hstarts_atomic_block hends_atomic_block hstep hs with
               | Some ls', Some hs' ->
                   var_hiding_lh_relation vr () ls' hs'
               | _, _ -> False)) =
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let laction = lstep.action in
  let haction = hstep.action in
  let lps = laction.program_statement in
  let hps = haction.program_statement in
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  lstep_corresponds_to_hstep_clarifier vr.vs pc_relation lstep hstep;
  assert (step_computation actor lstarts_atomic_block lends_atomic_block lstep ls ==
          action_computation actor lstarts_atomic_block lends_atomic_block lstep.nd lstep.action ls);
  assert (step_computation actor hstarts_atomic_block hends_atomic_block hstep hs ==
          action_computation actor hstarts_atomic_block hends_atomic_block hstep.nd hstep.action hs);
  statement_effect_independent_implications vr.vs pc_relation actor lstep.nd lthread.pc hthread.pc
    lps.end_pc hps.end_pc lps.statement hps.statement ls hs;
  match statement_computation actor lstep.nd lthread.pc lps.end_pc lps.statement ls,
        statement_computation actor hstep.nd hthread.pc hps.end_pc hps.statement hs with
  | ComputationProduces ls', ComputationProduces hs' ->
      assert (lstep.action.ok);
      assert (global_variables_unaddressed_in_memory vr.vs ls'.mem);
      assert (global_variables_unaddressed_in_memory vr.vs hs'.mem);
      assert (roots_match ls'.mem);
      assert (roots_match hs'.mem);
      assert (states_match_except_global_variables vr.vs pc_relation ls' hs');
      let ls'' = update_thread_pc_in_state ls' actor lps.end_pc in
      let hs'' = update_thread_pc_in_state hs' actor hps.end_pc in
      let lem1 () : Lemma (  unstarted_threads_have_empty_write_buffers ls'
                           /\ unstarted_threads_have_empty_write_buffers hs') = (
        executing_statement_maintains_unstarted_threads_have_empty_write_buffers actor lstep.nd
          lthread.pc lps.end_pc lps.statement ls;
        executing_statement_maintains_unstarted_threads_have_empty_write_buffers actor hstep.nd
          hthread.pc hps.end_pc hps.statement hs
      ) in
      assert (Some ls'' == step_computation actor lstarts_atomic_block lends_atomic_block lstep ls);
      assert (Some hs'' == step_computation actor hstarts_atomic_block hends_atomic_block hstep hs);
      let lem2 () : Lemma (states_match_except_global_variables vr.vs pc_relation ls'' hs'') = (
        update_thread_pcs_in_states_maintains_states_match_except_gvars vr.vs pc_relation
          actor ls' hs' lps.end_pc hps.end_pc
      ) in
      let lem3 () : Lemma (  global_variables_unaddressed_in_memory vr.vs ls''.mem
                           /\ global_variables_unaddressed_in_memory vr.vs hs''.mem
                           /\ roots_match ls''.mem
                           /\ roots_match hs''.mem) = (
        assert (ls''.mem == ls'.mem);
        assert (hs''.mem == hs'.mem)
      ) in
      lem1 ();
      lem2 ();
      lem3 ();
      assert (states_match_except_global_variables vr.vs pc_relation ls'' hs'');
      step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor lstarts_atomic_block
        lends_atomic_block lstep ls;
      assert (all_gvars_have_types ls''.mem vr.vs vr.tds);
      introduce NotStopped? ls''.stop_reason ==> vr.inv ls''
      with _. vr.inv_is_substep_invariant_proof ()
  | ComputationUndefined, ComputationUndefined ->
      assert (not lstep.action.ok)

#pop-options
#push-options "--z3rlimit 10"

let executing_step_updating_gvars_maintains_invariant
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (lstarts_atomic_block: bool)
  (lends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstep: Armada.Step.t)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires 
            (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
               var_hiding_lh_relation vr () ls hs
             /\ Some? (step_computation actor lstarts_atomic_block lends_atomic_block lstep ls)
             /\ contains_ubool lstep.action containing_latomic_action
             /\ contains_ubool containing_latomic_action vr.latomic_prog.actions
             /\ statement_updates_gvars vr.vs lstep.action.program_statement.statement
             /\ lstep.action.ok
             /\ Some? lstep.action.program_statement.end_pc
             /\ pc_relation.relation (Some?.v lstep.action.program_statement.end_pc) (hs.threads actor).pc
             /\ lstarts_atomic_block = lstep.action.program_statement.starts_atomic_block
             /\ lends_atomic_block = lstep.action.program_statement.ends_atomic_block
             /\ thread_state_applies ls actor (action_to_starting_thread_state lstep.action)))
    (ensures  (match step_computation actor lstarts_atomic_block lends_atomic_block lstep ls with
               | Some ls' -> var_hiding_lh_relation vr () ls' hs
               | _ -> False)) =
  let lthread = ls.threads actor in
  let laction = lstep.action in
  let lps = laction.program_statement in
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  statement_that_updates_gvars_s1_only_maintains_states_match vr.vs pc_relation actor lstep.nd lthread.pc
    lps.end_pc lps.statement ls hs;
  match statement_computation actor lstep.nd lthread.pc lps.end_pc lps.statement ls with
  | ComputationProduces ls' ->
      update_thread_pc_in_state_maintains_states_match_except_gvars vr.vs pc_relation actor ls' hs
        lps.end_pc;
      let ls'' = update_thread_pc_in_state ls' actor lps.end_pc in
      assert (states_match_except_global_variables vr.vs pc_relation ls'' hs);
      assert (global_variables_unaddressed_in_memory vr.vs ls''.mem);
      executing_statement_maintains_unstarted_threads_have_empty_write_buffers actor lstep.nd
        lthread.pc lps.end_pc lps.statement ls;
      assert (unstarted_threads_have_empty_write_buffers ls'');
      step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor lstarts_atomic_block
        lends_atomic_block lstep ls;
      assert (all_gvars_have_types ls''.mem vr.vs vr.tds);
      introduce NotStopped? ls''.stop_reason ==> vr.inv ls''
      with _. vr.inv_is_substep_invariant_proof ()
  | ComputationUndefined ->
      ()

#pop-options
#push-options "--z3rlimit 40"

let rec establish_normal_lifter_given_hsteps_at_correct_pc
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires
            (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
             let lstarts_atomic_block = actions_start_atomic_block lactions in
             let lends_atomic_block = actions_end_atomic_block lactions in
               var_hiding_lh_relation vr () ls hs
             /\ (Some? (steps_computation_permitting_empty actor lstarts_atomic_block lends_atomic_block lsteps ls))
             /\ (forall laction. contains_ubool laction lactions ==> contains_ubool laction containing_latomic_action)
             /\ contains_ubool containing_latomic_action vr.latomic_prog.actions
             /\ lactions == map_ghost armada_step_to_action lsteps
             /\ hactions == map_ghost armada_step_to_action hsteps
             /\ lsteps_correspond_to_hsteps vr.vs pc_relation
                 lstart_state hstart_state lend_state hend_state which_actions_hidden lsteps hsteps
             /\ action_list_doesnt_internally_yield lactions
             /\ action_list_doesnt_internally_yield hactions
             /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state
             /\ each_action_ends_atomic_block_if_necessary hactions))
    (ensures (let lstarts_atomic_block = actions_start_atomic_block lactions in
              let lends_atomic_block = actions_end_atomic_block lactions in
              let hstarts_atomic_block = actions_start_atomic_block hactions in
              let hends_atomic_block = actions_end_atomic_block hactions in
              match steps_computation_permitting_empty actor lstarts_atomic_block lends_atomic_block lsteps ls,
                    steps_computation_permitting_empty actor hstarts_atomic_block hends_atomic_block hsteps hs with
               | Some ls', Some hs' -> var_hiding_lh_relation vr () ls' hs'
               | _, _ -> False))
    (decreases lsteps) =
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  match which_actions_hidden, lactions, hactions, lsteps, hsteps with
  | [], [], [], [], [] -> ()
  | false :: remaining_which_actions_hidden, laction :: remaining_lactions, haction :: remaining_hactions,
      lstep :: remaining_lsteps, hstep :: remaining_hsteps ->
      let lthread = ls.threads actor in
      let hthread = hs.threads actor in
      let lps = laction.program_statement in
      let hps = haction.program_statement in
      let lstep: Armada.Step.t = lstep in
      let hstep: Armada.Step.t = hstep in
      let lstarts_atomic_block = actions_start_atomic_block lactions in
      let lends_atomic_block = actions_end_atomic_block lactions in
      let hstarts_atomic_block = actions_start_atomic_block hactions in
      let hends_atomic_block = actions_end_atomic_block hactions in
      let laction_ends_atomic_block = lps.ends_atomic_block || not laction.ok in
      let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
      assert (laction_ends_atomic_block = (if (Cons? remaining_lsteps) then false else lends_atomic_block));
      assert (haction_ends_atomic_block = (if (Cons? remaining_hsteps) then false else hends_atomic_block));
      executing_matching_steps_maintains_invariant vr actor lstart_state hstart_state
        (action_to_ending_thread_state lstep.action) (action_to_ending_thread_state hstep.action)
        lstarts_atomic_block hstarts_atomic_block laction_ends_atomic_block haction_ends_atomic_block
        ls hs lstep hstep containing_latomic_action;
      (match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls,
             step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
       | Some ls', Some hs' ->
           step_computation_has_thread_state_effect actor lstarts_atomic_block laction_ends_atomic_block lstep ls;
           step_computation_has_thread_state_effect actor hstarts_atomic_block haction_ends_atomic_block hstep hs;
           step_computation_has_thread_state_effect actor lstarts_atomic_block laction_ends_atomic_block lstep ls;
           step_computation_has_thread_state_effect actor hstarts_atomic_block haction_ends_atomic_block hstep hs;
           establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls' hs'
             (action_to_ending_thread_state lstep.action)
             (action_to_ending_thread_state hstep.action)
             lend_state hend_state remaining_which_actions_hidden remaining_lactions remaining_hactions remaining_lsteps
             remaining_hsteps containing_latomic_action
       | _, _ -> ())
  | true :: remaining_which_actions_hidden, laction :: remaining_lactions, _, lstep :: remaining_lsteps, _ ->
      let lthread = ls.threads actor in
      let lps = laction.program_statement in
      let lstep: Armada.Step.t = lstep in
      let lstarts_atomic_block = actions_start_atomic_block lactions in
      let lends_atomic_block = actions_end_atomic_block lactions in
      let laction_ends_atomic_block = lps.ends_atomic_block || not laction.ok in
      assert (laction_ends_atomic_block = (if (Cons? remaining_lsteps) then false else lends_atomic_block));
      assert (Some? (step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls));
      executing_step_updating_gvars_maintains_invariant vr actor lstarts_atomic_block laction_ends_atomic_block
        ls hs lstep containing_latomic_action;
      (match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls with
       | Some ls' ->
           step_computation_has_thread_state_effect actor lstarts_atomic_block
             laction_ends_atomic_block lstep ls;
           step_computation_has_thread_state_effect actor lstarts_atomic_block
             laction_ends_atomic_block lstep ls;
           establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls' hs
             (action_to_ending_thread_state lstep.action) hstart_state lend_state hend_state
             remaining_which_actions_hidden remaining_lactions hactions remaining_lsteps hsteps
             containing_latomic_action
       | None -> ())
  | _, _, _, _, _ -> ()

#pop-options

let get_normal_lifter_given_hsteps_at_correct_pc
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
                 var_hiding_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ hactions == map_ghost armada_step_to_action hsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ contains_ubool hactions vr.hatomic_prog.actions
               /\ lsteps_correspond_to_hsteps vr.vs pc_relation
                   lstart_state hstart_state lend_state hend_state which_actions_hidden lsteps hsteps
               /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
               /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
               /\ thread_state_applies ls actor lstart_state
               /\ thread_state_applies hs actor hstart_state
               /\ Cons? hactions))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  steps_computation_implies_start_and_end_atomic_block actor starts_atomic_block ends_atomic_block lsteps ls;
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  assert (var_hiding_lh_relation vr () ls hs);
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  assert (Some? (steps_computation_permitting_empty actor starts_atomic_block ends_atomic_block lsteps ls));
  vr.each_laction_doesnt_internally_yield_proof ();
  assert (action_list_doesnt_internally_yield lactions);
  vr.each_haction_doesnt_internally_yield_proof ();
  assert (action_list_doesnt_internally_yield hactions);
  vr.each_haction_ends_atomic_block_if_necessary_proof ();
  assert (each_action_ends_atomic_block_if_necessary hactions);
  establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls hs
    lstart_state hstart_state lend_state hend_state which_actions_hidden lactions hactions lsteps hsteps
    lactions;
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block hsteps hs;
  StepLifterLift hsteps ()

#push-options "--z3rlimit 10"

let rec establish_skip_lifter_given_hsteps_at_correct_pc
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (lactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires
            (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
             let lstarts_atomic_block = actions_start_atomic_block lactions in
             let lends_atomic_block = actions_end_atomic_block lactions in
               var_hiding_lh_relation vr () ls hs
             /\ (Some? (steps_computation_permitting_empty actor lstarts_atomic_block
                         lends_atomic_block lsteps ls))
             /\ lactions == map_ghost armada_step_to_action lsteps
             /\ lactions_all_hidden vr.vs vr.lpc_to_hpc lstart_state lend_state lactions
             /\ (forall laction. contains_ubool laction lactions ==> contains_ubool laction containing_latomic_action)
             /\ contains_ubool containing_latomic_action vr.latomic_prog.actions
             /\ action_list_doesnt_internally_yield lactions
             /\ thread_state_applies ls actor lstart_state))
    (ensures (let lstarts_atomic_block = actions_start_atomic_block lactions in
              let lends_atomic_block = actions_end_atomic_block lactions in
              match steps_computation_permitting_empty actor lstarts_atomic_block lends_atomic_block lsteps ls with
              | Some ls' -> var_hiding_lh_relation vr () ls' hs
              | _ -> False))
    (decreases lsteps) =
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  match lactions, lsteps with
  | [], [] -> ()
  | laction :: remaining_lactions, lstep :: remaining_lsteps ->
      let lthread = ls.threads actor in
      let lps = laction.program_statement in
      let lstep: Armada.Step.t = lstep in
      let lstarts_atomic_block = actions_start_atomic_block lactions in
      let lends_atomic_block = actions_end_atomic_block lactions in
      let laction_ends_atomic_block = lps.ends_atomic_block || not laction.ok in
      assert (laction_ends_atomic_block = (if (Cons? remaining_lsteps) then false else lends_atomic_block));
      assert (Some? (step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls));
      executing_step_updating_gvars_maintains_invariant vr actor lstarts_atomic_block laction_ends_atomic_block
        ls hs lstep containing_latomic_action;
      (match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls with
       | Some ls' ->
           step_computation_has_thread_state_effect actor lstarts_atomic_block
             laction_ends_atomic_block lstep ls;
           step_computation_has_thread_state_effect actor lstarts_atomic_block
             laction_ends_atomic_block lstep ls;
           establish_skip_lifter_given_hsteps_at_correct_pc vr actor ls' hs
             (action_to_ending_thread_state lstep.action) lend_state
             remaining_lactions remaining_lsteps containing_latomic_action
       | None -> ())

let get_skip_lifter_given_steps_at_correct_pc
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (lactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
                 var_hiding_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ lactions_all_hidden vr.vs vr.lpc_to_hpc lstart_state lend_state lactions
               /\ actions_start_atomic_block lactions = actions_end_atomic_block lactions
               /\ thread_state_applies ls actor lstart_state))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  steps_computation_implies_start_and_end_atomic_block actor starts_atomic_block ends_atomic_block lsteps ls;
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  assert (var_hiding_lh_relation vr () ls hs);
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  assert (Some? (steps_computation_permitting_empty actor starts_atomic_block ends_atomic_block lsteps ls));
  vr.each_laction_doesnt_internally_yield_proof ();
  assert (action_list_doesnt_internally_yield lactions);
  establish_skip_lifter_given_hsteps_at_correct_pc vr actor ls hs lstart_state lend_state lactions lsteps lactions;
  StepLifterSkip ()

let get_skip_lifter
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (lactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
                 var_hiding_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ lactions_all_hidden vr.vs vr.lpc_to_hpc lstart_state lend_state lactions
               /\ actions_start_atomic_block lactions = actions_end_atomic_block lactions))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  steps_computation_requires_start_thread_state actor starts_atomic_block ends_atomic_block lsteps ls;
  let lthread = ls.threads actor in
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  match lstart_state with
  | ThreadStateAtPC start_lpc ->
      assert (lstart_state = action_to_starting_thread_state (Cons?.hd lsteps).action);
      assert (lthread.pc = start_lpc);
      assert (threads_match_except_global_variables vr.vs pc_relation ls.threads hs.threads);
      assert (ThreadStatusRunning? lthread.status);
      get_skip_lifter_given_steps_at_correct_pc vr actor starts_atomic_block ends_atomic_block ls hs
        lstart_state lend_state lactions lsteps
  | _ -> false_elim ()

let get_normal_lifter_given_hsteps
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
                 var_hiding_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ hactions == map_ghost armada_step_to_action hsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ contains_ubool hactions vr.hatomic_prog.actions
               /\ lsteps_correspond_to_hsteps vr.vs pc_relation
                   lstart_state hstart_state lend_state hend_state which_actions_hidden lsteps hsteps
               /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
               /\ Cons? hactions))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  steps_computation_requires_start_thread_state actor starts_atomic_block ends_atomic_block lsteps ls;
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  lsteps_correspond_to_hsteps_implies_first_lstep_matches_lstart_state vr.vs pc_relation lstart_state hstart_state
    lend_state hend_state which_actions_hidden lsteps hsteps;
  match lstart_state, hstart_state with
  | ThreadStateAtPC start_lpc, ThreadStateAtPC start_hpc ->
      assert (lstart_state = action_to_starting_thread_state (Cons?.hd lsteps).action);
      assert (lthread.pc = start_lpc);
      assert (threads_match_except_global_variables vr.vs pc_relation ls.threads hs.threads);
      assert (ThreadStatusRunning? lthread.status);
      assert (pc_relation.relation lthread.pc hthread.pc);
      assert (vr.lpc_to_hpc lthread.pc = hthread.pc);
      assert (hthread.pc = start_hpc);
      get_normal_lifter_given_hsteps_at_correct_pc vr actor starts_atomic_block ends_atomic_block ls hs
        lstart_state hstart_state lend_state hend_state which_actions_hidden lactions hactions lsteps hsteps
  | _, _ -> false_elim ()

let rec impossible_constant_assignment_failure_is_impossible
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (s: Armada.State.t)
  (steps: list Armada.Step.t)
  (actions: list Armada.Action.t)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires   all_gvars_have_types s.mem vr.vs vr.tds
                    /\ (NotStopped? s.stop_reason ==> vr.inv s)
                    /\ actions == map_ghost armada_step_to_action steps
                    /\ Some? (steps_computation_generic armada_semantics actor
                               starts_atomic_block ends_atomic_block steps s)
                    /\ lactions_fail_final_statement_updating_gvars_using_constant vr.vs vr.tds actions
                    /\ (forall action. contains_ubool action actions ==> contains_ubool action containing_latomic_action)
                    /\ contains_ubool containing_latomic_action vr.latomic_prog.actions)
          (ensures  False)
          (decreases actions) =
  match steps, actions with
  | [step], [action] ->
      let ps = action.program_statement in
      let start_pc = (s.threads actor).pc in
      statement_that_updates_gvars_using_constant_must_succeed vr.vs vr.tds actor start_pc ps.end_pc ps.statement s
  | first_step :: remaining_steps, first_action :: remaining_actions ->
      (match step_computation actor starts_atomic_block false first_step s with
       | Some s' ->
           introduce NotStopped? s'.stop_reason ==> vr.inv s'
           with _. vr.inv_is_substep_invariant_proof ();
           step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor starts_atomic_block
             false first_step s;
           impossible_constant_assignment_failure_is_impossible vr actor false ends_atomic_block s'
             remaining_steps remaining_actions containing_latomic_action
       | None -> false_elim ())

let rec impossible_statement_failure_is_impossible
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (s: Armada.State.t)
  (steps: list Armada.Step.t)
  (actions: list Armada.Action.t)
  (ps: program_statement_t)
  (proof: program_statement_succeeds_proof_t vr.vs vr.tds vr.inv ps)
  (containing_latomic_action: list Armada.Action.t)
  : Lemma (requires   all_gvars_have_types s.mem vr.vs vr.tds
                    /\ Cons? actions
                    /\ thread_state_applies s actor (action_to_starting_thread_state (Cons?.hd actions))
                    /\ vr.inv s
                    /\ actions == map_ghost armada_step_to_action steps
                    /\ Some? (steps_computation_generic armada_semantics actor
                               starts_atomic_block ends_atomic_block steps s)
                    /\ lactions_fail_specific_final_statement ps actions
                    /\ (forall action. contains_ubool action actions ==> contains_ubool action containing_latomic_action)
                    /\ contains_ubool containing_latomic_action vr.latomic_prog.actions)
          (ensures  False)
          (decreases actions) =
  match steps, actions with
  | [step], [action] ->
      assert (Some? (steps_computation actor starts_atomic_block ends_atomic_block steps s));
      assert (Some? (step_computation actor starts_atomic_block ends_atomic_block step s));
      assert (not action.ok);
      assert (ComputationUndefined? (statement_computation actor step.nd (s.threads actor).pc
                action.program_statement.end_pc action.program_statement.statement s));
      proof actor step.nd s
  | first_step :: remaining_steps, first_action :: remaining_actions ->
      (match step_computation actor starts_atomic_block false first_step s with
       | Some s' ->
           introduce NotStopped? s'.stop_reason ==> vr.inv s'
           with _. vr.inv_is_substep_invariant_proof ();
           step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor starts_atomic_block
             false first_step s;
           step_computation_has_thread_state_effect actor starts_atomic_block false first_step s;
           impossible_statement_failure_is_impossible vr actor false ends_atomic_block s'
             remaining_steps remaining_actions ps proof containing_latomic_action
       | None -> false_elim ())

let get_normal_lifter
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_hiding_lh_relation vr () ls hs
              /\ Some? (steps_computation_generic armada_semantics actor
                         starts_atomic_block ends_atomic_block lsteps ls)
              /\ contains_ubool (map_ghost armada_step_to_action lsteps) vr.latomic_prog.actions
              /\ ~((Cons?.hd lsteps).action.program_statement.statement == PropagateWriteMessageStatement))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  vr.corresponding_hactions_correspond_proof ();
  let lactions = map_ghost armada_step_to_action lsteps in
  let correspondence = get_correspondent_from_lists_correspond_ubool
    (lactions_correspond_to_hactions_per_correspondence vr.vs vr.tds vr.inv vr.lpc_to_hpc vr.return_lpcs
       vr.hatomic_prog.actions)
    vr.latomic_prog.actions
    vr.corresponding_hactions_info
    lactions in
  match correspondence with
  | CorrespondenceHidden ->
      let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
      let lend_state = actions_to_ending_thread_state lactions in
      get_skip_lifter vr actor starts_atomic_block ends_atomic_block ls hs
        lstart_state lend_state lactions lsteps
  | CorrespondencePropagate hidx -> false_elim ()
  | CorrespondenceNormal hidx which_actions_hidden ->
      (match list_nth vr.hatomic_prog.actions hidx with
       | Some hactions ->
           let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
           nth_implies_contains_ubool vr.hatomic_prog.actions hidx hactions;
           let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
           let lend_state = actions_to_ending_thread_state lactions in
           let hstart_state = action_to_starting_thread_state (Cons?.hd hactions) in
           let hend_state = actions_to_ending_thread_state hactions in
           let hsteps = compute_hsteps_from_lsteps vr.vs vr.lpc_to_hpc
                          vr.return_lpcs vr.return_pcs_unique_proof
                          lstart_state hstart_state lend_state
                          hend_state which_actions_hidden lactions hactions lsteps in
           get_normal_lifter_given_hsteps vr actor starts_atomic_block ends_atomic_block ls hs
             lstart_state hstart_state lend_state hend_state which_actions_hidden lactions hactions lsteps hsteps
       | None -> false_elim ())
  | CorrespondenceImpossibleConstantAssignmentFailure ->
      impossible_constant_assignment_failure_is_impossible vr actor starts_atomic_block ends_atomic_block ls
        lsteps lactions lactions;
      false_elim ()
  | CorrespondenceImpossibleStatementFailure ps proof ->
      impossible_statement_failure_is_impossible vr actor starts_atomic_block ends_atomic_block ls
        lsteps lactions ps proof lactions;
      false_elim ()

#pop-options

let get_lifter_for_path
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_hiding_lh_relation vr () ls hs
              /\ Some? (steps_computation_generic armada_semantics actor
                         starts_atomic_block ends_atomic_block lsteps ls)
              /\ contains_ubool (map_ghost armada_step_to_action lsteps) vr.latomic_prog.actions)
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
                           nat (default_wfr nat)
                           (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  match lsteps with
  | first_step :: remaining_steps ->
      (match first_step.action.program_statement.statement with
       | PropagateWriteMessageStatement ->
           get_propagate_lifter vr actor starts_atomic_block ends_atomic_block ls hs lsteps
       | _ -> get_normal_lifter vr actor starts_atomic_block ends_atomic_block ls hs lsteps)

let paths_liftable_proof
  (vr: var_hiding_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (aux: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t{
       var_hiding_invariant ls
     /\ var_hiding_lh_relation vr aux ls hs
     /\ Some? (step_computation_generic (make_atomic_semantics armada_semantics)
                actor starts_atomic_block ends_atomic_block lsteps ls)
     /\ program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
         vr.latomic_prog lsteps})
  : GTot (lifter: (step_lifter_t (list Armada.Step.t) unit){
            step_lifter_works
              (make_atomic_semantics armada_semantics)
              (make_atomic_semantics armada_semantics)
              vr.latomic_prog vr.hatomic_prog unit (var_hiding_lh_relation vr)
              nat (default_wfr nat)
              (var_hiding_progress_measure vr) actor starts_atomic_block ends_atomic_block
              lsteps ls hs lifter}) =
  get_lifter_for_path vr actor starts_atomic_block ends_atomic_block ls hs lsteps

let inv_stepwise_invariant_proof
  (vr: var_hiding_relation_t)
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)
             vr.latomic_prog var_hiding_invariant) =
  ()

let initialize_hstate
  (vr: var_hiding_relation_t)
  (ls: Armada.State.t)
  : GTot Armada.State.t =
  let mem' = remove_hidden_initializers vr.which_initializers_are_hidings vr.lprog.global_initializers ls.mem in
  let thread = ls.threads ls.initial_tid in
  let thread' = { thread with pc = vr.hprog.main_start_pc } in
  let threads' = Spec.Map.upd ls.threads ls.initial_tid thread' in
  { ls with mem = mem'; threads = threads' }

let initialize_hstate_satisfies_hinit
  (vr: var_hiding_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  init_program vr.hprog (initialize_hstate vr ls)) =
  let hs = initialize_hstate vr ls in
  vr.program_inits_match_except_global_variables_proof ();
  remove_hidden_initializers_ensures_satisfies_global_initializers vr.vs vr.which_initializers_are_hidings
    vr.lprog.global_initializers vr.hprog.global_initializers ls.mem;
  let thread = hs.threads hs.initial_tid in
  let initial_frame_uniq = Cons?.hd hs.uniqs_used in
  remove_hidden_initializers_ensures_satisfies_main_stack_initializers vr.vs vr.which_initializers_are_hidings
    vr.lprog.global_initializers hs.initial_tid vr.hprog.main_method_id initial_frame_uniq
    thread.top.local_variables vr.hprog.main_stack_initializers ls.mem;
  remove_hidden_initializers_ensures_memory_invalid_outside_initializations vr.vs vr.which_initializers_are_hidings
    vr.lprog.global_initializers vr.hprog.global_initializers hs.initial_tid vr.hprog.main_method_id initial_frame_uniq
    thread.top.local_variables ls.mem

#push-options "--z3rlimit 10"

let initialize_hstate_satisfies_threads_match_except_global_variables
  (vr: var_hiding_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  (let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs
                                         vr.return_pcs_unique_proof in
                     let hs = initialize_hstate vr ls in
                     threads_match_except_global_variables vr.vs pc_relation ls.threads hs.threads)) =
  vr.initial_pcs_correspond_proof ()

#pop-options

let initialize_hstate_satisfies_var_hiding_lh_relation
  (vr: var_hiding_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures var_hiding_lh_relation vr () ls (initialize_hstate vr ls)) =
  let hs = initialize_hstate vr ls in
  initialize_hstate_satisfies_hinit vr ls;
  vr.program_inits_match_except_global_variables_proof ();
  remove_hidden_initializers_ensures_satisfies_global_initializers vr.vs vr.which_initializers_are_hidings
    vr.lprog.global_initializers vr.hprog.global_initializers ls.mem;
  init_implies_positions_valid_in_state vr.hprog hs;
  init_implies_roots_match vr.hprog hs;
  init_implies_unstarted_threads_have_empty_write_buffers vr.hprog hs;
  init_implies_positions_valid_in_state vr.lprog ls;
  init_implies_roots_match vr.lprog ls;
  init_implies_unstarted_threads_have_empty_write_buffers vr.lprog ls;
  let pc_relation = var_hiding_pc_relation vr.lpc_to_hpc vr.return_lpcs vr.return_pcs_unique_proof in
  initialize_hstate_satisfies_threads_match_except_global_variables vr ls;
  init_implies_roots_match vr.lprog ls;
  init_implies_roots_match vr.hprog hs;
  init_implies_unstarted_threads_have_empty_write_buffers vr.lprog ls;
  init_implies_unstarted_threads_have_empty_write_buffers vr.hprog hs;
  vr.global_variables_unaddressed_in_initializers_proof ();
  init_implies_global_variables_unaddressed_in_memory vr.vs vr.lprog ls;
  init_implies_global_variables_unaddressed_in_memory vr.vs vr.hprog hs;
  vr.all_introduced_global_variables_initialized_proof ();
  initialization_ensures_all_gvars_have_types vr.vs vr.tds vr.lprog.global_initializers ls.mem;
  assert (all_gvars_have_types ls.mem vr.vs vr.tds);
  introduce NotStopped? ls.stop_reason ==> vr.inv ls
  with _. (
    vr.inv_is_substep_invariant_proof ();
    vr.atomic_inits_match_regular_inits_proof ();
    assert (vr.latomic_prog.init_f ls)
  )

let init_implies_relation_proof
  (vr: var_hiding_relation_t)
  (ls: Armada.State.t{vr.latomic_prog.init_f ls})
  : GTot (hs_aux: (Armada.State.t * unit){
            let hs, aux = hs_aux in
            vr.hatomic_prog.init_f hs /\ var_hiding_lh_relation vr aux ls hs}) =
  let hs = initialize_hstate vr ls in
  let aux = () in
  vr.atomic_inits_match_regular_inits_proof ();
  initialize_hstate_satisfies_var_hiding_lh_relation vr ls;
  initialize_hstate_satisfies_hinit vr ls;
  (hs, aux)

let lh_relation_implies_refinement_proof
  (vr: var_hiding_relation_t)
  (aux: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t{var_hiding_invariant ls /\ var_hiding_lh_relation vr aux ls hs})
  : squash (refinement_requirement ls hs) =
  ()

let var_hiding_relation_implies_refinement (vr: var_hiding_relation_t)
  (* see .fsti file for spec *) =
  let lr: liftability_relation_t = {
    lsem = make_atomic_semantics armada_semantics;
    hsem = make_atomic_semantics armada_semantics;
    lprog = vr.latomic_prog;
    hprog = vr.hatomic_prog;
    aux_t = unit;
    inv = var_hiding_invariant;
    lh_relation = var_hiding_lh_relation vr;
    progress_t = nat;
    progress_wfr = default_wfr nat;
    progress_measure = var_hiding_progress_measure vr;
    refinement_relation = refinement_requirement;
    paths_liftable_proof = paths_liftable_proof vr;
    inv_stepwise_invariant_proof = (fun u -> inv_stepwise_invariant_proof vr);
    init_implies_relation_proof = init_implies_relation_proof vr;
    lh_relation_implies_refinement_proof = lh_relation_implies_refinement_proof vr;
  } in
  liftability_relation_implies_refinement lr
