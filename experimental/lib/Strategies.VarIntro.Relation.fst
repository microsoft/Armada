module Strategies.VarIntro.Relation

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
open Strategies.ArmadaStatement.Breaking
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
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Helpers
open Strategies.VarIntro.Initialization
open Strategies.VarIntro.Invariant
open Strategies.VarIntro.Propagate
open Util.List
open Util.Nth
open Util.Seq

let actions_among_hactions_implies_pcs_contains_new_pcs_of_actions
  (vr: var_intro_relation_t)
  (actions: list Armada.Action.t)
  : Lemma (requires contains_ubool actions vr.hatomic_prog.actions)
          (ensures  forall action. contains_ubool action actions ==> pcs_contain_new_pcs_of_action vr.hpcs action) =
  vr.hpcs_complete_proof ()

let introduction_succeeds_witness_implies_introduction_succeeds
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  (witness: introduction_succeeds_witness_t vr.vs vr.tds vr.inv)
  : Lemma (requires   valid_introduction_succeeds_witness vr.vs vr.tds vr.inv step.action.program_statement witness
                    /\ step.action.ok
                    /\ step.nd == []
                    /\ vr.inv s
                    /\ all_gvars_have_types s.mem vr.vs vr.tds
                    /\ (match step.action.program_statement.start_pc with
                       | None -> False
                       | Some pc -> thread_state_applies s actor (ThreadStateAtPC pc)))
          (ensures  (let ps = step.action.program_statement in
                     Some? (step_computation actor ps.starts_atomic_block ps.ends_atomic_block step s))) =
  let ps = step.action.program_statement in
  match witness with
  | IntroductionSucceedsBecauseItAssignsConstant ->
      statement_that_updates_gvars_using_constant_must_succeed vr.vs vr.tds actor (Some?.v ps.start_pc)
        ps.end_pc ps.statement s
  | IntroductionSucceedsProof ps' proof ->
      proof actor s

#push-options "--z3rlimit 40"

let executing_matching_steps_maintains_invariant
  (vr: var_intro_relation_t)
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
  (hactions: list Armada.Action.t)
  : Lemma (requires 
            (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
               var_intro_lh_relation_between_steps vr () ls hs
             /\ Some? (step_computation actor lstarts_atomic_block lends_atomic_block lstep ls)
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
             /\ pcs_contain_new_pcs_of_action vr.hpcs hstep.action
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state
             /\ contains_ubool hstep.action hactions
             /\ contains_ubool hactions vr.hatomic_prog.actions))
    (ensures  (match step_computation actor lstarts_atomic_block lends_atomic_block lstep ls,
                     step_computation actor hstarts_atomic_block hends_atomic_block hstep hs with
               | Some ls', Some hs' ->
                   var_intro_lh_relation_between_steps vr () ls' hs'
               | _, _ -> False)) =
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let laction = lstep.action in
  let haction = hstep.action in
  let lps = laction.program_statement in
  let hps = haction.program_statement in
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
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
      let lem2 () : Lemma (all_running_threads_have_pcs_in_list vr.hpcs hs'') = (
        executing_step_maintains_all_running_threads_have_pcs_in_list vr.hpcs actor
          hstarts_atomic_block hends_atomic_block hstep hs
      ) in
      let lem3 () : Lemma (states_match_except_global_variables vr.vs pc_relation ls'' hs'') = (
        update_thread_pcs_in_states_maintains_states_match_except_gvars vr.vs pc_relation
          actor ls' hs' lps.end_pc hps.end_pc
      ) in
      let lem4 () : Lemma (  global_variables_unaddressed_in_memory vr.vs ls''.mem
                           /\ global_variables_unaddressed_in_memory vr.vs hs''.mem
                           /\ roots_match ls''.mem
                           /\ roots_match hs''.mem) = (
        assert (ls''.mem == ls'.mem);
        assert (hs''.mem == hs'.mem)
      ) in
      lem1 ();
      lem2 ();
      lem3 ();
      lem4 ();
      step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor hstarts_atomic_block
        hends_atomic_block hstep hs;
      assert (all_gvars_have_types hs''.mem vr.vs vr.tds);
      assert (states_match_except_global_variables vr.vs pc_relation ls'' hs'');
      introduce NotStopped? hs''.stop_reason ==> vr.inv hs''
      with _. vr.inv_is_substep_invariant_proof ()
  | ComputationUndefined, ComputationUndefined ->
      assert (not lstep.action.ok)

#pop-options
#push-options "--z3rlimit 10"

let executing_step_updating_gvars_maintains_invariant
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (hstarts_atomic_block: bool)
  (hends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (hstep: Armada.Step.t)
  (actions: list Armada.Action.t)
  : Lemma (requires 
            (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
               var_intro_lh_relation_between_steps vr () ls hs
             /\ Some? (step_computation actor hstarts_atomic_block hends_atomic_block hstep hs)
             /\ statement_updates_gvars vr.vs hstep.action.program_statement.statement
             /\ hstep.action.ok
             /\ contains_ubool hstep.action actions
             /\ contains_ubool actions vr.hatomic_prog.actions
             /\ Some? hstep.action.program_statement.end_pc
             /\ pc_relation.relation (ls.threads actor).pc (Some?.v hstep.action.program_statement.end_pc)
             /\ hstarts_atomic_block = hstep.action.program_statement.starts_atomic_block
             /\ hends_atomic_block = hstep.action.program_statement.ends_atomic_block
             /\ pcs_contain_new_pcs_of_action vr.hpcs hstep.action
             /\ thread_state_applies hs actor (action_to_starting_thread_state hstep.action)))
    (ensures  (match step_computation actor hstarts_atomic_block hends_atomic_block hstep hs with
               | Some hs' -> var_intro_lh_relation_between_steps vr () ls hs'
               | _ -> False)) =
  let hthread = hs.threads actor in
  let haction = hstep.action in
  let hps = haction.program_statement in
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  statement_that_updates_gvars_s2_only_maintains_states_match vr.vs pc_relation actor hstep.nd hthread.pc
    hps.end_pc hps.statement ls hs;
  match statement_computation actor hstep.nd hthread.pc hps.end_pc hps.statement hs with
  | ComputationProduces hs' ->
      update_thread_pc_in_state_maintains_states_match_except_gvars vr.vs pc_relation actor ls hs'
        hps.end_pc;
      let hs'' = update_thread_pc_in_state hs' actor hps.end_pc in
      assert (states_match_except_global_variables vr.vs pc_relation ls hs'');
      executing_step_maintains_all_running_threads_have_pcs_in_list vr.hpcs actor hstarts_atomic_block
        hends_atomic_block hstep hs;
      assert (all_running_threads_have_pcs_in_list vr.hpcs hs'');
      assert (global_variables_unaddressed_in_memory vr.vs hs''.mem);
      executing_statement_maintains_unstarted_threads_have_empty_write_buffers actor hstep.nd
        hthread.pc hps.end_pc hps.statement hs;
      step_computation_maintains_all_gvars_have_types vr.vs vr.tds actor hstarts_atomic_block
        hends_atomic_block hstep hs;
      assert (all_gvars_have_types hs''.mem vr.vs vr.tds);
      assert (unstarted_threads_have_empty_write_buffers hs'');
      introduce NotStopped? hs''.stop_reason ==> vr.inv hs''
      with _. vr.inv_is_substep_invariant_proof ()
  | ComputationUndefined ->
      ()

#pop-options
#push-options "--z3rlimit 20"

let establish_invariant_maintained_given_hsteps_at_correct_pc_case_matching
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  (all_hactions: list Armada.Action.t)
  (remaining_mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (laction: Armada.Action.t)
  (remaining_lactions: list Armada.Action.t)
  (haction: Armada.Action.t)
  (remaining_hactions: list Armada.Action.t)
  (lstep: Armada.Step.t)
  (remaining_lsteps: list Armada.Step.t)
  (hstep: Armada.Step.t)
  (remaining_hsteps: list Armada.Step.t)
  : Lemma (requires
            (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
             let lstarts_atomic_block = actions_start_atomic_block lactions in
             let lends_atomic_block = actions_end_atomic_block lactions in
               var_intro_lh_relation_between_steps vr () ls hs
             /\ (Some? (steps_computation_permitting_empty actor lstarts_atomic_block
                         lends_atomic_block lsteps ls))
             /\ lactions == map_ghost armada_step_to_action lsteps
             /\ hactions == map_ghost armada_step_to_action hsteps
             /\ (forall haction. contains_ubool haction hactions ==> pcs_contain_new_pcs_of_action vr.hpcs haction)
             /\ lsteps_correspond_to_hsteps vr.vs vr.tds vr.inv pc_relation
                 lstart_state hstart_state lend_state hend_state mapper lsteps hsteps
             /\ action_list_doesnt_internally_yield lactions
             /\ action_list_doesnt_internally_yield hactions
             /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state
             /\ each_action_ends_atomic_block_if_necessary hactions
             /\ (forall action. contains_ubool action hactions ==> contains_ubool action all_hactions)
             /\ contains_ubool all_hactions vr.hatomic_prog.actions
             /\ mapper == MapperMatching :: remaining_mapper
             /\ lactions == laction :: remaining_lactions
             /\ hactions == haction :: remaining_hactions
             /\ lsteps == lstep :: remaining_lsteps
             /\ hsteps == hstep :: remaining_hsteps))
    (ensures (let lstarts_atomic_block = actions_start_atomic_block lactions in
              let hstarts_atomic_block = actions_start_atomic_block hactions in
              let lps = laction.program_statement in
              let hps = haction.program_statement in
              let laction_ends_atomic_block = lps.ends_atomic_block || not laction.ok in
              let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
              match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls,
                    step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
              | Some ls', Some hs' -> var_intro_lh_relation_between_steps vr () ls' hs'
              | _, _ -> False)) =
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
  map_ghost_contains_ubool armada_step_to_action hsteps hstep;
  assert (contains_ubool hstep.action hactions);
  executing_matching_steps_maintains_invariant vr actor lstart_state hstart_state
    (action_to_ending_thread_state lstep.action) (action_to_ending_thread_state hstep.action)
    lstarts_atomic_block hstarts_atomic_block laction_ends_atomic_block haction_ends_atomic_block
    ls hs lstep hstep all_hactions;
  (match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls,
         step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
   | Some ls', Some hs' ->
       introduce NotStopped? hs'.stop_reason ==> vr.inv hs'
       with _. vr.inv_is_substep_invariant_proof ()
   | _, _ -> ())

let establish_invariant_maintained_given_hsteps_at_correct_pc_case_introduced
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  (all_hactions: list Armada.Action.t)
  (witness: introduction_succeeds_witness_t vr.vs vr.tds vr.inv)
  (remaining_mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (haction: Armada.Action.t)
  (remaining_hactions: list Armada.Action.t)
  (hstep: Armada.Step.t)
  (remaining_hsteps: list Armada.Step.t)
  : Lemma (requires
            (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
             let lstarts_atomic_block = actions_start_atomic_block lactions in
             let lends_atomic_block = actions_end_atomic_block lactions in
               var_intro_lh_relation_between_steps vr () ls hs
             /\ (Some? (steps_computation_permitting_empty actor lstarts_atomic_block
                         lends_atomic_block lsteps ls))
             /\ lactions == map_ghost armada_step_to_action lsteps
             /\ hactions == map_ghost armada_step_to_action hsteps
             /\ (forall haction. contains_ubool haction hactions ==> pcs_contain_new_pcs_of_action vr.hpcs haction)
             /\ lsteps_correspond_to_hsteps vr.vs vr.tds vr.inv pc_relation
                 lstart_state hstart_state lend_state hend_state mapper lsteps hsteps
             /\ action_list_doesnt_internally_yield lactions
             /\ action_list_doesnt_internally_yield hactions
             /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state
             /\ each_action_ends_atomic_block_if_necessary hactions
             /\ (forall action. contains_ubool action hactions ==> contains_ubool action all_hactions)
             /\ contains_ubool all_hactions vr.hatomic_prog.actions
             /\ mapper == MapperIntroduced witness :: remaining_mapper
             /\ hactions == haction :: remaining_hactions
             /\ hsteps == hstep :: remaining_hsteps))
    (ensures (let lstarts_atomic_block = actions_start_atomic_block lactions in
              let hstarts_atomic_block = actions_start_atomic_block hactions in
              let hps = haction.program_statement in
              let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
              (match step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
               | Some hs' -> var_intro_lh_relation_between_steps vr () ls hs'
               | _ -> False))) =
  let hthread = hs.threads actor in
  let hps = haction.program_statement in
  let hstep: Armada.Step.t = hstep in
  let hstarts_atomic_block = actions_start_atomic_block hactions in
  let hends_atomic_block = actions_end_atomic_block hactions in
  let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
  assert (haction_ends_atomic_block = (if (Cons? remaining_hsteps) then false else hends_atomic_block));
  assert (hstep.nd == []);
  introduction_succeeds_witness_implies_introduction_succeeds vr actor hstep hs witness;
  map_ghost_contains_ubool armada_step_to_action hsteps hstep;
  assert (contains_ubool hstep.action hactions);
  executing_step_updating_gvars_maintains_invariant vr actor hstarts_atomic_block haction_ends_atomic_block
    ls hs hstep all_hactions;
  (match step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
   | Some hs' ->
       step_computation_has_thread_state_effect actor hstarts_atomic_block
         haction_ends_atomic_block hstep hs;
       step_computation_has_thread_state_effect actor hstarts_atomic_block
         haction_ends_atomic_block hstep hs;
       introduce NotStopped? hs'.stop_reason ==> vr.inv hs'
       with _. vr.inv_is_substep_invariant_proof ()
   | None -> ())

// Given a "normal" (i.e., not consisting of a propagate step)
// sequence of low-level steps satisfying
// steps_computation_permitting_empty, and a sequence of high-level
// steps satisfying lsteps_correspond_to_hsteps, and given that the
// high-level thread state corresponds to the starting thread state
// required for those high-level steps, show that the outcome of
// executing steps_computation_permitting_empty at the high level
// produces a state related to the low-level produced state by
// var_intro_lh_relation_between_steps.

let rec establish_normal_lifter_given_hsteps_at_correct_pc
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  (all_hactions: list Armada.Action.t)
  : Lemma (requires
            (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
             let lstarts_atomic_block = actions_start_atomic_block lactions in
             let lends_atomic_block = actions_end_atomic_block lactions in
               var_intro_lh_relation_between_steps vr () ls hs
             /\ (Some? (steps_computation_permitting_empty actor lstarts_atomic_block
                         lends_atomic_block lsteps ls))
             /\ lactions == map_ghost armada_step_to_action lsteps
             /\ hactions == map_ghost armada_step_to_action hsteps
             /\ (forall haction. contains_ubool haction hactions ==> pcs_contain_new_pcs_of_action vr.hpcs haction)
             /\ lsteps_correspond_to_hsteps vr.vs vr.tds vr.inv pc_relation
                 lstart_state hstart_state lend_state hend_state mapper lsteps hsteps
             /\ action_list_doesnt_internally_yield lactions
             /\ action_list_doesnt_internally_yield hactions
             /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
             /\ thread_state_applies ls actor lstart_state
             /\ thread_state_applies hs actor hstart_state
             /\ each_action_ends_atomic_block_if_necessary hactions
             /\ (forall action. contains_ubool action hactions ==> contains_ubool action all_hactions)
             /\ contains_ubool all_hactions vr.hatomic_prog.actions))
    (ensures (let lstarts_atomic_block = actions_start_atomic_block lactions in
              let lends_atomic_block = actions_end_atomic_block lactions in
              let hstarts_atomic_block = actions_start_atomic_block hactions in
              let hends_atomic_block = actions_end_atomic_block hactions in
              match steps_computation_permitting_empty actor lstarts_atomic_block lends_atomic_block lsteps ls,
                    steps_computation_permitting_empty actor hstarts_atomic_block hends_atomic_block hsteps hs with
              | Some ls', Some hs' ->
                  var_intro_lh_relation_between_steps vr () ls' hs'
              | _, _ -> False))
    (decreases hsteps) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  match mapper, lactions, hactions, lsteps, hsteps with
  | [], [], [], [], [] -> ()
  | MapperMatching :: remaining_mapper, laction :: remaining_lactions, haction :: remaining_hactions,
      lstep :: remaining_lsteps, hstep :: remaining_hsteps ->
      establish_invariant_maintained_given_hsteps_at_correct_pc_case_matching vr actor ls hs lstart_state hstart_state
        lend_state hend_state mapper lactions hactions lsteps hsteps all_hactions remaining_mapper
        laction remaining_lactions haction remaining_hactions lstep remaining_lsteps hstep remaining_hsteps;
      let lps = laction.program_statement in
      let hps = haction.program_statement in
      let lstarts_atomic_block = actions_start_atomic_block lactions in
      let lends_atomic_block = actions_end_atomic_block lactions in
      let hstarts_atomic_block = actions_start_atomic_block hactions in
      let hends_atomic_block = actions_end_atomic_block hactions in
      let laction_ends_atomic_block = lps.ends_atomic_block || not laction.ok in
      let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
      (match step_computation actor lstarts_atomic_block laction_ends_atomic_block lstep ls,
             step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
       | Some ls', Some hs' ->
           step_computation_has_thread_state_effect actor lstarts_atomic_block laction_ends_atomic_block lstep ls;
           step_computation_has_thread_state_effect actor hstarts_atomic_block haction_ends_atomic_block hstep hs;
           establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls' hs'
             (action_to_ending_thread_state lstep.action)
             (action_to_ending_thread_state hstep.action)
             lend_state hend_state remaining_mapper remaining_lactions remaining_hactions remaining_lsteps
             remaining_hsteps all_hactions)
  | MapperIntroduced witness :: remaining_mapper, _, haction :: remaining_hactions, _, hstep :: remaining_hsteps ->
      let hps = haction.program_statement in
      let hstarts_atomic_block = actions_start_atomic_block hactions in
      let hends_atomic_block = actions_end_atomic_block hactions in
      let haction_ends_atomic_block = hps.ends_atomic_block || not haction.ok in
      establish_invariant_maintained_given_hsteps_at_correct_pc_case_introduced vr actor ls hs lstart_state
        hstart_state lend_state hend_state mapper lactions hactions lsteps hsteps all_hactions witness
        remaining_mapper haction remaining_hactions hstep remaining_hsteps;
      (match step_computation actor hstarts_atomic_block haction_ends_atomic_block hstep hs with
       | Some hs' ->
           step_computation_has_thread_state_effect actor hstarts_atomic_block
             haction_ends_atomic_block hstep hs;
           step_computation_has_thread_state_effect actor hstarts_atomic_block
             haction_ends_atomic_block hstep hs;
           establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls hs'
             lstart_state (action_to_ending_thread_state hstep.action) lend_state hend_state
             remaining_mapper lactions remaining_hactions lsteps remaining_hsteps all_hactions
       | None -> ())
  | _, _, _, _, _ -> ()

#pop-options

let each_action_consistent_with_is_nonyielding_pc_implies_ends_atomic_block_if_necessary
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actions: list Armada.Action.t)
  : Lemma (requires each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc actions)
          (ensures  each_action_ends_atomic_block_if_necessary actions) =
  introduce forall action. contains_ubool action actions ==> action_ends_atomic_block_if_necessary action
  with introduce _ ==> _
  with _. assert (action_consistent_with_is_nonyielding_pc is_nonyielding_pc action)

// Given a "normal" (i.e., not consisting of a propagate step)
// sequence of low-level steps satisfying steps_computation_generic,
// and a sequence of high-level steps satisfying
// lsteps_correspond_to_hsteps and
// laction_haction_correspondence_complete, and given that the
// high-level thread state corresponds to the starting thread state
// required for those high-level steps, return a lifter object for the
// normal sequence of steps.

let get_normal_lifter_given_hsteps_at_correct_pc
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
                 var_intro_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ hactions == map_ghost armada_step_to_action hsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ contains_ubool hactions vr.hatomic_prog.actions
               /\ lsteps_correspond_to_hsteps vr.vs vr.tds vr.inv pc_relation
                   lstart_state hstart_state lend_state hend_state mapper lsteps hsteps
               /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
               /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
               /\ thread_state_applies ls actor lstart_state
               /\ thread_state_applies hs actor hstart_state
               /\ laction_haction_correspondence_complete vr.vs vr.tds vr.inv vr.lpc_to_hpcs vr.is_breaking_hpc
                    vr.hpc_info lactions hactions))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                           (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                           (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  steps_computation_implies_start_and_end_atomic_block actor starts_atomic_block
    ends_atomic_block lsteps ls;
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  assert (var_intro_lh_relation vr () ls hs);
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  assert (Some? (steps_computation_permitting_empty actor starts_atomic_block
                   ends_atomic_block lsteps ls));
  vr.each_laction_doesnt_internally_yield_proof ();
  assert (action_list_doesnt_internally_yield lactions);
  vr.each_haction_doesnt_internally_yield_proof ();
  assert (action_list_doesnt_internally_yield hactions);
  vr.hactions_consistent_with_is_nonyielding_pc_proof ();
  each_action_consistent_with_is_nonyielding_pc_implies_ends_atomic_block_if_necessary vr.is_nonyielding_hpc
    hactions;
  assert (each_action_ends_atomic_block_if_necessary hactions);
  actions_among_hactions_implies_pcs_contains_new_pcs_of_actions vr hactions;
  establish_normal_lifter_given_hsteps_at_correct_pc vr actor ls hs
    lstart_state hstart_state lend_state hend_state mapper lactions hactions lsteps hsteps hactions;
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block hsteps hs;
  let hstarts_atomic_block = actions_start_atomic_block hactions in
  let hends_atomic_block = actions_end_atomic_block hactions in
  vr.hactions_end_in_breaking_pc_proof ();
  steps_computation_maintains_all_threads_breaking vr.is_breaking_hpc actor hstarts_atomic_block
    hends_atomic_block hsteps hs;
  StepLifterLift hsteps ()

#push-options "--z3rlimit 20"

// Given a "normal" (i.e., not consisting of a propagate step)
// sequence of low-level steps satisfying steps_computation_generic,
// and a set of high-level steps known to be introducible, prove that
// executing those high-level steps produces a valid state that's
// related to the current low-level state via
// var_intro_lh_relation_between_steps.

let rec normal_lifter_works_given_hpc_introducible
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (hsteps: list Armada.Step.t)
  (hactions: list Armada.Action.t)
  (hstart_pc: pc_t)
  (hend_pc: pc_t)
  (introduction_succeeds_witnesses: list (introduction_succeeds_witness_t vr.vs vr.tds vr.inv))
  (all_hactions: list Armada.Action.t)
  : Lemma
    (requires   var_intro_lh_relation_between_steps vr () ls hs
              /\ NotStopped? hs.stop_reason
              /\ ThreadStatusRunning? (hs.threads actor).status
              /\ (hs.threads actor).pc = hstart_pc
              /\ hactions_introducible vr.vs vr.tds vr.inv vr.hpc_to_lpc hstart_pc hend_pc
                  introduction_succeeds_witnesses hactions
              /\ hsteps == compute_hsteps_from_hactions hactions
              /\ starts_atomic_block = not (vr.is_nonyielding_hpc hstart_pc)
              /\ ends_atomic_block = not (vr.is_nonyielding_lpc (vr.hpc_to_lpc hstart_pc))
              /\ each_action_consistent_with_is_nonyielding_pc vr.is_nonyielding_hpc hactions
              /\ action_list_doesnt_internally_yield hactions
              /\ Cons? hsteps
              /\ (forall haction. contains_ubool haction hactions ==> pcs_contain_new_pcs_of_action vr.hpcs haction)
              /\ actions_start_atomic_block hactions = starts_atomic_block
              /\ actions_end_atomic_block hactions = ends_atomic_block
              /\ (forall haction. contains_ubool haction hactions ==> contains_ubool haction all_hactions)
              /\ contains_ubool all_hactions vr.hatomic_prog.actions)
    (ensures  (match steps_computation actor starts_atomic_block ends_atomic_block hsteps hs with
               | Some hs' ->
                     var_intro_lh_relation_between_steps vr () ls hs'
                   /\ (hs'.threads actor).pc = hend_pc
               | None -> false))
    (decreases hsteps) =
  match hsteps, hactions, introduction_succeeds_witnesses with
  | [], [], [] -> ()
  | first_hstep :: remaining_hsteps, first_haction :: remaining_hactions,
      witness :: remaining_introduction_succeeds_witnesses ->
      let haction_ends_atomic_block = first_haction.program_statement.ends_atomic_block || not first_haction.ok in
      introduction_succeeds_witness_implies_introduction_succeeds vr actor first_hstep hs witness;
      executing_step_updating_gvars_maintains_invariant vr actor starts_atomic_block haction_ends_atomic_block
        ls hs first_hstep all_hactions;
      vr.inv_is_substep_invariant_proof ();
      step_computation_has_thread_state_effect actor starts_atomic_block haction_ends_atomic_block first_hstep hs;
       (match remaining_hsteps with
       | [] -> ()
       | _ -> (
          match step_computation actor starts_atomic_block haction_ends_atomic_block first_hstep hs with
          | Some hs2 ->
              normal_lifter_works_given_hpc_introducible vr actor haction_ends_atomic_block ends_atomic_block
                 ls hs2 remaining_hsteps remaining_hactions (hs2.threads actor).pc hend_pc
                 remaining_introduction_succeeds_witnesses all_hactions))
  | _, _, _ -> ()

// Given a "normal" (i.e., not consisting of a propagate step)
// sequence of low-level steps satisfying steps_computation_generic,
// and given that the current high-level PC has info indictating it's
// "introducible" (it's possible to introduce an atomic step at the
// high level that makes progress), return a lifter object for the
// normal sequence of steps.

let get_normal_lifter_given_hpc_introducible
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_intro_lh_relation vr () ls hs
              /\ NotStopped? hs.stop_reason
              /\ ThreadStatusRunning? (hs.threads actor).status
              /\ HPCInfoIntroduced? (vr.hpc_info (hs.threads actor).pc)
              /\ starts_atomic_block = not (vr.is_nonyielding_lpc (ls.threads actor).pc))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                           (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                           (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  let hthread = hs.threads actor in                         
  let hpc = hthread.pc in
  assert (list_contains hpc vr.hpcs);
  vr.introduced_atomic_actions_make_progress_proof ();
  assert (introduced_atomic_action_makes_progress vr.vs vr.tds vr.inv vr.hatomic_prog.actions
            vr.hpc_info vr.hpc_to_lpc vr.is_nonyielding_lpc hpc);
  match vr.hpc_info hpc with
  | HPCInfoIntroduced idx end_pc introduction_succeeds_witnesses progress ->
      (match list_nth vr.hatomic_prog.actions idx with
       | Some hactions ->
           assert (hactions_introducible vr.vs vr.tds vr.inv vr.hpc_to_lpc hpc end_pc introduction_succeeds_witnesses
                     hactions);
           let hsteps = compute_hsteps_from_hactions hactions in
           armada_steps_computation_equivalent actor starts_atomic_block
             starts_atomic_block hsteps hs;
           vr.hactions_consistent_with_is_nonyielding_pc_proof ();
           vr.each_haction_doesnt_internally_yield_proof ();
           nth_implies_contains_ubool vr.hatomic_prog.actions idx hactions;
           actions_among_hactions_implies_pcs_contains_new_pcs_of_actions vr hactions;
           normal_lifter_works_given_hpc_introducible vr actor starts_atomic_block starts_atomic_block ls hs
             hsteps hactions hpc end_pc introduction_succeeds_witnesses hactions;
           vr.hactions_end_in_breaking_pc_proof ();
           steps_computation_maintains_all_threads_breaking vr.is_breaking_hpc actor starts_atomic_block
             starts_atomic_block hsteps hs;
           (match steps_computation actor starts_atomic_block starts_atomic_block hsteps hs with
            | Some hs' ->
                let progress_wfr = lex_nondep_wfr (default_wfr nat) (default_wfr nat) in
                let progress_measure = var_intro_progress_measure vr in
                assert (progress_wfr.relation (progress_measure hs' lsteps actor) (progress_measure hs lsteps actor));
            StepLifterIntroduce hsteps ()))

// Given a "normal" (i.e., not consisting of a propagate step)
// sequence of low-level steps satisfying steps_computation_generic,
// and a sequence of high-level steps satisfying
// lsteps_correspond_to_hsteps and
// laction_haction_correspondence_complete, return a lifter object
// for the normal sequence of steps.

let get_normal_lifter_given_hsteps
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vr.vs vr.tds vr.inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
                 var_intro_lh_relation vr () ls hs
               /\ Some? (steps_computation_generic armada_semantics actor
                          starts_atomic_block ends_atomic_block lsteps ls)
               /\ lactions == map_ghost armada_step_to_action lsteps
               /\ hactions == map_ghost armada_step_to_action hsteps
               /\ contains_ubool lactions vr.latomic_prog.actions
               /\ contains_ubool hactions vr.hatomic_prog.actions
               /\ lsteps_correspond_to_hsteps vr.vs vr.tds vr.inv pc_relation
                   lstart_state hstart_state lend_state hend_state mapper lsteps hsteps
               /\ do_actions_start_and_end_atomic_block lactions = do_actions_start_and_end_atomic_block hactions
               /\ laction_haction_correspondence_complete vr.vs vr.tds vr.inv vr.lpc_to_hpcs
                   vr.is_breaking_hpc vr.hpc_info lactions hactions))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                           (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                           (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps ls;
  steps_computation_requires_start_thread_state actor starts_atomic_block ends_atomic_block lsteps ls;
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  lsteps_correspond_to_hsteps_implies_first_lstep_matches_lstart_state vr.vs vr.tds vr.inv
    pc_relation lstart_state hstart_state lend_state hend_state mapper lsteps hsteps;
  match lstart_state, hstart_state with
  | ThreadStateAtPC start_lpc, ThreadStateAtPC start_hpc ->
      assert (lstart_state = action_to_starting_thread_state (Cons?.hd lsteps).action);
      assert (lthread.pc = start_lpc);
      assert (threads_match_except_global_variables vr.vs pc_relation ls.threads hs.threads);
      assert (ThreadStatusRunning? lthread.status);
      assert (pc_relation.relation lthread.pc hthread.pc);
      assert (vr.hpc_to_lpc hthread.pc = lthread.pc);
      vr.lpc_to_hpcs_consistent_with_hpc_to_lpc_proof ();
      implication_of_contains_and_for_all
        (laction_haction_correspondence_complete_inner vr.vs vr.tds vr.inv vr.is_breaking_hpc vr.hpc_info start_hpc)
        hthread.pc (vr.lpc_to_hpcs start_lpc);
      assert (laction_haction_correspondence_complete_inner vr.vs vr.tds vr.inv vr.is_breaking_hpc vr.hpc_info
                start_hpc hthread.pc);
      if hthread.pc = start_hpc then
        get_normal_lifter_given_hsteps_at_correct_pc vr actor starts_atomic_block ends_atomic_block ls hs
          lstart_state hstart_state lend_state hend_state mapper lactions hactions lsteps hsteps
      else if not (vr.is_breaking_hpc hthread.pc) then (
        assert (all_threads_breaking vr.is_breaking_hpc hs);
        false_elim ()
      )
      else (
        vr.lactions_consistent_with_is_nonyielding_pc_proof ();
        assert (for_all_ghost (each_action_consistent_with_is_nonyielding_pc vr.is_nonyielding_lpc)
                  vr.latomic_prog.actions);
        assert (each_action_consistent_with_is_nonyielding_pc vr.is_nonyielding_lpc lactions);
        assert (action_consistent_with_is_nonyielding_pc vr.is_nonyielding_lpc (Cons?.hd lsteps).action);
        assert (starts_atomic_block = not (vr.is_nonyielding_lpc lthread.pc));
        get_normal_lifter_given_hpc_introducible vr actor starts_atomic_block ends_atomic_block ls hs lsteps
      )
  | _, _ -> false_elim ()

// Prove that every "normal" (i.e., not consisting of a propagate
// step) sequence of steps satisfying steps_computation_generic is
// liftable by returning the lifter for a given normal squence of
// steps.

let get_normal_lifter
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_intro_lh_relation vr () ls hs
              /\ Some? (steps_computation_generic armada_semantics actor
                         starts_atomic_block ends_atomic_block lsteps ls)
              /\ contains_ubool (map_ghost armada_step_to_action lsteps) vr.latomic_prog.actions
              /\ ~((Cons?.hd lsteps).action.program_statement.statement == PropagateWriteMessageStatement))
    (ensures  fun lifter -> step_lifter_works
                           (make_atomic_semantics armada_semantics)
                           (make_atomic_semantics armada_semantics)
                           vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                           (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                           (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
                           lsteps ls hs lifter) =
  vr.corresponding_hactions_correspond_proof ();
  let lactions = map_ghost armada_step_to_action lsteps in
  let correspondence = get_correspondent_from_lists_correspond_ubool
    (lactions_correspond_to_hactions_per_correspondence vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.lpc_to_hpcs vr.return_hpcs
       vr.is_breaking_hpc vr.hpc_info vr.hatomic_prog.actions)
    vr.latomic_prog.actions
    vr.corresponding_hactions_info
    lactions in
  match correspondence with
  | CorrespondencePropagate hidx -> false_elim ()
  | CorrespondenceNormal hidx mapper ->
      (match list_nth vr.hatomic_prog.actions hidx with
       | Some hactions ->
           let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
           nth_implies_contains_ubool vr.hatomic_prog.actions hidx hactions;
           let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
           let lend_state = actions_to_ending_thread_state lactions in
           let hstart_state = action_to_starting_thread_state (Cons?.hd hactions) in
           let hend_state = actions_to_ending_thread_state hactions in
           let hsteps = compute_hsteps_from_lsteps vr.vs vr.tds vr.inv vr.hpc_to_lpc
                          vr.return_hpcs vr.return_pcs_unique_proof lstart_state hstart_state lend_state
                          hend_state mapper lactions hactions lsteps in
           get_normal_lifter_given_hsteps vr actor starts_atomic_block ends_atomic_block ls hs
             lstart_state hstart_state lend_state hend_state mapper lactions hactions lsteps hsteps)

#pop-options

// Prove that every sequence of steps satisfying
// steps_computation_generic is liftable by returning the lifter for a
// given sequence of steps.

let get_lifter_for_path
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t{
       var_intro_lh_relation vr () ls hs
     /\ Some? (steps_computation_generic armada_semantics actor
                starts_atomic_block ends_atomic_block lsteps ls)
     /\ contains_ubool (map_ghost armada_step_to_action lsteps) vr.latomic_prog.actions})
  : GTot (lifter: (step_lifter_t (list Armada.Step.t) unit){
            step_lifter_works
              (make_atomic_semantics armada_semantics)
              (make_atomic_semantics armada_semantics)
              vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
              (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
              (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
              lsteps ls hs lifter}) =
  match lsteps with
  | first_step :: remaining_steps ->
      (match first_step.action.program_statement.statement with
       | PropagateWriteMessageStatement ->
           get_propagate_lifter vr actor starts_atomic_block ends_atomic_block ls hs lsteps
       | _ -> get_normal_lifter vr actor starts_atomic_block ends_atomic_block ls hs lsteps)

// Prove that every sequence of steps satisfying
// step_computation_generic is liftable by returning the lifter for a
// given sequence of steps.

let paths_liftable_proof
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (aux: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t{
       var_intro_invariant ls
     /\ var_intro_lh_relation vr aux ls hs
     /\ Some? (step_computation_generic (make_atomic_semantics armada_semantics)
                actor starts_atomic_block ends_atomic_block lsteps ls)
     /\ program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
         vr.latomic_prog lsteps})
  : GTot (lifter: (step_lifter_t (list Armada.Step.t) unit){
            step_lifter_works
              (make_atomic_semantics armada_semantics)
              (make_atomic_semantics armada_semantics)
              vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
              (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
              (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block
              lsteps ls hs lifter}) =
  get_lifter_for_path vr actor starts_atomic_block ends_atomic_block ls hs lsteps

let inv_stepwise_invariant_proof
  (vr: var_intro_relation_t)
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)
             vr.latomic_prog var_intro_invariant) =
  ()

let initialize_hstate
  (vr: var_intro_relation_t)
  (ls: Armada.State.t)
  : GTot Armada.State.t =
  let mem' = apply_introduced_initializers vr.which_initializers_are_intros vr.hprog.global_initializers ls.mem in
  let thread = ls.threads ls.initial_tid in
  let thread' = { thread with pc = vr.hprog.main_start_pc } in
  let threads' = Spec.Map.upd ls.threads ls.initial_tid thread' in
  { ls with mem = mem'; threads = threads' }

let initialize_hstate_satisfies_hinit
  (vr: var_intro_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  init_program vr.hprog (initialize_hstate vr ls)) =
  let hs = initialize_hstate vr ls in
  vr.program_inits_match_except_global_variables_proof ();
  vr.hinitializers_with_same_variable_id_match_proof ();
  apply_introduced_initializers_ensures_satisfies_global_initializers vr.vs vr.which_initializers_are_intros
    vr.lprog.global_initializers vr.hprog.global_initializers ls.mem;
  let thread = hs.threads hs.initial_tid in
  let initial_frame_uniq = Cons?.hd hs.uniqs_used in
  apply_introduced_initializers_ensures_satisfies_main_stack_initializers vr.vs vr.which_initializers_are_intros
    vr.hprog.global_initializers hs.initial_tid vr.hprog.main_method_id initial_frame_uniq
    thread.top.local_variables vr.hprog.main_stack_initializers ls.mem;
  apply_introduced_initializers_ensures_memory_invalid_outside_initializations vr.vs vr.which_initializers_are_intros
    vr.lprog.global_initializers vr.hprog.global_initializers hs.initial_tid vr.hprog.main_method_id initial_frame_uniq
    thread.top.local_variables ls.mem

let rec apply_introduced_initializers_ensures_gvar_has_type
  (vs: list var_id_t)
  (mem: Armada.Memory.t)
  (which_initializers_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (v: var_id_t)
  (td: object_td_t)
  (init: initializer_t)
  : Lemma (requires   initializers_match_except_global_variables vs which_initializers_are_intros linits hinits
                    /\ initializers_with_same_variable_id_match hinits
                    /\ contains_ubool init hinits
                    /\ initializer_matches_variable_and_td v td init
                    /\ list_contains v vs)
          (ensures  (let mem' = apply_introduced_initializers which_initializers_are_intros hinits mem in
                     gvar_has_type mem' v td)) =
  match which_initializers_are_intros, linits, hinits with
  | [], _, _ -> false_elim ()
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      let mem' = apply_introduced_initializers remaining_which_are_intros remaining_hinits mem in
      if eqb first_hinit init then
        apply_introduced_initializer_ensures_gvar_has_type first_hinit mem'
      else (
        apply_introduced_initializers_ensures_gvar_has_type vs mem remaining_which_are_intros
          linits remaining_hinits v td init;
        apply_introduced_initializer_ensures_gvar_has_type first_hinit mem'
      )
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      apply_introduced_initializers_ensures_gvar_has_type vs mem remaining_which_are_intros
        remaining_linits remaining_hinits v td init
  | _, _, _ -> false_elim ()

// Prove, by expanding the recursive definition of
// apply_introduced_initializers, that it ensures all_gvars_have_types
// for the given list vs. We need the extra condition that every
// variable in vs is also in vr.vs.

let rec apply_introduced_initializers_ensures_all_gvars_have_types_helper
  (vr: var_intro_relation_t)
  (mem: Armada.Memory.t)
  (which_initializers_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (vs: list var_id_t)
  (tds: list object_td_t)
  : Lemma (requires   initializers_match_except_global_variables vr.vs which_initializers_are_intros linits hinits
                    /\ initializers_with_same_variable_id_match hinits
                    /\ every_variable_appears_among_initializers hinits vs tds
                    /\ (forall v. list_contains v vs ==> list_contains v vr.vs))
          (ensures  (let mem' = apply_introduced_initializers which_initializers_are_intros hinits mem in
                     all_gvars_have_types mem' vs tds)) =
  match vs, tds with
  | [], [] -> ()
  | first_v :: remaining_vs, first_td :: remaining_tds ->
      let init = exists_ubool_to_witness (initializer_matches_variable_and_td first_v first_td) hinits in
      apply_introduced_initializers_ensures_gvar_has_type vr.vs mem which_initializers_are_intros linits hinits
        first_v first_td init;
      apply_introduced_initializers_ensures_all_gvars_have_types_helper vr mem
        which_initializers_are_intros linits hinits remaining_vs remaining_tds

let apply_introduced_initializers_ensures_all_gvars_have_types
  (vr: var_intro_relation_t)
  (mem: Armada.Memory.t)
  (which_initializers_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  : Lemma (requires   initializers_match_except_global_variables vr.vs which_initializers_are_intros linits hinits
                    /\ initializers_with_same_variable_id_match hinits
                    /\ every_variable_appears_among_initializers hinits vr.vs vr.tds)
          (ensures  (let mem' = apply_introduced_initializers which_initializers_are_intros hinits mem in
                     all_gvars_have_types mem' vr.vs vr.tds)) =
  apply_introduced_initializers_ensures_all_gvars_have_types_helper vr mem which_initializers_are_intros
    linits hinits vr.vs vr.tds

let initialize_hstate_ensures_all_variables_among_gvars
  (vr: var_intro_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  (let hs = initialize_hstate vr ls in
                     all_gvars_have_types hs.mem vr.vs vr.tds)) =
  vr.all_introduced_global_variables_initialized_proof ();
  vr.program_inits_match_except_global_variables_proof ();
  vr.hinitializers_with_same_variable_id_match_proof ();
  apply_introduced_initializers_ensures_all_gvars_have_types vr ls.mem vr.which_initializers_are_intros
    vr.lprog.global_initializers vr.hprog.global_initializers

#push-options "--z3rlimit 10"

let initialize_hstate_satisfies_threads_match_except_global_variables
  (vr: var_intro_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  (let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs
                                         vr.return_pcs_unique_proof in
                     let hs = initialize_hstate vr ls in
                     threads_match_except_global_variables vr.vs pc_relation ls.threads hs.threads)) =
  vr.initial_pcs_correspond_proof ()

#pop-options

let initialize_hstate_satisfies_var_intro_lh_relation
  (vr: var_intro_relation_t)
  (ls: Armada.State.t)
  : Lemma (requires init_program vr.lprog ls)
          (ensures  var_intro_lh_relation vr () ls (initialize_hstate vr ls)) =
  let hs = initialize_hstate vr ls in
  initialize_hstate_satisfies_hinit vr ls;
  vr.program_inits_match_except_global_variables_proof ();
  vr.hinitializers_with_same_variable_id_match_proof ();
  apply_introduced_initializers_ensures_satisfies_global_initializers vr.vs vr.which_initializers_are_intros
    vr.lprog.global_initializers vr.hprog.global_initializers ls.mem;
  init_implies_positions_valid_in_state vr.hprog hs;
  init_implies_roots_match vr.hprog hs;
  init_implies_unstarted_threads_have_empty_write_buffers vr.hprog hs;
  init_implies_positions_valid_in_state vr.lprog ls;
  init_implies_roots_match vr.lprog ls;
  init_implies_unstarted_threads_have_empty_write_buffers vr.lprog ls;
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  initialize_hstate_satisfies_threads_match_except_global_variables vr ls;
  vr.initial_pc_in_pcs_proof ();
  vr.initial_pc_breaking_proof ();
  init_implies_roots_match vr.lprog ls;
  init_implies_roots_match vr.hprog hs;
  init_implies_unstarted_threads_have_empty_write_buffers vr.lprog ls;
  init_implies_unstarted_threads_have_empty_write_buffers vr.hprog hs;
  vr.global_variables_unaddressed_in_initializers_proof ();
  init_implies_global_variables_unaddressed_in_memory vr.vs vr.lprog ls;
  init_implies_global_variables_unaddressed_in_memory vr.vs vr.hprog hs;
  initialize_hstate_ensures_all_variables_among_gvars vr ls;
  introduce NotStopped? hs.stop_reason ==> vr.inv hs
  with _. (
    vr.inv_is_substep_invariant_proof ();
    vr.atomic_inits_match_regular_inits_proof ();
    assert (vr.hatomic_prog.init_f hs)
  )

let init_implies_relation_proof
  (vr: var_intro_relation_t)
  (ls: Armada.State.t{vr.latomic_prog.init_f ls})
  : GTot (hs_aux: (Armada.State.t * unit){
            let hs, aux = hs_aux in
            vr.hatomic_prog.init_f hs /\ var_intro_lh_relation vr aux ls hs}) =
  let hs = initialize_hstate vr ls in
  let aux = () in
  vr.atomic_inits_match_regular_inits_proof ();
  initialize_hstate_satisfies_var_intro_lh_relation vr ls;
  initialize_hstate_satisfies_hinit vr ls;
  (hs, aux)

let lh_relation_implies_refinement_proof
  (vr: var_intro_relation_t)
  (aux: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t{var_intro_invariant ls /\ var_intro_lh_relation vr aux ls hs})
  : squash (refinement_requirement ls hs) =
  ()

let var_intro_relation_implies_refinement (vr: var_intro_relation_t)
  (* see .fsti file for spec *) =
  let lr: liftability_relation_t = {
    lsem = make_atomic_semantics armada_semantics;
    hsem = make_atomic_semantics armada_semantics;
    lprog = vr.latomic_prog;
    hprog = vr.hatomic_prog;
    aux_t = unit;
    inv = var_intro_invariant;
    lh_relation = var_intro_lh_relation vr;
    progress_t = nat * nat;
    progress_wfr = lex_nondep_wfr (default_wfr nat) (default_wfr nat);
    progress_measure = var_intro_progress_measure vr;
    refinement_relation = refinement_requirement;
    paths_liftable_proof = paths_liftable_proof vr;
    inv_stepwise_invariant_proof = (fun u -> inv_stepwise_invariant_proof vr);
    init_implies_relation_proof = init_implies_relation_proof vr;
    lh_relation_implies_refinement_proof = lh_relation_implies_refinement_proof vr;
  } in
  liftability_relation_implies_refinement lr
