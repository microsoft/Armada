module Strategies.VarIntro.Helpers

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
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.GlobalVars
open Strategies.GlobalVars.Init
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Util.List
open Util.Nth
open Util.Seq

/// Definitions

let return_pcs_unique_proof_t (hpc_to_lpc: pc_t -> GTot pc_t) (return_hpcs: list pc_t) =
  unit -> Lemma (return_pcs_unique hpc_to_lpc return_hpcs)

let var_intro_pc_relation
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (return_pcs_unique_proof: return_pcs_unique_proof_t hpc_to_lpc return_hpcs)
  : pc_relation_t =
  return_pcs_unique_proof ();
  let return_relation = (fun lpc hpc -> list_contains hpc return_hpcs && hpc_to_lpc hpc = lpc) in
  {
    relation = (fun lpc hpc -> hpc_to_lpc hpc = lpc);
    return_relation = return_relation;
  }

let rec compute_hsteps_from_hactions
  (hactions: list Armada.Action.t)
  : Ghost (list Armada.Step.t)
    (requires True)
    (ensures fun hsteps -> map_ghost armada_step_to_action hsteps == hactions) =
  match hactions with
  | [] -> []
  | first_haction :: remaining_hactions ->
      let first_hstep = { nd = []; action = first_haction } in
      first_hstep :: compute_hsteps_from_hactions remaining_hactions

/// Preserving all_running_threads_have_pcs_in_list

let all_running_threads_have_pcs_in_list
  (pcs: list pc_t)
  (s: Armada.State.t)
  : GTot ubool =
  NotStopped? s.stop_reason ==>
    (forall tid.{:pattern s.threads tid} let thread = s.threads tid in
       ThreadStatusRunning? thread.status ==> list_contains thread.pc pcs)

let propagate_maintains_all_running_threads_have_pcs_in_list
  (actor: tid_t)
  (nd: nondeterminism_t)
  (pcs: list pc_t)
  (s: Armada.State.t)
  : Lemma (requires   all_running_threads_have_pcs_in_list pcs s
                    /\ unstarted_threads_have_empty_write_buffers s
                    /\ (ComputationProduces? (propagate_write_message_statement_computation actor nd s)))
          (ensures  (let s' = ComputationProduces?.result (propagate_write_message_statement_computation actor nd s) in
                       all_running_threads_have_pcs_in_list pcs s'
                     /\ unstarted_threads_have_empty_write_buffers s')) =
 ()

let executing_step_maintains_all_running_threads_have_pcs_in_list
  (pcs: list pc_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_running_threads_have_pcs_in_list pcs s
                    /\ pcs_contain_new_pcs_of_action pcs step.action
                    /\ list_contains (s.threads actor).pc pcs)
          (ensures  (match step_computation actor starts_atomic_block ends_atomic_block step s with
                     | Some s' -> all_running_threads_have_pcs_in_list pcs s'
                     | None -> True)) =
  match step_computation actor starts_atomic_block ends_atomic_block step s with
  | Some s' ->
      step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s;
      executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s
  | None -> ()

/// Correspondence between lsteps and hsteps

let lstep_corresponds_to_hstep
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (lstep: Armada.Step.t)
  (hstep: Armada.Step.t)
  : GTot ubool =
  let lps, hps = lstep.action.program_statement, hstep.action.program_statement in
    lstep.nd == hstep.nd
  /\ statement_effect_independent_of_global_variables vs lps.statement
  /\ program_statements_match_per_pc_relation pc_relation.relation pc_relation.return_relation lps hps

let rec lsteps_correspond_to_hsteps
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (pc_relation: pc_relation_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : GTot ubool
  (decreases hsteps) =
  match mapper, lsteps, hsteps with
  | [], [], [] -> True
  | MapperMatching :: remaining_mapper, first_lstep :: remaining_lsteps, first_hstep :: remaining_hsteps ->
      let first_lstep: Armada.Step.t = first_lstep in
      let first_hstep: Armada.Step.t = first_hstep in
         lstep_corresponds_to_hstep vs pc_relation first_lstep first_hstep
      /\ action_to_starting_thread_state first_lstep.action = lstart_state
      /\ action_to_starting_thread_state first_hstep.action = hstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ ThreadStateAtPC? hstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation
           (action_to_ending_thread_state first_lstep.action) (action_to_ending_thread_state first_hstep.action)
      /\ lsteps_correspond_to_hsteps vs tds inv pc_relation
           (action_to_ending_thread_state first_lstep.action) (action_to_ending_thread_state first_hstep.action)
           lend_state hend_state remaining_mapper remaining_lsteps remaining_hsteps
  | MapperIntroduced witness :: remaining_mapper, _, first_hstep :: remaining_hsteps ->
        first_hstep.action.ok
      /\ Nil? first_hstep.nd
      /\ action_to_starting_thread_state first_hstep.action = hstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state
           (action_to_ending_thread_state first_hstep.action)
      /\ valid_introduction_succeeds_witness vs tds inv first_hstep.action.program_statement witness
      /\ statement_updates_gvars vs first_hstep.action.program_statement.statement
      /\ lsteps_correspond_to_hsteps vs tds inv pc_relation lstart_state
           (action_to_ending_thread_state first_hstep.action) lend_state hend_state
           remaining_mapper lsteps remaining_hsteps
  | _, _, _ -> False

#push-options "--z3rlimit 10"

let rec compute_hsteps_from_lsteps
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (hpc_to_lpc: pc_t -> GTot pc_t)
  (return_hpcs: list pc_t)
  (return_pcs_unique_proof: return_pcs_unique_proof_t hpc_to_lpc return_hpcs)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  : Ghost (list Armada.Step.t)
    (requires   lactions == map_ghost armada_step_to_action lsteps
              /\ lactions_correspond_to_hactions vs tds inv hpc_to_lpc return_hpcs lstart_state hstart_state
                  lend_state hend_state mapper lactions hactions)
    (ensures  fun hsteps -> (let pc_relation = var_intro_pc_relation hpc_to_lpc return_hpcs return_pcs_unique_proof in
                            lsteps_correspond_to_hsteps vs tds inv pc_relation lstart_state hstart_state
                              lend_state hend_state mapper lsteps hsteps
                          /\ hactions == map_ghost armada_step_to_action hsteps))
    (decreases hactions) =
  let pc_relation = var_intro_pc_relation hpc_to_lpc return_hpcs return_pcs_unique_proof in
  match mapper, lactions, hactions, lsteps with
  | [], [], [], [] -> []
  | MapperMatching :: remaining_mapper, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lstep :: remaining_lsteps ->
      let first_lstep: Armada.Step.t = first_lstep in
      let hstep = { nd = first_lstep.nd; action = first_haction } in
      let lnext_start_state = action_to_ending_thread_state first_laction in
      let hnext_start_state = action_to_ending_thread_state first_haction in
      let hsteps' = compute_hsteps_from_lsteps vs tds inv hpc_to_lpc return_hpcs return_pcs_unique_proof
                      lnext_start_state hnext_start_state lend_state hend_state remaining_mapper remaining_lactions
                      remaining_hactions remaining_lsteps in
      let hsteps = hstep :: hsteps' in
      assert (lsteps_correspond_to_hsteps vs tds inv pc_relation lstart_state hstart_state
                lend_state hend_state mapper lsteps hsteps);
      hsteps
  | MapperIntroduced _ :: remaining_mapper, _, first_haction :: remaining_hactions, _ ->
      let hstep = { nd = []; action = { ok = true; program_statement = first_haction.program_statement } } in
      let hnext_start_state = action_to_ending_thread_state first_haction in
      let hsteps' = compute_hsteps_from_lsteps vs tds inv hpc_to_lpc return_hpcs return_pcs_unique_proof
                      lstart_state hnext_start_state lend_state hend_state remaining_mapper lactions
                      remaining_hactions lsteps in
      let hsteps = hstep :: hsteps' in
      assert (lsteps_correspond_to_hsteps vs tds inv pc_relation lstart_state hstart_state
                lend_state hend_state mapper lsteps hsteps);
      hsteps
  | _, _, _, _ -> false_elim ()

#pop-options

let lstep_corresponds_to_hstep_clarifier
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (lstep: Armada.Step.t)
  (hstep: Armada.Step.t)
  : Lemma (requires lstep_corresponds_to_hstep vs pc_relation lstep hstep)
          (ensures  (let lps, hps = lstep.action.program_statement, hstep.action.program_statement in
                     match lps.end_pc, hps.end_pc with
                     | Some lpc, Some hpc ->
                           pc_relation.relation lpc hpc
                         /\ (ReturnStatement? lps.statement ==> pc_relation.return_relation lpc hpc)
                     | None, None -> True
                     | _, _ -> False)) =
  ()

let rec lactions_correspond_to_hactions_implies_not_propagate
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
  : Lemma (requires lactions_correspond_to_hactions vs tds inv hpc_to_lpc return_hpcs lstart_state hstart_state
                      lend_state hend_state mapper lactions hactions
                    /\ Cons? lactions)
          (ensures  ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement))
          (decreases hactions) =
  match mapper, lactions, hactions with
  | [], [], [] -> ()
  | MapperMatching :: remaining_mapper, first_laction :: remaining_lactions, first_haction :: remaining_hactions ->
      assert (laction_corresponds_to_haction vs hpc_to_lpc return_hpcs first_laction first_haction);
      assert (~(PropagateWriteMessageStatement? first_laction.program_statement.statement))
  | MapperIntroduced _ :: remaining_mapper, _, first_haction :: remaining_hactions ->
      lactions_correspond_to_hactions_implies_not_propagate vs tds inv hpc_to_lpc return_hpcs lstart_state
           (action_to_ending_thread_state first_haction) lend_state hend_state
           remaining_mapper lactions remaining_hactions
  | _, _, _ -> ()

#push-options "--z3rlimit 10"

let rec lsteps_correspond_to_hsteps_implies_first_lstep_matches_lstart_state
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inv: invariant_t Armada.State.t)
  (pc_relation: pc_relation_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (mapper: list (haction_mapper_t vs tds inv))
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Lemma (requires Cons? lsteps
                    /\ lsteps_correspond_to_hsteps vs tds inv pc_relation lstart_state hstart_state lend_state
                        hend_state mapper lsteps hsteps)
          (ensures    lstart_state = action_to_starting_thread_state (Cons?.hd lsteps).action
                    /\ ThreadStateAtPC? lstart_state)
          (decreases hsteps) =
  match mapper, lsteps, hsteps with
  | [], [], [] -> false_elim ()
  | MapperMatching :: remaining_mapper, first_lstep :: remaining_lsteps, first_hstep :: remaining_hsteps ->
      ()
  | MapperIntroduced _ :: remaining_mapper, _, first_hstep :: remaining_hsteps ->
      let first_hstep: Armada.Step.t = first_hstep in
      lsteps_correspond_to_hsteps_implies_first_lstep_matches_lstart_state vs tds inv pc_relation
        lstart_state (action_to_ending_thread_state first_hstep.action) lend_state hend_state
        remaining_mapper lsteps remaining_hsteps
  | _, _, _ -> false_elim ()

#pop-options


let rec propagate_maintains_all_gvars_have_types
  (vs: list var_id_t)
  (tds: list object_td_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s: Armada.State.t)
  : Lemma (requires   all_gvars_have_types s.mem vs tds
                    /\ (ComputationProduces? (propagate_write_message_statement_computation actor nd s)))
          (ensures  (let s' = ComputationProduces?.result (propagate_write_message_statement_computation actor nd s) in
                     all_gvars_have_types s'.mem vs tds)) =
  match vs, tds with
  | [], [] -> ()
  | first_v :: remaining_vs, first_td :: remaining_tds ->
      propagate_write_message_statement_computation_maintains_gvar_has_type first_v first_td actor nd s;
      propagate_maintains_all_gvars_have_types remaining_vs remaining_tds actor nd s

/// Maintaining states_match_except_global_variables

let update_thread_pcs_in_states_maintains_states_match_except_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (end_pc1: option pc_t)
  (end_pc2: option pc_t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ optional_pcs_match_per_pc_relation pc_relation end_pc1 end_pc2)
          (ensures  (let s1' = update_thread_pc_in_state s1 actor end_pc1 in
                     let s2' = update_thread_pc_in_state s2 actor end_pc2 in
                     states_match_except_global_variables vs pc_relation s1' s2')) =
  ()

let update_thread_pc_in_state_maintains_states_match_except_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (end_pc2: option pc_t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ Some? end_pc2
                    /\ pc_relation.relation (s1.threads actor).pc (Some?.v end_pc2))
          (ensures  (let s2' = update_thread_pc_in_state s2 actor end_pc2 in
                     states_match_except_global_variables vs pc_relation s1 s2')) =
  ()
