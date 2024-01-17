module Strategies.VarHiding.Helpers

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
open Strategies.ArmadaStatement.Propagate
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
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Util.List
open Util.Nth
open Util.Seq

/// Definitions

let return_pcs_unique_proof_t (lpc_to_hpc: pc_t -> GTot pc_t) (return_lpcs: list pc_t) =
  unit -> Lemma (return_pcs_unique lpc_to_hpc return_lpcs)

let var_hiding_pc_relation
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (return_pcs_unique_proof: return_pcs_unique_proof_t lpc_to_hpc return_lpcs)
  : pc_relation_t =
  return_pcs_unique_proof ();
  let return_relation = (fun lpc hpc -> list_contains lpc return_lpcs && lpc_to_hpc lpc = hpc) in
  {
    relation = (fun lpc hpc -> lpc_to_hpc lpc = hpc);
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
  /\ statements_match_per_pc_relation pc_relation.relation pc_relation.return_relation lps.statement hps.statement
  /\ (match lps.end_pc, hps.end_pc with
     | Some lpc, Some hpc ->
           pc_relation.relation lpc hpc
         /\ (ReturnStatement? lps.statement ==> pc_relation.return_relation lpc hpc)
     | None, None -> True
     | _, _ -> False)

let rec lsteps_correspond_to_hsteps
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : GTot ubool
  (decreases lsteps) =
  match which_actions_hidden, lsteps, hsteps with
  | [], [], [] -> True
  | false :: remaining_which_actions_hidden, first_lstep :: remaining_lsteps, first_hstep :: remaining_hsteps ->
      let first_lstep: Armada.Step.t = first_lstep in
      let first_hstep: Armada.Step.t = first_hstep in
         lstep_corresponds_to_hstep vs pc_relation first_lstep first_hstep
      /\ action_to_starting_thread_state first_lstep.action = lstart_state
      /\ action_to_starting_thread_state first_hstep.action = hstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ ThreadStateAtPC? hstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation (action_to_ending_thread_state first_lstep.action)
           (action_to_ending_thread_state first_hstep.action)
      /\ lsteps_correspond_to_hsteps vs pc_relation
           (action_to_ending_thread_state first_lstep.action) (action_to_ending_thread_state first_hstep.action)
           lend_state hend_state remaining_which_actions_hidden remaining_lsteps remaining_hsteps
  | true :: remaining_which_actions_hidden, first_lstep :: remaining_lsteps, _ ->
         action_to_starting_thread_state first_lstep.action = lstart_state
      /\ ThreadStateAtPC? lstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation lstart_state hstart_state
      /\ thread_states_match_per_pc_relation pc_relation.relation
           (action_to_ending_thread_state first_lstep.action) hstart_state
      /\ statement_updates_gvars vs first_lstep.action.program_statement.statement
      /\ lsteps_correspond_to_hsteps vs pc_relation (action_to_ending_thread_state first_lstep.action)
           hstart_state lend_state hend_state remaining_which_actions_hidden remaining_lsteps hsteps
  | _, _, _ -> False

#push-options "--split_queries always"
let rec compute_hsteps_from_lsteps
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (return_lpcs: list pc_t)
  (return_pcs_unique_proof: return_pcs_unique_proof_t lpc_to_hpc return_lpcs)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lactions: list Armada.Action.t)
  (hactions: list Armada.Action.t)
  (lsteps: list Armada.Step.t)
  : Ghost (list Armada.Step.t)
    (requires   lactions == map_ghost armada_step_to_action lsteps
              /\ lactions_correspond_to_hactions vs lpc_to_hpc return_lpcs lstart_state hstart_state
                  lend_state hend_state which_actions_hidden lactions hactions)
    (ensures  fun hsteps -> (let pc_relation = var_hiding_pc_relation lpc_to_hpc return_lpcs return_pcs_unique_proof in
                            lsteps_correspond_to_hsteps vs pc_relation lstart_state hstart_state
                              lend_state hend_state which_actions_hidden lsteps hsteps
                          /\ hactions == map_ghost armada_step_to_action hsteps))
    (decreases lactions) =
  let pc_relation = var_hiding_pc_relation lpc_to_hpc return_lpcs return_pcs_unique_proof in
  match which_actions_hidden, lactions, hactions, lsteps with
  | [], [], [], [] -> []
  | false :: remaining_which_actions_hidden, first_laction :: remaining_lactions, first_haction :: remaining_hactions,
      first_lstep :: remaining_lsteps ->
      let first_lstep: Armada.Step.t = first_lstep in
      let hstep = { nd = first_lstep.nd; action = first_haction } in
      let lnext_start_state = action_to_ending_thread_state first_laction in
      let hnext_start_state = action_to_ending_thread_state first_haction in
      let hsteps' = compute_hsteps_from_lsteps vs lpc_to_hpc return_lpcs return_pcs_unique_proof
                      lnext_start_state hnext_start_state lend_state hend_state remaining_which_actions_hidden
                      remaining_lactions remaining_hactions remaining_lsteps in
      let hsteps = hstep :: hsteps' in
      assert (lsteps_correspond_to_hsteps vs pc_relation lstart_state hstart_state lend_state hend_state
                which_actions_hidden lsteps hsteps);
      hsteps
  | true :: remaining_which_actions_hidden, first_laction :: remaining_lactions, _, first_lstep :: remaining_lsteps ->
      let lnext_start_state = action_to_ending_thread_state first_laction in
      let hsteps = compute_hsteps_from_lsteps vs lpc_to_hpc return_lpcs return_pcs_unique_proof
                     lnext_start_state hstart_state lend_state hend_state remaining_which_actions_hidden
                     remaining_lactions hactions remaining_lsteps in
      assert (lsteps_correspond_to_hsteps vs pc_relation lstart_state hstart_state lend_state hend_state
                which_actions_hidden lsteps hsteps);
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

let rec lactions_all_hidden_implies_not_propagate
  (vs: list var_id_t)
  (lpc_to_hpc: pc_t -> GTot pc_t)
  (lstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (lactions: list Armada.Action.t)
  : Lemma (requires   lactions_all_hidden vs lpc_to_hpc lstart_state lend_state lactions
                    /\ Cons? lactions)
          (ensures  ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement))
          (decreases lactions) =
  match lactions with
  | [] -> ()
  | first_laction :: remaining_lactions ->
      if Cons? remaining_lactions then
        lactions_all_hidden_implies_not_propagate vs lpc_to_hpc
          (action_to_ending_thread_state first_laction) lend_state remaining_lactions
      else
        ()

let rec lactions_correspond_to_hactions_implies_not_propagate
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
  : Lemma (requires lactions_correspond_to_hactions vs lpc_to_hpc return_lpcs lstart_state hstart_state
                      lend_state hend_state which_actions_hidden lactions hactions
                    /\ Cons? lactions)
          (ensures  ~(PropagateWriteMessageStatement? (Cons?.hd lactions).program_statement.statement))
          (decreases lactions) =
  match which_actions_hidden, lactions, hactions with
  | [], [], [] -> ()
  | false :: remaining_which_actions_hidden, first_laction :: remaining_lactions, first_haction :: remaining_hactions ->
      assert (laction_corresponds_to_haction vs lpc_to_hpc return_lpcs first_laction first_haction);
      assert (~(PropagateWriteMessageStatement? first_laction.program_statement.statement))
  | true :: remaining_which_actions_hidden, first_laction :: remaining_lactions, _ ->
      if Cons? remaining_lactions then
        lactions_correspond_to_hactions_implies_not_propagate vs lpc_to_hpc return_lpcs
          (action_to_ending_thread_state first_laction) hstart_state lend_state hend_state
          remaining_which_actions_hidden remaining_lactions hactions
      else
        ()
  | _, _, _ -> ()

let lsteps_correspond_to_hsteps_implies_first_lstep_matches_lstart_state
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (lstart_state: thread_state_t)
  (hstart_state: thread_state_t)
  (lend_state: thread_state_t)
  (hend_state: thread_state_t)
  (which_actions_hidden: list bool)
  (lsteps: list Armada.Step.t)
  (hsteps: list Armada.Step.t)
  : Lemma (requires   Cons? lsteps
                    /\ lsteps_correspond_to_hsteps vs pc_relation lstart_state hstart_state lend_state hend_state
                        which_actions_hidden lsteps hsteps)
          (ensures    lstart_state = action_to_starting_thread_state (Cons?.hd lsteps).action
                    /\ ThreadStateAtPC? lstart_state)
          (decreases lsteps) =
  ()

/// Propagate

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
  (end_pc1: option pc_t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ Some? end_pc1
                    /\ pc_relation.relation (Some?.v end_pc1) (s2.threads actor).pc)
          (ensures  (let s1' = update_thread_pc_in_state s1 actor end_pc1 in
                     states_match_except_global_variables vs pc_relation s1' s2)) =
  ()
