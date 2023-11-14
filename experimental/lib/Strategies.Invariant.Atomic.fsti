module Strategies.Invariant.Atomic

open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Strategies.Invariant
open Util.List

/// Proving invariants of atomic programs

noeq type atomic_special_case_invariant_proof_t (sem: semantics_t) (inv: invariant_t sem.state_t) =
  | AtomicSpecialCaseInvariantProof :
     (atomic_action: list sem.action_t) ->
     (special_case_proof:
       ((actor: sem.actor_t) ->
        (starts_atomic_block: bool) ->
        (ends_atomic_block: bool) ->
        (atomic_step: list sem.step_t) ->
        (s: sem.state_t{
            map_ghost sem.step_to_action_f atomic_step == atomic_action
          /\ inv s
          /\ Some? (steps_computation_generic sem actor starts_atomic_block ends_atomic_block atomic_step s)}) ->
        squash (inv (Some?.v (steps_computation_generic sem actor starts_atomic_block
                                ends_atomic_block atomic_step s))))) ->
  atomic_special_case_invariant_proof_t sem inv

let atomic_proof_option_applies
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: sem.action_t -> GTot ubool)
  (atomic_action: list sem.action_t)
  (proof_option: option (atomic_special_case_invariant_proof_t sem inv))
  : GTot ubool =
  match proof_option with
  | None -> for_all_ubool action_pred atomic_action
  | Some prf -> eqb prf.atomic_action atomic_action

let atomic_special_cases_apply
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: sem.action_t -> GTot ubool)
  (atomic_actions: list (list sem.action_t))
  (special_case_proofs: (list (option (atomic_special_case_invariant_proof_t sem inv)))) =
  lists_correspond_ubool (atomic_proof_option_applies sem inv action_pred) atomic_actions special_case_proofs

noeq type atomic_semantics_invariant_proof_t = {
  sem: semantics_t;
  program: program_t (make_atomic_semantics sem);
  inv: invariant_t sem.state_t;
  action_pred: sem.action_t -> GTot ubool;
  special_case_proofs: list (option (atomic_special_case_invariant_proof_t sem inv));
  init_implies_inv_proof: (s: sem.state_t{program.init_f s}) -> squash (inv s);
  action_proof: action_maintains_invariant_proof_t sem inv action_pred;
  special_cases_apply_proof: unit ->
     squash (atomic_special_cases_apply sem inv action_pred program.actions special_case_proofs);
}

val atomic_semantics_invariant_proof_implies_is_invariant (asip: atomic_semantics_invariant_proof_t)
  : Lemma (is_invariant_of_spec asip.inv (semantics_to_spec (make_atomic_semantics asip.sem) asip.program))

val atomic_semantics_invariant_proof_implies_stepwise_invariant (asip: atomic_semantics_invariant_proof_t)
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics asip.sem) asip.program asip.inv)
