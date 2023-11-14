module Strategies.Invariant.Armada.Atomic

open Armada.Action
open Armada.Base
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.Invariant
open Strategies.Invariant.Armada
open Strategies.Invariant.Atomic
open Util.List

noeq type armada_atomic_special_case_invariant_proof_t (inv: invariant_t Armada.State.t) =
  | ArmadaAtomicSpecialCaseInvariantProof :
     (atomic_action: list Armada.Action.t) ->
     (special_case_proof:
       ((actor: tid_t) ->
        (starts_atomic_block: bool) ->
        (ends_atomic_block: bool) ->
        (atomic_step: list Armada.Step.t) ->
        (s: Armada.State.t{
             map_ghost armada_step_to_action atomic_step == atomic_action
           /\ inv s
           /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s)}) ->
        squash (inv (Some?.v (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s))))) ->
  armada_atomic_special_case_invariant_proof_t inv

let armada_atomic_proof_option_applies
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool)
  (atomic_action: list Armada.Action.t)
  (proof_option: option (armada_atomic_special_case_invariant_proof_t inv))
  : GTot ubool =
  match proof_option with
  | None -> for_all_ubool action_pred atomic_action
  | Some prf -> prf.atomic_action == atomic_action

let armada_atomic_special_cases_apply
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool)
  (atomic_actions: list (list Armada.Action.t))
  (special_case_proofs: (list (option (armada_atomic_special_case_invariant_proof_t inv)))) =
  lists_correspond_ubool (armada_atomic_proof_option_applies inv action_pred) atomic_actions special_case_proofs

noeq type armada_atomic_semantics_invariant_witness_t
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t) =
{
  action_pred: Armada.Action.t -> GTot ubool;
  special_case_proofs: list (option (armada_atomic_special_case_invariant_proof_t inv));
  init_implies_inv_proof: (s: Armada.State.t{program.init_f s}) -> squash (inv s);
  action_proof: armada_action_maintains_invariant_proof_t inv action_pred;
}

let armada_atomic_semantics_invariant_witness_valid
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_semantics_invariant_witness_t program inv)
  : GTot ubool =
  armada_atomic_special_cases_apply inv aiw.action_pred program.actions aiw.special_case_proofs

val armada_atomic_semantics_invariant_witness_valid_implies_is_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_semantics_invariant_witness_t program inv)
  : Lemma (requires armada_atomic_semantics_invariant_witness_valid program inv aiw)
          (ensures  is_invariant_of_spec inv (semantics_to_spec (make_atomic_semantics armada_semantics) program))

val armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_semantics_invariant_witness_t program inv)
  : Lemma (requires armada_atomic_semantics_invariant_witness_valid program inv aiw)
          (ensures  semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics) program inv)
