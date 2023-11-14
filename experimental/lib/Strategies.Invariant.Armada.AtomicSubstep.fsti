module Strategies.Invariant.Armada.AtomicSubstep

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
open Util.List

noeq type armada_atomic_substep_invariant_witness_t
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t) =
{
  action_pred: Armada.Action.t -> GTot ubool;
  special_case_proofs: list (list (option (armada_action_special_case_invariant_proof_t inv)));
  init_implies_inv_proof: (s: Armada.State.t{program.init_f s}) -> squash (inv s);
  action_proof: armada_action_maintains_invariant_proof_t inv action_pred;
}

let armada_atomic_substep_special_cases_apply
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool)
  (program_actions: list (list Armada.Action.t))
  (special_case_proofs: (list (list (option (armada_action_special_case_invariant_proof_t inv))))) =
  lists_correspond_ubool
    (lists_correspond_ubool (armada_action_proof_option_applies inv action_pred))
    program_actions
    special_case_proofs

let armada_atomic_substep_invariant_witness_valid
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_substep_invariant_witness_t program inv)
  : GTot ubool =
  armada_atomic_substep_special_cases_apply inv aiw.action_pred program.actions aiw.special_case_proofs

let is_armada_substep_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  : GTot ubool =
    (forall s. program.init_f s ==> inv s)
  /\ (forall actor starts_atomic_block ends_atomic_block (step: Armada.Step.t) s actions.
        let s' = step_computation actor starts_atomic_block ends_atomic_block step s in
          contains_ubool actions program.actions
        /\ contains_ubool step.action actions
        /\ inv s
        /\ Some? s'
        ==> inv (Some?.v s'))

val armada_atomic_substep_invariant_witness_valid_implies_is_substep_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_substep_invariant_witness_t program inv)
  : Lemma (requires armada_atomic_substep_invariant_witness_valid program inv aiw)
          (ensures  is_armada_substep_invariant program inv)
