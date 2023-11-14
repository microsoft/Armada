module Strategies.Invariant.Armada

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
open Strategies.Invariant
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.List

let is_inductive_armada_invariant_of_program
  (inv: invariant_t Armada.State.t)
  (program: Armada.Program.t)
  : GTot ubool
  =   (forall (s: Armada.State.t). init_program program s ==> inv s)
    /\ (forall (s s': Armada.State.t) (transition: Armada.Transition.t).
          inv s /\ next_program program transition s s' ==> inv s')

val is_inductive_armada_invariant_of_program_implies_is_invariant_of_program
  (inv: invariant_t Armada.State.t)
  (program: Armada.Program.t)
  : Lemma
    (requires is_inductive_armada_invariant_of_program inv program)
    (ensures  is_invariant_of_spec inv (program_to_spec program))

noeq type armada_action_special_case_invariant_proof_t (inv: invariant_t Armada.State.t) = {
  action: Armada.Action.t;
  special_case_proof:
    (actor: tid_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (step: Armada.Step.t) ->
    (s: Armada.State.t{
        step.action == action
      /\ inv s
      /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)})
    -> squash (inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)));
}

type armada_action_maintains_invariant_proof_t
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool) =
  (actor: tid_t) ->
  (starts_atomic_block: bool) ->
  (ends_atomic_block: bool) ->
  (step: Armada.Step.t) ->
  (s: Armada.State.t{
      action_pred step.action
    /\ inv s
    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)}) ->
  squash (inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)))

let armada_action_proof_option_applies
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool)
  (action: Armada.Action.t)
  (proof_option: option (armada_action_special_case_invariant_proof_t inv))
  : GTot ubool =
  match proof_option with
  | None -> action_pred action
  | Some prf -> eqb prf.action action

let armada_action_special_cases_apply
  (inv: invariant_t Armada.State.t)
  (action_pred: Armada.Action.t -> GTot ubool)
  (program_actions: list Armada.Action.t)
  (special_case_proofs: (list (option (armada_action_special_case_invariant_proof_t inv)))) =
  lists_correspond_ubool (armada_action_proof_option_applies inv action_pred) program_actions special_case_proofs

/// Proving invariants of semantics-defined specs

noeq type armada_invariant_witness_t (program: Armada.Program.t) (inv: invariant_t Armada.State.t) = {
  action_pred: Armada.Action.t -> GTot ubool;
  special_case_proofs: list (option (armada_action_special_case_invariant_proof_t inv));
  init_implies_inv_proof: (s: Armada.State.t{init_program program s}) -> squash (inv s);
  action_proof: armada_action_maintains_invariant_proof_t inv action_pred;
}

let armada_invariant_witness_valid
  (program: Armada.Program.t)
  (inv: invariant_t Armada.State.t)
  (aiw: armada_invariant_witness_t program inv)
  : GTot ubool =
  armada_action_special_cases_apply inv aiw.action_pred (all_actions program.program_statements)
    aiw.special_case_proofs

val armada_invariant_witness_valid_implies_is_armada_invariant_of_program
  (program: Armada.Program.t)
  (inv: invariant_t Armada.State.t)
  (aiw: armada_invariant_witness_t program inv)
  : Lemma (requires armada_invariant_witness_valid program inv aiw)
          (ensures  is_invariant_of_spec inv (program_to_spec program))

/// Proving stepwise invariants of atomic programs

let armada_program_has_stepwise_inductive_invariant
  (inv: invariant_t Armada.State.t)
  (program: Armada.Program.t)
  : GTot ubool =
    (forall (s: Armada.State.t).{:pattern init_program program s} init_program program s ==> inv s)
  /\ (forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (step: Armada.Step.t) (s: Armada.State.t).
       (  inv s
        /\ contains_ubool step.action.program_statement program.program_statements)
       ==> (match step_computation actor starts_atomic_block ends_atomic_block step s with
           | None -> True
           | Some s' -> inv s'))

val armada_invariant_witness_valid_implies_stepwise_invariant
  (program: Armada.Program.t)
  (inv: invariant_t Armada.State.t)
  (aiw: armada_invariant_witness_t program inv)
  : Lemma (requires armada_invariant_witness_valid program inv aiw)
          (ensures  armada_program_has_stepwise_inductive_invariant inv program)
