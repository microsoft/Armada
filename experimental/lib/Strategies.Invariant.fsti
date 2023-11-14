module Strategies.Invariant

open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Util.List

/// Proving invariants of arbitrary state machines

type invariant_t (state_t: Type) = state_t -> GTot ubool

let is_invariant_of_behavior
  (#state_t: Type)
  (inv: invariant_t state_t)
  (b: behavior_t state_t)
  : GTot ubool
  = forall s. contains_ubool s b ==> inv s

let is_invariant_of_spec
  (#state_t: Type)
  (inv: invariant_t state_t)
  (spec: spec_t state_t)
  : GTot ubool
  = forall (b: behavior_t state_t). behavior_satisfies_spec b spec ==> is_invariant_of_behavior inv b

let is_inductive_invariant_of_spec
  (#state_t: Type)
  (inv: invariant_t state_t)
  (spec: spec_t state_t)
  : GTot ubool
  =   (forall (s: state_t). spec.init s ==> inv s)
    /\ (forall (s s': state_t). inv s /\ (spec.next s s') ==> inv s')

val is_inductive_invariant_of_spec_implies_is_invariant_of_spec
  (#state_t: Type)
  (inv: invariant_t state_t)
  (spec: spec_t state_t)
  : Lemma
    (requires is_inductive_invariant_of_spec inv spec)
    (ensures  is_invariant_of_spec inv spec)

noeq type action_special_case_invariant_proof_t (sem: semantics_t) (inv: invariant_t sem.state_t) = {
  action: sem.action_t;
  special_case_proof:
    (actor: sem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (step: sem.step_t) ->
    (s: sem.state_t{
         sem.step_to_action_f step == action
       /\ inv s
       /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)}) ->
    squash (inv (Some?.v (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)));
}

type action_maintains_invariant_proof_t
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: (sem.action_t -> GTot ubool)) =
  (actor: sem.actor_t) ->
  (starts_atomic_block: bool) ->
  (ends_atomic_block: bool) ->
  (step: sem.step_t) ->
  (s: sem.state_t{
       action_pred (sem.step_to_action_f step)
     /\ inv s
     /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)}) ->
  squash (inv (Some?.v (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)))

let action_proof_option_applies
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: sem.action_t -> GTot ubool)
  (action: sem.action_t)
  (proof_option: option (action_special_case_invariant_proof_t sem inv))
  : GTot ubool =
  match proof_option with
  | None -> action_pred action
  | Some prf -> eqb prf.action action

let action_special_cases_apply
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: sem.action_t -> GTot ubool)
  (program_actions: list sem.action_t)
  (special_case_proofs: (list (option (action_special_case_invariant_proof_t sem inv)))) =
  lists_correspond_ubool (action_proof_option_applies sem inv action_pred) program_actions special_case_proofs

/// Proving invariants of semantics-defined specs

noeq type semantics_invariant_proof_t = {
  sem: semantics_t;
  program: program_t sem;
  inv: invariant_t sem.state_t;
  action_pred: sem.action_t -> GTot ubool;
  special_case_proofs: list (option (action_special_case_invariant_proof_t sem inv));
  init_implies_inv_proof: (s: sem.state_t{init_program_generic sem program s}) -> squash (inv s);
  action_proof: action_maintains_invariant_proof_t sem inv action_pred;
  special_cases_apply_proof: unit ->
     squash (action_special_cases_apply sem inv action_pred program.actions special_case_proofs);
}

val semantics_invariant_proof_implies_is_invariant_of_spec (sip: semantics_invariant_proof_t)
  : Lemma (is_invariant_of_spec sip.inv (semantics_to_spec sip.sem sip.program))

/// Proving stepwise invariants of atomic programs

let semantics_has_stepwise_inductive_invariant
  (sem: semantics_t)
  (program: program_t sem)
  (inv: invariant_t sem.state_t)
  : GTot ubool =
    (forall (s: sem.state_t).{:pattern init_program_generic sem program s} init_program_generic sem program s ==> inv s)
  /\ (forall (actor: sem.actor_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (step: sem.step_t) (s: sem.state_t).
       (  inv s
        /\ program_contains_action_of_step_generic sem program step)
       ==> (match step_computation_generic sem actor starts_atomic_block ends_atomic_block step s with
           | None -> True
           | Some s' -> inv s'))

val semantics_invariant_proof_implies_stepwise_inductive_invariant (sip: semantics_invariant_proof_t)
  : Lemma (semantics_has_stepwise_inductive_invariant sip.sem sip.program sip.inv)
