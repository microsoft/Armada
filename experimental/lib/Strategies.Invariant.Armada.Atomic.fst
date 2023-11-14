module Strategies.Invariant.Armada.Atomic

open FStar.List.Tot
open Spec.Behavior
open Strategies.Atomic
open Strategies.Invariant.Armada
open Strategies.Invariant.Atomic
open Util.List

noeq type armada_atomic_semantics_invariant_proof_t = {
  program: program_t (make_atomic_semantics armada_semantics);
  inv: invariant_t Armada.State.t;
  action_pred: Armada.Action.t -> GTot ubool;
  special_case_proofs: list (option (armada_atomic_special_case_invariant_proof_t inv));
  init_implies_inv_proof: (s: Armada.State.t{program.init_f s}) -> squash (inv s);
  action_proof: armada_action_maintains_invariant_proof_t inv action_pred;
  special_cases_apply_proof: unit ->
     squash (armada_atomic_special_cases_apply inv action_pred program.actions special_case_proofs);
}

let transform_special_case_proof
  (inv: invariant_t Armada.State.t)
  (atomic_action: list Armada.Action.t)
  (special_case_proof:
     ((actor: tid_t) ->
      (starts_atomic_block: bool) ->
      (ends_atomic_block: bool) ->
      (atomic_step: list Armada.Step.t) ->
      (s: Armada.State.t{
          map_ghost armada_step_to_action atomic_step == atomic_action
        /\ inv s
        /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s)}) ->
      squash (inv (Some?.v (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s)))))
  : GTot ((actor: armada_semantics.actor_t) ->
          (starts_atomic_block: bool) ->
          (ends_atomic_block: bool) ->
          (atomic_step: list armada_semantics.step_t) ->
          (s: armada_semantics.state_t{
              map_ghost armada_semantics.step_to_action_f atomic_step == atomic_action
            /\ inv s
            /\ Some? (steps_computation_generic armada_semantics actor starts_atomic_block
                       ends_atomic_block atomic_step s)}) ->
          squash (inv (Some?.v (steps_computation_generic armada_semantics actor starts_atomic_block
                                  ends_atomic_block atomic_step s)))) =
  fun actor starts_atomic_block ends_atomic_block atomic_step s -> (
    armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block atomic_step s;
    special_case_proof actor starts_atomic_block ends_atomic_block atomic_step s
  )

let transform_special_case
  (inv: invariant_t Armada.State.t)
  (proof: armada_atomic_special_case_invariant_proof_t inv)
  : GTot (atomic_special_case_invariant_proof_t armada_semantics inv) =
  match proof with
  | ArmadaAtomicSpecialCaseInvariantProof atomic_action special_case_proof ->
      AtomicSpecialCaseInvariantProof atomic_action (transform_special_case_proof inv atomic_action special_case_proof)

let transform_optional_special_case
  (inv: invariant_t Armada.State.t)
  (optional_proof: option (armada_atomic_special_case_invariant_proof_t inv))
  : GTot (option (atomic_special_case_invariant_proof_t armada_semantics inv)) =
  match optional_proof with
  | None -> None
  | Some proof -> Some (transform_special_case inv proof)

let transform_special_cases
  (inv: invariant_t Armada.State.t)
  (proofs: list (option (armada_atomic_special_case_invariant_proof_t inv)))
  : GTot (list (option (atomic_special_case_invariant_proof_t armada_semantics inv))) =
  map_ghost (transform_optional_special_case inv) proofs

let armada_atomic_semantics_invariant_proof_implies_is_invariant
  (asip: armada_atomic_semantics_invariant_proof_t)
  : Lemma (is_invariant_of_spec asip.inv (semantics_to_spec (make_atomic_semantics armada_semantics) asip.program)) =
  asip.special_cases_apply_proof ();
  map_preserves_lists_correspond_ubool
    (armada_atomic_proof_option_applies asip.inv asip.action_pred)
    (atomic_proof_option_applies armada_semantics asip.inv asip.action_pred)
    (transform_optional_special_case asip.inv)
    asip.program.actions
    asip.special_case_proofs;
  let sip: atomic_semantics_invariant_proof_t = {
    sem = armada_semantics;
    program = asip.program;
    inv = asip.inv;
    action_pred = asip.action_pred;
    special_case_proofs = transform_special_cases asip.inv asip.special_case_proofs;
    init_implies_inv_proof = asip.init_implies_inv_proof;
    action_proof = asip.action_proof;
    special_cases_apply_proof = asip.special_cases_apply_proof;
  } in
  atomic_semantics_invariant_proof_implies_is_invariant sip

let armada_atomic_semantics_invariant_proof_implies_stepwise_invariant
  (asip: armada_atomic_semantics_invariant_proof_t)
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics) asip.program asip.inv) =
  asip.special_cases_apply_proof ();
  map_preserves_lists_correspond_ubool
    (armada_atomic_proof_option_applies asip.inv asip.action_pred)
    (atomic_proof_option_applies armada_semantics asip.inv asip.action_pred)
    (transform_optional_special_case asip.inv)
    asip.program.actions
    asip.special_case_proofs;
  let sip: atomic_semantics_invariant_proof_t = {
    sem = armada_semantics;
    program = asip.program;
    inv = asip.inv;
    action_pred = asip.action_pred;
    special_case_proofs = transform_special_cases asip.inv asip.special_case_proofs;
    init_implies_inv_proof = asip.init_implies_inv_proof;
    action_proof = asip.action_proof;
    special_cases_apply_proof = asip.special_cases_apply_proof;
  } in
  atomic_semantics_invariant_proof_implies_stepwise_invariant sip

let armada_atomic_semantics_invariant_witness_valid_implies_is_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_semantics_invariant_witness_t program inv)
  (* see .fsti file for spec *) =
  let aip: armada_atomic_semantics_invariant_proof_t = {
    program = program;
    inv = inv;
    action_pred = aiw.action_pred;
    special_case_proofs = aiw.special_case_proofs;
    init_implies_inv_proof = aiw.init_implies_inv_proof;
    action_proof = aiw.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  armada_atomic_semantics_invariant_proof_implies_is_invariant aip

let armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_semantics_invariant_witness_t program inv)
  (* see .fsti file for spec *) =
  let aip: armada_atomic_semantics_invariant_proof_t = {
    program = program;
    inv = inv;
    action_pred = aiw.action_pred;
    special_case_proofs = aiw.special_case_proofs;
    init_implies_inv_proof = aiw.init_implies_inv_proof;
    action_proof = aiw.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  armada_atomic_semantics_invariant_proof_implies_stepwise_invariant aip
