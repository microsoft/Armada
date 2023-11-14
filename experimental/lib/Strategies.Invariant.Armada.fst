module Strategies.Invariant.Armada

open FStar.List.Tot
open Spec.Behavior
open Strategies.Atomic
open Strategies.Invariant
open Strategies.Semantics.Armada
open Util.List

let is_inductive_armada_invariant_of_program_implies_is_invariant_of_program
  (inv: invariant_t Armada.State.t)
  (program: Armada.Program.t)
  (* see .fsti file for spec *) =
  is_inductive_invariant_of_spec_implies_is_invariant_of_spec inv (program_to_spec program)

noeq type armada_invariant_proof_t = {
  program: Armada.Program.t;
  inv: invariant_t Armada.State.t;
  action_pred: Armada.Action.t -> GTot ubool;
  special_case_proofs: list (option (armada_action_special_case_invariant_proof_t inv));
  init_implies_inv_proof: (s: Armada.State.t{init_program program s}) -> squash (inv s);
  action_proof: armada_action_maintains_invariant_proof_t inv action_pred;
  special_cases_apply_proof: unit ->
     squash (armada_action_special_cases_apply inv action_pred (all_actions program.program_statements)
               special_case_proofs);
}

let transform_special_case_proof
  (inv: invariant_t Armada.State.t)
  (action: Armada.Action.t)
  (special_case_proof:
     (actor: tid_t) ->
     (starts_atomic_block: bool) ->
     (ends_atomic_block: bool) ->
     (step: Armada.Step.t) ->
     (s: Armada.State.t{
          step.action == action
        /\ inv s
        /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)}) ->
     squash (inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))))
  : GTot ((actor: armada_semantics.actor_t) ->
          (starts_atomic_block: bool) ->
          (ends_atomic_block: bool) ->
          (step: armada_semantics.step_t) ->
          (s: armada_semantics.state_t{
              armada_semantics.step_to_action_f step == action
            /\ inv s
            /\ Some? (step_computation_generic armada_semantics actor starts_atomic_block
                       ends_atomic_block step s)}) ->
          squash (inv (Some?.v (step_computation_generic armada_semantics actor starts_atomic_block
                                  ends_atomic_block step s)))) =
  special_case_proof

let transform_special_case
  (inv: invariant_t Armada.State.t)
  (proof: armada_action_special_case_invariant_proof_t inv)
  : GTot (action_special_case_invariant_proof_t armada_semantics inv) =
  {
    action = proof.action;
    special_case_proof = transform_special_case_proof inv proof.action proof.special_case_proof;
  }

let transform_optional_special_case
  (inv: invariant_t Armada.State.t)
  (optional_proof: option (armada_action_special_case_invariant_proof_t inv))
  : GTot (option (action_special_case_invariant_proof_t armada_semantics inv)) =
  match optional_proof with
  | None -> None
  | Some proof -> Some (transform_special_case inv proof)

let transform_optional_special_cases
  (inv: invariant_t Armada.State.t)
  (optional_proofs: list (option (armada_action_special_case_invariant_proof_t inv)))
  : GTot (list (option (action_special_case_invariant_proof_t armada_semantics inv))) =
  map_ghost (transform_optional_special_case inv) optional_proofs

let armada_invariant_proof_implies_is_armada_invariant_of_program (aip: armada_invariant_proof_t)
  : Lemma (is_invariant_of_spec aip.inv (program_to_spec aip.program)) =
  aip.special_cases_apply_proof ();
  map_preserves_lists_correspond_ubool
    (armada_action_proof_option_applies aip.inv aip.action_pred)
    (action_proof_option_applies armada_semantics aip.inv aip.action_pred)
    (transform_optional_special_case aip.inv)
    (all_actions aip.program.program_statements)
    aip.special_case_proofs;
  let sip: semantics_invariant_proof_t = {
    sem = armada_semantics;
    program = armada_program_to_generic aip.program;
    inv = aip.inv;
    action_pred = aip.action_pred;
    special_case_proofs = transform_optional_special_cases aip.inv aip.special_case_proofs;
    init_implies_inv_proof = aip.init_implies_inv_proof;
    action_proof = aip.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  semantics_invariant_proof_implies_is_invariant_of_spec sip;
  introduce forall (b: behavior_t Armada.State.t).
              behavior_satisfies_spec b (program_to_spec aip.program) ==> is_invariant_of_behavior aip.inv b
  with introduce _ ==> _
  with _. behavior_satisfies_armada_spec_iff_it_satisfies_generic_spec aip.program b

let armada_invariant_witness_valid_implies_is_armada_invariant_of_program
  (program: Armada.Program.t)
  (inv: invariant_t Armada.State.t)
  (aiw: armada_invariant_witness_t program inv)
  (* see .fsti file for spec *) =
  let aip: armada_invariant_proof_t = {
    program = program;
    inv = inv;
    action_pred = aiw.action_pred;
    special_case_proofs = aiw.special_case_proofs;
    init_implies_inv_proof = aiw.init_implies_inv_proof;
    action_proof = aiw.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  armada_invariant_proof_implies_is_armada_invariant_of_program aip

let armada_invariant_proof_implies_stepwise_invariant (aip: armada_invariant_proof_t)
  : Lemma (armada_program_has_stepwise_inductive_invariant aip.inv aip.program) =
  aip.special_cases_apply_proof ();
  map_preserves_lists_correspond_ubool
    (armada_action_proof_option_applies aip.inv aip.action_pred)
    (action_proof_option_applies armada_semantics aip.inv aip.action_pred)
    (transform_optional_special_case aip.inv)
    (all_actions aip.program.program_statements)
    aip.special_case_proofs;
  let sip: semantics_invariant_proof_t = {
    sem = armada_semantics;
    program = armada_program_to_generic aip.program;
    inv = aip.inv;
    action_pred = aip.action_pred;
    special_case_proofs = transform_optional_special_cases aip.inv aip.special_case_proofs;
    init_implies_inv_proof = aip.init_implies_inv_proof;
    action_proof = aip.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  semantics_invariant_proof_implies_stepwise_inductive_invariant sip;

  introduce forall (s: Armada.State.t). init_program aip.program s ==> aip.inv s
  with introduce _ ==> _
  with _. assert (init_program_generic armada_semantics sip.program s);
  introduce forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (step: Armada.Step.t)
              (s: Armada.State.t).
              (  aip.inv s
               /\ contains_ubool step.action.program_statement aip.program.program_statements)
              ==> (match step_computation actor starts_atomic_block ends_atomic_block step s with
                   | None -> True
                   | Some s' -> aip.inv s')
  with introduce _ ==> _
  with _. (
    all_actions_has_all_actions step.action aip.program.program_statements;
    assert (program_contains_action_of_step_generic armada_semantics sip.program step);
    assert (step_computation actor starts_atomic_block ends_atomic_block step s ==
            step_computation_generic armada_semantics actor starts_atomic_block ends_atomic_block step s)
  )

let armada_invariant_witness_valid_implies_stepwise_invariant
  (program: Armada.Program.t)
  (inv: invariant_t Armada.State.t)
  (aiw: armada_invariant_witness_t program inv)
  (* see .fsti file for spec *) =
  let aip: armada_invariant_proof_t = {
    program = program;
    inv = inv;
    action_pred = aiw.action_pred;
    special_case_proofs = aiw.special_case_proofs;
    init_implies_inv_proof = aiw.init_implies_inv_proof;
    action_proof = aiw.action_proof;
    special_cases_apply_proof = (fun _ -> ());
  } in
  armada_invariant_proof_implies_stepwise_invariant aip
