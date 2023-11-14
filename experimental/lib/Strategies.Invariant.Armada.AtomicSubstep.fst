module Strategies.Invariant.Armada.AtomicSubstep

open FStar.List.Tot
open Strategies.Atomic
open Strategies.Invariant
open Strategies.Semantics.Armada
open Util.List

let armada_atomic_substep_invariant_witness_valid_implies_inv_preserved_on_step
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_substep_invariant_witness_t program inv)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  (actions: list Armada.Action.t)
  (s': Armada.State.t)
  : Lemma (requires   armada_atomic_substep_invariant_witness_valid program inv aiw
                    /\ contains_ubool actions program.actions
                    /\ contains_ubool step.action actions
                    /\ inv s
                    /\ Some s' == step_computation actor starts_atomic_block ends_atomic_block step s)
          (ensures  inv s') =
  let proofs = get_correspondent_from_lists_correspond_ubool
    (lists_correspond_ubool (armada_action_proof_option_applies inv aiw.action_pred))
    program.actions
    aiw.special_case_proofs
    actions in
  let proof_option = get_correspondent_from_lists_correspond_ubool
    (armada_action_proof_option_applies inv aiw.action_pred)
    actions
    proofs
    step.action in
  match proof_option with
  | None -> 
      assert (aiw.action_pred step.action);
      aiw.action_proof actor starts_atomic_block ends_atomic_block step s
  | Some proof ->
      assert (proof.action == step.action);
      proof.special_case_proof actor starts_atomic_block ends_atomic_block step s

let armada_atomic_substep_invariant_witness_valid_implies_is_substep_invariant
  (program: program_t (make_atomic_semantics armada_semantics))
  (inv: invariant_t Armada.State.t)
  (aiw: armada_atomic_substep_invariant_witness_t program inv)
  (* see .fsti file for spec *) =
  introduce forall s. program.init_f s ==> inv s
  with introduce _ ==> _
  with _. aiw.init_implies_inv_proof (s);
  introduce forall actor starts_atomic_block ends_atomic_block (step: Armada.Step.t) s actions.
          contains_ubool actions program.actions
        /\ contains_ubool step.action actions
        /\ inv s
        /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
        ==> inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))
  with introduce _ ==> _
  with _.
    armada_atomic_substep_invariant_witness_valid_implies_inv_preserved_on_step program inv aiw
      actor starts_atomic_block ends_atomic_block step s actions
      (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))
