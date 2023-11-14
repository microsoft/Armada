module Strategies.Weakening.Armada

open Armada.Action
open Armada.Base
open Armada.State
open Armada.Step
open Armada.Transition
open Armada.Type
open FStar.List.Tot
open FStar.Tactics
open Spec.Behavior
open Strategies.Atomic
open Strategies.Invariant
open Strategies.Invariant.Armada.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.Weakening
open Spec.List
open Spec.Ubool
open Util.List

let remove_index_from_steps_updater
  (u:(tid_t -> list Armada.Step.t -> Armada.State.t -> GTot (nat * list Armada.Step.t)))
  (tid: tid_t)
  (lsteps: list Armada.Step.t)
  (ls: Armada.State.t)
  : GTot (list Armada.Step.t) =
  let idx, steps = u tid lsteps ls in
  steps

let armada_steps_updater_works_implies_step_updater_works
  (lactions: list Armada.Action.t)
  (hatomic_actions: list (list Armada.Action.t))
  (hatomic_action_array: array_t (list Armada.Action.t))
  (inv: invariant_t Armada.State.t)
  (steps_updater: (tid_t -> list Armada.Step.t -> Armada.State.t -> GTot (nat * list Armada.Step.t)))
  (proof: unit -> squash (armada_steps_updater_works hatomic_action_array inv lactions steps_updater))
  : Lemma (requires hatomic_action_array == list_to_array hatomic_actions)
          (ensures  step_updater_works (make_atomic_semantics armada_semantics) hatomic_actions inv lactions
                      (remove_index_from_steps_updater steps_updater)) =
  let sem = make_atomic_semantics armada_semantics in
  introduce forall (actor: sem.actor_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: sem.step_t)
              (s: sem.state_t).
              (  sem.step_to_action_f lsteps == lactions
               /\ inv s
               /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block lsteps s)) ==>
              (let hatomic_action_idx, hsteps = steps_updater actor lsteps s in
               let hactions = sem.step_to_action_f hsteps in
                 (contains_ubool hactions hatomic_actions)
               /\ (step_computation_generic sem actor starts_atomic_block ends_atomic_block hsteps s ==
                  step_computation_generic sem actor starts_atomic_block ends_atomic_block lsteps s))
  with introduce _ ==> _
  with _. (
    proof ();
    armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block lsteps s;
    let hatomic_action_idx, hsteps = steps_updater actor lsteps s in
    armada_steps_computation_equivalent actor starts_atomic_block ends_atomic_block hsteps s;
    let hactions = sem.step_to_action_f hsteps in
    index_to_contains_ubool hatomic_actions hatomic_action_idx
  )

let armada_weakening_transformer_to_weakening_transformer
  (hatomic_actions: list (list Armada.Action.t))
  (hatomic_action_array: array_t (list Armada.Action.t){hatomic_action_array == list_to_array hatomic_actions})
  (inv: invariant_t Armada.State.t)
  (awt: armada_weakening_transformer_t hatomic_action_array inv)
  : GTot (weakening_transformer_t (make_atomic_semantics armada_semantics) hatomic_actions inv) =
  match awt with
  | ArmadaWeakeningTransformerSameStep hatomic_action_idx -> WeakeningTransformerSameStep hatomic_action_idx
  | ArmadaWeakeningTransformerUpdatedStep lactions step_updater proof ->
      armada_steps_updater_works_implies_step_updater_works lactions hatomic_actions hatomic_action_array inv
        step_updater proof;
      WeakeningTransformerUpdatedStep lactions (remove_index_from_steps_updater step_updater) (fun _ -> ())

let armada_weakening_transformers_to_weakening_transformers
  (hatomic_actions: list (list Armada.Action.t))
  (hatomic_action_array: array_t (list Armada.Action.t){hatomic_action_array == list_to_array hatomic_actions})
  (inv: invariant_t Armada.State.t)
  (awts: list (armada_weakening_transformer_t hatomic_action_array inv))
  : GTot (list (weakening_transformer_t (make_atomic_semantics armada_semantics) hatomic_actions inv)) =
  map_ghost (armada_weakening_transformer_to_weakening_transformer hatomic_actions hatomic_action_array inv) awts

let armada_weakening_witness_valid_implies_actions_match_weakening_transformers
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (ww: armada_weakening_witness_t lprog hprog)
  : Lemma (requires    ww.hatomic_action_array == list_to_array hprog.actions
                    /\ lists_correspond_ubool action_matches_armada_weakening_transformer lprog.actions
                        ww.weakening_transformers)
          (ensures  lists_correspond_ubool action_matches_weakening_transformer lprog.actions
                      (armada_weakening_transformers_to_weakening_transformers hprog.actions ww.hatomic_action_array
                         ww.inv ww.weakening_transformers)) =
  introduce forall lactions weakening_transformer.
                action_matches_armada_weakening_transformer lactions weakening_transformer ==>
                  action_matches_weakening_transformer lactions
                    (armada_weakening_transformer_to_weakening_transformer hprog.actions
                      ww.hatomic_action_array ww.inv weakening_transformer)
  with introduce _ ==> _
  with _. (
    let weakening_transformer = armada_weakening_transformer_to_weakening_transformer hprog.actions
                                  ww.hatomic_action_array ww.inv weakening_transformer in
    match weakening_transformer with
    | WeakeningTransformerSameStep haction_index ->
        list_to_array_implies_nth_equivalent ww.hatomic_action_array hprog.actions haction_index
    | WeakeningTransformerUpdatedStep action _ _ ->
        assert (lactions == action)
  );
  map_preserves_lists_correspond_ubool
    action_matches_armada_weakening_transformer
    action_matches_weakening_transformer
    (armada_weakening_transformer_to_weakening_transformer hprog.actions ww.hatomic_action_array ww.inv)
    lprog.actions ww.weakening_transformers

let armada_weakening_witness_valid_implies_refinement
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (ww: armada_weakening_witness_t lprog hprog)
  (* see .fsti file for spec *) =
  armada_weakening_witness_valid_implies_actions_match_weakening_transformers lprog hprog ww;
  let wr: weakening_relation_t = {
    sem = make_atomic_semantics armada_semantics;
    lprog = lprog;
    hprog = hprog;
    inv = ww.inv;
    weakening_transformers = armada_weakening_transformers_to_weakening_transformers hprog.actions
                               ww.hatomic_action_array ww.inv ww.weakening_transformers;
    sem_has_stepwise_inductive_invariant_proof = (fun _ -> ());
    actions_match_weakening_transformers_proof = (fun _ -> ());
    init_implies_init_proof = ww.init_implies_init_proof;
  } in
  weakening_relation_implies_refinement wr
