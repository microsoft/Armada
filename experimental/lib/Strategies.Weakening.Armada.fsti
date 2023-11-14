module Strategies.Weakening.Armada

open Armada.Action
open Armada.Base
open Armada.State
open Armada.Step
open Armada.Transition
open Armada.Type
open FStar.List.Tot
open Spec.Behavior
open Strategies.Atomic
open Strategies.Invariant
open Strategies.Invariant.Armada.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Spec.List
open Spec.Ubool
open Util.ImmutableArray
open Util.List

let armada_steps_updater_works
  (hatomic_action_array: array_t (list Armada.Action.t))
  (inv: invariant_t Armada.State.t)
  (lactions: list Armada.Action.t)
  (steps_updater: (tid_t -> list Armada.Step.t -> Armada.State.t -> GTot (nat * list Armada.Step.t)))
  : GTot ubool =
  forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: list Armada.Step.t)
       (s: Armada.State.t).
    (  map_ghost armada_step_to_action lsteps == lactions
     /\ inv s
     /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s)) ==>
    (let hatomic_action_idx, hsteps = steps_updater actor lsteps s in
     let haction = map_ghost armada_step_to_action hsteps in
       hatomic_action_idx < array_len hatomic_action_array
     /\ array_index hatomic_action_array hatomic_action_idx == haction
     /\ (steps_computation actor starts_atomic_block ends_atomic_block hsteps s ==
        steps_computation actor starts_atomic_block ends_atomic_block lsteps s))

noeq type armada_weakening_transformer_t
  (hatomic_action_array: array_t (list Armada.Action.t))
  (inv: invariant_t Armada.State.t) =
  | ArmadaWeakeningTransformerSameStep: (hatomic_action_idx: nat) ->
      armada_weakening_transformer_t hatomic_action_array inv
  | ArmadaWeakeningTransformerUpdatedStep:
     (lactions: list Armada.Action.t) ->
     (steps_updater: (tid_t -> list Armada.Step.t -> Armada.State.t -> GTot (nat * list Armada.Step.t))) ->
     (proof: unit -> squash (armada_steps_updater_works hatomic_action_array inv lactions steps_updater)) ->
     armada_weakening_transformer_t hatomic_action_array inv

let action_matches_armada_weakening_transformer
  (#hatomic_action_array: array_t (list Armada.Action.t))
  (#inv: invariant_t Armada.State.t)
  (lactions: list Armada.Action.t)
  (weakening_transformer: armada_weakening_transformer_t hatomic_action_array inv)
  : GTot ubool =
  match weakening_transformer with
  | ArmadaWeakeningTransformerSameStep hatomic_action_idx ->
        hatomic_action_idx < array_len hatomic_action_array
      /\ array_index hatomic_action_array hatomic_action_idx == lactions
  | ArmadaWeakeningTransformerUpdatedStep actions _ _ -> lactions == actions

noeq type armada_weakening_witness_t
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: program_t (make_atomic_semantics armada_semantics)) =
{
  inv: invariant_t Armada.State.t;
  hatomic_action_array: array_t (list Armada.Action.t);
  weakening_transformers: list (armada_weakening_transformer_t hatomic_action_array inv);
  init_implies_init_proof: (s: Armada.State.t{lprog.init_f s}) -> squash (hprog.init_f s);
}

let armada_weakening_witness_valid
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (ww: armada_weakening_witness_t lprog hprog)
  : GTot ubool =
  lists_correspond_ubool action_matches_armada_weakening_transformer lprog.actions ww.weakening_transformers

val armada_weakening_witness_valid_implies_refinement
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: program_t (make_atomic_semantics armada_semantics))
  (ww: armada_weakening_witness_t lprog hprog)
  : Lemma (requires   ww.hatomic_action_array == list_to_array hprog.actions
                    /\ semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics) lprog ww.inv
                    /\ armada_weakening_witness_valid lprog hprog ww)
          (ensures  spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) lprog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hprog)
                      eq2)
