/// This module allows one to prove that two Armada behaviors refine
/// each other if they satisfy the weakening relation.  To do this,
/// one calls [weakening_relation_implies_refinement], passing it an
/// input of type [weakening_relation_t] to demonstrate the weakening
/// relation.
///
/// The signature of [weakening_relation_implies_refinement] is:
/// 
///   val weakening_relation_implies_refinement (wr: weakening_relation_t)
///     : Lemma (ensures spec_refines_spec (semantics_to_spec wr.lsem) (semantics_to_spec wr.hsem) eq2)
/// 
/// The [weakening_relation_t] structure contains the following fields:
///
///   [sem] : semantics_t
/// 
///     The semantics of the low-level and high-level specifications.
///
///   [lprog] : program_t sem
///
///     The low-level program.
///
///   [hprog] : program_t sem
///
///     The high-level program.
///
///   [inv] : invariant_t lsem.state_t
///
///     A purported stepwise invariant of all behaviors of the low-level
///     semantics.
///
///   [weakening_transformers] : list (weakening_transformer_t sem hprog.actions inv)
///
///     A list of weakening transformers, one for each action of the low-level program.
///     That transformer must be either WeakeningTransformerSameStep, meaning that the
///     identical step exists in the high-level program, or WeakeningTransformerUpdatedStep,
///     meaning that there's a way to map any low-level step with that action to a high-level
///     step with identical behavior.
///
///   [sem_has_stepwise_inductive_invariant_proof]: unit -> squash (semantics_has_stepwise_inductive_invariant sem lprog inv)
///
///     A lemma that proves that inv is a stepwise invariant of the given low-level
///     semantics.
/// 
///   [actions_match_weakening_transformers_proof] : unit ->
///     squash (lists_correspond action_matches_weakening_transformer lprog.actions weakening_transformers)
///
///     A lemma that proves that each weakening transformer is a valid transformer for
///     the corresponding low-level action.
///
///   [inits_match] : s: lsem.state_t ->
///                   squash (requires init_program_generic lsem s) (ensures init_program_generic hsem s))
///
///     A lemma that proves that, if the low-level program allows a
///     state at initialization, the high-level program also allows
///     that state at initialization.

module Strategies.Weakening

open FStar.List.Tot
open Spec.Behavior
open Strategies.Invariant
open Strategies.Semantics
open Spec.List
open Spec.Ubool
open Util.List

let step_updater_works
  (sem: semantics_t)
  (hprogram_actions: list sem.action_t)
  (inv: invariant_t sem.state_t)
  (laction: sem.action_t)
  (step_updater: (sem.actor_t -> sem.step_t -> sem.state_t -> GTot sem.step_t))
  : GTot bool =
   u2b (forall (actor: sem.actor_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lstep: sem.step_t)
          (s: sem.state_t).
     (  sem.step_to_action_f lstep == laction
      /\ inv s
      /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block lstep s)) ==>
     (let hstep = step_updater actor lstep s in
      let haction = sem.step_to_action_f hstep in
        (contains_ubool haction hprogram_actions)
      /\ (step_computation_generic sem actor starts_atomic_block ends_atomic_block hstep s ==
         step_computation_generic sem actor starts_atomic_block ends_atomic_block lstep s)))

noeq type weakening_transformer_t
  (sem: semantics_t)
  (hprogram_actions: list sem.action_t)
  (inv: invariant_t sem.state_t) =
  | WeakeningTransformerSameStep: (haction_index: nat) -> weakening_transformer_t sem hprogram_actions inv
  | WeakeningTransformerUpdatedStep:
     (laction: sem.action_t) ->
     (step_updater: (sem.actor_t -> sem.step_t -> sem.state_t -> GTot sem.step_t)) ->
     (proof: unit -> squash (step_updater_works sem hprogram_actions inv laction step_updater)) ->
     weakening_transformer_t sem hprogram_actions inv

let action_matches_weakening_transformer
  (#sem: semantics_t)
  (#hprogram_actions: list sem.action_t)
  (#inv: invariant_t sem.state_t)
  (laction: sem.action_t)
  (weakening_transformer: weakening_transformer_t sem hprogram_actions inv)
  : GTot ubool =
  match weakening_transformer with
  | WeakeningTransformerSameStep haction_index -> nth hprogram_actions haction_index == Some laction
  | WeakeningTransformerUpdatedStep action _ _ -> laction == action

noeq type weakening_relation_t = {
  sem: semantics_t;
  lprog: program_t sem;
  hprog: program_t sem;
  inv: invariant_t sem.state_t;
  weakening_transformers: list (weakening_transformer_t sem hprog.actions inv);
  sem_has_stepwise_inductive_invariant_proof:
    unit -> squash (semantics_has_stepwise_inductive_invariant sem lprog inv);
  actions_match_weakening_transformers_proof: unit ->
    squash (lists_correspond_ubool action_matches_weakening_transformer lprog.actions weakening_transformers);
  init_implies_init_proof: (s: sem.state_t{lprog.init_f s}) -> squash (hprog.init_f s);
}

val weakening_relation_implies_refinement (wr: weakening_relation_t)
  : Lemma (ensures spec_refines_spec (semantics_to_spec wr.sem wr.lprog) (semantics_to_spec wr.sem wr.hprog) eq2)
