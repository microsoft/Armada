module Strategies.Lift.Generic

open FStar.WellFoundedRelation
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Invariant
open Strategies.Semantics

noeq type step_lifter_t (step_t: Type) (aux_t: Type) =
  | StepLifterSkip: (aux': aux_t) -> step_lifter_t step_t aux_t
  | StepLifterIntroduce: (hstep: step_t) -> (aux': aux_t) -> step_lifter_t step_t aux_t
  | StepLifterLift: (hstep: step_t) -> (aux': aux_t) -> step_lifter_t step_t aux_t

let step_lifter_works
  (lsem: semantics_t)
  (hsem: semantics_t{hsem.actor_t == lsem.actor_t})
  (lprog: program_t lsem)
  (hprog: program_t hsem)
  (aux_t: Type)
  (lh_relation: aux_t -> lsem.state_t -> hsem.state_t -> GTot ubool)
  (progress_t: Type)
  (progress_wfr: wfr_t progress_t)
  (progress_measure: hsem.state_t -> lsem.step_t -> lsem.actor_t -> GTot progress_t)
  (actor: lsem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lstep: lsem.step_t)
  (ls: lsem.state_t)
  (hs: hsem.state_t)
  (lifter: step_lifter_t hsem.step_t aux_t)
  : GTot ubool =
  match lifter with
  | StepLifterSkip aux' ->
      (match step_computation_generic lsem actor starts_atomic_block ends_atomic_block lstep ls with
       | Some ls' ->
             lh_relation aux' ls' hs
           /\ (starts_atomic_block = ends_atomic_block)
       | None -> False)
  | StepLifterIntroduce hstep aux' ->
      (* Introduced steps must have ends_atomic_block the same as starts_atomic_block *)
      (match step_computation_generic hsem actor starts_atomic_block starts_atomic_block hstep hs with
       | Some hs' ->
             lh_relation aux' ls hs'
           /\ program_contains_action_of_step_generic hsem hprog hstep
           /\ progress_wfr.relation (progress_measure hs' lstep actor) (progress_measure hs lstep actor)
       | None -> False)
  | StepLifterLift hstep aux' ->
      (match step_computation_generic lsem actor starts_atomic_block ends_atomic_block lstep ls,
             step_computation_generic hsem actor starts_atomic_block ends_atomic_block hstep hs with
       | Some ls', Some hs' ->
             program_contains_action_of_step_generic hsem hprog hstep
           /\ lh_relation aux' ls' hs'
       | _, _ -> False)

noeq type liftability_relation_t = {
  lsem: semantics_t;
  hsem: (hsem: semantics_t{hsem.actor_t == lsem.actor_t});
  lprog: program_t lsem;
  hprog: program_t hsem;
  aux_t: Type;
  inv: invariant_t lsem.state_t;
  lh_relation: aux_t -> lsem.state_t -> hsem.state_t -> GTot ubool;
  progress_t: Type;
  progress_wfr: wfr_t progress_t;
  progress_measure: hsem.state_t -> lsem.step_t -> lsem.actor_t -> GTot progress_t;
  refinement_relation: lsem.state_t -> hsem.state_t -> GTot ubool;

  paths_liftable_proof:
    (actor: lsem.actor_t) ->
    (starts_atomic_block: bool) ->
    (ends_atomic_block: bool) ->
    (aux: aux_t) ->
    (ls: lsem.state_t) ->
    (hs: hsem.state_t) ->
    (lstep: lsem.step_t{
         inv ls
       /\ lh_relation aux ls hs
       /\ Some? (step_computation_generic lsem actor starts_atomic_block ends_atomic_block lstep ls)
       /\ program_contains_action_of_step_generic lsem lprog lstep}) ->
    GTot (lifter: (step_lifter_t hsem.step_t aux_t){
      step_lifter_works lsem hsem lprog hprog aux_t lh_relation progress_t progress_wfr
        progress_measure actor starts_atomic_block ends_atomic_block lstep ls hs lifter});

  inv_stepwise_invariant_proof: unit -> squash (semantics_has_stepwise_inductive_invariant lsem lprog inv);

  init_implies_relation_proof:
    (ls: lsem.state_t{lprog.init_f ls}) ->
    GTot (hs_aux: (hsem.state_t * aux_t){
       let hs, aux = hs_aux in
       hprog.init_f hs /\ lh_relation aux ls hs});

  lh_relation_implies_refinement_proof:
    (aux: aux_t) ->
    (ls: lsem.state_t) ->
    (hs: hsem.state_t{inv ls /\ lh_relation aux ls hs}) ->
    squash (refinement_relation ls hs);
}

val liftability_relation_implies_refinement (lr: liftability_relation_t)
  : Lemma (ensures spec_refines_spec
                     (semantics_to_spec lr.lsem lr.lprog)
                     (semantics_to_spec lr.hsem lr.hprog)
                     lr.refinement_relation)
