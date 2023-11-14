module Strategies.Weakening

open FStar.WellFoundedRelation
open Spec.Behavior
open Strategies.Semantics
open Spec.Ubool
open Spec.List
open Strategies.Lift.Generic
open Util.Behavior
open Util.List
open Util.Nth

let lift_step_case_same_step
  (wr: weakening_relation_t)
  (actor: wr.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lstep: wr.sem.step_t)
  (s: wr.sem.state_t)
  (laction: wr.sem.action_t)
  (weakening_transformer: weakening_transformer_t wr.sem wr.hprog.actions wr.inv)
  : Ghost wr.sem.step_t
    (requires   wr.inv s
              /\ (Some? (step_computation_generic wr.sem actor
                          starts_atomic_block ends_atomic_block lstep s))
              /\ (program_contains_action_of_step_generic wr.sem wr.lprog lstep)
              /\ (wr.sem.step_to_action_f lstep == laction)
              /\ (action_matches_weakening_transformer laction weakening_transformer)
              /\ (WeakeningTransformerSameStep? weakening_transformer))
    (ensures  fun hstep ->   (Some? (step_computation_generic wr.sem actor
                                    starts_atomic_block ends_atomic_block lstep s))
                        /\ step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s ==
                            step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block lstep s
                        /\ wr.inv (Some?.v (step_computation_generic wr.sem actor
                                             starts_atomic_block ends_atomic_block lstep s))
                        /\ (program_contains_action_of_step_generic wr.sem wr.hprog hstep)) =
  wr.sem_has_stepwise_inductive_invariant_proof ();
  let haction_index = (WeakeningTransformerSameStep?.haction_index weakening_transformer) in
  let haction = Some?.v (nth wr.hprog.actions haction_index) in
  nth_implies_contains_ubool wr.hprog.actions haction_index haction;
  lstep
  
let lift_step_case_updated_step
  (wr: weakening_relation_t)
  (actor: wr.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lstep: wr.sem.step_t)
  (s: wr.sem.state_t)
  (laction: wr.sem.action_t)
  (weakening_transformer: weakening_transformer_t wr.sem wr.hprog.actions wr.inv)
  : Ghost wr.sem.step_t
    (requires   wr.inv s
              /\ (Some? (step_computation_generic wr.sem actor
                          starts_atomic_block ends_atomic_block lstep s))
              /\ (program_contains_action_of_step_generic wr.sem wr.lprog lstep)
              /\ (wr.sem.step_to_action_f lstep == laction)
              /\ (action_matches_weakening_transformer laction weakening_transformer)
              /\ WeakeningTransformerUpdatedStep? weakening_transformer)
    (ensures  fun hstep ->   (Some? (step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s))
                        /\ step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s ==
                            step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block lstep s
                        /\ wr.inv (Some?.v (step_computation_generic wr.sem actor
                                             starts_atomic_block ends_atomic_block lstep s))
                        /\ (program_contains_action_of_step_generic wr.sem wr.hprog hstep)) =
  wr.sem_has_stepwise_inductive_invariant_proof ();
  match weakening_transformer with
  | WeakeningTransformerUpdatedStep _ step_updater proof ->
      proof ();
      step_updater actor lstep s

let lift_step_using_weakening_transformer
  (wr: weakening_relation_t)
  (actor: wr.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lstep: wr.sem.step_t)
  (s: wr.sem.state_t)
  (laction: wr.sem.action_t)
  (weakening_transformer: weakening_transformer_t wr.sem wr.hprog.actions wr.inv)
  : Ghost wr.sem.step_t
    (requires   wr.inv s
              /\ (Some? (step_computation_generic wr.sem actor
                          starts_atomic_block ends_atomic_block lstep s))
              /\ (program_contains_action_of_step_generic wr.sem wr.lprog lstep)
              /\ (wr.sem.step_to_action_f lstep == laction)
              /\ (action_matches_weakening_transformer laction weakening_transformer))
    (ensures  fun hstep ->   (Some? (step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s))
                        /\ step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s ==
                            step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block lstep s
                        /\ wr.inv (Some?.v (step_computation_generic wr.sem actor
                                             starts_atomic_block ends_atomic_block lstep s))
                        /\ (program_contains_action_of_step_generic wr.sem wr.hprog hstep)) =
  match weakening_transformer with
  | WeakeningTransformerSameStep _ ->
     lift_step_case_same_step wr actor starts_atomic_block ends_atomic_block lstep s laction weakening_transformer
  | WeakeningTransformerUpdatedStep _ _ _ ->
     lift_step_case_updated_step wr actor starts_atomic_block ends_atomic_block lstep s laction weakening_transformer

let lift_step
  (wr: weakening_relation_t)
  (actor: wr.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lstep: wr.sem.step_t)
  (s: wr.sem.state_t)
  : Ghost wr.sem.step_t
    (requires   wr.inv s
              /\ (Some? (step_computation_generic wr.sem actor
                          starts_atomic_block ends_atomic_block lstep s))
              /\ (program_contains_action_of_step_generic wr.sem wr.lprog lstep))
    (ensures  fun hstep ->   (Some? (step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s))
                        /\ step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block hstep s ==
                            step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block lstep s
                        /\ wr.inv (Some?.v (step_computation_generic wr.sem actor
                                             starts_atomic_block ends_atomic_block lstep s))
                        /\ (program_contains_action_of_step_generic wr.sem wr.hprog hstep)) =
  let laction = wr.sem.step_to_action_f lstep in
  let laction_index = contains_to_index laction wr.lprog.actions in
  wr.actions_match_weakening_transformers_proof ();
  lists_correspond_ubool_implies_index_matches
    action_matches_weakening_transformer
    wr.lprog.actions
    wr.weakening_transformers
    laction_index;
  let weakening_transformer = (Some?.v (nth wr.weakening_transformers laction_index)) in
  lift_step_using_weakening_transformer wr actor starts_atomic_block ends_atomic_block lstep s laction
    weakening_transformer

let lh_relation_gen (wr: weakening_relation_t) (aux: unit) (ls: wr.sem.state_t) (hs: wr.sem.state_t) : GTot ubool =
  ls == hs

let progress_measure_gen (wr: weakening_relation_t) (hs: wr.sem.state_t) (lstep: wr.sem.step_t) (actor: wr.sem.actor_t)
  : GTot nat = 0

let paths_liftable_proof_gen
  (wr: weakening_relation_t)
  (actor: wr.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (aux: unit)
  (ls: wr.sem.state_t)
  (hs: wr.sem.state_t)
  (lstep: wr.sem.step_t{
       wr.inv ls
     /\ (lh_relation_gen wr) aux ls hs
     /\ Some? (step_computation_generic wr.sem actor starts_atomic_block ends_atomic_block lstep ls)
     /\ program_contains_action_of_step_generic wr.sem wr.lprog lstep})
  : GTot (lifter: (step_lifter_t wr.sem.step_t unit){
                      step_lifter_works wr.sem wr.sem wr.lprog wr.hprog unit (lh_relation_gen wr)
                        nat (default_wfr nat) (progress_measure_gen wr)
                        actor starts_atomic_block ends_atomic_block lstep ls hs lifter}) =
  StepLifterLift (lift_step wr actor starts_atomic_block ends_atomic_block lstep ls) ()

let init_implies_relation_proof_gen (wr: weakening_relation_t) (ls: wr.sem.state_t{wr.lprog.init_f ls})
  : GTot (hs_aux: (wr.sem.state_t * unit){
            let hs, aux = hs_aux in
            wr.hprog.init_f hs /\ lh_relation_gen wr aux ls hs}) =
  wr.init_implies_init_proof ls;
  assert (wr.hprog.init_f ls /\ lh_relation_gen wr () ls ls);
  (ls, ())

let lh_relation_implies_refinement_proof_gen
  (wr: weakening_relation_t)
  (aux: unit)
  (ls: wr.sem.state_t)
  (hs: wr.sem.state_t{wr.inv ls /\ lh_relation_gen wr aux ls hs})
  : squash (ls == hs) =
  ()

let weakening_relation_to_liftability_relation (wr: weakening_relation_t) : GTot liftability_relation_t =
  {
    lsem = wr.sem;
    hsem = wr.sem;
    lprog = wr.lprog;
    hprog = wr.hprog;
    aux_t = unit;
    inv = wr.inv;
    lh_relation = lh_relation_gen wr;
    progress_t = nat;
    progress_wfr = default_wfr nat;
    progress_measure = progress_measure_gen wr;
    refinement_relation = eq2;
    paths_liftable_proof = paths_liftable_proof_gen wr;
    inv_stepwise_invariant_proof = wr.sem_has_stepwise_inductive_invariant_proof;
    init_implies_relation_proof = init_implies_relation_proof_gen wr;
    lh_relation_implies_refinement_proof = lh_relation_implies_refinement_proof_gen wr;
  }

let weakening_relation_implies_refinement wr =
  (* see .fsti file for spec *)
  liftability_relation_implies_refinement (weakening_relation_to_liftability_relation wr)
