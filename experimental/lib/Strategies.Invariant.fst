module Strategies.Invariant

open FStar.List.Tot
open Spec.Behavior
open Strategies.Atomic
open Util.List

/// Proving invariants

let rec inductive_invariant_satisfied_initially_and_inductive_implies_invariant
  (#state: Type)
  (inv: invariant_t state)
  (spec: spec_t state)
  (b: behavior_t state)
  : Lemma
    (requires Cons? b ==>
                inv (Cons?.hd b)
              /\ behavior_satisfies_next b spec.next
              /\ (forall (s s': state). inv s /\ (spec.next s s') ==> inv s'))
    (ensures  is_invariant_of_behavior inv b)
  = match b with
    | [] -> ()
    | s :: tl -> inductive_invariant_satisfied_initially_and_inductive_implies_invariant inv spec tl

let is_inductive_invariant_of_spec_implies_is_invariant_of_behavior
  (#state: Type)
  (inv: invariant_t state)
  (spec: spec_t state)
  (b: behavior_t state)
  : Lemma
    (requires   is_inductive_invariant_of_spec inv spec
              /\ behavior_satisfies_spec b spec)
    (ensures  is_invariant_of_behavior inv b)
  = inductive_invariant_satisfied_initially_and_inductive_implies_invariant inv spec b

let is_inductive_invariant_of_spec_implies_is_invariant_of_spec
  (#state: Type)
  (inv: invariant_t state)
  (spec: spec_t state) =
  (* see .fsti file for spec *)
  introduce forall b. behavior_satisfies_spec b spec ==> is_invariant_of_behavior inv b
  with introduce _ ==> _
  with given_antecedent. is_inductive_invariant_of_spec_implies_is_invariant_of_behavior inv spec b

/// Proving invariants of semantics

let step_computation_generic_preserves_inv_case_action_pred
  (sip: semantics_invariant_proof_t)
  (actor: sip.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: sip.sem.step_t)
  (s: sip.sem.state_t)
  : Lemma (requires   (sip.inv s)
                    /\ (sip.action_pred (sip.sem.step_to_action_f step))
                    /\ (Some? (step_computation_generic sip.sem actor starts_atomic_block
                                ends_atomic_block step s)))
          (ensures  sip.inv (Some?.v (step_computation_generic sip.sem actor starts_atomic_block ends_atomic_block
                                        step s))) =
  sip.action_proof actor starts_atomic_block ends_atomic_block step s

let step_computation_generic_preserves_inv_case_special_case
  (sip: semantics_invariant_proof_t)
  (actor: sip.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: sip.sem.step_t)
  (s: sip.sem.state_t)
  (prf: action_special_case_invariant_proof_t sip.sem sip.inv)
  : Lemma (requires   (sip.inv s)
                    /\ prf.action == (sip.sem.step_to_action_f step)
                    /\ Some? (step_computation_generic sip.sem actor starts_atomic_block
                               ends_atomic_block step s))
          (ensures  sip.inv (Some?.v (step_computation_generic sip.sem actor starts_atomic_block ends_atomic_block
                                        step s))) =
  prf.special_case_proof actor starts_atomic_block ends_atomic_block step s

let get_proof_option
  (sip: semantics_invariant_proof_t)
  (action: sip.sem.action_t)
  : Ghost (option (action_special_case_invariant_proof_t sip.sem sip.inv))
    (requires contains_ubool action sip.program.actions)
    (ensures  fun proof_option ->
      action_proof_option_applies sip.sem sip.inv sip.action_pred action proof_option) =
  sip.special_cases_apply_proof ();
  let f = action_proof_option_applies sip.sem sip.inv sip.action_pred in
  get_correspondent_from_lists_correspond_ubool f sip.program.actions sip.special_case_proofs action

let step_computation_generic_preserves_inv
  (sip: semantics_invariant_proof_t)
  (actor: sip.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: sip.sem.step_t)
  (s: sip.sem.state_t)
  : Lemma (requires   (sip.inv s)
                    /\ (program_contains_action_of_step_generic sip.sem sip.program step)
                    /\ (Some? (step_computation_generic sip.sem actor starts_atomic_block
                                ends_atomic_block step s)))
          (ensures  sip.inv (Some?.v (step_computation_generic sip.sem actor starts_atomic_block ends_atomic_block
                                        step s))) =
  let action = sip.sem.step_to_action_f step in
  let proof_option = get_proof_option sip action in
  match proof_option with
  | None ->
      assert (action_proof_option_applies sip.sem sip.inv sip.action_pred action None ==
              sip.action_pred action)
        by FStar.Tactics.V2.trefl();
    step_computation_generic_preserves_inv_case_action_pred sip actor starts_atomic_block ends_atomic_block step s
  | Some prf -> step_computation_generic_preserves_inv_case_special_case sip actor
                 starts_atomic_block ends_atomic_block step s prf

let rec eval_steps_generic_preserves_inv
  (sip: semantics_invariant_proof_t)
  (actor: sip.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list sip.sem.step_t)
  (s: sip.sem.state_t)
  : Lemma (requires   sip.inv s
                    /\ for_all_ubool (program_contains_action_of_step_generic sip.sem sip.program) steps
                    /\ Some? (steps_computation_generic sip.sem actor starts_atomic_block
                               ends_atomic_block steps s))
          (ensures  sip.inv (Some?.v (steps_computation_generic sip.sem actor starts_atomic_block
                                        ends_atomic_block steps s)))
          (decreases steps) =
  match steps with
  | [last_step] ->
     step_computation_generic_preserves_inv sip actor starts_atomic_block ends_atomic_block last_step s
  | first_step :: remaining_steps ->
     step_computation_generic_preserves_inv sip actor starts_atomic_block false first_step s;
     let s' = Some?.v (step_computation_generic sip.sem actor starts_atomic_block false first_step s) in
     eval_steps_generic_preserves_inv sip actor false ends_atomic_block remaining_steps s'

let next_transition_generic_preserves_inv
  (sip: semantics_invariant_proof_t)
  (transition: transition_t sip.sem)
  (s: sip.sem.state_t)
  (s': sip.sem.state_t)
  : Lemma (requires   next_transition_generic sip.sem transition s s'
                    /\ (for_all_ubool (program_contains_action_of_step_generic sip.sem sip.program) transition.steps)
                    /\ sip.inv s)
          (ensures  sip.inv s') =
  eval_steps_generic_preserves_inv sip transition.actor true true transition.steps s

let next_program_generic_preserves_inv
  (sip: semantics_invariant_proof_t)
  (transition: transition_t sip.sem)
  (s: sip.sem.state_t)
  (s': sip.sem.state_t)
  : Lemma (requires   next_program_generic sip.sem sip.program transition s s'
                    /\ sip.inv s)
          (ensures sip.inv s') =
  next_transition_generic_preserves_inv sip transition s s'

let semantics_spec_next_preserves_inv
  (sip: semantics_invariant_proof_t)
  (s: sip.sem.state_t)
  (s': sip.sem.state_t)
  : Lemma (requires   sip.inv s
                    /\ (semantics_to_spec sip.sem sip.program).next s s')
          (ensures sip.inv s') =
  eliminate exists transition. next_program_generic sip.sem sip.program transition s s'
  returns   sip.inv s'
  with transition_satisfies_next_program.
    next_program_generic_preserves_inv sip transition s s'

let semantics_invariant_proof_implies_is_invariant_of_spec (sip: semantics_invariant_proof_t)
  (* see .fsti file for spec *) =
  let inv = sip.inv in
  let spec = semantics_to_spec sip.sem sip.program in

  introduce forall s. spec.init s ==> inv s
  with introduce spec.init s ==> inv s
  with given_spec_init. sip.init_implies_inv_proof s;

  introduce forall s s'. inv s /\ spec.next s s' ==> inv s'
  with introduce _ ==> _
  with given_next. (semantics_spec_next_preserves_inv sip s s');
  
  is_inductive_invariant_of_spec_implies_is_invariant_of_spec inv spec

let semantics_invariant_proof_implies_stepwise_inductive_invariant (sip: semantics_invariant_proof_t)
  (* see .fsti file for spec *) =
  let inv = sip.inv in
  let sem = sip.sem in
  introduce forall s. init_program_generic sem sip.program s ==> inv s
  with introduce init_program_generic sem sip.program s ==> inv s
  with given_antecedent. sip.init_implies_inv_proof s;

  introduce forall actor starts_atomic_block ends_atomic_block step s.
                 inv s
               /\ program_contains_action_of_step_generic sem sip.program step
               /\ Some? (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s)
               ==> inv (Some?.v (step_computation_generic sem actor starts_atomic_block ends_atomic_block step s))
  with introduce _ ==> _
  with _. step_computation_generic_preserves_inv sip actor starts_atomic_block ends_atomic_block step s
