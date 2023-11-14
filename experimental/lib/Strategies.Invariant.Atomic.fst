module Strategies.Invariant.Atomic

open FStar.List.Tot
open Spec.Behavior
open Strategies.Atomic
open Strategies.Invariant
open Util.List

/// Proving invariants of atomic semantics

let rec next_atomic_step_preserves_inv_case_action_pred
  (asip: atomic_semantics_invariant_proof_t)
  (actor: asip.sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (atomic_step: list asip.sem.step_t)
  (s: asip.sem.state_t{
      for_all_ubool asip.action_pred (map_ghost asip.sem.step_to_action_f atomic_step)
    /\ (asip.inv s)
    /\ Some? (steps_computation_generic asip.sem actor starts_atomic_block
               ends_atomic_block atomic_step s)})
  : GTot (squash (asip.inv (Some?.v (steps_computation_generic asip.sem actor starts_atomic_block
                                       ends_atomic_block atomic_step s))))
    (decreases atomic_step) =
  match atomic_step with
  | [last_step] -> 
      assert (asip.action_pred (asip.sem.step_to_action_f last_step));
      asip.action_proof actor starts_atomic_block ends_atomic_block last_step s
  | first_step :: remaining_steps ->
      assert (asip.action_pred (asip.sem.step_to_action_f first_step));
      asip.action_proof actor starts_atomic_block false first_step s;
      let s' = Some?.v (step_computation_generic asip.sem actor starts_atomic_block false first_step s) in
      next_atomic_step_preserves_inv_case_action_pred asip actor false ends_atomic_block remaining_steps s'

let atomic_special_case_proof_corresponds_to_action_special_case_proof
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (atomic_special_case_proof: option (atomic_special_case_invariant_proof_t sem inv))
  (action_special_case_proof: option (action_special_case_invariant_proof_t (make_atomic_semantics sem) inv))
  : GTot ubool =
  match atomic_special_case_proof with
  | None -> None? action_special_case_proof
  | Some prf ->    Some? action_special_case_proof
               && eqb prf.atomic_action (Some?.v action_special_case_proof).action

let convert_atomic_special_case_proof_to_action_special_case_proof
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (special_case_proof: option (atomic_special_case_invariant_proof_t sem inv))
  : Ghost (option (action_special_case_invariant_proof_t (make_atomic_semantics sem) inv))
  (requires True)
  (ensures fun action_special_case_proof -> atomic_special_case_proof_corresponds_to_action_special_case_proof sem
                                           inv special_case_proof action_special_case_proof) =
  match special_case_proof with
  | None -> None
  | Some prf ->
      let atomic_sem = make_atomic_semantics sem in
      let lem
        (actor: atomic_sem.actor_t)
        (starts_atomic_block: bool)
        (ends_atomic_block: bool)
        (atomic_step: atomic_sem.step_t)
        (s: atomic_sem.state_t{
             atomic_sem.step_to_action_f atomic_step == prf.atomic_action
           /\ inv s
           /\ Some? (step_computation_generic atomic_sem actor starts_atomic_block
                      ends_atomic_block atomic_step s)})
        : squash (inv (Some?.v (step_computation_generic atomic_sem actor starts_atomic_block
                                  ends_atomic_block atomic_step s))) =
        (prf.special_case_proof actor starts_atomic_block ends_atomic_block atomic_step s) in
      Some ({ action = prf.atomic_action; special_case_proof = lem; })

let rec convert_atomic_special_case_proofs_to_action_special_case_proofs
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (special_case_proofs: list (option (atomic_special_case_invariant_proof_t sem inv)))
  : Ghost (list (option (action_special_case_invariant_proof_t (make_atomic_semantics sem) inv)))
  (requires True)
  (ensures  fun action_special_case_proofs ->
     lists_correspond_ubool
     (atomic_special_case_proof_corresponds_to_action_special_case_proof sem inv)
     special_case_proofs
     action_special_case_proofs) =
  match special_case_proofs with
  | [] -> []
  | first_proof :: remaining_proofs ->
      (convert_atomic_special_case_proof_to_action_special_case_proof sem inv first_proof) ::
      (convert_atomic_special_case_proofs_to_action_special_case_proofs sem inv remaining_proofs)

let rec atomic_special_cases_apply_implies_action_special_cases_apply
  (sem: semantics_t)
  (inv: invariant_t sem.state_t)
  (action_pred: sem.action_t -> GTot ubool)
  (proven_actions: list (list sem.action_t))
  (action_special_case_proofs:
    list (option (action_special_case_invariant_proof_t (make_atomic_semantics sem) inv)))
  (atomic_special_case_proofs:
    list (option (atomic_special_case_invariant_proof_t sem inv)))
  : Lemma (requires   atomic_special_cases_apply sem inv action_pred proven_actions atomic_special_case_proofs
                    /\ lists_correspond_ubool
                        (atomic_special_case_proof_corresponds_to_action_special_case_proof sem inv)
                        atomic_special_case_proofs
                        action_special_case_proofs)
          (ensures action_special_cases_apply (make_atomic_semantics sem) inv
                    (for_all_ubool action_pred) proven_actions action_special_case_proofs) =
  match atomic_special_case_proofs with
  | [] -> ()
  | first_atomic_special_case_proof :: remaining_atomic_special_case_proofs ->
     match action_special_case_proofs with
     | [] -> assert (false)
     | first_action_special_case_proof :: remaining_action_special_case_proofs ->
        atomic_special_cases_apply_implies_action_special_cases_apply
          sem
          inv
          action_pred
          (tl proven_actions)
          remaining_action_special_case_proofs
          remaining_atomic_special_case_proofs

let atomic_semantics_invariant_proof_implies_is_invariant
  (asip: atomic_semantics_invariant_proof_t)
  (* see .fsti file for spec *) =
  let action_special_case_proofs = convert_atomic_special_case_proofs_to_action_special_case_proofs asip.sem asip.inv
                                      asip.special_case_proofs in
  asip.special_cases_apply_proof ();
  atomic_special_cases_apply_implies_action_special_cases_apply asip.sem asip.inv  asip.action_pred
    asip.program.actions action_special_case_proofs asip.special_case_proofs;
  let sip: semantics_invariant_proof_t = {
    sem = make_atomic_semantics asip.sem;
    program = asip.program;
    inv = asip.inv;
    action_pred = for_all_ubool asip.action_pred;
    special_case_proofs = action_special_case_proofs;
    init_implies_inv_proof = asip.init_implies_inv_proof;
    action_proof = next_atomic_step_preserves_inv_case_action_pred asip;
    special_cases_apply_proof = (fun _ -> _);
  } in
  semantics_invariant_proof_implies_is_invariant_of_spec sip

let atomic_semantics_invariant_proof_implies_stepwise_invariant
  (asip: atomic_semantics_invariant_proof_t)
  (* see .fsti file for spec *) =
  let action_special_case_proofs = convert_atomic_special_case_proofs_to_action_special_case_proofs asip.sem asip.inv
                                      asip.special_case_proofs in
  asip.special_cases_apply_proof ();
  atomic_special_cases_apply_implies_action_special_cases_apply asip.sem asip.inv asip.action_pred
    asip.program.actions action_special_case_proofs asip.special_case_proofs;
  let sip: semantics_invariant_proof_t = {
    sem = make_atomic_semantics asip.sem;
    program = asip.program;
    inv = asip.inv;
    action_pred = for_all_ubool asip.action_pred;
    special_case_proofs = action_special_case_proofs;
    init_implies_inv_proof = asip.init_implies_inv_proof;
    action_proof = next_atomic_step_preserves_inv_case_action_pred asip;
    special_cases_apply_proof = (fun _ -> _);
  } in
  semantics_invariant_proof_implies_stepwise_inductive_invariant sip
