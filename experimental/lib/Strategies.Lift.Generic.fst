module Strategies.Lift.Generic

open FStar.WellFoundedRelation
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Invariant
open Strategies.Semantics
open Util.List
open Util.Logic

noeq type refinement_choice_t (step_t: Type) (state_t: Type) (aux_t: Type) =
  | RefinementChoiceSkip: (aux': aux_t) -> refinement_choice_t step_t state_t aux_t
  | RefinementChoiceIntroduce: (steps: list step_t) -> (state: state_t) -> (aux': aux_t) ->
                               refinement_choice_t step_t state_t aux_t
  | RefinementChoiceLift: (steps: list step_t) -> (state: state_t) -> (aux': aux_t) ->
                          refinement_choice_t step_t state_t aux_t

let refinement_choice_works
  (lr: liftability_relation_t)
  (ls: lr.lsem.state_t)
  (actor: lr.lsem.actor_t)
  (starts_atomic_block: bool)
  (steps: list lr.lsem.step_t)
  (ls': lr.lsem.state_t)
  (hs: lr.hsem.state_t)
  (choice: refinement_choice_t lr.hsem.step_t lr.hsem.state_t lr.aux_t)
  : GTot ubool =
  match choice with
  | RefinementChoiceSkip aux' ->
         starts_atomic_block
      /\ lr.inv ls'
      /\ lr.lh_relation aux' ls' hs
  | RefinementChoiceIntroduce hsteps hs' aux' ->
         starts_atomic_block
      /\ for_all_ubool (program_contains_action_of_step_generic lr.hsem lr.hprog) hsteps
      /\ Some hs' == steps_computation_generic lr.hsem actor starts_atomic_block true
                      hsteps hs
      /\ lr.lh_relation aux' ls hs'
      /\ (match steps with
         | [] -> False
         | lstep :: _ ->
             lr.progress_wfr.relation (lr.progress_measure hs' lstep actor) (lr.progress_measure hs lstep actor))
  | RefinementChoiceLift hsteps hs' aux' ->
        for_all_ubool (program_contains_action_of_step_generic lr.hsem lr.hprog) hsteps
      /\ (Some hs') == steps_computation_generic lr.hsem actor starts_atomic_block true
                        hsteps hs
      /\ lr.inv ls'
      /\ lr.lh_relation aux' ls' hs'

let rec get_refinement_choice
  (lr: liftability_relation_t)
  (aux: lr.aux_t)
  (ls: lr.lsem.state_t)
  (actor: lr.lsem.actor_t)
  (starts_atomic_block: bool)
  (lsteps: list lr.lsem.step_t)
  (ls': lr.lsem.state_t)
  (hs: lr.hsem.state_t{
        eqb (Some ls') (steps_computation_generic lr.lsem actor starts_atomic_block true
                          lsteps ls)
      /\ (for_all_ubool (program_contains_action_of_step_generic lr.lsem lr.lprog) lsteps)
      /\ lr.inv ls
      /\ lr.lh_relation aux ls hs})
  : GTot (choice: refinement_choice_t lr.hsem.step_t lr.hsem.state_t lr.aux_t{
            refinement_choice_works lr ls actor starts_atomic_block lsteps ls' hs choice})
    (decreases (lex_nondep_wfr (default_wfr (list lr.lsem.step_t)) lr.progress_wfr).decreaser
               (lsteps, lr.progress_measure hs (Cons?.hd lsteps) actor)) =
  lr.inv_stepwise_invariant_proof ();
  match lsteps with
  | [lstep] ->
      let ls2 = Some?.v (step_computation_generic lr.lsem actor starts_atomic_block true
                           lstep ls) in
      assert (lr.inv ls2);
      (match lr.paths_liftable_proof actor starts_atomic_block true aux ls hs lstep with
       | StepLifterSkip aux' ->
           RefinementChoiceSkip aux'
       | StepLifterIntroduce hstep aux2 ->
           let hs2 = Some?.v (step_computation_generic lr.hsem actor
                                starts_atomic_block starts_atomic_block hstep hs) in
           if starts_atomic_block then
             RefinementChoiceIntroduce [hstep] hs2 aux2
           else (
             let choice' = get_refinement_choice lr aux2 ls actor starts_atomic_block lsteps ls' hs2 in
             let RefinementChoiceLift hsteps hs' aux' = choice' in
             RefinementChoiceLift (hstep :: hsteps) hs' aux'
           )
        | StepLifterLift hstep aux' ->
            let hs' = Some?.v (step_computation_generic lr.hsem actor starts_atomic_block true
                                 hstep hs) in
            RefinementChoiceLift [hstep] hs' aux')
  | lstep :: lsteps' ->
      let ls2 = Some?.v (step_computation_generic lr.lsem actor starts_atomic_block false
                           lstep ls) in
      lr.inv_stepwise_invariant_proof ();
      assert (lr.inv ls2);
      (match lr.paths_liftable_proof actor starts_atomic_block false aux ls hs lstep with
       | StepLifterSkip aux2 ->
           get_refinement_choice lr aux2 ls2 actor false lsteps' ls' hs
       | StepLifterIntroduce hstep aux2 ->
           let hs2 = Some?.v (step_computation_generic lr.hsem actor
                                starts_atomic_block starts_atomic_block hstep hs) in
           if starts_atomic_block then
             RefinementChoiceIntroduce [hstep] hs2 aux2
           else
             let choice' = get_refinement_choice lr aux2 ls actor starts_atomic_block lsteps ls' hs2 in
             let RefinementChoiceLift hsteps hs' aux' = choice' in
             RefinementChoiceLift (hstep :: hsteps) hs' aux'
       | StepLifterLift hstep aux2 ->
           let hs2 = Some?.v (step_computation_generic lr.hsem actor starts_atomic_block false
                                hstep hs) in
           let choice' = get_refinement_choice lr aux2 ls2 actor false lsteps' ls' hs2 in
           let RefinementChoiceLift hsteps' hs' aux' = choice' in
           RefinementChoiceLift (hstep :: hsteps') hs' aux')

#push-options "--z3rlimit 10"

let rec get_hbehavior_satisfying_next
  (lr: liftability_relation_t)
  (aux: lr.aux_t)
  (ltransition: transition_t lr.lsem)
  (lb: behavior_t lr.lsem.state_t)
  (hs: lr.hsem.state_t{
       behavior_satisfies_next lb (semantics_to_spec lr.lsem lr.lprog).next
    /\ (for_all_ubool (program_contains_action_of_step_generic lr.lsem lr.lprog) ltransition.steps)
    /\ (match lb with
       | ls ::  ls' :: _ ->
            lr.inv ls
          /\ lr.lh_relation aux ls hs
          /\ next_transition_generic lr.lsem ltransition ls ls'
       | _ -> False)})
  : GTot (hb: behavior_t lr.hsem.state_t{
              behavior_satisfies_next hb (semantics_to_spec lr.hsem lr.hprog).next
            /\ behavior_refines_behavior lb hb lr.refinement_relation
            /\ Cons? hb
            /\ Cons?.hd hb == hs})
    (decreases (lex_nondep_wfr (default_wfr (behavior_t lr.lsem.state_t)) lr.progress_wfr).decreaser
               (lb, lr.progress_measure hs (Cons?.hd ltransition.steps) ltransition.actor)) =
  match lb with
  | ls :: ls' :: lb' ->
      lr.lh_relation_implies_refinement_proof aux ls hs;
      let choice = get_refinement_choice lr aux ls ltransition.actor true ltransition.steps ls' hs in
      (match choice with
       | RefinementChoiceSkip aux' ->
           (match lb' with
            | [] ->
                lr.lh_relation_implies_refinement_proof aux' ls' hs;
                [hs]
            | ls'' :: lb'' ->
                let ltransition' = simpler_indefinite_description
                  (fun ltransition' -> next_program_generic lr.lsem lr.lprog ltransition' ls' ls'') in
                get_hbehavior_satisfying_next lr aux' ltransition' (ls' :: lb') hs)
       | RefinementChoiceIntroduce hsteps hs' aux' ->
           lr.lh_relation_implies_refinement_proof aux' ls hs';
           let hb' = get_hbehavior_satisfying_next lr aux' ltransition lb hs' in
           let htransition = { actor = ltransition.actor <: lr.hsem.actor_t; steps = hsteps } in
           assert (next_program_generic lr.hsem lr.hprog htransition hs hs');
           hs :: hb'
       | RefinementChoiceLift hsteps hs' aux' ->
           lr.lh_relation_implies_refinement_proof aux' ls' hs';
           let htransition = { actor = ltransition.actor <: lr.hsem.actor_t; steps = hsteps } in
           assert (next_program_generic lr.hsem lr.hprog htransition hs hs');
           (match lb' with
            | [] ->
                [hs; hs']
            | ls'' :: lb'' ->
                let ltransition' = simpler_indefinite_description
                  (fun ltransition' -> next_program_generic lr.lsem lr.lprog ltransition' ls' ls'') in
                let hb' = get_hbehavior_satisfying_next lr aux' ltransition' (ls' :: lb') hs' in
                hs :: hb'))

#pop-options

let get_hbehavior_satisfying_spec
  (lr: liftability_relation_t)
  (lb: behavior_t lr.lsem.state_t{behavior_satisfies_spec lb (semantics_to_spec lr.lsem lr.lprog)})
  : GTot (hb: behavior_t lr.hsem.state_t{
              behavior_satisfies_spec hb (semantics_to_spec lr.hsem lr.hprog)
            /\ behavior_refines_behavior lb hb lr.refinement_relation}) =
  match lb with
  | ls :: lb' ->
      lr.inv_stepwise_invariant_proof ();
      let hs, aux = lr.init_implies_relation_proof ls in
      (match lb' with
       | [] ->
           lr.lh_relation_implies_refinement_proof aux ls hs;
           [hs]
       | ls' :: _ ->
           let ltransition = simpler_indefinite_description
             (fun ltransition -> next_program_generic lr.lsem lr.lprog ltransition ls ls') in
           get_hbehavior_satisfying_next lr aux ltransition lb hs)

let liftability_relation_implies_refinement (lr: liftability_relation_t)
  (* see .fsti file for spec *) =
  let lspec = semantics_to_spec lr.lsem lr.lprog in
  let hspec = semantics_to_spec lr.hsem lr.hprog in
  introduce forall lb. behavior_satisfies_spec lb lspec ==>
              (exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb lr.refinement_relation)
  with introduce _ ==> _
  with _.
    introduce exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb lr.refinement_relation
    with (get_hbehavior_satisfying_spec lr lb)
    and ()
