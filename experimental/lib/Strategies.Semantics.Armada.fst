module Strategies.Semantics.Armada

open Armada.Action
open Armada.Step
open Armada.Program
open Armada.Threads
open Armada.Transition
open Armada.Type
open Spec.Behavior
open Spec.List
open Strategies.Semantics
open Util.Behavior
open Util.List

let rec all_actions_has_all_actions
  (action: Armada.Action.t)
  (program_statements: list program_statement_t)
  : Lemma (contains_ubool action.program_statement program_statements <==>
             (contains_ubool action (all_actions program_statements))) =
  match program_statements with
  | [] -> ()
  | hd :: tl -> if eqb hd action.program_statement then () else all_actions_has_all_actions action tl

let armada_state_satisfies_init_equivalent (program: Armada.Program.t) (s: Armada.State.t)
  : Lemma ((program_to_spec program).init s <==>
           (semantics_to_spec armada_semantics (armada_program_to_generic program)).init s) =
  ()

let rec armada_steps_computation_equivalent
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures  steps_computation actor starts_atomic_block ends_atomic_block steps s ==
                    steps_computation_generic armada_semantics actor starts_atomic_block ends_atomic_block
                      steps s)
          (decreases steps) =
  match steps with
  | [] -> ()
  | [last_step] -> ()
  | first_step :: remaining_steps ->
      (match step_computation actor starts_atomic_block false first_step s with
       | None -> ()
       | Some s' -> armada_steps_computation_equivalent actor false ends_atomic_block remaining_steps s')

let armada_transition_to_generic (transition: Armada.Transition.t) : transition_t armada_semantics =
  { actor = transition.actor; steps = transition.steps; }

let generic_transition_to_armada (transition: transition_t armada_semantics) : Armada.Transition.t =
  { actor = transition.actor; steps = transition.steps; }

let armada_next_transition_equivalent_forward
  (program: Armada.Program.t)
  (transition: Armada.Transition.t)
  (s s': Armada.State.t)
  : Lemma (requires Armada.Transition.next_transition transition s s')
          (ensures  next_transition_generic armada_semantics (armada_transition_to_generic transition) s s') =
  let sem = armada_semantics in
  armada_steps_computation_equivalent transition.actor true true transition.steps s

let armada_next_transition_equivalent_backward
  (transition: transition_t armada_semantics)
  (s s': Armada.State.t)
  : Lemma (requires next_transition_generic armada_semantics transition s s')
          (ensures  Armada.Transition.next_transition (generic_transition_to_armada transition) s s') =
  armada_steps_computation_equivalent transition.actor true true transition.steps s

let armada_next_program_equivalent_forward
  (program: Armada.Program.t)
  (transition: Armada.Transition.t)
  (s s': Armada.State.t)
  : Lemma (requires Armada.Program.next_program program transition s s')
          (ensures  next_program_generic armada_semantics (armada_program_to_generic program)
                     (armada_transition_to_generic transition) s s') =
  let lem (step: Armada.Step.t)
    : Lemma (requires program_contains_statement_of_step program step)
            (ensures  program_contains_action_of_step_generic armada_semantics
                        (armada_program_to_generic program) step) =
    all_actions_has_all_actions step.action program.program_statements in
  for_all_ubool_implication lem transition.steps;
  armada_next_transition_equivalent_forward program transition s s'

let armada_next_program_equivalent_backward
  (program: Armada.Program.t)
  (transition: transition_t armada_semantics)
  (s s': Armada.State.t)
  : Lemma (requires next_program_generic armada_semantics (armada_program_to_generic program) transition s s')
          (ensures  Armada.Program.next_program program (generic_transition_to_armada transition) s s') =
  let lem (step: Armada.Step.t)
    : Lemma (requires program_contains_action_of_step_generic armada_semantics
               (armada_program_to_generic program) step)
            (ensures  program_contains_statement_of_step program step) =
    all_actions_has_all_actions step.action program.program_statements in
  for_all_ubool_implication lem transition.steps;
  armada_next_transition_equivalent_backward transition s s'

let armada_next_equivalent (program: Armada.Program.t) (s s': Armada.State.t)
  : Lemma ((program_to_spec program).next s s' <==>
           (semantics_to_spec armada_semantics (armada_program_to_generic program)).next s s') =
  introduce (program_to_spec program).next s s' ==>
            (semantics_to_spec armada_semantics (armada_program_to_generic program)).next s s'
  with knowing_program_next. (
    eliminate exists transition. Armada.Program.next_program program transition s s'
    returns   _
    with knowing_transition_satisfies_next_program.
      armada_next_program_equivalent_forward program transition s s'
  );
  introduce (semantics_to_spec armada_semantics (armada_program_to_generic program)).next s s' ==>
            (program_to_spec program).next s s'
  with knowing_semantics_next. (
    eliminate exists transition. next_program_generic armada_semantics
                              (armada_program_to_generic program) transition s s'
    returns   _
    with knowing_transition_satisfies_next_program.
      armada_next_program_equivalent_backward program transition s s'
  )

let rec armada_behavior_satisfies_next_equivalent (program: Armada.Program.t) (b: behavior_t Armada.State.t)
  : Lemma (behavior_satisfies_next b (program_to_spec program).next <==>
           behavior_satisfies_next b (semantics_to_spec armada_semantics
                                       (armada_program_to_generic program)).next) =
  match b with
  | [] -> ()
  | [s] -> ()
  | s1 :: s2 :: tl ->
      armada_next_equivalent program s1 s2; armada_behavior_satisfies_next_equivalent program (s2 :: tl)

let armada_behavior_satisfies_generic_spec (program: Armada.Program.t) (b: behavior_t Armada.State.t)
  : Lemma (requires behavior_satisfies_spec b (program_to_spec program))
          (ensures  behavior_satisfies_spec b (semantics_to_spec armada_semantics
                                                (armada_program_to_generic program))) =
  armada_behavior_satisfies_next_equivalent program b;
  armada_state_satisfies_init_equivalent program (Cons?.hd b)

let armada_generic_behavior_satisfies_spec (program: Armada.Program.t) (b: behavior_t Armada.State.t)
  : Lemma (requires behavior_satisfies_spec b (semantics_to_spec armada_semantics
                                                (armada_program_to_generic program)))
          (ensures  behavior_satisfies_spec b (program_to_spec program)) =
  armada_behavior_satisfies_next_equivalent program b;
  armada_state_satisfies_init_equivalent program (Cons?.hd b)

let armada_spec_refines_generic (program: Armada.Program.t)
  (* see .fsti file for spec *) =
  let lspec = program_to_spec program in
  let hspec = semantics_to_spec armada_semantics (armada_program_to_generic program) in
  introduce forall (lb: behavior_t Armada.State.t).
              behavior_satisfies_spec lb lspec ==> 
              (exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb eq2)
  with
    introduce _ ==> _
    with knowing_lb_satisfies_spec. (
      armada_behavior_satisfies_generic_spec program lb;
      refinement_relation_reflexive_implies_behavior_refines_itself lb eq2;
      introduce exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb eq2
      with lb and ())

let armada_generic_refines_spec (program: Armada.Program.t)
  (* see .fsti file for spec *) =
  let lspec = semantics_to_spec armada_semantics (armada_program_to_generic program) in
  let hspec = program_to_spec program in
  introduce forall (lb: behavior_t Armada.State.t).
              behavior_satisfies_spec lb lspec ==>
              (exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb eq2)
  with
    introduce _ ==> _
    with knowing_lb_satisfies_spec. (
      armada_generic_behavior_satisfies_spec program lb;
      refinement_relation_reflexive_implies_behavior_refines_itself lb eq2;
      introduce exists hb. behavior_satisfies_spec hb hspec /\ behavior_refines_behavior lb hb eq2
      with lb and ())

let behavior_satisfies_armada_spec_iff_it_satisfies_generic_spec
  (program: Armada.Program.t)
  (b: behavior_t Armada.State.t)
  (* see .fsti file for spec *) =
  armada_behavior_satisfies_next_equivalent program b;
  match b with
  | [] -> ()
  | s :: _ -> armada_state_satisfies_init_equivalent program s
