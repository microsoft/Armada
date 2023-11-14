module Strategies.Semantics.Armada

open Armada.Action
open Armada.Base
open Armada.Step
open Armada.Program
open Armada.Threads
open Armada.Transition
open Armada.Type
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Semantics
open Util.Behavior

let armada_step_to_action (step: Armada.Step.t) : Armada.Action.t =
  step.action

let armada_semantics : semantics_t = {
  actor_t = tid_t;
  state_t = Armada.State.t;
  action_t = Armada.Action.t;
  step_t = Armada.Step.t;
  step_to_action_f = armada_step_to_action;
  step_computation_f = Armada.Transition.step_computation;
}

let rec all_actions (program_statements: list program_statement_t) : list Armada.Action.t =
  match program_statements with
  | [] -> []
  | first_program_statement :: remaining_program_statements ->
      { ok = true; program_statement = first_program_statement } ::
      { ok = false; program_statement = first_program_statement } ::
      all_actions remaining_program_statements

val all_actions_has_all_actions
  (action: Armada.Action.t)
  (program_statements: list program_statement_t)
  : Lemma (contains_ubool action.program_statement program_statements <==>
             (contains_ubool action (all_actions program_statements)))

let armada_program_to_generic (program: Armada.Program.t) : program_t armada_semantics = {
  init_f = Armada.Program.init_program program;
  actions = all_actions program.program_statements;
}

val armada_steps_computation_equivalent
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures  steps_computation actor starts_atomic_block ends_atomic_block steps s ==
                    steps_computation_generic armada_semantics actor starts_atomic_block ends_atomic_block
                      steps s)

val armada_spec_refines_generic (program: Armada.Program.t)
  : Lemma (spec_refines_spec
            (program_to_spec program)
            (semantics_to_spec armada_semantics (armada_program_to_generic program))
            eq2)

val armada_generic_refines_spec (program: Armada.Program.t)
  : Lemma (spec_refines_spec
            (semantics_to_spec armada_semantics (armada_program_to_generic program))
            (program_to_spec program)
            eq2)

val behavior_satisfies_armada_spec_iff_it_satisfies_generic_spec
  (program: Armada.Program.t)
  (b: behavior_t Armada.State.t)
  : Lemma (behavior_satisfies_spec b (program_to_spec program) <==>
           behavior_satisfies_spec b (semantics_to_spec armada_semantics (armada_program_to_generic program)))
