module Strategies.Semantics

open Armada.Program
open Armada.State
open Armada.Threads
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Util.Behavior
open Util.List

noeq type semantics_t = {
  // Types

  actor_t: eqtype;
  state_t: Type;
  action_t: Type;
  step_t: Type;

  // Projections

  step_to_action_f: step_t -> GTot action_t;

  // Functions

  step_computation_f: (actor: actor_t) -> (starts_atomic_block: bool) -> (ends_atomic_block: bool) ->
                        (step: step_t) -> (s: state_t) -> GTot (option state_t);
}

noeq type transition_t (sem: semantics_t) = {
  actor: sem.actor_t;
  steps: list sem.step_t;
}

let make_transition (sem: semantics_t) (actor: sem.actor_t) (steps: list sem.step_t) : transition_t sem =
  { actor = actor; steps = steps }

noeq type program_t (sem: semantics_t) = {
  init_f: sem.state_t -> GTot ubool;
  actions: list sem.action_t;
}

let step_computation_generic
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: sem.step_t)
  (s: sem.state_t)
  : GTot (option sem.state_t) =
  sem.step_computation_f actor starts_atomic_block ends_atomic_block step s

let rec steps_computation_generic
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list sem.step_t)
  (s: sem.state_t)
  : GTot (option sem.state_t)
    (decreases steps) =
  match steps with
  | [] -> None
  | [last_step] -> step_computation_generic sem actor starts_atomic_block ends_atomic_block last_step s
  | first_step :: remaining_steps ->
      (match step_computation_generic sem actor starts_atomic_block false first_step s with
       | None -> None
       | Some s' -> steps_computation_generic sem actor false ends_atomic_block remaining_steps s')

let next_transition_generic
  (sem: semantics_t)
  (transition: transition_t sem)
  (s s': sem.state_t)
  : GTot ubool =
  Some s' == steps_computation_generic sem transition.actor true true transition.steps s

let init_program_generic (sem: semantics_t) (program: program_t sem) (s: sem.state_t) : GTot ubool =
  program.init_f s

let program_contains_action_of_step_generic
  (sem: semantics_t)
  (program: program_t sem)
  (step: sem.step_t)
  : GTot ubool =
  contains_ubool (sem.step_to_action_f step) program.actions

let next_program_generic
  (sem: semantics_t)
  (program: program_t sem)
  (transition: transition_t sem)
  (s s': sem.state_t)
  : GTot ubool =
    for_all_ubool (program_contains_action_of_step_generic sem program) transition.steps
  /\ next_transition_generic sem transition s s'

let semantics_to_spec (sem: semantics_t) (program: program_t sem) : GTot (spec_t sem.state_t) =
  { init = init_program_generic sem program;
    next = fun s s' -> exists transition. next_program_generic sem program transition s s' }

// Useful lemmas

let rec append_one_extends_steps_computation_generic
  (sem: semantics_t)
  (actor: sem.actor_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (first_steps: list sem.step_t)
  (last_step: sem.step_t)
  (s: sem.state_t)
  : Lemma (requires Some? (steps_computation_generic sem actor starts_atomic_block false first_steps s))
          (ensures  (let s' = Some?.v (steps_computation_generic sem actor starts_atomic_block false first_steps s) in
                     steps_computation_generic sem actor starts_atomic_block ends_atomic_block
                       (append first_steps [last_step]) s ==
                         step_computation_generic sem actor false ends_atomic_block last_step s'))
          (decreases first_steps) =
  match first_steps with
  | [] -> ()
  | [last_step] -> ()
  | first_step :: remaining_steps ->
      let s' = Some?.v (step_computation_generic sem actor starts_atomic_block false first_step s) in
      append_one_extends_steps_computation_generic sem actor false ends_atomic_block remaining_steps last_step s'
