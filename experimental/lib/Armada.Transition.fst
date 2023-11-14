module Armada.Transition

open Armada.Action
open Armada.Base
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Threads
open Armada.Type
open Spec.List
open Spec.Ubool

noeq type t = {
  actor: tid_t;
  steps: list Armada.Step.t;
}

let step_computation
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : GTot (option Armada.State.t) =
  action_computation actor starts_atomic_block ends_atomic_block step.nd step.action s

let rec steps_computation
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : GTot (option Armada.State.t)
    (decreases steps) =
  match steps with
  | [] -> None
  | [last_step] -> step_computation actor starts_atomic_block ends_atomic_block last_step s
  | first_step :: remaining_steps ->
      (match step_computation actor starts_atomic_block false first_step s with
       | None -> None
       | Some s' -> steps_computation actor false ends_atomic_block remaining_steps s')

let next_transition (transition: Armada.Transition.t) (s s': Armada.State.t) : GTot bool =
  eqb (Some s') (steps_computation transition.actor true true transition.steps s)
