module Strategies.Atomic

open Strategies.Semantics
open Util.List

let make_atomic_semantics (sem: semantics_t) : semantics_t = {
  actor_t = sem.actor_t;
  state_t = sem.state_t;
  action_t = list sem.action_t;
  step_t = list sem.step_t;
  step_to_action_f = map_ghost sem.step_to_action_f;
  step_computation_f = steps_computation_generic sem;
}
