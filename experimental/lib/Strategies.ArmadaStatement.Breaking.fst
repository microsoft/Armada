module Strategies.ArmadaStatement.Breaking

open Armada.Action
open Armada.Base
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Spec.List
open Spec.Ubool
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List

let all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (s: Armada.State.t)
  : GTot ubool =
  NotStopped? s.stop_reason ==>
    (forall tid. let thread = s.threads tid in
            ThreadStatusRunning? thread.status ==> is_breaking_pc thread.pc)

let all_other_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (s: Armada.State.t)
  (actor: tid_t)
  : GTot ubool =
  NotStopped? s.stop_reason ==>
    (forall tid. let thread = s.threads tid in
            tid <> actor /\ ThreadStatusRunning? thread.status ==> is_breaking_pc thread.pc)

let final_step_computation_establishes_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_breaking is_breaking_pc s actor
                    /\ action_only_creates_breaking_threads is_breaking_pc step.action
                    /\ action_breaks is_breaking_pc step.action)
          (ensures (match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> all_threads_breaking is_breaking_pc s'
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s;
  step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s

let step_computation_maintains_all_other_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_breaking is_breaking_pc s actor
                    /\ action_only_creates_breaking_threads is_breaking_pc step.action)
          (ensures (match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> all_other_threads_breaking is_breaking_pc s' actor
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s;
  step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s

let rec steps_computation_maintains_all_threads_breaking_if_actions_end_with_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_breaking is_breaking_pc s actor
                    /\ actions_end_with_all_threads_breaking is_breaking_pc (map_ghost armada_step_to_action steps))
          (ensures (match steps_computation actor starts_atomic_block ends_atomic_block steps s with
                    | Some s' -> all_threads_breaking is_breaking_pc s'
                    | None -> True))
          (decreases steps) =
  match steps with
  | [] -> ()
  | [final_step] ->
      final_step_computation_establishes_all_threads_breaking is_breaking_pc actor starts_atomic_block
        ends_atomic_block final_step s
  | first_step :: remaining_steps ->
      step_computation_maintains_all_other_threads_breaking is_breaking_pc actor starts_atomic_block false
        first_step s;
      (match step_computation actor starts_atomic_block false first_step s with
       | None -> ()
       | Some s' ->
           steps_computation_maintains_all_threads_breaking_if_actions_end_with_all_threads_breaking
             is_breaking_pc actor false ends_atomic_block remaining_steps s')

let steps_computation_maintains_all_threads_breaking
  (is_breaking_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_threads_breaking is_breaking_pc s
                    /\ actions_maintain_all_threads_breaking is_breaking_pc (map_ghost armada_step_to_action steps))
          (ensures (match steps_computation actor starts_atomic_block ends_atomic_block steps s with
                    | Some s' -> all_threads_breaking is_breaking_pc s'
                    | None -> True)) =
  let actions = map_ghost armada_step_to_action steps in
  if actions_are_propagate actions then (
    let step = Cons?.hd steps in
    executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s;
    step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s;
    step_computation_requires_start_thread_state actor starts_atomic_block ends_atomic_block step s
  )
  else
    steps_computation_maintains_all_threads_breaking_if_actions_end_with_all_threads_breaking is_breaking_pc
      actor starts_atomic_block ends_atomic_block steps s
