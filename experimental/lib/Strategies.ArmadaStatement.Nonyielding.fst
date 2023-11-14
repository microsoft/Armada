module Strategies.ArmadaStatement.Nonyielding

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
open Strategies.Nonyielding
open Strategies.PCIndices
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List

let all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (s: Armada.State.t)
  : GTot ubool =
  NotStopped? s.stop_reason ==>
    (forall tid. let thread = s.threads tid in
            ThreadStatusRunning? thread.status ==> not (is_nonyielding_pc thread.pc))

let all_other_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (s: Armada.State.t)
  (actor: tid_t)
  : GTot ubool =
  NotStopped? s.stop_reason ==>
    (forall tid. let thread = s.threads tid in
            tid <> actor /\ ThreadStatusRunning? thread.status ==> not (is_nonyielding_pc thread.pc))

let final_step_computation_maintains_all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_threads_yielding is_nonyielding_pc s
                    /\ (step.action.ok ==> ends_atomic_block)
                    /\ action_consistent_with_is_nonyielding_pc is_nonyielding_pc step.action)
          (ensures (match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> all_threads_yielding is_nonyielding_pc s'
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s;
  step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s

let sole_step_computation_maintains_all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_threads_yielding is_nonyielding_pc s
                    /\ action_consistent_with_is_nonyielding_pc is_nonyielding_pc step.action)
          (ensures (match step_computation actor true true step s with
                    | Some s' -> all_threads_yielding is_nonyielding_pc s'
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor true true step s;
  step_effects_on_other_threads actor true true step s

let step_computation_maintains_all_other_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_yielding is_nonyielding_pc s actor
                    /\ action_consistent_with_is_nonyielding_pc is_nonyielding_pc step.action)
          (ensures (match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> all_other_threads_yielding is_nonyielding_pc s' actor
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s;
  step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s

let final_step_computation_establishes_all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_yielding is_nonyielding_pc s actor
                    /\ (step.action.ok ==> ends_atomic_block)
                    /\ action_consistent_with_is_nonyielding_pc is_nonyielding_pc step.action)
          (ensures (match step_computation actor false ends_atomic_block step s with
                    | Some s' -> all_threads_yielding is_nonyielding_pc s'
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor false ends_atomic_block step s;
  step_effects_on_other_threads actor false ends_atomic_block step s

let rec final_steps_computation_establishes_all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_other_threads_yielding is_nonyielding_pc s actor
                    /\ each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc
                        (map_ghost armada_step_to_action steps))
          (ensures (match steps_computation actor false true steps s with
                    | Some s' -> all_threads_yielding is_nonyielding_pc s'
                    | None -> True)) =
  match steps with
  | [] -> ()
  | [step] -> final_step_computation_establishes_all_threads_yielding is_nonyielding_pc actor true step s
  | first_step :: remaining_steps ->
      step_computation_maintains_all_other_threads_yielding is_nonyielding_pc actor false false first_step s;
      (match step_computation actor false false first_step s with
       | Some s' ->
           final_steps_computation_establishes_all_threads_yielding is_nonyielding_pc actor remaining_steps s'
       | None -> ())

let steps_computation_maintains_all_threads_yielding
  (is_nonyielding_pc: pc_t -> GTot bool)
  (actor: tid_t)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   all_threads_yielding is_nonyielding_pc s
                    /\ each_action_consistent_with_is_nonyielding_pc is_nonyielding_pc
                        (map_ghost armada_step_to_action steps))
          (ensures (match steps_computation actor true true steps s with
                    | Some s' -> all_threads_yielding is_nonyielding_pc s'
                    | None -> True)) =
  match steps with
  | [] -> ()
  | [step] -> sole_step_computation_maintains_all_threads_yielding is_nonyielding_pc actor step s
  | first_step :: remaining_steps ->
      step_computation_maintains_all_other_threads_yielding is_nonyielding_pc actor true false first_step s;
      (match step_computation actor true false first_step s with
       | Some s' ->
           final_steps_computation_establishes_all_threads_yielding is_nonyielding_pc actor remaining_steps s'
       | None -> ())

