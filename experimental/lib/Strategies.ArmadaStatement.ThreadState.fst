module Strategies.ArmadaStatement.ThreadState

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open FStar.Tactics
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaStatement
open Strategies.ArmadaStatement.Status
open Strategies.PCIndices
open Strategies.PCRelation
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List
open Util.Relation
open Util.Tactics

type thread_state_t =
  | ThreadStateRunning: thread_state_t
  | ThreadStateAtPC: (pc: pc_t) -> thread_state_t
  | ThreadStateNotRunning: (status: thread_status_t) -> thread_state_t
  | ThreadStateProcessStopped: (stop_reason: stop_reason_t) -> thread_state_t

type efficient_thread_state_t =
  | EfficientThreadStateRunning: efficient_thread_state_t
  | EfficientThreadStateAtPC: (pc: nat) -> efficient_thread_state_t
  | EfficientThreadStateNotRunning: (status: thread_status_t) -> efficient_thread_state_t
  | EfficientThreadStateProcessStopped: (stop_reason: stop_reason_t) -> efficient_thread_state_t

let thread_state_applies (s: Armada.State.t) (actor: tid_t) (ts: thread_state_t) : GTot bool =
  match ts with
  | ThreadStateRunning ->
         NotStopped? s.stop_reason
      && ThreadStatusRunning? (s.threads actor).status
  | ThreadStateAtPC pc ->
         NotStopped? s.stop_reason
      && ThreadStatusRunning? (s.threads actor).status
      && (s.threads actor).pc = pc
  | ThreadStateNotRunning status ->
         NotStopped? s.stop_reason
      && (s.threads actor).status = status
      && not (ThreadStatusRunning? status)
  | ThreadStateProcessStopped stop_reason ->
         s.stop_reason = stop_reason
      && not (NotStopped? stop_reason)

let action_enabled_in_thread_state (ts: thread_state_t) (action: Armada.Action.t) : GTot bool =
  match ts with
  | ThreadStateRunning -> None? action.program_statement.start_pc
  | ThreadStateAtPC pc ->
      (match action.program_statement.start_pc with
       | Some start_pc -> start_pc = pc
       | None -> true)
  | ThreadStateNotRunning _ -> false
  | ThreadStateProcessStopped _ -> false

let action_ensures_final_thread_state (ts: thread_state_t) (action: Armada.Action.t) : GTot bool =
  if not action.ok then
    ts = ThreadStateProcessStopped StopReasonUndefinedBehavior
  else
    match action.program_statement.statement with
    | AssertFalseStatement _ -> ts = ThreadStateProcessStopped StopReasonAssertionFailure
    | TerminateProcessStatement _ -> ts = ThreadStateProcessStopped StopReasonTerminated
    | TerminateThreadStatement _ -> ts = ThreadStateNotRunning ThreadStatusJoinable
    | MethodCallStatement _ _ _ _ _ true (* stack overflow *) -> ts = ThreadStateProcessStopped StopReasonStackOverflow
    | _ -> (match action.program_statement.end_pc with
           | Some pc -> ts = ThreadStateAtPC pc || ts = ThreadStateRunning
           | None -> ts = ThreadStateRunning)

let action_to_starting_thread_state (action: Armada.Action.t) : GTot thread_state_t =
  match action.program_statement.start_pc with
  | Some pc -> ThreadStateAtPC pc
  | None -> ThreadStateRunning

let efficient_action_to_starting_thread_state (pc_indices: statement_pc_indices_t) : GTot efficient_thread_state_t =
  match pc_indices.start_pc_index with
  | Some pc -> EfficientThreadStateAtPC pc
  | None -> EfficientThreadStateRunning

let program_statement_to_ending_thread_state (ps: program_statement_t) : thread_state_t =
  match ps.statement with
  | AssertFalseStatement _ -> ThreadStateProcessStopped StopReasonAssertionFailure
  | TerminateProcessStatement _ -> ThreadStateProcessStopped StopReasonTerminated
  | TerminateThreadStatement _ -> ThreadStateNotRunning ThreadStatusJoinable
  | MethodCallStatement _ _ _ _ _ true (* stack overflow *) -> ThreadStateProcessStopped StopReasonStackOverflow
  | _ -> (match ps.end_pc with
         | Some pc -> ThreadStateAtPC pc
         | None -> ThreadStateRunning)

let action_to_ending_thread_state (action: Armada.Action.t) : thread_state_t =
  if not action.ok then
    ThreadStateProcessStopped StopReasonUndefinedBehavior
  else
    program_statement_to_ending_thread_state action.program_statement

let efficient_program_statement_to_ending_thread_state
  (ps: program_statement_t)
  (pc_indices: statement_pc_indices_t)
  : efficient_thread_state_t =
  match ps.statement with
  | AssertFalseStatement _ -> EfficientThreadStateProcessStopped StopReasonAssertionFailure
  | TerminateProcessStatement _ -> EfficientThreadStateProcessStopped StopReasonTerminated
  | TerminateThreadStatement _ -> EfficientThreadStateNotRunning ThreadStatusJoinable
  | MethodCallStatement _ _ _ _ _ true (* stack overflow *) ->
      EfficientThreadStateProcessStopped StopReasonStackOverflow
  | _ -> (match pc_indices.end_pc_index with
         | Some pc -> EfficientThreadStateAtPC pc
         | None -> EfficientThreadStateRunning)

let efficient_action_to_ending_thread_state
  (action: Armada.Action.t)
  (pc_indices: statement_pc_indices_t)
  : efficient_thread_state_t =
  if not action.ok then
    EfficientThreadStateProcessStopped StopReasonUndefinedBehavior
  else
    efficient_program_statement_to_ending_thread_state action.program_statement pc_indices

let thread_states_match_per_pc_relation
  (relation: relation_t pc_t pc_t)
  (ts1: thread_state_t)
  (ts2: thread_state_t)
  : GTot bool =
  match ts1, ts2 with
  | ThreadStateAtPC pc1, ThreadStateAtPC pc2 -> relation pc1 pc2
  | ThreadStateNotRunning status1, ThreadStateNotRunning status2 -> status1 = status2
  | ThreadStateProcessStopped stop_reason1, ThreadStateProcessStopped stop_reason2 -> stop_reason1 = stop_reason2
  | _, _ -> false

let efficient_thread_states_match_per_pc_relation
  (relation: relation_t nat nat)
  (ts1: efficient_thread_state_t)
  (ts2: efficient_thread_state_t)
  : GTot bool =
  match ts1, ts2 with
  | EfficientThreadStateAtPC pc1, EfficientThreadStateAtPC pc2 -> relation pc1 pc2
  | EfficientThreadStateNotRunning status1, EfficientThreadStateNotRunning status2 -> status1 = status2
  | EfficientThreadStateProcessStopped stop_reason1, EfficientThreadStateProcessStopped stop_reason2 ->
      stop_reason1 = stop_reason2
  | _, _ -> false

let efficient_starting_thread_states_match_per_pc_relation_implies_thread_states_match_per_pc_relation
  (pcs1: array_t pc_t)
  (pcs2: array_t pc_t)
  (idx_relation: relation_t nat nat)
  (pc_relation: relation_t pc_t pc_t)
  (action1: Armada.Action.t)
  (action2: Armada.Action.t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : Lemma (requires   program_statement_corresponds_to_statement_pc_indices pcs1 action1.program_statement pc_indices1
                    /\ program_statement_corresponds_to_statement_pc_indices pcs2 action2.program_statement pc_indices2
                    /\ efficient_thread_states_match_per_pc_relation idx_relation
                         (efficient_action_to_starting_thread_state pc_indices1)
                         (efficient_action_to_starting_thread_state pc_indices2)
                    /\ (forall (idx1: nat) (idx2: nat). idx1 < array_len pcs1 /\ idx2 < array_len pcs2 ==>
                         (let pc1 = array_index pcs1 idx1 in
                          let pc2 = array_index pcs2 idx2 in
                          idx_relation idx1 idx2 ==> pc_relation pc1 pc2)))
         (ensures thread_states_match_per_pc_relation pc_relation (action_to_starting_thread_state action1)
                    (action_to_starting_thread_state action2)) =
  ()

let efficient_ending_thread_states_match_per_pc_relation_implies_thread_states_match_per_pc_relation
  (pcs1: array_t pc_t)
  (pcs2: array_t pc_t)
  (idx_relation: relation_t nat nat)
  (pc_relation: relation_t pc_t pc_t)
  (action1: Armada.Action.t)
  (action2: Armada.Action.t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : Lemma (requires   program_statement_corresponds_to_statement_pc_indices pcs1 action1.program_statement pc_indices1
                    /\ program_statement_corresponds_to_statement_pc_indices pcs2 action2.program_statement pc_indices2
                    /\ efficient_thread_states_match_per_pc_relation idx_relation
                         (efficient_action_to_ending_thread_state action1 pc_indices1)
                         (efficient_action_to_ending_thread_state action2 pc_indices2)
                    /\ (forall (idx1: nat) (idx2: nat). idx1 < array_len pcs1 /\ idx2 < array_len pcs2 ==>
                         (let pc1 = array_index pcs1 idx1 in
                          let pc2 = array_index pcs2 idx2 in
                          idx_relation idx1 idx2 ==> pc_relation pc1 pc2)))
         (ensures thread_states_match_per_pc_relation pc_relation (action_to_ending_thread_state action1)
                    (action_to_ending_thread_state action2)) =
  ()

let step_computation_has_thread_state_effect
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures (let ts = action_to_ending_thread_state step.action in
                    match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> thread_state_applies s' actor ts
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s

let step_computation_requires_start_thread_state
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures (let ts = action_to_starting_thread_state step.action in
                    match step_computation actor starts_atomic_block ends_atomic_block step s with
                    | Some s' -> thread_state_applies s actor ts
                    | None -> True)) =
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s

let steps_computation_requires_start_thread_state
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures (match steps_computation actor starts_atomic_block ends_atomic_block steps s with
                    | Some s' -> thread_state_applies s actor (action_to_starting_thread_state (Cons?.hd steps).action)
                    | None -> True)) =
  match steps with
  | [] -> ()
  | first_step :: _ ->
      executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block
        first_step s

let rec actions_to_ending_thread_state
  (actions: list Armada.Action.t)
  : GTot thread_state_t (decreases actions) =
  match actions with
  | [] -> ThreadStateRunning
  | [action] -> action_to_ending_thread_state action
  | first_action :: remaining_actions -> actions_to_ending_thread_state remaining_actions

let rec efficient_actions_to_ending_thread_state
  (actions: list Armada.Action.t)
  (pc_indices_list: list statement_pc_indices_t)
  : GTot efficient_thread_state_t (decreases actions) =
  match actions, pc_indices_list with
  | [], _ -> EfficientThreadStateRunning
  | [action], [pc_indices] -> efficient_action_to_ending_thread_state action pc_indices
  | first_action :: remaining_actions, first_pc_indices :: remaining_pc_indices ->
      efficient_actions_to_ending_thread_state remaining_actions remaining_pc_indices
  | _, _ -> EfficientThreadStateRunning

let rec steps_to_ending_thread_state
  (steps: list Armada.Step.t)
  : GTot thread_state_t (decreases steps) =
  match steps with
  | [] -> ThreadStateRunning
  | [step] -> action_to_ending_thread_state step.action
  | first_step :: remaining_steps -> steps_to_ending_thread_state remaining_steps

let rec steps_computation_has_thread_state_effect
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures (let ts = steps_to_ending_thread_state steps in
                    match steps_computation actor starts_atomic_block ends_atomic_block steps s with
                    | Some s' -> thread_state_applies s' actor ts
                    | None -> True))
          (decreases steps) =
  match steps with
  | [] -> ()
  | [step] ->
      executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s
  | first_step :: remaining_steps ->
      executing_step_changes_status_depending_on_statement actor starts_atomic_block false first_step s;
      (match step_computation actor starts_atomic_block false first_step s with
       | Some s' ->
           steps_computation_has_thread_state_effect actor false ends_atomic_block remaining_steps s'
       | None -> ())

let steps_computation_permitting_empty
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : GTot (option Armada.State.t) =
  match steps with
  | [] -> Some s
  | _ -> steps_computation actor starts_atomic_block ends_atomic_block steps s

let rec steps_computation_permitting_empty_has_thread_state_effect
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures  (Cons? steps ==>
                     (let ts = actions_to_ending_thread_state (map_ghost armada_step_to_action steps) in
                      match steps_computation actor starts_atomic_block ends_atomic_block steps s with
                      | Some s' -> thread_state_applies s' actor ts
                      | None -> True)))
          (decreases steps) =
  match steps with
  | [] -> ()
  | [step] ->
      executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s
  | first_step :: remaining_steps ->
      executing_step_changes_status_depending_on_statement actor starts_atomic_block false first_step s;
      (match step_computation actor starts_atomic_block false first_step s with
       | Some s' ->
           steps_computation_permitting_empty_has_thread_state_effect actor false ends_atomic_block remaining_steps s'
       | None -> ())
