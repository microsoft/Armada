module Strategies.ArmadaStatement.Status

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
open FStar.Sequence.Base
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaStatement
open Strategies.PCRelation
open Strategies.Semantics.Armada

let status_unchanged (actor: tid_t) (s: Armada.State.t) (s': Armada.State.t) : Type0 =
      s'.stop_reason = s.stop_reason
   /\ (s'.threads actor).status = (s.threads actor).status
   /\ (s'.threads actor).pc = (s.threads actor).pc
   /\ (forall other_actor. other_actor <> actor ==> s'.threads other_actor == s.threads other_actor)

val push_stack_variables_maintains_status
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : Lemma (ensures  (match push_stack_variables actor writer_pc writer_expression_number method_id
                             frame_uniq initializers s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> status_unchanged actor s s'))

val push_stack_parameters_maintains_status
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : Lemma (ensures  (match push_stack_parameters actor writer_pc writer_expression_number method_id frame_uniq
                             var_ids parameters s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> status_unchanged actor s s'))

val executing_statement_changes_status_depending_on_statement
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (requires   NotStopped? s.stop_reason
                    /\ ThreadStatusRunning? (s.threads actor).status)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s with
                     | ComputationProduces s' ->
                         (match statement with
                          | AssertFalseStatement _ -> StopReasonAssertionFailure? s'.stop_reason
                          | TerminateProcessStatement _ -> StopReasonTerminated? s'.stop_reason
                          | TerminateThreadStatement _ ->
                                NotStopped? s'.stop_reason
                             && ThreadStatusJoinable? (s'.threads actor).status
                          | MethodCallStatement _ _ _ _ _ true (* stack overflow *) ->
                              StopReasonStackOverflow? s'.stop_reason
                          | _ ->
                                 NotStopped? s'.stop_reason
                              && ThreadStatusRunning? (s'.threads actor).status
                              && (s'.threads actor).pc = (s.threads actor).pc)
                     | _ -> True))

val most_statement_types_dont_affect_other_threads
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (ensures
      (match statement_computation actor nd start_pc end_pc statement s with
       | ComputationProduces s' ->
           not (  CreateThreadStatement? statement
                || JoinStatement? statement
                || PropagateWriteMessageStatement? statement) ==>
           (forall other_actor. other_actor <> actor ==> s'.threads other_actor == s.threads other_actor)
       | _ -> True))

val statement_effects_on_other_threads
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (ensures
      (match statement_computation actor nd start_pc end_pc statement s with
       | ComputationProduces s' ->
           (match statement with
            | CreateThreadStatement _ initial_pc _ _ _ _ _ ->
                let create_thread_nd: create_thread_nd_t =
                  ObjectValueAbstract?.value (Cons?.hd nd) in
                let new_tid = create_thread_nd.new_tid in
                if new_tid = 0 then
                  (forall other_actor. other_actor <> actor ==> s'.threads other_actor == s.threads other_actor)
                else (
                    (s'.threads new_tid).pc = initial_pc
                  /\ (forall other_actor. other_actor <> actor /\ other_actor <> new_tid ==>
                                    s'.threads other_actor == s.threads other_actor)
                )
            | JoinStatement join_tid ->
                (match rvalue_computation join_tid actor s with
                 | ComputationProduces tid_value ->
                     let other_tid = PrimitiveBoxThreadId?.tid
                                     (ObjectValuePrimitive?.value tid_value) in
                       (forall other_actor. other_actor <> actor /\ other_actor <> other_tid ==>
                                       s'.threads other_actor == s.threads other_actor)
                     /\ (ThreadStatusPostJoin? (s'.threads other_tid).status)
                 | _ -> False)
            | PropagateWriteMessageStatement ->
                let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
                  (forall other_actor. other_actor <> actor /\ other_actor <> receiver_tid ==>
                                  s'.threads other_actor == s.threads other_actor)
                /\ (s'.threads receiver_tid).status = (s.threads receiver_tid).status
                /\ (s'.threads receiver_tid).pc = (s.threads receiver_tid).pc
            | _ -> (forall other_actor. other_actor <> actor ==>
                                  s'.threads other_actor == s.threads other_actor))
       | _ -> True))

val executing_step_changes_status_depending_on_statement
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures
      (match step_computation actor starts_atomic_block ends_atomic_block step s with
       | Some s' ->
           if not step.action.ok then
             eqb s' ({ s with stop_reason = StopReasonUndefinedBehavior })
           else
             (match step.action.program_statement.statement with
              | AssertFalseStatement _ -> StopReasonAssertionFailure? s'.stop_reason
              | TerminateProcessStatement _ -> StopReasonTerminated? s'.stop_reason
              | TerminateThreadStatement _ ->
                     NotStopped? s'.stop_reason
                  && ThreadStatusJoinable? (s'.threads actor).status
              | MethodCallStatement _ _ _ _ _ true (* stack overflow *) ->
                  StopReasonStackOverflow? s'.stop_reason
              | _ ->    NotStopped? s'.stop_reason
                    && ThreadStatusRunning? (s'.threads actor).status
                    && (s'.threads actor).pc =
                          (match step.action.program_statement.end_pc with
                           | Some pc -> pc
                           | None -> (s.threads actor).pc))
       | None -> True))

val step_effects_on_other_threads
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (ensures
      (match step_computation actor starts_atomic_block ends_atomic_block step s with
       | Some s' ->
           if not step.action.ok then
             eqb s' ({ s with stop_reason = StopReasonUndefinedBehavior })
           else
             (match step.action.program_statement.statement with
              | CreateThreadStatement _ initial_pc _ _ _ _ _ ->
                  let create_thread_nd: create_thread_nd_t =
                    ObjectValueAbstract?.value (Cons?.hd step.nd) in
                  let new_tid = create_thread_nd.new_tid in
                  if new_tid = 0 then
                     (forall other_actor. other_actor <> actor ==> s'.threads other_actor == s.threads other_actor)
                  else (
                      (s'.threads new_tid).pc = initial_pc
                    /\ (forall other_actor. other_actor <> actor /\ other_actor <> new_tid ==>
                                      s'.threads other_actor == s.threads other_actor)
                  )
              | JoinStatement join_tid ->
                  (match rvalue_computation join_tid actor s with
                   | ComputationProduces tid_value ->
                       let other_tid = PrimitiveBoxThreadId?.tid
                                       (ObjectValuePrimitive?.value tid_value) in
                         (forall other_actor. other_actor <> actor /\ other_actor <> other_tid ==>
                                         s'.threads other_actor == s.threads other_actor)
                       /\ (ThreadStatusPostJoin? (s'.threads other_tid).status)
                   | _ -> False)
              | PropagateWriteMessageStatement ->
                  let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd step.nd) in
                    (forall other_actor. other_actor <> actor /\ other_actor <> receiver_tid ==>
                                    s'.threads other_actor == s.threads other_actor)
                  /\ (s'.threads receiver_tid).status = (s.threads receiver_tid).status
                  /\ (s'.threads receiver_tid).pc = (s.threads receiver_tid).pc
              | _ -> (forall other_actor. other_actor <> actor ==>
                                    s'.threads other_actor == s.threads other_actor))
       | None -> True))
