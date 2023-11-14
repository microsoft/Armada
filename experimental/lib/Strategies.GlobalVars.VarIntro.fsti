module Strategies.GlobalVars.VarIntro

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.GlobalVars
open Strategies.GlobalVars.Types
open Strategies.PCRelation
open Util.List

let rec pointer_among_global_variables (vs: list var_id_t) (ptr: Armada.Pointer.t) : GTot bool =
  match ptr with
  | PointerUninitialized -> false
  | PointerNull -> false
  | PointerRoot root_id -> not (global_variables_unmentioned_in_root_id vs root_id)
  | PointerField struct_ptr _ -> pointer_among_global_variables vs struct_ptr
  | PointerIndex array_ptr _ -> pointer_among_global_variables vs array_ptr

let rec lvalue_expression_among_global_variables
  (vs: list var_id_t)
  (e: expression_t)
  : GTot bool =
  match e with
  | ExpressionGlobalVariable _ var_id -> list_contains var_id vs
  | ExpressionFieldOf _ obj _ -> lvalue_expression_among_global_variables vs obj
  | _ -> false

let statement_updates_gvars
  (vs: list var_id_t)
  (statement: Armada.Statement.t)
  : GTot bool =
  match statement with
  | UpdateStatement bypassing_write_buffer dst src ->
         lvalue_expression_among_global_variables vs dst
      && global_variables_unaddressed_in_rvalue_expression vs src
  | NondeterministicUpdateStatement bypassing_write_buffer dst ->
      lvalue_expression_among_global_variables vs dst
  | _ -> false

let statement_updates_specific_gvar_to_constant
  (v: var_id_t)
  (td: object_td_t)
  (statement: Armada.Statement.t)
  : GTot ubool =
  match statement with
  | UpdateStatement bypassing_write_buffer (ExpressionGlobalVariable td' v') (ExpressionConstant value) ->
        v' = v
      /\ td' == td
      /\ object_value_to_td value == td
      /\ (ObjectValuePrimitive? value || ObjectValueAbstract? value)
  | _ -> False

let rec statement_updates_gvars_using_constant
  (vs: list var_id_t)
  (tds: list object_td_t)
  (statement: Armada.Statement.t)
  : GTot ubool =
  match vs, tds with
  | v :: remaining_vs, td :: remaining_tds ->
        statement_updates_specific_gvar_to_constant v td statement
      \/ statement_updates_gvars_using_constant remaining_vs remaining_tds statement
  | _, _ -> False

val pointer_among_gvars_implies_gvars_addressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  : Lemma (requires pointer_among_global_variables vs p)
          (ensures  not (global_variables_unaddressed_in_pointer vs p))

val statement_that_updates_gvars_s2_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ statement_updates_gvars vs statement)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s2 with
                     | ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1 s2'
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s2'.mem
                     | _ -> True))

val statement_that_updates_gvars_using_constant_must_succeed
  (vs: list var_id_t)
  (tds: list object_td_t)
  (actor: tid_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (requires   all_gvars_have_types s.mem vs tds
                    /\ statement_updates_gvars_using_constant vs tds statement)
          (ensures  ComputationProduces? (statement_computation actor [] start_pc end_pc statement s))

val propagate_write_message_statement_computation_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ unstarted_threads_have_empty_write_buffers s1
                    /\ unstarted_threads_have_empty_write_buffers s2
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ (let receiver_tid = ObjectValueAbstract?.value (Cons?.hd nd) in
                       let thread1 = s1.threads actor in
                       let thread2 = s2.threads actor in
                       let write_buffer1 = thread1.write_buffer in
                       let write_buffer2 = thread2.write_buffer in
                       let position1 = (s1.threads receiver_tid).position_in_other_write_buffers actor in
                       let position2 = (s2.threads receiver_tid).position_in_other_write_buffers actor in
                         length write_buffer1 > position1
                       /\ length write_buffer2 > position2
                       /\ (let write_message1 = index write_buffer1 position1 in
                          let write_message2 = index write_buffer2 position2 in
                            global_variables_unaddressed_in_write_message vs write_message1
                          /\ global_variables_unaddressed_in_write_message vs write_message2
                          /\ write_messages_match write_message1 write_message2)))
          (ensures  (match propagate_write_message_statement_computation actor nd s1,
                           propagate_write_message_statement_computation actor nd s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                         /\ unstarted_threads_have_empty_write_buffers s1'
                         /\ unstarted_threads_have_empty_write_buffers s2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))

val propagate_write_message_statement_computation_s2_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ unstarted_threads_have_empty_write_buffers s1
                    /\ unstarted_threads_have_empty_write_buffers s2
                    /\ ThreadStatusRunning? (s2.threads actor).status
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ (let receiver_tid = ObjectValueAbstract?.value (Cons?.hd nd) in
                       let thread2 = s2.threads actor in
                       let write_buffer2 = thread2.write_buffer in
                       let position2 = (s2.threads receiver_tid).position_in_other_write_buffers actor in
                         length write_buffer2 > position2
                       /\ (let write_message2 = index write_buffer2 position2 in
                          not (global_variables_unaddressed_in_write_message vs write_message2))))
          (ensures  (match propagate_write_message_statement_computation actor nd s2 with
                     | ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1 s2'
                         /\ global_variables_unaddressed_in_memory vs s2.mem
                         /\ roots_match s2.mem
                         /\ unstarted_threads_have_empty_write_buffers s2'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True))
