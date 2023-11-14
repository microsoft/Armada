module Strategies.GlobalVars.Statement

open Armada.Base
open Armada.BinaryOp
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open Armada.UnaryOp
open FStar.Sequence.Ambient
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.GlobalVars
open Strategies.GlobalVars.Pointer
open Strategies.GlobalVars.Util
open Strategies.PCRelation
open Strategies.ArmadaStatement.Status
open Util.Seq

let statement_effect_independent_preconditions
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t) =
     states_match_except_global_variables vs pc_relation s1 s2
   /\ global_variables_unaddressed_in_memory vs s1.mem
   /\ global_variables_unaddressed_in_memory vs s2.mem
   /\ roots_match s1.mem
   /\ roots_match s2.mem
   /\ unstarted_threads_have_empty_write_buffers s1
   /\ unstarted_threads_have_empty_write_buffers s2
   /\ pc_relation.relation start_pc1 start_pc2
   /\ ThreadStatusRunning? (s1.threads actor).status

let statement_effect_independent_postconditions
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (cs1': conditional_computation_t Armada.State.t)
  (cs2': conditional_computation_t Armada.State.t) =
  match cs1', cs2' with
  | ComputationProduces s1', ComputationProduces s2' ->
        states_match_except_global_variables vs pc_relation s1' s2'
      /\ global_variables_unaddressed_in_memory vs s1'.mem
      /\ global_variables_unaddressed_in_memory vs s2'.mem
      /\ roots_match s1'.mem
      /\ roots_match s2'.mem
  | ComputationImpossible, ComputationImpossible -> True
  | ComputationUndefined, ComputationUndefined -> True
  | _ -> False

#push-options "--z3rlimit 20"

let statement_effect_independent_in_assume_expression_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (exp: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs exp)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (assume_expression_statement_computation actor nd start_pc1 exp s1)
                      (assume_expression_statement_computation actor nd start_pc2 exp s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2

let statement_effect_independent_in_assert_true_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (exp: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs exp)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (assert_true_statement_computation actor nd start_pc1 exp s1)
                      (assert_true_statement_computation actor nd start_pc2 exp s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2

let statement_effect_independent_in_assert_false_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (exp: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs exp)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (assert_false_statement_computation actor nd start_pc1 exp s1)
                      (assert_false_statement_computation actor nd start_pc2 exp s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2

let statement_effect_independent_in_conditional_jump_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (cond: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs cond)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (conditional_jump_statement_computation actor nd start_pc1 cond s1)
                      (conditional_jump_statement_computation actor nd start_pc2 cond s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation cond actor s1 s2

let statement_effect_independent_in_unconditional_jump_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (unconditional_jump_statement_computation actor nd start_pc1 s1)
                      (unconditional_jump_statement_computation actor nd start_pc2 s2)) =
  ()

let statement_effect_independent_in_update_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (src: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs dst
                    /\ global_variables_unmentioned_in_expression vs src)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (update_statement_computation actor nd start_pc1 bypassing_write_buffer dst src s1)
                      (update_statement_computation actor nd start_pc2 bypassing_write_buffer dst src s2)) =
  if   Cons? nd
     || neqb (expression_to_td dst) (expression_to_td src) then
    ()
  else (
    assert (global_variables_unmentioned_in_expression vs src);
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation src actor s1 s2;
    (match rvalue_computation src actor s1 with
     | ComputationImpossible | ComputationUndefined -> ()
     | ComputationProduces src_value ->
         update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation
           dst actor start_pc1 start_pc2 0 0 bypassing_write_buffer src_value s1 s2)
  )

let statement_effect_independent_in_nondeterministic_update_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs dst)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (nondeterministic_update_statement_computation actor nd start_pc1 bypassing_write_buffer
                         dst s1)
                      (nondeterministic_update_statement_computation actor nd start_pc2 bypassing_write_buffer
                         dst s2)) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (expression_to_td dst) then
    ()
  else (
    let nd_value = Cons?.hd nd in
    if not (object_value_has_all_pointers_uninitialized nd_value) then
      ()
    else (
      if_object_value_has_all_pointers_uninitialized_then_it_doesnt_depend_on_gvars vs nd_value;
      update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation
           dst actor start_pc1 start_pc2 0 0 bypassing_write_buffer nd_value s1 s2
    )
  )

let statement_effect_independent_in_compare_and_swap_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (target: expression_t)
  (old_val: expression_t)
  (new_val: expression_t)
  (bypassing_write_buffer: bool)
  (optional_result: option expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs target
                    /\ global_variables_unmentioned_in_expression vs old_val
                    /\ global_variables_unmentioned_in_expression vs new_val
                    /\ global_variables_unmentioned_in_optional_expression vs optional_result)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (compare_and_swap_statement_computation actor nd start_pc1 target old_val new_val
                         bypassing_write_buffer optional_result s1)
                      (compare_and_swap_statement_computation actor nd start_pc2 target old_val new_val
                         bypassing_write_buffer optional_result s2)) =
  if   Cons? nd
     || neqb (expression_to_td target) (expression_to_td old_val)
     || neqb (expression_to_td target) (expression_to_td new_val)
     || (match optional_result with
        | Some result -> neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDBool)
        | None -> false) then
    ()
  else begin
    check_expression_up_to_date_for_rmw_doesnt_depend_on_gvars vs pc_relation target actor s1 s2;
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation old_val actor s1 s2;
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation target actor s1 s2;
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation new_val actor s1 s2;
    lvalue_computation_doesnt_depend_on_global_variables vs pc_relation target actor s1 s2;
    match check_expression_up_to_date_for_rmw target actor s1, rvalue_computation old_val actor s1,
          rvalue_computation target actor s1, rvalue_computation new_val actor s1,
          lvalue_computation target actor s1 with
    | ComputationProduces _, ComputationProduces old_value,
      ComputationProduces target_value, ComputationProduces new_value,
      ComputationProduces target_ptr -> begin
        let swap = eqb target_value old_value in
        update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation target_ptr actor start_pc1 start_pc2 0 0 false new_value s1 s2;
        match optional_result with
        | None -> ()
        | Some result ->
          lvalue_computation_doesnt_depend_on_global_variables vs pc_relation result actor s1 s2;
          match lvalue_computation result actor s1,
                (if swap then update_pointed_to_value target_ptr actor start_pc1 0 false new_value s1 else return s1),
                (if swap then update_pointed_to_value target_ptr actor start_pc2 0 false new_value s2 else return s2) with
          | ComputationProduces result_ptr, ComputationProduces s1', ComputationProduces s2' ->
              let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
              update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation result_ptr actor start_pc1 start_pc2 1 1 bypassing_write_buffer swap_value s1' s2'
          | _ -> ()
      end
    | _ -> ()
  end

let statement_effect_independent_in_atomic_exchange_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (old_val: expression_t)
  (target: expression_t)
  (new_val: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs old_val
                    /\ global_variables_unmentioned_in_expression vs target
                    /\ global_variables_unmentioned_in_expression vs new_val)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (atomic_exchange_statement_computation actor nd start_pc1 old_val target new_val s1)
                      (atomic_exchange_statement_computation actor nd start_pc2 old_val target new_val s2)) =
  // I hate to do this (for potential performance issues), but it works fine this time and it eliminates so many line of proofs...
  check_expression_up_to_date_for_rmw_doesnt_depend_on_gvars vs pc_relation target actor s1 s2;
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation target actor s1 s2;
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation new_val actor s1 s2;
  lvalue_computation_doesnt_depend_on_global_variables vs pc_relation old_val actor s1 s2;
  assert (lvalue_computation old_val actor s1 == lvalue_computation old_val actor s2);
  lvalue_computation_doesnt_depend_on_global_variables vs pc_relation target actor s1 s2;
  assert (lvalue_computation target actor s1 == lvalue_computation target actor s2);
  match check_expression_up_to_date_for_rmw target actor s1, rvalue_computation target actor s1, rvalue_computation new_val actor s1, lvalue_computation old_val actor s1, lvalue_computation target actor s1 with
  | ComputationProduces _, ComputationProduces target_value, ComputationProduces new_value, ComputationProduces old_ptr, ComputationProduces target_ptr ->
    update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation old_ptr actor start_pc1 start_pc2 0 0 false target_value s1 s2;
    begin match update_pointed_to_value old_ptr actor start_pc1 0 false target_value s1, update_pointed_to_value old_ptr actor start_pc2 0 false target_value s2 with
          | ComputationProduces s1', ComputationProduces s2' ->
            update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation target_ptr actor start_pc1 start_pc2 1 1 false new_value s1' s2'
          | _ -> ()
    end
  | _ -> ()

let statement_effect_independent_in_create_thread_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (method_id: method_id_t)
  (initial_pc1: pc_t)
  (initial_pc2: pc_t)
  (bypassing_write_buffer: bool)
  (optional_result: option expression_t)
  (parameter_var_ids: list var_id_t)
  (parameter_expressions: list expression_t)
  (local_variable_initializers: list initializer_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ pc_relation.relation initial_pc1 initial_pc2
                    /\ (match optional_result with
                       | Some result -> global_variables_unmentioned_in_expression vs result
                       | None -> true)
                    /\ global_variables_unmentioned_in_expressions vs parameter_expressions
                    /\ global_variables_unaddressed_in_initializers vs local_variable_initializers)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (create_thread_statement_computation actor nd start_pc1 method_id initial_pc1
                         bypassing_write_buffer optional_result parameter_var_ids parameter_expressions
                         local_variable_initializers s1)
                      (create_thread_statement_computation actor nd start_pc2 method_id initial_pc2
                         bypassing_write_buffer optional_result parameter_var_ids parameter_expressions
                         local_variable_initializers s2)) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract create_thread_nd_t)
     || (   Some? optional_result
        && neqb (expression_to_td (Some?.v optional_result)) (ObjectTDPrimitive PrimitiveTDThreadId))
     || list_len parameter_var_ids <> list_len parameter_expressions then
    ()
  else (
    let create_thread_nd: create_thread_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let new_tid = create_thread_nd.new_tid in
    if new_tid = 0 then
      (match optional_result with
       | None -> ()
       | Some result ->
          let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
          update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation result
            actor start_pc1 start_pc2
            (list_len parameter_var_ids + list_len local_variable_initializers)
            (list_len parameter_var_ids + list_len local_variable_initializers)
            bypassing_write_buffer new_tid_value s1 s2)
    else (
      let frame_uniq = create_thread_nd.frame_uniq in
      let new_thread = s1.threads new_tid in
      if   new_thread.status <> ThreadStatusNotStarted
         || length new_thread.write_buffer <> 0
         || list_contains frame_uniq s1.uniqs_used then
        ()
      else (
        rvalues_computation_doesnt_depend_on_global_variables vs pc_relation parameter_expressions actor s1 s2;
        match rvalues_computation parameter_expressions actor s1 with
        | ComputationImpossible | ComputationUndefined -> ()
        | ComputationProduces parameter_values ->
            let s21 = make_thread_running method_id initial_pc1 new_tid frame_uniq s1 in
            let s22 = make_thread_running method_id initial_pc2 new_tid frame_uniq s2 in
            make_thread_running_doesnt_depend_on_gvars vs pc_relation method_id initial_pc1 initial_pc2
              new_tid frame_uniq s1 s2;
            push_stack_parameters_doesnt_depend_on_gvars vs pc_relation new_tid start_pc1 start_pc2 0 0 method_id
              frame_uniq parameter_var_ids parameter_values s21 s22;
            (match push_stack_parameters new_tid start_pc1 0 method_id frame_uniq parameter_var_ids
                     parameter_values s21,
                   push_stack_parameters new_tid start_pc2 0 method_id frame_uniq parameter_var_ids
                     parameter_values s22 with
             | ComputationProduces s31, ComputationProduces s32 ->
                  push_stack_variables_doesnt_depend_on_gvars vs pc_relation new_tid start_pc1 start_pc2
                    (list_len parameter_var_ids) (list_len parameter_var_ids) method_id frame_uniq
                    local_variable_initializers s31 s32;
                  (match push_stack_variables new_tid start_pc1 (list_len parameter_var_ids) method_id frame_uniq
                           local_variable_initializers s31,
                         push_stack_variables new_tid start_pc2 (list_len parameter_var_ids) method_id frame_uniq
                           local_variable_initializers s32 with
                   | ComputationProduces s41, ComputationProduces s42 ->
                       (match optional_result with
                        | None -> ()
                        | Some result ->
                           let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
                           push_stack_parameters_maintains_status new_tid start_pc1 0 method_id frame_uniq
                             parameter_var_ids parameter_values s21;
                           push_stack_variables_maintains_status new_tid start_pc1 (list_len parameter_var_ids)
                             method_id frame_uniq local_variable_initializers s31;
                           assert (new_tid <> actor);
                           assert (s41.threads actor == s21.threads actor);
                           update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation result
                             actor start_pc1 start_pc2
                             (list_len parameter_var_ids + list_len local_variable_initializers)
                             (list_len parameter_var_ids + list_len local_variable_initializers)
                             bypassing_write_buffer new_tid_value s41 s42)
                   | _, _ -> ())
             | _, _ -> ())
      )
    )
  )

let statement_effect_independent_in_method_call_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (method_id: method_id_t)
  (return_pc1: pc_t)
  (return_pc2: pc_t)
  (parameter_var_ids: list var_id_t)
  (parameter_expressions: list expression_t)
  (local_variable_initializers: list initializer_t)
  (stack_overflow: bool)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ pc_relation.relation return_pc1 return_pc2
                    /\ pc_relation.return_relation return_pc1 return_pc2
                    /\ global_variables_unmentioned_in_expressions vs parameter_expressions
                    /\ global_variables_unaddressed_in_initializers vs local_variable_initializers)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (method_call_statement_computation actor nd start_pc1 method_id return_pc1 parameter_var_ids
                         parameter_expressions local_variable_initializers stack_overflow s1)
                      (method_call_statement_computation actor nd start_pc2 method_id return_pc2 parameter_var_ids
                         parameter_expressions local_variable_initializers stack_overflow s2)) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract method_call_nd_t) then
    ()
  else (
    let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let frame_uniq = method_call_nd.frame_uniq in
    rvalues_computation_doesnt_depend_on_global_variables vs pc_relation parameter_expressions actor s1 s2;
    match rvalues_computation parameter_expressions actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces parameter_values ->
        let s21 = push_stack_frame actor method_id return_pc1 frame_uniq s1 in
        let s22 = push_stack_frame actor method_id return_pc2 frame_uniq s2 in
        push_stack_parameters_doesnt_depend_on_gvars vs pc_relation actor start_pc1 start_pc2 0 0 method_id frame_uniq
          parameter_var_ids parameter_values s21 s22;
        (match push_stack_parameters actor start_pc1 0 method_id frame_uniq parameter_var_ids parameter_values s21,
               push_stack_parameters actor start_pc2 0 method_id frame_uniq parameter_var_ids parameter_values s22 with
         | ComputationProduces s31, ComputationProduces s32 ->
             push_stack_variables_doesnt_depend_on_gvars vs pc_relation actor start_pc1 start_pc2
               (list_len parameter_var_ids) (list_len parameter_var_ids) method_id frame_uniq
               local_variable_initializers s31 s32
         | _, _ -> ())
  )

let statement_effect_independent_in_return_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (end_pc1: option pc_t)
  (end_pc2: option pc_t)
  (method_id: method_id_t)
  (bypassing_write_buffer: bool)
  (output_dsts: list expression_t)
  (output_srcs: list expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expressions vs output_dsts
                    /\ global_variables_unmentioned_in_expressions vs output_srcs
                    /\ (match end_pc1, end_pc2 with
                       | Some pc1, Some pc2 -> pc_relation.relation pc1 pc2 /\ pc_relation.return_relation pc1 pc2
                       | None, None -> True
                       | _, _ -> False))
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (return_statement_computation actor nd start_pc1 end_pc1 method_id bypassing_write_buffer
                        output_dsts output_srcs s1)
                      (return_statement_computation actor nd start_pc2 end_pc2 method_id bypassing_write_buffer
                        output_dsts output_srcs s2)) =
  let thread1 = s1.threads actor in
  let thread2 = s2.threads actor in
  if   Cons? nd
     || eqb thread1.stack []
     || thread1.top.method_id <> method_id
     || end_pc1 <> Some (Cons?.hd thread1.stack).return_pc then
    ()
  else (
    rvalues_computation_doesnt_depend_on_global_variables vs pc_relation output_srcs actor s1 s2;
    (match rvalues_computation output_srcs actor s1 with
     | ComputationImpossible | ComputationUndefined -> ()
     | ComputationProduces output_values ->
         pop_stack_variables_doesnt_depend_on_gvars vs actor method_id thread1.top.frame_uniq
           thread1.top.local_variables s1.mem s2.mem;
         (match pop_stack_variables actor method_id thread1.top.frame_uniq thread1.top.local_variables s1.mem,
                pop_stack_variables actor method_id thread2.top.frame_uniq thread2.top.local_variables s2.mem with
          | ComputationProduces mem1', ComputationProduces mem2' ->
              let s21 = pop_stack_frame actor mem1' s1 in
              let s22 = pop_stack_frame actor mem2' s2 in
              update_expressions_with_gvars_unaddressed_maintains_states_match vs pc_relation output_dsts actor
                start_pc1 start_pc2 0 0 bypassing_write_buffer output_values s21 s22
         | _, _ -> ()))
  )

let statement_effect_independent_in_terminate_thread_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (method_id: method_id_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (terminate_thread_statement_computation actor nd start_pc1 method_id s1)
                      (terminate_thread_statement_computation actor nd start_pc2 method_id s2)) =
  let thread1 = s1.threads actor in
  if neqb thread1.stack [] then
    ()
  else
    pop_stack_variables_doesnt_depend_on_gvars vs actor method_id thread1.top.frame_uniq
      thread1.top.local_variables s1.mem s2.mem

let statement_effect_independent_in_terminate_process_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (method_id: method_id_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (terminate_process_statement_computation actor nd start_pc1 method_id s1)
                      (terminate_process_statement_computation actor nd start_pc2 method_id s2)) =
  ()

let statement_effect_independent_in_join_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (join_tid: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs join_tid)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (join_statement_computation actor nd start_pc1 join_tid s1)
                      (join_statement_computation actor nd start_pc2 join_tid s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation join_tid actor s1 s2

#pop-options
#push-options "--z3rlimit 30"

let statement_effect_independent_in_alloc_successful_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (zero_initialized: bool)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (allocation_td: object_td_t)
  (count: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs result
                    /\ global_variables_unmentioned_in_expression vs count)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (alloc_successful_statement_computation actor nd start_pc1 zero_initialized
                         bypassing_write_buffer result allocation_td count s1)
                      (alloc_successful_statement_computation actor nd start_pc2 zero_initialized
                         bypassing_write_buffer result allocation_td count s2)) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract root_id_uniquifier_t)
     || neqb (expression_to_td count) (ObjectTDAbstract nat)
     || neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDPointer) then
    ()
  else (
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation count actor s1 s2;
    match rvalue_computation count actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces count_value ->
        let sz = ObjectValueAbstract?.value count_value in
        let array_td = ObjectTDArray allocation_td sz in
        let uniq = ObjectValueAbstract?.value (Cons?.hd nd) in
        let root_id = RootIdAllocation uniq in
        (match s1.mem root_id with
         | RootAllocated allocated freed storage ->
             if   allocated
                || freed
                || neqb (object_storage_to_td storage) array_td
                || not (is_storage_ready_for_allocation storage)
                || (not zero_initialized && not (object_storage_arbitrarily_initialized_correctly storage))
                || (zero_initialized && not (is_storage_zero_filled storage)) then
               ()
             else (
               if zero_initialized then (
                 assert (is_storage_zero_filled storage);
                 object_storage_zero_filled_doesnt_depend_on_gvars vs storage;
                 assert (global_variables_unaddressed_in_storage vs storage)
               )
               else (
                 assert (object_storage_arbitrarily_initialized_correctly storage);
                 object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs storage;
                 assert (global_variables_unaddressed_in_storage vs storage)
               );
               mark_allocation_root_allocated_doesnt_depend_on_gvars vs pc_relation uniq storage s1 s2;
               let s1' = mark_allocation_root_allocated uniq storage s1 in
               let s2' = mark_allocation_root_allocated uniq storage s2 in
               let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
               update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation result actor
                 start_pc1 start_pc2 0 0 bypassing_write_buffer p s1' s2'
             )
         | _ -> ())
  )

#pop-options
#push-options "--z3rlimit 20"

let statement_effect_independent_in_alloc_returning_null_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (count: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs result
                    /\ global_variables_unmentioned_in_expression vs count)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (alloc_returning_null_statement_computation actor nd start_pc1 bypassing_write_buffer
                         result count s1)
                      (alloc_returning_null_statement_computation actor nd start_pc2 bypassing_write_buffer
                         result count s2)) =
  rvalue_computation_doesnt_depend_on_global_variables vs pc_relation count actor s1 s2;
  match rvalue_computation count actor s1 with
  | ComputationImpossible | ComputationUndefined -> ()
  | ComputationProduces _ ->
      let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
      update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation result actor
        start_pc1 start_pc2 0 0 bypassing_write_buffer p s1 s2

let statement_effect_independent_in_dealloc_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (ptr: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs ptr)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (dealloc_statement_computation actor nd start_pc1 ptr s1)
                      (dealloc_statement_computation actor nd start_pc2 ptr s2)) =
  if   Cons? nd
     || neqb (expression_to_td ptr) (ObjectTDPrimitive PrimitiveTDPointer) then
    ()
  else (
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2;
    match rvalue_computation ptr actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces ptr_value ->
        free_pointer_doesnt_depend_on_gvars vs ptr_value s1.mem s2.mem
  )

let statement_effect_independent_in_somehow_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (ensures_cond: expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs undefined_unless_cond
                    /\ global_variables_unmentioned_in_expressions vs modifies_clauses
                    /\ expressions_lack_pointer_field modifies_clauses
                    /\ global_variables_unmentioned_in_expression vs ensures_cond
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (somehow_statement_computation actor nd start_pc1 undefined_unless_cond
                         bypassing_write_buffer modifies_clauses ensures_cond s1)
                      (somehow_statement_computation actor nd start_pc2 undefined_unless_cond
                         bypassing_write_buffer modifies_clauses ensures_cond s2)) =
  if   neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ()
  else (
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation undefined_unless_cond actor s1 s2;
    match rvalue_computation undefined_unless_cond actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces undefined_unless_value ->
        let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value undefined_unless_value) in
        if not undefined_unless_bool then
          ()
        else (
          update_expressions_lacking_pointer_field_maintains_states_match vs pc_relation modifies_clauses
            actor start_pc1 start_pc2 0 0 bypassing_write_buffer nd s1 s2;
          (match update_expressions modifies_clauses actor start_pc1 0 bypassing_write_buffer nd s1,
                 update_expressions modifies_clauses actor start_pc2 0 bypassing_write_buffer nd s2 with
           | ComputationProduces s1', ComputationProduces s2' ->
               rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ensures_cond actor s1' s2'
           | _, _ -> ())
        )
  )

let statement_effect_independent_in_fence_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (fence_statement_computation actor nd start_pc1 s1)
                      (fence_statement_computation actor nd start_pc2 s2)) =
  let root = s1.mem RootIdFence in
  match root_to_storage_computation root with
  | ComputationImpossible | ComputationUndefined -> ()
  | ComputationProduces storage ->
      if not (object_storage_up_to_date_for_rmw_operation storage actor) then
        ()
      else (
        let p = PointerRoot RootIdFence in
        assert (global_variables_unaddressed_in_object_value vs (ObjectValuePrimitive (PrimitiveBoxBool false)));
        assert (global_variables_unaddressed_in_pointer vs p);
        update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation
          p actor start_pc1 start_pc2 0 0 false (ObjectValuePrimitive (PrimitiveBoxBool false)) s1 s2
      )

let statement_effect_independent_in_external_method_start_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (await_cond: expression_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs await_cond
                    /\ global_variables_unmentioned_in_expression vs undefined_unless_cond
                    /\ global_variables_unmentioned_in_expressions vs modifies_clauses
                    /\ expressions_lack_pointer_field modifies_clauses
                    /\ global_variables_unmentioned_in_reads_clauses vs reads_clauses)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (external_method_start_statement_computation actor nd start_pc1 await_cond
                         undefined_unless_cond bypassing_write_buffer modifies_clauses reads_clauses s1)
                      (external_method_start_statement_computation actor nd start_pc2 await_cond
                         undefined_unless_cond bypassing_write_buffer modifies_clauses reads_clauses s2)) =
  if   neqb (expression_to_td await_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || list_len modifies_clauses <> list_len nd then
    ()
  else (
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation await_cond actor s1 s2;
    match rvalue_computation await_cond actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces await_value ->
        let await_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
        if not await_bool then
          ()
        else (
          rvalue_computation_doesnt_depend_on_global_variables vs pc_relation undefined_unless_cond actor s1 s2;
          match rvalue_computation undefined_unless_cond actor s1 with
          | ComputationImpossible | ComputationUndefined -> ()
          | ComputationProduces undefined_unless_value ->
              let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
              if not undefined_unless_bool then
                ()
              else (
                update_expressions_lacking_pointer_field_maintains_states_match vs pc_relation
                  modifies_clauses actor start_pc1 start_pc2 0 0 bypassing_write_buffer nd s1 s2;
                match update_expressions modifies_clauses actor start_pc1 0 bypassing_write_buffer nd s1,
                      update_expressions modifies_clauses actor start_pc2 0 bypassing_write_buffer nd s2 with
                | ComputationProduces s1', ComputationProduces s2' ->
                    external_method_take_snapshot_of_reads_clauses_computation_doesnt_depend_on_gvars
                      vs pc_relation actor start_pc1 start_pc2 (list_len modifies_clauses) (list_len modifies_clauses)
                      bypassing_write_buffer reads_clauses s1' s2'
                | _, _ -> ()
              )
        )
  )

let statement_effect_independent_in_external_method_middle_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expressions vs modifies_clauses
                    /\ expressions_lack_pointer_field modifies_clauses
                    /\ global_variables_unmentioned_in_reads_clauses vs reads_clauses)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (external_method_middle_statement_computation actor nd start_pc1
                         bypassing_write_buffer modifies_clauses reads_clauses s1)
                      (external_method_middle_statement_computation actor nd start_pc2
                         bypassing_write_buffer modifies_clauses reads_clauses s2)) =
  external_method_check_snapshot_computation_doesnt_depend_on_gvars vs pc_relation actor reads_clauses s1 s2;
  (match external_method_check_snapshot_computation actor reads_clauses s1 with
   | ComputationImpossible | ComputationUndefined -> ()
   | ComputationProduces _ ->
       update_expressions_lacking_pointer_field_maintains_states_match vs pc_relation modifies_clauses
         actor start_pc1 start_pc2 0 0 bypassing_write_buffer nd s1 s2;
       (match update_expressions modifies_clauses actor start_pc1 0 bypassing_write_buffer nd s1,
              update_expressions modifies_clauses actor start_pc2 0 bypassing_write_buffer nd s2 with
        | ComputationProduces s1_next, ComputationProduces s2_next ->
            external_method_take_snapshot_of_reads_clauses_computation_doesnt_depend_on_gvars vs pc_relation
              actor start_pc1 start_pc2 (list_len modifies_clauses) (list_len modifies_clauses)
              bypassing_write_buffer reads_clauses s1_next s2_next
        | _, _ -> ()))

let statement_effect_independent_in_external_method_end_statement_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (ensures_cond: expression_t)
  (logs_clauses: list expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2
                    /\ global_variables_unmentioned_in_expression vs ensures_cond
                    /\ global_variables_unmentioned_in_expressions vs logs_clauses)
          (ensures  statement_effect_independent_postconditions vs pc_relation
                      (external_method_end_statement_computation actor nd start_pc1 ensures_cond logs_clauses s1)
                      (external_method_end_statement_computation actor nd start_pc2 ensures_cond logs_clauses s2)) =
  if   Cons? nd
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ()
  else (
    rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ensures_cond actor s1 s2;
    match rvalue_computation ensures_cond actor s1 with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces ensures_value ->
        let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
        log_expressions_computation_doesnt_depend_on_gvars vs pc_relation actor logs_clauses s1 s2
  )

#pop-options
#push-options "--z3rlimit 30"

let statement_effect_independent_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (end_pc1: option pc_t)
  (end_pc2: option pc_t)
  (statement1: Armada.Statement.t)
  (statement2: Armada.Statement.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (* see .fsti file for spec *) =
  let cs1' = statement_computation actor nd start_pc1 end_pc1 statement1 s1 in
  let cs2' = statement_computation actor nd start_pc2 end_pc2 statement2 s2 in
  assert (statement_effect_independent_preconditions vs pc_relation actor start_pc1 start_pc2 s1 s2);
  (match statement1 with
   | AssumeExpressionStatement exp ->
       statement_effect_independent_in_assume_expression_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 exp s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | AssumePredicateStatement pred ->
       false_elim ();
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | AssertTrueStatement exp ->
       statement_effect_independent_in_assert_true_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 exp s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | AssertFalseStatement exp ->
       statement_effect_independent_in_assert_false_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 exp s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | ConditionalJumpStatement cond ->
       statement_effect_independent_in_conditional_jump_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 cond s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | UnconditionalJumpStatement ->
       statement_effect_independent_in_unconditional_jump_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2   s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | UpdateStatement bypassing_write_buffer dst src ->
       statement_effect_independent_in_update_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 bypassing_write_buffer dst src s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | NondeterministicUpdateStatement bypassing_write_buffer dst ->
       statement_effect_independent_in_nondeterministic_update_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 bypassing_write_buffer dst s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | PropagateWriteMessageStatement ->
       false_elim ();
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
       statement_effect_independent_in_compare_and_swap_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 target old_val new_val bypassing_write_buffer optional_result s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | AtomicExchangeStatement old_val target new_val ->
       statement_effect_independent_in_atomic_exchange_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 old_val target new_val s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                           parameter_expressions local_variable_initializers ->
       let initial_pc2 = (CreateThreadStatement?.initial_pc statement2) in
       statement_effect_independent_in_create_thread_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 method_id initial_pc initial_pc2 bypassing_write_buffer optional_result
         parameter_var_ids parameter_expressions local_variable_initializers s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                           stack_overflow ->
       let return_pc2 = (MethodCallStatement?.return_pc statement2) in
       statement_effect_independent_in_method_call_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 method_id return_pc return_pc2 parameter_var_ids parameter_expressions
         local_variable_initializers stack_overflow s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
       statement_effect_independent_in_return_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 end_pc1 end_pc2 method_id bypassing_write_buffer output_dsts output_srcs s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | TerminateThreadStatement method_id ->
       statement_effect_independent_in_terminate_thread_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 method_id s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | TerminateProcessStatement method_id ->
       statement_effect_independent_in_terminate_process_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 method_id s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | JoinStatement join_tid ->
       statement_effect_independent_in_join_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 join_tid s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
       statement_effect_independent_in_alloc_successful_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 false bypassing_write_buffer result allocation_td count s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | MallocReturningNullStatement bypassing_write_buffer result count ->
       statement_effect_independent_in_alloc_returning_null_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 bypassing_write_buffer result count s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
       statement_effect_independent_in_alloc_successful_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 true bypassing_write_buffer result allocation_td count s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | CallocReturningNullStatement bypassing_write_buffer result count ->
       statement_effect_independent_in_alloc_returning_null_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 bypassing_write_buffer result count s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | DeallocStatement ptr ->
       statement_effect_independent_in_dealloc_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 ptr s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
       statement_effect_independent_in_somehow_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | FenceStatement ->
       statement_effect_independent_in_fence_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer
                                  modifies_clauses reads_clauses ->
       statement_effect_independent_in_external_method_start_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 await_cond undefined_unless_cond bypassing_write_buffer
           modifies_clauses reads_clauses s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
       statement_effect_independent_in_external_method_middle_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 bypassing_write_buffer modifies_clauses reads_clauses s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
   | ExternalMethodEndStatement ensures_cond logs_clauses ->
       statement_effect_independent_in_external_method_end_statement_implications vs pc_relation actor nd
         start_pc1 start_pc2 ensures_cond logs_clauses s1 s2;
       assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
  );
  assert (statement_effect_independent_postconditions vs pc_relation cs1' cs2')
