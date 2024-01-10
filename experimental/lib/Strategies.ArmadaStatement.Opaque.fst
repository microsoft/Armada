module Strategies.ArmadaStatement.Opaque

open Armada.Base
open Armada.BinaryOp
open Armada.BoundedInt
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
open FStar.Sequence.Base
open FStar.Tactics.V2
open Spec.List
open Spec.Ubool
open Util.List

/// Opaque versions of complex functions called from statement definitions

[@"opaque_to_smt"]
let rvalue_computation_opaque = rvalue_computation

[@"opaque_to_smt"]
let rvalues_computation_opaque = rvalues_computation

[@"opaque_to_smt"]
let update_pointed_to_value_opaque = update_pointed_to_value

[@"opaque_to_smt"]
let update_expression_opaque = update_expression

[@"opaque_to_smt"]
let update_expressions_opaque = update_expressions

[@"opaque_to_smt"]
let propagate_write_message_opaque = propagate_write_message

[@"opaque_to_smt"]
let check_expression_up_to_date_for_rmw_opaque = check_expression_up_to_date_for_rmw

[@"opaque_to_smt"]
let push_stack_variables_opaque = push_stack_variables

[@"opaque_to_smt"]
let push_stack_parameters_opaque = push_stack_parameters

[@"opaque_to_smt"]
let pop_stack_variables_opaque = pop_stack_variables

[@"opaque_to_smt"]
let free_pointer_opaque = free_pointer

[@"opaque_to_smt"]
let external_method_take_snapshot_of_reads_clauses_computation_opaque =
  external_method_take_snapshot_of_reads_clauses_computation

[@"opaque_to_smt"]
let external_method_check_snapshot_computation_opaque = external_method_check_snapshot_computation

[@"opaque_to_smt"]
let log_expressions_computation_opaque = log_expressions_computation

[@"opaque_to_smt"]
let make_thread_running_opaque = make_thread_running

[@"opaque_to_smt"]
let push_stack_frame_opaque = push_stack_frame

[@"opaque_to_smt"]
let pop_stack_frame_opaque = pop_stack_frame

[@"opaque_to_smt"]
let mark_allocation_root_allocated_opaque = mark_allocation_root_allocated

/// Redacted versions of statement definitions that complex functions called from statement definitions

let assume_expression_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td exp) (ObjectTDAbstract bool) then
     ComputationImpossible
  else (
    let? value = rvalue_computation_opaque exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let assume_predicate_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (pred: Armada.State.t -> GTot bool)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || not (pred s) then
    ComputationImpossible
  else
    return s

let assert_true_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td exp) (ObjectTDAbstract bool) then
     ComputationImpossible
  else (
    let? value = rvalue_computation_opaque exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let assert_false_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td exp) (ObjectTDAbstract bool) then
     ComputationImpossible
  else (
    let? value = rvalue_computation_opaque exp actor s in
    if ObjectValueAbstract?.value value <> false then
      ComputationImpossible
    else
      let s' = { s with stop_reason = StopReasonAssertionFailure } in
      return s'
  )

let conditional_jump_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td exp) (ObjectTDAbstract bool) then
    ComputationImpossible
  else (
    let? value = rvalue_computation_opaque exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let unconditional_jump_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if Cons? nd then
    ComputationImpossible
  else
    return s
  
let update_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (src: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td dst) (expression_to_td src) then
    ComputationImpossible
  else (
    let? src_value = rvalue_computation_opaque src actor s in
    update_expression_opaque dst actor start_pc 0 bypassing_write_buffer src_value s
  )
  
let nondeterministic_update_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (expression_to_td dst) then
    ComputationImpossible
  else (
    let nd_value = Cons?.hd nd in
    if not (object_value_has_all_pointers_uninitialized nd_value) then
      ComputationImpossible
    else
      update_expression_opaque dst actor start_pc 0 bypassing_write_buffer nd_value s
  )

let propagate_write_message_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
    ComputationImpossible
  else
    let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    if receiver_tid = actor then // can't propagate to the same thread
      ComputationImpossible
    else
      let propagator_thread = s.threads actor in
      let receiver_thread = s.threads receiver_tid in
      let which_message = receiver_thread.position_in_other_write_buffers actor in
      if which_message >= length propagator_thread.write_buffer then
        ComputationImpossible
      else
        let write_message = index propagator_thread.write_buffer which_message in
        let position_in_other_write_buffers' =
          Spec.Map.upd receiver_thread.position_in_other_write_buffers actor (which_message + 1) in
        let receiver_thread' =
          { receiver_thread with position_in_other_write_buffers = position_in_other_write_buffers' } in
        let threads' = Spec.Map.upd s.threads receiver_tid receiver_thread' in
        match propagate_write_message_opaque write_message receiver_tid s.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            // If propagate would trigger undefined behavior (e.g., by propagating to freed memory),
            // it just leaves memory unchanged.
            return ({ s with threads = threads'; })
        | ComputationProduces mem' ->
            return ({ s with mem = mem'; threads = threads'; })

let compare_and_swap_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (target: expression_t)
  (old_val: expression_t)
  (new_val: expression_t)
  (bypassing_write_buffer: bool)
  (optional_result: option expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td target) (expression_to_td old_val)
     || neqb (expression_to_td target) (expression_to_td new_val)
     || (match optional_result with
        | Some result -> neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDBool)
        | None -> false) then
     ComputationImpossible
  else (
    let? _ = check_expression_up_to_date_for_rmw_opaque target actor s in
    let? old_value = rvalue_computation_opaque old_val actor s in
    let? target_value = rvalue_computation_opaque target actor s in
    let? new_value = rvalue_computation_opaque new_val actor s in
    let? target_ptr = lvalue_computation target actor s in
    let swap = eqb target_value old_value in
    let? s' = (if swap then update_pointed_to_value_opaque target_ptr actor start_pc 0 false new_value s else return s)
    in
    match optional_result with
    | None -> return s'
    | Some result ->
        // this line is deceptive, and we might be potentially bitten by it later
        // but it simplify the control flow
        let? result_ptr = lvalue_computation result actor s in
        let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
        update_pointed_to_value_opaque result_ptr actor start_pc 1 bypassing_write_buffer swap_value s'
  )

let atomic_exchange_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (old_val: expression_t)
  (target: expression_t)
  (new_val: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td target) (expression_to_td old_val)
     || neqb (expression_to_td target) (expression_to_td new_val) then
    ComputationImpossible
  else (
    // pre-update
    let? _ = check_expression_up_to_date_for_rmw_opaque target actor s in
    let? target_value = rvalue_computation_opaque target actor s in
    let? new_value = rvalue_computation_opaque new_val actor s in
    let? old_ptr = lvalue_computation old_val actor s in
    let? target_ptr = lvalue_computation target actor s in
    // post-update
    let? s' = update_pointed_to_value_opaque old_ptr actor start_pc 0 false target_value s in
    update_pointed_to_value_opaque target_ptr actor start_pc 1 false new_value s'
  )

let create_thread_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (initial_pc: pc_t)
  (bypassing_write_buffer: bool)
  (optional_result: option expression_t)
  (parameter_var_ids: list var_id_t)
  (parameter_expressions: list expression_t)
  (local_variable_initializers: list initializer_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // Nondeterminism must have exactly one element, of type create_thread_nd_t
  // If there is a target, then it must be of type thread ID
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract create_thread_nd_t)
     || (   Some? optional_result
        && neqb (expression_to_td (Some?.v optional_result)) (ObjectTDPrimitive PrimitiveTDThreadId))
     || list_len parameter_var_ids <> list_len parameter_expressions then
    ComputationImpossible
  else
    let create_thread_nd: create_thread_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let new_tid = create_thread_nd.new_tid in
    if new_tid = 0 then // thread creation failed, so just set the result to 0
      (match optional_result with
       | None -> return s
       | Some result ->
           let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
           update_expression_opaque result actor start_pc
              (list_len parameter_var_ids + list_len local_variable_initializers)
              bypassing_write_buffer new_tid_value s)
    else (
      let frame_uniq = create_thread_nd.frame_uniq in
      let new_thread = s.threads new_tid in
      if   new_thread.status <> ThreadStatusNotStarted
         || length new_thread.write_buffer <> 0
         || list_contains frame_uniq s.uniqs_used then
        ComputationImpossible
      else (
        // Evaluate parameter expressions
        let? parameter_values = rvalues_computation_opaque parameter_expressions actor s in
        // Set the new thread's parameters, and give it status "running".
        let s2 = make_thread_running_opaque method_id initial_pc new_tid frame_uniq s in
        // Initialize the input parameters on the stack of the new thread.
        // All input variables are assumed to be strongly consistent.
        let? s3 = push_stack_parameters_opaque new_tid start_pc 0 method_id frame_uniq parameter_var_ids
                    parameter_values s2 in
        // Initialize all remaining parameters on the stack of the new thread.
        let? s4 = push_stack_variables_opaque new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq
                    local_variable_initializers s3 in
        // Set the target to the new thread's thread ID, if there is a target
        (match optional_result with
         | None -> return s4
         | Some result ->
             let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
             update_expression_opaque result actor start_pc
               (list_len parameter_var_ids + list_len local_variable_initializers)
               bypassing_write_buffer new_tid_value s4)
    )
  )

let method_call_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (return_pc: pc_t)
  (parameter_var_ids: list var_id_t)
  (parameter_expressions: list expression_t)
  (local_variable_initializers: list initializer_t)
  (stack_overflow: bool)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // Nondeterminism must have exactly one element, of type method_call_nd_t
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract method_call_nd_t) then
    ComputationImpossible
  else
    let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let frame_uniq = method_call_nd.frame_uniq in
    if list_contains frame_uniq s.uniqs_used then
      ComputationImpossible
    else (
      // Evaluate parameter expressions on old stack, in case they reference local variables
      let? parameter_values = rvalues_computation_opaque parameter_expressions actor s in
      let s2 = push_stack_frame_opaque actor method_id return_pc frame_uniq s in
      // All input variables are assumed to be strongly consistent, so pass weakly_consistent=false
      let? s3 = push_stack_parameters_opaque actor start_pc 0 method_id frame_uniq parameter_var_ids
                  parameter_values s2 in
      let? s4 = push_stack_variables_opaque actor start_pc (list_len parameter_var_ids) method_id frame_uniq
                  local_variable_initializers s3 in
      if stack_overflow then
        return ({ s4 with stop_reason = StopReasonStackOverflow })
      else
        return s4
    )

let return_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (method_id: method_id_t)
  (bypassing_write_buffer: bool)
  (output_dsts: list expression_t)
  (output_srcs: list expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  let thread = s.threads actor in
  if   Cons? nd
     || eqb thread.stack []
     || thread.top.method_id <> method_id
     || end_pc <> Some (Cons?.hd thread.stack).return_pc then
    ComputationImpossible
  else (
    // First, evaluate output sources, before we pop the stack.
    let? output_values = rvalues_computation_opaque output_srcs actor s in
    // Second, free the stack variables and pop the stack.
    let? mem' = pop_stack_variables_opaque actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
    let s2 = pop_stack_frame_opaque actor mem' s in
    // Third, assign output values to output destinations.
    update_expressions_opaque output_dsts actor start_pc 0 bypassing_write_buffer output_values s2
  )

let terminate_thread_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  let thread = s.threads actor in
  if   Cons? nd
     || neqb thread.stack []
     || thread.top.method_id <> method_id
     || actor = s.initial_tid then // returning from main in the initial thread terminates the process, not the thread
    ComputationImpossible
  else (
    // Otherwise, mark thread as joinable and free all stack variables
    let? mem' = pop_stack_variables_opaque actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
    let thread' = { thread with status = ThreadStatusJoinable } in
    let threads' = Spec.Map.upd s.threads actor thread' in
    let s' = { s with mem = mem'; threads = threads' } in
    return s'
  )

let terminate_process_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  let thread = s.threads actor in
  if   Cons? nd
     || neqb thread.stack []
     || thread.top.method_id <> method_id
     || actor <> s.initial_tid then // the process is terminated by having the initial thread terminate
    ComputationImpossible
  else
    let s' = { s with stop_reason = StopReasonTerminated } in
    return s'

let join_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (join_tid: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td join_tid) (ObjectTDPrimitive PrimitiveTDThreadId) then
    ComputationImpossible
  else (
    let? tid_value = rvalue_computation_opaque join_tid actor s in
    let other_tid = PrimitiveBoxThreadId?.tid (ObjectValuePrimitive?.value tid_value) in
    let thread = s.threads other_tid in
    match thread.status with
    | ThreadStatusNotStarted -> ComputationImpossible // can't get a handle to a non-started thread
    | ThreadStatusRunning -> ComputationImpossible    // not possible since join would block
    | ThreadStatusPostJoin -> ComputationUndefined    // not defined to join a thread twice
    | ThreadStatusJoinable ->
        let thread' = { thread with status = ThreadStatusPostJoin } in
        let threads' = Spec.Map.upd s.threads other_tid thread' in
        let s' = { s with threads = threads' } in
        return s'
  )

let alloc_successful_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (zero_initialized: bool)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (allocation_td: object_td_t)
  (count: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // There should be one non-determinism parameter, the root ID uniquifier.
  // The result destination should be of type pointer.
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract root_id_uniquifier_t)
     || neqb (expression_to_td count) (ObjectTDAbstract nat)
     || neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDPointer) then
    ComputationImpossible
  else (
    let? count_value = rvalue_computation_opaque count actor s in
    let sz = ObjectValueAbstract?.value count_value in
    let array_td = ObjectTDArray allocation_td sz in
    let uniq = ObjectValueAbstract?.value (Cons?.hd nd) in
    let root_id = RootIdAllocation uniq in
    match s.mem root_id with
    | RootAllocated allocated freed storage ->
        if   allocated
           || freed
           || neqb (object_storage_to_td storage) array_td
           || not (is_storage_ready_for_allocation storage)
           || (not zero_initialized && not (object_storage_arbitrarily_initialized_correctly storage))
           || (zero_initialized && not (is_storage_zero_filled storage)) then
          ComputationImpossible
        else
          // update memory by marking root as allocated
          let s' = mark_allocation_root_allocated_opaque uniq storage s in
          // store the pointer to the first element of the newly allocated array in result
          let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
          update_expression_opaque result actor start_pc 0 bypassing_write_buffer p s'
    | _ -> ComputationImpossible
  )

let alloc_returning_null_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (count: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td count) (ObjectTDAbstract nat)
     || neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDPointer) then
    ComputationImpossible
  else (
    let? _ = rvalue_computation_opaque count actor s in
    let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
    update_expression_opaque result actor start_pc 0 bypassing_write_buffer p s
  )

let dealloc_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (ptr: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td ptr) (ObjectTDPrimitive PrimitiveTDPointer) then
    ComputationImpossible
  else (
    let? ptr_value = rvalue_computation_opaque ptr actor s in
    let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
    let? mem' = free_pointer_opaque p s.mem in
    let s' = { s with mem = mem' } in
    return s'
  )

let somehow_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (ensures_cond: expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // The non-determinism can be any length, since it's the set of modified objects.
  if   neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ComputationImpossible
  else (
    // Exhibit undefined behavior unless the undefined_unless condition holds
    let? undefined_unless_value = rvalue_computation_opaque undefined_unless_cond actor s in
    let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value undefined_unless_value) in
    if not undefined_unless_bool then
      ComputationUndefined
    else (
      // Update each element of the modifies clauses using the nondeterminism to supply modified values
      let? s' = update_expressions_opaque modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
      // Assume the ensures clause holds
      let? ensures_value = rvalue_computation_opaque ensures_cond actor s' in
      let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
      if not ensures_bool then
        ComputationImpossible
      else
        return s'
    )
  )

let fence_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if Cons? nd then
    ComputationImpossible
  else (
    let root = s.mem RootIdFence in
    let? storage = root_to_storage_computation root in
    if not (object_storage_up_to_date_for_rmw_operation storage actor) then
      ComputationImpossible
    else
      let p = PointerRoot RootIdFence in
      update_pointed_to_value_opaque p actor start_pc 0 false (ObjectValuePrimitive (PrimitiveBoxBool false)) s
  )

let external_method_take_snapshot_of_reads_clauses_computation_redacted
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t)
    (decreases reads_clauses) =
  match reads_clauses with
  | [] -> return s
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      let? first_value = rvalue_computation_opaque first_reads_expression actor s in
      let td = expression_to_td first_reads_expression in
      let local_var = ExpressionLocalVariable td first_var_id in
      let? s' = update_expression_opaque local_var actor writer_pc writer_expression_number bypassing_write_buffer
                  first_value s in
      external_method_take_snapshot_of_reads_clauses_computation_opaque actor writer_pc (writer_expression_number + 1)
        bypassing_write_buffer remaining_reads_clauses s'

let external_method_start_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (await_cond: expression_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // The nondeterminism should be a list of all the values to write into the write set
  if   neqb (expression_to_td await_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || list_len modifies_clauses <> list_len nd then
    ComputationImpossible
  else (
    // First, wait for all the awaits clauses to hold.
    let? await_value = rvalue_computation_opaque await_cond actor s in
    let await_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
    if not await_bool then
      ComputationImpossible
    else (
      // Second, manifest undefined behavior if the undefined_unless clauses don't all hold.
      let? undefined_unless_value = rvalue_computation_opaque undefined_unless_cond actor s in
      let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
      if not undefined_unless_bool then
        ComputationUndefined
      else (
        // Third, havoc the write set, using the nondeterminism to supply the new values.
        let? s2 = update_expressions_opaque modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
        // Fourth, capture the read set into local stack variables, starting with variable 0.
        external_method_take_snapshot_of_reads_clauses_computation_opaque actor start_pc (list_len modifies_clauses)
          bypassing_write_buffer reads_clauses s2
      )
    )
  )

let external_method_middle_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  // The nondeterminism should be a list of all the values to write into the write set
  // First, manifest undefined behavior if the reads clauses don't match the snapshot on the stack,
  // starting with variable 0.
  let? _ = external_method_check_snapshot_computation_opaque actor reads_clauses s in
  // Second, havoc the write set, using the nondeterminism `nd` to supply the new values.
  let? s2 = update_expressions_opaque modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
  // Third, capture the read set into local stack variables, starting with variable 0.
  external_method_take_snapshot_of_reads_clauses_computation_opaque actor start_pc (list_len modifies_clauses)
    bypassing_write_buffer reads_clauses s2

let external_method_end_statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (ensures_cond: expression_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   Cons? nd
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ComputationImpossible
  else (
    let? ensures_value = rvalue_computation_opaque ensures_cond actor s in
    let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
    if not ensures_bool then
      ComputationImpossible
    else
      log_expressions_computation_opaque actor logs_clauses s
  )

let statement_computation_redacted
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  match statement with
  | AssumeExpressionStatement exp ->
      assume_expression_statement_computation_redacted actor nd start_pc exp s
  | AssumePredicateStatement pred ->
      assume_predicate_statement_computation_redacted actor nd start_pc pred s
  | AssertTrueStatement exp ->
      assert_true_statement_computation_redacted actor nd start_pc exp s
  | AssertFalseStatement exp ->
      assert_false_statement_computation_redacted actor nd start_pc exp s
  | ConditionalJumpStatement cond ->
      conditional_jump_statement_computation_redacted actor nd start_pc cond s
  | UnconditionalJumpStatement ->
      unconditional_jump_statement_computation_redacted actor nd start_pc s
  | UpdateStatement bypassing_write_buffer dst src ->
      update_statement_computation_redacted actor nd start_pc bypassing_write_buffer dst src s
  | NondeterministicUpdateStatement bypassing_write_buffer dst ->
      nondeterministic_update_statement_computation_redacted actor nd start_pc bypassing_write_buffer dst s
  | PropagateWriteMessageStatement ->
      propagate_write_message_statement_computation_redacted actor nd s
  | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
      compare_and_swap_statement_computation_redacted actor nd start_pc target old_val new_val
        bypassing_write_buffer optional_result s
  | AtomicExchangeStatement old_val target new_val ->
      atomic_exchange_statement_computation_redacted actor nd start_pc old_val target new_val s
  | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                          parameter_expressions local_variable_initializers ->
      create_thread_statement_computation_redacted actor nd start_pc method_id initial_pc bypassing_write_buffer
        optional_result parameter_var_ids parameter_expressions local_variable_initializers s
  | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                          stack_overflow ->
      method_call_statement_computation_redacted actor nd start_pc method_id return_pc parameter_var_ids
        parameter_expressions local_variable_initializers stack_overflow s
  | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
      return_statement_computation_redacted actor nd start_pc end_pc method_id bypassing_write_buffer output_dsts
        output_srcs s
  | TerminateThreadStatement method_id ->
      terminate_thread_statement_computation_redacted actor nd start_pc method_id s
  | TerminateProcessStatement method_id ->
      terminate_process_statement_computation_redacted actor nd start_pc method_id s
  | JoinStatement join_tid ->
      join_statement_computation_redacted actor nd start_pc join_tid s
  | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_computation_redacted actor nd start_pc false bypassing_write_buffer result
        allocation_td count s
  | MallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_computation_redacted actor nd start_pc bypassing_write_buffer result count s
  | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_computation_redacted actor nd start_pc true bypassing_write_buffer result
        allocation_td count s
  | CallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_computation_redacted actor nd start_pc bypassing_write_buffer result count s
  | DeallocStatement ptr ->
      dealloc_statement_computation_redacted actor nd start_pc ptr s
  | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
      somehow_statement_computation_redacted actor nd start_pc undefined_unless_cond
        bypassing_write_buffer modifies_clauses ensures_cond s
  | FenceStatement ->
      fence_statement_computation_redacted actor nd start_pc s
  | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer
                                 modifies_clauses reads_clauses ->
      external_method_start_statement_computation_redacted actor nd start_pc await_cond undefined_unless_cond
        bypassing_write_buffer modifies_clauses reads_clauses s
  | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
      external_method_middle_statement_computation_redacted actor nd start_pc bypassing_write_buffer modifies_clauses
        reads_clauses s
  | ExternalMethodEndStatement ensures_cond logs_clauses ->
      external_method_end_statement_computation_redacted actor nd start_pc ensures_cond logs_clauses s

/// Proofs that redacted versions are equivalent to unredacted versions

let statement_computation_redacted_equivalent ()
  : Lemma (statement_computation_redacted == statement_computation) =
  assert (assume_expression_statement_computation_redacted == assume_expression_statement_computation) by trefl();
  assert (assume_predicate_statement_computation_redacted == assume_predicate_statement_computation) by trefl();
  assert (assert_true_statement_computation_redacted == assert_true_statement_computation) by trefl();
  assert (assert_false_statement_computation_redacted == assert_false_statement_computation) by trefl();
  assert (conditional_jump_statement_computation_redacted == conditional_jump_statement_computation) by trefl();
  assert (unconditional_jump_statement_computation_redacted == unconditional_jump_statement_computation) by trefl();
  assert (update_statement_computation_redacted == update_statement_computation) by trefl();
  assert (nondeterministic_update_statement_computation_redacted == nondeterministic_update_statement_computation)
    by trefl();
  assert (propagate_write_message_statement_computation_redacted == propagate_write_message_statement_computation)
    by trefl();
  assert (compare_and_swap_statement_computation_redacted == compare_and_swap_statement_computation) by trefl();
  assert (atomic_exchange_statement_computation_redacted == atomic_exchange_statement_computation) by trefl();
  assert (create_thread_statement_computation_redacted == create_thread_statement_computation) by trefl();
  assert (method_call_statement_computation_redacted == method_call_statement_computation) by trefl();
  assert (return_statement_computation_redacted == return_statement_computation) by trefl();
  assert (terminate_thread_statement_computation_redacted == terminate_thread_statement_computation) by trefl();
  assert (terminate_process_statement_computation_redacted == terminate_process_statement_computation) by trefl();
  assert (join_statement_computation_redacted == join_statement_computation) by trefl();
  assert (alloc_successful_statement_computation_redacted == alloc_successful_statement_computation) by trefl();
  assert (alloc_returning_null_statement_computation_redacted == alloc_returning_null_statement_computation)
    by trefl();
  assert (dealloc_statement_computation_redacted == dealloc_statement_computation) by trefl();
  assert (somehow_statement_computation_redacted == somehow_statement_computation) by trefl();
  assert (fence_statement_computation_redacted == fence_statement_computation) by trefl();
  assert (external_method_take_snapshot_of_reads_clauses_computation_redacted ==
          external_method_take_snapshot_of_reads_clauses_computation) by trefl();
  assert (external_method_start_statement_computation_redacted == external_method_start_statement_computation)
    by trefl();
  assert (external_method_middle_statement_computation_redacted == external_method_middle_statement_computation)
    by trefl();
  assert (external_method_end_statement_computation_redacted == external_method_end_statement_computation) by trefl();
  assert (statement_computation_redacted == statement_computation) by trefl()
