module Armada.Statement

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Thread
open Armada.Threads
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Map
open Spec.Ubool

noeq type t =
  | AssumeExpressionStatement: (exp: expression_t) -> t
  | AssumePredicateStatement: (pred: Armada.State.t -> GTot bool) -> t
  | AssertTrueStatement: (exp: expression_t) -> t
  | AssertFalseStatement: (exp: expression_t) -> t
  | ConditionalJumpStatement: (cond: expression_t) -> t // if or while
  | UnconditionalJumpStatement: t // skip, jump past else, jump back to loop head, break, continue, goto, if *, while *
  | UpdateStatement: (bypassing_write_buffer: bool) -> // whether ::= is used
                     (dst: expression_t) -> (src: expression_t) -> t
  | NondeterministicUpdateStatement: (bypassing_write_buffer: bool) -> // whether ::= is used
                                     (dst: expression_t) -> t
  | PropagateWriteMessageStatement: t
  | CompareAndSwapStatement: (target: expression_t) ->  // the location to compare to and possibly store into
                             (old_val: expression_t) -> // the value to compare the current value to
                             (new_val: expression_t) -> // the value to swap in if the equality comparison succeeds
                             (bypassing_write_buffer: bool) -> // whether ::= is used for assigning optional_result
                             (optional_result: option expression_t) -> t // where to write the boolean "did swap happen?"
  | AtomicExchangeStatement: (old_val: expression_t) -> // where the old value of target will be put
                             (target: expression_t) ->  // where the new value should be assigned to 
                             (new_val: expression_t) -> t // the new value
                             // e.g., x := atomic_exchange(y, 3) has old_val x, target y, and new_val 3,
                             // and means to atomically set x := y then y := 3
  | CreateThreadStatement: (method_id: method_id_t) ->
                           (initial_pc: pc_t) ->              // initial PC of created thread
                           (bypassing_write_buffer: bool) ->  // whether ::= is used for assigning the new thread ID
                           (optional_result: option expression_t) -> // where the resulting thread ID should be
                                                                    // written (optional)
                           (parameter_var_ids: list var_id_t) ->  // local variables to store parameters
                                                                 // (assumed strongly consistent)
                           (parameter_expressions: list expression_t) -> // expressions to be stored as parameters
                           (local_variable_initializers: list initializer_t) ->  t
  | MethodCallStatement: (method_id: method_id_t) ->
                         (return_pc: pc_t) ->
                         (parameter_var_ids: list var_id_t) -> // local variables to store parameters
                                                              // (assumed strongly consistent)
                         (parameter_expressions: list expression_t) -> // expressions to be stored as parameters
                         (local_variable_initializers: list initializer_t) ->
                            // If this is an external method, there should be one local variable initializer for
                            // each reads clause. The types of these initializers should match the types of those
                            // reads clauses, in order. So, for instance if it has "reads p[3], x" and the types of
                            // p[3] and x are t1 and t2, then the local variable initializers should be a list
                            // whose first element is an initializer with type t1 and whose second element is
                            // an initializer of type t2.
                         (stack_overflow: bool) -> t
  | ReturnStatement: (method_id: method_id_t) ->
                     (bypassing_write_buffer: bool) ->   // whether ::= is used for assigning output variables
                     (output_dsts: list expression_t) ->
                     (output_srcs: list expression_t) -> // output sources to be evaluated before popping the stack;
                                                        // generally, each of these will be an ExpressionLocalVariable
                                                        // corresponding to an output stack variable
                     t
  | TerminateThreadStatement: (method_id: method_id_t) -> t  // top-level method being returned from
  | TerminateProcessStatement: (method_id: method_id_t) -> t // main method ID being returned from
  | JoinStatement: (join_tid: expression_t) -> t // in concrete levels, this expression shouldn't read shared state
  | MallocSuccessfulStatement: (bypassing_write_buffer: bool) -> // whether ::= is used to write the resulting pointer
                               (result: expression_t) ->         // where the resulting pointer is written
                               (allocation_td: object_td_t) ->   // type being allocated
                               (count: expression_t) ->          // count must be a nat
                               t
  | MallocReturningNullStatement: (bypassing_write_buffer: bool) -> (result: expression_t) -> (count: expression_t) -> t
  | CallocSuccessfulStatement: (bypassing_write_buffer: bool) -> (result: expression_t) -> // result must be a pointer
                               (allocation_td: object_td_t) -> (count: expression_t) ->    // count must be a nat
                               t
  | CallocReturningNullStatement: (bypassing_write_buffer: bool) ->
                                  (result: expression_t) -> // result must be a pointer
                                  (count: expression_t) ->  // count must be a nat
                                  t
  | DeallocStatement: (ptr: expression_t) -> t
  | SomehowStatement: (undefined_unless_cond: expression_t) -> // undefined_unless conditions combined with &&
                      (bypassing_write_buffer: bool) ->        // whether updates to modifies clauses
                                                              //   bypass write buffers
                      (modifies_clauses: list expression_t) ->
                      (ensures_cond: expression_t) ->          // ensures conditions combined with &&
                      t
  | FenceStatement: t
  | ExternalMethodStartStatement: (await_cond: expression_t) ->            // awaits conditions combined with &&
                                  (undefined_unless_cond: expression_t) -> // undefined_unless conditions
                                                                          //   combined with &&
                                  (bypassing_write_buffer: bool) ->        // whether havocs of modifies clauses
                                                                          //   bypass write buffer
                                  (modifies_clauses: list expression_t) -> // modifies clauses to havoc
                                  (reads_clauses: list (var_id_t * expression_t)) -> // reads clauses to snapshot
                                  t
  | ExternalMethodMiddleStatement: (bypassing_write_buffer: bool) ->        // whether havocs of modifies clauses
                                                                           //   bypass write buffer
                                   (modifies_clauses: list expression_t) -> // modifies clauses to havoc
                                   (reads_clauses: list (var_id_t * expression_t)) -> // reads clauses to snapshot
                                   t
  | ExternalMethodEndStatement: (ensures_cond: expression_t) ->             // ensures clauses combined with &&
                                (logs_clauses: list expression_t) ->        // values to be appended to
                                                                           //   external-event trace
                                t

let assume_expression_statement_computation
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
    let? value = rvalue_computation exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let assume_predicate_statement_computation
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

let assert_true_statement_computation
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
    let? value = rvalue_computation exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let assert_false_statement_computation
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
    let? value = rvalue_computation exp actor s in
    if ObjectValueAbstract?.value value <> false then
      ComputationImpossible
    else
      let s' = { s with stop_reason = StopReasonAssertionFailure } in
      return s'
  )

let conditional_jump_statement_computation
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
    let? value = rvalue_computation exp actor s in
    if ObjectValueAbstract?.value value <> true then
      ComputationImpossible
    else
      return s
  )

let unconditional_jump_statement_computation
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if Cons? nd then
    ComputationImpossible
  else
    return s

let update_statement_computation
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
    let? src_value = rvalue_computation src actor s in
    update_expression dst actor start_pc 0 bypassing_write_buffer src_value s
  )

let nondeterministic_update_statement_computation
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
      update_expression dst actor start_pc 0 bypassing_write_buffer nd_value s
  )

let propagate_write_message_statement_computation
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
        match propagate_write_message write_message receiver_tid s.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            // If propagate would trigger undefined behavior (e.g., by propagating to freed memory),
            // it just leaves memory unchanged.
            return ({ s with threads = threads'; })
        | ComputationProduces mem' ->
            return ({ s with mem = mem'; threads = threads'; })

let compare_and_swap_statement_computation
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
    let? _ = check_expression_up_to_date_for_rmw target actor s in
    let? old_value = rvalue_computation old_val actor s in
    let? target_value = rvalue_computation target actor s in
    let? new_value = rvalue_computation new_val actor s in
    let? target_ptr = lvalue_computation target actor s in
    let swap = eqb target_value old_value in
    let? s' = (if swap then update_pointed_to_value target_ptr actor start_pc 0 false new_value s else return s) in
    match optional_result with
    | None -> return s'
    | Some result ->
        // this line is deceptive, and we might be potentially bitten by it later
        // but it simplify the control flow
        let? result_ptr = lvalue_computation result actor s in
        let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
        update_pointed_to_value result_ptr actor start_pc 1 bypassing_write_buffer swap_value s'
  )

let atomic_exchange_statement_computation
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
    let? _ = check_expression_up_to_date_for_rmw target actor s in
    let? target_value = rvalue_computation target actor s in
    let? new_value = rvalue_computation new_val actor s in
    let? old_ptr = lvalue_computation old_val actor s in
    let? target_ptr = lvalue_computation target actor s in
    // post-update
    let? s' = update_pointed_to_value old_ptr actor start_pc 0 false target_value s in
    update_pointed_to_value target_ptr actor start_pc 1 false new_value s'
  )

type create_thread_nd_t = {
  new_tid: tid_t;
  frame_uniq: root_id_uniquifier_t;
}

let make_thread_running
  (method_id: method_id_t)
  (initial_pc: pc_t)
  (new_tid: tid_t)
  (frame_uniq: root_id_uniquifier_t)
  (s: Armada.State.t)
  : GTot Armada.State.t =
  let thread = s.threads new_tid in
  let thread' =
    { thread with
      status = ThreadStatusRunning;
      pc = initial_pc;
      top = { method_id = method_id; frame_uniq = frame_uniq; local_variables = [] };
      stack = []; } in
  let threads' = upd s.threads new_tid thread' in
  { s with threads = threads'; uniqs_used = frame_uniq :: s.uniqs_used }

let create_thread_statement_computation
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
  else (
    let create_thread_nd: create_thread_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let new_tid = create_thread_nd.new_tid in
    if new_tid = 0 then // thread creation failed, so just set the result to 0
      (match optional_result with
       | None -> return s
       | Some result ->
           let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
           update_expression result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers)
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
        let? parameter_values = rvalues_computation parameter_expressions actor s in
        // Set the new thread's parameters, and give it status "running".
        let s2 = make_thread_running method_id initial_pc new_tid frame_uniq s in
        // Initialize the input parameters on the stack of the new thread.
        // All input variables are assumed to be strongly consistent.
        let? s3 = push_stack_parameters new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2 in
        // Initialize all remaining parameters on the stack of the new thread.
        let? s4 = push_stack_variables new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq
                    local_variable_initializers s3 in
        // Set the target to the new thread's thread ID, if there is a target
        (match optional_result with
         | None -> return s4
         | Some result ->
             let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
             update_expression result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers)
               bypassing_write_buffer new_tid_value s4)
      )
    )
  )

type method_call_nd_t = {
  frame_uniq: root_id_uniquifier_t;
}

let push_stack_frame
  (actor: tid_t)
  (method_id: method_id_t)
  (return_pc: pc_t)
  (frame_uniq: root_id_uniquifier_t)
  (s: Armada.State.t)
  : GTot Armada.State.t =
  let thread = s.threads actor in
  let extended_stack_frame' = { return_pc = return_pc; frame = thread.top } in
  let stack' = extended_stack_frame' :: thread.stack in
  let top' = { method_id = method_id; frame_uniq = frame_uniq; local_variables = [] } in
  let thread' = { thread with top = top'; stack = stack' } in
  let threads' = upd s.threads actor thread' in
  { s with threads = threads'; uniqs_used = frame_uniq :: s.uniqs_used }

let method_call_statement_computation
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
  else (
    let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let frame_uniq = method_call_nd.frame_uniq in
    if list_contains frame_uniq s.uniqs_used then
      ComputationImpossible
    else (
      // Evaluate parameter expressions on old stack, in case they reference local variables
      let? parameter_values = rvalues_computation parameter_expressions actor s in
      let s2 = push_stack_frame actor method_id return_pc frame_uniq s in
      // All input variables are assumed to be strongly consistent, so pass weakly_consistent=false
      let? s3 = push_stack_parameters actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2 in
      let? s4 = push_stack_variables actor start_pc (list_len parameter_var_ids) method_id frame_uniq
                  local_variable_initializers s3 in
      if stack_overflow then
        return ({ s4 with stop_reason = StopReasonStackOverflow })
      else
        return s4
    )
  )

let pop_stack_frame
  (actor: tid_t)
  (mem': Armada.Memory.t)
  (s: Armada.State.t{Cons? (s.threads actor).stack})
  : GTot Armada.State.t =
  let thread = s.threads actor in
  let stack' = Cons?.tl thread.stack in
  let top' = (Cons?.hd thread.stack).frame in
  let thread' = { thread with top = top'; stack = stack' } in
  let threads' = Spec.Map.upd s.threads actor thread' in
  { s with mem = mem'; threads = threads' }

let return_statement_computation
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
    let? output_values = rvalues_computation output_srcs actor s in
    // Second, free the stack variables and pop the stack.
    let? mem' = pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
    let s2 = pop_stack_frame actor mem' s in
    // Third, assign output values to output destinations.
    update_expressions output_dsts actor start_pc 0 bypassing_write_buffer output_values s2
  )

let terminate_thread_statement_computation
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
    let? mem' = pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
    let thread' = { thread with status = ThreadStatusJoinable } in
    let threads' = Spec.Map.upd s.threads actor thread' in
    let s' = { s with mem = mem'; threads = threads' } in
    return s'
  )

let terminate_process_statement_computation
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

let join_statement_computation
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
    let? tid_value = rvalue_computation join_tid actor s in
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

let mark_allocation_root_allocated
  (uniq: root_id_uniquifier_t)
  (storage: valid_object_storage_t)
  (s: Armada.State.t)
  : GTot Armada.State.t =
  let root' = RootAllocated true false storage in
  let mem' = Spec.Map.upd s.mem (RootIdAllocation uniq) root' in
  { s with mem = mem' }

let alloc_successful_statement_computation
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
    let? count_value = rvalue_computation count actor s in
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
          let s' = mark_allocation_root_allocated uniq storage s in
          // store the pointer to the first element of the newly allocated array in result
          let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
          update_expression result actor start_pc 0 bypassing_write_buffer p s'
    | _ -> ComputationImpossible
  )

let alloc_returning_null_statement_computation
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
    let? _ = rvalue_computation count actor s in
    let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
    update_expression result actor start_pc 0 bypassing_write_buffer p s
  )

let dealloc_statement_computation
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
    let? ptr_value = rvalue_computation ptr actor s in
    let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
    let? mem' = free_pointer p s.mem in
    let s' = { s with mem = mem' } in
    return s'
  )

let somehow_statement_computation
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
    let? undefined_unless_value = rvalue_computation undefined_unless_cond actor s in
    let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value undefined_unless_value) in
    if not undefined_unless_bool then
      ComputationUndefined
    else (
      // Update each element of the modifies clauses using the nondeterminism to supply modified values
      let? s' = update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
      // Assume the ensures clause holds
      let? ensures_value = rvalue_computation ensures_cond actor s' in
      let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
      if not ensures_bool then
        ComputationImpossible
      else
        return s'
    )
  )

let fence_statement_computation
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
      update_pointed_to_value p actor start_pc 0 false (ObjectValuePrimitive (PrimitiveBoxBool false)) s
  )

let rec external_method_take_snapshot_of_reads_clauses_computation
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
      let? first_value = rvalue_computation first_reads_expression actor s in
      let td = expression_to_td first_reads_expression in
      let local_var = ExpressionLocalVariable td first_var_id in
      let? s' = update_expression local_var actor writer_pc writer_expression_number bypassing_write_buffer
                  first_value s in
      external_method_take_snapshot_of_reads_clauses_computation actor writer_pc (writer_expression_number + 1)
        bypassing_write_buffer remaining_reads_clauses s'

let external_method_start_statement_computation
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
    let? await_value = rvalue_computation await_cond actor s in
    let await_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
    if not await_bool then
      ComputationImpossible
    else (
      // Second, manifest undefined behavior if the undefined_unless clauses don't all hold.
      let? undefined_unless_value = rvalue_computation undefined_unless_cond actor s in
      let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
      if not undefined_unless_bool then
        ComputationUndefined
      else (
        // Third, havoc the write set, using the nondeterminism to supply the new values.
        let? s2 = update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
        // Fourth, capture the read set into local stack variables, starting with variable 0.
        external_method_take_snapshot_of_reads_clauses_computation actor start_pc (list_len modifies_clauses)
          bypassing_write_buffer reads_clauses s2
      )
    )
  )

let rec external_method_check_snapshot_computation
  (actor: tid_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : GTot (conditional_computation_t unit) =
  match reads_clauses with
  | [] -> return ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      let? first_value = rvalue_computation first_reads_expression actor s in
      let td = expression_to_td first_reads_expression in
      let local_var = ExpressionLocalVariable td first_var_id in
      let? snapshot_value = rvalue_computation local_var actor s in
      if neqb first_value snapshot_value then
        ComputationUndefined
      else
        external_method_check_snapshot_computation actor remaining_reads_clauses s

let external_method_middle_statement_computation
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
  let? _ = external_method_check_snapshot_computation actor reads_clauses s in
  // Second, havoc the write set, using the nondeterminism `nd` to supply the new values.
  let? s2 = update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer nd s in
  // Third, capture the read set into local stack variables, starting with variable 0.
  external_method_take_snapshot_of_reads_clauses_computation actor start_pc (list_len modifies_clauses)
    bypassing_write_buffer reads_clauses s2

let rec log_expressions_computation
  (actor: tid_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  match logs_clauses with
  | [] -> return s
  | first_logs_clause :: remaining_logs_clauses ->
      let? event = rvalue_computation first_logs_clause actor s in
      let trace' = s.trace $:: event in
      let s' = { s with trace = trace' } in
      log_expressions_computation actor remaining_logs_clauses s'

let external_method_end_statement_computation
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
    let? ensures_value = rvalue_computation ensures_cond actor s in
    let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
    if not ensures_bool then
      ComputationImpossible
    else
      log_expressions_computation actor logs_clauses s
  )

let statement_computation
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  match statement with
  | AssumeExpressionStatement exp ->
      assume_expression_statement_computation actor nd start_pc exp s
  | AssumePredicateStatement pred ->
      assume_predicate_statement_computation actor nd start_pc pred s
  | AssertTrueStatement exp ->
      assert_true_statement_computation actor nd start_pc exp s
  | AssertFalseStatement exp ->
      assert_false_statement_computation actor nd start_pc exp s
  | ConditionalJumpStatement cond ->
      conditional_jump_statement_computation actor nd start_pc cond s
  | UnconditionalJumpStatement ->
      unconditional_jump_statement_computation actor nd start_pc s
  | UpdateStatement bypassing_write_buffer dst src ->
      update_statement_computation actor nd start_pc bypassing_write_buffer dst src s
  | NondeterministicUpdateStatement bypassing_write_buffer dst ->
      nondeterministic_update_statement_computation actor nd start_pc bypassing_write_buffer dst s
  | PropagateWriteMessageStatement ->
      propagate_write_message_statement_computation actor nd s
  | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
      compare_and_swap_statement_computation actor nd start_pc target old_val new_val bypassing_write_buffer
        optional_result s
  | AtomicExchangeStatement old_val target new_val ->
      atomic_exchange_statement_computation actor nd start_pc old_val target new_val s
  | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                          parameter_expressions local_variable_initializers ->
      create_thread_statement_computation actor nd start_pc method_id initial_pc bypassing_write_buffer optional_result
        parameter_var_ids parameter_expressions local_variable_initializers s
  | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                          stack_overflow ->
      method_call_statement_computation actor nd start_pc method_id return_pc parameter_var_ids parameter_expressions
        local_variable_initializers stack_overflow s
  | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
      return_statement_computation actor nd start_pc end_pc method_id bypassing_write_buffer output_dsts output_srcs s
  | TerminateThreadStatement method_id ->
      terminate_thread_statement_computation actor nd start_pc method_id s
  | TerminateProcessStatement method_id ->
      terminate_process_statement_computation actor nd start_pc method_id s
  | JoinStatement join_tid ->
      join_statement_computation actor nd start_pc join_tid s
  | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_computation actor nd start_pc false bypassing_write_buffer result allocation_td count s
  | MallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_computation actor nd start_pc bypassing_write_buffer result count s
  | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_computation actor nd start_pc true bypassing_write_buffer result allocation_td count s
  | CallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_computation actor nd start_pc bypassing_write_buffer result count s
  | DeallocStatement ptr ->
      dealloc_statement_computation actor nd start_pc ptr s
  | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
      somehow_statement_computation actor nd start_pc undefined_unless_cond
        bypassing_write_buffer modifies_clauses ensures_cond s
  | FenceStatement ->
      fence_statement_computation actor nd start_pc s
  | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer
                                 modifies_clauses reads_clauses ->
      external_method_start_statement_computation actor nd start_pc await_cond undefined_unless_cond
        bypassing_write_buffer modifies_clauses reads_clauses s
  | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
      external_method_middle_statement_computation actor nd start_pc bypassing_write_buffer modifies_clauses
        reads_clauses s
  | ExternalMethodEndStatement ensures_cond logs_clauses ->
      external_method_end_statement_computation actor nd start_pc ensures_cond logs_clauses s
