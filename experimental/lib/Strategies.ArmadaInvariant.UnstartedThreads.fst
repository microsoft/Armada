module Strategies.ArmadaInvariant.UnstartedThreads

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Type
open FStar.Sequence.Base
open Spec.Ubool
open Strategies.ArmadaStatement

let init_implies_unstarted_threads_have_empty_write_buffers (program: Armada.Program.t) (s: Armada.State.t)
  : Lemma (requires init_program program s)
          (ensures  unstarted_threads_have_empty_write_buffers s) =
  ()

#push-options "--z3rlimit 10"

let push_stack_variable_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match push_stack_variable actor writer_pc writer_expression_number method_id
                             frame_uniq initializer s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           (forall tid. ThreadStatusRunning? (s.threads tid).status ==>
                                   ThreadStatusRunning? (s'.threads tid).status)
                         /\ unstarted_threads_have_empty_write_buffers s')) =
  ()

#pop-options

let rec push_stack_variables_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match push_stack_variables actor writer_pc writer_expression_number method_id
                             frame_uniq initializers s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           (forall tid. ThreadStatusRunning? (s.threads tid).status ==>
                                   ThreadStatusRunning? (s'.threads tid).status)
                         /\ unstarted_threads_have_empty_write_buffers s'))
          (decreases initializers) =
  match initializers with
  | [] -> ()
  | first_initializer :: remaining_initializers ->
      push_stack_variable_maintains_unstarted_threads_have_empty_write_buffers actor writer_pc
        writer_expression_number method_id frame_uniq first_initializer s;
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_variables_maintains_unstarted_threads_have_empty_write_buffers actor writer_pc
             (writer_expression_number + 1) method_id frame_uniq remaining_initializers s')

let rec push_stack_parameters_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match push_stack_parameters actor writer_pc writer_expression_number method_id frame_uniq
                             var_ids parameters s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           (forall tid. ThreadStatusRunning? (s.threads tid).status ==>
                                   ThreadStatusRunning? (s'.threads tid).status)
                         /\ unstarted_threads_have_empty_write_buffers s'))
          (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> ()
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer =
        { var_id = first_var_id; iv = InitializerSpecific first_parameter; weakly_consistent = false } in
      push_stack_variable_maintains_unstarted_threads_have_empty_write_buffers actor writer_pc
        writer_expression_number method_id frame_uniq first_initializer s;
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_parameters_maintains_unstarted_threads_have_empty_write_buffers actor writer_pc
             (writer_expression_number + 1) method_id frame_uniq remaining_var_ids remaining_parameters s')
  | _ -> ()

let update_pointed_to_value_maintains_unstarted_threads_have_empty_write_buffers
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           ThreadStatusRunning? (s'.threads actor).status
                         /\ unstarted_threads_have_empty_write_buffers s')) =
  let cs' = update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
              new_value s in
  ()

let update_expression_maintains_unstarted_threads_have_empty_write_buffers
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match update_expression exp actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           ThreadStatusRunning? (s'.threads actor).status
                         /\ unstarted_threads_have_empty_write_buffers s')) =
  let cs' = update_expression exp actor writer_pc writer_expression_number bypassing_write_buffer
              new_value s in
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else
    ()

let rec update_expressions_maintains_unstarted_threads_have_empty_write_buffers
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match update_expressions exps actor writer_pc writer_expression_number bypassing_write_buffer
                             new_values s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' ->
                           ThreadStatusRunning? (s'.threads actor).status
                         /\ unstarted_threads_have_empty_write_buffers s'))
          (decreases exps) =
  match exps, new_values with
  | [], [] -> ()
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      update_expression_maintains_unstarted_threads_have_empty_write_buffers first_exp actor writer_pc
        writer_expression_number bypassing_write_buffer first_new_value s;
      (match update_expression first_exp actor writer_pc writer_expression_number
               bypassing_write_buffer first_new_value s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           update_expressions_maintains_unstarted_threads_have_empty_write_buffers remaining_exps actor writer_pc
             (writer_expression_number + 1) bypassing_write_buffer remaining_new_values s')
  | _ -> ()

let rec external_method_take_snapshot_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                             writer_expression_number bypassing_write_buffer reads_clauses s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s'))
          (decreases reads_clauses) =
  match reads_clauses with
  | [] -> ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      (match rvalue_computation first_reads_expression actor s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces first_value ->
           let td = expression_to_td first_reads_expression in
           let local_var = ExpressionLocalVariable td first_var_id in
           update_expression_maintains_unstarted_threads_have_empty_write_buffers local_var actor writer_pc
             writer_expression_number bypassing_write_buffer first_value s;
           (match update_expression local_var actor writer_pc writer_expression_number bypassing_write_buffer
                    first_value s with
            | ComputationImpossible | ComputationUndefined -> ()
            | ComputationProduces s' ->
                external_method_take_snapshot_maintains_unstarted_threads_have_empty_write_buffers
                  actor writer_pc (writer_expression_number + 1) bypassing_write_buffer remaining_reads_clauses s'))
  | _ -> ()

let rec log_expressions_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match log_expressions_computation actor logs_clauses s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s'))
          (decreases logs_clauses) =
  match logs_clauses with
  | [] -> ()
  | first_logs_clause :: remaining_logs_clauses ->
      (match rvalue_computation first_logs_clause actor s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces event ->
           let trace' = s.trace $:: event in
           let s' = { s with trace = trace' } in
           log_expressions_computation_maintains_unstarted_threads_have_empty_write_buffers actor
             remaining_logs_clauses s')

#push-options "--z3rlimit 10"

let assume_expression_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match assume_expression_statement_computation actor nd start_pc exp s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let assume_predicate_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (pred: Armada.State.t -> GTot bool)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match assume_predicate_statement_computation actor nd start_pc pred s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let assert_true_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match assert_true_statement_computation actor nd start_pc exp s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let assert_false_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match assert_false_statement_computation actor nd start_pc exp s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let conditional_jump_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (exp: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match conditional_jump_statement_computation actor nd start_pc exp s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let unconditional_jump_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match unconditional_jump_statement_computation actor nd start_pc s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let update_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (src: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match update_statement_computation actor nd start_pc bypassing_write_buffer dst src s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = update_statement_computation actor nd start_pc bypassing_write_buffer dst src s in
  if   Cons? nd
     || neqb (expression_to_td dst) (expression_to_td src) then
    ()
  else (
    match rvalue_computation src actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces src_value ->
        update_expression_maintains_unstarted_threads_have_empty_write_buffers dst actor start_pc 0
          bypassing_write_buffer src_value s
  )

let nondeterministic_update_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (dst: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match nondeterministic_update_statement_computation actor nd start_pc bypassing_write_buffer
                             dst s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = nondeterministic_update_statement_computation actor nd start_pc bypassing_write_buffer dst s in
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (expression_to_td dst) then
    ()
  else (
    let nd_value = Cons?.hd nd in
    if not (object_value_has_all_pointers_uninitialized nd_value) then
      ()
    else
      update_expression_maintains_unstarted_threads_have_empty_write_buffers dst actor start_pc 0
        bypassing_write_buffer nd_value s
  )

let propagate_write_message_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match propagate_write_message_statement_computation actor nd s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let compare_and_swap_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (target: expression_t)
  (old_val: expression_t)
  (new_val: expression_t)
  (bypassing_write_buffer: bool)
  (optional_result: option expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match compare_and_swap_statement_computation actor nd start_pc target old_val new_val
                             bypassing_write_buffer optional_result s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = compare_and_swap_statement_computation actor nd start_pc target old_val new_val
              bypassing_write_buffer optional_result s in
  if   Cons? nd
     || neqb (expression_to_td target) (expression_to_td old_val)
     || neqb (expression_to_td target) (expression_to_td new_val)
     || (match optional_result with
        | Some result -> neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDBool)
        | None -> false) then
    ()
  else begin
    match check_expression_up_to_date_for_rmw target actor s, rvalue_computation old_val actor s,
          rvalue_computation target actor s, rvalue_computation new_val actor s,
          lvalue_computation target actor s  with
    | ComputationProduces _, ComputationProduces old_value,
      ComputationProduces target_value, ComputationProduces new_value,
      ComputationProduces target_ptr -> begin
        let swap = eqb target_value old_value in
        update_pointed_to_value_maintains_unstarted_threads_have_empty_write_buffers target_ptr actor start_pc 0 false new_value s;
        match optional_result with
        | None -> ()
        | Some result ->
          match lvalue_computation result actor s, (if swap then update_pointed_to_value target_ptr actor start_pc 0 false new_value s else return s) with
          | ComputationProduces result_ptr, ComputationProduces s' ->
              let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
              update_pointed_to_value_maintains_unstarted_threads_have_empty_write_buffers result_ptr actor start_pc 1 bypassing_write_buffer swap_value s'
          | _ -> ()
      end
    | _ -> ()
  end

let atomic_exchange_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (old_val: expression_t)
  (target: expression_t)
  (new_val: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match atomic_exchange_statement_computation actor nd start_pc old_val target new_val s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = atomic_exchange_statement_computation actor nd start_pc old_val target new_val s in
  match check_expression_up_to_date_for_rmw target actor s with
  | ComputationImpossible | ComputationUndefined -> ()
  | ComputationProduces _ ->
      (match rvalue_computation target actor s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces target_value ->
           (match rvalue_computation new_val actor s with
            | ComputationImpossible | ComputationUndefined -> ()
            | ComputationProduces new_value ->
                update_expression_maintains_unstarted_threads_have_empty_write_buffers old_val actor
                  start_pc 0 false target_value s;
                (match update_expression old_val actor start_pc 0 false target_value s with
                 | ComputationImpossible | ComputationUndefined -> ()
                 | ComputationProduces s' ->
                     update_expression_maintains_unstarted_threads_have_empty_write_buffers target actor
                       start_pc 1 false new_value s')))

let make_thread_running_maintains_unstarted_threads_have_empty_write_buffers
  (method_id: method_id_t)
  (initial_pc: pc_t)
  (new_tid: tid_t)
  (frame_uniq: root_id_uniquifier_t)
  (s: Armada.State.t)
  : Lemma (requires unstarted_threads_have_empty_write_buffers s)
          (ensures  unstarted_threads_have_empty_write_buffers (make_thread_running method_id initial_pc new_tid
                      frame_uniq s)) =
  ()

let create_thread_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
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
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match create_thread_statement_computation actor nd start_pc method_id initial_pc
                             bypassing_write_buffer optional_result parameter_var_ids parameter_expressions
                             local_variable_initializers s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = create_thread_statement_computation actor nd start_pc method_id initial_pc
              bypassing_write_buffer optional_result parameter_var_ids parameter_expressions
              local_variable_initializers s in
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
          update_expression_maintains_unstarted_threads_have_empty_write_buffers result actor start_pc
            (list_len parameter_var_ids + list_len local_variable_initializers) bypassing_write_buffer
            new_tid_value s)
    else (
      let frame_uniq = create_thread_nd.frame_uniq in
      match rvalues_computation parameter_expressions actor s with
      | ComputationImpossible | ComputationUndefined -> ()
      | ComputationProduces parameter_values ->
          let s2 = make_thread_running method_id initial_pc new_tid frame_uniq s in
          make_thread_running_maintains_unstarted_threads_have_empty_write_buffers method_id initial_pc new_tid
            frame_uniq s;
          push_stack_parameters_maintains_unstarted_threads_have_empty_write_buffers new_tid start_pc 0 method_id
            frame_uniq parameter_var_ids parameter_values s2;
          (match push_stack_parameters new_tid start_pc 0 method_id frame_uniq parameter_var_ids
                   parameter_values s2 with
           | ComputationImpossible | ComputationUndefined -> ()
           | ComputationProduces s3 ->
                push_stack_variables_maintains_unstarted_threads_have_empty_write_buffers new_tid start_pc
                  (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3;
                (match push_stack_variables new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq
                         local_variable_initializers s3 with
                 | ComputationImpossible | ComputationUndefined -> ()
                 | ComputationProduces s4 ->
                     (match optional_result with
                      | None -> ()
                      | Some result ->
                         let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
                         update_expression_maintains_unstarted_threads_have_empty_write_buffers result actor start_pc
                           (list_len parameter_var_ids + list_len local_variable_initializers) bypassing_write_buffer
                           new_tid_value s4)))
    )
  )

let method_call_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
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
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match method_call_statement_computation actor nd start_pc method_id return_pc parameter_var_ids
                             parameter_expressions local_variable_initializers stack_overflow s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract method_call_nd_t) then
    ()
  else (
    let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    let frame_uniq = method_call_nd.frame_uniq in
    match rvalues_computation parameter_expressions actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces parameter_values ->
        let s2 = push_stack_frame actor method_id return_pc frame_uniq s in
        push_stack_parameters_maintains_unstarted_threads_have_empty_write_buffers actor start_pc 0
          method_id frame_uniq parameter_var_ids parameter_values s2;
        (match push_stack_parameters actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2 with
         | ComputationImpossible | ComputationUndefined -> ()
         | ComputationProduces s3 ->
             push_stack_variables_maintains_unstarted_threads_have_empty_write_buffers actor start_pc
               (list_len parameter_var_ids) method_id frame_uniq
               local_variable_initializers s3)
  )

let return_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (method_id: method_id_t)
  (bypassing_write_buffer: bool)
  (output_dsts: list expression_t)
  (output_srcs: list expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match return_statement_computation actor nd start_pc end_pc method_id bypassing_write_buffer
                             output_dsts output_srcs s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let thread = s.threads actor in
  if   Cons? nd
     || eqb thread.stack []
     || thread.top.method_id <> method_id
     || end_pc <> Some (Cons?.hd thread.stack).return_pc then
    ()
  else (
    match rvalues_computation output_srcs actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces output_values ->
        (match pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem with
         | ComputationImpossible | ComputationUndefined -> ()
         | ComputationProduces mem' ->
             let s2 = pop_stack_frame actor mem' s in
             update_expressions_maintains_unstarted_threads_have_empty_write_buffers output_dsts actor
               start_pc 0 bypassing_write_buffer output_values s2)
  )

let terminate_thread_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match terminate_thread_statement_computation actor nd start_pc method_id s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let terminate_process_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (method_id: method_id_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match terminate_process_statement_computation actor nd start_pc method_id s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let join_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (join_tid: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match join_statement_computation actor nd start_pc join_tid s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let alloc_successful_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (zero_initialized: bool)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (allocation_td: object_td_t)
  (count: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match alloc_successful_statement_computation actor nd start_pc zero_initialized
                             bypassing_write_buffer result allocation_td count s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = alloc_successful_statement_computation actor nd start_pc zero_initialized bypassing_write_buffer result
              allocation_td count s in
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract root_id_uniquifier_t)
     || neqb (expression_to_td count) (ObjectTDAbstract nat)
     || neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDPointer) then
    ()
  else (
    match rvalue_computation count actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces count_value ->
        let sz = ObjectValueAbstract?.value count_value in
        let array_td = ObjectTDArray allocation_td sz in
        let uniq = ObjectValueAbstract?.value (Cons?.hd nd) in
        let root_id = RootIdAllocation uniq in
        (match s.mem root_id with
         | RootAllocated allocated freed storage ->
             if   allocated
                || freed
                || neqb (object_storage_to_td storage) array_td
                || not (is_storage_ready_for_allocation storage)
                || (not zero_initialized && not (object_storage_arbitrarily_initialized_correctly storage))
                || (zero_initialized && not (is_storage_zero_filled storage)) then
               ()
             else (
               let s' = mark_allocation_root_allocated uniq storage s in
               let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
               update_expression_maintains_unstarted_threads_have_empty_write_buffers result actor start_pc 0
                 bypassing_write_buffer p s'
             )
         | _ -> ())
  )

let alloc_returning_null_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (result: expression_t)
  (count: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match alloc_returning_null_statement_computation actor nd start_pc bypassing_write_buffer
                             result count s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = alloc_returning_null_statement_computation actor nd start_pc bypassing_write_buffer
              result count s in
  if   Cons? nd
     || neqb (expression_to_td count) (ObjectTDAbstract nat)
     || neqb (expression_to_td result) (ObjectTDPrimitive PrimitiveTDPointer) then
    ()
  else (
    match rvalue_computation count actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces _ ->
        let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
        update_expression_maintains_unstarted_threads_have_empty_write_buffers result actor start_pc 0
          bypassing_write_buffer p s
  )

let dealloc_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (ptr: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match dealloc_statement_computation actor nd start_pc ptr s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let somehow_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (ensures_cond: expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match somehow_statement_computation actor nd start_pc undefined_unless_cond
                             bypassing_write_buffer modifies_clauses ensures_cond s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = somehow_statement_computation actor nd start_pc undefined_unless_cond bypassing_write_buffer
              modifies_clauses ensures_cond s in
  if   neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ()
  else (
    match rvalue_computation undefined_unless_cond actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces undefined_unless_value ->
        let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value undefined_unless_value) in
        if not undefined_unless_bool then
          ()
        else
          update_expressions_maintains_unstarted_threads_have_empty_write_buffers modifies_clauses actor start_pc 0
            bypassing_write_buffer nd s
  )

let fence_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match fence_statement_computation actor nd start_pc s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  ()

let external_method_start_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (await_cond: expression_t)
  (undefined_unless_cond: expression_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match external_method_start_statement_computation actor nd start_pc await_cond
                             undefined_unless_cond bypassing_write_buffer modifies_clauses reads_clauses s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = external_method_start_statement_computation actor nd start_pc await_cond undefined_unless_cond
              bypassing_write_buffer modifies_clauses reads_clauses s in
  if   neqb (expression_to_td await_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || neqb (expression_to_td undefined_unless_cond) (ObjectTDPrimitive PrimitiveTDBool)
     || list_len modifies_clauses <> list_len nd then
    ()
  else (
    match rvalue_computation await_cond actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces await_value ->
        let await_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
        if not await_bool then
          ()
        else (
          match rvalue_computation undefined_unless_cond actor s with
          | ComputationImpossible | ComputationUndefined -> ()
          | ComputationProduces undefined_unless_value ->
              let undefined_unless_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value await_value) in
              if not undefined_unless_bool then
                ()
              else (
                update_expressions_maintains_unstarted_threads_have_empty_write_buffers modifies_clauses
                  actor start_pc 0 bypassing_write_buffer nd s;
                match update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer nd s with
                | ComputationImpossible | ComputationUndefined -> ()
                | ComputationProduces s' ->
                    external_method_take_snapshot_maintains_unstarted_threads_have_empty_write_buffers
                      actor start_pc (list_len modifies_clauses) bypassing_write_buffer reads_clauses s'
              )
        )
  )

let external_method_middle_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (bypassing_write_buffer: bool)
  (modifies_clauses: list expression_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match external_method_middle_statement_computation actor nd start_pc bypassing_write_buffer
                             modifies_clauses reads_clauses s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = external_method_middle_statement_computation actor nd start_pc bypassing_write_buffer
              modifies_clauses reads_clauses s in
  match external_method_check_snapshot_computation actor reads_clauses s with
  | ComputationImpossible | ComputationUndefined -> ()
  | ComputationProduces _ ->
      update_expressions_maintains_unstarted_threads_have_empty_write_buffers modifies_clauses actor start_pc 0
        bypassing_write_buffer nd s;
      (match update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer nd s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           external_method_take_snapshot_maintains_unstarted_threads_have_empty_write_buffers
             actor start_pc (list_len modifies_clauses) bypassing_write_buffer reads_clauses s')

let external_method_end_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (ensures_cond: expression_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match external_method_end_statement_computation actor nd start_pc ensures_cond logs_clauses s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  let cs' = external_method_end_statement_computation actor nd start_pc ensures_cond logs_clauses s in
  if   Cons? nd
     || neqb (expression_to_td ensures_cond) (ObjectTDPrimitive PrimitiveTDBool) then
    ()
  else (
    match rvalue_computation ensures_cond actor s with
    | ComputationImpossible | ComputationUndefined -> ()
    | ComputationProduces ensures_value ->
        let ensures_bool = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value ensures_value) in
        log_expressions_computation_maintains_unstarted_threads_have_empty_write_buffers actor logs_clauses s
  )

#pop-options

let executing_statement_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s')) =
  match statement_computation actor nd start_pc end_pc statement s with
  | ComputationImpossible | ComputationUndefined -> ()
  | ComputationProduces s' ->
      (match statement with
       | AssumeExpressionStatement exp ->
           assume_expression_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc exp s
       | AssumePredicateStatement pred ->
           assume_predicate_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc pred s
       | AssertTrueStatement exp ->
           assert_true_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc exp s
       | AssertFalseStatement exp ->
           assert_false_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc exp s
       | ConditionalJumpStatement cond ->
           conditional_jump_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc cond s
       | UnconditionalJumpStatement ->
           unconditional_jump_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc s
       | UpdateStatement bypassing_write_buffer dst src ->
           update_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc bypassing_write_buffer dst src s
       | NondeterministicUpdateStatement bypassing_write_buffer dst ->
           nondeterministic_update_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc bypassing_write_buffer dst s
       | PropagateWriteMessageStatement ->
           propagate_write_message_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
             actor nd s
       | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
           compare_and_swap_statement_computation_maintains_unstarted_threads_have_empty_write_buffers
             actor nd start_pc target old_val new_val bypassing_write_buffer optional_result s
       | AtomicExchangeStatement old_val target new_val ->
           atomic_exchange_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc old_val target new_val s
       | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                               parameter_expressions local_variable_initializers ->
           create_thread_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
             parameter_expressions local_variable_initializers s
       | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                               stack_overflow ->
           method_call_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
             stack_overflow s
       | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
           return_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc end_pc method_id bypassing_write_buffer output_dsts output_srcs s
       | TerminateThreadStatement method_id ->
           terminate_thread_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc method_id s
       | TerminateProcessStatement method_id ->
           terminate_process_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc method_id s
       | JoinStatement join_tid ->
           join_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc join_tid s
       | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
           alloc_successful_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc false bypassing_write_buffer result allocation_td count s
       | MallocReturningNullStatement bypassing_write_buffer result count ->
           alloc_returning_null_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc bypassing_write_buffer result count s
       | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
           alloc_successful_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc true bypassing_write_buffer result allocation_td count s
       | CallocReturningNullStatement bypassing_write_buffer result count ->
           alloc_returning_null_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc bypassing_write_buffer result count s
       | DeallocStatement ptr ->
           dealloc_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd start_pc ptr s
       | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
           somehow_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond s
       | FenceStatement ->
           fence_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd start_pc s
       | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer
                                      modifies_clauses reads_clauses ->
           external_method_start_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc await_cond undefined_unless_cond bypassing_write_buffer modifies_clauses reads_clauses s
       | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
           external_method_middle_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc bypassing_write_buffer modifies_clauses reads_clauses s
       | ExternalMethodEndStatement ensures_cond logs_clauses ->
           external_method_end_statement_computation_maintains_unstarted_threads_have_empty_write_buffers actor nd
             start_pc ensures_cond logs_clauses s
      )     
