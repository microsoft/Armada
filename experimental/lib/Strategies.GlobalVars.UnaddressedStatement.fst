module Strategies.GlobalVars.UnaddressedStatement

open FStar.Sequence.Ambient
open FStar.Sequence.Base

open Util.Seq
open Util.Trigger
open Spec.List
open Spec.Ubool

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
open Armada.Transition
open Armada.UnaryOp

open Strategies.Invariant
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.GlobalVars
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.Unaddressed
open Strategies.ArmadaStatement

#push-options "--z3rlimit 10"

let inductive_invariant (vs: list var_id_t) (s: Armada.State.t) =
  global_variables_unaddressed_in_memory vs s.mem /\ positions_valid_in_state s /\ roots_match s.mem

let rec object_lacking_pointer_field_global_variables_unaddressed
  (vs: list var_id_t)
  (value: object_value_t)
  : Lemma (requires   object_td_lacks_pointer_field (object_value_to_td value)
                    /\ object_value_valid value)
          (ensures    global_variables_unaddressed_in_object_value vs value)
          (decreases  rank value)
  = match value with
    | ObjectValuePrimitive value ->
      ()
    | ObjectValueStruct fields ->
      objects_lacking_pointer_field_global_variables_unaddressed vs fields
    | ObjectValueArray element_td elements -> begin
        objects_lacking_pointer_field_global_variables_unaddressed vs elements;
        global_variables_unaddressed_in_object_value_seq_equivalent_to_forall vs elements
      end
    | ObjectValueAbstract _ _ -> ()

and objects_lacking_pointer_field_global_variables_unaddressed
  (vs: list var_id_t)
  (values: seq object_value_t)
  : Lemma (requires    (forall value. contains values value ==> object_value_valid value)
                    /\ (forall value. contains values value ==> object_td_lacks_pointer_field (object_value_to_td value)))
          (ensures     forall value. contains values value ==> global_variables_unaddressed_in_object_value vs value)
          (decreases   rank values)
  = if length values = 0 then
      ()
    else begin
      object_lacking_pointer_field_global_variables_unaddressed vs (index values 0);
      objects_lacking_pointer_field_global_variables_unaddressed vs (drop values 1)
    end

let rvalue_computation_lacking_pointer_field_global_variable_unaddrsessed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires expression_lacks_pointer_field exp)
          (ensures  otherwise true begin
                      let? value = rvalue_computation exp actor s in
                      return (global_variables_unaddressed_in_object_value vs value)
                    end)
  = match rvalue_computation exp actor s with
    | ComputationProduces value -> begin
      assert (object_value_valid value /\ object_value_to_td value == expression_to_td exp);
      object_lacking_pointer_field_global_variables_unaddressed vs value
      end
    | _ -> ()

let rvalue_computation_when_gvars_unaddressed_at_top_level_produces_value_with_gvars_unaddressed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_at_top_level_in_rvalue_expression vs exp
                    /\ inductive_invariant vs s)
          (ensures    otherwise true begin
                        let? value = rvalue_computation exp actor s in
                        return (global_variables_unaddressed_in_object_value vs value)
                      end)
    = if global_variables_unaddressed_in_rvalue_expression vs exp then
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs exp actor s
      else
        rvalue_computation_lacking_pointer_field_global_variable_unaddrsessed vs exp actor s

let update_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   UpdateStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let stmt = step.action.program_statement.statement in
       let thread = s.threads actor in
       let dst = UpdateStatement?.dst stmt in
       let src = UpdateStatement?.src stmt in
       let bypassing_write_buffer = UpdateStatement?.bypassing_write_buffer stmt in
       let new_value = ComputationProduces?.result (rvalue_computation src actor s) in
       rvalue_computation_when_gvars_unaddressed_at_top_level_produces_value_with_gvars_unaddressed vs src actor s;
       update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed vs dst actor thread.pc 0 bypassing_write_buffer new_value s
    end

let nondeterministic_update_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   NondeterministicUpdateStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let stmt = step.action.program_statement.statement in
       let thread = s.threads actor in
       let dst = NondeterministicUpdateStatement?.dst stmt in
       let nd_value = Cons?.hd step.nd in
       let bypassing_write_buffer = NondeterministicUpdateStatement?.bypassing_write_buffer stmt in
       update_expression_lacking_pointer_field_maintains_gvars_unaddressed vs dst actor thread.pc 0 bypassing_write_buffer nd_value s
    end

let propagate_write_message_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   PropagateWriteMessageStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | PropagateWriteMessageStatement -> begin
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd step.nd) in
         let propagator_thread = s.threads actor in
         let receiver_thread = s.threads receiver_tid in
         let which_message = receiver_thread.position_in_other_write_buffers actor in
         let write_message = index propagator_thread.write_buffer which_message in
         let position_in_other_write_buffers' =
           Spec.Map.upd receiver_thread.position_in_other_write_buffers actor (which_message + 1) in
         let receiver_thread' =
           { receiver_thread with position_in_other_write_buffers = position_in_other_write_buffers' } in
         let threads' = Spec.Map.upd s.threads receiver_tid receiver_thread' in
         match propagate_write_message write_message receiver_tid s.mem with
         | ComputationProduces mem' -> begin
           let p = write_message.location in
           let storage = ComputationProduces?.result (dereference_computation p s.mem) in
           dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs p s.mem;
           match storage with
           | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
             let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message.version in
             let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values new_local_versions in
             assert (global_variables_unaddressed_in_storage vs new_storage);
             update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed vs p new_storage s.mem
           | _ -> ()
         end
         | _ -> ()
       end
       | _ -> ()
    end


let compare_and_swap_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   CompareAndSwapStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
      let ps = step.action.program_statement in
      let thread = s.threads actor in
      let stmt = ps.statement in
      let target = CompareAndSwapStatement?.target stmt in
      let old_val = CompareAndSwapStatement?.old_val stmt in
      let new_val = CompareAndSwapStatement?.new_val stmt in
      let optional_result = CompareAndSwapStatement?.optional_result stmt in
      let bypassing_write_buffer = CompareAndSwapStatement?.bypassing_write_buffer stmt in
      let target_value = ComputationProduces?.result (rvalue_computation target actor s) in
      let old_value = ComputationProduces?.result (rvalue_computation old_val actor s) in
      let new_value = ComputationProduces?.result (rvalue_computation new_val actor s) in
      let target_ptr = ComputationProduces?.result (lvalue_computation target actor s) in
      rvalue_computation_when_gvars_unaddressed_at_top_level_produces_value_with_gvars_unaddressed vs new_val actor s;
      update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed
        vs target_ptr actor thread.pc 0 false new_value s;
      let swap = eqb target_value old_value in
      let s' = ComputationProduces?.result (if swap then update_expression target actor thread.pc 0 false new_value s
                                                    else return s) in
      match optional_result with
      | Some result ->
        let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
        let result_ptr = ComputationProduces?.result (lvalue_computation result actor s) in
        assert (global_variables_unaddressed_in_object_value vs swap_value);
        update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed
          vs result_ptr actor thread.pc 1 bypassing_write_buffer swap_value s'
      | _ -> ()
    end

let expression_lvalue_computable_gvars_unaddressed_in_rvalue
  (vs: list var_id_t)
  (e: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires begin match lvalue_computation e actor s with
                          | ComputationImpossible -> false
                          | _ -> true
                    end)
          (ensures  global_variables_unaddressed_in_rvalue_expression vs e)
  = ()

#push-options "--z3rlimit 30"

let atomic_exchange_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   AtomicExchangeStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       let thread = s.threads actor in
       let old_val = AtomicExchangeStatement?.old_val stmt in
       let old_ptr = ComputationProduces?.result (lvalue_computation old_val actor s) in
       let new_val = AtomicExchangeStatement?.new_val stmt in
       let new_value = ComputationProduces?.result (rvalue_computation new_val actor s) in
       let target = AtomicExchangeStatement?.target stmt in
       let target_value = ComputationProduces?.result (rvalue_computation target actor s) in
       let target_ptr = ComputationProduces?.result (lvalue_computation target actor s) in
       let s' = ComputationProduces?.result (update_pointed_to_value old_ptr actor thread.pc 0 false target_value s) in
       rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs target actor s;
       expression_lvalue_computable_gvars_unaddressed_in_rvalue vs target actor s;
       update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed vs old_ptr actor thread.pc 0 false target_value s;
       rvalue_computation_when_gvars_unaddressed_at_top_level_produces_value_with_gvars_unaddressed vs new_val actor s;
       update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed vs target_ptr actor thread.pc 0 false new_value s'
    end

#pop-options

let rec rvalues_computation_when_gvars_unaddressed_at_top_level_produce_values_with_gvars_unaddressed
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_at_top_level_in_rvalue_expressions vs exps
                    /\ inductive_invariant vs s)
          (ensures  (match rvalues_computation exps actor s with
                     | ComputationProduces values -> global_variables_unaddressed_in_object_values vs values
                     | _ -> True))
          (decreases exps) =
  match exps with
  | [] -> ()
  | exp :: exps' ->
    rvalue_computation_when_gvars_unaddressed_at_top_level_produces_value_with_gvars_unaddressed vs exp actor s;
    rvalues_computation_when_gvars_unaddressed_at_top_level_produce_values_with_gvars_unaddressed vs exps' actor s

let push_stack_variable_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s: Armada.State.t)
  : Lemma (requires   inductive_invariant vs s
                    /\ global_variables_unaddressed_in_initializer vs initializer)
          (ensures    otherwise True begin
                        let? s' = push_stack_variable
                                  actor writer_pc writer_expression_number method_id frame_uniq initializer s in
                        return (inductive_invariant vs s')
                      end) =
  let root_id = RootIdStack actor method_id frame_uniq initializer.var_id in
  let root = s.mem root_id in
  if not (stack_variable_ready_for_push root initializer) then
    ()
  else
    let thread = s.threads actor in
    let var_id = initializer.var_id in
    if list_contains var_id thread.top.local_variables then
      ()
    else
      let local_variables' = var_id :: thread.top.local_variables in
      let top' = { thread.top with local_variables = local_variables' } in
      let thread' = { thread with top = top' } in
      let threads' = Spec.Map.upd s.threads actor thread' in
      let storage = RootStackVariable?.storage root in
      assert (object_storage_arbitrarily_initialized_correctly storage);
      object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs storage;
      let root' = RootStackVariable true false (RootStackVariable?.storage root) in
      assert (global_variables_unaddressed_in_root vs root');
      let mem' = Spec.Map.upd s.mem root_id root' in
      let mem_unaddressed(): Lemma (ensures global_variables_unaddressed_in_memory vs mem') =
        introduce forall root_id' . global_variables_unaddressed_in_root vs (mem' root_id')
        with
          if root_id = root_id' then
            ()
          else
            ()
      in
      mem_unaddressed();
      let s' = { s with mem = mem'; threads = threads' } in
      (match initializer.iv with
       | InitializerArbitrary td -> ()
       | InitializerSpecific value ->
           push_stack_variable_maintains_roots_match
             actor writer_pc writer_expression_number method_id frame_uniq initializer s';
           let td = (object_value_to_td value) in
           update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed
             vs (ExpressionLocalVariable td var_id) actor writer_pc
             writer_expression_number false value s')

let rec push_stack_variables_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : Lemma (requires   inductive_invariant vs s
                    /\ global_variables_unaddressed_in_initializers vs initializers)
          (ensures    otherwise True begin
                        let? s' = push_stack_variables
                                  actor writer_pc writer_expression_number method_id frame_uniq initializers s in
                        return (inductive_invariant vs s')
                      end)
          (decreases initializers) =
  match initializers with
  | [] -> ()
  | first_initializer :: remaining_initializers ->
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           assert (global_variables_unaddressed_in_initializer vs first_initializer);
           push_stack_variable_maintains_inductive_invariant
             vs actor writer_pc writer_expression_number method_id frame_uniq first_initializer s;
           assert (inductive_invariant vs s');
           push_stack_variables_maintains_inductive_invariant
             vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_initializers s')

let rec push_stack_parameters_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   inductive_invariant vs s
                    /\ global_variables_unaddressed_in_object_values vs parameters)
          (ensures    otherwise True begin
                        let? s' = push_stack_parameters
                                  actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s in
                      return (inductive_invariant vs s')
                    end)
          (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> ()
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer =
        { var_id = first_var_id; iv = InitializerSpecific first_parameter; weakly_consistent = false } in
      assert (global_variables_unaddressed_in_initializer vs first_initializer);
      push_stack_variable_maintains_inductive_invariant
        vs actor writer_pc writer_expression_number method_id frame_uniq first_initializer s;
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_parameters_maintains_inductive_invariant
             vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_var_ids remaining_parameters s')
  | _ -> ()

let create_thread_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   CreateThreadStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids parameter_expressions local_variable_initializers ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let create_thread_nd: create_thread_nd_t = ObjectValueAbstract?.value (Cons?.hd step.nd) in
         let new_tid = create_thread_nd.new_tid in
         if new_tid = 0 then
           match optional_result with
           | None -> ()
           | Some result ->
             let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
             update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed vs result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers) bypassing_write_buffer new_tid_value s
         else begin
           let new_thread = s.threads new_tid in
           let frame_uniq = create_thread_nd.frame_uniq in
           assert (~ (new_thread.status <> ThreadStatusNotStarted
                  || length new_thread.write_buffer <> 0
                  || list_contains frame_uniq s.uniqs_used));
           let parameter_values = ComputationProduces?.result (rvalues_computation parameter_expressions actor s) in
           rvalues_computation_when_gvars_unaddressed_at_top_level_produce_values_with_gvars_unaddressed vs parameter_expressions actor s;
           let s2 = make_thread_running method_id initial_pc new_tid frame_uniq s in
           push_stack_parameters_maintains_inductive_invariant
             vs new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2;
           let s3 = ComputationProduces?.result
             (push_stack_parameters new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2) in
           push_stack_variables_maintains_inductive_invariant
             vs new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3;
           let s4 = ComputationProduces?.result
             (push_stack_variables new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq
              local_variable_initializers s3) in
           match optional_result with
           | None -> ()
           | Some result ->
             let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
             update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed
               vs result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers)
               bypassing_write_buffer new_tid_value s4
         end
       | _ -> ()
    end

let method_call_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   MethodCallStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
         let stmt = ps.statement in
         match stmt with
         | MethodCallStatement
           method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers stack_overflow ->
           let thread = s.threads actor in
           let start_pc = thread.pc in
           let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd step.nd) in
           let frame_uniq = method_call_nd.frame_uniq in
           assert (~ (list_contains frame_uniq s.uniqs_used));
           let parameter_values = ComputationProduces?.result (rvalues_computation parameter_expressions actor s) in
           let s2 = push_stack_frame actor method_id return_pc frame_uniq s in
           let s3 = ComputationProduces?.result
             (push_stack_parameters actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2) in
           rvalues_computation_when_gvars_unaddressed_at_top_level_produce_values_with_gvars_unaddressed vs parameter_expressions actor s;
           push_stack_parameters_maintains_inductive_invariant
             vs actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2;
           let s4 = ComputationProduces?.result
             (push_stack_variables actor start_pc (list_len parameter_var_ids) method_id frame_uniq 
              local_variable_initializers s3) in
           push_stack_variables_maintains_inductive_invariant
             vs actor start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3
         | _ -> ()
         end

let rec pop_stack_variables_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (s: Armada.State.t)
  : Lemma (requires inductive_invariant vs s)
          (ensures otherwise True begin
                     let? mem' = pop_stack_variables actor method_id frame_uniq var_ids s.mem in
                     return (inductive_invariant vs ({ s with mem = mem' }))
                   end)
  = match var_ids with
    | [] -> ()
    | first_var_id :: remaining_var_ids -> begin
      match pop_stack_variable actor method_id frame_uniq first_var_id s.mem with
      | ComputationProduces mem' ->
        assert (inductive_invariant vs ({s with mem = mem'}));
        pop_stack_variables_maintains_inductive_invariant
          vs actor method_id frame_uniq remaining_var_ids ({s with mem = mem'})
      | _ -> ()
    end

let return_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ReturnStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let output_values = ComputationProduces?.result (rvalues_computation output_srcs actor s) in
         rvalues_computation_when_gvars_unaddressed_at_top_level_produce_values_with_gvars_unaddressed vs output_srcs actor s;
         let mem' = ComputationProduces?.result
           (pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem) in
         pop_stack_variables_maintains_inductive_invariant
           vs actor method_id thread.top.frame_uniq thread.top.local_variables s;
         let s2 = pop_stack_frame actor mem' s in
         update_expressions_with_gvars_unaddressed_maintains_gvars_unaddressed
           vs output_dsts actor start_pc 0 bypassing_write_buffer output_values s2
       | _ -> ()
    end


let terminate_thread_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   TerminateThreadStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | TerminateThreadStatement method_id ->
         let thread = s.threads actor in
         pop_stack_variables_maintains_inductive_invariant
           vs actor method_id thread.top.frame_uniq thread.top.local_variables s
       | _ -> ()
    end

let mark_allocation_root_allocated_maintains_inductive_invariant
  (vs: list var_id_t)
  (uniq: root_id_uniquifier_t)
  (storage: valid_object_storage_t)
  (s: Armada.State.t)
  : Lemma (requires   inductive_invariant vs s
                    /\ global_variables_unaddressed_in_storage vs storage)
          (ensures inductive_invariant vs (mark_allocation_root_allocated uniq storage s))
  = ()

let alloc_successful_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   (  MallocSuccessfulStatement? step.action.program_statement.statement
                      || CallocSuccessfulStatement? step.action.program_statement.statement)
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count
       | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let count_value = ComputationProduces?.result (rvalue_computation count actor s) in
         let sz = ObjectValueAbstract?.value count_value in
         let array_td = ObjectTDArray allocation_td sz in
         let uniq = ObjectValueAbstract?.value (Cons?.hd step.nd) in
         let root_id = RootIdAllocation uniq in
         match s.mem root_id with
         | RootAllocated allocated freed storage ->
           let storage_doesnt_depend_on_gvars (): Lemma (ensures global_variables_unaddressed_in_storage vs storage) =
             if (object_storage_arbitrarily_initialized_correctly storage) then
               object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs storage
             else
               object_storage_zero_filled_doesnt_depend_on_gvars vs storage
           in
           storage_doesnt_depend_on_gvars ();
           let s' = mark_allocation_root_allocated uniq storage s in
           mark_allocation_root_allocated_maintains_inductive_invariant vs uniq storage s;
           let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
           update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed
             vs result actor start_pc 0 bypassing_write_buffer p s'
         | _ -> ()
       | _ -> ()
    end

let alloc_returning_null_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   (  MallocReturningNullStatement? step.action.program_statement.statement
                      || CallocReturningNullStatement? step.action.program_statement.statement)
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | MallocReturningNullStatement bypassing_write_buffer result count
       | CallocReturningNullStatement bypassing_write_buffer result count ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
         update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed
           vs result actor start_pc 0 bypassing_write_buffer p s
       | _ -> ()
    end

let somehow_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   SomehowStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         update_expressions_lacking_pointer_field_maintains_gvars_unaddressed
           vs modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s
       | _ -> ()
    end

let fence_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   FenceStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | FenceStatement ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let p = PointerRoot RootIdFence in
         update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed
           vs p actor start_pc 0 false (ObjectValuePrimitive (PrimitiveBoxBool false)) s
       | _ -> ()
    end

let rec external_method_take_snapshot_of_reads_clauses_computation_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_reads_clauses vs reads_clauses
                    /\ inductive_invariant vs s)
          (ensures  otherwise True begin
                      let? s' = external_method_take_snapshot_of_reads_clauses_computation actor writer_pc writer_expression_number bypassing_write_buffer reads_clauses s in
                      return (inductive_invariant vs s')
                    end)
          (decreases reads_clauses)
  = match reads_clauses with
  | [] -> ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses -> begin
    match rvalue_computation first_reads_expression actor s with
    | ComputationProduces first_value -> begin
      let td = expression_to_td first_reads_expression in
      let local_var = ExpressionLocalVariable td first_var_id in
      match lvalue_computation local_var actor s with
      | ComputationProduces p -> begin
        assert (global_variables_unaddressed_in_pointer vs p);
        match update_pointed_to_value
              p actor writer_pc writer_expression_number bypassing_write_buffer first_value s with
        | ComputationProduces s' ->
          rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed
            vs first_reads_expression actor s;
          update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed
            vs p actor writer_pc writer_expression_number bypassing_write_buffer first_value s;
          external_method_take_snapshot_of_reads_clauses_computation_maintains_inductive_invariant
            vs actor writer_pc (writer_expression_number + 1) bypassing_write_buffer remaining_reads_clauses s'
        | _ -> ()
      end
      | _ -> ()
    end
    | _ -> ()
  end

let external_method_start_middle_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   (   ExternalMethodStartStatement? step.action.program_statement.statement
                       || ExternalMethodMiddleStatement? step.action.program_statement.statement)
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ExternalMethodStartStatement
         _ _ bypassing_write_buffer modifies_clauses reads_clauses
       | ExternalMethodMiddleStatement
         bypassing_write_buffer modifies_clauses reads_clauses ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let s2 = ComputationProduces?.result
           (update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s) in
         update_expressions_lacking_pointer_field_maintains_gvars_unaddressed
           vs modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s;
         external_method_take_snapshot_of_reads_clauses_computation_maintains_inductive_invariant
           vs actor start_pc (list_len modifies_clauses) bypassing_write_buffer reads_clauses s2
       | _ -> ()
       | _ -> ()
    end

let rec log_expressions_computation_maintains_inductive_invariant
  (vs: list var_id_t)
  (actor: tid_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : Lemma (requires inductive_invariant vs s)
          (ensures  otherwise True begin
                      let? s' = log_expressions_computation actor logs_clauses s in
                        return (inductive_invariant vs s')
                    end)
  = match logs_clauses with
  | [] -> ()
  | first_logs_clause :: remaining_logs_clauses -> begin
    match rvalue_computation first_logs_clause actor s with
    | ComputationProduces event ->
      let trace' = s.trace $:: event in
      let s' = { s with trace = trace' } in
      log_expressions_computation_maintains_inductive_invariant vs actor remaining_logs_clauses s'
    | _ -> ()
  end

let external_method_end_statement_unaddressable_global_vars_unaddressed_in_memory
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ExternalMethodEndStatement? step.action.program_statement.statement
                    /\ global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ inductive_invariant vs s)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ExternalMethodEndStatement _ logs_clauses ->
         let thread = s.threads actor in
         log_expressions_computation_maintains_inductive_invariant vs actor logs_clauses s
       | _ -> ()
    end

#push-options "--z3rlimit 30"

let global_variables_unaddressable_by_statement_global_vars_unaddressed_in_state
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressable_in_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ roots_match s.mem /\ positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem)
          (ensures  global_variables_unaddressed_in_memory vs (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)).mem)
  = match step.action.program_statement.statement with
  | UpdateStatement bypassing_write_buffer dst src ->
      update_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | NondeterministicUpdateStatement bypassing_write_buffer dst ->
      nondeterministic_update_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | PropagateWriteMessageStatement ->
      propagate_write_message_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
      compare_and_swap_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | AtomicExchangeStatement old_val target new_val ->
      atomic_exchange_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                          parameter_expressions local_variable_initializers ->
      create_thread_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                          stack_overflow ->
      method_call_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
      return_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | TerminateThreadStatement method_id ->
      terminate_thread_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count
  | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | MallocReturningNullStatement bypassing_write_buffer result count
  | CallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
      somehow_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | FenceStatement ->
      fence_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | ExternalMethodStartStatement _ _ _ _ _
  | ExternalMethodMiddleStatement _ _ _ ->
      external_method_start_middle_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | ExternalMethodEndStatement ensures_cond logs_clauses ->
      external_method_end_statement_unaddressable_global_vars_unaddressed_in_memory
        vs actor step starts_atomic_block ends_atomic_block s
  | _ -> ()

#pop-options
