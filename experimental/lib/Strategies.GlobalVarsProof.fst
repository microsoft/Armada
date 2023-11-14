module Strategies.GlobalVarsProof

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

let ($$) (#a: Type) (#b: Type) (f: a -> b) (x: a): b = f x
let ($$$) (#a: Type) (f: a -> GTot (conditional_computation_t a)) (x: a): GTot (conditional_computation_t a) = f x

let memories_match_on_global_variables
  (vs: list var_id_t)
  (mem1 mem2: Armada.Memory.t)
  : GTot ubool
  = forall v . list_contains v vs ==>
      mem1 (RootIdGlobal v) == mem2 (RootIdGlobal v)

let states_match_on_global_variables
  (vs: list var_id_t)
  (s1 s2: Armada.State.t)
  : GTot ubool
  = memories_match_on_global_variables vs s1.mem s2.mem


let state_well_formed (vs: list var_id_t) (s: Armada.State.t): GTot ubool =
  roots_match s.mem /\ positions_valid_in_state s /\ global_variables_unaddressed_in_memory vs s.mem

let rec update_pointer_directly_with_gvars_unaddressed_memories_match_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem: Armada.Memory.t)
  : Lemma (requires global_variables_unaddressed_in_pointer vs p)
          (ensures  otherwise True begin
                      let? mem' = update_pointer_directly p new_storage mem in
                      return $$$ memories_match_on_global_variables vs mem mem'
                    end) =
  match p with
  | PointerField struct_ptr field_id ->
      (match dereference_computation struct_ptr mem with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageStruct fields ->
                if   field_id >= length fields
                   || neqb (object_storage_to_td new_storage)
                          (object_storage_to_td (index fields field_id)) then
                  ()
                  else (
                  let new_parent = update_storage_child parent field_id new_storage in
                    update_pointer_directly_with_gvars_unaddressed_memories_match_on_global_variables
                      vs struct_ptr new_parent mem
                )
            | _ -> ())
      | _ -> ())
  | PointerIndex array_ptr idx ->
      (match dereference_computation array_ptr mem with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageArray element_td elements ->
                if   idx < 0
                   || idx >= length elements
                   || neqb (object_storage_to_td new_storage) element_td then
                  ()
                else (
                  let new_parent = update_storage_child parent idx new_storage in
                  update_pointer_directly_with_gvars_unaddressed_memories_match_on_global_variables
                    vs array_ptr new_parent mem
                )
            | _ -> ())
      | _ -> ())
  | _ -> ()

let update_pointer_with_object_with_gvars_unaddressed_memories_match_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (mem: Armada.Memory.t)
  : Lemma (requires global_variables_unaddressed_in_pointer vs p)
          (ensures  otherwise True begin
                      let? v = update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value mem in
                      return $$$ memories_match_on_global_variables vs mem (snd v)
                    end) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           ()
       | _ -> ())
  | PointerField struct_ptr field_id ->
      (match dereference_computation struct_ptr mem with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageStruct fields ->
               if field_id >= length fields then
                 ()
               else
                 let field = index fields field_id in
                 if not (object_storage_valid field) || neqb (object_storage_to_td field) (object_value_to_td new_value) then
                   ()
                 else (
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer field new_value with
                    | ComputationProduces (write_message, new_field) ->
                        if (not (can_update_storage_child parent field_id new_field)) then
                          ()
                        else (
                          let new_parent = update_storage_child parent field_id new_field in
                          update_pointer_directly_with_gvars_unaddressed_memories_match_on_global_variables
                            vs struct_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      (match dereference_computation array_ptr mem with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageArray element_td elements ->
               if idx < 0 || idx >= length elements then
                 ()
               else
                 let element = index elements idx in
                 if not (object_storage_valid element) then
                   ()
                 else (
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer element new_value with
                    | ComputationProduces (write_message, new_element) ->
                        if not (can_update_storage_child parent idx new_element) then
                          ()
                        else (
                          let new_parent = update_storage_child parent idx new_element in
                          update_pointer_directly_with_gvars_unaddressed_memories_match_on_global_variables
                            vs array_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())

let update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_pointer vs p)
          (ensures  (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer new_value s with
                      | ComputationProduces s' -> states_match_on_global_variables vs s s'
                      | _ -> True)) =
  update_pointer_with_object_with_gvars_unaddressed_memories_match_on_global_variables vs p actor writer_pc
    writer_expression_number bypassing_write_buffer new_value s.mem;
  match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value s.mem with
  | ComputationProduces (optional_write_message, new_mem) -> begin
      match optional_write_message with
      | Some write_message ->
          let thread = s.threads actor in
          let new_write_buffer = build thread.write_buffer write_message in
          let new_thread = { thread with write_buffer = new_write_buffer } in
          let new_threads = Spec.Map.upd s.threads actor new_thread in
          let s' = { s with mem = new_mem; threads = new_threads; } in
          assert (states_match_on_global_variables vs s s')
      | None ->
          let s' = { s with mem = new_mem; } in
          assert (states_match_on_global_variables vs s s')
      | _ -> false_elim ()
  end
  | _ -> ()

#push-options "--z3rlimit 10"

let update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_lvalue_expression vs exp
                    /\ state_well_formed vs s)
          (ensures  otherwise True begin
                      let? s' = update_expression exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s in
                      return $$$ states_match_on_global_variables vs s s'
                    end) =
  if   not (expression_valid exp)
          || not (object_value_valid new_value)
          || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else begin
    let td = expression_to_td exp in
    match lvalue_computation exp actor s with
    | ComputationProduces p ->
        lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs exp actor s;
        update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs p actor writer_pc writer_expression_number bypassing_write_buffer new_value s;
        (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                 new_value s with
         | ComputationProduces s' -> ()
         | _ -> ())
    | _ -> ()
  end

#pop-options

let rec update_expressions_with_gvars_unaddressed_in_both_values_memories_match_on_global_variables
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   state_well_formed vs s
                    /\ global_variables_unaddressed_in_object_values vs new_values
                    /\ global_variables_unaddressed_in_lvalue_expressions vs exps)
          (ensures otherwise True begin
                     let? s' = update_expressions exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s in
                     return $$$ states_match_on_global_variables vs s s'
                   end)
  = match exps, new_values with
    | [], [] -> ()
    | first_exp :: remaining_exps, first_new_value :: remaining_new_values -> begin
      update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed vs first_exp actor writer_pc
        writer_expression_number bypassing_write_buffer first_new_value s;
      update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs first_exp actor writer_pc writer_expression_number bypassing_write_buffer first_new_value s;
      match update_expression first_exp actor writer_pc writer_expression_number
               bypassing_write_buffer first_new_value s with
       | ComputationProduces s_next ->
           update_expressions_with_gvars_unaddressed_in_both_values_memories_match_on_global_variables vs
             remaining_exps actor writer_pc (writer_expression_number + 1)
             bypassing_write_buffer remaining_new_values s_next
       | _ -> ()
    end
    | _ -> ()

let rec update_expressions_with_gvars_unaddressed_in_lvalues_and_lacking_pointer_field_memories_match_on_global_variables
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   state_well_formed vs s
                    /\ expressions_lack_pointer_field exps
                    /\ global_variables_unaddressed_in_lvalue_expressions vs exps)
          (ensures otherwise True begin
                     let? s' = update_expressions exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s in
                     return $$$ states_match_on_global_variables vs s s'
                   end)
  = match exps, new_values with
    | [], [] -> ()
    | first_exp :: remaining_exps, first_new_value :: remaining_new_values -> begin
      update_expression_lacking_pointer_field_maintains_gvars_unaddressed vs first_exp actor writer_pc
        writer_expression_number bypassing_write_buffer first_new_value s;
      update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs first_exp actor writer_pc writer_expression_number bypassing_write_buffer first_new_value s;
      match update_expression first_exp actor writer_pc writer_expression_number
               bypassing_write_buffer first_new_value s with
       | ComputationProduces s_next ->
           update_expressions_with_gvars_unaddressed_in_lvalues_and_lacking_pointer_field_memories_match_on_global_variables vs
             remaining_exps actor writer_pc (writer_expression_number + 1)
             bypassing_write_buffer remaining_new_values s_next
       | _ -> ()
    end
    | _ -> ()

#push-options "--z3rlimit 10"

let rec push_stack_parameters_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires True)
          (ensures otherwise True begin
                      let? s' = push_stack_parameters actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s in
                      return $$$ states_match_on_global_variables vs s s'
                    end)
          (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> ()
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer =
        { var_id = first_var_id; iv = InitializerSpecific first_parameter; weakly_consistent = false } in
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_parameters_memories_match_on_global_variables vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_var_ids remaining_parameters s')
  | _ -> ()

#pop-options

let rec push_stack_variables_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : Lemma (requires True)
          (ensures  otherwise True begin
                      let? s' = push_stack_variables actor writer_pc writer_expression_number method_id frame_uniq initializers s in
                      return $$$ states_match_on_global_variables vs s s'
                    end)
          (decreases initializers) =
  match initializers with
  | [] -> ()
  | first_initializer :: remaining_initializers ->
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_variables_memories_match_on_global_variables vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_initializers s')

let rec pop_stack_variables_maintains_state_well_formed
  (vs: list var_id_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (s: Armada.State.t)
  : Lemma (requires state_well_formed vs s)
          (ensures otherwise True begin
                     let? mem' = pop_stack_variables actor method_id frame_uniq var_ids s.mem in
                     return $$$ state_well_formed vs ({ s with mem = mem' })
                   end)
  = match var_ids with
    | [] -> ()
    | first_var_id :: remaining_var_ids -> begin
      match pop_stack_variable actor method_id frame_uniq first_var_id s.mem with
      | ComputationProduces mem' ->
        assert (state_well_formed vs ({s with mem = mem'}));
        pop_stack_variables_maintains_state_well_formed vs actor method_id frame_uniq remaining_var_ids ({s with mem = mem'})
      | _ -> ()
    end

let rec pop_stack_variables_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (mem: Armada.Memory.t)
  : Lemma (requires True)
          (ensures otherwise True begin
                     let? mem' = pop_stack_variables actor method_id frame_uniq var_ids mem in
                     return $$$ memories_match_on_global_variables vs mem mem'
                   end)
  = match var_ids with
    | [] -> ()
    | first_var_id :: remaining_var_ids -> begin
      match pop_stack_variable actor method_id frame_uniq first_var_id mem with
      | ComputationProduces mem' ->
        assert (memories_match_on_global_variables vs mem mem');
        pop_stack_variables_memories_match_on_global_variables vs actor method_id frame_uniq remaining_var_ids mem'
      | _ -> ()
    end


let push_stack_variable_maintains_state_well_formed
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s: Armada.State.t)
  : Lemma (requires state_well_formed vs s
                    /\ global_variables_unaddressed_in_initializer vs initializer)
          (ensures  otherwise True begin
                      let? s' = push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq initializer s in
                      return $$$ state_well_formed vs s'
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
           push_stack_variable_maintains_roots_match actor writer_pc writer_expression_number method_id frame_uniq initializer s';
           let td = (object_value_to_td value) in
           update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed vs (ExpressionLocalVariable td var_id) actor writer_pc
             writer_expression_number false value s')

let rec push_stack_variables_maintains_state_well_formed
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : Lemma (requires    state_well_formed vs s
                    /\ global_variables_unaddressed_in_initializers vs initializers)
          (ensures  otherwise True begin
                      let? s' = push_stack_variables actor writer_pc writer_expression_number method_id frame_uniq initializers s in
                      return $$$ state_well_formed vs s'
                    end)
          (decreases initializers) =
  match initializers with
  | [] -> ()
  | first_initializer :: remaining_initializers ->
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           assert (global_variables_unaddressed_in_initializer vs first_initializer);
           push_stack_variable_maintains_state_well_formed vs actor writer_pc writer_expression_number method_id frame_uniq first_initializer s;
           assert (state_well_formed vs s');
           push_stack_variables_maintains_state_well_formed vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_initializers s')

let rec push_stack_parameters_maintains_state_well_formed
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires state_well_formed vs s
                    /\ global_variables_unaddressed_in_object_values vs parameters)
          (ensures  otherwise True begin
                      let? s' = push_stack_parameters actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s in
                      return $$$ state_well_formed vs s'
                    end)
          (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> ()
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer =
        { var_id = first_var_id; iv = InitializerSpecific first_parameter; weakly_consistent = false } in
      assert (global_variables_unaddressed_in_initializer vs first_initializer);
      push_stack_variable_maintains_state_well_formed vs actor writer_pc writer_expression_number method_id frame_uniq first_initializer s;
      (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s with
       | ComputationImpossible | ComputationUndefined -> ()
       | ComputationProduces s' ->
           push_stack_parameters_maintains_state_well_formed vs actor writer_pc (writer_expression_number + 1)
             method_id frame_uniq remaining_var_ids remaining_parameters s')
  | _ -> ()

let mark_allocation_root_allocated_state_well_formed
  (vs: list var_id_t)
  (uniq: root_id_uniquifier_t)
  (storage: valid_object_storage_t)
  (s: Armada.State.t)
  : Lemma (requires   state_well_formed vs s
                    /\ global_variables_unaddressed_in_storage vs storage)
          (ensures state_well_formed vs (mark_allocation_root_allocated uniq storage s))
  = ()

let rec log_expressions_computation_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (logs_clauses: list expression_t)
  (s: Armada.State.t)
  : Lemma (ensures otherwise True begin
                     let? s' = log_expressions_computation actor logs_clauses s in
                     return $$$ states_match_on_global_variables vs s s'
                   end) =
  match logs_clauses with
  | [] -> ()
  | first_logs_clause :: remaining_logs_clauses -> begin
      match rvalue_computation first_logs_clause actor s with
      | ComputationProduces event ->
        let trace' = s.trace $:: event in
        let s' = { s with trace = trace' } in
        log_expressions_computation_memories_match_on_global_variables vs actor remaining_logs_clauses s'
      | _ -> ()
  end

let update_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   UpdateStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let stmt = step.action.program_statement.statement in
       let thread = s.threads actor in
       let dst = UpdateStatement?.dst stmt in
       let bypassing_write_buffer = UpdateStatement?.bypassing_write_buffer stmt in
       let new_value = ComputationProduces?.result $$ rvalue_computation (UpdateStatement?.src stmt) actor s in
       update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs dst actor thread.pc 0 bypassing_write_buffer new_value s
    end

#push-options "--z3rlimit 10"

let compare_and_swap_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   CompareAndSwapStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
    let ps = step.action.program_statement in
      let thread = s.threads actor in
      let stmt = ps.statement in
      let target = CompareAndSwapStatement?.target stmt in
      let old_val = CompareAndSwapStatement?.old_val stmt in
      let new_val = CompareAndSwapStatement?.new_val stmt in
      let optional_result = CompareAndSwapStatement?.optional_result stmt in
      let bypassing_write_buffer = CompareAndSwapStatement?.bypassing_write_buffer stmt in
      let target_value = ComputationProduces?.result $$ rvalue_computation target actor s in
      let old_value = ComputationProduces?.result $$ rvalue_computation old_val actor s in
      let new_value = ComputationProduces?.result $$ rvalue_computation new_val actor s in
      let target_ptr = ComputationProduces?.result $$ lvalue_computation target actor s in
      lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs target actor s;
      update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs target_ptr actor thread.pc 0 false new_value s;
      let swap = eqb target_value old_value in
      let s' = ComputationProduces?.result $$ (if swap then update_expression target actor thread.pc 0 false new_value s else return s) in
      match optional_result with
      | Some result ->
        let swap_value = ObjectValuePrimitive (PrimitiveBoxBool swap) in
        let result_ptr = ComputationProduces?.result $$ lvalue_computation result actor s in
        lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs result actor s;
        update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs result_ptr actor thread.pc 1 bypassing_write_buffer swap_value s'
      | _ -> ()
    end

#pop-options

#push-options "--z3rlimit 30"

let atomic_exchange_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   AtomicExchangeStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       let thread = s.threads actor in
       let old_val = AtomicExchangeStatement?.old_val stmt in
       let old_ptr = ComputationProduces?.result $$ lvalue_computation old_val actor s in
       let new_val = AtomicExchangeStatement?.new_val stmt in
       let new_value = ComputationProduces?.result $$ rvalue_computation new_val actor s in
       let target = AtomicExchangeStatement?.target stmt in
       let target_value = ComputationProduces?.result $$ rvalue_computation target actor s in
       let target_ptr = ComputationProduces?.result $$ lvalue_computation target actor s in

       let s' = ComputationProduces?.result $$ update_pointed_to_value old_ptr actor thread.pc 0 false target_value s in

       lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs old_val actor s;
       lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs target actor s;
       update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs old_ptr actor thread.pc 0 false target_value s;
       update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs target_ptr actor thread.pc 0 false new_value s'
    end

let create_thread_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   CreateThreadStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
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
             update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers) bypassing_write_buffer new_tid_value s
         else begin
           let new_thread = s.threads new_tid in
           let frame_uniq = create_thread_nd.frame_uniq in
           assert (~ (new_thread.status <> ThreadStatusNotStarted
                  || length new_thread.write_buffer <> 0
                  || list_contains frame_uniq s.uniqs_used));
           let parameter_values = ComputationProduces?.result $$ rvalues_computation parameter_expressions actor s in
           rvalues_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs parameter_expressions actor s;
           let s2 = make_thread_running method_id initial_pc new_tid frame_uniq s in
           assert (states_match_on_global_variables vs s s2);
           assert (state_well_formed vs s2);
           let s3 = ComputationProduces?.result $$ push_stack_parameters new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2 in
           push_stack_parameters_maintains_state_well_formed vs new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2;
           push_stack_parameters_memories_match_on_global_variables vs new_tid start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2;
           assert (states_match_on_global_variables vs s s3);
           assert (state_well_formed vs s3);
           let s4 = ComputationProduces?.result $$ push_stack_variables new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3 in
           push_stack_variables_maintains_state_well_formed vs new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3;
           push_stack_variables_memories_match_on_global_variables vs new_tid start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3;
           assert (states_match_on_global_variables vs s s4);
           assert (state_well_formed vs s4);
           match optional_result with
           | None -> ()
           | Some result ->
             let new_tid_value = ObjectValuePrimitive (PrimitiveBoxThreadId new_tid) in
             assert (global_variables_unaddressed_in_lvalue_expression vs result);
             update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs result actor start_pc (list_len parameter_var_ids + list_len local_variable_initializers) bypassing_write_buffer new_tid_value s4
         end
       | _ -> ()
    end

let method_call_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   MethodCallStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers stack_overflow ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let method_call_nd: method_call_nd_t = ObjectValueAbstract?.value (Cons?.hd step.nd) in
         let frame_uniq = method_call_nd.frame_uniq in
         assert (~ (list_contains frame_uniq s.uniqs_used));
         let parameter_values = ComputationProduces?.result $$ rvalues_computation parameter_expressions actor s in
         let s2 = push_stack_frame actor method_id return_pc frame_uniq s in
         assert (states_match_on_global_variables vs s s2);
         let s3 = ComputationProduces?.result $$ push_stack_parameters actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2 in
         push_stack_parameters_memories_match_on_global_variables vs actor start_pc 0 method_id frame_uniq parameter_var_ids parameter_values s2;
         let s4 = ComputationProduces?.result $$ push_stack_variables actor start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3 in
         push_stack_variables_memories_match_on_global_variables vs actor start_pc (list_len parameter_var_ids) method_id frame_uniq local_variable_initializers s3;
         ()
       | _ -> ()
    end

let return_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ReturnStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let output_values = ComputationProduces?.result $$ rvalues_computation output_srcs actor s in
         rvalues_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs output_srcs actor s;
         let mem' = ComputationProduces?.result $$ pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
         pop_stack_variables_memories_match_on_global_variables vs actor method_id thread.top.frame_uniq thread.top.local_variables s.mem;
         pop_stack_variables_maintains_state_well_formed vs actor method_id thread.top.frame_uniq thread.top.local_variables s;
         let s2 = pop_stack_frame actor mem' s in
         assert (states_match_on_global_variables vs s s2);
         update_expressions_with_gvars_unaddressed_in_both_values_memories_match_on_global_variables vs output_dsts actor start_pc 0 bypassing_write_buffer output_values s2
       | _ -> ()
    end

#pop-options

let terminate_thread_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   TerminateThreadStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | TerminateThreadStatement method_id ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let mem' = ComputationProduces?.result $$ pop_stack_variables actor method_id thread.top.frame_uniq thread.top.local_variables s.mem in
         pop_stack_variables_memories_match_on_global_variables vs actor method_id thread.top.frame_uniq thread.top.local_variables s.mem;
         pop_stack_variables_maintains_state_well_formed vs actor method_id thread.top.frame_uniq thread.top.local_variables s;
         let thread' = { thread with status = ThreadStatusJoinable } in
         let threads' = Spec.Map.upd s.threads actor thread' in
         let s' = { s with mem = mem'; threads = threads' } in
         assert (states_match_on_global_variables vs s s')
       | _ -> ()
    end

#push-options "--z3rlimit 30"

let alloc_successful_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   (MallocSuccessfulStatement? step.action.program_statement.statement || CallocSuccessfulStatement? step.action.program_statement.statement)
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count
       | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let count_value = ComputationProduces?.result $$ rvalue_computation count actor s in
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
           mark_allocation_root_allocated_state_well_formed vs uniq storage s;
           let p = ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot root_id) 0)) in
           update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs result actor start_pc 0 bypassing_write_buffer p s'
         | _ -> ()
       | _ -> ()
    end

#pop-options

let nondeterministic_update_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   NondeterministicUpdateStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | NondeterministicUpdateStatement bypassing_write_buffer dst ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let nd_value = Cons?.hd step.nd in
         update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs dst actor start_pc 0 bypassing_write_buffer nd_value s
       | _ -> ()
    end

let alloc_returning_null_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   (MallocReturningNullStatement? step.action.program_statement.statement || CallocReturningNullStatement? step.action.program_statement.statement)
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | MallocReturningNullStatement bypassing_write_buffer result count
       | CallocReturningNullStatement bypassing_write_buffer result count ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let p = ObjectValuePrimitive (PrimitiveBoxPointer PointerNull) in
         update_expression_with_gvars_unaddressed_in_lvalue_memories_match_on_global_variables vs result actor start_pc 0 bypassing_write_buffer p s
       | _ -> ()
    end

let somehow_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   SomehowStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         update_expressions_with_gvars_unaddressed_in_lvalues_and_lacking_pointer_field_memories_match_on_global_variables vs modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s
       | _ -> ()
    end

let rec external_method_take_snapshot_of_reads_clauses_computation_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (reads_clauses: list (var_id_t * expression_t))
  (s: Armada.State.t)
  : Lemma (requires True)
          (ensures otherwise True begin
                     let? s' = external_method_take_snapshot_of_reads_clauses_computation actor writer_pc writer_expression_number bypassing_write_buffer reads_clauses s in
                     return $$$ states_match_on_global_variables vs s s'
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
        match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer first_value s with
        | ComputationProduces s' ->
          update_pointed_to_value_with_gvars_unaddressed_memories_match_on_global_variables vs p actor writer_pc writer_expression_number bypassing_write_buffer first_value s;
          external_method_take_snapshot_of_reads_clauses_computation_memories_match_on_global_variables vs actor writer_pc (writer_expression_number + 1) bypassing_write_buffer remaining_reads_clauses s'
        | _ -> ()
      end
      | _ -> ()
    end
    | _ -> ()
  end

let external_method_start_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ExternalMethodStartStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer modifies_clauses reads_clauses ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let s2 = ComputationProduces?.result $$ update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s in
         update_expressions_with_gvars_unaddressed_in_lvalues_and_lacking_pointer_field_memories_match_on_global_variables vs modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s;
         external_method_take_snapshot_of_reads_clauses_computation_memories_match_on_global_variables vs actor start_pc (list_len modifies_clauses) bypassing_write_buffer reads_clauses s2
       | _ -> ()
    end

let external_method_middle_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ExternalMethodMiddleStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         let s2 = ComputationProduces?.result $$ update_expressions modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s in
         update_expressions_with_gvars_unaddressed_in_lvalues_and_lacking_pointer_field_memories_match_on_global_variables vs modifies_clauses actor start_pc 0 bypassing_write_buffer step.nd s;
         external_method_take_snapshot_of_reads_clauses_computation_memories_match_on_global_variables vs actor start_pc (list_len modifies_clauses) bypassing_write_buffer reads_clauses s2
       | _ -> ()
    end

let external_method_end_statement_memories_match_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   ExternalMethodEndStatement? step.action.program_statement.statement
                    /\ global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = if step.action.ok then begin
       let ps = step.action.program_statement in
       let stmt = ps.statement in
       match stmt with
       | ExternalMethodEndStatement ensures_cond logs_clauses ->
         let thread = s.threads actor in
         let start_pc = thread.pc in
         log_expressions_computation_memories_match_on_global_variables vs actor logs_clauses s
       | _ -> ()
    end

#push-options "--z3rlimit 30"

let global_variables_unmodifiable_by_statement_memories_matches_on_global_variables
  (vs: list var_id_t)
  (actor: tid_t)
  (step: Armada.Step.t)
  (starts_atomic_block ends_atomic_block: bool)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unmodifiable_by_statement vs step.action.program_statement.statement
                    /\ Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ state_well_formed vs s)
          (ensures  states_match_on_global_variables vs s (Some?.v $$ step_computation actor starts_atomic_block ends_atomic_block step s))
  = match step.action.program_statement.statement with
    | UpdateStatement bypassing_write_buffer dst src ->
      update_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | NondeterministicUpdateStatement bypassing_write_buffer dst ->
      nondeterministic_update_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
      compare_and_swap_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | AtomicExchangeStatement old_val target new_val ->
      atomic_exchange_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | CreateThreadStatement method_id initial_pc bypassing_write_buffer optional_result parameter_var_ids
                            parameter_expressions local_variable_initializers -> create_thread_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | MethodCallStatement method_id return_pc parameter_var_ids parameter_expressions local_variable_initializers
                          stack_overflow ->
      method_call_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | ReturnStatement method_id bypassing_write_buffer output_dsts output_srcs ->
      return_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | TerminateThreadStatement method_id ->
      terminate_thread_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | MallocSuccessfulStatement bypassing_write_buffer result allocation_td count
    | CallocSuccessfulStatement bypassing_write_buffer result allocation_td count ->
      alloc_successful_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | MallocReturningNullStatement bypassing_write_buffer result count
    | CallocReturningNullStatement bypassing_write_buffer result count ->
      alloc_returning_null_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | SomehowStatement undefined_unless_cond bypassing_write_buffer modifies_clauses ensures_cond ->
      somehow_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | ExternalMethodStartStatement await_cond undefined_unless_cond bypassing_write_buffer
                                   modifies_clauses reads_clauses ->
      external_method_start_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | ExternalMethodMiddleStatement bypassing_write_buffer modifies_clauses reads_clauses ->
      external_method_middle_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | ExternalMethodEndStatement ensures_cond logs_clauses ->
      external_method_end_statement_memories_match_on_global_variables vs actor step starts_atomic_block ends_atomic_block s
    | _ -> ()

#pop-options
