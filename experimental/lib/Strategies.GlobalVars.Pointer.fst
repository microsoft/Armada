module Strategies.GlobalVars.Pointer

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
open Strategies.GlobalVars
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Value
open Strategies.PCRelation
open Util.List
open Util.Nth
open Util.Seq
open Util.Trigger

#push-options "--z3rlimit 30"

let rec dereference_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_pointer vs p
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  dereference_computation p mem1 == dereference_computation p mem2
                    /\ (match dereference_computation p mem1 with
                       | ComputationProduces storage -> global_variables_unaddressed_in_storage vs storage
                       | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_doesnt_depend_on_global_variables vs struct_ptr mem1 mem2
  | PointerIndex array_ptr idx ->
      dereference_computation_doesnt_depend_on_global_variables vs array_ptr mem1 mem2

let dereference_as_td_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (td: object_td_t)
  (actor: tid_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_pointer vs p
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  dereference_as_td_computation p td actor mem1 == dereference_as_td_computation p td actor mem2
                    /\ (match dereference_as_td_computation p td actor mem1 with
                       | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                       | _ -> True)) =
  dereference_computation_doesnt_depend_on_global_variables vs p mem1 mem2;
  match dereference_computation p mem1 with
  | ComputationProduces storage ->
      global_variables_unaddressed_in_storage_implies_unaddressed_in_object_value vs actor storage
  | _ -> ()

#pop-options
#push-options "--z3rlimit 80"

let rec rvalue_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expression vs exp
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures  rvalue_computation exp actor s1 == rvalue_computation exp actor s2
                    /\ (match rvalue_computation exp actor s1 with
                       | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                       | _ -> True))
          (decreases exp) =
  if not (expression_valid exp) then
    ()
  else
    match exp with
    | ExpressionConstant value -> ()
    | ExpressionGlobalVariable td var_id ->
        dereference_as_td_computation_doesnt_depend_on_global_variables vs (PointerRoot (RootIdGlobal var_id)) td actor
          s1.mem s2.mem
    | ExpressionLocalVariable td var_id ->
        let thread = s1.threads actor in
        if list_contains var_id thread.top.local_variables then
          dereference_as_td_computation_doesnt_depend_on_global_variables vs
            (PointerRoot (RootIdStack actor thread.top.method_id thread.top.frame_uniq var_id)) td actor s1.mem s2.mem
        else
          ()
    | ExpressionUnaryOperator _ _ operator operand ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand actor s1 s2
    | ExpressionBinaryOperator _ _ _ operator operand1 operand2 ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand1 actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand2 actor s1 s2
    | ExpressionIf _ cond operand_then operand_else ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation cond actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand_then actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand_else actor s1 s2
    | ExpressionDereference td ptr ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2;
        (match rvalue_computation ptr actor s1 with
         | ComputationUndefined | ComputationImpossible -> ()
         | ComputationProduces ptr_value ->
             let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
             dereference_as_td_computation_doesnt_depend_on_global_variables vs p td actor s1.mem s2.mem)
    | ExpressionAddressOf obj ->
        lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2
    | ExpressionPointerOffset ptr offset ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation offset actor s1 s2;
        (match rvalue_computation ptr actor s1 with
         | ComputationUndefined | ComputationImpossible -> ()
         | ComputationProduces ptr_value ->
             (match rvalue_computation offset actor s1 with
              | ComputationUndefined | ComputationImpossible -> ()
              | ComputationProduces offset_value ->
                  let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
                  (match p with
                   | PointerIndex array_ptr idx ->
                       let offset_int = ObjectValueAbstract?.value offset_value in
                       dereference_computation_doesnt_depend_on_global_variables vs array_ptr s1.mem s2.mem
                   | _ -> ())))
    | ExpressionFieldOf td obj field_id ->
        lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2;
        (match lvalue_computation obj actor s1 with
         | ComputationProduces obj_ptr ->
             dereference_as_td_computation_doesnt_depend_on_global_variables vs (PointerField obj_ptr field_id)
               td actor s1.mem s2.mem
         | _ -> ())
    | ExpressionAllocated ptr ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2
    | ExpressionApplyFunction td operands return_type operand_types fn ->
        rvalues_computation_doesnt_depend_on_global_variables vs pc_relation operands actor s1 s2
    | ExpressionIfUndefined td potentially_unsafe safe_substitution ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation potentially_unsafe actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation safe_substitution actor s1 s2
    | ExpressionInitialTid -> ()
    | ExpressionUniqsUsed -> ()
    | ExpressionStopReason -> ()

and lvalue_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expression vs exp
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures    lvalue_computation exp actor s1 == lvalue_computation exp actor s2
                    /\ (match lvalue_computation exp actor s1 with
                       | ComputationProduces p -> global_variables_unaddressed_in_pointer vs p
                       | _ -> True))
          (decreases exp) =
  match exp with
  | ExpressionGlobalVariable _ var_id -> ()
  | ExpressionLocalVariable _ var_id -> ()
  | ExpressionDereference _ ptr ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2
  | ExpressionFieldOf td obj field_id ->
      lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2
  | _ -> ()
  
and rvalues_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exps: list expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expressions vs exps
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures  rvalues_computation exps actor s1 == rvalues_computation exps actor s2
                    /\ (match rvalues_computation exps actor s1 with
                       | ComputationProduces values -> global_variables_unaddressed_in_object_values vs values
                       | _ -> True))
          (decreases exps) =
  match exps with
  | [] -> ()
  | exp :: exps' ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2;
      rvalues_computation_doesnt_depend_on_global_variables vs pc_relation exps' actor s1 s2

#pop-options
#push-options "--z3rlimit 30"

let rec update_pointer_directly_with_gvars_unaddressed_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_pointer vs p
                    /\ global_variables_unaddressed_in_storage vs new_storage
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ memories_match_except_global_variables vs mem1 mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  (match update_pointer_directly p new_storage mem1, update_pointer_directly p new_storage mem2 with
                     | ComputationProduces mem1', ComputationProduces mem2' ->
                           global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ memories_match_except_global_variables vs mem1' mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_doesnt_depend_on_global_variables vs struct_ptr mem1 mem2;
      (match dereference_computation struct_ptr mem1 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageStruct fields ->
                if   field_id >= length fields
                   || neqb (object_storage_to_td new_storage)
                          (object_storage_to_td (index fields field_id)) then
                  ()
                else (
                  let new_parent = update_storage_child parent field_id new_storage in
                  update_pointer_directly_with_gvars_unaddressed_maintains_states_match vs struct_ptr
                    new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_doesnt_depend_on_global_variables vs array_ptr mem1 mem2;
      (match dereference_computation array_ptr mem1 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageArray element_td elements ->
                if   idx < 0
                   || idx >= length elements
                   || neqb (object_storage_to_td new_storage) element_td then
                  ()
                else (
                  let new_parent = update_storage_child parent idx new_storage in
                  update_pointer_directly_with_gvars_unaddressed_maintains_states_match
                    vs array_ptr new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())

let rec update_pointer_directly_s1_only_among_gvars_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   not (global_variables_unaddressed_in_pointer vs p)
                    /\ global_variables_unaddressed_in_storage vs new_storage
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ memories_match_except_global_variables vs mem1 mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  (match update_pointer_directly p new_storage mem1 with
                     | ComputationProduces mem1' ->
                           global_variables_unaddressed_in_memory vs mem1'
                         /\ memories_match_except_global_variables vs mem1' mem2
                         /\ roots_match mem1'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem1;
      (match dereference_computation struct_ptr mem1 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageStruct fields ->
                if   field_id >= length fields
                   || neqb (object_storage_to_td new_storage)
                          (object_storage_to_td (index fields field_id)) then
                  ()
                else (
                  let new_parent = update_storage_child parent field_id new_storage in
                  update_pointer_directly_s1_only_among_gvars_maintains_states_match vs struct_ptr
                    new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem1;
      (match dereference_computation array_ptr mem1 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageArray element_td elements ->
                if   idx < 0
                   || idx >= length elements
                   || neqb (object_storage_to_td new_storage) element_td then
                  ()
                else (
                  let new_parent = update_storage_child parent idx new_storage in
                  update_pointer_directly_s1_only_among_gvars_maintains_states_match
                    vs array_ptr new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())

let rec update_pointer_directly_s2_only_among_gvars_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   not (global_variables_unaddressed_in_pointer vs p)
                    /\ global_variables_unaddressed_in_storage vs new_storage
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ memories_match_except_global_variables vs mem1 mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  (match update_pointer_directly p new_storage mem2 with
                     | ComputationProduces mem2' ->
                           global_variables_unaddressed_in_memory vs mem2'
                         /\ memories_match_except_global_variables vs mem1 mem2'
                         /\ roots_match mem2'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem2;
      (match dereference_computation struct_ptr mem2 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageStruct fields ->
                if   field_id >= length fields
                   || neqb (object_storage_to_td new_storage)
                          (object_storage_to_td (index fields field_id)) then
                  ()
                else (
                  let new_parent = update_storage_child parent field_id new_storage in
                  update_pointer_directly_s2_only_among_gvars_maintains_states_match vs struct_ptr
                    new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem2;
      (match dereference_computation array_ptr mem2 with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageArray element_td elements ->
                if   idx < 0
                   || idx >= length elements
                   || neqb (object_storage_to_td new_storage) element_td then
                  ()
                else (
                  let new_parent = update_storage_child parent idx new_storage in
                  update_pointer_directly_s2_only_among_gvars_maintains_states_match
                    vs array_ptr new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())

#pop-options
#push-options "--z3rlimit 80"

let update_pointer_with_object_lacking_pointer_field_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (td: object_td_t)
  (new_value: valid_object_value_t td)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ object_td_lacks_pointer_field td
                    /\ global_variables_unaddressed_in_pointer vs p)
          (ensures  (match update_pointer p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                             new_value mem1,
                           update_pointer p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                             new_value mem2 with
                     | ComputationProduces (optional_write_message1, mem1'),
                       ComputationProduces (optional_write_message2, mem2') ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                         /\ (match optional_write_message1, optional_write_message2 with
                            | Some write_message1, Some write_message2 ->
                                write_messages_match write_message1 write_message2 
                            | None, None -> True
                            | _, _ -> False)
                    | ComputationImpossible, ComputationImpossible -> True
                    | ComputationUndefined, ComputationUndefined -> True
                    | _ -> False)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem1 root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc1
             writer_expression_number1 bypassing_write_buffer storage td new_value;
           update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc2
             writer_expression_number2 bypassing_write_buffer storage td new_value
       | _ -> ())
  | PointerField struct_ptr field_id ->
      dereference_computation_doesnt_depend_on_global_variables vs struct_ptr mem1 mem2;
      (match dereference_computation struct_ptr mem1 with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageStruct fields ->
               if field_id >= length fields then
                 ()
               else
                 let field = index fields field_id in
                 if not (object_storage_valid field) || neqb (object_storage_to_td field) td then
                   ()
                 else (
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc1
                     writer_expression_number1 bypassing_write_buffer field td new_value;
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc2
                     writer_expression_number2 bypassing_write_buffer field td new_value;
                   (match update_storage p actor writer_pc1 writer_expression_number1
                            bypassing_write_buffer field new_value,
                          update_storage p actor writer_pc2 writer_expression_number2
                            bypassing_write_buffer field new_value with
                    | ComputationProduces (write_message1, new_field1),
                      ComputationProduces (write_message2, new_field2) ->
                        assert (new_field1 == new_field2);
                        if (not (can_update_storage_child parent field_id new_field1)) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent field_id new_field1;
                          let new_parent = update_storage_child parent field_id new_field1 in
                          update_pointer_directly_with_gvars_unaddressed_maintains_states_match
                            vs struct_ptr new_parent mem1 mem2
                        )
                    | _, _ -> ()
                   ))
          | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_doesnt_depend_on_global_variables vs array_ptr mem1 mem2;
      (match dereference_computation array_ptr mem1 with
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
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc1
                     writer_expression_number1 bypassing_write_buffer element td new_value;
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc2
                     writer_expression_number2 bypassing_write_buffer element td new_value;
                   (match update_storage p actor writer_pc1 writer_expression_number1
                            bypassing_write_buffer element new_value,
                          update_storage p actor writer_pc2 writer_expression_number2
                            bypassing_write_buffer element new_value with
                    | ComputationProduces (write_message1, new_element1),
                      ComputationProduces (write_message2, new_element2) ->
                        assert (new_element1 == new_element2);
                        if not (can_update_storage_child parent idx new_element1) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent idx new_element1;
                          let new_parent = update_storage_child parent idx new_element1 in
                          update_pointer_directly_with_gvars_unaddressed_maintains_states_match
                            vs array_ptr new_parent mem1 mem2
                        )
                    | _, _ -> ()
                   ))
          | _ -> ())
       | _ -> ())

let update_pointer_with_object_with_gvars_unaddressed_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ global_variables_unaddressed_in_object_value vs new_value
                    /\ global_variables_unaddressed_in_pointer vs p)
          (ensures  (match update_pointer p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                             new_value mem1,
                           update_pointer p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                             new_value mem2 with
                     | ComputationProduces (optional_write_message1, mem1'),
                       ComputationProduces (optional_write_message2, mem2') ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                         /\ (match optional_write_message1, optional_write_message2 with
                            | Some write_message1, Some write_message2 ->
                                write_messages_match write_message1 write_message2 
                            | None, None -> True
                            | _, _ -> False)
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem1 root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc1
             writer_expression_number1 bypassing_write_buffer storage new_value;
           update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc2
             writer_expression_number2 bypassing_write_buffer storage new_value
       | _ -> ())
  | PointerField struct_ptr field_id ->
      dereference_computation_doesnt_depend_on_global_variables vs struct_ptr mem1 mem2;
      (match dereference_computation struct_ptr mem1 with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageStruct fields ->
               if field_id >= length fields then
                 ()
               else
                 let field = index fields field_id in
                 if   not (object_storage_valid field)
                    || neqb (object_storage_to_td field) (object_value_to_td new_value) then
                   ()
                 else (
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc1
                     writer_expression_number1 bypassing_write_buffer field new_value;
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc2
                     writer_expression_number2 bypassing_write_buffer field new_value;
                   (match update_storage p actor writer_pc1 writer_expression_number1
                            bypassing_write_buffer field new_value,
                          update_storage p actor writer_pc2 writer_expression_number2
                            bypassing_write_buffer field new_value with
                    | ComputationProduces (write_message1, new_field1),
                      ComputationProduces (write_message2, new_field2) ->
                        assert (new_field1 == new_field2);
                        if (not (can_update_storage_child parent field_id new_field1)) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent field_id new_field1;
                          let new_parent = update_storage_child parent field_id new_field1 in
                          update_pointer_directly_with_gvars_unaddressed_maintains_states_match
                            vs struct_ptr new_parent mem1 mem2
                        )
                    | _, _ -> ()
                   ))
          | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_doesnt_depend_on_global_variables vs array_ptr mem1 mem2;
      (match dereference_computation array_ptr mem1 with
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
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc1
                     writer_expression_number1 bypassing_write_buffer element new_value;
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc2
                     writer_expression_number2 bypassing_write_buffer element new_value;
                   (match update_storage p actor writer_pc1 writer_expression_number1
                            bypassing_write_buffer element new_value,
                          update_storage p actor writer_pc2 writer_expression_number2
                            bypassing_write_buffer element new_value with
                    | ComputationProduces (write_message1, new_element1),
                      ComputationProduces (write_message2, new_element2) ->
                        assert (new_element1 == new_element2);
                        if not (can_update_storage_child parent idx new_element1) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent idx new_element1;
                          let new_parent = update_storage_child parent idx new_element1 in
                          update_pointer_directly_with_gvars_unaddressed_maintains_states_match
                            vs array_ptr new_parent mem1 mem2
                        )
                    | _, _ -> ()
                   ))
          | _ -> ())
       | _ -> ())

#pop-options

let unread_write_buffer_commutes_with_append
  (threads: Armada.Threads.t{positions_valid_in_threads threads})
  (sender_tid: tid_t)
  (receiver_tid: tid_t)
  (write_message: write_message_t)
  : Lemma (requires positions_valid_in_threads threads)
          (ensures  (let threads' = append_to_thread_write_buffer threads sender_tid write_message in
                       positions_valid_in_threads threads'
                     /\ unread_write_buffer threads' sender_tid receiver_tid ==
                         build (unread_write_buffer threads sender_tid receiver_tid) write_message)) =
  assert (sender_receiver_trigger sender_tid receiver_tid)

let rec append_effect_on_remove_global_variables_from_write_buffer_list
  (vs: list var_id_t)
  (write_messages: list write_message_t)
  (write_message: write_message_t)
  : Lemma (ensures   remove_global_variables_from_write_buffer vs
                       (FStar.List.Tot.append write_messages [write_message])
                   == (if global_variables_unaddressed_in_write_message vs write_message then
                         FStar.List.Tot.append (remove_global_variables_from_write_buffer vs write_messages)
                           [write_message]
                       else 
                         remove_global_variables_from_write_buffer vs write_messages)) =
  match write_messages with
  | [] -> ()
  | hd :: tl -> append_effect_on_remove_global_variables_from_write_buffer_list vs tl write_message

let rec append_message_preserves_write_buffer_lists_match
  (write_buffer1: list write_message_t)
  (write_buffer2: list write_message_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  : Lemma (requires   write_buffers_match write_buffer1 write_buffer2
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (let write_buffer1' = FStar.List.Tot.append write_buffer1 [write_message1] in
                     let write_buffer2' = FStar.List.Tot.append write_buffer2 [write_message2] in
                     write_buffers_match write_buffer1' write_buffer2')) =
  match write_buffer1, write_buffer2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 -> append_message_preserves_write_buffer_lists_match tl1 tl2 write_message1 write_message2
  | _, _ -> false_elim()

let append_preserves_write_buffer_lists_match_except_global_variables
  (vs: list var_id_t)
  (write_buffer1: list write_message_t)
  (write_buffer2: list write_message_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  : Lemma (requires write_buffers_match (remove_global_variables_from_write_buffer vs write_buffer1)
                      (remove_global_variables_from_write_buffer vs write_buffer2)
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (let write_buffer1' = FStar.List.Tot.append write_buffer1 [write_message1] in
                     let write_buffer2' = FStar.List.Tot.append write_buffer2 [write_message2] in
                     write_buffers_match (remove_global_variables_from_write_buffer vs write_buffer1')
                       (remove_global_variables_from_write_buffer vs write_buffer2'))) =
  append_effect_on_remove_global_variables_from_write_buffer_list vs write_buffer1 write_message1;
  append_effect_on_remove_global_variables_from_write_buffer_list vs write_buffer2 write_message2;
  append_message_preserves_write_buffer_lists_match (remove_global_variables_from_write_buffer vs write_buffer1)
    (remove_global_variables_from_write_buffer vs write_buffer2) write_message1 write_message2

let append_preserves_write_buffers_match_except_global_variables
  (vs: list var_id_t)
  (write_buffer1: seq write_message_t)
  (write_buffer2: seq write_message_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  : Lemma (requires   write_buffers_match_except_global_variables vs write_buffer1 write_buffer2
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (let write_buffer1' = build write_buffer1 write_message1 in
                     let write_buffer2' = build write_buffer2 write_message2 in
                     write_buffers_match_except_global_variables vs write_buffer1' write_buffer2'))
          (decreases length write_buffer1 + length write_buffer2) =
  build_equivalent_to_append write_buffer1 write_message1;
  build_equivalent_to_append write_buffer2 write_message2;
  append_preserves_write_buffer_lists_match_except_global_variables vs (seq_to_list write_buffer1)
    (seq_to_list write_buffer2) write_message1 write_message2

let adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffer_matches_for_actor
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  (receiver_tid: tid_t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ global_variables_unaddressed_in_write_message vs write_message1
                    /\ write_messages_match write_message1 write_message2
                    /\ positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message1 in
                     let threads2' = append_to_thread_write_buffer threads2 actor write_message2 in
                       positions_valid_in_threads threads1'
                     /\ positions_valid_in_threads threads2'
                     /\ write_buffers_match_except_global_variables vs
                         (unread_write_buffer threads1' actor receiver_tid)
                         (unread_write_buffer threads2' actor receiver_tid))) =
  assert (sender_receiver_trigger actor receiver_tid);
  append_preserves_write_buffers_match_except_global_variables vs
    (unread_write_buffer threads1 actor receiver_tid)
    (unread_write_buffer threads2 actor receiver_tid)
    write_message1
    write_message2;
  unread_write_buffer_commutes_with_append threads1 actor receiver_tid write_message1;
  unread_write_buffer_commutes_with_append threads2 actor receiver_tid write_message2

#push-options "--z3rlimit 20"

let adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffer_matches
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  (sender_tid: tid_t)
  (receiver_tid: tid_t)
  : Lemma (requires   global_variables_unaddressed_in_write_message vs write_message1
                    /\ write_messages_match write_message1 write_message2
                    /\ positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message1 in
                     let threads2' = append_to_thread_write_buffer threads2 actor write_message2 in
                      positions_valid_in_threads threads1'
                     /\ positions_valid_in_threads threads2'
                     /\ (write_buffers_match_except_global_variables vs
                         (unread_write_buffer threads1' sender_tid receiver_tid)
                         (unread_write_buffer threads2' sender_tid receiver_tid)))) =
  if sender_tid <> actor then
    assert (sender_receiver_trigger sender_tid receiver_tid)
  else
    adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffer_matches_for_actor vs pc_relation
      actor write_message1 write_message2 threads1 threads2 receiver_tid

#pop-options

let adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffers_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ global_variables_unaddressed_in_write_message vs write_message1
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message1 in
                     let threads2' = append_to_thread_write_buffer threads2 actor write_message2 in
                       positions_valid_in_threads threads1'
                     /\ positions_valid_in_threads threads2'
                     /\ positions_in_write_buffers_match_except_global_variables vs threads1' threads2')) =
  let threads1' = append_to_thread_write_buffer threads1 actor write_message1 in
  let threads2' = append_to_thread_write_buffer threads2 actor write_message2 in
  introduce forall sender_tid receiver_tid.
               write_buffers_match_except_global_variables vs
                 (unread_write_buffer threads1' sender_tid receiver_tid)
                 (unread_write_buffer threads2' sender_tid receiver_tid)
  with adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffer_matches vs pc_relation actor
         write_message1 write_message2 threads1 threads2 sender_tid receiver_tid

let adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffers_match_and_positions_valid
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ global_variables_unaddressed_in_write_message vs write_message1
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message1 in
                     let threads2' = append_to_thread_write_buffer threads2 actor write_message2 in
                       positions_valid_in_threads threads1'
                     /\ positions_valid_in_threads threads2'
                     /\ positions_in_write_buffers_match_except_global_variables vs threads1' threads2')) =
  adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffers_match vs pc_relation actor
    write_message1 write_message2 threads1 threads2

#push-options "--z3rlimit 50"

let update_pointed_to_value_lacking_pointer_field_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (td: object_td_t)
  (new_value: valid_object_value_t td)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ object_td_lacks_pointer_field td
                    /\ global_variables_unaddressed_in_pointer vs p)
          (ensures  (match update_pointed_to_value p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                             new_value s1,
                           update_pointed_to_value p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                             new_value s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  update_pointer_with_object_lacking_pointer_field_maintains_states_match vs p actor writer_pc1 writer_pc2
    writer_expression_number1 writer_expression_number2 bypassing_write_buffer td new_value s1.mem s2.mem;
  match update_pointer p actor writer_pc1 writer_expression_number1 bypassing_write_buffer new_value s1.mem,
        update_pointer p actor writer_pc2 writer_expression_number2 bypassing_write_buffer new_value s2.mem with
  | ComputationProduces (optional_write_message1, new_mem1), ComputationProduces (optional_write_message2, new_mem2) ->
      (match optional_write_message1, optional_write_message2 with
       | Some write_message1, Some write_message2 ->
           let thread1 = s1.threads actor in
           let new_write_buffer1 = build thread1.write_buffer write_message1 in
           let new_thread1 = { thread1 with write_buffer = new_write_buffer1 } in
           let new_threads1 = Spec.Map.upd s1.threads actor new_thread1 in
           let s1' = { s1 with mem = new_mem1; threads = new_threads1; } in
           let s2' = ComputationProduces?.result (update_pointed_to_value p actor writer_pc2 writer_expression_number2
                                                    bypassing_write_buffer new_value s2) in
           adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffers_match_and_positions_valid
             vs pc_relation actor write_message1 write_message2 s1.threads s2.threads;
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (global_variables_unaddressed_in_memory vs s2'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2')
       | None, None ->
           let s1' = { s1 with mem = new_mem1; } in
           let s2' = ComputationProduces?.result (update_pointed_to_value p actor writer_pc2 writer_expression_number2
                                                    bypassing_write_buffer new_value s2) in
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (global_variables_unaddressed_in_memory vs s2'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2')
       | _, _ -> false_elim()
      )
  | _, _ -> ()

let update_pointed_to_value_with_gvars_unaddressed_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ global_variables_unaddressed_in_object_value vs new_value
                    /\ global_variables_unaddressed_in_pointer vs p)
          (ensures  (match update_pointed_to_value p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                             new_value s1,
                           update_pointed_to_value p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                             new_value s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  update_pointer_with_object_with_gvars_unaddressed_maintains_states_match vs p actor writer_pc1 writer_pc2
    writer_expression_number1 writer_expression_number2 bypassing_write_buffer new_value s1.mem s2.mem;
  match update_pointer p actor writer_pc1 writer_expression_number1 bypassing_write_buffer new_value s1.mem,
        update_pointer p actor writer_pc2 writer_expression_number2 bypassing_write_buffer new_value s2.mem with
  | ComputationProduces (optional_write_message1, new_mem1), ComputationProduces (optional_write_message2, new_mem2) ->
      (match optional_write_message1, optional_write_message2 with
       | Some write_message1, Some write_message2 ->
           let thread = s1.threads actor in
           let new_write_buffer = build thread.write_buffer write_message1 in
           let new_thread = { thread with write_buffer = new_write_buffer } in
           let new_threads = Spec.Map.upd s1.threads actor new_thread in
           let s1' = { s1 with mem = new_mem1; threads = new_threads; } in
           let s2' = ComputationProduces?.result (update_pointed_to_value p actor writer_pc2 writer_expression_number2
                                                    bypassing_write_buffer new_value s2) in
           adding_write_message_unaddressing_gvars_maintains_positions_in_write_buffers_match_and_positions_valid
             vs pc_relation actor write_message1 write_message2 s1.threads s2.threads;
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (global_variables_unaddressed_in_memory vs s2'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2');
           assert (roots_match s1'.mem);
           assert (roots_match s2'.mem)
       | None, None ->
           let s1' = { s1 with mem = new_mem1; } in
           let s2' = ComputationProduces?.result (update_pointed_to_value p actor writer_pc2 writer_expression_number2
                                                    bypassing_write_buffer new_value s2) in
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (global_variables_unaddressed_in_memory vs s2'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2');
           assert (roots_match s1'.mem);
           assert (roots_match s2'.mem)
       | _, _ -> false_elim ()
      )
  | _, _ -> ()

#pop-options
