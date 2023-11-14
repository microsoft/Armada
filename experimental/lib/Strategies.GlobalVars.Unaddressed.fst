module Strategies.GlobalVars.Unaddressed

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
open Util.Seq
open Util.Trigger

let rec global_variables_unaddressed_in_storage_implies_unaddressed_in_object_value
  (vs: list var_id_t)
  (actor: tid_t)
  (storage: object_storage_t)
  : Lemma (requires global_variables_unaddressed_in_storage vs storage)
          (ensures  global_variables_unaddressed_in_object_value vs (object_storage_to_value actor storage))
          (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions -> ()
  | ObjectStoragePrimitive value -> ()
  | ObjectStorageStruct fields ->
      global_variables_unaddressed_in_storages_implies_unaddressed_in_object_values vs actor fields
  | ObjectStorageArray element_td elements ->
      global_variables_unaddressed_in_storages_implies_unaddressed_in_object_values vs actor elements
  | ObjectStorageAbstract ty value -> ()

and global_variables_unaddressed_in_storages_implies_unaddressed_in_object_values
  (vs: list var_id_t)
  (actor: tid_t)
  (storages: seq object_storage_t)
  : Lemma (requires global_variables_unaddressed_in_storages vs storages)
          (ensures  global_variables_unaddressed_in_object_value_seq vs
                      (map_refine (object_storage_to_value actor) storages))
          (decreases rank storages) =
  let values = map_refine (object_storage_to_value actor) storages in
  introduce forall value. contains values value ==> global_variables_unaddressed_in_object_value vs value
  with
    introduce _ ==> _
    with _.
      eliminate exists storage. contains storages storage /\ value == object_storage_to_value actor storage
      returns _
      with _. global_variables_unaddressed_in_storage_implies_unaddressed_in_object_value vs actor storage


let rec dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem)
          (ensures  (match dereference_computation p mem with
                     | ComputationProduces storage -> global_variables_unaddressed_in_storage vs storage
                     | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem

let dereference_as_td_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (td: object_td_t)
  (actor: tid_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem)
          (ensures  (match dereference_as_td_computation p td actor mem with
                     | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                     | _ -> True)) =
  dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs p mem;
  match dereference_computation p mem with
  | ComputationProduces storage ->
      global_variables_unaddressed_in_storage_implies_unaddressed_in_object_value vs actor storage
  | _ -> ()

#push-options "--z3rlimit 30"

let rec rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_rvalue_expression vs exp
                    /\ positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem)
          (ensures  (match rvalue_computation exp actor s with
                     | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                     | _ -> True))
          (decreases exp) =
  if not (expression_valid exp) then
    ()
  else
    match exp with
    | ExpressionConstant value -> ()
    | ExpressionGlobalVariable td var_id ->
        dereference_as_td_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs
          (PointerRoot (RootIdGlobal var_id)) td actor s.mem
    | ExpressionLocalVariable td var_id ->
        let thread = s.threads actor in
        if list_contains var_id thread.top.local_variables then
          dereference_as_td_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs
            (PointerRoot (RootIdStack actor thread.top.method_id thread.top.frame_uniq var_id)) td actor s.mem
        else
          ()
    | ExpressionUnaryOperator _ _ operator operand ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operand actor s
    | ExpressionBinaryOperator _ _ _ operator operand1 operand2 ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operand1 actor s;
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operand2 actor s
    | ExpressionIf _ cond operand_then operand_else ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs cond actor s;
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operand_then actor s;
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operand_else actor s
    | ExpressionDereference td ptr ->
        (match rvalue_computation ptr actor s with
         | ComputationProduces ptr_value ->
             let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
             dereference_as_td_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs p td actor
               s.mem
         | _ -> ())
    | ExpressionAddressOf obj ->
        lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs obj actor s
    | ExpressionPointerOffset ptr offset ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs ptr actor s
    | ExpressionFieldOf td obj field_id ->
        (match lvalue_computation obj actor s with
         | ComputationProduces obj_ptr ->
             dereference_as_td_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs
               (PointerField obj_ptr field_id) td actor s.mem
         | _ -> ())
    | ExpressionAllocated ptr ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs ptr actor s
    | ExpressionApplyFunction td operands return_type operand_types fn ->
        rvalues_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs operands actor s
    | ExpressionIfUndefined td potentially_unsafe safe_substitution ->
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs
          potentially_unsafe actor s;
        rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs
          safe_substitution actor s
    | ExpressionInitialTid -> ()
    | ExpressionUniqsUsed -> ()
    | ExpressionStopReason -> ()

and lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_lvalue_expression vs exp
                    /\ positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem)
          (ensures  (match lvalue_computation exp actor s with
                     | ComputationProduces p -> global_variables_unaddressed_in_pointer vs p
                     | _ -> True))
          (decreases exp) =
  match exp with
  | ExpressionGlobalVariable _ var_id -> ()
  | ExpressionLocalVariable _ var_id -> ()
  | ExpressionDereference _ ptr ->
      rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs ptr actor s
  | ExpressionFieldOf td obj field_id ->
      lvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs obj actor s
  | _ -> ()
  
and rvalues_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (requires   global_variables_unaddressed_in_rvalue_expressions vs exps
                    /\ positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem)
          (ensures  (match rvalues_computation exps actor s with
                     | ComputationProduces values -> global_variables_unaddressed_in_object_values vs values
                     | _ -> True))
          (decreases exps) =
  match exps with
  | [] -> ()
  | exp :: exps' ->
      rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs exp actor s;
      rvalues_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs exps' actor s

#pop-options
#push-options "--z3rlimit 20"

let update_storage_lacking_pointer_field_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (storage: valid_object_storage_t)
  (td: object_td_t)
  (new_value: valid_object_value_t td)
  : Lemma (requires object_td_lacks_pointer_field td)
          (ensures  (match update_storage p actor writer_pc writer_expression_number bypassing_write_buffer
                             storage new_value with
                     | ComputationProduces (optional_write_message, storage') ->
                         global_variables_unaddressed_in_storage vs storage'
                     | _ -> True)) =
  ()

let update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (storage: valid_object_storage_t)
  (new_value: object_value_t)
  : Lemma (requires   global_variables_unaddressed_in_storage vs storage
                    /\ global_variables_unaddressed_in_object_value vs new_value)
          (ensures  (match update_storage p actor writer_pc writer_expression_number bypassing_write_buffer
                             storage new_value with
                     | ComputationProduces (optional_write_message, storage') ->
                         global_variables_unaddressed_in_storage vs storage'
                     | _ -> True)) =
  ()

let rec object_storage_lacks_pointer_field_implies_gvars_unaddressed
  (vs: list var_id_t)
  (storage: valid_object_storage_t)
  : Lemma (requires object_td_lacks_pointer_field (object_storage_to_td storage))
          (ensures  global_variables_unaddressed_in_storage vs storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values _ -> ()
  | ObjectStoragePrimitive value -> ()
  | ObjectStorageStruct fields ->
      introduce forall field. contains fields field ==> global_variables_unaddressed_in_storage vs field
      with introduce _ ==> _
      with _. object_storage_lacks_pointer_field_implies_gvars_unaddressed vs field
  | ObjectStorageArray _ elements ->
      introduce forall element. contains elements element ==> global_variables_unaddressed_in_storage vs element
      with introduce _ ==> _
      with _. object_storage_lacks_pointer_field_implies_gvars_unaddressed vs element
  | ObjectStorageAbstract _ _ -> ()

let update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (storage: valid_object_storage_t)
  (idx: nat)
  (new_child: valid_object_storage_t{can_update_storage_child storage idx new_child})
  : Lemma (requires   global_variables_unaddressed_in_storage vs storage
                    /\ global_variables_unaddressed_in_storage vs new_child)
          (ensures  (let storage' = update_storage_child storage idx new_child in
                     global_variables_unaddressed_in_storage vs storage')) =
  ()

let rec update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_storage vs new_storage
                    /\ global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem)
          (ensures  (match update_pointer_directly p new_storage mem with
                     | ComputationProduces mem' ->
                           global_variables_unaddressed_in_memory vs mem'
                         /\ roots_match mem'
                     | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem;
      (match dereference_computation struct_ptr mem with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageStruct fields ->
                if   field_id >= length fields
                   || neqb (object_storage_to_td new_storage)
                          (object_storage_to_td (index fields field_id)) then
                  ()
                else
                  let new_parent = update_storage_child parent field_id new_storage in
                  update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed vs
                    parent field_id new_storage;
                  update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed vs
                    struct_ptr new_parent mem
            | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem;
      (match dereference_computation array_ptr mem with
       | ComputationProduces parent ->
           (match parent with
            | ObjectStorageArray element_td elements ->
                if   idx < 0
                   || idx >= length elements
                   || neqb (object_storage_to_td new_storage) element_td then
                  ()
                else
                  let new_parent = update_storage_child parent idx new_storage in
                  update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed vs parent idx new_storage;
                  update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed vs array_ptr new_parent mem
            | _ -> ())
       | _ -> ())

let update_pointer_with_object_lacking_pointer_field_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (td: object_td_t)
  (new_value: valid_object_value_t td)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem
                    /\ object_td_lacks_pointer_field td)
          (ensures  (match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value mem with
                     | ComputationProduces (optional_write_message, mem') ->
                           global_variables_unaddressed_in_memory vs mem'
                         /\ roots_match mem'
                    | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc
             writer_expression_number bypassing_write_buffer storage td new_value
       | _ -> ())
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem;
      (match dereference_computation struct_ptr mem with
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
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc
                     writer_expression_number bypassing_write_buffer field td new_value;
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer field new_value with
                    | ComputationProduces (write_message, new_field) ->
                        if (not (can_update_storage_child parent field_id new_field)) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent field_id new_field;
                          let new_parent = update_storage_child parent field_id new_field in
                          update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs struct_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem;
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
                   update_storage_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc
                     writer_expression_number bypassing_write_buffer element td new_value;
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer element new_value with
                    | ComputationProduces (write_message, new_element) ->
                        if not (can_update_storage_child parent idx new_element) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent idx new_element;
                          let new_parent = update_storage_child parent idx new_element in
                          update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs array_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())

let update_pointer_with_object_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem
                    /\ global_variables_unaddressed_in_object_value vs new_value)
          (ensures  (match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value mem with
                     | ComputationProduces (optional_write_message, mem') ->
                           global_variables_unaddressed_in_memory vs mem'
                         /\ roots_match mem'
                     | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
             writer_expression_number bypassing_write_buffer storage new_value
       | _ -> ())
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem;
      (match dereference_computation struct_ptr mem with
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
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
                     writer_expression_number bypassing_write_buffer field new_value;
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer field new_value with
                    | ComputationProduces (write_message, new_field) ->
                        if (not (can_update_storage_child parent field_id new_field)) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent field_id new_field;
                          let new_parent = update_storage_child parent field_id new_field in
                          update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs struct_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem;
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
                   update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
                     writer_expression_number bypassing_write_buffer element new_value;
                   (match update_storage p actor writer_pc writer_expression_number
                            bypassing_write_buffer element new_value with
                    | ComputationProduces (write_message, new_element) ->
                        if not (can_update_storage_child parent idx new_element) then
                          ()
                        else (
                          update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs parent idx new_element;
                          let new_parent = update_storage_child parent idx new_element in
                          update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed
                            vs array_ptr new_parent mem
                        )
                    | _ -> ()
                   ))
          | _ -> ())
       | _ -> ())

let update_pointed_to_value_lacking_pointer_field_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (td: object_td_t)
  (new_value: valid_object_value_t td)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ object_td_lacks_pointer_field td)
          (ensures  (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  update_pointer_with_object_lacking_pointer_field_maintains_gvars_unaddressed vs p actor writer_pc
    writer_expression_number bypassing_write_buffer td new_value s.mem;
  match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value s.mem with
  | ComputationProduces (optional_write_message, new_mem) ->
      (match optional_write_message with
       | Some write_message ->
           let thread = s.threads actor in
           let new_write_buffer = build thread.write_buffer write_message in
           let new_thread = { thread with write_buffer = new_write_buffer } in
           let new_threads = Spec.Map.upd s.threads actor new_thread in
           let s' = { s with mem = new_mem; threads = new_threads; } in
           assert (global_variables_unaddressed_in_memory vs s'.mem);
           assert (positions_valid_in_state s')
       | None ->
           let s' = { s with mem = new_mem; } in
           assert (global_variables_unaddressed_in_memory vs s'.mem);
           assert (positions_valid_in_state s')
       | _ -> false_elim()
      )
  | _ -> ()

let update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ global_variables_unaddressed_in_object_value vs new_value)
          (ensures  (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  update_pointer_with_object_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
    writer_expression_number bypassing_write_buffer new_value s.mem;
  match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value s.mem with
  | ComputationProduces (optional_write_message, new_mem) ->
      (match optional_write_message with
       | Some write_message ->
           let thread = s.threads actor in
           let new_write_buffer = build thread.write_buffer write_message in
           let new_thread = { thread with write_buffer = new_write_buffer } in
           let new_threads = Spec.Map.upd s.threads actor new_thread in
           let s' = { s with mem = new_mem; threads = new_threads; } in
           assert (global_variables_unaddressed_in_memory vs s'.mem);
           assert (positions_valid_in_state s');
           assert (roots_match s'.mem)
       | None ->
           let s' = { s with mem = new_mem; } in
           assert (global_variables_unaddressed_in_memory vs s'.mem);
           assert (positions_valid_in_state s');
           assert (roots_match s'.mem)
       | _ -> false_elim ()
      )
  | _ -> ()

let update_expression_lacking_pointer_field_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ object_td_lacks_pointer_field (expression_to_td exp))
          (ensures  (match update_expression exp actor writer_pc writer_expression_number
                             bypassing_write_buffer new_value s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else (
    let td = expression_to_td exp in
    match lvalue_computation exp actor s with
    | ComputationProduces p ->
        update_pointed_to_value_lacking_pointer_field_maintains_gvars_unaddressed vs p actor
          writer_pc writer_expression_number bypassing_write_buffer td new_value s;
        (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                 new_value s with
         | ComputationProduces s' -> ()
         | _ -> ())
    | _ -> ()
  )

let update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ global_variables_unaddressed_in_object_value vs new_value)
          (ensures  (match update_expression exp actor writer_pc writer_expression_number
                             bypassing_write_buffer new_value s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else (
    let td = expression_to_td exp in
    match lvalue_computation exp actor s with
    | ComputationProduces p ->
        update_pointed_to_value_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
          writer_expression_number bypassing_write_buffer new_value s;
        (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                 new_value s with
         | ComputationProduces s' -> ()
         | _ -> ())
    | _ -> ()
  )

let rec update_expressions_with_gvars_unaddressed_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ global_variables_unaddressed_in_object_values vs new_values)
          (ensures  (match update_expressions exps actor writer_pc writer_expression_number
                             bypassing_write_buffer new_values s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  match exps, new_values with
  | [], [] -> ()
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      update_expression_with_gvars_unaddressed_maintains_gvars_unaddressed vs first_exp actor writer_pc
        writer_expression_number bypassing_write_buffer first_new_value s;
      (match update_expression first_exp actor writer_pc writer_expression_number
               bypassing_write_buffer first_new_value s with
       | ComputationProduces s_next ->
           update_expressions_with_gvars_unaddressed_maintains_gvars_unaddressed vs
             remaining_exps actor writer_pc (writer_expression_number + 1)
             bypassing_write_buffer remaining_new_values s_next;
           (match update_expressions exps actor writer_pc writer_expression_number
                    bypassing_write_buffer new_values s with
            | ComputationProduces s' -> ()
            | _ -> ())
       | _ -> ())
  | _ -> ()

let rec update_expressions_lacking_pointer_field_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : Lemma (requires   positions_valid_in_state s
                    /\ global_variables_unaddressed_in_memory vs s.mem
                    /\ roots_match s.mem
                    /\ expressions_lack_pointer_field exps)
          (ensures  (match update_expressions exps actor writer_pc writer_expression_number
                             bypassing_write_buffer new_values s with
                     | ComputationProduces s' ->
                           positions_valid_in_state s'
                         /\ global_variables_unaddressed_in_memory vs s'.mem
                         /\ roots_match s'.mem
                     | _ -> True)) =
  match exps, new_values with
  | [], [] -> ()
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      update_expression_lacking_pointer_field_maintains_gvars_unaddressed vs first_exp actor writer_pc
        writer_expression_number bypassing_write_buffer first_new_value s;
      (match update_expression first_exp actor writer_pc writer_expression_number
               bypassing_write_buffer first_new_value s with
       | ComputationProduces s_next ->
           update_expressions_lacking_pointer_field_maintains_gvars_unaddressed vs remaining_exps actor
             writer_pc (writer_expression_number + 1) bypassing_write_buffer remaining_new_values s_next;
           (match update_expressions exps actor writer_pc writer_expression_number
                    bypassing_write_buffer new_values s with
            | ComputationProduces s' -> ()
            | _ -> ())
       | _ -> ())
  | _ -> ()

let propagate_write_message_maintains_gvars_unaddressed
  (vs: list var_id_t)
  (write_message: write_message_t)
  (receiver_tid: tid_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   global_variables_unaddressed_in_memory vs mem
                    /\ roots_match mem)
          (ensures  (match propagate_write_message write_message receiver_tid mem with
                     | ComputationProduces mem' ->
                           global_variables_unaddressed_in_memory vs mem'
                         /\ roots_match mem'
                     | _ -> True)) =
  let p = write_message.location in
  dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs p mem;
  match dereference_computation p mem with
  | ComputationProduces storage ->
      (match storage with
       | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
           if   primitive_td <> write_message.primitive_td
              || write_message.version >= length values
              || local_versions receiver_tid >= write_message.version then
             ()
           else
             let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message.version in
             let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values
                                 new_local_versions in
             if not (object_storage_valid new_storage) then
               ()
             else
               update_pointer_directly_with_gvars_unaddressed_maintains_gvars_unaddressed vs p new_storage mem
       | _ -> ()
     )
  | _ -> ()
