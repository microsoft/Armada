module Strategies.GlobalVars

open Armada.Base
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.PCRelation
open Util.List
open Util.Relation
open Util.Seq

let global_variables_unmentioned_in_root_id (vs: list var_id_t) (root_id: root_id_t) : GTot bool =
  match root_id with
  | RootIdGlobal var_id -> not (FStar.List.Tot.contains var_id vs)
  | _ -> true

let rec global_variables_unaddressed_in_pointer (vs: list var_id_t) (ptr: Armada.Pointer.t) : GTot bool =
  match ptr with
  | PointerUninitialized -> true
  | PointerNull -> true
  | PointerRoot root_id -> global_variables_unmentioned_in_root_id vs root_id
  | PointerField struct_ptr _ -> global_variables_unaddressed_in_pointer vs struct_ptr
  | PointerIndex array_ptr _ -> global_variables_unaddressed_in_pointer vs array_ptr

let global_variables_unaddressed_in_box (vs: list var_id_t) (box: primitive_box_t) : GTot bool =
  match box with
  | PrimitiveBoxPointer ptr -> global_variables_unaddressed_in_pointer vs ptr
  | _ -> true

let global_variables_unaddressed_in_boxes (vs: list var_id_t) (boxes: seq primitive_box_t) : GTot bool =
  for_all_seq (global_variables_unaddressed_in_box vs) boxes

let global_variables_unaddressed_in_boxes_equivalent_to_forall (vs: list var_id_t) (boxes: seq primitive_box_t)
  : Lemma (ensures global_variables_unaddressed_in_boxes vs boxes <==>
                   (forall box. contains boxes box ==> global_variables_unaddressed_in_box vs box))
          [SMTPat (global_variables_unaddressed_in_boxes vs boxes)] =
  for_all_seq_equivalent_to_forall_seq_ubool (global_variables_unaddressed_in_box vs) boxes

let rec global_variables_unaddressed_in_object_value (vs: list var_id_t) (value: object_value_t)
  : GTot bool (decreases rank value) =
  all_seq_facts_lemma ();
  match value with
  | ObjectValuePrimitive value -> global_variables_unaddressed_in_box vs value
  | ObjectValueStruct fields -> global_variables_unaddressed_in_object_value_seq vs fields
  | ObjectValueArray _ elements -> global_variables_unaddressed_in_object_value_seq vs elements
  | ObjectValueAbstract _ _ -> true

and global_variables_unaddressed_in_object_value_seq (vs: list var_id_t) (values: seq object_value_t)
  : GTot bool (decreases rank values) =
  all_seq_facts_lemma ();
  if length values = 0 then
    true
  else (
       global_variables_unaddressed_in_object_value vs (index values 0)
    && global_variables_unaddressed_in_object_value_seq vs (drop values 1)
  )

let rec global_variables_unaddressed_in_object_value_seq_equivalent_to_forall
  (vs: list var_id_t)
  (values: seq object_value_t)
  : Lemma (ensures global_variables_unaddressed_in_object_value_seq vs values <==>
                   (forall value. contains values value ==> global_variables_unaddressed_in_object_value vs value))
          (decreases rank values)
          [SMTPat (global_variables_unaddressed_in_object_value_seq vs values)] =
  all_seq_facts_lemma ();
  if length values = 0 then
    ()
  else
    global_variables_unaddressed_in_object_value_seq_equivalent_to_forall vs (drop values 1)

let global_variables_unaddressed_in_object_values (vs: list var_id_t) (values: list object_value_t)
  : GTot bool =
  for_all_ghost (global_variables_unaddressed_in_object_value vs) values

let global_variables_unaddressed_in_object_values_equivalent_to_forall (vs: list var_id_t) (values: list object_value_t)
  : Lemma (ensures global_variables_unaddressed_in_object_values vs values <==>
                   (forall value. contains_ubool value values ==> global_variables_unaddressed_in_object_value vs value))
          [SMTPat (global_variables_unaddressed_in_object_values vs values)] =
  for_all_ghost_equivalent_to_forall (global_variables_unaddressed_in_object_value vs) values

let global_variables_unaddressed_in_initializer (vs: list var_id_t) (initializer: initializer_t)
  : GTot bool =
  match initializer.iv with
  | InitializerArbitrary _ -> true
  | InitializerSpecific value -> global_variables_unaddressed_in_object_value vs value

let global_variables_unaddressed_in_initializers (vs: list var_id_t) (initializers: list initializer_t)
  : GTot bool =
  for_all_ghost (global_variables_unaddressed_in_initializer vs) initializers

let global_variables_unaddressed_in_initializers_equivalent_to_forall
  (vs: list var_id_t)
  (initializers: list initializer_t)
  : Lemma (ensures global_variables_unaddressed_in_initializers vs initializers <==>
                   (forall initializer. contains_ubool initializer initializers ==>
                                   global_variables_unaddressed_in_initializer vs initializer))
          [SMTPat (global_variables_unaddressed_in_initializers vs initializers)] =
  for_all_ghost_equivalent_to_forall (global_variables_unaddressed_in_initializer vs) initializers

let rec global_variables_unaddressed_in_rvalue_expression (vs: list var_id_t) (e: expression_t)
  : GTot bool =
  match e with
  | ExpressionConstant value -> global_variables_unaddressed_in_object_value vs value
  | ExpressionGlobalVariable _ var_id -> true
  | ExpressionLocalVariable _ _ -> true
  | ExpressionUnaryOperator _ _ _ operand -> global_variables_unaddressed_in_rvalue_expression vs operand
  | ExpressionBinaryOperator _ _ _ _ operand1 operand2 ->
        global_variables_unaddressed_in_rvalue_expression vs operand1
      && global_variables_unaddressed_in_rvalue_expression vs operand2
  | ExpressionIf _ cond operand_then operand_else ->
         global_variables_unaddressed_in_rvalue_expression vs cond
      && global_variables_unaddressed_in_rvalue_expression vs operand_then
      && global_variables_unaddressed_in_rvalue_expression vs operand_else
  | ExpressionDereference _ _ -> true
  | ExpressionAddressOf obj -> global_variables_unaddressed_in_lvalue_expression vs obj
  | ExpressionPointerOffset ptr offset -> global_variables_unaddressed_in_rvalue_expression vs ptr
  | ExpressionFieldOf _ _ _ -> true
  | ExpressionAllocated ptr -> global_variables_unaddressed_in_rvalue_expression vs ptr
  | ExpressionApplyFunction _ operands _ _ _ -> global_variables_unaddressed_in_rvalue_expressions vs operands
  | ExpressionIfUndefined _ potentially_unsafe safe_substitution ->
         global_variables_unaddressed_in_rvalue_expression vs potentially_unsafe
      && global_variables_unaddressed_in_rvalue_expression vs safe_substitution
  | ExpressionInitialTid -> true
  | ExpressionUniqsUsed -> true
  | ExpressionStopReason -> true

and global_variables_unaddressed_in_lvalue_expression (vs: list var_id_t) (e: expression_t) : GTot bool =
  match e with
  | ExpressionGlobalVariable _ var_id -> not (FStar.List.Tot.contains var_id vs)
  | ExpressionDereference _ ptr -> global_variables_unaddressed_in_rvalue_expression vs ptr
  | ExpressionFieldOf td obj field_id -> global_variables_unaddressed_in_lvalue_expression vs obj
  | _ -> true

and global_variables_unaddressed_in_rvalue_expressions (vs: list var_id_t) (es: list expression_t)
  : GTot bool =
  match es with
  | [] -> true
  | e :: es' ->
         global_variables_unaddressed_in_rvalue_expression vs e
      && global_variables_unaddressed_in_rvalue_expressions vs es'

and global_variables_unaddressed_in_lvalue_expressions (vs: list var_id_t) (es: list expression_t)
  : GTot bool =
  match es with
  | [] -> true
  | e :: es' ->
         global_variables_unaddressed_in_lvalue_expression vs e
      && global_variables_unaddressed_in_lvalue_expressions vs es'

let rec global_variables_unaddressed_in_rvalue_expressions_equivalent_to_forall
  (vs: list var_id_t)
  (es: list expression_t)
  : Lemma (ensures global_variables_unaddressed_in_rvalue_expressions vs es <==>
                   (forall e. contains_ubool e es ==> global_variables_unaddressed_in_rvalue_expression vs e))
          [SMTPat (global_variables_unaddressed_in_rvalue_expressions vs es)] =
  match es with
  | [] -> ()
  | e :: es' -> global_variables_unaddressed_in_rvalue_expressions_equivalent_to_forall vs es'

let rec global_variables_unaddressed_in_lvalue_expressions_equivalent_to_forall
  (vs: list var_id_t)
  (es: list expression_t)
  : Lemma (ensures global_variables_unaddressed_in_lvalue_expressions vs es <==>
                   (forall e. contains_ubool e es ==> global_variables_unaddressed_in_lvalue_expression vs e))
          [SMTPat (global_variables_unaddressed_in_lvalue_expressions vs es)] =
  match es with
  | [] -> ()
  | e :: es' -> global_variables_unaddressed_in_lvalue_expressions_equivalent_to_forall vs es'

let global_variables_unaddressed_in_optional_lvalue_expression
  (vs: list var_id_t)
  (oe: option expression_t)
  : GTot bool =
  match oe with
  | None -> true
  | Some e -> global_variables_unaddressed_in_lvalue_expression vs e

let rec global_variables_unmentioned_in_expression (vs: list var_id_t) (e: expression_t)
  : GTot bool =
  match e with
  | ExpressionConstant value -> global_variables_unaddressed_in_object_value vs value
  | ExpressionGlobalVariable _ var_id -> not (FStar.List.Tot.contains var_id vs)
  | ExpressionLocalVariable _ var_id -> true
  | ExpressionUnaryOperator _ _ _ operand -> global_variables_unmentioned_in_expression vs operand
  | ExpressionBinaryOperator _ _ _ _ operand1 operand2 ->
         global_variables_unmentioned_in_expression vs operand1
      && global_variables_unmentioned_in_expression vs operand2
  | ExpressionIf _ cond operand_then operand_else ->
         global_variables_unmentioned_in_expression vs cond
      && global_variables_unmentioned_in_expression vs operand_then
      && global_variables_unmentioned_in_expression vs operand_else
  | ExpressionDereference _ ptr -> global_variables_unmentioned_in_expression vs ptr
  | ExpressionAddressOf obj -> global_variables_unmentioned_in_expression vs obj
  | ExpressionPointerOffset ptr offset ->
         global_variables_unmentioned_in_expression vs ptr
      && global_variables_unmentioned_in_expression vs offset
  | ExpressionFieldOf _ obj _ -> global_variables_unmentioned_in_expression vs obj
  | ExpressionAllocated ptr -> global_variables_unmentioned_in_expression vs ptr
  | ExpressionApplyFunction _ operands _ _ _ -> global_variables_unmentioned_in_expressions vs operands
  | ExpressionIfUndefined _ potentially_unsafe safe_substitution ->
         global_variables_unmentioned_in_expression vs potentially_unsafe
      && global_variables_unmentioned_in_expression vs safe_substitution
  | ExpressionInitialTid -> true
  | ExpressionUniqsUsed -> true
  | ExpressionStopReason -> true

and global_variables_unmentioned_in_expressions (vs: list var_id_t) (es: list expression_t)
  : GTot bool =
  match es with
  | [] -> true
  | e :: es' -> global_variables_unmentioned_in_expression vs e && global_variables_unmentioned_in_expressions vs es'

let rec global_variables_unmentioned_in_expressions_equivalent_to_forall (vs: list var_id_t) (es: list expression_t)
  : Lemma (ensures global_variables_unmentioned_in_expressions vs es <==>
                   (forall e. contains_ubool e es ==> global_variables_unmentioned_in_expression vs e))
          [SMTPat (global_variables_unmentioned_in_expressions vs es)] =
  match es with
  | [] -> ()
  | e :: es' -> global_variables_unmentioned_in_expressions_equivalent_to_forall vs es'

let global_variables_unmentioned_in_optional_expression (vs: list var_id_t) (oe: option expression_t)
  : GTot bool =
  match oe with
  | None -> true
  | Some e -> global_variables_unmentioned_in_expression vs e

let global_variables_unaddressed_in_reads_clause
  (vs: list var_id_t)
  (reads_clause: var_id_t * expression_t)
  : GTot bool =
  global_variables_unaddressed_in_rvalue_expression vs (snd reads_clause)

let global_variables_unaddressed_in_reads_clauses
  (vs: list var_id_t)
  (reads_clauses: list (var_id_t * expression_t))
  : GTot bool =
  for_all_ghost (global_variables_unaddressed_in_reads_clause vs) reads_clauses

let global_variables_unmentioned_in_reads_clause
  (vs: list var_id_t)
  (reads_clause: var_id_t * expression_t)
  : GTot bool =
  global_variables_unmentioned_in_expression vs (snd reads_clause)

let global_variables_unmentioned_in_reads_clauses
  (vs: list var_id_t)
  (reads_clauses: list (var_id_t * expression_t))
  : GTot bool =
  for_all_ghost (global_variables_unmentioned_in_reads_clause vs) reads_clauses

let rec object_td_lacks_pointer_field (td: object_td_t) : GTot bool (decreases rank td) =
  all_seq_facts_lemma ();
  match td with
  | ObjectTDPrimitive primitive_td -> not (PrimitiveTDPointer? primitive_td)
  | ObjectTDStruct field_tds -> object_tds_lack_pointer_field field_tds
  | ObjectTDArray element_td _ -> object_td_lacks_pointer_field element_td
  | ObjectTDAbstract _ -> true

and object_tds_lack_pointer_field (tds: seq object_td_t) : GTot bool (decreases rank tds) =
  all_seq_facts_lemma ();
    length tds = 0
  || (   object_td_lacks_pointer_field (index tds 0)
     && object_tds_lack_pointer_field (drop tds 1))

let rec object_tds_lack_pointer_field_equivalent_to_forall (tds: seq object_td_t)
  : Lemma (ensures object_tds_lack_pointer_field tds <==>
                     (forall td. contains tds td ==> object_td_lacks_pointer_field td))
          (decreases rank tds)
          [SMTPat (object_tds_lack_pointer_field tds)] =
  all_seq_facts_lemma ();
  if length tds = 0 then
    ()
  else
    object_tds_lack_pointer_field_equivalent_to_forall (drop tds 1)

let expression_lacks_pointer_field (e: expression_t) : GTot bool =
  object_td_lacks_pointer_field (expression_to_td e)

let expressions_lack_pointer_field (es: list expression_t) : GTot bool =
  for_all_ghost expression_lacks_pointer_field es

let global_variables_unaddressed_at_top_level_in_rvalue_expression
  (vs: list var_id_t)
  (e: expression_t)
  : GTot bool =
    global_variables_unaddressed_in_rvalue_expression vs e
  || expression_lacks_pointer_field e

let global_variables_unaddressed_at_top_level_in_rvalue_expressions
  (vs: list var_id_t)
  (es: list expression_t)
  : GTot bool =
  for_all_ghost (global_variables_unaddressed_at_top_level_in_rvalue_expression vs) es

let global_variables_unaddressed_at_top_level_in_optional_rvalue_expression
  (vs: list var_id_t)
  (oe: option expression_t)
  : GTot bool =
  match oe with
  | None -> true
  | Some e -> global_variables_unaddressed_at_top_level_in_rvalue_expression vs e

let global_variables_unmodifiable_by_statement
  (vs: list var_id_t)
  (statement: Armada.Statement.t)
  : GTot bool =
  match statement with
  | UpdateStatement _ dst _ -> global_variables_unaddressed_in_lvalue_expression vs dst
  | NondeterministicUpdateStatement _ dst -> global_variables_unaddressed_in_lvalue_expression vs dst
  | PropagateWriteMessageStatement -> false
  | CompareAndSwapStatement target _ _ _ optional_result ->
         global_variables_unaddressed_in_lvalue_expression vs target
      && global_variables_unaddressed_in_optional_lvalue_expression vs optional_result
  | AtomicExchangeStatement old_val target _ ->
         global_variables_unaddressed_in_lvalue_expression vs old_val
      && global_variables_unaddressed_in_lvalue_expression vs target
  | CreateThreadStatement _ _ _ optional_result _ parameter_expressions local_variable_initializers ->
      global_variables_unaddressed_in_optional_lvalue_expression vs optional_result
      && global_variables_unaddressed_in_rvalue_expressions vs parameter_expressions
      && global_variables_unaddressed_in_initializers vs local_variable_initializers
  | ReturnStatement _ _ output_dsts output_srcs ->
         global_variables_unaddressed_in_lvalue_expressions vs output_dsts
      && global_variables_unaddressed_in_rvalue_expressions vs output_srcs
  | MallocSuccessfulStatement _ result _ _ ->
      global_variables_unaddressed_in_lvalue_expression vs result
  | MallocReturningNullStatement _ result _ ->
      global_variables_unaddressed_in_lvalue_expression vs result
  | CallocSuccessfulStatement _ result _ _ ->
      global_variables_unaddressed_in_lvalue_expression vs result
  | CallocReturningNullStatement _ result _ ->
      global_variables_unaddressed_in_lvalue_expression vs result
  | SomehowStatement _ _ modifies_clauses _ ->
         global_variables_unaddressed_in_lvalue_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
  | ExternalMethodStartStatement _ _ _ modifies_clauses _ ->
         global_variables_unaddressed_in_lvalue_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
  | ExternalMethodMiddleStatement _ modifies_clauses _ ->
         global_variables_unaddressed_in_lvalue_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
  | _ -> true

let global_variables_unaddressable_in_statement
  (vs: list var_id_t)
  (statement: Armada.Statement.t)
  : GTot bool =
  match statement with
  | UpdateStatement _ dst src ->
       global_variables_unaddressed_at_top_level_in_rvalue_expression vs src
  | NondeterministicUpdateStatement _ dst ->
       expression_lacks_pointer_field dst
  | CompareAndSwapStatement target _ new_val _ optional_result ->
         global_variables_unaddressed_at_top_level_in_rvalue_expression vs new_val
  | AtomicExchangeStatement _ _ new_val ->
         global_variables_unaddressed_at_top_level_in_rvalue_expression vs new_val
  | CreateThreadStatement _ _ _ _ parameter_var_ids parameter_expressions
                          local_variable_initializers ->
         global_variables_unaddressed_at_top_level_in_rvalue_expressions vs parameter_expressions
      && global_variables_unaddressed_in_initializers vs local_variable_initializers
  | MethodCallStatement _ _ parameter_var_ids parameter_expressions local_variable_initializers _ ->
         global_variables_unaddressed_at_top_level_in_rvalue_expressions vs parameter_expressions
      && global_variables_unaddressed_in_initializers vs local_variable_initializers
  | ReturnStatement _ _ output_dsts output_srcs ->
      global_variables_unaddressed_at_top_level_in_rvalue_expressions vs output_srcs

  // For SomehowStatement, we have no idea what's put into the
  // destinations specified in modifies clauses.  So all we can do is
  // make sure that none of those destinations has any pointer fields.
  
  | SomehowStatement _ _ modifies_clauses _ ->
      expressions_lack_pointer_field modifies_clauses

  // For ExternalMethodStartStatement and
  // ExternalMethodMiddleStatement, we have no idea what's put into
  // the destinations specified in modifies clauses.  So all we can do
  // is make sure that none of those destinations has any pointer
  // fields.

  | ExternalMethodStartStatement _ _ _ modifies_clauses reads_clauses ->
         expressions_lack_pointer_field modifies_clauses
      && global_variables_unaddressed_in_reads_clauses vs reads_clauses
  | ExternalMethodMiddleStatement _ modifies_clauses reads_clauses ->
        expressions_lack_pointer_field modifies_clauses
      && global_variables_unaddressed_in_reads_clauses vs reads_clauses
  | _ -> true

let rec global_variables_unaddressed_in_storage (vs: list var_id_t) (storage: object_storage_t)
  : GTot ubool (decreases rank storage) =
  all_seq_facts_lemma ();
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values _ ->
      global_variables_unaddressed_in_boxes vs values
  | ObjectStoragePrimitive value -> global_variables_unaddressed_in_box vs value
  | ObjectStorageStruct fields -> global_variables_unaddressed_in_storages vs fields
  | ObjectStorageArray _ elements -> global_variables_unaddressed_in_storages vs elements
  | ObjectStorageAbstract _ _ -> true

and global_variables_unaddressed_in_storages (vs: list var_id_t) (storages: seq object_storage_t)
  : GTot ubool (decreases rank storages) =
  all_seq_facts_lemma ();
    length storages = 0
  \/ (  global_variables_unaddressed_in_storage vs (index storages 0)
     /\ global_variables_unaddressed_in_storages vs (drop storages 1))

let rec global_variables_unaddressed_in_storages_equivalent_to_forall
  (vs: list var_id_t)
  (storages: seq object_storage_t)
  : Lemma (ensures global_variables_unaddressed_in_storages vs storages <==>
                   (forall storage. contains storages storage ==> global_variables_unaddressed_in_storage vs storage))
          (decreases rank storages)
          [SMTPat (global_variables_unaddressed_in_storages vs storages)] =
  all_seq_facts_lemma ();
  if length storages = 0 then
    ()
  else
     global_variables_unaddressed_in_storages_equivalent_to_forall vs (drop storages 1)

let global_variables_unaddressed_in_root (vs: list var_id_t) (root: root_t) : GTot ubool =
  match root with
  | RootGlobal storage -> global_variables_unaddressed_in_storage vs storage
  | RootStackVariable pushed popped storage ->
      (not pushed) \/ global_variables_unaddressed_in_storage vs storage
  | RootAllocated allocated freed storage ->
      (not allocated) \/ global_variables_unaddressed_in_storage vs storage
  | _ -> True

let global_variables_unaddressed_in_memory (vs: list var_id_t) (mem: Armada.Memory.t) : GTot ubool =
  forall root_id. global_variables_unaddressed_in_root vs (mem root_id)

let global_variables_unaddressed_in_write_message (vs: list var_id_t) (write_message: write_message_t) : GTot bool =
  global_variables_unaddressed_in_pointer vs write_message.location

let global_variables_unaddressed_in_write_messages (vs: list var_id_t) (write_messages: seq write_message_t)
  : GTot ubool =
  forall write_message. contains write_messages write_message ==>
                     global_variables_unaddressed_in_write_message vs write_message

let global_variables_unaddressed_in_thread (vs: list var_id_t) (thread: Armada.Thread.t) : GTot ubool =
  global_variables_unaddressed_in_write_messages vs thread.write_buffer

let global_variables_unaddressed_in_threads (vs: list var_id_t) (threads: Armada.Threads.t) : GTot ubool =
  forall tid. global_variables_unaddressed_in_thread vs (threads tid)

let global_variables_unaddressed_in_state (vs: list var_id_t) (s: Armada.State.t) : GTot ubool =
     global_variables_unaddressed_in_memory vs s.mem
  /\ global_variables_unaddressed_in_threads vs s.threads

let rec remove_global_variables_from_write_buffer
  (vs: list var_id_t)
  (write_messages: list write_message_t)
  : GTot (list write_message_t) =
  match write_messages with
  | [] -> []
  | hd :: tl ->
      if global_variables_unaddressed_in_write_message vs hd then
        hd :: (remove_global_variables_from_write_buffer vs tl)
      else
        remove_global_variables_from_write_buffer vs tl

let write_buffers_match_except_global_variables
  (vs: list var_id_t)
  (write_messages1: seq write_message_t)
  (write_messages2: seq write_message_t)
  : GTot ubool =
  write_buffers_match (remove_global_variables_from_write_buffer vs (seq_to_list write_messages1))
    (remove_global_variables_from_write_buffer vs (seq_to_list write_messages2))

let unread_write_buffer
  (threads: Armada.Threads.t{positions_valid_in_threads threads})
  (sender_tid: tid_t)
  (receiver_tid: tid_t)
  : GTot (seq write_message_t) =
  let write_buffer = (threads sender_tid).write_buffer in
  let position_in_other_write_buffers = (threads receiver_tid).position_in_other_write_buffers in
  let position = position_in_other_write_buffers sender_tid in
  assert (sender_receiver_trigger sender_tid receiver_tid);
  drop write_buffer position

let positions_in_write_buffers_match_except_global_variables
  (vs: list var_id_t)
  (threads1: Armada.Threads.t{positions_valid_in_threads threads1})
  (threads2: Armada.Threads.t{positions_valid_in_threads threads2})
  : GTot ubool =
  forall sender_tid receiver_tid.{:pattern sender_receiver_trigger sender_tid receiver_tid}
     sender_receiver_trigger sender_tid receiver_tid
     ==> write_buffers_match_except_global_variables vs
           (unread_write_buffer threads1 sender_tid receiver_tid)
           (unread_write_buffer threads2 sender_tid receiver_tid)

let threads_match_except_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (threads1: Armada.Threads.t{positions_valid_in_threads threads1})
  (threads2: Armada.Threads.t{positions_valid_in_threads threads2})
  : GTot ubool =
    threads_match_except_write_buffers_per_pc_relation pc_relation threads1 threads2
  /\ positions_in_write_buffers_match_except_global_variables vs threads1 threads2

let memories_match_except_global_variables (vs: list var_id_t) (mem1: Armada.Memory.t) (mem2: Armada.Memory.t)
  : GTot ubool =
  forall root_id.{:pattern mem1 root_id; mem2 root_id}
            (match root_id with
             | RootIdGlobal v -> FStar.List.Tot.contains v vs \/ (mem1 root_id == mem2 root_id)
             | _ -> mem1 root_id == mem2 root_id)

let states_match_except_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : GTot ubool =
    s1.initial_tid = s2.initial_tid
  /\ s1.uniqs_used = s2.uniqs_used
  /\ memories_match_except_global_variables vs s1.mem s2.mem
  /\ positions_valid_in_state s1
  /\ positions_valid_in_state s2
  /\ threads_match_except_global_variables vs pc_relation s1.threads s2.threads
  /\ s1.trace == s2.trace
  /\ s1.stop_reason = s2.stop_reason

let equality_pc_relation_implies_state_matches_itself_except_global_variables
  (vs: list var_id_t)
  (s: Armada.State.t)
  : Lemma (requires positions_valid_in_state s)
          (ensures  states_match_except_global_variables vs equality_pc_relation s s) =
  introduce forall tid. stacks_match_per_pc_relation equality_pc_relation (s.threads tid).stack (s.threads tid).stack
  with equality_pc_relation_implies_stack_matches_itself (s.threads tid).stack;
  assert (threads_match_except_write_buffers_per_pc_relation equality_pc_relation s.threads s.threads);
  introduce forall sender_tid receiver_tid.
              sender_receiver_trigger sender_tid receiver_tid ==>
              write_buffers_match_except_global_variables vs
                (unread_write_buffer s.threads sender_tid receiver_tid)
                (unread_write_buffer s.threads sender_tid receiver_tid)
  with introduce _ ==> _
  with _.
    equality_pc_relation_implies_write_buffer_matches_itself
      (remove_global_variables_from_write_buffer vs
        (seq_to_list (unread_write_buffer s.threads sender_tid receiver_tid)))
