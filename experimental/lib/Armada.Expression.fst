module Armada.Expression

open Armada.Base
open Armada.BinaryOp
open Armada.BoundedInt
open Armada.Computation
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Thread
open Armada.Type
open Armada.UnaryOp
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Util.List

let rec build_function_type (return_type: Type0) (operand_types: list Type0) : Type =
  match operand_types with
  | [] -> conditional_computation_t return_type
  | first_type :: remaining_types -> (first_type -> GTot (build_function_type return_type remaining_types))

noeq type expression_t =
  | ExpressionConstant: (value: object_value_t) -> expression_t
  | ExpressionGlobalVariable: (td: object_td_t) -> (var_id: var_id_t) -> expression_t
  | ExpressionLocalVariable: (td: object_td_t) -> (var_id: var_id_t) -> expression_t
  | ExpressionUnaryOperator:
      (operand_td: object_td_t) -> (result_td: object_td_t) ->
      (operator: unary_op_t operand_td result_td) -> (operand: expression_t) -> expression_t
  | ExpressionBinaryOperator:
      (operand_td1: object_td_t) -> (operand_td2: object_td_t) -> (result_td: object_td_t) ->
      (operator: binary_op_t operand_td1 operand_td2 result_td) ->
      (operand1: expression_t) -> (operand2: expression_t) -> expression_t
  | ExpressionIf: (td: object_td_t) -> (cond: expression_t) -> (operand_then: expression_t) ->
      (operand_else: expression_t) -> expression_t
  | ExpressionDereference: (td: object_td_t) -> (ptr: expression_t) -> expression_t
  | ExpressionAddressOf: (obj: expression_t) -> expression_t
  | ExpressionPointerOffset: (ptr: expression_t) -> (offset: expression_t) -> expression_t
  | ExpressionFieldOf: (td: object_td_t) -> (obj: expression_t) -> (field_id: nat) -> expression_t
  | ExpressionAllocated: (ptr: expression_t) -> expression_t
  | ExpressionApplyFunction:
      (td: object_td_t) -> (operands: list expression_t) -> (return_type: Type0) -> (operand_types: list Type0) ->
      (fn: build_function_type return_type operand_types) -> expression_t
  | ExpressionIfUndefined:
      (td: object_td_t) -> (potentially_unsafe: expression_t) -> (safe_substitution: expression_t) -> expression_t
  | ExpressionInitialTid: expression_t
  | ExpressionUniqsUsed: expression_t
  | ExpressionStopReason: expression_t

let expression_to_td (exp: expression_t) : GTot object_td_t =
  match exp with
  | ExpressionConstant value -> object_value_to_td value
  | ExpressionGlobalVariable td _ -> td
  | ExpressionLocalVariable td _ -> td
  | ExpressionUnaryOperator _ result_td _ _ -> result_td
  | ExpressionBinaryOperator _ _ result_td _ _ _ -> result_td
  | ExpressionIf td _ _ _ -> td
  | ExpressionDereference td _ -> td
  | ExpressionAddressOf obj -> ObjectTDPrimitive PrimitiveTDPointer
  | ExpressionPointerOffset _ _ -> ObjectTDPrimitive PrimitiveTDPointer
  | ExpressionFieldOf td _ _ -> td
  | ExpressionAllocated _ -> ObjectTDPrimitive PrimitiveTDBool
  | ExpressionApplyFunction td _ _ _ _ -> td
  | ExpressionIfUndefined td _ _ -> td
  | ExpressionInitialTid -> ObjectTDAbstract tid_t
  | ExpressionUniqsUsed -> ObjectTDAbstract (list root_id_uniquifier_t)
  | ExpressionStopReason -> ObjectTDAbstract stop_reason_t

let rec expressions_to_tds (exps: list expression_t) : GTot (list object_td_t) =
  match exps with
  | [] -> []
  | first_exp :: remaining_exps -> (expression_to_td first_exp) :: (expressions_to_tds remaining_exps)

let rec types_to_tds (tys: list Type0) : (list object_td_t) =
  match tys with
  | [] -> []
  | first_ty :: remaining_tys -> (ObjectTDAbstract first_ty) :: (types_to_tds remaining_tys)

let rec expression_valid (exp: expression_t) : GTot bool =
  match exp with
  | ExpressionConstant value -> object_value_valid value
  | ExpressionGlobalVariable td _ -> true
  | ExpressionLocalVariable td _ -> true
  | ExpressionUnaryOperator operand_td result_td operator operand ->
         expression_valid operand
      && eqb (expression_to_td operand) operand_td
  | ExpressionBinaryOperator operand_td1 operand_td2 result_td operator operand1 operand2 ->
         expression_valid operand1
      && expression_valid operand2
      && eqb (expression_to_td operand1) operand_td1
      && eqb (expression_to_td operand2) operand_td2
  | ExpressionIf td cond operand_then operand_else ->
         expression_valid cond
      && expression_valid operand_then
      && expression_valid operand_else
      && eqb (expression_to_td cond) (ObjectTDPrimitive PrimitiveTDBool)
      && eqb (expression_to_td operand_then) td
      && eqb (expression_to_td operand_else) td
  | ExpressionDereference td ptr ->
         expression_valid ptr
      && eqb (expression_to_td ptr) (ObjectTDPrimitive PrimitiveTDPointer)
  | ExpressionAddressOf obj -> expression_valid obj
  | ExpressionPointerOffset ptr offset ->
         expression_valid ptr
      && expression_valid offset
      && eqb (expression_to_td ptr) (ObjectTDPrimitive PrimitiveTDPointer)
      && eqb (expression_to_td offset) (ObjectTDAbstract int)
  | ExpressionFieldOf td obj field_id ->
         expression_valid obj
      && ObjectTDStruct? (expression_to_td obj)
      && 0 <= field_id
      && field_id < length (ObjectTDStruct?.field_tds (expression_to_td obj))
      && eqb td ((ObjectTDStruct?.field_tds (expression_to_td obj)) `index` field_id)
  | ExpressionAllocated ptr ->
         expression_valid ptr
      && eqb (expression_to_td ptr) (ObjectTDPrimitive PrimitiveTDPointer)
  | ExpressionApplyFunction td operands return_type operand_types _ ->
         eqb td (ObjectTDAbstract return_type)
      && eqb (expressions_to_tds operands) (types_to_tds operand_types)
  | ExpressionIfUndefined td potentially_unsafe safe_substitution ->
         eqb td (expression_to_td potentially_unsafe)
      && eqb td (expression_to_td safe_substitution)
  | ExpressionInitialTid -> true
  | ExpressionUniqsUsed -> true
  | ExpressionStopReason -> true

type valid_expression_t = value: expression_t{expression_valid value}

let rec apply_function_to_operands
  (operands: list object_value_t)
  (return_type: Type0)
  (operand_types: list Type0)
  (fn: build_function_type return_type operand_types)
  : GTot (conditional_computation_t return_type) =
  match operands, operand_types with
  | [], [] -> fn
  | first_operand :: remaining_operands, first_operand_type :: remaining_operand_types ->
      (match first_operand with
       | ObjectValueAbstract ty value ->
           if eqb first_operand_type ty then
             let fn_cast: first_operand_type -> GTot (build_function_type return_type remaining_operand_types) = fn in
             apply_function_to_operands remaining_operands return_type remaining_operand_types (fn_cast value)
           else
             ComputationUndefined
       | _ -> ComputationUndefined)
  | _ -> ComputationImpossible

let rec rvalue_computation
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t (valid_object_value_t (expression_to_td exp)))
  (decreases exp) =
  if not (expression_valid exp) then
    ComputationImpossible
  else
    match exp with
    | ExpressionConstant value -> return value
    | ExpressionGlobalVariable td var_id ->
        dereference_as_td_computation (PointerRoot (RootIdGlobal var_id)) td actor s.mem
    | ExpressionLocalVariable td var_id ->
        let thread = s.threads actor in
        if not (list_contains var_id thread.top.local_variables) then
          ComputationImpossible
        else
          dereference_as_td_computation
            (PointerRoot (RootIdStack actor thread.top.method_id thread.top.frame_uniq var_id)) td actor s.mem
    | ExpressionUnaryOperator operand_td result_td operator operand ->
        let? operand_value = rvalue_computation operand actor s in
        eval_unary_op operator operand_value
    | ExpressionBinaryOperator operand_td1 operand_td2 result_td operator operand1 operand2 ->
        let? operand_value1 = rvalue_computation operand1 actor s in
        let? operand_value2 = rvalue_computation operand2 actor s in
        eval_binary_op operator operand_value1 operand_value2
    | ExpressionIf td cond operand_then operand_else ->
        let? cond_value = rvalue_computation cond actor s in
        let? operand_then_value = rvalue_computation operand_then actor s in
        let? operand_else_value = rvalue_computation operand_else actor s in
        let b = PrimitiveBoxBool?.b (ObjectValuePrimitive?.value cond_value) in
        (ComputationProduces (if b then operand_then_value else operand_else_value))
    | ExpressionDereference td ptr ->
        let? ptr_value = rvalue_computation ptr actor s in
        let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
        dereference_as_td_computation p td actor s.mem
    | ExpressionAddressOf obj ->
        let? p = lvalue_computation obj actor s in
        return (ObjectValuePrimitive (PrimitiveBoxPointer p) <: valid_object_value_t (expression_to_td exp))
    | ExpressionPointerOffset ptr offset ->
        let? ptr_value = rvalue_computation ptr actor s in
        let? offset_value = rvalue_computation offset actor s in
        let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
        // It's undefined behavior to offset a pointer that doesn't point into an array,
        // or to offset outside of the array, except exactly one past the end of the array
        // (idx == array_len).  This is part of C semantics:  As described in
        // https://en.cppreference.com/w/cpp/language/operator_arithmetic, "Any
        // other situations (that is, attempts to generate a pointer that isn't pointing
        // at an element of the same array or one past the end) invoke undefined
        // behavior."
        (match p with
         | PointerIndex array_ptr idx ->
             let offset_int = ObjectValueAbstract?.value offset_value in
             let? array_value = dereference_computation array_ptr s.mem in
             (match array_value with
              | ObjectStorageArray _ elements ->
                  let new_idx: int = (idx <: int) + offset_int in
                  // It's OK to be equal to `length elements` (one past the end), but not OK to be any higher
                  if new_idx < 0 || new_idx > length elements then
                    ComputationUndefined
                  else
                    let p' = PointerIndex array_ptr new_idx in
                    let obj = ObjectValuePrimitive (PrimitiveBoxPointer p') in
                    return (obj <: valid_object_value_t (expression_to_td exp))
              | _ -> ComputationUndefined)
         | _ -> ComputationUndefined)
    | ExpressionFieldOf td obj field_id ->
        let? obj_ptr = lvalue_computation obj actor s in
        dereference_as_td_computation (PointerField obj_ptr field_id) td actor s.mem
    | ExpressionAllocated ptr ->
        let? ptr_value = rvalue_computation ptr actor s in
        let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
        return (ObjectValuePrimitive (PrimitiveBoxBool (p <> PointerUninitialized))
                <: valid_object_value_t (expression_to_td exp))
    | ExpressionApplyFunction td operands return_type operand_types fn ->
        let? operand_values = rvalues_computation operands actor s in
        let? value = apply_function_to_operands operand_values return_type operand_types fn in
        let v: valid_object_value_t td = ObjectValueAbstract return_type value in
        return v
    | ExpressionIfUndefined td potentially_unsafe safe_substitution ->
        (match rvalue_computation potentially_unsafe actor s with
         | ComputationImpossible -> ComputationImpossible
         | ComputationUndefined -> rvalue_computation safe_substitution actor s
         | ComputationProduces value -> return value)
    | ExpressionInitialTid ->
        return (ObjectValueAbstract tid_t s.initial_tid)
    | ExpressionUniqsUsed ->
        return (ObjectValueAbstract (list root_id_uniquifier_t) s.uniqs_used)
    | ExpressionStopReason ->
        return (ObjectValueAbstract stop_reason_t s.stop_reason)

and lvalue_computation
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.Pointer.t) =
  if not (expression_valid exp) then
    ComputationImpossible
  else
    match exp with
    | ExpressionGlobalVariable _ var_id -> return (PointerRoot (RootIdGlobal var_id))
    | ExpressionLocalVariable _ var_id ->
        let thread = s.threads actor in
        if not (list_contains var_id thread.top.local_variables) then
          ComputationImpossible
        else
          return (PointerRoot (RootIdStack actor thread.top.method_id thread.top.frame_uniq var_id))
    | ExpressionDereference _ ptr ->
        let? ptr_value = rvalue_computation ptr actor s in
        return (PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value))
    | ExpressionFieldOf td obj field_id ->
        let? obj_ptr = lvalue_computation obj actor s in
        return (PointerField obj_ptr field_id)
    | _ -> ComputationImpossible

and rvalues_computation
  (exps: list expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t (list object_value_t)) =
  match exps with
  | [] -> return []
  | first_exp :: remaining_exps ->
      let? first_value = rvalue_computation first_exp actor s in
      let? remaining_values = rvalues_computation remaining_exps actor s in
      return (first_value :: remaining_values)

let append_to_thread_write_buffer
  (threads: Armada.Threads.t)
  (actor: tid_t)
  (write_message: write_message_t)
  : GTot Armada.Threads.t =
  let thread = threads actor in
  let write_buffer' = build thread.write_buffer write_message in
  let thread' = { thread with write_buffer = write_buffer' } in
  Spec.Map.upd threads actor thread'

let update_pointed_to_value
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value s.mem with
  | ComputationImpossible -> ComputationImpossible
  | ComputationUndefined -> ComputationUndefined
  | ComputationProduces (optional_write_message, mem') ->
      (match optional_write_message with
       | Some write_message ->
           let threads' = append_to_thread_write_buffer s.threads actor write_message in
           let s' = { s with mem = mem'; threads = threads' } in
           return s'
       | None ->
           let s' = { s with mem = mem' }
           in return s'
      )

let update_expression
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ComputationImpossible
  else (
    let? p = lvalue_computation exp actor s in
    update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer new_value s
  )

let rec update_expressions
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  match exps, new_values with
  | [], [] -> return s
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      let? s' = update_expression first_exp actor writer_pc writer_expression_number
              bypassing_write_buffer first_new_value s in
      update_expressions remaining_exps actor writer_pc (writer_expression_number + 1)
        bypassing_write_buffer remaining_new_values s'
  | _ -> ComputationImpossible

let check_expression_up_to_date_for_rmw
  (exp: expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t unit) =
  if not (expression_valid exp) then
    ComputationImpossible
  else (
    let? p = lvalue_computation exp actor s in
    let? storage = dereference_computation p s.mem in
    if object_storage_up_to_date_for_rmw_operation storage actor then
      return ()
    else
      ComputationImpossible
  )

let expression_corresponds_to_value
  (actor: tid_t)
  (s: Armada.State.t)
  (exp: expression_t)
  (value: object_value_t)
  : GTot bool =
     expression_valid exp
  && object_value_valid value
  && eqb (object_value_to_td value) (expression_to_td exp)
  && eqb (rvalue_computation exp actor s) (return value)

let rec rvalues_computation_facts
  (exps: list expression_t)
  (actor: tid_t)
  (s: Armada.State.t)
  : Lemma (match rvalues_computation exps actor s with
           | ComputationImpossible ->
                exists (exp: expression_t).
                  contains_ubool exp exps /\ ComputationImpossible? (rvalue_computation exp actor s)
           | ComputationUndefined ->
                exists (exp: valid_expression_t).
                  contains_ubool exp exps /\ ComputationUndefined? (rvalue_computation exp actor s)
           | ComputationProduces values ->
               lists_correspond (expression_corresponds_to_value actor s) exps values) =
  match exps with
  | [] -> ()
  | first_exp :: remaining_exps ->
      (match rvalue_computation first_exp actor s with
       | ComputationImpossible -> ()
       | ComputationUndefined -> ()
       | ComputationProduces first_value -> rvalues_computation_facts remaining_exps actor s)
