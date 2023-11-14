module Armada.BinaryOp

open Armada.Computation
open Armada.Type
open Armada.BoundedInt
open Armada.Pointer
open FStar.BV
open Spec.Ubool

noeq type t = {
  operand_td1: object_td_t;
  operand_td2: object_td_t;
  result_td: object_td_t;
  eval: (operand1: valid_object_value_t operand_td1) ->
        (operand2: valid_object_value_t operand_td2) ->
         GTot (conditional_computation_t (valid_object_value_t result_td));
}

// infix operator for mathematical integer types

let add_op : t = 
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 + op2 in
    return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let sub_op : t = 
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 - op2 in
    return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let mul_op : t = 
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 `op_Multiply` op2 in
    return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let div_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let numerator = ObjectValueAbstract?.value operand1 in
    let divisor = ObjectValueAbstract?.value operand2 in
    if divisor = 0 then
      ComputationUndefined
    else
      let result = numerator / divisor in
      return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let mod_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let numerator = ObjectValueAbstract?.value operand1 in
    let divisor = ObjectValueAbstract?.value operand2 in
    if divisor = 0 then
      ComputationUndefined
    else
      let result = numerator % divisor in
      return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let left_shift_op : t = 
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract nat))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = FStar.Math.Lib.shift_left op1 op2 in
    return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract nat;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let right_shift_op : t = 
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract nat))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = FStar.Math.Lib.arithmetic_shift_right op1 op2 in
    return (ObjectValueAbstract int result)) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract nat;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

// infix operator for bounded integers
// signed integer overflows are treated as undefined behavior, following C11 standard:
// http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1548.pdf, pp. 76, section 6.5.5

let bounded_add_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = add bt op1 op2 in
    if is_signed bt && result <> op1 + op2 then
       ComputationUndefined
    else
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bounded_sub_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = sub bt op1 op2 in
    if is_signed bt && result <> op1 - op2 then
       ComputationUndefined
    else
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bounded_mul_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt (double_bt_size bt))))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = mul bt op1 op2 in
    if is_signed bt && result <> op1 `op_Multiply` op2 then
       ComputationUndefined
    else
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt (double_bt_size bt) result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt (double_bt_size bt));
    eval = local_eval;
  }

// is overflow check for div/mod necessary?
// I guess so: https://stackoverflow.com/questions/30394086/integer-division-overflows/30400252#30400252

let bounded_div_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    if op2 = 0 then
       ComputationUndefined
    else
      let result = div bt op1 op2 in
      if is_signed bt && result <> op1 / op2 then
         ComputationUndefined
      else
         return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bounded_mod_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    if op2 = 0 then
       ComputationUndefined
    else
      let result = mod bt op1 op2 in
      if is_signed bt && result <> op1 % op2 then
         ComputationUndefined
      else
         return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

// logic operators

let and_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool (op1 && op2))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let or_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool (op1 || op2))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let xor_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool ((op1 && not op2) || (not op1 && op2)))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let equiv_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool ((not op1 && not op2) || (op1 && op2)))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let imply_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool (not op1 || (op1 && op2)))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let exply_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      return (ObjectValuePrimitive (PrimitiveBoxBool (not op2 || (op1 && op2)))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBool);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBool);
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let ptr_eq (operand1 operand2: Armada.Pointer.t) :
    GTot (option bool) =
  match operand1, operand2 with
  | PointerNull, PointerNull -> Some true
  | PointerNull, _ | _, PointerNull -> Some false
  | PointerRoot id1, PointerRoot id2 -> Some (id1 = id2)
  | PointerField struct1 field1, PointerField struct2 field2 ->
    if struct1 = struct2 then Some (field1 = field2) else None
  | PointerIndex arr1 idx1, PointerIndex arr2 idx2 ->
    if arr1 = arr2 then Some (idx1 = idx2) else None
  | _, _ -> None

let eq_op (op_td: object_td_t) : t =
  let local_eval
    (operand1: valid_object_value_t op_td)
    (operand2: valid_object_value_t op_td)
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    match op_td with
    | ObjectTDAbstract _ ->
      let op1 = ObjectValueAbstract?.value operand1 in
      let op2 = ObjectValueAbstract?.value operand2 in
        return (ObjectValuePrimitive (PrimitiveBoxBool (u2b (op1 == op2))))
    | ObjectTDPrimitive PrimitiveTDPointer ->
      let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
      let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      (
        match ptr_eq op1 op2 with
        | Some b -> return (ObjectValuePrimitive (PrimitiveBoxBool b))
        | None -> ComputationUndefined
      )
    | ObjectTDPrimitive PrimitiveTDThreadId ->
      ComputationUndefined
    | ObjectTDPrimitive _ ->
      let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
      let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
        return (ObjectValuePrimitive (PrimitiveBoxBool (op1 = op2)))
    | _ ->
      ComputationUndefined
  in
  {
    operand_td1 = op_td;
    operand_td2 = op_td;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let neq_op (op_td: object_td_t) : t =
  let local_eval
    (operand1: valid_object_value_t op_td)
    (operand2: valid_object_value_t op_td)
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) =
    match op_td with
    | ObjectTDAbstract _ ->
      let op1 = ObjectValueAbstract?.value operand1 in
      let op2 = ObjectValueAbstract?.value operand2 in
        return (ObjectValuePrimitive (PrimitiveBoxBool (not (u2b (op1 == op2)))))
    | ObjectTDPrimitive PrimitiveTDPointer ->
      let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
      let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
      (
        match ptr_eq op1 op2 with
        | Some b -> return (ObjectValuePrimitive (PrimitiveBoxBool (not b)))
        | None -> ComputationUndefined
      )
    | ObjectTDPrimitive PrimitiveTDThreadId ->
      ComputationUndefined
    | ObjectTDPrimitive _ ->
      let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
      let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
        return (ObjectValuePrimitive (PrimitiveBoxBool (op1 <> op2)))
    | _ ->
      ComputationUndefined
  in
  {
    operand_td1 = op_td;
    operand_td2 = op_td;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let less_than_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 < op2 in
    return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let less_than_or_equal_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 <= op2 in
    return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let greater_than_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 > op2 in
    return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let greater_than_or_equal_op : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDAbstract int))
    (operand2: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBool)))) = (
    let op1 = ObjectValueAbstract?.value operand1 in
    let op2 = ObjectValueAbstract?.value operand2 in
    let result = op1 >= op2 in
    return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDAbstract int;
    operand_td2 = ObjectTDAbstract int;
    result_td = ObjectTDPrimitive (PrimitiveTDBool);
    eval = local_eval;
  }

let bounded_less_than_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = op1 < op2 in
      return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let bounded_less_than_or_equal_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = op1 <= op2 in
      return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let bounded_greater_than_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = op1 > op2 in
      return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let bounded_greater_than_or_equal_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    let result = op1 >= op2 in
      return (ObjectValuePrimitive (PrimitiveBoxBool result))) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let pointer_less_than_op : t =
  let local_eval
    (operand1 operand2: valid_object_value_t (ObjectTDPrimitive PrimitiveTDPointer))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    match op1, op2 with
    | PointerIndex arr1 field1, PointerIndex arr2 field2 ->
      if arr1 = arr2 then return (ObjectValuePrimitive (PrimitiveBoxBool (field1 < field2))) else ComputationUndefined
    | _ -> ComputationUndefined
    ) in
  {
    operand_td1 = ObjectTDPrimitive PrimitiveTDPointer;
    operand_td2 = ObjectTDPrimitive PrimitiveTDPointer;
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let pointer_less_than_or_equal_op : t =
  let local_eval
    (operand1 operand2: valid_object_value_t (ObjectTDPrimitive PrimitiveTDPointer))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    match op1, op2 with
    | PointerIndex arr1 field1, PointerIndex arr2 field2 ->
      if arr1 = arr2 then return (ObjectValuePrimitive (PrimitiveBoxBool (field1 < field2))) else ComputationUndefined
    | _ -> ComputationUndefined
    ) in
  {
    operand_td1 = ObjectTDPrimitive PrimitiveTDPointer;
    operand_td2 = ObjectTDPrimitive PrimitiveTDPointer;
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let pointer_greater_than_op : t =
  let local_eval
    (operand1 operand2: valid_object_value_t (ObjectTDPrimitive PrimitiveTDPointer))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    match op1, op2 with
    | PointerIndex arr1 field1, PointerIndex arr2 field2 ->
      if arr1 = arr2 then return (ObjectValuePrimitive (PrimitiveBoxBool (field1 > field2))) else ComputationUndefined
    | _ -> ComputationUndefined
    ) in
  {
    operand_td1 = ObjectTDPrimitive PrimitiveTDPointer;
    operand_td2 = ObjectTDPrimitive PrimitiveTDPointer;
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let pointer_greater_than_or_equal_op : t =
  let local_eval
    (operand1 operand2: valid_object_value_t (ObjectTDPrimitive PrimitiveTDPointer))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) = (
    let op1 = unbox_primitive_box (ObjectValuePrimitive?.value operand1) in
    let op2 = unbox_primitive_box (ObjectValuePrimitive?.value operand2) in
    match op1, op2 with
    | PointerIndex arr1 field1, PointerIndex arr2 field2 ->
      if arr1 = arr2 then return (ObjectValuePrimitive (PrimitiveBoxBool (field1 >= field2))) else ComputationUndefined
    | _ -> ComputationUndefined
    ) in
  {
    operand_td1 = ObjectTDPrimitive PrimitiveTDPointer;
    operand_td2 = ObjectTDPrimitive PrimitiveTDPointer;
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

// Bitwise and/or/xor/left shift/right shift

let bitwise_and_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    if is_signed bt then
       ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op1: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand1)) in
      let op2: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand2)) in
      let result: bt_to_ty bt = bv2int (bvand op1 op2) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result)))
    ) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bitwise_or_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    if is_signed bt then
       ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op1: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand1)) in
      let op2: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand2)) in
      let result: bt_to_ty bt = bv2int (bvor op1 op2) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result)))
    ) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bitwise_xor_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    if is_signed bt then
       ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op1: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand1)) in
      let op2: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand2)) in
      let result: bt_to_ty bt = bv2int (bvxor op1 op2) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result)))
    ) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bitwise_left_shift_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDAbstract nat))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    if is_signed bt then
       ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op1: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand1)) in
      let op2 = ObjectValueAbstract?.value operand2 in
      let result: bt_to_ty bt = bv2int (bvshl op1 op2) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result)))
    ) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDAbstract nat;
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

let bitwise_right_shift_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand1: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    (operand2: valid_object_value_t (ObjectTDAbstract nat))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) = (
    if is_signed bt then
       ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op1: bv_t num_bits = int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand1)) in
      let op2 = ObjectValueAbstract?.value operand2 in
      let result: bt_to_ty bt = bv2int (bvshr op1 op2) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result)))
    ) in
  {
    operand_td1 = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    operand_td2 = ObjectTDAbstract nat;
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

noeq type binary_op_t : (operand_td1: object_td_t) -> (operand_td2: object_td_t) -> (result_td: object_td_t) -> Type =
  | BinaryOpAddInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
  | BinaryOpSubInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
  | BinaryOpMulInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
  | BinaryOpDivInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
  | BinaryOpModInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
  | BinaryOpLeftShift: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract nat) (ObjectTDAbstract int)
  | BinaryOpRightShift: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract nat) (ObjectTDAbstract int)
  | BinaryOpBoundedAdd:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBoundedSub:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBoundedMul:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt (double_bt_size bt)))
  | BinaryOpBoundedDiv:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBoundedMod:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpAnd: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                             (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpOr: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                            (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpXor: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                             (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpEquiv: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                             (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpImply: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                             (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpExply: binary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
                             (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpEq: op_td: object_td_t -> binary_op_t op_td op_td (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpNeq: op_td: object_td_t -> binary_op_t op_td op_td (ObjectTDPrimitive (PrimitiveTDBool))
  | BinaryOpLtInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpLeInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpGtInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpGeInt: binary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpBoundedLt:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpBoundedLe:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpBoundedGt:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpBoundedGe:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpPtrLt: binary_op_t (ObjectTDPrimitive PrimitiveTDPointer) (ObjectTDPrimitive PrimitiveTDPointer)
                               (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpPtrLe: binary_op_t (ObjectTDPrimitive PrimitiveTDPointer) (ObjectTDPrimitive PrimitiveTDPointer)
                               (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpPtrGt: binary_op_t (ObjectTDPrimitive PrimitiveTDPointer) (ObjectTDPrimitive PrimitiveTDPointer)
                               (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpPtrGe: binary_op_t (ObjectTDPrimitive PrimitiveTDPointer) (ObjectTDPrimitive PrimitiveTDPointer)
                               (ObjectTDPrimitive PrimitiveTDBool)
  | BinaryOpBitwiseAnd:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBitwiseOr:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBitwiseXor:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBitwiseLeftShift:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDAbstract nat)
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | BinaryOpBitwiseRightShift:
      bt: bounded_int_type_t ->
      binary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDAbstract nat)
                  (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))

let get_binary_op
  (#operand_td1: object_td_t)
  (#operand_td2: object_td_t)
  (#result_td: object_td_t)
  (binary_op: binary_op_t operand_td1 operand_td2 result_td)
  : GTot (op: t{op.operand_td1 == operand_td1 /\ op.operand_td2 == operand_td2 /\ op.result_td == result_td}) =
  match binary_op with
  | BinaryOpAddInt -> add_op
  | BinaryOpSubInt -> sub_op
  | BinaryOpMulInt -> mul_op
  | BinaryOpDivInt -> div_op
  | BinaryOpModInt -> mod_op
  | BinaryOpLeftShift -> left_shift_op
  | BinaryOpRightShift -> right_shift_op
  | BinaryOpBoundedAdd bt -> bounded_add_op bt
  | BinaryOpBoundedSub bt -> bounded_sub_op bt
  | BinaryOpBoundedMul bt -> bounded_mul_op bt
  | BinaryOpBoundedDiv bt -> bounded_div_op bt
  | BinaryOpBoundedMod bt -> bounded_mod_op bt
  | BinaryOpAnd -> and_op
  | BinaryOpOr -> or_op
  | BinaryOpXor -> xor_op
  | BinaryOpEquiv -> equiv_op
  | BinaryOpImply -> imply_op
  | BinaryOpExply -> exply_op
  | BinaryOpEq op_td -> eq_op op_td
  | BinaryOpNeq op_td -> neq_op op_td
  | BinaryOpLtInt -> less_than_op
  | BinaryOpLeInt -> less_than_or_equal_op
  | BinaryOpGtInt -> greater_than_op
  | BinaryOpGeInt -> greater_than_or_equal_op
  | BinaryOpBoundedLt bt -> bounded_less_than_op bt
  | BinaryOpBoundedLe bt -> bounded_less_than_or_equal_op bt
  | BinaryOpBoundedGt bt -> bounded_greater_than_op bt
  | BinaryOpBoundedGe bt -> bounded_greater_than_or_equal_op bt
  | BinaryOpPtrLt -> pointer_less_than_op
  | BinaryOpPtrLe -> pointer_less_than_or_equal_op
  | BinaryOpPtrGt -> pointer_greater_than_op
  | BinaryOpPtrGe -> pointer_greater_than_or_equal_op
  | BinaryOpBitwiseAnd bt -> bitwise_and_op bt
  | BinaryOpBitwiseOr bt -> bitwise_or_op bt
  | BinaryOpBitwiseXor bt -> bitwise_xor_op bt
  | BinaryOpBitwiseLeftShift bt -> bitwise_left_shift_op bt
  | BinaryOpBitwiseRightShift bt -> bitwise_right_shift_op bt

let eval_binary_op
  (#operand_td1: object_td_t)
  (#operand_td2: object_td_t)
  (#result_td: object_td_t)
  (binary_op: binary_op_t operand_td1 operand_td2 result_td)
  (operand1: valid_object_value_t operand_td1)
  (operand2: valid_object_value_t operand_td2)
  : GTot (conditional_computation_t (valid_object_value_t result_td)) =
  let op = get_binary_op binary_op in
  op.eval operand1 operand2

