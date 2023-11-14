module Armada.UnaryOp

open Armada.Computation
open Armada.Type
open Spec.Ubool
open Armada.BoundedInt

noeq type t = {
  operand_td: object_td_t;
  result_td: object_td_t;
  eval: (operand: valid_object_value_t operand_td -> GTot (conditional_computation_t (valid_object_value_t result_td)));
}

let not_op : t =
  let local_eval
    (operand: valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive PrimitiveTDBool))) =
    let op = unbox_primitive_box (ObjectValuePrimitive?.value operand) in
      return (ObjectValuePrimitive (PrimitiveBoxBool (not op)))
  in
  {
    operand_td = ObjectTDPrimitive PrimitiveTDBool;
    result_td = ObjectTDPrimitive PrimitiveTDBool;
    eval = local_eval;
  }

let neg_op : t =
  let local_eval
    (operand: valid_object_value_t (ObjectTDAbstract int))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDAbstract int))) =
    let op = ObjectValueAbstract?.value operand in
      return (ObjectValueAbstract int (- op))
  in
  {
    operand_td = ObjectTDAbstract int;
    result_td = ObjectTDAbstract int;
    eval = local_eval;
  }

let bounded_neg_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) =
    let op = unbox_primitive_box (ObjectValuePrimitive?.value operand) in
    let result = sub bt 0 op in
    if result = -op then
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))
    else
      ComputationUndefined
  in
  {
    operand_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

// casting
let cast_op (bt_op bt_res: bounded_int_type_t) : t =
  let local_eval
  (operand: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt_op)))
  : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt_res)))) =
  let op = unbox_primitive_box (ObjectValuePrimitive?.value operand) in
  if not (is_signed bt_res) then
  // casting to unsigned are always well-defined
    return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt_res (fit bt_res op)))
  else if (=) #int op (fit bt_res op) then
  // if the value fits in the result type then it's well-defined
    return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt_res op))
  else
  // otherwise it's "implementation defined", I will leave it UB for now
  // we might change this later, if it turns out we need to verify these code
    ComputationUndefined
  in
  {
    operand_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt_op);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt_res);
    eval = local_eval;
  }

let bitwise_not_op (bt: bounded_int_type_t) : t =
  let local_eval
    (operand: valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))
    : GTot (conditional_computation_t (valid_object_value_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)))) =
    if is_signed bt then
      ComputationUndefined
    else (
      let num_bits = num_bits_in_bounded_int_type bt in
      let op: FStar.BV.bv_t num_bits = FStar.BV.int2bv (unbox_primitive_box (ObjectValuePrimitive?.value operand)) in
      let result: bt_to_ty bt = FStar.BV.bv2int (FStar.BV.bvnot op) in
      return (ObjectValuePrimitive (PrimitiveBoxBoundedInt bt result))
    )
  in
  {
    operand_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    result_td = ObjectTDPrimitive (PrimitiveTDBoundedInt bt);
    eval = local_eval;
  }

noeq type unary_op_t : (operand_td: object_td_t) -> (result_td: object_td_t) -> Type =
  | UnaryOpNot: unary_op_t (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool)
  | UnaryOpNeg: unary_op_t (ObjectTDAbstract int) (ObjectTDAbstract int)
  | UnaryOpBoundedNeg:
      bt: bounded_int_type_t ->
      unary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))
  | UnaryOpCast:
      bt_op: bounded_int_type_t ->
      bt_res: bounded_int_type_t ->
      unary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt_op)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt_res))
  | UnaryOpBitwiseNot:
      bt: bounded_int_type_t ->
      unary_op_t (ObjectTDPrimitive (PrimitiveTDBoundedInt bt)) (ObjectTDPrimitive (PrimitiveTDBoundedInt bt))

let get_unary_op
  (#operand_td: object_td_t)
  (#result_td: object_td_t)
  (unary_op: unary_op_t operand_td result_td)
  : GTot (op: t{op.operand_td == operand_td /\ op.result_td == result_td}) =
  match unary_op with
  | UnaryOpNot -> not_op
  | UnaryOpNeg -> neg_op
  | UnaryOpBoundedNeg bt -> bounded_neg_op bt
  | UnaryOpCast bt_op bt_res -> cast_op bt_op bt_res
  | UnaryOpBitwiseNot bt -> bitwise_not_op bt

let eval_unary_op
  (#operand_td: object_td_t)
  (#result_td: object_td_t)
  (unary_op: unary_op_t operand_td result_td)
  (operand: valid_object_value_t operand_td)
  : GTot (conditional_computation_t (valid_object_value_t result_td)) =
  let op = get_unary_op unary_op in
  op.eval operand
