module Armada.Type

open Armada.Base
open Armada.BoundedInt
open Spec.Map
open Spec.Ubool
open FStar.Sequence.Base
open Util.Seq

/// "td" stands for "type descriptor"

type primitive_td_t =
  | PrimitiveTDBool: primitive_td_t
  | PrimitiveTDBoundedInt: (bt: bounded_int_type_t) -> primitive_td_t
  | PrimitiveTDThreadId: primitive_td_t
  | PrimitiveTDPointer: primitive_td_t

type primitive_box_t =
  | PrimitiveBoxBool: (b: bool) -> primitive_box_t
  | PrimitiveBoxBoundedInt: (bt: bounded_int_type_t) -> (n: bt_to_ty bt) -> primitive_box_t
  | PrimitiveBoxThreadId: (tid: tid_t) -> primitive_box_t
  | PrimitiveBoxPointer: (ptr: Armada.Pointer.t) -> primitive_box_t

let primitive_td_to_type (td: primitive_td_t) : Type =
  match td with
  | PrimitiveTDBool -> bool
  | PrimitiveTDBoundedInt bt -> bt_to_ty bt
  | PrimitiveTDThreadId -> tid_t
  | PrimitiveTDPointer -> Armada.Pointer.t

let primitive_box_to_td (b: primitive_box_t) : primitive_td_t =
  match b with
  | PrimitiveBoxBool _ -> PrimitiveTDBool
  | PrimitiveBoxBoundedInt bt _ -> PrimitiveTDBoundedInt bt
  | PrimitiveBoxThreadId _ -> PrimitiveTDThreadId
  | PrimitiveBoxPointer _ -> PrimitiveTDPointer

let primitive_box_to_type (b: primitive_box_t) : Type =
  primitive_td_to_type (primitive_box_to_td b)

let primitive_box_matches_primitive_td (b: primitive_box_t) (td: primitive_td_t) : bool =
  primitive_box_to_td b = td

let unbox_primitive_box (b: primitive_box_t) : (primitive_box_to_type b) =
  match b with
  | PrimitiveBoxBool v -> v
  | PrimitiveBoxBoundedInt _ v -> v
  | PrimitiveBoxThreadId v -> v
  | PrimitiveBoxPointer v -> v

noeq type object_td_t =
  | ObjectTDPrimitive: (primitive_td: primitive_td_t) -> object_td_t
  | ObjectTDStruct: (field_tds: seq object_td_t) -> object_td_t
  | ObjectTDArray: (element_td: object_td_t) -> (sz: nat) -> object_td_t
  | ObjectTDAbstract: (ty: Type0) -> object_td_t

noeq type object_value_t =
  | ObjectValuePrimitive: (value: primitive_box_t) -> object_value_t
  | ObjectValueStruct: (fields: seq object_value_t) -> object_value_t
  | ObjectValueArray: (element_td: object_td_t) -> (elements: seq object_value_t) -> object_value_t
  | ObjectValueAbstract: (ty: Type0) -> (value: ty) -> object_value_t

let rec object_value_to_td (value: object_value_t) : GTot object_td_t (decreases rank value) =
  FStar.Sequence.Ambient.all_seq_facts_ambient;
  match value with
  | ObjectValuePrimitive primitive_value -> ObjectTDPrimitive (primitive_box_to_td primitive_value)
  | ObjectValueStruct fields -> ObjectTDStruct (map_refine object_value_to_td fields)
  | ObjectValueArray element_td elements -> ObjectTDArray element_td (length elements)
  | ObjectValueAbstract ty _ -> ObjectTDAbstract ty

let rec object_value_valid (value: object_value_t) : GTot bool (decreases rank value) =
  match value with
  | ObjectValuePrimitive value -> true
  | ObjectValueStruct fields -> u2b (forall field. contains fields field ==> object_value_valid field)
  | ObjectValueArray element_td elements ->
      u2b (forall element. contains elements element ==>
                      object_value_valid element /\ object_value_to_td element == element_td)
  | ObjectValueAbstract ty _ -> true

type valid_object_value_t (td: object_td_t) =
  value: object_value_t{object_value_valid value /\ object_value_to_td value == td}

type nondeterminism_t = list object_value_t
