module Armada.Memory

open Armada.Base
open Armada.Computation
open Armada.Pointer
open Armada.Thread
open Armada.Type
open FStar.Sequence.Base
open Spec.Ubool
open Util.Seq

noeq type object_storage_t =
  | ObjectStorageWeaklyConsistentPrimitive:
      (primitive_td: primitive_td_t) ->
      (values: seq primitive_box_t) ->
      (local_versions: Spec.Map.t tid_t nat) ->
      object_storage_t
  | ObjectStoragePrimitive: (value: primitive_box_t) -> object_storage_t
  | ObjectStorageStruct: (fields: seq object_storage_t) -> object_storage_t
  | ObjectStorageArray: (element_td: object_td_t) -> (elements: seq object_storage_t) -> object_storage_t
  | ObjectStorageAbstract: (ty: Type) -> (value: ty) -> object_storage_t

let rec object_storage_to_td (storage: object_storage_t) : GTot object_td_t (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td _ _ -> ObjectTDPrimitive primitive_td
  | ObjectStoragePrimitive value -> ObjectTDPrimitive (primitive_box_to_td value)
  | ObjectStorageStruct fields -> ObjectTDStruct (map_refine object_storage_to_td fields)
  | ObjectStorageArray element_td elements -> ObjectTDArray element_td (length elements)
  | ObjectStorageAbstract ty _ -> ObjectTDAbstract ty

let object_storage_to_td_equivalent_to_map (storage: object_storage_t)
  : Lemma (ensures (let td = object_storage_to_td storage in
                    match storage with
                    | ObjectStorageStruct fields -> td == ObjectTDStruct (map object_storage_to_td fields)
                    | _ -> True))
          [SMTPat (object_storage_to_td storage)] =
  let td = object_storage_to_td storage in
  match storage with
  | ObjectStorageStruct fields ->
      assert (equal (ObjectTDStruct?.field_tds td) (map object_storage_to_td fields))
  | _ -> ()

let rec object_storage_valid (storage: object_storage_t) : GTot bool (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
         u2b (forall tid.{:pattern local_versions tid} local_versions tid < length values)
      && u2b (forall value.{:pattern contains values value} contains values value ==> primitive_box_matches_primitive_td value primitive_td)
  | ObjectStoragePrimitive value -> true
  | ObjectStorageStruct fields ->
      u2b (forall field.{:pattern contains fields field} contains fields field ==> object_storage_valid field)
  | ObjectStorageArray element_td elements ->
      u2b (forall element.{:pattern contains elements element} contains elements element ==>
             object_storage_valid element /\ object_storage_to_td element == element_td)
  | ObjectStorageAbstract _ _ -> true

let valid_object_storage_t = (storage: object_storage_t{object_storage_valid storage})

let rec object_storage_to_value (actor: tid_t) (storage: object_storage_t)
  : GTot object_value_t (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions ->
      let version = local_versions actor in
      if version < length values then
        ObjectValuePrimitive (index values version)
      else
        ObjectValueAbstract bool false
  | ObjectStoragePrimitive value -> ObjectValuePrimitive value
  | ObjectStorageStruct fields -> ObjectValueStruct (map_refine (object_storage_to_value actor) fields)
  | ObjectStorageArray element_td elements -> ObjectValueArray element_td (map_refine (object_storage_to_value actor) elements)
  | ObjectStorageAbstract ty value -> ObjectValueAbstract ty value

let rec object_storage_to_value_preserves_td
  (actor: tid_t)
  (storage: valid_object_storage_t)
  : Lemma (ensures (let value = object_storage_to_value actor storage in
                      object_value_to_td value == object_storage_to_td storage
                    /\ object_value_valid value))
          (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
      let version = local_versions actor in
      assert (contains values (index values version))
  | ObjectStoragePrimitive _ -> ()
  | ObjectStorageStruct fields ->
      let value = object_storage_to_value actor storage in
      let td = object_storage_to_td storage in
      let field_tds = (ObjectTDStruct?.field_tds td) in
      (match value with
       | ObjectValueStruct value_fields ->
           introduce forall (i: nat). i < length fields ==>
                         object_value_to_td (index value_fields i) == index field_tds i
                       /\ object_value_valid (index value_fields i)
           with introduce _ ==> _
           with given_antecedent. (
             assert (contains fields (index fields i));
             object_storage_to_value_preserves_td actor (index fields i)
           );
           (match object_value_to_td (object_storage_to_value actor storage) with
            | ObjectTDStruct field_tds' -> assert (equal field_tds' field_tds)))
  | ObjectStorageArray element_td elements ->
      let value = object_storage_to_value actor storage in
      (match value with
       | ObjectValueArray _ value_elements ->
          introduce forall (i: nat). i < length elements ==>
                        object_value_to_td (index value_elements i) == element_td
                      /\ object_value_valid (index value_elements i)
          with introduce _ ==> _
          with given_antecedent. (
            assert (contains elements (index elements i));
            assert (index elements i << elements);
            object_storage_to_value_preserves_td actor (index elements i)
          )
      )
  | ObjectStorageAbstract ty value -> ()

let object_storage_to_value_preserves_validity
  (actor: tid_t)
  (storage: valid_object_storage_t)
  : Lemma (ensures object_value_valid (object_storage_to_value actor storage))
          (decreases rank storage) =
  object_storage_to_value_preserves_td actor storage

let object_storage_to_value_equivalent_to_map (actor: tid_t) (storage: object_storage_t)
  : Lemma (ensures (let value = object_storage_to_value actor storage in
                    match storage with
                    | ObjectStorageStruct fields ->
                        value == ObjectValueStruct (map (object_storage_to_value actor) fields)
                    | ObjectStorageArray element_td elements ->
                        value == ObjectValueArray element_td (map (object_storage_to_value actor) elements)
                    | _ -> True))
          [SMTPat (object_storage_to_value actor storage)] =
  let value = object_storage_to_value actor storage in
  match storage with
  | ObjectStorageStruct fields ->
      assert (equal (ObjectValueStruct?.fields value) (map (object_storage_to_value actor) fields))
  | ObjectStorageArray element_td elements ->
      assert (equal (ObjectValueArray?.elements value) (map (object_storage_to_value actor) elements))
  | _ -> ()

let object_storage_up_to_date_for_rmw_operation (storage: object_storage_t) (tid: tid_t) : GTot bool =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
      let version_id = local_versions tid in
      eqb version_id (length values - 1)
  | _ -> true

let rec object_value_to_storage (value: object_value_t) : GTot object_storage_t (decreases rank value) =
  match value with
  | ObjectValuePrimitive value -> ObjectStoragePrimitive value
  | ObjectValueStruct fields -> ObjectStorageStruct (map_refine object_value_to_storage fields)
  | ObjectValueArray element_td elements ->
      ObjectStorageArray element_td (map_refine object_value_to_storage elements)
  | ObjectValueAbstract ty v -> ObjectStorageAbstract ty v

let rec object_value_to_storage_preserves_validity (value: object_value_t)
  : Lemma (requires object_value_valid value)
          (ensures    object_storage_valid (object_value_to_storage value)
                    /\ (object_storage_to_td (object_value_to_storage value)) == (object_value_to_td value))
          (decreases rank value) =
  match value with
  | ObjectValuePrimitive value -> ()
  | ObjectValueStruct fields ->
      let storage = object_value_to_storage value in
      let td = object_value_to_td value in
      let field_tds = (ObjectTDStruct?.field_tds td) in
      (match storage with
       | ObjectStorageStruct storage_fields ->
           introduce forall (i: nat). i < length fields ==>
                         object_storage_to_td (index storage_fields i) == index field_tds i
                       /\ object_storage_valid (index storage_fields i)
           with introduce _ ==> _
           with given_antecedent. (
             assert (contains fields (index fields i));
             object_value_to_storage_preserves_validity (index fields i)
           );
           (match object_storage_to_td (object_value_to_storage value) with
            | ObjectTDStruct field_tds' -> assert (equal field_tds' field_tds)
           ))
  | ObjectValueArray element_td elements ->
      let storage = object_value_to_storage value in
      (match storage with
       | ObjectStorageArray _ storage_elements ->
          introduce forall (i: nat). i < length elements ==>
                        object_storage_to_td (index storage_elements i) == element_td
                      /\ object_storage_valid (index storage_elements i)
          with introduce _ ==> _
          with given_antecedent. (
            assert (contains elements (index elements i));
            object_value_to_storage_preserves_validity (index elements i)
          ))
  | ObjectValueAbstract ty v -> ()

let rec object_value_has_all_pointers_uninitialized (value: object_value_t)
  : GTot bool =
  match value with
  | ObjectValuePrimitive primitive_value ->
      (match primitive_value with
       | PrimitiveBoxPointer ptr -> PointerUninitialized? ptr
       | _ -> true)
  | ObjectValueStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      u2b (forall field. contains fields field ==> object_value_has_all_pointers_uninitialized field)
  | ObjectValueArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      u2b (forall element. contains elements element ==> object_value_has_all_pointers_uninitialized element)
  | ObjectValueAbstract ty _ -> true

let rec object_storage_arbitrarily_initialized_correctly (storage: object_storage_t)
  : GTot bool (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions ->
         length values = 1
      && u2b (forall tid. local_versions tid = 0)
      && (match index values 0 with
          | PrimitiveBoxPointer ptr -> PointerUninitialized? ptr
          | _ -> true)
  | ObjectStoragePrimitive primitive_value ->
      (match primitive_value with
       | PrimitiveBoxPointer ptr -> PointerUninitialized? ptr
       | _ -> true)
  | ObjectStorageStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      u2b (forall field. contains fields field ==> object_storage_arbitrarily_initialized_correctly field)
  | ObjectStorageArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      u2b (forall element. contains elements element ==> object_storage_arbitrarily_initialized_correctly element)
  | ObjectStorageAbstract ty value -> true

let rec object_storage_initialized_correctly (storage: object_storage_t) (value: object_value_t)
  : GTot bool (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions ->
      (match value with
       | ObjectValuePrimitive primitive_value ->
              eqb values (singleton primitive_value)
           && u2b (forall tid. local_versions tid = 0)
       | _ -> false)
  | ObjectStoragePrimitive primitive_value ->
      eqb value (ObjectValuePrimitive primitive_value)
  | ObjectStorageStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      (match value with
       | ObjectValueStruct field_values ->
             length fields = length field_values
           && u2b (forall (i: nat). i < length fields ==>
                             object_storage_initialized_correctly (index fields i) (index field_values i))
       | _ -> false)
  | ObjectStorageArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      (match value with
       | ObjectValueArray element_td' element_values ->
             length elements = length element_values
           && eqb element_td' element_td
           && u2b (forall (i: nat). i < length elements ==>
                     object_storage_initialized_correctly (index elements i) (index element_values i))
       | _ -> false)
  | ObjectStorageAbstract ty value' -> eqb value (ObjectValueAbstract ty value')

let rec is_object_storage_weakly_consistent (storage: object_storage_t) : GTot bool =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ _ _ -> true
  | ObjectStoragePrimitive _ -> false
  | ObjectStorageStruct fields -> u2b (forall field. contains fields field ==> is_object_storage_weakly_consistent field)
  | ObjectStorageArray _ elements -> u2b (forall element. contains elements element ==>
                                                    is_object_storage_weakly_consistent element)
  | ObjectStorageAbstract _ _ -> false

let rec is_object_storage_strongly_consistent (obj: object_storage_t) : GTot bool =
  match obj with
  | ObjectStorageWeaklyConsistentPrimitive _ _ _ -> false
  | ObjectStoragePrimitive _ -> true
  | ObjectStorageStruct fields -> u2b (forall field. contains fields field ==>
                                               is_object_storage_strongly_consistent field)
  | ObjectStorageArray _ elements -> u2b (forall element. contains elements element ==>
                                                    is_object_storage_strongly_consistent element)
  | ObjectStorageAbstract _ _ -> true

noeq type root_t =
  | RootGlobal: (storage: valid_object_storage_t) -> root_t
  | RootStackVariable: (pushed: bool) -> (popped: bool) -> (storage: valid_object_storage_t) -> root_t
  | RootAllocated: (allocated: bool) -> (freed: bool) -> (storage: valid_object_storage_t) -> root_t
  | RootFence: (storage: valid_object_storage_t) -> root_t
  | RootInvalid: root_t

type t = Spec.Map.t root_id_t root_t

let root_to_storage_computation (root: root_t) : GTot (conditional_computation_t valid_object_storage_t) =
  match root with
  | RootGlobal storage -> return storage
  | RootStackVariable pushed popped storage ->
      if not pushed then ComputationImpossible else if popped then ComputationUndefined else return storage
  | RootAllocated allocated freed storage ->
      if not allocated then ComputationImpossible else if freed then ComputationUndefined else return storage
  | RootFence storage -> return storage
  | RootInvalid -> ComputationImpossible

let update_root_storage (root: root_t) (new_storage: valid_object_storage_t) : root_t =
  match root with
  | RootGlobal storage -> RootGlobal new_storage
  | RootStackVariable pushed popped storage -> RootStackVariable pushed popped new_storage
  | RootAllocated allocated freed storage -> RootAllocated allocated freed new_storage
  | RootFence storage -> RootFence new_storage
  | RootInvalid -> RootInvalid

/// There are four ways to trigger undefined behavior when
/// dereferencing a pointer.
///
/// 1) Have the pointer be null-based (e.g., if p == NULL, then access
///    *p or *p.f or *p[3] or *p.f1.f2[7][42])
///
/// 2) Have the pointer be based on an uninitalized pointer.
///
/// 3) Have the pointer be based on an allocated, freed heap root.
///    (The state-machine translator won't let you access a
///    not-yet-allocated part of the heap, so it's not possible to
///    trigger undefined behavior by accessing a non-yet-allocated
///    part of the heap.)
/// 
/// 4) Have the pointer be correctly typed when ignoring array bounds
///    but incorrectly typed when considering array bounds.  (The
///    state-machine translator won't let you access non-existent
///    struct fields, so it's not possible to manifest undefined
///    behavior by having the pointer be incorrectly typed when
///    ignoring array bounds.)

/// On the other hand, there are various invalid ways to dereference a
/// pointer that don't trigger undefined behavior because the
/// state-machine translation process prevents them from happening.
/// So the following cases are presumed to be impossible:
///
/// 1) Dereferencing a pointer based on a non-null, initialized
///    pointer to a not-yet-allocated root.  There's no way to assign
///    the value of such a pointer to any variable or derive it in an
///    expression.
/// 
/// 2) Dereferencing a pointer using a struct field ID that's >= the
///    number of fields in the pointed-to struct.  The state-machine
///    translator knows the type of every pointer, including what kind
///    of struct it points to and what fields that struct has.
///
/// 3) Dereferencing a non-null pointer that doesn't match the heap's
///    structure.  After all, the state-machine translator knows the
///    type of every pointer and doesn't allow casting.
///
/// 4) Dereferencing a pointer that matches the heap structure but for
///    which the heap has a dynamic value of the wrong type.  After
///    all, the state-machine translator won't generate a program that
///    ever stores something of one type into a location of a
///    different type.

let rec dereference_computation (p: Armada.Pointer.t) (mem: t)
  : GTot (conditional_computation_t valid_object_storage_t) =
  match p with
  | PointerUninitialized -> ComputationUndefined
  | PointerNull -> ComputationUndefined
  | PointerRoot root_id ->
      let root = mem root_id in
      root_to_storage_computation root
  | PointerField struct_ptr field_id ->
      let? parent = dereference_computation struct_ptr mem in
      (match parent with
       | ObjectStorageStruct fields ->
           if field_id >= length fields then
             ComputationImpossible
           else
             let field = index fields field_id in
             if not (object_storage_valid field) then
               ComputationImpossible
             else
               return (field <: valid_object_storage_t)
       | _ -> ComputationImpossible)
  | PointerIndex array_ptr idx ->
      let? parent = dereference_computation array_ptr mem in
      (match parent with
       | ObjectStorageArray _ elements ->
           if idx < 0 || idx >= length elements then
             ComputationUndefined
           else
             let element = index elements idx in
             if not (object_storage_valid element) then
               ComputationImpossible
             else
               return (element <: valid_object_storage_t)
       | _ -> ComputationImpossible)

let dereference_as_td_computation (p: Armada.Pointer.t) (td: object_td_t) (actor: tid_t) (mem: t)
  : GTot (conditional_computation_t (valid_object_value_t td)) =
  let? storage = dereference_computation p mem in
  object_storage_to_value_preserves_validity actor storage;
  let value = object_storage_to_value actor storage in
  if eqb (object_value_to_td value) td then
    return (object_storage_to_value actor storage <: valid_object_value_t td)
  else
    ComputationImpossible

let can_update_storage_child
  (storage: valid_object_storage_t)
  (idx: nat)
  (new_child: valid_object_storage_t)
  : GTot bool =
  match storage with
  | ObjectStorageStruct fields ->
        idx < length fields
     && eqb (object_storage_to_td new_child) (object_storage_to_td (index fields idx))
  | ObjectStorageArray element_td elements ->
        idx < length elements
     && eqb (object_storage_to_td new_child) element_td
  | _ -> false

#push-options "--z3cliopt smt.qi.eager_threshold=100"

let update_storage_child
  (storage: valid_object_storage_t)
  (idx: nat)
  (new_child: valid_object_storage_t{can_update_storage_child storage idx new_child})
  : GTot valid_object_storage_t =
  match storage with
  | ObjectStorageStruct fields ->
      let td = object_storage_to_td storage in
      let field_tds = ObjectTDStruct?.field_tds td in
      let fields' = update fields idx new_child in
      let storage' = ObjectStorageStruct fields' in
      let td' = object_storage_to_td storage' in
      let field_tds' = ObjectTDStruct?.field_tds td' in
      assert (equal field_tds field_tds');
      assert (forall field. contains fields field ==> object_storage_valid field);
      storage'
  | ObjectStorageArray element_td elements ->
      let elements' = update elements idx new_child in
      let storage' = ObjectStorageArray element_td elements' in
      assert (forall element. contains elements element ==>
                object_storage_valid element /\ object_storage_to_td element == element_td);
      storage'

#pop-options

let update_storage
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (storage: valid_object_storage_t)
  (new_value: object_value_t)
  : GTot (conditional_computation_t (option write_message_t * valid_object_storage_t))
    (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
      (match new_value with
       | ObjectValuePrimitive new_box ->
           if not (primitive_box_matches_primitive_td new_box primitive_td) then
             ComputationImpossible
           else
             let new_version_id = length values in
             let new_values = build values new_box in
             if bypassing_write_buffer then
               let new_local_versions = Spec.Map.const new_version_id in
               let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td new_values
                                   new_local_versions in
               return (None, new_storage)
             else
               let new_local_versions = Spec.Map.upd local_versions actor new_version_id in
               let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td new_values
                                   new_local_versions in
               let write_message = {
                 location = p;
                 primitive_td = primitive_td;
                 version = new_version_id;
                 writer_pc = writer_pc;
                 writer_expression_number = writer_expression_number
               } in
               if not (object_storage_valid new_storage) then
                 ComputationImpossible
               else
                 return (Some write_message, new_storage)
       | _ -> ComputationImpossible)
  | ObjectStoragePrimitive value ->
      (match new_value with
       | ObjectValuePrimitive new_box ->
           if (primitive_box_to_td new_box) <> (primitive_box_to_td value) then
             ComputationImpossible
           else
             let new_storage = ObjectStoragePrimitive new_box in
             return (None, new_storage)
       | _ -> ComputationImpossible)
  | ObjectStorageStruct fields -> ComputationImpossible
  | ObjectStorageArray element_td elements -> ComputationImpossible
  | ObjectStorageAbstract ty value ->
      (match new_value with
       | ObjectValueAbstract ty' value' ->
           if neqb ty ty' then
             ComputationImpossible
           else
             let new_storage = ObjectStorageAbstract ty' value' in
             return (None, new_storage)
       | _ -> ComputationImpossible)

let rec update_pointer_directly
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem: t)
  : GTot (conditional_computation_t t) =
  match p with
  | PointerUninitialized -> ComputationUndefined
  | PointerNull -> ComputationUndefined
  | PointerRoot root_id ->
      let root = mem root_id in
      let? storage = root_to_storage_computation root in
      if neqb (object_storage_to_td storage) (object_storage_to_td new_storage) then
        ComputationImpossible
      else
        let new_root = update_root_storage root new_storage in
        let mem' = Spec.Map.upd mem root_id new_root in
        return mem'
  | PointerField struct_ptr field_id ->
      let? parent = dereference_computation struct_ptr mem in
      (match parent with
       | ObjectStorageStruct fields ->
           if   field_id >= length fields
              || neqb (object_storage_to_td new_storage)
                     (object_storage_to_td (index fields field_id)) then
             ComputationImpossible
           else
             let new_parent = update_storage_child parent field_id new_storage in
             update_pointer_directly struct_ptr new_parent mem
       | _ -> ComputationImpossible)
  | PointerIndex array_ptr idx ->
      let? parent = dereference_computation array_ptr mem in
      (match parent with
       | ObjectStorageArray element_td elements ->
           if   idx < 0
              || idx >= length elements
              || neqb (object_storage_to_td new_storage) element_td then
             ComputationImpossible
           else
             let new_parent = update_storage_child parent idx new_storage in
             update_pointer_directly array_ptr new_parent mem
       | _ -> ComputationImpossible)

let update_pointer
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (mem: t)
  : GTot (conditional_computation_t (option write_message_t * t)) =
  match p with
  | PointerUninitialized -> ComputationUndefined
  | PointerNull -> ComputationUndefined
  | PointerRoot root_id ->
      let root = mem root_id in
      let? storage = root_to_storage_computation root in
      (match update_storage p actor writer_pc writer_expression_number bypassing_write_buffer storage
               new_value with
       | ComputationImpossible -> ComputationImpossible
       | ComputationUndefined -> ComputationUndefined
       | ComputationProduces (write_message, new_root_storage) ->
           let new_root = update_root_storage root new_root_storage in
           let new_mem = Spec.Map.upd mem root_id new_root in
           return (write_message, new_mem))
  | PointerField struct_ptr field_id ->
      let? parent = dereference_computation struct_ptr mem in
      (match parent with
       | ObjectStorageStruct fields ->
           if field_id >= length fields then
             ComputationImpossible
           else
             let field = index fields field_id in
             if   not (object_storage_valid field)
                || neqb (object_storage_to_td field) (object_value_to_td new_value) then
               ComputationImpossible
             else
               (match update_storage p actor writer_pc writer_expression_number
                        bypassing_write_buffer field new_value with
                | ComputationImpossible -> ComputationImpossible
                | ComputationUndefined -> ComputationUndefined
                | ComputationProduces (write_message, new_field) ->
                    if (not (can_update_storage_child parent field_id new_field)) then
                      ComputationImpossible
                    else
                      let new_parent = update_storage_child parent field_id new_field in
                      let? new_mem = update_pointer_directly struct_ptr new_parent mem in
                      return (write_message, new_mem))
       | _ -> ComputationImpossible)
  | PointerIndex array_ptr idx ->
      let? parent = dereference_computation array_ptr mem in
      (match parent with
       | ObjectStorageArray element_td elements ->
           if idx < 0 || idx >= length elements then
             ComputationUndefined
           else
             let element = index elements idx in
             if not (object_storage_valid element) then
               ComputationImpossible
             else
               (match update_storage p actor writer_pc writer_expression_number
                        bypassing_write_buffer element new_value with
                | ComputationImpossible -> ComputationImpossible
                | ComputationUndefined -> ComputationUndefined
                | ComputationProduces (write_message, new_element) ->
                    if not (can_update_storage_child parent idx new_element) then
                      ComputationImpossible
                    else
                      let new_parent = update_storage_child parent idx new_element in
                      let? new_mem = update_pointer_directly array_ptr new_parent mem in
                      return (write_message, new_mem))
        | _ -> ComputationImpossible)

let propagate_write_message
  (write_message: write_message_t)
  (receiver_tid: tid_t)
  (mem: t)
  : GTot (conditional_computation_t t) =
  let p = write_message.location in
  let? storage = dereference_computation p mem in
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
      if   primitive_td <> write_message.primitive_td
         || write_message.version >= length values then
        ComputationImpossible
      else if local_versions receiver_tid >= write_message.version then
        // Skip
        return mem
      else
        // Propagate
        let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message.version in
        let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values
                            new_local_versions in
        if not (object_storage_valid new_storage) then
          ComputationImpossible
        else
          update_pointer_directly p new_storage mem
  | _ -> ComputationImpossible

let free_allocated_root (root_id: root_id_t) (mem: t) : GTot (conditional_computation_t t) =
  let root = mem root_id in
  match root with
  | RootGlobal storage -> ComputationUndefined
  | RootStackVariable pushed popped storage ->
      if not pushed then ComputationImpossible else ComputationUndefined
  | RootAllocated allocated freed storage ->
      if not allocated then
        ComputationImpossible
      else if freed then
        ComputationUndefined
      else
        let root' = RootAllocated true true storage in
        let mem' = Spec.Map.upd mem root_id root' in
        return mem'
  | RootFence storage -> ComputationImpossible // there's no way to compile a free of a fence root
  | RootInvalid -> ComputationImpossible

let free_pointer (p: Armada.Pointer.t) (mem: t) : GTot (conditional_computation_t t) =
  match p with
  | PointerIndex (PointerRoot root_id) idx ->
      if idx <> 0 then
        ComputationUndefined
      else
        free_allocated_root root_id mem
  | _ -> ComputationUndefined

let pop_stack_variable
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_id: var_id_t)
  (mem: t)
  : GTot (conditional_computation_t t) =
  let root_id = RootIdStack actor method_id frame_uniq var_id in
  let root = mem root_id in
  match root with
  | RootGlobal storage -> ComputationImpossible
  | RootStackVariable pushed popped storage ->
      if not pushed || popped then
        ComputationImpossible
      else
        let root' = RootStackVariable true true storage in
        let mem' = Spec.Map.upd mem root_id root' in
        return mem'
  | RootAllocated allocated freed storage -> ComputationImpossible
  | RootFence storage -> ComputationImpossible
  | RootInvalid -> ComputationImpossible

let rec pop_stack_variables
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (mem: t)
  : GTot (conditional_computation_t t) =
  match var_ids with
  | [] -> return mem
  | first_var_id :: remaining_var_ids ->
      let? mem' = pop_stack_variable actor method_id frame_uniq first_var_id mem in
      pop_stack_variables actor method_id frame_uniq remaining_var_ids mem'

let is_primitive_box_zero_filled (box: primitive_box_t) : bool =
  match box with
  | PrimitiveBoxBool b -> not b
  | PrimitiveBoxBoundedInt _ n -> n = 0
  | PrimitiveBoxThreadId tid -> tid = 0
  | PrimitiveBoxPointer ptr -> PointerNull? ptr

let rec is_storage_zero_filled (storage: object_storage_t) : GTot bool =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values _ ->
      length values = 1 && is_primitive_box_zero_filled (index values 0)
  | ObjectStoragePrimitive value ->
      is_primitive_box_zero_filled value
  | ObjectStorageStruct fields ->
      u2b (forall field.{:pattern contains fields field} contains fields field ==> is_storage_zero_filled field)
  | ObjectStorageArray _ elements ->
      u2b (forall element.{:pattern contains elements element}
             contains elements element ==> is_storage_zero_filled element)
  | ObjectStorageAbstract _ _ ->
      false

let rec is_storage_ready_for_allocation (storage: object_storage_t) : GTot bool =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values _ ->
       length values = 1
  | ObjectStoragePrimitive _ ->
      false
  | ObjectStorageStruct fields ->
      u2b (forall field.{:pattern contains fields field} contains fields field ==> is_storage_ready_for_allocation field)
  | ObjectStorageArray _ elements ->
      u2b (forall element.{:pattern contains elements element}
             contains elements element ==> is_storage_ready_for_allocation element)
  | ObjectStorageAbstract _ _ ->
      false
