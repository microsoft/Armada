module Armada.Init

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Thread
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Map
open Spec.Ubool

/////////////////////////
// Initializer values
/////////////////////////

noeq type initializer_value_t =
  | InitializerArbitrary: (td: object_td_t) -> initializer_value_t
  | InitializerSpecific: (value: object_value_t) -> initializer_value_t

noeq type initializer_t = {
  var_id: var_id_t;
  iv: initializer_value_t;
  weakly_consistent: bool;
}

let storage_satisfies_initializer_value (storage: valid_object_storage_t) (initializer: initializer_value_t)
  : GTot bool =
  match initializer with
  | InitializerArbitrary td ->
         object_storage_arbitrarily_initialized_correctly storage
      && eqb (object_storage_to_td storage) td
  | InitializerSpecific value ->
         object_storage_initialized_correctly storage value
      && eqb (object_storage_to_td storage) (object_value_to_td value)

let storage_satisfies_initializer_value_type (storage: valid_object_storage_t) (initializer: initializer_value_t)
  : GTot bool =
  match initializer with
  | InitializerArbitrary td ->
      eqb (object_storage_to_td storage) td
  | InitializerSpecific value ->
      eqb (object_storage_to_td storage) (object_value_to_td value)

////////////////////////////
// Global initialization
////////////////////////////

let storage_satisfies_initializer
  (storage: valid_object_storage_t)
  (iv: initializer_value_t)
  (weakly_consistent: bool)
  : GTot bool =
     storage_satisfies_initializer_value storage iv
  && (if weakly_consistent then
        is_object_storage_weakly_consistent storage
      else
        is_object_storage_strongly_consistent storage)

let memory_satisfies_global_initializer
  (mem: Armada.Memory.t)
  (initializer: initializer_t)
  : GTot ubool =
  let root = mem (RootIdGlobal initializer.var_id) in
  match root with
  | RootGlobal storage ->
      storage_satisfies_initializer storage initializer.iv initializer.weakly_consistent
  | _ -> False

let memory_satisfies_global_initializers
  (mem: Armada.Memory.t)
  (initializers: list initializer_t)
  : GTot ubool =
  forall init. contains_ubool init initializers ==> memory_satisfies_global_initializer mem init

///////////////////////////////
// Stack frame initialization
///////////////////////////////

let stack_root_satisfies_main_stack_initializer
  (initializer: initializer_t)
  (root: root_t)
  : GTot bool =
  match root with
  | RootStackVariable pushed popped storage ->
         pushed
      && not popped
      && storage_satisfies_initializer storage initializer.iv initializer.weakly_consistent
  | _ -> false

let memory_satisfies_main_stack_initializer
  (mem: Armada.Memory.t)
  (tid: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_id: var_id_t)
  (initializer: initializer_t)
  : GTot bool =
     var_id = initializer.var_id
  && (let root_id = RootIdStack tid method_id frame_uniq var_id in
      let root = mem root_id in
      stack_root_satisfies_main_stack_initializer initializer root)

let rec memory_satisfies_main_stack_initializers
  (mem: Armada.Memory.t)
  (tid: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (initializers: list initializer_t)
  : GTot bool =
  match var_ids, initializers with
  | [], [] -> true
  | var_id :: remaining_var_ids, initializer :: remaining_initializers ->
         memory_satisfies_main_stack_initializer mem tid method_id frame_uniq var_id initializer
      && memory_satisfies_main_stack_initializers mem tid method_id frame_uniq
           remaining_var_ids remaining_initializers
  | _ -> false

let storage_satisfies_initializer_type (storage: valid_object_storage_t) (initializer: initializer_t) : GTot bool =
     storage_satisfies_initializer_value_type storage initializer.iv
  && (if initializer.weakly_consistent then
        is_object_storage_weakly_consistent storage
      else
        is_object_storage_strongly_consistent storage)

let stack_variable_ready_for_push
  (root: root_t)
  (initializer: initializer_t)
  : GTot bool =
  match root with
  | RootStackVariable pushed popped storage ->
         not pushed
      && not popped
      && storage_satisfies_initializer_type storage initializer
      && object_storage_arbitrarily_initialized_correctly storage
  | _ -> false

let push_stack_variable
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t) =
  let root_id = RootIdStack actor method_id frame_uniq initializer.var_id in
  let root = s.mem root_id in
  if not (stack_variable_ready_for_push root initializer) then
    ComputationImpossible
  else
    let thread = s.threads actor in
    let var_id = initializer.var_id in
    if list_contains var_id thread.top.local_variables then
      ComputationImpossible
    else
      let local_variables' = var_id :: thread.top.local_variables in
      let top' = { thread.top with local_variables = local_variables' } in
      let thread' = { thread with top = top' } in
      let threads' = upd s.threads actor thread' in
      let root' = RootStackVariable true false (RootStackVariable?.storage root) in
      let mem' = Spec.Map.upd s.mem root_id root' in
      let s' = { s with mem = mem'; threads = threads' } in
      (match initializer.iv with
       | InitializerArbitrary td -> return s'
       | InitializerSpecific value ->
           let td = (object_value_to_td value) in
           update_expression (ExpressionLocalVariable td var_id) actor writer_pc writer_expression_number
             false value s')

let rec push_stack_variables
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t)
    (decreases initializers) =
  match initializers with
  | [] -> return s
  | first_initializer :: remaining_initializers ->
      let? s' = push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s in
      push_stack_variables actor writer_pc (writer_expression_number + 1) method_id frame_uniq remaining_initializers s'
  | _ -> ComputationImpossible

let rec push_stack_parameters
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s: Armada.State.t)
  : GTot (conditional_computation_t Armada.State.t)
    (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> return s
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer =
        { var_id = first_var_id; iv = InitializerSpecific first_parameter; weakly_consistent = false } in
      let? s' = push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq first_initializer s in
      push_stack_parameters actor writer_pc (writer_expression_number + 1) method_id frame_uniq remaining_var_ids
        remaining_parameters s'
  | _ -> ComputationImpossible

///////////////////////////////
// Fence initialization
///////////////////////////////

let initial_fence_storage: valid_object_storage_t =
  ObjectStorageWeaklyConsistentPrimitive PrimitiveTDBool (singleton (PrimitiveBoxBool false)) (Spec.Map.const 0)

////////////////////////////////////////
// Making uninitalized memory invalid
////////////////////////////////////////

let var_id_in_initializer
  (var_id: var_id_t)
  (initializer: initializer_t)
  : GTot bool =
  initializer.var_id = var_id

let root_invalid_outside_initializations
  (mem: Armada.Memory.t)
  (global_initializers: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_stack_variables: list var_id_t)
  (root_id: root_id_t)
  : ubool =
  match mem root_id with
  | RootGlobal _ ->
      (match root_id with
       | RootIdGlobal var_id -> exists init. contains_ubool init global_initializers /\ var_id_in_initializer var_id init 
       | _ -> False)
  | RootStackVariable pushed popped storage ->
      (match root_id with
       | RootIdStack tid method_id frame_uniq var_id ->
           pushed ==> (   tid = initial_tid
                       /\ method_id = main_method_id
                       /\ frame_uniq = initial_frame_uniq
                       /\ list_contains var_id local_stack_variables)
       | _ -> False)
  | RootAllocated allocated freed storage -> RootIdAllocation? root_id /\ not allocated
  | RootFence storage -> RootIdFence? root_id
  | RootInvalid -> True

let memory_invalid_outside_initializations
  (mem: Armada.Memory.t)
  (global_initializers: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_stack_variables: list var_id_t)
  : GTot ubool =
  forall root_id. root_invalid_outside_initializations mem global_initializers initial_tid
               main_method_id initial_frame_uniq local_stack_variables root_id
