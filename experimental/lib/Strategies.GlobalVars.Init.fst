module Strategies.GlobalVars.Init

open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open Spec.List
open Spec.Ubool
open Strategies.GlobalVars
open Strategies.GlobalVars.Util
open Util.List

let rec memory_satisfies_main_stack_initializers_implies_satisfies_initializer
  (mem: Armada.Memory.t)
  (tid: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (initializers: list initializer_t)
  (initializer: initializer_t)
  : Lemma (requires   contains_ubool initializer initializers
                    /\ memory_satisfies_main_stack_initializers mem tid method_id frame_uniq var_ids initializers)
          (ensures  memory_satisfies_main_stack_initializer mem tid method_id frame_uniq initializer.var_id
                      initializer) =
  match var_ids, initializers with
  | first_var_id :: remaining_var_ids, first_initializer :: remaining_initializers ->
      if eqb first_initializer initializer then
        ()
      else
        memory_satisfies_main_stack_initializers_implies_satisfies_initializer mem tid method_id frame_uniq
          remaining_var_ids remaining_initializers initializer

let rec get_initializer_for_initialized_main_stack_variable
  (mem: Armada.Memory.t)
  (tid: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (initializers: list initializer_t)
  (var_id: var_id_t)
  : Ghost initializer_t
     (requires   list_contains var_id var_ids
               /\ memory_satisfies_main_stack_initializers mem tid method_id frame_uniq var_ids initializers)
     (ensures  fun initializer ->
                     contains_ubool initializer initializers
                   /\ memory_satisfies_main_stack_initializer mem tid method_id frame_uniq var_id initializer) =
  match var_ids, initializers with
  | first_var_id :: remaining_var_ids, first_initializer :: remaining_initializers ->
      if eqb first_var_id var_id then
        first_initializer
      else
        get_initializer_for_initialized_main_stack_variable mem tid method_id frame_uniq remaining_var_ids
          remaining_initializers var_id

let storage_satisfies_initializer_implies_gvars_unaddressed
  (vs: list var_id_t)
  (initializer: initializer_t)
  (storage: valid_object_storage_t)
  : Lemma (requires   global_variables_unaddressed_in_initializer vs initializer
                    /\ storage_satisfies_initializer storage initializer.iv initializer.weakly_consistent)
          (ensures  global_variables_unaddressed_in_storage vs storage) =
  match initializer.iv with
  | InitializerArbitrary td ->
      object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs storage
  | InitializerSpecific value ->
      object_storage_initialized_correctly_doesnt_depend_on_gvars vs storage value

let init_implies_global_variables_unaddressed_in_memory
  (vs: list var_id_t)
  (program: Armada.Program.t)
  (s: Armada.State.t)
  : Lemma (requires   init_program program s
                    /\ global_variables_unaddressed_in_initializers vs program.global_initializers
                    /\ global_variables_unaddressed_in_initializers vs program.main_stack_initializers)
          (ensures  global_variables_unaddressed_in_memory vs s.mem) =
  introduce forall root_id. global_variables_unaddressed_in_root vs (s.mem root_id)
  with (
    let thread = s.threads s.initial_tid in
    let initial_frame_uniq = Cons?.hd s.uniqs_used in
    let root = s.mem root_id in
    assert (root_invalid_outside_initializations s.mem program.global_initializers s.initial_tid
              program.main_method_id initial_frame_uniq thread.top.local_variables root_id);
    match root with
    | RootGlobal storage ->
        (match root_id with
         | RootIdGlobal var_id ->
             assert (exists_ghost (var_id_in_initializer var_id) program.global_initializers);
             let initializer = exists_ghost_to_witness (var_id_in_initializer var_id) program.global_initializers in
             for_all_ubool_equivalent_to_forall (memory_satisfies_global_initializer s.mem) program.global_initializers;
             assert (memory_satisfies_global_initializer s.mem initializer);
             storage_satisfies_initializer_implies_gvars_unaddressed vs initializer storage)
    | RootStackVariable pushed popped storage ->
        if pushed then (
          match root_id with
          | RootIdStack tid method_id frame_uniq var_id ->
              let initializer = get_initializer_for_initialized_main_stack_variable s.mem tid method_id frame_uniq
                thread.top.local_variables program.main_stack_initializers var_id in
              storage_satisfies_initializer_implies_gvars_unaddressed vs initializer storage
        )
        else
          ()
    | RootAllocated allocated freed storage -> ()
    | _ -> ()
  )
