module Strategies.GlobalVars.VarHiding

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
open Strategies.GlobalVars.Pointer
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarIntro
open Strategies.PCRelation
open Util.Seq
open Util.Trigger
  
let append_among_gvars_s1_only_preserves_write_buffer_lists_match_except_global_variables
  (vs: list var_id_t)
  (write_buffer1: list write_message_t)
  (write_buffer2: list write_message_t)
  (write_message: write_message_t)
  : Lemma (requires   write_buffers_match (remove_global_variables_from_write_buffer vs write_buffer1)
                        (remove_global_variables_from_write_buffer vs write_buffer2)
                    /\ pointer_among_global_variables vs write_message.location)
          (ensures  (let write_buffer1' = FStar.List.Tot.append write_buffer1 [write_message] in
                     write_buffers_match (remove_global_variables_from_write_buffer vs write_buffer1')
                       (remove_global_variables_from_write_buffer vs write_buffer2))) =
  pointer_among_gvars_implies_gvars_addressed vs write_message.location;
  append_effect_on_remove_global_variables_from_write_buffer_list vs write_buffer1 write_message

let append_among_gvars_s1_only_preserves_write_buffers_match_except_global_variables
  (vs: list var_id_t)
  (write_buffer1: seq write_message_t)
  (write_buffer2: seq write_message_t)
  (write_message: write_message_t)
  : Lemma (requires   write_buffers_match_except_global_variables vs write_buffer1 write_buffer2
                    /\ pointer_among_global_variables vs write_message.location)
          (ensures  (let write_buffer1' = build write_buffer1 write_message in
                     write_buffers_match_except_global_variables vs write_buffer1' write_buffer2))
          (decreases length write_buffer1 + length write_buffer2) =
  build_equivalent_to_append write_buffer1 write_message;
  append_among_gvars_s1_only_preserves_write_buffer_lists_match_except_global_variables vs (seq_to_list write_buffer1)
    (seq_to_list write_buffer2) write_message

let adding_write_message_among_gvars_s1_only_maintains_positions_in_write_buffers_match_and_positions_valid_for_receiver
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  (receiver_tid: tid_t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ pointer_among_global_variables vs write_message.location
                    /\ positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message in
                       positions_valid_in_threads threads1'
                     /\ write_buffers_match_except_global_variables vs
                         (unread_write_buffer threads1' actor receiver_tid)
                         (unread_write_buffer threads2 actor receiver_tid))) =
  assert (sender_receiver_trigger actor receiver_tid);
  append_among_gvars_s1_only_preserves_write_buffers_match_except_global_variables vs
    (unread_write_buffer threads1 actor receiver_tid)
    (unread_write_buffer threads2 actor receiver_tid)
    write_message;
  unread_write_buffer_commutes_with_append threads1 actor receiver_tid write_message

let adding_write_message_among_gvars_s1_only_maintains_positions_match_and_positions_valid_for_tid_pair
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  (sender_tid: tid_t)
  (receiver_tid: tid_t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ pointer_among_global_variables vs write_message.location
                    /\ positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message in
                       positions_valid_in_threads threads1'
                     /\ (write_buffers_match_except_global_variables vs
                         (unread_write_buffer threads1' sender_tid receiver_tid)
                         (unread_write_buffer threads2 sender_tid receiver_tid)))) =
  if sender_tid <> actor then
    assert (sender_receiver_trigger sender_tid receiver_tid)
  else
    adding_write_message_among_gvars_s1_only_maintains_positions_in_write_buffers_match_and_positions_valid_for_receiver
      vs pc_relation actor write_message threads1 threads2 receiver_tid

let adding_write_message_among_gvars_s1_only_maintains_positions_in_write_buffers_match_and_positions_valid
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (write_message: write_message_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  : Lemma (requires   positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2
                    /\ threads_match_except_global_variables vs pc_relation threads1 threads2
                    /\ pointer_among_global_variables vs write_message.location
                    /\ positions_valid_in_threads threads1
                    /\ positions_valid_in_threads threads2)
          (ensures  (let threads1' = append_to_thread_write_buffer threads1 actor write_message in
                       positions_valid_in_threads threads1'
                     /\ positions_in_write_buffers_match_except_global_variables vs threads1' threads2)) =
  let threads1' = append_to_thread_write_buffer threads1 actor write_message in
  introduce forall sender_tid receiver_tid.
               write_buffers_match_except_global_variables vs
                 (unread_write_buffer threads1' sender_tid receiver_tid)
                 (unread_write_buffer threads2 sender_tid receiver_tid)
  with adding_write_message_among_gvars_s1_only_maintains_positions_match_and_positions_valid_for_tid_pair
         vs pc_relation actor write_message threads1 threads2 sender_tid receiver_tid

#push-options "--z3rlimit 30"

let rec lvalue_computation_among_gvars_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   lvalue_expression_among_global_variables vs exp
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem)
          (ensures  lvalue_computation exp actor s1 == lvalue_computation exp actor s2
                    /\ (match lvalue_computation exp actor s1 with
                       | ComputationProduces p -> pointer_among_global_variables vs p
                       | _ -> True)) =
  match exp with
  | ExpressionGlobalVariable _ var_id -> ()
  | ExpressionFieldOf td obj field_id ->
      lvalue_computation_among_gvars_doesnt_depend_on_gvars vs pc_relation obj actor s1 s2
  | _ -> ()

#pop-options
#push-options "--z3rlimit 30"

let rec update_pointer_directly_among_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (new_storage: valid_object_storage_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   pointer_among_global_variables vs p
                    /\ global_variables_unaddressed_in_storage vs new_storage
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ memories_match_except_global_variables vs mem1 mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ (ComputationProduces? (update_pointer_directly p new_storage mem1)))
          (ensures  (match update_pointer_directly p new_storage mem1 with
                     | ComputationProduces mem1' ->
                           global_variables_unaddressed_in_memory vs mem1'
                         /\ memories_match_except_global_variables vs mem1' mem2
                         /\ roots_match mem1')) =
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
                  update_pointer_directly_among_gvars_s1_only_maintains_states_match vs struct_ptr
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
                  update_pointer_directly_among_gvars_s1_only_maintains_states_match vs array_ptr
                    new_parent mem1 mem2
                )
            | _ -> ())
      | _ -> ())

let update_pointer_among_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
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
                    /\ pointer_among_global_variables vs p
                    /\ (ComputationProduces? (update_pointer p actor writer_pc writer_expression_number
                                               bypassing_write_buffer new_value mem1)))
          (ensures  (match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value mem1 with
                     | ComputationProduces (optional_write_message, mem1') ->
                           memories_match_except_global_variables vs mem1' mem2
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ roots_match mem1')) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id ->
      let root = mem1 root_id in
      (match root_to_storage_computation root with
       | ComputationProduces storage ->
           update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
             writer_expression_number bypassing_write_buffer storage new_value)
  | PointerField struct_ptr field_id ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs struct_ptr mem1;
      (match dereference_computation struct_ptr mem1 with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageStruct fields ->
               let field = index fields field_id in
               update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
                 writer_expression_number bypassing_write_buffer field new_value;
               (match update_storage p actor writer_pc writer_expression_number
                        bypassing_write_buffer field new_value with
                | ComputationProduces (write_message, new_field) ->
                    update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                      vs parent field_id new_field;
                    let new_parent = update_storage_child parent field_id new_field in
                    update_pointer_directly_among_gvars_s1_only_maintains_states_match
                      vs struct_ptr new_parent mem1 mem2)))
  | PointerIndex array_ptr idx ->
      dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs array_ptr mem1;
      (match dereference_computation array_ptr mem1 with
       | ComputationProduces parent ->
          (match parent with
           | ObjectStorageArray element_td elements ->
               let element = index elements idx in
               update_storage_with_gvars_unaddressed_maintains_gvars_unaddressed vs p actor writer_pc
                 writer_expression_number bypassing_write_buffer element new_value;
               (match update_storage p actor writer_pc writer_expression_number
                        bypassing_write_buffer element new_value with
                | ComputationProduces (write_message, new_element) ->
                    update_storage_child_with_gvars_unaddressed_maintains_gvars_unaddressed
                      vs parent idx new_element;
                    let new_parent = update_storage_child parent idx new_element in
                    update_pointer_directly_among_gvars_s1_only_maintains_states_match vs array_ptr new_parent
                      mem1 mem2)))

let update_pointed_to_value_among_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (p: Armada.Pointer.t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
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
                    /\ pointer_among_global_variables vs p
                    /\ (ComputationProduces? (update_pointed_to_value p actor writer_pc writer_expression_number
                                               bypassing_write_buffer new_value s1)))
          (ensures  (match update_pointed_to_value p actor writer_pc writer_expression_number bypassing_write_buffer
                             new_value s1 with
                     | ComputationProduces s1' ->
                           states_match_except_global_variables vs pc_relation s1' s2
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ roots_match s1'.mem)) =
  update_pointer_among_gvars_s1_only_maintains_states_match vs p actor writer_pc
    writer_expression_number bypassing_write_buffer new_value s1.mem s2.mem;
  match update_pointer p actor writer_pc writer_expression_number bypassing_write_buffer new_value s1.mem with
  | ComputationProduces (optional_write_message, new_mem) ->
      (match optional_write_message with
       | Some write_message ->
           let thread = s1.threads actor in
           let new_write_buffer = build thread.write_buffer write_message in
           let new_thread = { thread with write_buffer = new_write_buffer } in
           let new_threads = Spec.Map.upd s1.threads actor new_thread in
           let s1' = { s1 with mem = new_mem; threads = new_threads; } in
           adding_write_message_among_gvars_s1_only_maintains_positions_in_write_buffers_match_and_positions_valid
             vs pc_relation actor write_message s1.threads s2.threads;
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2);
           assert (roots_match s1'.mem)
       | None ->
           let s1' = { s1 with mem = new_mem; } in
           assert (global_variables_unaddressed_in_memory vs s1'.mem);
           assert (states_match_except_global_variables vs pc_relation s1' s2);
           assert (roots_match s1'.mem)
      )

let update_expression_with_lvalue_among_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc: pc_t)
  (writer_expression_number: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ lvalue_expression_among_global_variables vs exp
                    /\ global_variables_unaddressed_in_object_value vs new_value
                    /\ (ComputationProduces? (update_expression exp actor writer_pc writer_expression_number
                                               bypassing_write_buffer new_value s1)))
          (ensures  (match update_expression exp actor writer_pc writer_expression_number
                             bypassing_write_buffer new_value s1 with
                     | ComputationProduces s1' ->
                           states_match_except_global_variables vs pc_relation s1' s2
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ roots_match s1'.mem)) =
  lvalue_computation_among_gvars_doesnt_depend_on_gvars vs pc_relation exp actor s1 s2;
  let td = expression_to_td exp in
  match lvalue_computation exp actor s1 with
  | ComputationProduces p ->
      update_pointed_to_value_among_gvars_s1_only_maintains_states_match vs pc_relation p actor writer_pc
        writer_expression_number bypassing_write_buffer new_value s1 s2

let statement_that_updates_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (* see .fsti file for spec *) =
  match statement_computation actor nd start_pc end_pc statement s1 with
  | ComputationProduces s1' ->
      (match statement with
       | UpdateStatement bypassing_write_buffer dst src ->
           rvalue_computation_when_gvars_unaddressed_produces_value_with_gvars_unaddressed vs src actor s1;
           let src_value = ComputationProduces?.result (rvalue_computation src actor s1) in
           update_expression_with_lvalue_among_gvars_s1_only_maintains_states_match vs pc_relation dst
             actor start_pc 0 bypassing_write_buffer src_value s1 s2;
           assert (states_match_except_global_variables vs pc_relation s1' s2)
       | NondeterministicUpdateStatement bypassing_write_buffer dst ->
           let nd_value = Cons?.hd nd in
           if_object_value_has_all_pointers_uninitialized_then_it_doesnt_depend_on_gvars vs nd_value;
           update_expression_with_lvalue_among_gvars_s1_only_maintains_states_match vs pc_relation dst
             actor start_pc 0 bypassing_write_buffer nd_value s1 s2;
           assert (states_match_except_global_variables vs pc_relation s1' s2))
  | _ -> ()

let positions_in_write_buffers_match_preserved_by_s1_advance_past_gvar_helper
  (vs: list var_id_t)
  (write_buffer1: seq write_message_t)
  (write_buffer2: seq write_message_t)
  (write_message1: write_message_t)
  : Lemma (requires   length write_buffer1 > 0
                    /\ write_message1 == index write_buffer1 0
                    /\ write_buffers_match_except_global_variables vs write_buffer1 write_buffer2
                    /\ not (global_variables_unaddressed_in_write_message vs write_message1))
          (ensures  write_buffers_match_except_global_variables vs (drop write_buffer1 1) write_buffer2) =
  let write_messages1 = seq_to_list write_buffer1 in
  let write_messages2 = seq_to_list write_buffer2 in
  assert (write_buffers_match (remove_global_variables_from_write_buffer vs write_messages1)
            (remove_global_variables_from_write_buffer vs write_messages2));
  match write_messages1 with
  | hd1 :: tl1 ->
      assert (hd1 == write_message1);
      assert (write_buffers_match (remove_global_variables_from_write_buffer vs tl1)
                (remove_global_variables_from_write_buffer vs write_messages2));
      seq_to_list_drop_equals_tail write_buffer1;
      assert (seq_to_list (drop write_buffer1 1) == tl1)

let positions_in_write_buffers_match_preserved_by_s1_advance_past_gvar
  (vs: list var_id_t)
  (threads1: Armada.Threads.t)
  (threads2: Armada.Threads.t)
  (sender_tid: tid_t)
  (receiver_tid: tid_t)
  (threads1': Armada.Threads.t)
  : Lemma (requires (let sender_thread1 = threads1 sender_tid in
                     let receiver_thread1 = threads1 receiver_tid in
                     let write_buffer1 = sender_thread1.write_buffer in
                     let position1 = (threads1 receiver_tid).position_in_other_write_buffers sender_tid in
                       length write_buffer1 > position1
                     /\ positions_valid_in_threads threads1
                     /\ positions_valid_in_threads threads2
                     /\ (let write_message1 = index write_buffer1 position1 in
                        let position_in_other_write_buffers1' =
                          Spec.Map.upd receiver_thread1.position_in_other_write_buffers sender_tid
                            (position1 + 1) in
                        let receiver_thread1' = { receiver_thread1 with position_in_other_write_buffers =
                                                    position_in_other_write_buffers1' } in
                          threads1' == Spec.Map.upd threads1 receiver_tid receiver_thread1'
                        /\ not (global_variables_unaddressed_in_write_message vs write_message1)
                        /\ positions_in_write_buffers_match_except_global_variables vs threads1 threads2)))
          (ensures   positions_valid_in_threads threads1'
                   /\ positions_in_write_buffers_match_except_global_variables vs threads1' threads2) =
  introduce forall sender_tid' receiver_tid'.
     sender_receiver_trigger sender_tid' receiver_tid'
     ==>    position_valid threads1' sender_tid' receiver_tid'
         /\ write_buffers_match_except_global_variables vs
           (unread_write_buffer threads1' sender_tid' receiver_tid')
           (unread_write_buffer threads2 sender_tid' receiver_tid')
  with introduce _ ==> _
  with _. (
    assert (sender_receiver_trigger sender_tid' receiver_tid');
    assert (position_valid threads2 sender_tid' receiver_tid');
    assert (write_buffers_match_except_global_variables vs
              (unread_write_buffer threads1 sender_tid' receiver_tid')
              (unread_write_buffer threads2 sender_tid' receiver_tid'));
    assert ((threads1' sender_tid').write_buffer == (threads1 sender_tid').write_buffer);
    if receiver_tid <> receiver_tid' then (
      assert ((threads1' receiver_tid').position_in_other_write_buffers ==
              (threads1 receiver_tid').position_in_other_write_buffers)
    )
    else if sender_tid <> sender_tid' then (
      assert ((threads1' receiver_tid').position_in_other_write_buffers sender_tid' ==
              (threads1 receiver_tid').position_in_other_write_buffers sender_tid')
    )
    else (
      let sender_thread1 = threads1 sender_tid in
      let receiver_thread1 = threads1 receiver_tid in
      let write_buffer1 = sender_thread1.write_buffer in
      let position1 = (threads1 receiver_tid).position_in_other_write_buffers sender_tid in
      let write_message1 = index write_buffer1 position1 in
      let unread_write_buffer1 = unread_write_buffer threads1 sender_tid receiver_tid in
      let unread_write_buffer2 = unread_write_buffer threads2 sender_tid receiver_tid in
      let unread_write_buffer1' = unread_write_buffer threads1' sender_tid receiver_tid in
      assert (unread_write_buffer1' == drop unread_write_buffer1 1);
      assert (index unread_write_buffer1 0 == write_message1);
      positions_in_write_buffers_match_preserved_by_s1_advance_past_gvar_helper vs unread_write_buffer1
        unread_write_buffer2 write_message1
    )
  )

let propagate_write_message_statement_computation_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (* see .fsti file for spec *) =
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
     ()
  else
    let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    if receiver_tid = actor then // can't propagate to the same thread
      ()
    else
      let propagator_thread1 = s1.threads actor in
      let receiver_thread1 = s1.threads receiver_tid in
      let which_message1 = receiver_thread1.position_in_other_write_buffers actor in
      if which_message1 >= length propagator_thread1.write_buffer then
        false_elim ()
      else (
        assert (which_message1 < length propagator_thread1.write_buffer);
        let write_message1 = index propagator_thread1.write_buffer which_message1 in
        let position_in_other_write_buffers1' =
          Spec.Map.upd receiver_thread1.position_in_other_write_buffers actor (which_message1 + 1) in
        let receiver_thread1' =
          { receiver_thread1 with position_in_other_write_buffers = position_in_other_write_buffers1' } in
        let threads1' = Spec.Map.upd s1.threads receiver_tid receiver_thread1' in
        propagate_write_message_s1_only_among_gvars_maintains_states_match vs write_message1 receiver_tid
          s1.mem s2.mem;
        match propagate_write_message write_message1 receiver_tid s1.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            let s1' = ({ s1 with threads = threads1'; }) in
            positions_in_write_buffers_match_preserved_by_s1_advance_past_gvar vs s1.threads s2.threads
              actor receiver_tid s1'.threads;
            assert (positions_in_write_buffers_match_except_global_variables vs s1'.threads s2.threads)
        | ComputationProduces mem1' ->
            let s1' = ({ s1 with mem = mem1'; threads = threads1'; }) in
            positions_in_write_buffers_match_preserved_by_s1_advance_past_gvar vs s1.threads s2.threads
              actor receiver_tid s1'.threads;
            assert (positions_in_write_buffers_match_except_global_variables vs s1'.threads s2.threads)
      )
