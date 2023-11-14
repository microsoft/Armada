module Strategies.GlobalVars.Util

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
open Strategies.GlobalVars.Value
open Strategies.PCRelation
open Util.List
open Util.Nth
open Util.Seq
open Util.Trigger

let memories_match_except_global_variables_reflexive (vs: list var_id_t) (mem: Armada.Memory.t)
  : Lemma (memories_match_except_global_variables vs mem mem) =
  ()

let memories_match_except_global_variables_commutative
  (vs: list var_id_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (memories_match_except_global_variables vs mem1 mem2 <==>
             memories_match_except_global_variables vs mem2 mem1) =
  ()

let memories_match_except_global_variables_transitive
  (vs: list var_id_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  (mem3: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ memories_match_except_global_variables vs mem2 mem3)
          (ensures  memories_match_except_global_variables vs mem1 mem3) =
  introduce forall root_id. (match root_id with
                        | RootIdGlobal v -> list_contains v vs \/ (mem1 root_id == mem3 root_id)
                        | _ -> mem1 root_id == mem3 root_id)
  with (
    match root_id with
    | RootIdGlobal v ->
        assert (list_contains v vs \/ (mem1 root_id == mem2 root_id));
        assert (list_contains v vs \/ (mem2 root_id == mem3 root_id))
    | _ ->
        assert (mem1 root_id == mem2 root_id);
        assert (mem2 root_id == mem3 root_id)
  )

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

#push-options "--z3rlimit 60"

let update_expression_lacking_pointer_field_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expression vs exp
                    /\ object_td_lacks_pointer_field (expression_to_td exp))
          (ensures  (match update_expression exp actor writer_pc1 writer_expression_number1
                             bypassing_write_buffer new_value s1,
                           update_expression exp actor writer_pc2 writer_expression_number2
                             bypassing_write_buffer new_value s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else (
    lvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2;
    assert (lvalue_computation exp actor s1 == lvalue_computation exp actor s2);
    let td = expression_to_td exp in
    match lvalue_computation exp actor s1 with
    | ComputationProduces p ->
        update_pointed_to_value_lacking_pointer_field_maintains_states_match vs pc_relation p actor
          writer_pc1 writer_pc2 writer_expression_number1 writer_expression_number2 bypassing_write_buffer
          td new_value s1 s2;
        (match update_pointed_to_value p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                 new_value s1,
               update_pointed_to_value p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                 new_value s2 with
         | ComputationProduces s1', ComputationProduces s2' -> ()
         | ComputationImpossible, ComputationImpossible -> ()
         | ComputationUndefined, ComputationUndefined -> ()
         | _, _ -> false_elim ())
    | _ -> ()
  )

#pop-options
#push-options "--z3rlimit 80"

let update_expression_with_gvars_unaddressed_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_value: object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expression vs exp
                    /\ global_variables_unaddressed_in_object_value vs new_value)
          (ensures  (match update_expression exp actor writer_pc1 writer_expression_number1
                             bypassing_write_buffer new_value s1,
                           update_expression exp actor writer_pc2 writer_expression_number2
                             bypassing_write_buffer new_value s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  if   not (expression_valid exp)
     || not (object_value_valid new_value)
     || neqb (object_value_to_td new_value) (expression_to_td exp) then
    ()
  else (
    lvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2;
    assert (lvalue_computation exp actor s1 == lvalue_computation exp actor s2);
    let td = expression_to_td exp in
    match lvalue_computation exp actor s1 with
    | ComputationProduces p ->
        update_pointed_to_value_with_gvars_unaddressed_maintains_states_match vs pc_relation
          p actor writer_pc1 writer_pc2 writer_expression_number1 writer_expression_number2 bypassing_write_buffer
          new_value s1 s2;
        (match update_pointed_to_value p actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                 new_value s1,
               update_pointed_to_value p actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                 new_value s2 with
         | ComputationProduces s1', ComputationProduces s2' -> ()
         | ComputationImpossible, ComputationImpossible -> ()
         | ComputationUndefined, ComputationUndefined -> ()
         | _, _ -> false_elim ())
    | _ -> ()
  )

#pop-options
#push-options "--z3rlimit 10"

let rec update_expressions_with_gvars_unaddressed_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expressions vs exps
                    /\ global_variables_unaddressed_in_object_values vs new_values)
          (ensures  (match update_expressions exps actor writer_pc1 writer_expression_number1
                             bypassing_write_buffer new_values s1,
                           update_expressions exps actor writer_pc2 writer_expression_number2
                             bypassing_write_buffer new_values s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                            states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  match exps, new_values with
  | [], [] -> ()
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation
        first_exp actor writer_pc1 writer_pc2 writer_expression_number1 writer_expression_number2
        bypassing_write_buffer first_new_value s1 s2;
      (match update_expression first_exp actor writer_pc1 writer_expression_number1
               bypassing_write_buffer first_new_value s1,
             update_expression first_exp actor writer_pc2 writer_expression_number2
               bypassing_write_buffer first_new_value s2 with
       | ComputationProduces s1_next, ComputationProduces s2_next ->
           update_expressions_with_gvars_unaddressed_maintains_states_match vs pc_relation
             remaining_exps actor writer_pc1 writer_pc2 (writer_expression_number1 + 1) (writer_expression_number2 + 1)
             bypassing_write_buffer remaining_new_values s1_next s2_next;
           (match update_expressions exps actor writer_pc1 writer_expression_number1
                    bypassing_write_buffer new_values s1,
                  update_expressions exps actor writer_pc2 writer_expression_number2
                    bypassing_write_buffer new_values s2 with
            | ComputationProduces s1', ComputationProduces s2' -> ()
            | ComputationImpossible, ComputationImpossible -> ()
            | ComputationUndefined, ComputationUndefined -> ()
            | _, _ -> ())
       | ComputationImpossible, ComputationImpossible -> ()
       | ComputationUndefined, ComputationUndefined -> ()
       | _, _ -> ())
  | _, _ -> ()

let rec update_expressions_lacking_pointer_field_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exps: list expression_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (new_values: list object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expressions vs exps
                    /\ expressions_lack_pointer_field exps)
          (ensures  (match update_expressions exps actor writer_pc1 writer_expression_number1
                             bypassing_write_buffer new_values s1,
                           update_expressions exps actor writer_pc2 writer_expression_number2
                             bypassing_write_buffer new_values s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                         /\ ThreadStatusRunning? (s1'.threads actor).status
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  match exps, new_values with
  | [], [] -> ()
  | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
      update_expression_lacking_pointer_field_maintains_states_match vs pc_relation
        first_exp actor writer_pc1 writer_pc2 writer_expression_number1 writer_expression_number2
        bypassing_write_buffer first_new_value s1 s2;
      (match update_expression first_exp actor writer_pc1 writer_expression_number1
               bypassing_write_buffer first_new_value s1,
             update_expression first_exp actor writer_pc2 writer_expression_number2
               bypassing_write_buffer first_new_value s2 with
       | ComputationProduces s1_next, ComputationProduces s2_next ->
           update_expressions_lacking_pointer_field_maintains_states_match vs pc_relation
             remaining_exps actor writer_pc1 writer_pc2 (writer_expression_number1 + 1) (writer_expression_number2 + 1)
             bypassing_write_buffer remaining_new_values s1_next s2_next;
           (match update_expressions exps actor writer_pc1 writer_expression_number1
                    bypassing_write_buffer new_values s1,
                  update_expressions exps actor writer_pc2 writer_expression_number2
                    bypassing_write_buffer new_values s2 with
            | ComputationProduces s1', ComputationProduces s2' -> ()
            | ComputationImpossible, ComputationImpossible -> ()
            | ComputationUndefined, ComputationUndefined -> ()
            | _, _ -> ())
       | ComputationImpossible, ComputationImpossible -> ()
       | ComputationUndefined, ComputationUndefined -> ()
       | _, _ -> ())
  | _, _ -> ()

let propagate_write_message_maintains_states_match
  (vs: list var_id_t)
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  (receiver_tid: tid_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ global_variables_unaddressed_in_write_message vs write_message1
                    /\ global_variables_unaddressed_in_write_message vs write_message2
                    /\ write_messages_match write_message1 write_message2)
          (ensures  (match propagate_write_message write_message1 receiver_tid mem1,
                           propagate_write_message write_message2 receiver_tid mem2 with
                     | ComputationProduces mem1', ComputationProduces mem2' ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  let p = write_message1.location in
  dereference_computation_doesnt_depend_on_global_variables vs p mem1 mem2;
  match dereference_computation p mem1 with
  | ComputationProduces storage ->
      (match storage with
       | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
           if   primitive_td <> write_message1.primitive_td
              || write_message1.version >= length values
              || local_versions receiver_tid >= write_message1.version then
             ()
           else
             let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message1.version in
             let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values
                                 new_local_versions in
             if not (object_storage_valid new_storage) then
               ()
             else
               update_pointer_directly_with_gvars_unaddressed_maintains_states_match vs p
                 new_storage mem1 mem2
       | _ -> ()
     )
  | _ -> ()

let propagate_write_message_s1_only_among_gvars_maintains_states_match
  (vs: list var_id_t)
  (write_message1: write_message_t)
  (receiver_tid: tid_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ not (global_variables_unaddressed_in_write_message vs write_message1))
          (ensures  (match propagate_write_message write_message1 receiver_tid mem1 with
                     | ComputationProduces mem1' ->
                           memories_match_except_global_variables vs mem1' mem2
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ roots_match mem1'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True)) =
  let p = write_message1.location in
  dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs p mem1;
  match dereference_computation p mem1 with
  | ComputationProduces storage ->
      (match storage with
       | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
           if   primitive_td <> write_message1.primitive_td
              || write_message1.version >= length values
              || local_versions receiver_tid >= write_message1.version then
             ()
           else (
             let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message1.version in
             let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values
                                 new_local_versions in
             assert (global_variables_unaddressed_in_storage vs new_storage);
             if not (object_storage_valid new_storage) then
               ()
             else
               update_pointer_directly_s1_only_among_gvars_maintains_states_match vs p new_storage mem1 mem2
           )
       | _ -> ()
     )
  | _ -> ()

let propagate_write_message_s2_only_among_gvars_maintains_states_match
  (vs: list var_id_t)
  (write_message2: write_message_t)
  (receiver_tid: tid_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ not (global_variables_unaddressed_in_write_message vs write_message2))
          (ensures  (match propagate_write_message write_message2 receiver_tid mem2 with
                     | ComputationProduces mem2' ->
                           memories_match_except_global_variables vs mem1 mem2'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem2'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True)) =
  let p = write_message2.location in
  dereference_computation_when_gvars_unaddressed_produces_storage_with_gvars_unaddressed vs p mem2;
  match dereference_computation p mem2 with
  | ComputationProduces storage ->
      (match storage with
       | ObjectStorageWeaklyConsistentPrimitive primitive_td values local_versions ->
           if   primitive_td <> write_message2.primitive_td
              || write_message2.version >= length values
              || local_versions receiver_tid >= write_message2.version then
             ()
           else (
             let new_local_versions = Spec.Map.upd local_versions receiver_tid write_message2.version in
             let new_storage = ObjectStorageWeaklyConsistentPrimitive primitive_td values
                                 new_local_versions in
             assert (global_variables_unaddressed_in_storage vs new_storage);
             if not (object_storage_valid new_storage) then
               ()
             else
               update_pointer_directly_s2_only_among_gvars_maintains_states_match vs p new_storage mem1 mem2
           )
       | _ -> ()
     )
  | _ -> ()

let check_expression_up_to_date_for_rmw_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expression vs exp)
          (ensures  check_expression_up_to_date_for_rmw exp actor s1 ==
                    check_expression_up_to_date_for_rmw exp actor s2) =
  if not (expression_valid exp) then
    ()
  else (
    lvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2;
    match lvalue_computation exp actor s1 with
    | ComputationProduces p -> dereference_computation_doesnt_depend_on_global_variables vs p s1.mem s2.mem
    | _ -> ()
  )

let rec if_object_value_has_all_pointers_uninitialized_then_it_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (value: object_value_t)
  : Lemma (requires object_value_has_all_pointers_uninitialized value)
          (ensures  global_variables_unaddressed_in_object_value vs value)
          (decreases rank value) =
  match value with
  | ObjectValuePrimitive primitive_value -> ()
  | ObjectValueStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      introduce forall field. contains fields field ==> global_variables_unaddressed_in_object_value vs field
      with introduce _ ==> _
      with _. if_object_value_has_all_pointers_uninitialized_then_it_doesnt_depend_on_gvars vs field
  | ObjectValueArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      introduce forall element. contains elements element ==> global_variables_unaddressed_in_object_value vs element
      with introduce _ ==> _
      with _. if_object_value_has_all_pointers_uninitialized_then_it_doesnt_depend_on_gvars vs element
  | ObjectValueAbstract ty value -> ()

let rec object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (storage: object_storage_t)
  : Lemma (requires object_storage_arbitrarily_initialized_correctly storage)
          (ensures  global_variables_unaddressed_in_storage vs storage)
          (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions -> ()
  | ObjectStoragePrimitive primitive_value -> ()
  | ObjectStorageStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      introduce forall field. contains fields field ==> global_variables_unaddressed_in_storage vs field
      with introduce _ ==> _
      with _. object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs field
  | ObjectStorageArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      introduce forall element. contains elements element ==> global_variables_unaddressed_in_storage vs element
      with introduce _ ==> _
      with _. object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs element
  | ObjectStorageAbstract ty value -> ()

let rec object_storage_zero_filled_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (storage: object_storage_t)
  : Lemma (requires is_storage_zero_filled storage)
          (ensures  global_variables_unaddressed_in_storage vs storage)
          (decreases rank storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions -> ()
  | ObjectStoragePrimitive primitive_value -> ()
  | ObjectStorageStruct fields ->
      assert (forall field. contains fields field ==> rank field << rank fields);
      introduce forall field. contains fields field ==> global_variables_unaddressed_in_storage vs field
      with introduce _ ==> _
      with _. object_storage_zero_filled_doesnt_depend_on_gvars vs field
  | ObjectStorageArray element_td elements ->
      assert (forall element. contains elements element ==> rank element << rank elements);
      introduce forall element. contains elements element ==> global_variables_unaddressed_in_storage vs element
      with introduce _ ==> _
      with _. object_storage_zero_filled_doesnt_depend_on_gvars vs element
  | ObjectStorageAbstract ty value -> ()

let rec object_storage_initialized_correctly_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (storage: object_storage_t)
  (value: object_value_t)
  : Lemma (requires   global_variables_unaddressed_in_object_value vs value
                    /\ object_storage_initialized_correctly storage value)
          (ensures  global_variables_unaddressed_in_storage vs storage) =
  match storage with
  | ObjectStorageWeaklyConsistentPrimitive _ values local_versions -> ()
  | ObjectStoragePrimitive value -> ()
  | ObjectStorageStruct fields ->
      global_variables_unaddressed_in_storages_equivalent_to_forall vs fields;
      introduce forall field. contains fields field ==> global_variables_unaddressed_in_storage vs field
      with introduce _ ==> _
      with _. (
        let i = seq_contains_to_index fields field in
        let field_values = ObjectValueStruct?.fields value in
        let field_value = index field_values i in
        assert (rank field << rank fields);
        object_storage_initialized_correctly_doesnt_depend_on_gvars vs field field_value
      )
  | ObjectStorageArray element_td elements ->
      global_variables_unaddressed_in_storages_equivalent_to_forall vs elements;
      introduce forall element. contains elements element ==> global_variables_unaddressed_in_storage vs element
      with introduce _ ==> _
      with _. (
        let i = seq_contains_to_index elements element in
        let element_values = ObjectValueArray?.elements value in
        let element_value = index element_values i in
        assert (rank element << rank elements);
        object_storage_initialized_correctly_doesnt_depend_on_gvars vs element element_value
      )
  | ObjectStorageAbstract ty value -> ()

#pop-options
#push-options "--z3rlimit 40"

let push_stack_variable_doesnt_depend_on_gvars_helper
  (vs: list var_id_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  (thread1: Armada.Thread.t)
  (thread2: Armada.Thread.t)
  (local_variables1': list var_id_t)
  (local_variables2': list var_id_t)
  (top1': stack_frame_t)
  (top2': stack_frame_t)
  (thread1': Armada.Thread.t)
  (thread2': Armada.Thread.t)
  (threads1': Armada.Threads.t)
  (threads2': Armada.Threads.t)
  : Lemma (requires   positions_valid_in_state s1
                    /\ positions_valid_in_state s2
                    /\ positions_in_write_buffers_match_except_global_variables vs s1.threads s2.threads
                    /\ thread1 == s1.threads actor
                    /\ thread2 == s2.threads actor
                    /\ local_variables1' == initializer.var_id :: thread1.top.local_variables
                    /\ local_variables2' == initializer.var_id :: thread2.top.local_variables
                    /\ top1' == { thread1.top with local_variables = local_variables1' }
                    /\ top2' == { thread2.top with local_variables = local_variables2' }
                    /\ thread1' == { thread1 with top = top1' }
                    /\ thread2' == { thread2 with top = top2' }
                    /\ threads1' == Spec.Map.upd s1.threads actor thread1'
                    /\ threads2' == Spec.Map.upd s2.threads actor thread2'
                    /\ positions_valid_in_threads threads1'
                    /\ positions_valid_in_threads threads2')
          (ensures  positions_in_write_buffers_match_except_global_variables vs threads1' threads2') =
  introduce forall sender_tid receiver_tid. write_buffers_match_except_global_variables vs
                                         (unread_write_buffer threads1' sender_tid receiver_tid)
                                         (unread_write_buffer threads2' sender_tid receiver_tid)
  with (
    assert (sender_receiver_trigger sender_tid receiver_tid);
    assert (write_buffers_match_except_global_variables vs
               (unread_write_buffer s1.threads sender_tid receiver_tid)
               (unread_write_buffer s2.threads sender_tid receiver_tid));
    assert (unread_write_buffer threads1' sender_tid receiver_tid ==
              unread_write_buffer s1.threads sender_tid receiver_tid);
    assert (unread_write_buffer threads2' sender_tid receiver_tid ==
              unread_write_buffer s2.threads sender_tid receiver_tid)
  );
  assert (positions_in_write_buffers_match_except_global_variables vs threads1' threads2')

let push_stack_variable_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializer: initializer_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unaddressed_in_initializer vs initializer)
          (ensures  (match push_stack_variable actor writer_pc1 writer_expression_number1 method_id frame_uniq
                             initializer s1,
                           push_stack_variable actor writer_pc2 writer_expression_number2 method_id frame_uniq
                             initializer s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                         /\ ThreadStatusRunning? (s1'.threads actor).status
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _, _ -> False)) =
  let root_id = RootIdStack actor method_id frame_uniq initializer.var_id in
  let root = s1.mem root_id in
  assert (root == s2.mem root_id);
  if not (stack_variable_ready_for_push root initializer) then
    ()
  else (
    object_storage_arbitrarily_initialized_correctly_doesnt_depend_on_gvars vs (RootStackVariable?.storage root);
    let thread1 = s1.threads actor in
    let thread2 = s2.threads actor in
    let var_id = initializer.var_id in
    if list_contains var_id thread1.top.local_variables then
      ()
    else (
      let local_variables1' = var_id :: thread1.top.local_variables in
      let local_variables2' = var_id :: thread2.top.local_variables in
      let top1' = { thread1.top with local_variables = local_variables1' } in
      let top2' = { thread2.top with local_variables = local_variables2' } in
      let thread1' = { thread1 with top = top1' } in
      let thread2' = { thread2 with top = top2' } in
      let threads1' = Spec.Map.upd s1.threads actor thread1' in
      let threads2' = Spec.Map.upd s2.threads actor thread2' in
      let root' = RootStackVariable true false (RootStackVariable?.storage root) in
      let mem1' = Spec.Map.upd s1.mem root_id root' in
      let mem2' = Spec.Map.upd s2.mem root_id root' in
      let s1' = { s1 with mem = mem1'; threads = threads1' } in
      let s2' = { s2 with mem = mem2'; threads = threads2' } in
      push_stack_variable_doesnt_depend_on_gvars_helper vs actor writer_pc1 writer_pc2
        writer_expression_number1 writer_expression_number2
        method_id frame_uniq initializer s1 s2 thread1 thread2 local_variables1' local_variables2' top1'
        top2' thread1' thread2' threads1' threads2';
      assert (threads_match_except_global_variables vs pc_relation s1'.threads s2'.threads);
      assert (states_match_except_global_variables vs pc_relation s1' s2');
      assert (roots_match s1'.mem);
      assert (roots_match s2'.mem);
      (match initializer.iv with
       | InitializerArbitrary td -> ()
       | InitializerSpecific value ->
           let td = (object_value_to_td value) in
           update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation
             (ExpressionLocalVariable td var_id) actor writer_pc1 writer_pc2
             writer_expression_number1 writer_expression_number2 false value s1' s2'
      )
    )
  )

let rec push_stack_variables_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (initializers: list initializer_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unaddressed_in_initializers vs initializers)
          (ensures  (match push_stack_variables actor writer_pc1 writer_expression_number1 method_id frame_uniq
                             initializers s1,
                           push_stack_variables actor writer_pc2 writer_expression_number2 method_id frame_uniq
                             initializers s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                         /\ ThreadStatusRunning? (s1'.threads actor).status
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))
          (decreases initializers) =
  match initializers with
  | [] -> ()
  | first_initializer :: remaining_initializers ->
      push_stack_variable_doesnt_depend_on_gvars vs pc_relation actor writer_pc1 writer_pc2
        writer_expression_number1 writer_expression_number2 method_id frame_uniq first_initializer s1 s2;
      (match push_stack_variable actor writer_pc1 writer_expression_number1 method_id frame_uniq
               first_initializer s1,
             push_stack_variable actor writer_pc2 writer_expression_number2 method_id frame_uniq
               first_initializer s2 with
       | ComputationProduces s1_next, ComputationProduces s2_next ->
          push_stack_variables_doesnt_depend_on_gvars vs pc_relation actor writer_pc1 writer_pc2
            (writer_expression_number1 + 1) (writer_expression_number2 + 1)
            method_id frame_uniq remaining_initializers s1_next s2_next;
          (match push_stack_variables actor writer_pc1 writer_expression_number1 method_id frame_uniq
                   initializers s1,
                 push_stack_variables actor writer_pc2 writer_expression_number2 method_id frame_uniq
                   initializers s2 with
           | ComputationProduces s1', ComputationProduces s2' ->
               assert (states_match_except_global_variables vs pc_relation s1' s2');
               assert (global_variables_unaddressed_in_memory vs s1'.mem);
               assert (global_variables_unaddressed_in_memory vs s2'.mem);
               assert (roots_match s1'.mem);
               assert (roots_match s2'.mem)
           | ComputationImpossible, ComputationImpossible -> ()
           | ComputationUndefined, ComputationUndefined -> ()
           | _ -> ())
       | ComputationImpossible, ComputationImpossible -> ()
       | ComputationUndefined, ComputationUndefined -> ()
       | _, _ -> ())
  | _ -> ()

let rec push_stack_parameters_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (parameters: list object_value_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unaddressed_in_object_values vs parameters)
          (ensures  (match push_stack_parameters actor writer_pc1 writer_expression_number1 method_id frame_uniq
                             var_ids parameters s1,
                           push_stack_parameters actor writer_pc2 writer_expression_number2 method_id frame_uniq
                             var_ids parameters s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                         /\ ThreadStatusRunning? (s1'.threads actor).status
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))
          (decreases parameters) =
  match parameters, var_ids with
  | [], [] -> ()
  | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
      let first_initializer = {
        var_id = first_var_id;
        iv = InitializerSpecific first_parameter;
        weakly_consistent = false
      } in
      push_stack_variable_doesnt_depend_on_gvars vs pc_relation actor writer_pc1 writer_pc2
        writer_expression_number1 writer_expression_number2 method_id frame_uniq first_initializer s1 s2;
      (match push_stack_variable actor writer_pc1 writer_expression_number1 method_id frame_uniq
               first_initializer s1,
             push_stack_variable actor writer_pc2 writer_expression_number2 method_id frame_uniq
               first_initializer s2 with
       | ComputationProduces s1_next, ComputationProduces s2_next ->
           push_stack_parameters_doesnt_depend_on_gvars vs pc_relation actor writer_pc1 writer_pc2
             (writer_expression_number1 + 1) (writer_expression_number2 + 1)
             method_id frame_uniq remaining_var_ids remaining_parameters s1_next s2_next;
           (match push_stack_parameters actor writer_pc1 writer_expression_number1 method_id frame_uniq
                    var_ids parameters s1,
                  push_stack_parameters actor writer_pc2 writer_expression_number2 method_id frame_uniq
                    var_ids parameters s2 with
            | ComputationProduces s1', ComputationProduces s2' ->
                assert (states_match_except_global_variables vs pc_relation s1' s2');
                assert (global_variables_unaddressed_in_memory vs s1'.mem);
                assert (global_variables_unaddressed_in_memory vs s2'.mem);
                assert (roots_match s1'.mem);
                assert (roots_match s2'.mem)
            | ComputationImpossible, ComputationImpossible -> ()
            | ComputationUndefined, ComputationUndefined -> ()
            | _, _ -> ())
       | ComputationImpossible, ComputationImpossible -> ()
       | ComputationUndefined, ComputationUndefined -> ()
       | _, _ -> ())
  | _ -> ()

let pop_stack_variable_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_id: var_id_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  (match pop_stack_variable actor method_id frame_uniq var_id mem1,
                           pop_stack_variable actor method_id frame_uniq var_id mem2 with
                     | ComputationProduces mem1', ComputationProduces mem2' ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  ()

let rec pop_stack_variables_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (frame_uniq: root_id_uniquifier_t)
  (var_ids: list var_id_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  (match pop_stack_variables actor method_id frame_uniq var_ids mem1,
                           pop_stack_variables actor method_id frame_uniq var_ids mem2 with
                     | ComputationProduces mem1', ComputationProduces mem2' ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  match var_ids with
  | [] -> ()
  | first_var_id :: remaining_var_ids ->
      pop_stack_variable_doesnt_depend_on_gvars vs actor method_id frame_uniq first_var_id mem1 mem2;
      (match pop_stack_variable actor method_id frame_uniq first_var_id mem1,
             pop_stack_variable actor method_id frame_uniq first_var_id mem2 with
       | ComputationProduces mem1_next, ComputationProduces mem2_next ->
           pop_stack_variables_doesnt_depend_on_gvars vs actor method_id frame_uniq remaining_var_ids
             mem1_next mem2_next;
           (match pop_stack_variables actor method_id frame_uniq remaining_var_ids mem1_next,
                  pop_stack_variables actor method_id frame_uniq remaining_var_ids mem2_next with
            | ComputationProduces mem1', ComputationProduces mem2' ->
                assert (ComputationProduces mem1' == pop_stack_variables actor method_id frame_uniq var_ids mem1);
                assert (ComputationProduces mem2' == pop_stack_variables actor method_id frame_uniq var_ids mem2);
                assert (memories_match_except_global_variables vs mem1' mem2');
                assert (global_variables_unaddressed_in_memory vs mem1');
                assert (global_variables_unaddressed_in_memory vs mem2');
                assert (roots_match mem1');
                assert (roots_match mem2')
            | ComputationImpossible, ComputationImpossible -> ()
            | ComputationUndefined, ComputationUndefined -> ()
            | _ -> ())
       | ComputationImpossible, ComputationImpossible -> ()
       | ComputationUndefined, ComputationUndefined -> ()
       | _ -> ())
  | _ -> ()

let free_pointer_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (ptr_value: valid_object_value_t (ObjectTDPrimitive PrimitiveTDPointer))
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2
                    /\ global_variables_unaddressed_in_object_value vs ptr_value)
          (ensures  (let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
                     match free_pointer p mem1, free_pointer p mem2 with
                     | ComputationProduces mem1', ComputationProduces mem2' ->
                           memories_match_except_global_variables vs mem1' mem2'
                         /\ global_variables_unaddressed_in_memory vs mem1'
                         /\ global_variables_unaddressed_in_memory vs mem2'
                         /\ roots_match mem1'
                         /\ roots_match mem2'
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False)) =
  let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
  match p with
  | PointerIndex (PointerRoot root_id) idx ->
      if idx <> 0 then
        ()
      else
        (match mem1 root_id with
         | RootAllocated allocated freed storage ->
             if not allocated || freed then
               ()
             else (
               let root' = RootAllocated true true storage in
               let mem1' = Spec.Map.upd mem1 root_id root' in
               let mem2' = Spec.Map.upd mem2 root_id root' in
               assert (memories_match_except_global_variables vs mem1' mem2');
               assert (global_variables_unaddressed_in_memory vs mem1');
               assert (global_variables_unaddressed_in_memory vs mem2')
             )
         | _ -> ())
  | _ -> ()

let rec external_method_take_snapshot_of_reads_clauses_computation_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (writer_pc1: pc_t)
  (writer_pc2: pc_t)
  (writer_expression_number1: nat)
  (writer_expression_number2: nat)
  (bypassing_write_buffer: bool)
  (reads_clauses: list (var_id_t * expression_t))
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_reads_clauses vs reads_clauses)
          (ensures  (match external_method_take_snapshot_of_reads_clauses_computation actor writer_pc1
                             writer_expression_number1 bypassing_write_buffer reads_clauses s1,
                           external_method_take_snapshot_of_reads_clauses_computation actor writer_pc2
                             writer_expression_number2 bypassing_write_buffer reads_clauses s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))
          (decreases reads_clauses) =
  match reads_clauses with
  | [] -> ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation first_reads_expression actor s1 s2;
      (match rvalue_computation first_reads_expression actor s1 with
       | ComputationProduces first_value ->
           let td = expression_to_td first_reads_expression in
           let local_var = ExpressionLocalVariable td first_var_id in
           update_expression_with_gvars_unaddressed_maintains_states_match vs pc_relation local_var actor
             writer_pc1 writer_pc2 writer_expression_number1 writer_expression_number2
             bypassing_write_buffer first_value s1 s2;
           (match update_expression local_var actor writer_pc1 writer_expression_number1 bypassing_write_buffer
                    first_value s1,
                  update_expression local_var actor writer_pc2 writer_expression_number2 bypassing_write_buffer
                    first_value s2 with
            | ComputationProduces s1_next, ComputationProduces s2_next ->
                external_method_take_snapshot_of_reads_clauses_computation_doesnt_depend_on_gvars vs pc_relation
                  actor writer_pc1 writer_pc2 (writer_expression_number1 + 1) (writer_expression_number2 + 1)
                  bypassing_write_buffer remaining_reads_clauses s1_next s2_next
            | ComputationImpossible, ComputationImpossible -> ()
            | ComputationUndefined, ComputationUndefined -> ()
            | _ -> ())
       | _ -> ())

let rec external_method_check_snapshot_computation_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (reads_clauses: list (var_id_t * expression_t))
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_reads_clauses vs reads_clauses)
          (ensures  external_method_check_snapshot_computation actor reads_clauses s1 ==
                    external_method_check_snapshot_computation actor reads_clauses s2)
          (decreases reads_clauses) =
  match reads_clauses with
  | [] -> ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation first_reads_expression actor s1 s2;
      (match rvalue_computation first_reads_expression actor s1 with
       | ComputationProduces first_value ->
           let td = expression_to_td first_reads_expression in
           let local_var = ExpressionLocalVariable td first_var_id in
           rvalue_computation_doesnt_depend_on_global_variables vs pc_relation local_var actor s1 s2;
           (match rvalue_computation local_var actor s1 with
            | ComputationProduces snapshot_value ->
                if neqb first_value snapshot_value then
                  ()
                else
                  external_method_check_snapshot_computation_doesnt_depend_on_gvars vs pc_relation
                    actor remaining_reads_clauses s1 s2
            | _ -> ())
       | _ -> ())

let rec log_expressions_computation_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (logs_clauses: list expression_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ global_variables_unmentioned_in_expressions vs logs_clauses)
          (ensures  (match log_expressions_computation actor logs_clauses s1,
                           log_expressions_computation actor logs_clauses s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))
          (decreases logs_clauses) =
  match logs_clauses with
  | [] -> ()
  | first_logs_clause :: remaining_logs_clauses ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation first_logs_clause actor s1 s2;
      (match rvalue_computation first_logs_clause actor s1 with
       | ComputationProduces event ->
           let trace1' = s1.trace $:: event in
           let s1' = { s1 with trace = trace1' } in
           let trace2' = s2.trace $:: event in
           let s2' = { s2 with trace = trace2' } in
           log_expressions_computation_doesnt_depend_on_gvars vs pc_relation actor remaining_logs_clauses s1' s2'
       | _ -> ())

#pop-options
#push-options "--z3rlimit 10"

let make_thread_running_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (method_id: method_id_t)
  (initial_pc1: pc_t)
  (initial_pc2: pc_t)
  (new_tid: tid_t)
  (frame_uniq: root_id_uniquifier_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ pc_relation.relation initial_pc1 initial_pc2)
          (ensures  (let s1' = make_thread_running method_id initial_pc1 new_tid frame_uniq s1 in
                     let s2' = make_thread_running method_id initial_pc2 new_tid frame_uniq s2 in
                       states_match_except_global_variables vs pc_relation s1' s2'
                     /\ global_variables_unaddressed_in_memory vs s1'.mem
                     /\ global_variables_unaddressed_in_memory vs s2'.mem
                     /\ roots_match s1'.mem
                     /\ roots_match s2'.mem)) =
  assert (stacks_match_per_pc_relation pc_relation [] [])

let push_stack_frame_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (method_id: method_id_t)
  (return_pc1: pc_t)
  (return_pc2: pc_t)
  (frame_uniq: root_id_uniquifier_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ pc_relation.relation return_pc1 return_pc2
                    /\ pc_relation.return_relation return_pc1 return_pc2)
          (ensures  (let s1' = push_stack_frame actor method_id return_pc1 frame_uniq s1 in
                     let s2' = push_stack_frame actor method_id return_pc2 frame_uniq s2 in
                       states_match_except_global_variables vs pc_relation s1' s2'
                     /\ global_variables_unaddressed_in_memory vs s1'.mem
                     /\ global_variables_unaddressed_in_memory vs s2'.mem
                     /\ roots_match s1'.mem
                     /\ roots_match s2'.mem)) =
  let s1' = push_stack_frame actor method_id return_pc1 frame_uniq s1 in
  let s2' = push_stack_frame actor method_id return_pc2 frame_uniq s2 in
  assert (stacks_match_per_pc_relation pc_relation (s1'.threads actor).stack (s2'.threads actor).stack)

let pop_stack_frame_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (mem1': Armada.Memory.t)
  (mem2': Armada.Memory.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   Cons? (s1.threads actor).stack
                    /\ Cons? (s2.threads actor).stack
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ memories_match_except_global_variables vs mem1' mem2'
                    /\ global_variables_unaddressed_in_memory vs mem1'
                    /\ global_variables_unaddressed_in_memory vs mem2'
                    /\ roots_match mem1'
                    /\ roots_match mem2')
          (ensures  (let s1' = pop_stack_frame actor mem1' s1 in
                     let s2' = pop_stack_frame actor mem2' s2 in
                       states_match_except_global_variables vs pc_relation s1' s2'
                     /\ global_variables_unaddressed_in_memory vs s1'.mem
                     /\ global_variables_unaddressed_in_memory vs s2'.mem
                     /\ roots_match s1'.mem
                     /\ roots_match s2'.mem)) =
  ()

let mark_allocation_root_allocated_doesnt_depend_on_gvars
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (uniq: root_id_uniquifier_t)
  (storage: valid_object_storage_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ global_variables_unaddressed_in_storage vs storage)
          (ensures  (let s1' = mark_allocation_root_allocated uniq storage s1 in
                     let s2' = mark_allocation_root_allocated uniq storage s2 in
                       states_match_except_global_variables vs pc_relation s1' s2'
                     /\ global_variables_unaddressed_in_memory vs s1'.mem
                     /\ global_variables_unaddressed_in_memory vs s2'.mem
                     /\ roots_match s1'.mem
                     /\ roots_match s2'.mem)) =
  let s1' = mark_allocation_root_allocated uniq storage s1 in
  let s2' = mark_allocation_root_allocated uniq storage s2 in
  assert (states_match_except_global_variables vs pc_relation s1' s2');
  assert (roots_match s1'.mem);
  assert (roots_match s2'.mem)
