module Armada.Thread

open Armada.Base
open Armada.Type
open FStar.Sequence.Base
open FStar.List.Tot
open Spec.Ubool

type thread_status_t =
  | ThreadStatusNotStarted: thread_status_t
  | ThreadStatusRunning: thread_status_t
  | ThreadStatusJoinable: thread_status_t
  | ThreadStatusPostJoin: thread_status_t

noeq type stack_frame_t = {
  method_id: method_id_t;
  frame_uniq: root_id_uniquifier_t;
  local_variables: list var_id_t;
}

noeq type extended_stack_frame_t = {
  return_pc: pc_t;
  frame: stack_frame_t;
}

noeq type write_message_t = {
  location: Armada.Pointer.t;
  primitive_td: primitive_td_t;
  version: nat;
  writer_pc: pc_t;
  writer_expression_number: nat;
}

noeq type t = {
  status: thread_status_t;
  pc: pc_t;
  top: stack_frame_t;
  stack: list extended_stack_frame_t;
  write_buffer: seq write_message_t;
  position_in_other_write_buffers: Spec.Map.t tid_t nat;
}
