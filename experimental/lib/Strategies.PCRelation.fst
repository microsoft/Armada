module Strategies.PCRelation

open Armada.Base
open Armada.Thread
open Armada.Threads
open Spec.Ubool
open Strategies.ArmadaInvariant.PositionsValid
open Util.Relation

noeq type pc_relation_t = {
  relation: relation_t pc_t pc_t;
  return_relation: one_to_one_relation_t pc_t pc_t;
}

let equality_pc_relation : pc_relation_t =
  {
    relation = (fun pc1 pc2 -> pc1 = pc2);
    return_relation = (fun pc1 pc2 -> pc1 = pc2);
  }

let optional_pcs_match_per_pc_relation
  (pc_relation: pc_relation_t)
  (opc1: option pc_t)
  (opc2: option pc_t)
  : GTot bool =
  match opc1, opc2 with
  | Some pc1, Some pc2 -> pc_relation.relation pc1 pc2
  | None, None -> true
  | _, _ -> false

let extended_stack_frames_match_per_pc_relation
  (pc_relation: pc_relation_t)
  (eframe1: extended_stack_frame_t)
  (eframe2: extended_stack_frame_t)
  : GTot ubool =
    pc_relation.relation eframe1.return_pc eframe2.return_pc
  /\ pc_relation.return_relation eframe1.return_pc eframe2.return_pc
  /\ eframe1.frame == eframe2.frame

let rec stacks_match_per_pc_relation
  (pc_relation: pc_relation_t)
  (stack1: list extended_stack_frame_t)
  (stack2: list extended_stack_frame_t)
  : GTot ubool =
  match stack1, stack2 with
  | [], [] -> True    
  | eframe1 :: tail1, eframe2 :: tail2 ->
        extended_stack_frames_match_per_pc_relation pc_relation eframe1 eframe2
      /\ stacks_match_per_pc_relation pc_relation tail1 tail2
  | _ -> False

let threads_match_except_write_buffers_per_pc_relation
  (pc_relation: pc_relation_t)
  (threads1: Armada.Threads.t{positions_valid_in_threads threads1})
  (threads2: Armada.Threads.t{positions_valid_in_threads threads2})
  : GTot ubool =
  forall tid.{:pattern (threads1 tid).status}
    let thread1 = threads1 tid in
    let thread2 = threads2 tid in
      thread1.status == thread2.status
    /\ (ThreadStatusRunning? thread1.status ==>
            pc_relation.relation thread1.pc thread2.pc
         /\ thread1.top == thread2.top
         /\ stacks_match_per_pc_relation pc_relation thread1.stack thread2.stack)

let write_messages_match
  (write_message1: write_message_t)
  (write_message2: write_message_t)
  : GTot bool =
     write_message1.location = write_message2.location
  && write_message1.primitive_td = write_message2.primitive_td
  && write_message1.version = write_message2.version
  // no need for any relationship for writer_pc and writer_expression_number fields since they don't affect behavior

let rec write_buffers_match
  (write_buffer1: list write_message_t)
  (write_buffer2: list write_message_t)
  : GTot ubool =
  match write_buffer1, write_buffer2 with
  | [], [] -> True
  | write_message1 :: tail1, write_message2 :: tail2 ->
        write_messages_match write_message1 write_message2
      /\ write_buffers_match tail1 tail2
  | _, _ -> False

let rec equality_pc_relation_implies_stack_matches_itself
  (stack: list extended_stack_frame_t)
  : Lemma (stacks_match_per_pc_relation equality_pc_relation stack stack) =
  match stack with
  | [] -> ()
  | eframe :: tail -> equality_pc_relation_implies_stack_matches_itself tail

let rec equality_pc_relation_implies_write_buffer_matches_itself
  (write_buffer: list write_message_t)
  : Lemma (ensures write_buffers_match write_buffer write_buffer) =
  match write_buffer with
  | [] -> ()
  | write_message :: tail -> equality_pc_relation_implies_write_buffer_matches_itself tail
