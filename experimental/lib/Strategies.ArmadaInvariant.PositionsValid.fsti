module Strategies.ArmadaInvariant.PositionsValid

open Armada.Base
open Armada.Computation
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Type
open FStar.Sequence.Base
open Spec.Ubool

let position_valid (threads: Armada.Threads.t) (sender_tid: tid_t) (receiver_tid: tid_t) : GTot bool =
  let sender_thread = threads sender_tid in
  let receiver_thread = threads receiver_tid in
  let position = receiver_thread.position_in_other_write_buffers sender_tid in
  position <= length sender_thread.write_buffer

let sender_receiver_trigger (sender_tid: tid_t) (receiver_tid: tid_t) : GTot bool =
  true

let positions_valid_in_threads (threads: Armada.Threads.t) : GTot ubool =
  forall sender_tid receiver_tid.{:pattern sender_receiver_trigger sender_tid receiver_tid}
    sender_receiver_trigger sender_tid receiver_tid
    ==> position_valid threads sender_tid receiver_tid

let positions_valid_in_state (s: Armada.State.t) : GTot ubool =
  positions_valid_in_threads s.threads

val init_implies_positions_valid_in_state (program: Armada.Program.t) (s: Armada.State.t)
  : Lemma (requires init_program program s)
          (ensures  positions_valid_in_state s)

val propagate_write_message_statement_computation_maintains_positions_valid_in_state
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s: Armada.State.t)
  : Lemma (requires positions_valid_in_state s)
          (ensures  (match propagate_write_message_statement_computation actor nd s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> positions_valid_in_state s'))

val executing_statement_maintains_positions_valid_in_state
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (requires positions_valid_in_state s)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s with
                     | ComputationProduces s' -> positions_valid_in_state s'
                     | _ -> True))
