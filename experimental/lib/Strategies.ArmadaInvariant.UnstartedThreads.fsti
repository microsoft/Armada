module Strategies.ArmadaInvariant.UnstartedThreads

open Armada.Base
open Armada.Computation
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool

let unstarted_threads_have_empty_write_buffers (s: Armada.State.t) : GTot ubool =
  forall tid. let thread = s.threads tid in
         ThreadStatusNotStarted? thread.status ==> length thread.write_buffer = 0

val init_implies_unstarted_threads_have_empty_write_buffers (program: Armada.Program.t) (s: Armada.State.t)
  : Lemma (requires init_program program s)
          (ensures  unstarted_threads_have_empty_write_buffers s)

val executing_statement_maintains_unstarted_threads_have_empty_write_buffers
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s: Armada.State.t)
  : Lemma (requires   ThreadStatusRunning? (s.threads actor).status
                    /\ unstarted_threads_have_empty_write_buffers s)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s with
                     | ComputationImpossible | ComputationUndefined -> True
                     | ComputationProduces s' -> unstarted_threads_have_empty_write_buffers s'))
