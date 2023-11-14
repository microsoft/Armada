module Armada.Program

open Armada.Action
open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.Step
open Armada.State
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.Behavior
open Spec.List
open Spec.Ubool

noeq type t = {
  main_method_id: method_id_t;
  main_start_pc: pc_t;
  global_initializers: list initializer_t;
  main_stack_initializers: list initializer_t;
  program_statements: list program_statement_t;
}

let program_contains_statement_of_step (program: Armada.Program.t) (step: Armada.Step.t) : GTot ubool =
  contains_ubool step.action.program_statement program.program_statements

let init_program (program: t) (s: Armada.State.t) : GTot ubool =
     list_len s.uniqs_used = 1 // only one uniquifier has been used, for the main thread's initial stack frame
  /\ memory_satisfies_global_initializers s.mem program.global_initializers
  /\ s.mem RootIdFence == RootFence initial_fence_storage
  /\ s.initial_tid <> 0
  /\ (let thread = s.threads s.initial_tid in
      let initial_frame_uniq = Cons?.hd s.uniqs_used in
         ThreadStatusRunning? thread.status
      /\ thread.pc = program.main_start_pc
      /\ eqb thread.stack []
      /\ thread.top.method_id = program.main_method_id
      /\ thread.top.frame_uniq = initial_frame_uniq
      /\ memory_satisfies_main_stack_initializers s.mem s.initial_tid program.main_method_id initial_frame_uniq
           thread.top.local_variables program.main_stack_initializers
      /\ memory_invalid_outside_initializations s.mem program.global_initializers s.initial_tid program.main_method_id
           initial_frame_uniq thread.top.local_variables)
  /\ (forall tid.{:pattern s.threads tid} let thread = s.threads tid in
               length thread.write_buffer = 0
             /\ thread.position_in_other_write_buffers == Spec.Map.const 0
             /\ (tid <> s.initial_tid ==> ThreadStatusNotStarted? thread.status))

let next_program (program: Armada.Program.t) (transition: Armada.Transition.t) (s s': Armada.State.t) : GTot ubool =
    (forall step. contains_ubool step transition.steps ==> program_contains_statement_of_step program step)
  /\ next_transition transition s s'

let program_to_spec (program: Armada.Program.t) : GTot (spec_t Armada.State.t) =
  { init = init_program program;
    next = fun s s' -> exists (transition: Armada.Transition.t). next_program program transition s s' }
