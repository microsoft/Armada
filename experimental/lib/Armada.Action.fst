module Armada.Action

open Armada.Base
open Armada.Computation
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Type
open Spec.Logic
open Spec.Map
open Spec.Ubool

noeq type program_statement_t = {
  start_pc: option pc_t;         // if Some `x`, then actor's PC must be at `x` when action begins
  end_pc: option pc_t;           // if end_pc is Some `y`, then actor's PC is changed to `y` by the action;
                                 // if end_pc is None and start_pc is None, then actor's PC is unchanged by the action;
                                 // if end_pc is None and start_pc is Some `x`, then actor is terminated by the action
  starts_atomic_block: bool;     // whether this action starts with the actor yielded
  ends_atomic_block: bool;       // whether this action causes the actor to yield when ok=true
  statement: Armada.Statement.t; // statement to be executed before performing end_pc modification
}

noeq type t = {
  ok: bool;
  program_statement: program_statement_t;
}

let update_thread_pc_in_state (s: Armada.State.t) (tid: tid_t) (opc: option pc_t) : Armada.State.t =
  match opc with
  | Some pc ->
      let thread = s.threads tid in
      let new_thread = { thread with pc = pc; } in
      let new_threads = Spec.Map.upd s.threads tid new_thread in
      { s with threads = new_threads }
  | None -> s

let action_computation
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (nd: nondeterminism_t)
  (action: t)
  (s: Armada.State.t)
  : GTot (option Armada.State.t) =
  // It's illegal to take a step from a stopped state.
  // Also, if a step isn't crashing, then the action should be yielding if and only if
  // it's the last step of a transition.  And the action can't crash unless it's the last
  // step of a transition.
  let ps = action.program_statement in
  if   not (NotStopped? s.stop_reason)
     || (starts_atomic_block <> ps.starts_atomic_block)
     || (ends_atomic_block <> (not action.ok || ps.ends_atomic_block)) then
    None
  else
    let thread = s.threads actor in
    // actor must be a running thread
    // if start_pc isn't None, then it must match the thread's PC
    if    not (ThreadStatusRunning? thread.status)
        || (Some? ps.start_pc && Some?.v ps.start_pc <> thread.pc) then
      None
    else
      (match statement_computation actor nd thread.pc ps.end_pc ps.statement s with
       | ComputationImpossible -> None
       | ComputationUndefined ->
           if action.ok then
             None
           else
             Some ({ s with stop_reason = StopReasonUndefinedBehavior })
       | ComputationProduces s' ->
           if not action.ok then
             None
           else
             Some (update_thread_pc_in_state s' actor ps.end_pc))
