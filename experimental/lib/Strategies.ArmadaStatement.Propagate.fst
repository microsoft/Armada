module Strategies.ArmadaStatement.Propagate

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Step
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open Spec.List
open Spec.Ubool
open Util.List

let propagate_program_statement: program_statement_t =
  { start_pc = None;
    end_pc = None;
    starts_atomic_block = true;
    ends_atomic_block = true;
    statement = PropagateWriteMessageStatement }

let propagate_action: Armada.Action.t =
  { ok = true; program_statement = propagate_program_statement }

let propagate_action_list: list Armada.Action.t =
  [propagate_action]

let possible_propagate_action_ok
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (s: Armada.State.t)
  (steps: list Armada.Step.t)
  : Lemma (requires   Some? (steps_computation actor starts_atomic_block ends_atomic_block steps s)
                    /\ Cons? steps
                    /\ (Cons?.hd steps).action.program_statement == propagate_program_statement)
          (ensures  (Cons?.hd steps).action.ok) =
  ()

let step_computation_is_propagate_computation
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s: Armada.State.t)
  (step: Armada.Step.t)
  : Lemma (requires  (  step == { nd = nd; action = propagate_action }
                      /\ NotStopped? s.stop_reason
                      /\ ThreadStatusRunning? (s.threads actor).status
                      /\ (ComputationProduces? (propagate_write_message_statement_computation actor nd s))))
          (ensures  step_computation actor true true step s ==
                      Some (ComputationProduces?.result (propagate_write_message_statement_computation actor nd s))) =
  ()
