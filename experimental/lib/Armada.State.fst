module Armada.State

open Armada.Base
open Armada.Memory
open Armada.Threads
open Armada.Type
open FStar.Sequence.Base
open Spec.Behavior
open Spec.List
open Spec.Ubool

type stop_reason_t =
  | NotStopped
  | StopReasonTerminated
  | StopReasonAssertionFailure
  | StopReasonUndefinedBehavior
  | StopReasonStackOverflow

type trace_entry = object_value_t

noeq type t = {
  initial_tid: tid_t;
  uniqs_used: list root_id_uniquifier_t;
  mem: Armada.Memory.t;
  threads: Armada.Threads.t;
  trace: seq trace_entry;
  stop_reason: stop_reason_t;
}

let refinement_requirement (ls: Armada.State.t) (hs: Armada.State.t) : GTot ubool =
  if NotStopped? ls.stop_reason then
    is_prefix ls.trace hs.trace
  else
    ls.stop_reason = hs.stop_reason /\ ls.trace == hs.trace
