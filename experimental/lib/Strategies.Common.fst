module Strategies.Common

open Armada.State
open Util.Behavior
open Util.List
open Util.Seq

let refinement_requirement_reflexive () : Lemma (refinement_relation_reflexive refinement_requirement) =
  let lem (s: Armada.State.t) : Lemma (ensures refinement_requirement s s) [SMTPat (refinement_requirement s s)] =
    () in
  ()
