module Strategies.AtomicToRegular

open Armada.Action
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open Spec.Behavior
open FStar.List.Tot
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Util.Behavior
open Util.List
open Util.Nth

let valid_atomic_to_regular_map
  (sem: semantics_t)
  (atomic_actions: list (list sem.action_t))
  (regular_actions: list sem.action_t)
  (atomic_to_regular_map: list (list nat))
  : GTot ubool =
  let index_and_action_corr = fun index -> fun action -> (nth regular_actions index) == (Some action) in
  let indices_and_actions_corr =
    fun indices -> fun atomic_action -> lists_correspond_ubool index_and_action_corr indices atomic_action in
  lists_correspond_ubool indices_and_actions_corr atomic_to_regular_map atomic_actions

noeq type atomic_refines_regular_relation_t = {
  sem: semantics_t;
  lprog: program_t (make_atomic_semantics sem);
  hprog: program_t sem;
  atomic_to_regular_map: list (list nat);

  atomic_to_regular_map_valid: unit ->
     squash (valid_atomic_to_regular_map sem lprog.actions hprog.actions atomic_to_regular_map);
  init_implies_init: (s: sem.state_t{lprog.init_f s}) -> squash (hprog.init_f s);
}

val atomic_refines_regular_relation_implies_refinement (ar: atomic_refines_regular_relation_t)
  : Lemma (ensures spec_refines_spec
                     (semantics_to_spec (make_atomic_semantics ar.sem) ar.lprog)
                     (semantics_to_spec ar.sem ar.hprog)
                     eq2)
