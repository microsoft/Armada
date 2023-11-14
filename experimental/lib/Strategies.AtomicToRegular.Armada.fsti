module Strategies.AtomicToRegular.Armada

open Armada.Action
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open FStar.ImmutableArray
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Atomic
open Strategies.AtomicToRegular
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.List
open Util.Nth

let valid_atomic_to_armada_map
  (atomic_actions: list (list Armada.Action.t))
  (atomic_to_regular_map: list (list nat))
  (actions_array: array_t Armada.Action.t)
  : GTot ubool =
  let index_and_action_corr = fun idx -> fun action -> (array_nth actions_array idx) == (Some action) in
  let indices_and_actions_corr =
    fun indices -> fun atomic_action -> lists_correspond_ubool index_and_action_corr indices atomic_action in
  lists_correspond_ubool indices_and_actions_corr atomic_to_regular_map atomic_actions

noeq type atomic_refines_armada_witness_t = {
  atomic_to_regular_map: list (list nat);
  actions_array: array_t Armada.Action.t;
}

let atomic_refines_armada_witness_valid
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: Armada.Program.t)
  (aw: atomic_refines_armada_witness_t)
  : GTot ubool =
  valid_atomic_to_armada_map lprog.actions aw.atomic_to_regular_map aw.actions_array

val atomic_refines_armada_witness_valid_implies_refinement
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: Armada.Program.t)
  (aw: atomic_refines_armada_witness_t)
  : Lemma (requires   atomic_refines_armada_witness_valid lprog hprog aw
                    /\ lprog.init_f == init_program hprog
                    /\ aw.actions_array == list_to_array (all_actions hprog.program_statements))
          (ensures  (spec_refines_spec
                       (semantics_to_spec (make_atomic_semantics armada_semantics) lprog)
                       (program_to_spec hprog)
                       eq2))
