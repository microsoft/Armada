module Strategies.AtomicToRegular.Armada

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
open Strategies.AtomicToRegular
open Util.Behavior
open Util.ImmutableArray
open Util.List
open Util.Nth

noeq type atomic_refines_armada_relation_t = {
  lprog: program_t (make_atomic_semantics armada_semantics);
  hprog: Armada.Program.t;
  atomic_to_regular_map: list (list nat);
  actions_array: array_t Armada.Action.t;

  actions_array_correct: unit ->
    squash (array_matches_list actions_array (all_actions hprog.program_statements));
  atomic_to_regular_map_valid: unit ->
    squash (valid_atomic_to_armada_map lprog.actions atomic_to_regular_map actions_array);
  init_implies_init: s: Armada.State.t{lprog.init_f s} -> squash (init_program hprog s);
}

let atomic_refines_armada_relation_implies_valid_atomic_to_regular_map
  (aa: atomic_refines_armada_relation_t)
  : Lemma (ensures (valid_atomic_to_regular_map armada_semantics aa.lprog.actions
                      (all_actions aa.hprog.program_statements) aa.atomic_to_regular_map)) =
  let regular_actions = all_actions aa.hprog.program_statements in
  let atomic_actions = aa.lprog.actions in
  let index_and_action_corr =
    fun index -> fun action -> (array_nth aa.actions_array index) == (Some action) in
  let indices_and_actions_corr =
    fun indices -> fun atomic_action -> lists_correspond_ubool index_and_action_corr indices atomic_action in
  let index_and_action_corr' = fun index -> fun action -> (nth regular_actions index) == (Some action) in
  let indices_and_actions_corr' =
    fun indices -> fun atomic_act -> lists_correspond_ubool index_and_action_corr' indices atomic_act in
  let lem1 (index: nat) (action: Armada.Action.t) : Lemma
    (requires index_and_action_corr index action)
    (ensures  index_and_action_corr' index action) =
    (aa.actions_array_correct ();
     array_matches_list_implies_nth_equivalent aa.actions_array regular_actions index) in
  let lem2 (indices: list nat) (atomic_action: list Armada.Action.t) : Lemma
    (requires indices_and_actions_corr indices atomic_action)
    (ensures  indices_and_actions_corr' indices atomic_action) =
    (lists_correspond_ubool_implies_weaker_correspondence
       index_and_action_corr index_and_action_corr' indices atomic_action lem1) in
  aa.atomic_to_regular_map_valid ();
  assert (valid_atomic_to_armada_map atomic_actions aa.atomic_to_regular_map aa.actions_array ==
           lists_correspond_ubool indices_and_actions_corr aa.atomic_to_regular_map atomic_actions)
    by FStar.Tactics.V2.trefl();
  lists_correspond_ubool_implies_weaker_correspondence
    indices_and_actions_corr indices_and_actions_corr' aa.atomic_to_regular_map atomic_actions lem2;
  assert (valid_atomic_to_regular_map armada_semantics atomic_actions regular_actions aa.atomic_to_regular_map ==
           lists_correspond_ubool indices_and_actions_corr' aa.atomic_to_regular_map atomic_actions)
    by FStar.Tactics.V2.trefl()

let atomic_refines_armada_relation_implies_refinement (aa: atomic_refines_armada_relation_t)
  : Lemma (ensures (spec_refines_spec
                    (semantics_to_spec (make_atomic_semantics armada_semantics) aa.lprog)
                    (program_to_spec aa.hprog)
                    eq2)) =
  let ar: atomic_refines_regular_relation_t = {
    sem = armada_semantics;
    lprog = aa.lprog;
    hprog = armada_program_to_generic aa.hprog;
    atomic_to_regular_map = aa.atomic_to_regular_map;
    atomic_to_regular_map_valid = (fun _ -> atomic_refines_armada_relation_implies_valid_atomic_to_regular_map aa);
    init_implies_init = aa.init_implies_init;
  } in
  atomic_refines_regular_relation_implies_refinement ar;
  armada_generic_refines_spec aa.hprog;
  spec_refinement_transitivity
    (semantics_to_spec (make_atomic_semantics armada_semantics) aa.lprog)
    (semantics_to_spec armada_semantics (armada_program_to_generic aa.hprog))
    (program_to_spec aa.hprog)
    eq2
    eq2
    eq2

let atomic_refines_armada_witness_valid_implies_refinement
  (lprog: program_t (make_atomic_semantics armada_semantics))
  (hprog: Armada.Program.t)
  (aw: atomic_refines_armada_witness_t)
  (* see .fsti file for spec *) =
  list_to_array_implies_array_matches_list aw.actions_array (all_actions hprog.program_statements);
  let ar: atomic_refines_armada_relation_t = {
    lprog = lprog;
    hprog = hprog;
    atomic_to_regular_map = aw.atomic_to_regular_map;
    actions_array = aw.actions_array;
    actions_array_correct = (fun _ -> ());
    atomic_to_regular_map_valid = (fun _ -> ());
    init_implies_init = (fun _ -> ());
  } in
  atomic_refines_armada_relation_implies_refinement ar
