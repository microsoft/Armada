module MyAtomicToRegularRefinement

open Armada.Action
open Armada.BinaryOp
open Armada.Expression
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Type
open FStar.Tactics.V2
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.AtomicToRegular.Armada
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.Nth

let my_atomic_to_regular_map: (list (list nat)) =
  [[0]; [1]; [2; 4; 6]; [3]; [2; 5]; [2; 4; 7]; [8]; [9]]

let lemma_MyAtomicHProg_refines_MyHProg ()
  : Lemma (ensures spec_refines_spec
                     (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicHProg.prog)
                     (program_to_spec MyHProg.prog)
                     eq2) =
  let aw: atomic_refines_armada_witness_t = {
    atomic_to_regular_map = my_atomic_to_regular_map;
    actions_array = list_to_array (all_actions MyHProg.prog.program_statements)
  } in
  assert (atomic_refines_armada_witness_valid MyAtomicHProg.prog MyHProg.prog aw)
    by (compute(); trivial());
  atomic_refines_armada_witness_valid_implies_refinement MyAtomicHProg.prog MyHProg.prog aw
