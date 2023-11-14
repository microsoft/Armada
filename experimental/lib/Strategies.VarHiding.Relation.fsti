module Strategies.VarHiding.Relation

open Armada.State
open Armada.Type
open Spec.Behavior
open Strategies.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs

val var_hiding_relation_implies_refinement (vr: var_hiding_relation_t)
  : Lemma (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) vr.latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) vr.hatomic_prog)
                      refinement_requirement))
