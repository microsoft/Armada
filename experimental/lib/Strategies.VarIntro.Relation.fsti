module Strategies.VarIntro.Relation

open Armada.Action
open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Type
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Atomic
open Strategies.GlobalVars
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Util.List
open Util.Nth

val var_intro_relation_implies_refinement (vr: var_intro_relation_t)
  : Lemma (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) vr.latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) vr.hatomic_prog)
                      refinement_requirement))
