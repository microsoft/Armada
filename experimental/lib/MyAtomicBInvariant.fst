module MyAtomicBInvariant

open Armada.Action
open Armada.Base
open Armada.BinaryOp
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Step
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.Behavior
open Strategies.Atomic
open Strategies.GlobalVars.Types
open Strategies.Invariant
open Strategies.Invariant.Armada
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Semantics
open Strategies.Semantics.Armada
open Spec.List
open Spec.Ubool
open Util.List

let inv (s: Armada.State.t) : GTot ubool =
    gvar_has_type s.mem "a" (ObjectTDAbstract int)
  /\ gvar_has_type s.mem "c" (ObjectTDAbstract int)
  /\ gvar_has_type s.mem "e" (ObjectTDAbstract int)

private let action_pred (action: Armada.Action.t) : GTot ubool =
  True

#push-options "--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100"

private let atomic_bprog_init_establishes_inv
  (s: Armada.State.t{(semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicBProg.prog).init s})
  : squash (inv s) =
  ()

private let action_pred_preserves_inv
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
    /\ action_pred step.action
    /\ inv s})
  : squash (inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) =
  step_computation_maintains_all_gvars_have_types
    ["a"; "c"; "e"]
    [ObjectTDAbstract int; ObjectTDAbstract int; ObjectTDAbstract int]
    actor starts_atomic_block ends_atomic_block step s

#pop-options

private let my_special_case_proofs
  : list (list (option (armada_action_special_case_invariant_proof_t inv))) =
  [
    // Atomic action #0 has 3 actions
    [None; None; None];
    // Atomic action #1 has 1 action
    [None];
    // Atomic action #2 has 2 actions
    [None; None];
    // Atomic action #3 has 3 actions
    [None; None; None];
    // Atomic action #4 has 3 actions
    [None; None; None];
    // Atomic action #5 has 1 action
    [None];
    // Atomic action #6 has 2 actions
    [None; None];
    // Atomic action #7 has 3 actions
    [None; None; None];
    // Atomic action #8 has 1 action
    [None];
    // Atomic action #9 has 1 action
    [None];
    // Atomic action #10 has 1 action
    [None];
    // Atomic action #11 has 1 action
    [None];
    // Atomic action #12 has 1 action
    [None];
    // Atomic action #13 has 1 action
    [None];
    // Atomic action #14 has 1 action
    [None];
    // Atomic action #15 has 1 action
    [None];
    // Atomic action #16 has 1 action
    [None];
    // Atomic action #17 has 1 action
    [None];
    // Atomic action #18 has 1 action
    [None];
    // Atomic action #19 has 1 action
    [None];
    // Atomic action #20 has 1 action
    [None];
    // Atomic action #21 has 1 action
    [None];
    // Atomic action #22 has 2 actions
    [None; None];
    // Atomic action #23 has 1 action
    [None];
    // Atomic action #24 has 2 actions
    [None; None];
    // Atomic action #25 has 1 action
    [None];
    // Atomic action #26 has 1 action
    [None];
  ]

let inv_witness () : armada_atomic_substep_invariant_witness_t MyAtomicBProg.prog inv =
  {
    action_pred = action_pred;
    special_case_proofs = my_special_case_proofs;
    init_implies_inv_proof = atomic_bprog_init_establishes_inv;
    action_proof = action_pred_preserves_inv;
  }

let inv_is_stepwise_invariant ()
  : Lemma (is_armada_substep_invariant MyAtomicBProg.prog inv) =
  let aiw = inv_witness () in
  assert (armada_atomic_substep_invariant_witness_valid MyAtomicBProg.prog inv aiw)
    by (FStar.Tactics.compute(); FStar.Tactics.trivial ());
  armada_atomic_substep_invariant_witness_valid_implies_is_substep_invariant MyAtomicBProg.prog inv aiw
