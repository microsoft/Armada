module MyProgramInvariant

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
open Strategies.Invariant
open Strategies.Invariant.Armada.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Spec.List
open Spec.Ubool
open Util.List

let my_inv (s: Armada.State.t) : GTot ubool =
  let root_one: root_t = RootGlobal (ObjectStorageAbstract int 1) in
    s.mem (RootIdGlobal "f") == root_one
  /\ s.mem (RootIdGlobal "g") == root_one

#push-options "--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100"

private let atomic_lprog_init_establishes_my_inv
  (s: Armada.State.t{(semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicLProg.prog).init s})
  : squash (my_inv s) =
  let initializer5: initializer_t =
    { var_id = "f"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } in
  assert (contains_ubool initializer5 MyLProg.prog.global_initializers)
    by FStar.Tactics.V2.norm [delta];
  let initializer6: initializer_t =
    { var_id = "g"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } in
  assert (contains_ubool initializer6 MyLProg.prog.global_initializers)
    by FStar.Tactics.V2.norm [delta];
  ()

#pop-options

private let my_action_pred (action: Armada.Action.t) : GTot ubool =
    (not action.ok)
  \/ (match action.program_statement.statement with
     | UpdateStatement bypassing_write_buffer dst src ->
           bypassing_write_buffer = false
         /\ (match dst with
            | ExpressionGlobalVariable _ v -> v <> "f" && v <> "g"
            | _ -> False)
     | _ -> False)

#push-options "--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100"

private let my_action_pred_preserves_my_inv
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
    /\ my_action_pred step.action
    /\ my_inv s})
  : squash (my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) =
  ()

#pop-options

private let my_divide_by_one_special_case_atomic_action : list Armada.Action.t =
  [ { ok = true;
      program_statement = { start_pc = Some "main.4";
                            end_pc = Some "main.5";
                            starts_atomic_block = true;
                            ends_atomic_block = true;
                            statement = UpdateStatement false
                              (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                              (ExpressionBinaryOperator
                                (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int) BinaryOpDivInt
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "f")); } } ]

#push-options "--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100"

private let my_divide_by_one_special_case_proof
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (atomic_step: list Armada.Step.t)
  (s: Armada.State.t{
       map_ghost armada_step_to_action atomic_step == my_divide_by_one_special_case_atomic_action
     /\ my_inv s
     /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s)})
  : squash (my_inv (Some?.v (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s))) =
  (* SMT automatically figures out that dividing value #5 by itself preserves the invariant that
     value #5 is 1. *)
  ()

#pop-options

private let my_special_case_proof: armada_atomic_special_case_invariant_proof_t my_inv =
  ArmadaAtomicSpecialCaseInvariantProof my_divide_by_one_special_case_atomic_action my_divide_by_one_special_case_proof

private let my_special_case_proofs
  : list (option (armada_atomic_special_case_invariant_proof_t my_inv)) =
  [
    None;
    None;
    None;
    None;
    None;
    None;
    Some (ArmadaAtomicSpecialCaseInvariantProof my_divide_by_one_special_case_atomic_action
            my_divide_by_one_special_case_proof);
    None
  ]

let my_inv_witness () : armada_atomic_semantics_invariant_witness_t MyAtomicLProg.prog my_inv =
  {
    action_pred = my_action_pred;
    special_case_proofs = my_special_case_proofs;
    init_implies_inv_proof = atomic_lprog_init_establishes_my_inv;
    action_proof = my_action_pred_preserves_my_inv;
  }

let my_inv_is_stepwise_invariant ()
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)
             MyAtomicLProg.prog my_inv) =
  let aiw = my_inv_witness () in
  assert (armada_atomic_semantics_invariant_witness_valid MyAtomicLProg.prog my_inv aiw)
    by (FStar.Tactics.V2.compute (); FStar.Tactics.V2.trivial ());
  armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant MyAtomicLProg.prog my_inv aiw
