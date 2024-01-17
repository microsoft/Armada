module GlobalVarExampleInvariant

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

open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.GlobalVars
open Strategies.GlobalVars.Init
open Strategies.GlobalVarsProof
open Strategies.GlobalVars.UnaddressedStatement

let vs = ["f"]

let my_inv (s: Armada.State.t) : GTot ubool =
  let root_one: root_t = RootGlobal (ObjectStorageAbstract int 1) in
    s.mem (RootIdGlobal "f") == root_one

private let my_action_pred (action: Armada.Action.t) : GTot ubool =
      (not action.ok)
    \/ (  global_variables_unmodifiable_by_statement vs action.program_statement.statement
       /\ global_variables_unaddressable_in_statement vs action.program_statement.statement)

private let inductive_inv (s: Armada.State.t) : GTot ubool =
    roots_match s.mem
  /\ positions_valid_in_state s
  /\ global_variables_unaddressed_in_memory vs s.mem

private let inductive_my_inv (s: Armada.State.t) : GTot ubool =
  inductive_inv s /\ my_inv s

private let step_relation (s s': Armada.State.t): GTot ubool =
  states_match_on_global_variables vs s s'

private let step_relation_preserves_my_inv (s s': Armada.State.t)
  : Lemma (requires my_inv s /\ step_relation s s')
          (ensures  my_inv s') =
  ()

#push-options "--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100"

private let atomic_lprog_init_establishes_inductive_my_inv
  (s: Armada.State.t{(semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicLProg.prog).init s})
  : squash (inductive_my_inv s) =
  let initializer5: initializer_t =
    { var_id = "f"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } in
  assert (contains_ubool initializer5 MyLProg.prog.global_initializers)
    by FStar.Tactics.V2.norm [delta];
  assert (global_variables_unaddressed_in_initializers vs MyLProg.prog.global_initializers)
    by (FStar.Tactics.V2.compute (); FStar.Tactics.V2.trivial ());
  init_implies_global_variables_unaddressed_in_memory vs MyLProg.prog s;
  assert (global_variables_unaddressed_in_memory vs s.mem)

#pop-options

private let my_action_pred_preserves_inductive_my_inv_proof
  (actor: tid_t)
  (starts_atomic_block ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
                    /\ my_action_pred step.action
                    /\ inductive_my_inv s)
          (ensures    inductive_my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)))
  = executing_statement_maintains_roots_match actor step.nd ((s.threads actor).pc) step.action.program_statement.end_pc step.action.program_statement.statement s;
    executing_statement_maintains_positions_valid_in_state actor step.nd ((s.threads actor).pc) step.action.program_statement.end_pc step.action.program_statement.statement s;
    if (step.action.ok) then begin
      global_variables_unaddressable_by_statement_global_vars_unaddressed_in_state vs actor step starts_atomic_block ends_atomic_block s;
      global_variables_unmodifiable_by_statement_memories_matches_on_global_variables vs actor step starts_atomic_block ends_atomic_block s;
      step_relation_preserves_my_inv s (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))
    end

private let my_action_pred_preserves_inductive_my_inv
  (actor: tid_t)
  (starts_atomic_block ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      Some? (step_computation actor starts_atomic_block ends_atomic_block step s)
    /\ my_action_pred step.action
    /\ inductive_my_inv s
  })
  : squash (inductive_my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)))
  = my_action_pred_preserves_inductive_my_inv_proof actor starts_atomic_block ends_atomic_block step s

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
     /\ inductive_my_inv s
     /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s)})
  : squash (inductive_my_inv (Some?.v (steps_computation actor starts_atomic_block ends_atomic_block atomic_step s))) =
  (* SMT automatically figures out that dividing value #5 by itself preserves the invariant that
     value #5 is 1. *)
  ()

#pop-options

private let my_special_case_proof: armada_atomic_special_case_invariant_proof_t inductive_my_inv =
  ArmadaAtomicSpecialCaseInvariantProof my_divide_by_one_special_case_atomic_action my_divide_by_one_special_case_proof

private let my_special_case_proofs
  : list (option (armada_atomic_special_case_invariant_proof_t inductive_my_inv)) =
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

let inductive_my_inv_witness () : armada_atomic_semantics_invariant_witness_t MyAtomicLProg.prog inductive_my_inv =
  {
    action_pred = my_action_pred;
    special_case_proofs = my_special_case_proofs;
    init_implies_inv_proof = atomic_lprog_init_establishes_inductive_my_inv;
    action_proof = my_action_pred_preserves_inductive_my_inv;
  }

let my_inv_is_stepwise_invariant ()
  : Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)
             MyAtomicLProg.prog inductive_my_inv) =
  let aiw = inductive_my_inv_witness () in
  assert (armada_atomic_semantics_invariant_witness_valid MyAtomicLProg.prog inductive_my_inv aiw)
    by (FStar.Tactics.V2.compute (); FStar.Tactics.V2.trivial ());
  armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant MyAtomicLProg.prog inductive_my_inv aiw
