module MyProgramProof

open Armada.Action
open Armada.Base
open Armada.Expression
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Transition
open Armada.Type
open FStar.List.Tot.Base
open FStar.Tactics.V2
open MyAtomicToRegularRefinement
open MyProgramInvariant
open MyRegularToAtomicRefinement
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.Invariant
open Strategies.Invariant.Armada.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.Weakening.Armada
open Util.Behavior
open Util.ImmutableArray
open Util.List

private let my_special_case_action_0 : list Armada.Action.t =
  [ { ok = true;
      program_statement = { start_pc = Some "main.0"; end_pc = Some "main.1"; starts_atomic_block = true;
                            ends_atomic_block = true;
                            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                          (ExpressionGlobalVariable (ObjectTDAbstract int) "f"); } } ]

private let my_special_case_action_1 : list Armada.Action.t =
  [ { ok = false;
      program_statement = { start_pc = Some "main.0"; end_pc = Some "main.1"; starts_atomic_block = true;
                            ends_atomic_block = true;
                            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                          (ExpressionGlobalVariable (ObjectTDAbstract int) "f"); } } ]

private let my_special_case_steps_updater_0
  (actor: tid_t)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : nat * (list Armada.Step.t) =
  let step: Armada.Step.t = {
    nd = [];
    action = {
      ok = true;
      program_statement = { start_pc = Some "main.0"; end_pc = Some "main.1"; starts_atomic_block = true;
                            ends_atomic_block = true;
                            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                          (ExpressionGlobalVariable (ObjectTDAbstract int) "g"); }
    }
  } in
  (0, [step]) // this atomic action is the 0th one in the list of MyAtomicHProg.prog.actions

private let my_special_case_steps_updater_1
  (actor: tid_t)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : nat * (list Armada.Step.t) =
  let step: Armada.Step.t = {
    nd = [];
    action = {
      ok = false;
      program_statement = { start_pc = Some "main.0"; end_pc = Some "main.1"; starts_atomic_block = true;
                            ends_atomic_block = true;
                            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                          (ExpressionGlobalVariable (ObjectTDAbstract int) "g"); }
    }
  } in
  (1, [step]) // this atomic action is the 1st one in the list of MyAtomicHProg.prog.actions

#push-options "--z3rlimit 10 --fuel 4"

private let my_special_case_steps_updater_satisfies_weakening_0
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lsteps: list Armada.Step.t)
  (haction_index: nat)
  (hsteps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   (FStar.List.Tot.map armada_step_to_action lsteps == my_special_case_action_0)
                    /\ (my_inv s)
                    /\ (Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s))
                    /\ ((haction_index, hsteps) == my_special_case_steps_updater_0 actor lsteps s))
          (ensures  (  (Some? (steps_computation actor starts_atomic_block ends_atomic_block hsteps s))
                     /\ (steps_computation actor starts_atomic_block ends_atomic_block lsteps s ==
                        steps_computation actor starts_atomic_block ends_atomic_block hsteps s)
                     /\ nth MyAtomicHProg.prog.actions haction_index ==
                         Some (map_ghost armada_step_to_action hsteps))) =
  ()

private let my_special_case_steps_updater_satisfies_weakening_1
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (lsteps: list Armada.Step.t)
  (haction_index: nat)
  (hsteps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   (FStar.List.Tot.map armada_step_to_action lsteps == my_special_case_action_1)
                    /\ (my_inv s)
                    /\ (Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s))
                    /\ ((haction_index, hsteps) == my_special_case_steps_updater_1 actor lsteps s))
          (ensures  (  (Some? (steps_computation actor starts_atomic_block ends_atomic_block hsteps s))
                     /\ (steps_computation actor starts_atomic_block ends_atomic_block lsteps s ==
                        steps_computation actor starts_atomic_block ends_atomic_block hsteps s)
                     /\ nth MyAtomicHProg.prog.actions haction_index ==
                         Some (map_ghost armada_step_to_action hsteps))) =
  ()

#pop-options

private let my_special_case_steps_updater_works_0 ()
  : squash (armada_steps_updater_works (list_to_array MyAtomicHProg.prog.actions) my_inv my_special_case_action_0
              my_special_case_steps_updater_0) =
  let hatomic_action_array = list_to_array MyAtomicHProg.prog.actions in
  introduce forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: list Armada.Step.t)
              (s: Armada.State.t).
      map_ghost armada_step_to_action lsteps == my_special_case_action_0
    /\ my_inv s
    /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s)
    ==> 
    (let hatomic_action_idx, hsteps = my_special_case_steps_updater_0 actor lsteps s in
     let haction = map_ghost armada_step_to_action hsteps in
       hatomic_action_idx < array_len hatomic_action_array
     /\ array_index hatomic_action_array hatomic_action_idx == haction
     /\ (steps_computation actor starts_atomic_block ends_atomic_block hsteps s ==
        steps_computation actor starts_atomic_block ends_atomic_block lsteps s))
  with introduce _ ==> _
  with _.
    let hatomic_action_idx, hsteps = my_special_case_steps_updater_0 actor lsteps s in
    list_to_array_implies_nth_equivalent hatomic_action_array MyAtomicHProg.prog.actions hatomic_action_idx;
    my_special_case_steps_updater_satisfies_weakening_0 actor starts_atomic_block ends_atomic_block
      lsteps hatomic_action_idx hsteps s

private let my_special_case_steps_updater_works_1 ()
  : squash (armada_steps_updater_works (list_to_array MyAtomicHProg.prog.actions) my_inv my_special_case_action_1
              my_special_case_steps_updater_1) =
  let hatomic_action_array = list_to_array MyAtomicHProg.prog.actions in
  introduce forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: list Armada.Step.t)
              (s: Armada.State.t).
      map_ghost armada_step_to_action lsteps == my_special_case_action_1
    /\ my_inv s
    /\ Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s)
    ==> 
    (let hatomic_action_idx, hsteps = my_special_case_steps_updater_1 actor lsteps s in
     let haction = map_ghost armada_step_to_action hsteps in
       hatomic_action_idx < array_len hatomic_action_array
     /\ array_index hatomic_action_array hatomic_action_idx == haction
     /\ (steps_computation actor starts_atomic_block ends_atomic_block hsteps s ==
        steps_computation actor starts_atomic_block ends_atomic_block lsteps s))
  with introduce _ ==> _
  with _.
    let hatomic_action_idx, hsteps = my_special_case_steps_updater_1 actor lsteps s in
    list_to_array_implies_nth_equivalent hatomic_action_array MyAtomicHProg.prog.actions hatomic_action_idx;
    my_special_case_steps_updater_satisfies_weakening_1 actor starts_atomic_block ends_atomic_block
      lsteps hatomic_action_idx hsteps s

private let my_weakening_transformers
  : list (armada_weakening_transformer_t (list_to_array MyAtomicHProg.prog.actions) my_inv) =
  [ ArmadaWeakeningTransformerUpdatedStep my_special_case_action_0 my_special_case_steps_updater_0
                                            my_special_case_steps_updater_works_0;
    ArmadaWeakeningTransformerUpdatedStep my_special_case_action_1 my_special_case_steps_updater_1
                                            my_special_case_steps_updater_works_1;
    ArmadaWeakeningTransformerSameStep 2;
    ArmadaWeakeningTransformerSameStep 3;
    ArmadaWeakeningTransformerSameStep 4;
    ArmadaWeakeningTransformerSameStep 5;
    ArmadaWeakeningTransformerSameStep 6;
    ArmadaWeakeningTransformerSameStep 7 ]

let lemma_MyAtomicLProg_refines_MyAtomicHProg ()
  : Lemma (spec_refines_spec
           (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicLProg.prog)
           (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicHProg.prog)
           eq2) =
  let ww: armada_weakening_witness_t MyAtomicLProg.prog MyAtomicHProg.prog = {
    inv = my_inv;
    hatomic_action_array = list_to_array MyAtomicHProg.prog.actions;
    weakening_transformers = my_weakening_transformers;
    init_implies_init_proof = (fun _ -> ());
  } in
  assert (armada_weakening_witness_valid MyAtomicLProg.prog MyAtomicHProg.prog ww)
    by (compute (); trivial ());
  my_inv_is_stepwise_invariant ();
  armada_weakening_witness_valid_implies_refinement MyAtomicLProg.prog MyAtomicHProg.prog ww

let lemma_my_lprog_atomic_refines_my_hprog ()
  : Lemma (spec_refines_spec
           (program_to_spec MyLProg.prog)
           (program_to_spec MyHProg.prog)
           eq2) =
  lemma_MyLProg_refines_MyAtomicLProg ();
  lemma_MyAtomicLProg_refines_MyAtomicHProg ();
  lemma_MyAtomicHProg_refines_MyHProg ();
  spec_refinement_transitivity_4
    (program_to_spec MyLProg.prog)
    (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicLProg.prog)
    (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicHProg.prog)
    (program_to_spec MyHProg.prog)
    eq2
    eq2
    eq2
    eq2
    eq2
