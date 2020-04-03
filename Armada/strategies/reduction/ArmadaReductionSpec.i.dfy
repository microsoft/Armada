/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file is the specification for a request to perform refinement via a Cohen-Lamport reduction
// on an Armada behavior.  Such a reduction takes a behavior satisfying a low-level spec, which
// allows threads to sometimes be in phase 1 or 2 between multisteps, and returns a behavior
// satisfying a higher-level specification that only allows those phases in the middle of
// multisteps.  It does so by lifting sequences of multisteps in the lower-level specification to
// single multisteps in the higher-level specification.
//
// To use this specification, first create a request r of type ArmadaReductionRequest.  Then, prove
// that it's a valid request, i.e., that ValidArmadaReductionRequest(r).  Finally, call
// lemma_PerformArmadaReduction (in ArmadaReduction.i.dfy).
//
// The request describes the Armada state machine in an abstract way.  It models the Armada
// multisteps as instances of ArrStepSequence, which include a sequence of steps of type LOneStep.
// It models the steps as being either tau steps or non-tau steps.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "../../util/option.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../generic/GenericArmadaSpec.i.dfy"

module ArmadaReductionSpecModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened GenericArmadaSpecModule
  import opened ArmadaCommonDefinitions

  datatype ArmadaReductionRequest<!LState, !LOneStep, !LPC, !HState, !HOneStep, !HPC> =
    ArmadaReductionRequest(
      l:Armada_SpecFunctions<LState, LOneStep, LPC>,
      h:Armada_SpecFunctions<HState, HOneStep, HPC>,
      relation:RefinementRelation<LState, HState>,
      inv:LState->bool,
      self_relation:RefinementRelation<LState, LState>,
      lstate_to_hstate:LState->HState,
      lonestep_to_honestep:LOneStep->HOneStep,
      lpc_to_hpc:LPC->HPC,
      is_phase1:LPC->bool,
      is_phase2:LPC->bool,
      generate_left_mover:(LState, Armada_ThreadHandle)->LOneStep,
      left_mover_generation_progress:(LState,Armada_ThreadHandle)->int
      )

  predicate LInitImpliesHInit<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: arr.l.init(ls) ==> arr.h.init(arr.lstate_to_hstate(ls))
  }

  predicate LStateToHStateMapsPCsCorrectly<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, tid :: var hs := arr.lstate_to_hstate(ls);
                var lpc := arr.l.get_thread_pc(ls, tid);
                var hpc := arr.h.get_thread_pc(hs, tid);
                hpc == if lpc.Some? then Some(arr.lpc_to_hpc(lpc.v)) else None()
  }

  predicate LHYieldingCorrespondence<LState, LOneStep, LPC(!new), HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall lpc :: var hpc := arr.lpc_to_hpc(lpc);
            arr.h.is_pc_nonyielding(hpc) <==> (arr.l.is_pc_nonyielding(lpc) || arr.is_phase1(lpc) || arr.is_phase2(lpc))
  }

  predicate LHOneStepPropertiesMatch<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall lstep :: var hstep := arr.lonestep_to_honestep(lstep);
              && arr.l.step_to_thread(lstep) == arr.h.step_to_thread(hstep)
              && arr.l.is_step_tau(lstep) == arr.h.is_step_tau(hstep)
  }

  predicate LOneStepImpliesHOneStep<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, lstep ::
      arr.inv(ls) && arr.l.step_valid(ls, lstep) ==>
      var ls' := arr.l.step_next(ls, lstep);
      var hs := arr.lstate_to_hstate(ls);
      var hstep := arr.lonestep_to_honestep(lstep);
      var hs' := arr.lstate_to_hstate(ls');
      && arr.h.step_valid(hs, hstep)
      && hs' == arr.h.step_next(hs, hstep)
  }

  predicate StateConversionPreservesOK<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: arr.h.state_ok(arr.lstate_to_hstate(ls)) == arr.l.state_ok(ls)
  }

  predicate StateConversionSatisfiesRelation<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: RefinementPair(ls, arr.lstate_to_hstate(ls)) in arr.relation
  }

  predicate ThreadsDontStartInAnyPhase<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, tid :: arr.l.init(s) && arr.l.get_thread_pc(s, tid).Some?
        ==> var pc := arr.l.get_thread_pc(s, tid).v;
            !arr.is_phase1(pc) && !arr.is_phase2(pc)
  }

  predicate PhasesDontOverlap<LState, LOneStep, LPC(!new), HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall pc :: arr.is_phase1(pc) ==> !arr.is_phase2(pc)
  }

  predicate ThreadCantAffectOtherThreadPhaseExceptViaFork
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step, tid :: arr.l.step_valid(s, step) && arr.l.step_to_thread(step) != tid
       ==> var s' := arr.l.step_next(s, step);
           var pc := arr.l.get_thread_pc(s, tid);
           var pc' := arr.l.get_thread_pc(s', tid);
           (pc' != pc ==> pc.None? && !arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v) && !arr.l.is_pc_nonyielding(pc'.v))
  }

  predicate PhasesPrecededByYielding<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step ::
      var tid := arr.l.step_to_thread(step);
      var s' := arr.l.step_next(s, step);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.step_valid(s, step)
      && pc'.Some?
      && (arr.is_phase1(pc'.v) || arr.is_phase2(pc'.v))
      && pc.Some?
      && (!arr.is_phase1(pc.v) && !arr.is_phase2(pc.v))
      ==> !arr.l.is_pc_nonyielding(pc.v)
  }

  predicate PhasesSucceededByYielding<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step ::
      var tid := arr.l.step_to_thread(step);
      var s' := arr.l.step_next(s, step);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.step_valid(s, step)
      && pc.Some?
      && (arr.is_phase1(pc.v) || arr.is_phase2(pc.v))
      && pc'.Some?
      && (!arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v))
      ==> !arr.l.is_pc_nonyielding(pc'.v)
  }

  predicate Phase2NotFollowedByPhase1<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step ::
      var tid := arr.l.step_to_thread(step);
      var s' := arr.l.step_next(s, step);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.step_valid(s, step)
      && pc.Some?
      && arr.is_phase2(pc.v)
      && pc'.Some?
      && !arr.is_phase2(pc'.v)
      ==> !arr.is_phase1(pc'.v)
  }

  predicate RightMoversPreserveStateRefinement
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step :: arr.l.step_valid(s, step) && !arr.l.is_step_tau(step)
       ==> var tid := arr.l.step_to_thread(step);
           var s' := arr.l.step_next(s, step);
           var pc' := arr.l.get_thread_pc(s', tid);
           (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
  }

  predicate LeftMoversPreserveStateRefinement
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, step :: arr.l.step_valid(s, step) && !arr.l.is_step_tau(step)
       ==> var tid := arr.l.step_to_thread(step);
           var s' := arr.l.step_next(s, step);
           var pc := arr.l.get_thread_pc(s, tid);
           (pc.Some? && arr.is_phase2(pc.v) ==> RefinementPair(s, s') in arr.self_relation)
  }

  predicate RightMoversCommuteConditions<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    initial_state:LState,
    right_mover:LOneStep,
    other_step:LOneStep
    )
  {
    var tid := arr.l.step_to_thread(right_mover);
    var other_tid := arr.l.step_to_thread(other_step);
    var other_tau := arr.l.is_step_tau(other_step);
    var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
    var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
    var pc := arr.l.get_thread_pc(state_after_right_mover, tid);
    && arr.inv(initial_state)
    && !arr.l.is_step_tau(right_mover)
    && arr.l.step_valid(initial_state, right_mover)
    && pc.Some?
    && arr.is_phase1(pc.v)
    && arr.l.step_valid(state_after_right_mover, other_step)
    && arr.l.state_ok(state_after_both_steps)
    && (other_tau || other_tid != tid)
  }

  predicate RightMoversCommute<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
      forall initial_state, right_mover, other_step
        {:trigger RightMoversCommuteConditions(arr, initial_state, right_mover, other_step)}
        :: RightMoversCommuteConditions(arr, initial_state, right_mover, other_step)
        ==> var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
            var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
            var new_middle_state := arr.l.step_next(initial_state, other_step);
            && arr.l.step_valid(initial_state, other_step)
            && arr.l.step_valid(new_middle_state, right_mover)
            && state_after_both_steps == arr.l.step_next(new_middle_state, right_mover)
  }

  predicate LeftMoversCommuteConditions<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    initial_state:LState,
    other_step:LOneStep,
    left_mover:LOneStep
    )
  {
    var tid := arr.l.step_to_thread(left_mover);
    var state_after_other_step := arr.l.step_next(initial_state, other_step);
    var pc := arr.l.get_thread_pc(state_after_other_step, tid);
    && arr.inv(initial_state)
    && arr.l.step_valid(initial_state, other_step)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && !arr.l.is_step_tau(left_mover)
    && arr.l.step_valid(state_after_other_step, left_mover)
    && (arr.l.is_step_tau(other_step) || arr.l.step_to_thread(other_step) != tid)
  }

  predicate LeftMoversCommute<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall initial_state, other_step, left_mover
      {:trigger LeftMoversCommuteConditions(arr, initial_state, other_step, left_mover)}
      :: LeftMoversCommuteConditions(arr, initial_state, other_step, left_mover)
        ==> var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
            var new_middle_state := arr.l.step_next(initial_state, left_mover);
            && arr.l.step_valid(initial_state, left_mover)
            && arr.l.step_valid(new_middle_state, other_step)
            && state_after_both_steps == arr.l.step_next(new_middle_state, other_step)
  }

  predicate LeftMoversAlwaysEnabledConditions
    <LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    && arr.inv(s)
    && arr.l.state_ok(s)
    && arr.l.get_thread_pc(s, tid).Some?
    && arr.is_phase2(arr.l.get_thread_pc(s, tid).v)
  }

  predicate LeftMoversAlwaysEnabled<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall s, tid
      {:trigger LeftMoversAlwaysEnabledConditions(arr, s, tid)}
      :: LeftMoversAlwaysEnabledConditions(arr, s, tid)
      ==> var step := arr.generate_left_mover(s, tid);
          && arr.l.step_valid(s, step)
          && arr.l.step_to_thread(step) == tid
          && !arr.l.is_step_tau(step)
          && var s' := arr.l.step_next(s, step);
            0 <= arr.left_mover_generation_progress(s', tid) < arr.left_mover_generation_progress(s, tid)
  }

  predicate RightMoverCrashPreservationConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    initial_state:LState,
    right_mover:LOneStep,
    other_step:LOneStep
    )
  {
    var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
    var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
    var tid := arr.l.step_to_thread(right_mover);
    var pc := arr.l.get_thread_pc(state_after_right_mover, tid);
    var other_tau := arr.l.is_step_tau(other_step);
    var other_tid := arr.l.step_to_thread(other_step);
    && arr.inv(initial_state)
    && arr.l.step_valid(initial_state, right_mover)
    && arr.l.step_valid(state_after_right_mover, other_step)
    && !arr.l.state_ok(state_after_both_steps)
    && !arr.l.is_step_tau(right_mover)
    && pc.Some?
    && arr.is_phase1(pc.v)
    && (other_tau || other_tid != tid)
  }
    
  predicate RightMoverCrashPreservation<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall initial_state, right_mover, other_step
      {:trigger RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_step)}
      :: RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_step)
      ==> var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
          var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
          var state_after_other_step' := arr.l.step_next(initial_state, other_step);
          && arr.l.step_valid(initial_state, other_step)
          && !arr.l.state_ok(state_after_other_step')
          && RefinementPair(state_after_both_steps, state_after_other_step') in arr.self_relation
  }

  predicate LeftMoverCrashPreservationConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    initial_state:LState,
    left_mover:LOneStep,
    other_step:LOneStep
    )
  {
    var state_after_other_step := arr.l.step_next(initial_state, other_step);
    var tid := arr.l.step_to_thread(left_mover);
    var pc := arr.l.get_thread_pc(initial_state, tid);
    var other_tau := arr.l.is_step_tau(other_step);
    var other_tid := arr.l.step_to_thread(other_step);
    && arr.inv(initial_state)
    && !arr.l.is_step_tau(left_mover)
    && arr.l.step_valid(initial_state, left_mover)
    && arr.l.step_valid(initial_state, other_step)
    && arr.l.state_ok(initial_state)
    && !arr.l.state_ok(state_after_other_step)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && (other_tau || other_tid != tid)
  }
  
  predicate LeftMoverCrashPreservation<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall initial_state, left_mover, other_step
      {:trigger LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_step)}
      :: LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_step)
      ==> var state_after_other_step := arr.l.step_next(initial_state, other_step);
          var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
          var state_after_both_steps := arr.l.step_next(state_after_left_mover, other_step);
          && arr.l.step_valid(state_after_left_mover, other_step)
          && !arr.l.state_ok(state_after_both_steps)
          && RefinementPair(state_after_other_step, state_after_both_steps) in arr.self_relation
  }

  predicate LeftMoverSelfCrashPreservationConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    initial_state:LState,
    left_mover:LOneStep,
    other_step:LOneStep
    )
  {
    var state_after_other_step := arr.l.step_next(initial_state, other_step);
    var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
    var tid := arr.l.step_to_thread(left_mover);
    var pc := arr.l.get_thread_pc(state_after_other_step, tid);
    var other_tau := arr.l.is_step_tau(other_step);
    var other_tid := arr.l.step_to_thread(other_step);
    && arr.inv(initial_state)
    && !arr.l.is_step_tau(left_mover)
    && arr.l.step_valid(initial_state, other_step)
    && arr.l.step_valid(state_after_other_step, left_mover)
    && arr.l.state_ok(initial_state)
    && !arr.l.state_ok(state_after_both_steps)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && (other_tau || other_tid != tid)
  }
    
  predicate LeftMoverSelfCrashPreservation<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall initial_state, left_mover, other_step
      {:trigger LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_step)}
      :: LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_step)
      ==> var state_after_other_step := arr.l.step_next(initial_state, other_step);
          var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
          var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
          && arr.l.step_valid(initial_state, left_mover)
          && !arr.l.state_ok(state_after_left_mover)
          && RefinementPair(state_after_both_steps, state_after_left_mover) in arr.self_relation
  }

  predicate ValidArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    && RefinementRelationReflexive(arr.self_relation)
    && RefinementRelationTransitive(arr.self_relation)
    && RefinementRelationsConvolve(arr.self_relation, arr.relation, arr.relation)
    && LInitImpliesHInit(arr)
    && InitImpliesInv(arr.l, arr.inv)
    && OneStepPreservesInv(arr.l, arr.inv)
    && OneStepRequiresOK(arr.l)
    && InitImpliesYielding(arr.l)
    && InitImpliesOK(arr.l)
    && LStateToHStateMapsPCsCorrectly(arr)
    && LHYieldingCorrespondence(arr)
    && LHOneStepPropertiesMatch(arr)
    && LOneStepImpliesHOneStep(arr)
    && StateConversionPreservesOK(arr)
    && StateConversionSatisfiesRelation(arr)
    && ThreadsDontStartInAnyPhase(arr)
    && PhasesDontOverlap(arr)
    && PhasesPrecededByYielding(arr)
    && PhasesSucceededByYielding(arr)
    && Phase2NotFollowedByPhase1(arr)
    && SteppingThreadHasPC(arr.l)
    && TauLeavesPCUnchanged(arr.l)
    && ThreadCantAffectOtherThreadPhaseExceptViaFork(arr)
    && RightMoversPreserveStateRefinement(arr)
    && LeftMoversPreserveStateRefinement(arr)
    && RightMoversCommute(arr)
    && LeftMoversCommute(arr)
    && RightMoverCrashPreservation(arr)
    && LeftMoverCrashPreservation(arr)
    && LeftMoverSelfCrashPreservation(arr)
    && LeftMoversAlwaysEnabled(arr)
  }

}
