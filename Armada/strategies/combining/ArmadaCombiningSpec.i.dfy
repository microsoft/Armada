/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file is the specification for a request to perform combining on an Armada behavior.  Such a
// combining takes a behavior satisfying a low-level spec, which has a certain atomic step
// represented as a multistep consisting of two or more mini-steps, and returns a behavior
// satisfying a higher-level specification that has that atomic step consist of a single mini-step.
// It does so by lifting multi-step multisteps in the lower-level specification to single-step
// multisteps in the higher-level specification.
//
// To use this specification, first create a request r of type ArmadaCombiningRequest.  Then, prove
// that it's a valid request, i.e., that ValidArmadaCombiningRequest(r).  Finally, call
// lemma_PerformArmadaCombining (in ArmadaCombining.i.dfy).
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

module ArmadaCombiningSpecModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened GenericArmadaSpecModule
  import opened ArmadaCommonDefinitions

  datatype ArmadaCombiningRequest<!LState, !LOneStep, !LPC, !HState, !HOneStep, !HPC> =
    ArmadaCombiningRequest(
      l:Armada_SpecFunctions<LState, LOneStep, LPC>,
      h:Armada_SpecFunctions<HState, HOneStep, HPC>,
      relation:RefinementRelation<LState, HState>,
      inv:LState->bool,
      lstate_to_hstate:LState->HState,
      lonestep_to_honestep:LOneStep->HOneStep,
      lpc_to_hpc:LPC->HPC,
      is_inner_pc:LPC->bool
      )

  predicate IsInnerOptionalPC
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    pc:Option<LPC>
    )
  {
    pc.Some? && acr.is_inner_pc(pc.v)
  }

  predicate IsInnerStep
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:LOneStep
    )
  {
    var tid := acr.l.step_to_thread(step);
    || IsInnerOptionalPC(acr, acr.l.get_thread_pc(s, tid))
    || IsInnerOptionalPC(acr, acr.l.get_thread_pc(s', tid))
  }

  predicate LInitImpliesHInit<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: acr.l.init(ls) ==> acr.h.init(acr.lstate_to_hstate(ls))
  }

  predicate LStateToHStateMapsPCsCorrectly
    <LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, tid :: var hs := acr.lstate_to_hstate(ls);
                var lpc := acr.l.get_thread_pc(ls, tid);
                var hpc := acr.h.get_thread_pc(hs, tid);
                hpc == if lpc.Some? then Some(acr.lpc_to_hpc(lpc.v)) else None()
  }

  predicate LHYieldingCorrespondence<LState, LOneStep, LPC(!new), HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall lpc :: var hpc := acr.lpc_to_hpc(lpc);
            acr.is_inner_pc(lpc) || (acr.h.is_pc_nonyielding(hpc) <==> acr.l.is_pc_nonyielding(lpc))
  }

  predicate StateConversionPreservesOK<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: acr.h.state_ok(acr.lstate_to_hstate(ls)) == acr.l.state_ok(ls)
  }

  predicate StateConversionSatisfiesRelation
    <LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls :: RefinementPair(ls, acr.lstate_to_hstate(ls)) in acr.relation
  }

  predicate InnerPCsDontYield<LState, LOneStep, LPC(!new), HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall pc :: acr.is_inner_pc(pc) ==> acr.l.is_pc_nonyielding(pc)
  }

  predicate InnerPCPrecededByInnerOrYieldingPCConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    lstep:LOneStep
    )
  {
    var ls' := acr.l.step_next(ls, lstep);
    var tid := acr.l.step_to_thread(lstep);
    var pc' := acr.l.get_thread_pc(ls', tid);
    && !acr.l.is_step_tau(lstep)
    && acr.l.step_valid(ls, lstep)
    && pc'.Some?
    && acr.is_inner_pc(pc'.v)
  }

  predicate InnerPCPrecededByInnerOrYieldingPC
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, lstep {:trigger InnerPCPrecededByInnerOrYieldingPCConditions(acr, ls, lstep)} ::
      InnerPCPrecededByInnerOrYieldingPCConditions(acr, ls, lstep)
      ==> var tid := acr.l.step_to_thread(lstep);
          var pc := acr.l.get_thread_pc(ls, tid);
          pc.Some? && (acr.is_inner_pc(pc.v) || !acr.l.is_pc_nonyielding(pc.v))
  }

  predicate InnerPCSucceededByInnerOrYieldingPCConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    lstep:LOneStep
    )
  {
    var tid := acr.l.step_to_thread(lstep);
    var pc := acr.l.get_thread_pc(ls, tid);
    && !acr.l.is_step_tau(lstep)
    && acr.l.step_valid(ls, lstep)
    && pc.Some?
    && acr.is_inner_pc(pc.v)
  }

  predicate InnerPCSucceededByInnerOrYieldingPC
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, lstep {:trigger InnerPCSucceededByInnerOrYieldingPCConditions(acr, ls, lstep)} ::
      InnerPCSucceededByInnerOrYieldingPCConditions(acr, ls, lstep)
      ==> var tid := acr.l.step_to_thread(lstep);
          var ls' := acr.l.step_next(ls, lstep);
          var pc' := acr.l.get_thread_pc(ls', tid);
          pc'.Some? && (acr.is_inner_pc(pc'.v) || !acr.l.is_pc_nonyielding(pc'.v))
  }

  predicate NonInnerStepsLiftableConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    lstep:LOneStep
    )
  {
    var ls' := acr.l.step_next(ls, lstep);
    && acr.inv(ls)
    && acr.l.step_valid(ls, lstep)
    && !IsInnerStep(acr, ls, ls', lstep)
  }

  predicate NonInnerStepsLiftable<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, lstep {:trigger NonInnerStepsLiftableConditions(acr, ls, lstep)} ::
      NonInnerStepsLiftableConditions(acr, ls, lstep)
      ==> var ls' := acr.l.step_next(ls, lstep);
          var hs := acr.lstate_to_hstate(ls);
          var hstep := acr.lonestep_to_honestep(lstep);
          var hs' := acr.lstate_to_hstate(ls');
          && acr.l.step_to_thread(lstep) == acr.h.step_to_thread(hstep)
          && acr.l.is_step_tau(lstep) == acr.h.is_step_tau(hstep)
          && acr.h.step_valid(hs, hstep)
          && hs' == acr.h.step_next(hs, hstep)
  }

  predicate CanCombineInnerStepsConditions
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep(!new), HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lsteps:seq<LOneStep>,
    tid:Armada_ThreadHandle
    )
  {
     && acr.inv(ls)
     && Armada_NextMultistep(acr.l, ls, ls', lsteps, tid, false)
     && |lsteps| > 0
     && IsInnerOptionalPC(acr, acr.l.get_thread_pc(acr.l.step_next(ls, lsteps[0]), tid))
  }

  predicate InnerStepsCombined
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    hstep:HOneStep
    )
  {
    var hs := acr.lstate_to_hstate(ls);
    var hs' := acr.lstate_to_hstate(ls');
    !acr.h.is_step_tau(hstep) && acr.h.step_valid(hs, hstep) && hs' == acr.h.step_next(hs, hstep)
  }

  predicate CanCombineInnerSteps
    <LState(!new), LOneStep(!new), LPC, HState, HOneStep(!new), HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    forall ls, ls', lsteps, tid {:trigger CanCombineInnerStepsConditions(acr, ls, ls', lsteps, tid)} ::
      CanCombineInnerStepsConditions(acr, ls, ls', lsteps, tid)
      ==> exists hstep :: InnerStepsCombined(acr, ls, ls', hstep)
  }

  predicate ValidArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
  {
    && InitImpliesInv(acr.l, acr.inv)
    && OneStepPreservesInv(acr.l, acr.inv)
    && OneStepRequiresOK(acr.l)
    && InitImpliesYielding(acr.l)
    && InitImpliesOK(acr.l)
    && SteppingThreadHasPC(acr.l)
    && TauLeavesPCUnchanged(acr.l)
    && ThreadCantAffectOtherThreadPCExceptViaFork(acr.l)
    && LInitImpliesHInit(acr)
    && LStateToHStateMapsPCsCorrectly(acr)
    && LHYieldingCorrespondence(acr)
    && StateConversionPreservesOK(acr)
    && StateConversionSatisfiesRelation(acr)
    && InnerPCsDontYield(acr)
    && InnerPCPrecededByInnerOrYieldingPC(acr)
    && InnerPCSucceededByInnerOrYieldingPC(acr)
    && NonInnerStepsLiftable(acr)
    && CanCombineInnerSteps(acr)
  }

}

