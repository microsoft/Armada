/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains lemmas useful in effecting a refinement via combining on an Armada behavior.
// They support lemma_PerformArmadaCombining (in ArmadaCombining.i.dfy).
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "ArmadaCombiningSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"
include "../generic/GenericArmadaLemmas.i.dfy"

module ArmadaCombiningLemmasModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaCombiningSpecModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened ArmadaCommonDefinitions

  lemma lemma_LiftMultistepCaseNoSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires |lstep.steps| == 0
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    hstep := Armada_Multistep([], lstep.tid, lstep.tau);
  }

  lemma lemma_LiftMultistepCaseTau<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires lstep.tau
    requires |lstep.steps| == 1
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    var lonestep := lstep.steps[0];
    assert acr.l.step_valid(ls, lonestep);
    assert acr.l.state_ok(ls);
    var tid := acr.l.step_to_thread(lonestep);
    assert Armada_NextMultipleSteps(acr.l, acr.l.step_next(ls, lonestep), ls', lstep.steps[1..]);
    assert lstep.steps[1..] == [];
    assert ls' == acr.l.step_next(ls, lonestep);
    assert Armada_ThreadYielding(acr.l, ls, tid);
    assert !IsInnerStep(acr, ls, ls', lonestep);
    var honestep := acr.lonestep_to_honestep(lonestep);
    assert NonInnerStepsLiftableConditions(acr, ls, lonestep);
    assert acr.h.step_valid(hs, honestep) && hs' == acr.h.step_next(hs, honestep);
    hstep := Armada_Multistep([honestep], acr.h.step_to_thread(honestep), acr.h.is_step_tau(honestep));
    assert Armada_NextMultistep(acr.h, hs, hs', hstep.steps, hstep.tid, hstep.tau);
  }

  lemma lemma_LiftMultistepCaseCombinable<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires !lstep.tau
    requires |lstep.steps| > 0
    requires IsInnerOptionalPC(acr, acr.l.get_thread_pc(acr.l.step_next(ls, lstep.steps[0]), lstep.tid))
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    assert CanCombineInnerStepsConditions(acr, ls, ls', lstep.steps, lstep.tid);
    var honestep :| InnerStepsCombined(acr, ls, ls', honestep);
    assert !acr.h.is_step_tau(honestep) && acr.h.step_valid(hs, honestep) && hs' == acr.h.step_next(hs, honestep);
    hstep := Armada_Multistep([honestep], acr.h.step_to_thread(honestep), false);
    assert Armada_ThreadYielding(acr.l, ls, hstep.tid);
    assert Armada_ThreadYielding(acr.l, ls', hstep.tid);
    assert Armada_NextMultistep(acr.h, hs, hs', hstep.steps, hstep.tid, hstep.tau);
    assert ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next;
  }

  lemma lemma_LiftMultistepCaseAllNonInnerSteps
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState,
    lstates:seq<LState>
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires lstates == Armada_GetStateSequence(acr.l, ls, lstep.steps);
    requires !lstep.tau
    requires |lstep.steps| > 0
    requires forall i :: 0 <= i < |lstep.steps| ==> !IsInnerStep(acr, lstates[i], lstates[i+1], lstep.steps[i])
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    var tid := lstep.tid;
    var lsteps := lstep.steps;
    var hsteps := MapSeqToSeq(lsteps, acr.lonestep_to_honestep);
    hstep := Armada_Multistep(hsteps, tid, lstep.tau);
    var hstates := Armada_GetStateSequence(acr.h, hs, hsteps);

    var pos := 0;
    while pos < |hsteps|
      invariant 0 <= pos <= |hsteps|
      invariant forall i :: 0 <= i <= pos ==> hstates[i] == acr.lstate_to_hstate(lstates[i])
      invariant forall i :: 0 <= i < pos ==> acr.h.step_to_thread(hsteps[i]) == acr.l.step_to_thread(lsteps[i])
      invariant forall i :: 0 <= i < pos ==> acr.h.is_step_tau(hsteps[i]) == acr.l.is_step_tau(lsteps[i])
      invariant forall i :: 0 <= i < pos ==> acr.h.step_valid(hstates[i], hsteps[i])
      invariant forall i :: 0 <= i < pos ==> hstates[i+1] == acr.h.step_next(hstates[i], hsteps[i])
      invariant forall i :: 0 < i < pos ==> var pc := acr.h.get_thread_pc(hstates[i], tid); pc.Some? && acr.h.is_pc_nonyielding(pc.v)
    {
      lemma_InvariantHoldsAtIntermediateState(acr.l, acr.inv, ls, ls', lsteps, lstates, pos);
      lemma_ArmadaNextMultipleStepsImpliesValidStep(acr.l, ls, ls', lsteps, lstates, pos);
      assert !IsInnerStep(acr, lstates[pos], lstates[pos+1], lsteps[pos]);
      assert NonInnerStepsLiftableConditions(acr, lstates[pos], lsteps[pos]);
      lemma_ArmadaGetStateSequenceOnePos(acr.h, hs, hsteps, pos);
      assert hstates[pos+1] == acr.h.step_next(hstates[pos], hsteps[pos]);
      assert hstates[pos+1] == acr.lstate_to_hstate(lstates[pos+1]);
      pos := pos + 1;
    }

    lemma_ArmadaNextMultipleStepsLastElement(acr.l, ls, ls', lsteps, lstates);
    lemma_IfAllStepsValidThenArmadaNextMultipleSteps(acr.h, hstates, hsteps);
    assert Armada_NextMultistep(acr.h, hs, hs', hsteps, tid, lstep.tau);
  }

  lemma lemma_LiftMultistepCaseNonInnerPC<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires !lstep.tau
    requires |lstep.steps| > 0
    requires !IsInnerOptionalPC(acr, acr.l.get_thread_pc(acr.l.step_next(ls, lstep.steps[0]), lstep.tid))
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    var tid := lstep.tid;
    var lsteps := lstep.steps;
    var lstates := Armada_GetStateSequence(acr.l, ls, lstep.steps);

    var pos := 1;
    while pos < |lsteps|
      invariant 1 <= pos <= |lsteps|
      invariant forall i :: 0 <= i <= pos ==> !IsInnerOptionalPC(acr, acr.l.get_thread_pc(lstates[i], tid))
    {
      var pc := acr.l.get_thread_pc(lstates[pos], tid);
      var pc' := acr.l.get_thread_pc(lstates[pos+1], tid);
      lemma_ArmadaNextMultipleStepsImpliesValidStep(acr.l, ls, ls', lsteps, lstates, pos);
      assert !acr.l.is_step_tau(lsteps[pos]);
      assert acr.l.step_valid(lstates[pos], lsteps[pos]);
      assert lstates[pos+1] == acr.l.step_next(lstates[pos], lsteps[pos]);
      if pc'.Some? && acr.is_inner_pc(pc'.v) {
        assert InnerPCPrecededByInnerOrYieldingPCConditions(acr, lstates[pos], lsteps[pos]);
        assert pc.Some? && (acr.is_inner_pc(pc.v) || !acr.l.is_pc_nonyielding(pc.v));
        assert !IsInnerOptionalPC(acr, pc);
        assert !acr.l.is_pc_nonyielding(pc.v);
        assert false;
      }
      assert !IsInnerOptionalPC(acr, pc');
      pos := pos + 1;
    }

    assert forall i :: 0 <= i <= |lsteps| ==> !IsInnerOptionalPC(acr, acr.l.get_thread_pc(lstates[i], tid));

    hstep := lemma_LiftMultistepCaseAllNonInnerSteps(acr, ls, ls', lstep, hs, hs', lstates);
  }

  lemma lemma_LiftMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lstep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState
    ) returns (
    hstep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires acr.inv(ls)
    requires ActionTuple(ls, ls', lstep) in SpecFunctionsToSpec(acr.l).next
    requires forall tid :: Armada_ThreadYielding(acr.l, ls, tid)
    requires forall tid :: Armada_ThreadYielding(acr.l, ls', tid)
    requires hs == acr.lstate_to_hstate(ls)
    requires hs' == acr.lstate_to_hstate(ls')
    ensures  ActionTuple(hs, hs', hstep) in SpecFunctionsToSpec(acr.h).next
  {
    var lstates := Armada_GetStateSequence(acr.l, ls, lstep.steps);
    if |lstep.steps| == 0 {
      hstep := lemma_LiftMultistepCaseNoSteps(acr, ls, ls', lstep, hs, hs');
    }
    else if lstep.tau {
      hstep := lemma_LiftMultistepCaseTau(acr, ls, ls', lstep, hs, hs');
    }
    else if IsInnerOptionalPC(acr, acr.l.get_thread_pc(acr.l.step_next(ls, lstep.steps[0]), lstep.tid)) {
      hstep := lemma_LiftMultistepCaseCombinable(acr, ls, ls', lstep, hs, hs');
    }
    else {
      hstep := lemma_LiftMultistepCaseNonInnerPC(acr, ls, ls', lstep, hs, hs');
    }
  }

}
