/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains a lemma for performing refinement via combining on an Armada behavior.  Such a
// combining takes a behavior satisfying a low-level spec, which has a certain atomic step
// represented as a multistep consisting of two or more mini-steps, and returns a behavior
// satisfying a higher-level specification that has that atomic step consist of a single mini-step.
// It does so by lifting multi-step multisteps in the lower-level specification to single-step
// multisteps in the higher-level specification.
//
// To use this lemma, first create a request r of type ArmadaCombiningRequest (defined in
// ArmadaCombiningSpec.i.dfy).  Then, prove that it's a valid request, i.e., that
// ValidArmadaCombiningRequest(r).
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "ArmadaCombiningSpec.i.dfy"
include "ArmadaCombiningLemmas.i.dfy"

module ArmadaCombiningModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened GeneralRefinementModule
  import opened AnnotatedBehaviorModule
  import opened ArmadaCombiningSpecModule
  import opened ArmadaCombiningLemmasModule
  import opened GenericArmadaLemmasModule
  import opened ArmadaCommonDefinitions
  import opened GenericArmadaSpecModule

  lemma lemma_PerformArmadaCombining<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    acr:ArmadaCombiningRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    lb:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>
    ) returns (
    hb:AnnotatedBehavior<HState, Armada_Multistep<HOneStep>>
    )
    requires ValidArmadaCombiningRequest(acr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(acr.l))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, acr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(acr.h))
  {
    var hstates := MapSeqToSeq(lb.states, acr.lstate_to_hstate);
    var htrace := [];
    var pos := 0;

    while pos < |lb.trace|
      invariant 0 <= pos <= |lb.trace|
      invariant |htrace| == pos
      invariant AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(hstates[..pos+1], htrace), SpecFunctionsToSpec(acr.h))
      invariant acr.inv(lb.states[pos])
    {
      lemma_MultistepNextMaintainsInv(acr.l, acr.inv, lb.states[pos], lb.states[pos+1], lb.trace[pos]);
      lemma_AllThreadsYieldingAtPos(acr.l, lb, pos);
      lemma_AllThreadsYieldingAtPos(acr.l, lb, pos+1);
      var hstep := lemma_LiftMultistep(acr, lb.states[pos], lb.states[pos+1], lb.trace[pos], hstates[pos], hstates[pos+1]);
      htrace := htrace + [hstep];
      pos := pos + 1;
    }

    hb := AnnotatedBehavior(hstates, htrace);
    var lh_map := ConvertMapToSeq(|lb.states|, map i | 0 <= i < |lb.states| :: RefinementRange(i, i));
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hstates, acr.relation, lh_map);
  }

}
