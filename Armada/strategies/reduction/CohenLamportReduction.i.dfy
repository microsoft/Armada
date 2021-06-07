/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains the lemma for performing a Cohen-Lamport reduction on a behavior.  Such a
// reduction takes a behavior where some states are in phase 1 or 2, and returns a behavior in which
// no state (except possibly the last, crashing state) is in phase 1 or 2.  That resulting behavior
// satisfies the same specification, but is a refinement of the original behavior.
//
// To use this lemma, lemma_PerformCohenLamportReduction, you need to first create a request r of
// type CohenLamportReductionRequest (defined in CohenLamportReductionSpec.i.dfy), then prove that
// it's a valid request, i.e., that ValidCohenLamportReductionRequest(r).
//
// The lemma allows behaviors that crash as their final step.  But, it demans that action sequences
// be reducible if they crash in the middle, i.e., even if the actor performing those action
// sequences executes a step that crashes while in phase 1 or 2.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "CohenLamportReductionSpec.i.dfy"
include "CohenLamportReductionLemmas.i.dfy"

module CohenLamportReductionModule {

  import opened AnnotatedBehaviorModule
  import opened GeneralRefinementModule
  import opened RefinementConvolutionModule
  import opened CohenLamportReductionSpecModule
  import opened CohenLamportReductionLemmasModule

  lemma lemma_PerformCohenLamportReduction<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  forall i, actor :: 0 <= i < |hb.states| ==> var s := hb.states[i]; !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
  {
    var mb := lemma_RemoveAllNonmovers(clrr, lb);
    hb := lemma_RemoveAllRightMovers(clrr, mb);
    lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);
  }

}
