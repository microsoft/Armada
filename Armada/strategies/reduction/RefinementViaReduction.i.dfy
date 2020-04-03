/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains a lemma for performing refinement via a Cohen-Lamport reduction on a
// behavior. Such a reduction takes a behavior where some states are in phase 1 or 2, and returns a
// behavior satisfying a higher-level specification that lacks those phases.  It does so by lifting
// sequences of steps in the lower-level specification to atomic steps in the higher-level
// specification.
//
// To use this specification, first create a request r of type RefinementViaReductionRequest.  Then,
// prove that it's a valid request, i.e., that ValidRefinementViaReductionRequest(r).  Finally, call
// lemma_PerformRefinementViaReduction (in RefinementViaReduction.i.dfy).
//
// The request specification allows behaviors that crash as their final step.  But, the request
// specification also demands that action sequences be reducible if they crash in the middle, i.e.,
// even if the actor performing those action sequences executes a step that crashes while in phase 1
// or 2.
//
// This lemma makes use of a lemma (lemma_PerformCohenLamportReduction) for performing Cohen-Lamport
// reduction on a behavior without changing its specification.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "RefinementViaReductionLemmas.i.dfy"
include "CohenLamportReduction.i.dfy"

module RefinementViaReductionModule {

  import opened AnnotatedBehaviorModule
  import opened RefinementViaReductionSpecModule
  import opened RefinementViaReductionLemmasModule
  import opened GeneralRefinementModule
  import opened RefinementConvolutionModule
  import opened CohenLamportReductionModule

  lemma lemma_PerformRefinementViaReduction<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    lb:AnnotatedBehavior<State, LStep>
    ) returns (
    hb:AnnotatedBehavior<State, HStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, rr.lspec)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, rr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, rr.hspec)
  {
    var cb := lemma_LiftBehaviorToCrossLevel(rr, lb);
    var clrr := GetCohenLamportReductionRequest(rr);
    lemma_IsValidCohenLamportReductionRequest(rr);
    var mb := lemma_PerformCohenLamportReduction(clrr, cb);
    lemma_RefinementConvolutionPure(lb.states, cb.states, mb.states, GetIdentityRelation<State>(), clrr.relation, rr.relation);
    hb := lemma_LiftBehaviorToHighLayer(rr, mb);
  }
}
