/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains a lemma for performing refinement via a Cohen-Lamport reduction on an Armada
// behavior.  Such a reduction takes a behavior satisfying a low-level spec, which allows threads to
// sometimes be in phase 1 or 2 between multisteps, and returns a behavior satisfying a higher-level
// specification that only allows those phases in the middle of multisteps.  It does so by lifting
// sequences of multisteps in the lower-level specification to single multisteps in the higher-level
// specification.
//
// To use this lemma, first create a request r of type ArmadaReductionRequest (defined in
// ArmadaReductionSpec.i.dfy).  Then, prove that it's a valid request, i.e., that
// ValidArmadaReductionRequest(r).
//
// This lemma makes use of a lemma in another file (lemma_PerformRefinementViaReduction, in
// RefinementViaReduction.i.dfy).  That lemma performs refinement via reduction for generic state
// machines.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "ArmadaReductionSpec.i.dfy"
include "ArmadaReductionLemmas.i.dfy"
include "RefinementViaReduction.i.dfy"

module ArmadaReductionModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaReductionSpecModule
  import opened ArmadaReductionLemmasModule
  import opened RefinementViaReductionSpecModule
  import opened RefinementViaReductionModule
  import opened GenericArmadaSpecModule
  import opened ArmadaCommonDefinitions

  lemma lemma_PerformArmadaReduction<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    lb:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>
    ) returns (
    hb:AnnotatedBehavior<HState, Armada_Multistep<HOneStep>>
    )
    requires ValidArmadaReductionRequest(arr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(arr.l))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, arr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(arr.h))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    var hspec := SpecFunctionsToSpec(arr.h);

    lemma_IfArmadaReductionRequestValidThenRefinementViaReductionRequestValid(arr);
    lemma_IfBehaviorSatisfiesGenericSpecThenItSatisfiesRefinementViaReductionLSpec(arr, lb);
    var mb := lemma_PerformRefinementViaReduction(rr, lb);
    var hstates := MapSeqToSeq(mb.states, arr.lstate_to_hstate);
    var htrace := MapSeqToSeq(mb.trace, x => LMultistepToHMultistep(arr, x));
    hb := AnnotatedBehavior(hstates, htrace);
    assert hstates[0] in hspec.init;
    var mh_map := ConvertMapToSeq(|hstates|, map i | 0 <= i < |hstates| :: RefinementRange(i, i));
    assert BehaviorRefinesBehaviorUsingRefinementMap(mb.states, hb.states, arr.relation, mh_map);
    forall i | 0 <= i < |htrace|
      ensures ActionTuple(hstates[i], hstates[i+1], htrace[i]) in hspec.next
    {
      lemma_GenericNextReducedBehaviorSatisfiesInv(arr, mb, i);
      lemma_LHMaintainsNext(arr, mb.states[i], mb.states[i+1], mb.trace[i], hstates[i], hstates[i+1], htrace[i]);
    }
    assert AnnotatedBehaviorSatisfiesSpec(hb, hspec);
    lemma_RefinementConvolutionPure(lb.states, mb.states, hb.states, arr.self_relation, arr.relation, arr.relation);
  }

}
