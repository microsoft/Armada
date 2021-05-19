/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains a lemma for performing refinement via a Cohen-Lamport reduction on an Armada
// atomic behavior.  Such a reduction takes a behavior satisfying a low-level spec, which allows
// threads to sometimes be in phase 1 or 2 between multisteps, and returns a behavior satisfying a
// higher-level specification that only allows those phases in the middle of multisteps.  It does so
// by lifting sequences of multisteps in the lower-level specification to single multisteps in the
// higher-level specification.
//
// To use this lemma, first create a request r of type AtomicReductionRequest (defined in
// AtomicReductionSpec.i.dfy).  Then, prove that it's a valid request, i.e., that
// ValidAtomicReductionRequest(r).
//
// This lemma makes use of a lemma in another file (lemma_PerformRefinementViaReduction, in
// RefinementViaReduction.i.dfy).  That lemma performs refinement via reduction for generic state
// machines.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "AtomicReductionSpec.i.dfy"
include "AtomicReductionLemmas.i.dfy"
include "RefinementViaReduction.i.dfy"

module AtomicReductionModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened AtomicReductionSpecModule
  import opened AtomicReductionLemmasModule
  import opened RefinementViaReductionSpecModule
  import opened RefinementViaReductionModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaAtomicModule
  import opened ArmadaCommonDefinitions

  lemma lemma_ReduceAtomicBehavior<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    lb:AnnotatedBehavior<LState, AtomicTraceEntry<LPath>>
    ) returns (
    hb:AnnotatedBehavior<HState, AtomicTraceEntry<HPath>>
    )
    requires ValidAtomicReductionRequest(arr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, AtomicAnnotatedSpec(arr.l))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, arr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, AtomicAnnotatedSpec(arr.h))
  {
    var mb1 := lemma_IfBehaviorSatisfiesGenericSpecThenItSatisfiesRefinementViaReductionLSpec(arr, lb);

    lemma_IfAtomicReductionRequestValidThenRefinementViaReductionRequestValid(arr);
    var mb2 := lemma_PerformRefinementViaReduction(GetRefinementViaReductionRequest(arr), mb1);

    var hstates := MapSeqToSeq(mb2.states, arr.lstate_to_hstate);
    var htrace := MapSeqToSeq(mb2.trace, x => ConvertMultistepToAtomicTraceEntry(arr, x));
    hb := AnnotatedBehavior(hstates, htrace);

    var mh_map := ConvertMapToSeq(|hstates|, map i | 0 <= i < |hstates| :: RefinementRange(i, i));
    var hspec := AtomicAnnotatedSpec(arr.h);
    assert BehaviorRefinesBehaviorUsingRefinementMap(mb2.states, hb.states, arr.relation, mh_map);
    forall i | 0 <= i < |htrace|
      ensures ActionTuple(hstates[i], hstates[i+1], htrace[i]) in hspec.next
    {
      lemma_GenericNextReducedBehaviorSatisfiesInv(arr, mb2, i);
      lemma_LHMaintainsNext(arr, mb2.states[i], mb2.states[i+1], mb2.trace[i], hstates[i], hstates[i+1], htrace[i]);
    }
    assert AnnotatedBehaviorSatisfiesSpec(hb, hspec);
    lemma_RefinementConvolutionPure(lb.states, mb2.states, hb.states, arr.self_relation, arr.relation, arr.relation);
  }

  lemma lemma_PerformAtomicReduction<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  SpecRefinesSpec(AtomicSpec(arr.l), AtomicSpec(arr.h), arr.relation)
  {
    var lspec := AtomicSpec(arr.l);
    var hspec := AtomicSpec(arr.h);
    forall lb | BehaviorSatisfiesSpec(lb, lspec)
      ensures BehaviorRefinesSpec(lb, hspec, arr.relation)
    {
      var alb := lemma_AtomicBehaviorToAnnotatedBehavior(arr.l, lb);
      var ahb := lemma_ReduceAtomicBehavior(arr, alb);
      lemma_AtomicAnnotatedBehaviorSatisfiesAtomicSpec(arr.h, ahb);
      assert BehaviorRefinesBehavior(lb, ahb.states, arr.relation) && BehaviorSatisfiesSpec(ahb.states, hspec);
    }
  }

}
