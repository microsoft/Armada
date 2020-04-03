include "StarWeakeningSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"
include "../../spec/refinement.s.dfy"

module StarWeakeningModule {

    import opened StarWeakeningSpecModule
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule
    import opened util_collections_seqs_i
    import opened util_collections_seqs_s
    
    lemma lemma_LRefinesH<LState, HState, LStep, HStep> (
      lb:AnnotatedBehavior<LState, LStep>,
      hb:AnnotatedBehavior<HState, HStep>,
      wr:StarWeakeningRequest<LState, HState, LStep, HStep>,
      lh_map:RefinementMap)
      
      requires ValidStarWeakeningRequest(wr)
      requires AnnotatedBehaviorSatisfiesSpec(lb, wr.lspec)
      requires hb.states == MapSeqToSeq(lb.states, wr.converter);
      requires |lh_map| == |lb.states|
      requires forall i :: 0 <= i < |lh_map| ==> lh_map[i] == RefinementRange(i, i)
      ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, wr.relation, lh_map)
    {
      assert hb.states == MapSeqToSeq(lb.states, wr.converter);
      lemma_InvariantHoldsAtStep(lb, 0, wr.lspec, wr.inv);
      var i := 0;
      while i < |lb.states|
        invariant 0 <= i <= |lb.states|
        invariant forall j :: 0 <= j < i ==>  RefinementPair(lb.states[j], hb.states[j]) in wr.relation;
      {
        lemma_InvariantHoldsAtStep(lb, i, wr.lspec, wr.inv);
        assert RefinementPair(lb.states[i], hb.states[i]) in wr.relation;
        i := i + 1;
      }
    }

    lemma lemma_PerformStarWeakening<LState, HState, LStep, HStep>(
        wr:StarWeakeningRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>
    )
    returns (
        hb:AnnotatedBehavior<HState, HStep>
    )
      requires ValidStarWeakeningRequest(wr)
      requires AnnotatedBehaviorSatisfiesSpec(lb, wr.lspec)
      ensures  hb.states == MapSeqToSeq(lb.states, wr.converter)
      ensures  AnnotatedBehaviorSatisfiesSpec(hb, wr.hspec)
      ensures  BehaviorRefinesBehavior(lb.states, hb.states, wr.relation)
    {
      var hstates := [wr.converter(lb.states[0])];
      var htrace := [];
      var lh_map := [RefinementRange(0, 0)];
      var pos := 0;

      lemma_InvariantHoldsAtStep(lb, 0, wr.lspec, wr.inv);

      while pos < |lb.states| - 1
        invariant 0 <= pos < |lb.states|
            invariant |htrace| == |hstates|-1
            invariant hstates[0] in wr.hspec.init
            invariant forall i :: 0 <= i < |htrace| ==> ActionTuple(hstates[i], hstates[i+1], htrace[i]) in wr.hspec.next
            invariant last(hstates) == wr.converter(lb.states[pos])
            invariant hstates == MapSeqToSeq(lb.states[..pos + 1], wr.converter)
            invariant forall i :: 0 <= i < |lh_map| ==> lh_map[i] == RefinementRange(i, i)
            invariant |lh_map| == pos + 1
      {
        lemma_InvariantHoldsAtStep(lb, pos, wr.lspec, wr.inv);
        lemma_InvariantHoldsAtStep(lb, pos+1, wr.lspec, wr.inv);
        var ls := lb.states[pos];
        var ls' := lb.states[pos+1];
        var lstep := lb.trace[pos];
        assert ActionTuple(ls, ls', lstep) in wr.lspec.next;
        assert ls in wr.inv;

        var hstep := wr.step_refiner(ls, lstep);
        htrace := htrace + [hstep];
        hstates := hstates + [wr.converter(ls')];
        assert hstates == MapSeqToSeq(lb.states[..pos + 2], wr.converter);
          
        lh_map := lh_map + [RefinementRange(|hstates|-1, |hstates|-1)];
        pos := pos + 1;
      }

      hb := AnnotatedBehavior(hstates, htrace);
      lemma_LRefinesH(lb, hb, wr, lh_map);
    }

}

