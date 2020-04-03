include "VarHidingSpec.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../../util/collections/seqs.i.dfy"

module VarHidingModule {

    import opened VarHidingSpecModule
    import opened util_collections_maps_s
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule
    import opened RefinementConvolutionModule

    lemma lemma_PerformVarHiding<LState, HState, LStep, HStep>(
        vr:VarHidingRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>
        ) returns (
        hb:AnnotatedBehavior<HState, HStep>
        )
        requires ValidVarHidingRequest(vr)
        requires AnnotatedBehaviorSatisfiesSpec(lb, vr.lspec)
        ensures  BehaviorRefinesBehavior(lb.states, hb.states, vr.relation)
        ensures  AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
    {
        var hstates := [vr.hider(lb.states[0])];
        var htrace := [];
        var lh_map := [RefinementRange(0, 0)];
        var pos := 0;

        lemma_InvariantPredicateHoldsAtStep(lb, 0, vr.lspec, vr.inv);

        while pos < |lb.states| - 1
            invariant 0 <= pos < |lb.states|
            invariant |htrace| == |hstates|-1
            invariant hstates[0] in vr.hspec.init
            invariant forall i :: 0 <= i < |htrace| ==> ActionTuple(hstates[i], hstates[i+1], htrace[i]) in vr.hspec.next
            invariant last(hstates) == vr.hider(lb.states[pos])
            invariant BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hstates, vr.relation, lh_map)
        {
            lemma_InvariantPredicateHoldsAtStep(lb, pos, vr.lspec, vr.inv);
            lemma_InvariantPredicateHoldsAtStep(lb, pos+1, vr.lspec, vr.inv);
            var s := lb.states[pos];
            var s' := lb.states[pos+1];
            var lstep := lb.trace[pos];
            assert ActionTuple(s, s', lstep) in vr.lspec.next;
            assert vr.inv(s);
            if (vr.hider(s) != vr.hider(s')) {
                var hstep := vr.step_refiner(s, lstep);
                htrace := htrace + [hstep];
                hstates := hstates + [vr.hider(s')];
            }
            lh_map := lh_map + [RefinementRange(|hstates|-1, |hstates|-1)];
            pos := pos + 1;

            var lstates := lb.states[..pos+1];
            forall i, j {:trigger RefinementPair(lstates[i], hstates[j]) in vr.relation}
                | 0 <= i < |lstates| && lh_map[i].first <= j <= lh_map[i].last
                ensures RefinementPair(lstates[i], hstates[j]) in vr.relation
            {
            }
        }

        hb := AnnotatedBehavior(hstates, htrace);
        assert lb.states[..pos+1] == lb.states;
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, vr.relation, lh_map);
    }

}
