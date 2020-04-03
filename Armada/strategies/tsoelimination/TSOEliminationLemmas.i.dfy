include "TSOEliminationSpec.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../../util/collections/seqs.i.dfy"

module TSOEliminationLemmasModule {

    import opened TSOEliminationSpecModule
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule
    import opened RefinementConvolutionModule

    lemma lemma_IntermediateRelationImpliesRefinementRelation<LState, HState, ThreadID, LStep, HStep>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>,
        ls:LState,
        hs:HState
        )
        requires ValidTSOEliminationRequest(ter)
        requires ter.inv(ls)
        requires ter.intermediate_relation(ls, hs)
        ensures  RefinementPair(ls, hs) in ter.relation
    {
    }

    lemma lemma_PerformOneStepOfTSOElimination<LState, HState, ThreadID, LStep, HStep>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>,
        pos:int,
        hstates:seq<HState>,
        htrace:seq<HStep>,
        lh_map:RefinementMap
        ) returns (
        hstates':seq<HState>,
        htrace':seq<HStep>,
        lh_map':RefinementMap
        )
        requires ValidTSOEliminationRequest(ter)
        requires AnnotatedBehaviorSatisfiesSpec(lb, ter.lspec)
        requires 0 <= pos < |lb.states| - 1
        requires |htrace| == |hstates|-1
        requires hstates[0] in ter.hspec.init
        requires forall i :: 0 <= i < |htrace| ==> ActionTuple(hstates[i], hstates[i+1], htrace[i]) in ter.hspec.next
        requires ter.intermediate_relation(lb.states[pos], last(hstates))
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hstates, ter.relation, lh_map)
        ensures  |htrace'| == |hstates'|-1
        ensures  hstates'[0] == hstates[0]
        ensures  forall i :: 0 <= i < |htrace'| ==> ActionTuple(hstates'[i], hstates'[i+1], htrace'[i]) in ter.hspec.next
        ensures  ter.intermediate_relation(lb.states[pos+1], last(hstates'))
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+2], hstates', ter.relation, lh_map')
    {
        var ls := lb.states[pos];
        var ls' := lb.states[pos+1];
        var lstep := lb.trace[pos];
        var hs := last(hstates);
        assert ActionTuple(ls, ls', lstep) in ter.lspec.next;

        lemma_InvariantPredicateHoldsAtStep(lb, pos, ter.lspec, ter.inv);
        assert ter.inv(ls);

        assert ter.intermediate_relation(ls, hs);

        var hstep := ter.step_refiner(ls, hs, lstep);
        var hs' := ter.next_state(hs, hstep);
        
        assert ActionTuple(hs, hs', hstep) in ter.hspec.next;
        assert ter.intermediate_relation(ls', hs');

        hstates' := hstates + [hs'];
        htrace' := htrace + [hstep];
        lh_map' := lh_map + [RefinementRange(|hstates|, |hstates|)];

        lemma_InvariantPredicateHoldsAtStep(lb, pos+1, ter.lspec, ter.inv);
        lemma_IntermediateRelationImpliesRefinementRelation(ter, ls', hs');

        var lstates := lb.states[..pos+2];
        forall i, j {:trigger RefinementPair(lstates[i], hstates'[j]) in ter.relation}
            | 0 <= i < |lstates| && lh_map'[i].first <= j <= lh_map'[i].last
            ensures RefinementPair(lstates[i], hstates'[j]) in ter.relation
        {
        }

        forall i | 0 <= i < |lh_map'|-1
            ensures lh_map'[i+1].first == lh_map'[i].last || lh_map'[i+1].first == lh_map'[i].last + 1
        {
            if i < |lh_map|-1 {
                assert lh_map'[i] == lh_map[i];
                assert lh_map'[i+1] == lh_map[i+1];
            }
            else {
                assert lh_map'[i] == last(lh_map);
                assert last(lh_map).last == |hstates|-1;
                assert lh_map'[i+1].first == |hstates|;
                assert lh_map'[i+1].first == lh_map'[i].last + 1;
            }
        }

        forall i | 0 <= i < |htrace'|
            ensures ActionTuple(hstates'[i], hstates'[i+1], htrace'[i]) in ter.hspec.next
        {
            if i < |htrace| {
                assert hstates'[i] == hstates[i];
                assert hstates'[i+1] == hstates[i+1];
                assert htrace'[i] == htrace[i];
            }
            else {
                assert i == |htrace| == |hstates|-1;
                assert hstates[i] == last(hstates);
                assert hstates'[i] == hstates[i] == last(hstates) == hs;
                assert hstates'[i+1] == hs';
                assert htrace'[i] == hstep;
            }
        }
    }
}
