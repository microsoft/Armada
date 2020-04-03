include "TSOEliminationLemmas.i.dfy"

module TSOEliminationModule {

    import opened AnnotatedBehaviorModule
    import opened GeneralRefinementModule
    import opened InvariantsModule
    import opened util_collections_seqs_s
    import opened TSOEliminationSpecModule
    import opened TSOEliminationLemmasModule

    lemma lemma_PerformTSOElimination<LState, HState, ThreadID, LStep, HStep>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>
        ) returns (
        hb:AnnotatedBehavior<HState, HStep>
        )
        requires ValidTSOEliminationRequest(ter)
        requires AnnotatedBehaviorSatisfiesSpec(lb, ter.lspec)
        ensures  BehaviorRefinesBehavior(lb.states, hb.states, ter.relation)
        ensures  AnnotatedBehaviorSatisfiesSpec(hb, ter.hspec)
    {
        var hstates := [ter.initial_state_refiner(lb.states[0])];
        var htrace := [];
        var lh_map := [RefinementRange(0, 0)];
        var pos := 0;

        lemma_InvariantPredicateHoldsAtStep(lb, 0, ter.lspec, ter.inv);

        while pos < |lb.states| - 1
            invariant 0 <= pos < |lb.states|
            invariant |htrace| == |hstates|-1
            invariant hstates[0] in ter.hspec.init
            invariant forall i :: 0 <= i < |htrace| ==> ActionTuple(hstates[i], hstates[i+1], htrace[i]) in ter.hspec.next
            invariant ter.intermediate_relation(lb.states[pos], last(hstates))
            invariant BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hstates, ter.relation, lh_map)
        {
            hstates, htrace, lh_map := lemma_PerformOneStepOfTSOElimination(ter, lb, pos, hstates, htrace, lh_map);
            pos := pos + 1;
        }

        hb := AnnotatedBehavior(hstates, htrace);
        assert lb.states[..pos+1] == lb.states;
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, ter.relation, lh_map);
    }

}
