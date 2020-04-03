include "VarIntroSpec.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../../util/collections/seqs.s.dfy"
include "../../util/collections/seqs.i.dfy"

module VarIntroModule {

    import opened VarIntroSpecModule
    import opened util_collections_maps_s
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule
    import opened RefinementConvolutionModule

    lemma lemma_PerformVarIntroOneStepCaseAtNewInstruction<LState, HState, LStep, HStep>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>,
        hb:AnnotatedBehavior<HState, HStep>,
        lh_map:RefinementMap,
        pos:int
        )
        returns (
        hb':AnnotatedBehavior<HState, HStep>,
        lh_map':RefinementMap
        )
        requires ValidVarIntroRequest(vr)
        requires AnnotatedBehaviorSatisfiesSpec(lb, vr.lspec)
        requires 1 <= pos < |lb.states|
        requires |hb.states| > 0
        requires vr.at_new_instruction(last(hb.states))
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, vr.relation, lh_map)
        requires AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
        requires lb.states[pos-1] == vr.hider(last(hb.states))
        requires vr.inv(last(hb.states))
        ensures  |hb'.states| > 0
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hb'.states, vr.relation, lh_map')
        ensures  AnnotatedBehaviorSatisfiesSpec(hb', vr.hspec)
        ensures  lb.states[pos] == vr.hider(last(hb'.states))
        ensures  vr.inv(last(hb'.states))
        decreases vr.progress_measure(last(hb.states)), 0
    {
        var hs := last(hb.states);
        var hstep := vr.next_step(hs);
        var hs_mid := vr.next_state(hs, hstep);
        assert vr.inv(hs_mid);
        assert vr.hider(hs) == vr.hider(hs_mid);
        assert ActionTuple(hs, hs_mid, hstep) in vr.hspec.next;
        assert 0 <= vr.progress_measure(hs_mid) < vr.progress_measure(hs);

        var htrace_mid := hb.trace + [hstep];
        var hstates_mid := hb.states + [hs_mid];
        var hb_mid := AnnotatedBehavior(hstates_mid, htrace_mid);
        var lh_map_mid := lh_map[|lh_map|-1 := last(lh_map).(last := |hb.states|)];
        hb', lh_map' := lemma_PerformVarIntroOneStep(vr, lb, hb_mid, lh_map_mid, pos);
    }

    lemma lemma_PerformVarIntroOneStepCaseNotAtNewInstruction<LState, HState, LStep, HStep>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>,
        hb:AnnotatedBehavior<HState, HStep>,
        lh_map:RefinementMap,
        pos:int
        )
        returns (
        hb':AnnotatedBehavior<HState, HStep>,
        lh_map':RefinementMap
        )
        requires ValidVarIntroRequest(vr)
        requires AnnotatedBehaviorSatisfiesSpec(lb, vr.lspec)
        requires 1 <= pos < |lb.states|
        requires |hb.states| > 0
        requires !vr.at_new_instruction(last(hb.states))
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, vr.relation, lh_map)
        requires AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
        requires lb.states[pos-1] == vr.hider(last(hb.states))
        requires vr.inv(last(hb.states))
        ensures  |hb'.states| > 0
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hb'.states, vr.relation, lh_map')
        ensures  AnnotatedBehaviorSatisfiesSpec(hb', vr.hspec)
        ensures  lb.states[pos] == vr.hider(last(hb'.states))
        ensures  vr.inv(last(hb'.states))
        decreases vr.progress_measure(last(hb.states))
    {
        var prev := pos-1;
        var ls := lb.states[prev];
        var ls' := lb.states[prev+1];
        var lstep := lb.trace[prev];
        assert ActionTuple(ls, ls', lstep) in vr.lspec.next;
        var hs := last(hb.states);
        var hstep := vr.step_mapper(lstep);
        var hs' := vr.next_state(hs, hstep);
        assert vr.inv(hs');
        assert ls' == vr.hider(hs');
        assert ActionTuple(hs, hs', hstep) in vr.hspec.next;
        var htrace' := hb.trace + [hstep];
        var hstates' := hb.states + [hs'];
        lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];
        hb' := AnnotatedBehavior(hstates', htrace');

        var lstates' := lb.states[..pos+1];
        forall i, j {:trigger RefinementPair(lstates'[i], hstates'[j]) in vr.relation}
            | 0 <= i < |lstates'| && lh_map'[i].first <= j <= lh_map'[i].last
            ensures RefinementPair(lstates'[i], hstates'[j]) in vr.relation
        {
        }
    }

    lemma lemma_PerformVarIntroOneStep<LState, HState, LStep, HStep>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>,
        hb:AnnotatedBehavior<HState, HStep>,
        lh_map:RefinementMap,
        pos:int
        )
        returns (
        hb':AnnotatedBehavior<HState, HStep>,
        lh_map':RefinementMap
        )
        requires ValidVarIntroRequest(vr)
        requires AnnotatedBehaviorSatisfiesSpec(lb, vr.lspec)
        requires 1 <= pos < |lb.states|
        requires |hb.states| > 0
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, vr.relation, lh_map)
        requires AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
        requires lb.states[pos-1] == vr.hider(last(hb.states))
        requires vr.inv(last(hb.states))
        ensures  |hb'.states| > 0
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hb'.states, vr.relation, lh_map')
        ensures  AnnotatedBehaviorSatisfiesSpec(hb', vr.hspec)
        ensures  lb.states[pos] == vr.hider(last(hb'.states))
        ensures  vr.inv(last(hb'.states))
        decreases vr.progress_measure(last(hb.states)), 1
    {
        var ls := lb.states[pos-1];
        var ls' := lb.states[pos-1+1];
        var hs := last(hb.states);

        if vr.at_new_instruction(hs) {
            hb', lh_map' := lemma_PerformVarIntroOneStepCaseAtNewInstruction(vr, lb, hb, lh_map, pos);
        }
        else {
            hb', lh_map' := lemma_PerformVarIntroOneStepCaseNotAtNewInstruction(vr, lb, hb, lh_map, pos);
        }
    }

    lemma lemma_PerformVarIntro<LState, HState, LStep, HStep>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>,
        lb:AnnotatedBehavior<LState, LStep>
        ) returns (
        hb:AnnotatedBehavior<HState, HStep>
        )
        requires ValidVarIntroRequest(vr)
        requires AnnotatedBehaviorSatisfiesSpec(lb, vr.lspec)
        ensures  BehaviorRefinesBehavior(lb.states, hb.states, vr.relation)
        ensures  AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
    {
        var ls := lb.states[0];
        assert ls in vr.lspec.init;
        var hs := vr.revealer(ls);
        assert vr.hider(hs) == ls && vr.inv(hs) && hs in vr.hspec.init;
        var hstates := [hs];
        var htrace := [];
        hb := AnnotatedBehavior(hstates, htrace);
        var pos := 1;
        var lh_map := [RefinementRange(0, 0)];

        while pos < |lb.states|
            invariant 1 <= pos <= |lb.states|
            invariant |hb.states| > 0
            invariant BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, vr.relation, lh_map)
            invariant AnnotatedBehaviorSatisfiesSpec(hb, vr.hspec)
            invariant lb.states[pos-1] == vr.hider(last(hb.states))
            invariant vr.inv(last(hb.states))
        {
            hb, lh_map := lemma_PerformVarIntroOneStep(vr, lb, hb, lh_map, pos);
            pos := pos + 1;
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, vr.relation, lh_map);
    }

}
