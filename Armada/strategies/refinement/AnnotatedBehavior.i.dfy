include "../../spec/refinement.s.dfy"
include "../../util/collections/seqs.i.dfy"

module AnnotatedBehaviorModule {

    import opened GeneralRefinementModule
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i

    datatype ActionTuple<State, Step> = ActionTuple(s:State, s':State, step:Step)

    datatype AnnotatedBehavior<State, Step> = AnnotatedBehavior(
        states:seq<State>,
        trace:seq<Step>
        )

    datatype AnnotatedBehaviorSpec<State(==), Step(==)> = AnnotatedBehaviorSpec(
        init:iset<State>,
        next:iset<ActionTuple<State, Step>>
        )

    predicate StateNextSeq<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>
        )
    {
        && |states| == |trace| + 1
        && (forall i {:trigger ActionTuple(states[i], states[i+1], trace[i]) in next} :: 0 <= i < |trace| ==> ActionTuple(states[i], states[i+1], trace[i]) in next)
    }

    predicate AnnotatedBehaviorSatisfiesSpec<State, Step>(
        b:AnnotatedBehavior<State, Step>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && StateNextSeq(b.states, b.trace, spec.next)
        && b.states[0] in spec.init
    }

    function AnnotatedBehaviorSpecToSpec<State(!new), Step(!new)>(spec:AnnotatedBehaviorSpec<State, Step>) : Spec<State>
    {
        Spec(spec.init,
             iset s, s', step | ActionTuple(s, s', step) in spec.next :: StatePair(s, s'))
    }

    predicate AnnotatedBehaviorSpecRefinesSpec<State(!new), Step(!new)>(
        aspec:AnnotatedBehaviorSpec<State, Step>,
        spec:Spec<State>
        )
    {
        && aspec.init <= spec.init
        && (forall s, s', step :: ActionTuple(s, s', step) in aspec.next ==> StatePair(s, s') in spec.next)
    }

    predicate SpecRefinesAnnotatedBehaviorSpec<State(!new), Step(!new)>(
        spec:Spec<State>,
        aspec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && spec.init <= aspec.init
        && (forall s, s' :: StatePair(s, s') in spec.next ==> exists step:Step :: ActionTuple(s, s', step) in aspec.next)
    }

    lemma lemma_AnnotatedBehaviorSpecEquivalentToConvertedSelf<State, Step>(spec:AnnotatedBehaviorSpec<State, Step>)
        ensures AnnotatedBehaviorSpecRefinesSpec(spec, AnnotatedBehaviorSpecToSpec(spec));
        ensures SpecRefinesAnnotatedBehaviorSpec(AnnotatedBehaviorSpecToSpec(spec), spec);
    {
    }

    lemma lemma_BehaviorInAnnotatedBehaviorSatisfiesSpec<State, Step>(
        ab:AnnotatedBehavior<State, Step>,
        aspec:AnnotatedBehaviorSpec<State, Step>,
        spec:Spec<State>
        )
        requires AnnotatedBehaviorSatisfiesSpec(ab, aspec);
        requires AnnotatedBehaviorSpecRefinesSpec(aspec, spec);
        ensures  BehaviorSatisfiesSpec(ab.states, spec);
    {
        forall i | 0 <= i < |ab.trace|
            ensures ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in aspec.next
        {
        }
    }

    lemma lemma_BehaviorInAnnotatedBehaviorSatisfiesConvertedSpec<State, Step>(
        b:AnnotatedBehavior<State, Step>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires AnnotatedBehaviorSatisfiesSpec(b, spec);
        ensures  BehaviorSatisfiesSpec(b.states, AnnotatedBehaviorSpecToSpec(spec));
    {
        lemma_AnnotatedBehaviorSpecEquivalentToConvertedSelf(spec);
        lemma_BehaviorInAnnotatedBehaviorSatisfiesSpec(b, spec, AnnotatedBehaviorSpecToSpec(spec));
    }

    lemma lemma_CreateAnnotatedBehaviorFromBehavior<State, Step>(
        b:seq<State>,
        spec:Spec<State>,
        aspec:AnnotatedBehaviorSpec<State, Step>
        ) returns (
        ab:AnnotatedBehavior<State, Step>
        )
        requires SpecRefinesAnnotatedBehaviorSpec(spec, aspec);
        requires BehaviorSatisfiesSpec(b, spec);
        ensures  ab.states == b;
        ensures  AnnotatedBehaviorSatisfiesSpec(ab, aspec);
    {
        if |b| == 1 {
            ab := AnnotatedBehavior(b, []);
        }
        else {
            var ab_prefix := lemma_CreateAnnotatedBehaviorFromBehavior(all_but_last(b), spec, aspec);
            var penult := |b|-2;
            assert StatePair(b[penult], b[penult+1]) in spec.next;
            var step :| ActionTuple(b[|b|-2], b[|b|-2+1], step) in aspec.next;
            ab := AnnotatedBehavior(b, ab_prefix.trace + [step]);
        }
    }

    lemma lemma_ExtendStateNextSeqRight<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        new_state:State,
        new_step:Step
        )
        requires StateNextSeq(states, trace, next)
        requires ActionTuple(last(states), new_state, new_step) in next
        ensures  StateNextSeq(states + [new_state], trace + [new_step], next)
    {
    }

    lemma lemma_ExtendStateNextSeqLeft<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        new_state:State,
        new_step:Step
        )
        requires StateNextSeq(states, trace, next)
        requires ActionTuple(new_state, states[0], new_step) in next
        ensures  StateNextSeq([new_state] + states, [new_step] + trace, next)
    {
        var states' := [new_state] + states;
        var trace' := [new_step] + trace;
        forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in next} | 0 <= i < |trace'|
            ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in next
        {
            if i == 0 {
                assert states'[i] == new_state;
                assert states'[i+1] == states[0];
                assert trace'[i] == new_step;
            }
            else {
                var iminus := i-1;
                assert states'[i] == states[iminus];
                assert states'[i+1] == states[iminus+1];
                assert trace'[i] == trace[iminus];
                assert ActionTuple(states[iminus], states[iminus+1], trace[iminus]) in next;
            }
        }
    }

    lemma lemma_ReduceStateNextSeqRight<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>
        )
        requires StateNextSeq(states, trace, next)
        requires |trace| > 0
        ensures  StateNextSeq(all_but_last(states), all_but_last(trace), next)
    {
    }

    lemma lemma_ReduceStateNextSeqLeft<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>
        )
        requires StateNextSeq(states, trace, next)
        requires |trace| > 0
        ensures  StateNextSeq(states[1..], trace[1..], next)
    {
        var states' := states[1..];
        var trace' := trace[1..];
        forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in next} | 0 <= i < |trace'|
            ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in next
        {
            var iplus := i+1;
            assert states'[i] == states[iplus];
            assert states'[i+1] == states[iplus+1];
            assert trace'[i] == trace[iplus];
            assert ActionTuple(states[iplus], states[iplus+1], trace[iplus]) in next;
        }
    }

    lemma lemma_ReplaceStateOnlyStateNextSeqRight<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        new_state:State
        )
        requires StateNextSeq(states, trace, next)
        requires |states| > 1
        requires ActionTuple(states[|states|-2], new_state, last(trace)) in next
        ensures  StateNextSeq(all_but_last(states) + [new_state], trace, next)
    {
    }

    lemma lemma_ReplaceStateNextSeqRight<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        new_state:State,
        new_step:Step
        )
        requires StateNextSeq(states, trace, next)
        requires |states| > 1
        requires ActionTuple(states[|states|-2], new_state, new_step) in next
        ensures  StateNextSeq(all_but_last(states) + [new_state], all_but_last(trace) + [new_step], next)
    {
    }

    lemma lemma_TakeStateNextSeq<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        pos:int
        )
        requires StateNextSeq(states, trace, next)
        requires |trace| > 0
        requires 0 <= pos <= |trace|
        ensures  StateNextSeq(states[..pos+1], trace[..pos], next)
    {
    }

    lemma lemma_DropStateNextSeq<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        next:iset<ActionTuple<State, Step>>,
        pos:int
        )
        requires StateNextSeq(states, trace, next)
        requires |trace| > 0
        requires 0 <= pos <= |trace|
        ensures  StateNextSeq(states[pos..], trace[pos..], next)
    {
        var states' := states[pos..];
        var trace' := trace[pos..];
        forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in next} | 0 <= i < |trace'|
            ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in next
        {
            var iplus := i+pos;
            lemma_IndexIntoDrop(states, pos, i);
            lemma_IndexIntoDrop(states, pos, i+1);
            lemma_IndexIntoDrop(trace, pos, i);
            assert states'[i] == states[iplus];
            assert states'[i+1] == states[iplus+1];
            assert trace'[i] == trace[iplus];
            assert ActionTuple(states[iplus], states[iplus+1], trace[iplus]) in next;
        }
    }

}
