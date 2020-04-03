include "refinement/AnnotatedBehavior.i.dfy"
include "../spec/refinement.s.dfy"

module InvariantsModule
{
    import opened util_collections_seqs_s
    import opened AnnotatedBehaviorModule
    import opened GeneralRefinementModule

    datatype StateActorPair<State, Actor> = StateActorPair(s:State, actor:Actor)

    ////////////////////////////////////////
    // INVARIANTS OF SPECS
    ////////////////////////////////////////

    function {:opaque} Reachables<State(!new)>(spec:Spec<State>) : iset<State>
    {
        iset b | BehaviorSatisfiesSpec(b, spec) :: last(b)
    }

    lemma lemma_ReachablesPremiumProperties<State>(
        spec:Spec<State>
        )
        ensures var rs := Reachables(spec);
                && (forall s {:trigger s in spec.init} {:trigger s in rs} ::
                        s in spec.init ==> s in rs)
                && (forall s, s' {:trigger s in rs, StatePair(s, s') in spec.next} ::
                        s in rs && StatePair(s, s') in spec.next ==> s' in rs)
                && (forall s' {:trigger s' in rs, s' in spec.init} ::
                        s' in rs && s' !in spec.init ==>
                        exists s :: s in rs && StatePair(s, s') in spec.next)
                && (forall b, s {:trigger BehaviorSatisfiesSpec(b, spec), s in b}{:trigger BehaviorSatisfiesSpec(b, spec),s in rs} ::
                        BehaviorSatisfiesSpec(b, spec) && s in b ==> s in rs);
    {
        reveal Reachables();
        var rs := Reachables(spec);

        forall s | s in spec.init
            ensures s in rs;
        {
            var b := [s];
            assert BehaviorSatisfiesSpec(b, spec);
        }

        forall s, s' | s in rs && StatePair(s, s') in spec.next
            ensures s' in rs;
        {
            var b :| BehaviorSatisfiesSpec(b, spec) && s == last(b);
            var b' := b + [s'];
            assert BehaviorSatisfiesSpec(b', spec);
        }

        forall s' | s' in rs && s' !in spec.init
            ensures exists s :: s in rs && StatePair(s, s') in spec.next;
        {
            var b :| BehaviorSatisfiesSpec(b, spec) && s' == last(b);
            assert |b| > 1;
            var b' := all_but_last(b);
            assert BehaviorSatisfiesSpec(b', spec);
            var s := last(b');
            var penult := |b|-2;
            assert s == b[penult];
            assert s' == b[penult+1];
            assert s in rs && StatePair(s, s') in spec.next;
        }

        forall b, s | BehaviorSatisfiesSpec(b, spec) && s in b
            ensures s in rs;
        {
            var i :| 0 <= i < |b| && s == b[i];
            var b' := b[..i+1];
            assert BehaviorSatisfiesSpec(b', spec);
            assert s == last(b');
        }
    }

    function ReachablesPremium<State(!new)>(spec:Spec<State>) : (rs:iset<State>)
        ensures rs == Reachables(spec)
        ensures (forall s {:trigger s in spec.init} {:trigger s in rs} ::
                        s in spec.init ==> s in rs);
        ensures (forall s, s' {:trigger s in rs, StatePair(s, s') in spec.next} ::
                        s in rs && StatePair(s, s') in spec.next ==> s' in rs);
        ensures (forall s' {:trigger s' in rs, s' in spec.init} ::
                        s' in rs && s' !in spec.init ==>
                        exists s :: s in rs && StatePair(s, s') in spec.next);
        ensures (forall b, s {:trigger BehaviorSatisfiesSpec(b, spec), s in b}{:trigger BehaviorSatisfiesSpec(b, spec), s in rs} ::
                        BehaviorSatisfiesSpec(b, spec) && s in b ==> s in rs);
    {
        lemma_ReachablesPremiumProperties(spec);
        Reachables(spec)
    }

    predicate IsSpecInvariant<State(==)>(
        inv:iset<State>,
        spec:Spec<State>
        )
    {
        Reachables(spec) <= inv
    }

    predicate ConditionsForSpecInvariance<State(==, !new)>(
        inv:iset<State>,
        spec:Spec<State>
        )
    {
        && (forall s :: s in spec.init ==> s in inv)
        && (forall s, s' :: s in inv && StatePair(s, s') in spec.next ==> s' in inv)
    }

    predicate ConditionsForSpecInvarianceDeduction<State(==, !new)>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:Spec<State>
        )
    {
        && (forall s :: s in spec.init ==> s in inv_unknown)
        && (forall s, s' :: && s in inv_known
                      && s in inv_unknown
                      && StatePair(s, s') in spec.next
                      ==> s' in inv_unknown)
    }

    predicate ConditionsForSpecInvarianceDeductionBeforeAndAfter<State(==)>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:Spec<State>
        )
    {
        && (forall s :: s in spec.init ==> s in inv_unknown)
        && (forall s, s' :: && s in inv_known
                      && s' in inv_known
                      && s in inv_unknown
                      && StatePair(s, s') in spec.next
                      ==> s' in inv_unknown)
    }

    function ExtendSpecWithInvariant<State(==, !new)>(spec:Spec<State>, inv:iset<State>) : Spec<State>
    {
        Spec(spec.init, iset s, s' | StatePair(s, s') in spec.next && s in inv :: StatePair(s, s'))
    }

    lemma lemma_EstablishSpecInvariantPure<State(==)>(
        inv:iset<State>,
        spec:Spec<State>
        )
        requires ConditionsForSpecInvariance(inv, spec)
        ensures  IsSpecInvariant(inv, spec)
    {
        var rs := Reachables(spec);
        reveal Reachables();

        forall r | r in rs
            ensures r in inv;
        {
            var b :| BehaviorSatisfiesSpec(b, spec) && last(b) == r;
            assert b[0] in spec.init;
            var i := 0;
            while i < |b|-1
                invariant 0 <= i < |b|;
                invariant b[i] in inv;
            {
                assert b[i] in inv;
                assert StatePair(b[i], b[i+1]) in spec.next;
                assert b[i+1] in inv;
                i := i + 1;
            }
            assert i == |b|-1;
            assert b[i] == r;
        }
    }

    lemma lemma_EstablishSpecInvariantUsingInvariant<State>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:Spec<State>
        )
        requires IsSpecInvariant(inv_known, spec)
        requires ConditionsForSpecInvarianceDeduction(inv_unknown, inv_known, spec)
        ensures  IsSpecInvariant(inv_unknown, spec)
    {
        var rs := Reachables(spec);
        reveal Reachables();

        forall r | r in rs
            ensures r in inv_unknown;
        {
            var b :| BehaviorSatisfiesSpec(b, spec) && last(b) == r;
            var i := 0;
            while i < |b|-1
                invariant 0 <= i < |b|;
                invariant b[i] in inv_unknown;
            {
                assert BehaviorSatisfiesSpec(b[..i+1], spec);
                assert StatePair(b[i], b[i+1]) in spec.next;
                i := i + 1;
            }
            assert i == |b|-1;
            assert b[i] == r;
        }
    }

    lemma lemma_EstablishSpecInvariantUsingInvariantBeforeAndAfter<State>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:Spec<State>
        )
        requires IsSpecInvariant(inv_known, spec)
        requires ConditionsForSpecInvarianceDeductionBeforeAndAfter(inv_unknown, inv_known, spec)
        ensures  IsSpecInvariant(inv_unknown, spec)
    {
        var rs := Reachables(spec);
        reveal Reachables();

        forall r | r in rs
            ensures r in inv_unknown;
        {
            var b :| BehaviorSatisfiesSpec(b, spec) && last(b) == r;
            var i := 0;
            while i < |b|-1
                invariant 0 <= i < |b|;
                invariant b[i] in inv_unknown;
            {
                assert BehaviorSatisfiesSpec(b[..i+1], spec);
                assert BehaviorSatisfiesSpec(b[..i+1+1], spec);
                assert StatePair(b[i], b[i+1]) in spec.next;
                i := i + 1;
            }
            assert i == |b|-1;
            assert b[i] == r;
        }
    }

    lemma lemma_SpecInvariantHoldsAtStart<State(==)>(
        s:State,
        spec:Spec<State>,
        inv:iset<State>
        )
        requires s in spec.init
        requires IsSpecInvariant(inv, spec)
        ensures  s in inv
    {
        var rs := ReachablesPremium(spec);
    }

    lemma lemma_SpecInvariantHoldsAtStep<State(==)>(
        b:seq<State>,
        t:int,
        spec:Spec<State>,
        inv:iset<State>
        )
        requires BehaviorSatisfiesSpec(b, spec)
        requires 0 <= t < |b|
        requires IsSpecInvariant(inv, spec)
        ensures  b[t] in inv
    {
        reveal Reachables();
        var b' := b[..t+1];
        assert BehaviorSatisfiesSpec(b', spec);
    }

    lemma lemma_ReachablesSatisfyConditionsForSpecInvariance<State(==)>(
        spec:Spec<State>
        )
        ensures ConditionsForSpecInvariance(Reachables(spec), spec);
    {
        var rs := ReachablesPremium(spec);
    }

    lemma lemma_ExtendingSpecWithInvariantProducesEquivalentSpec<State(==)>(
        spec:Spec<State>,
        inv:iset<State>,
        b:seq<State>
        )
        requires IsSpecInvariant(inv, spec)
        ensures  BehaviorSatisfiesSpec(b, spec) <==> BehaviorSatisfiesSpec(b, ExtendSpecWithInvariant(spec, inv))
    {
        var espec := ExtendSpecWithInvariant(spec, inv);

        if BehaviorSatisfiesSpec(b, spec) {
            lemma_ReachablesPremiumProperties(spec);
            assert BehaviorSatisfiesSpec(b, espec);
        }

        if BehaviorSatisfiesSpec(b, espec) {
            forall i | 0 <= i < |b|-1
                ensures StatePair(b[i], b[i+1]) in espec.next
            {
            }
            assert BehaviorSatisfiesSpec(b, spec);
        }
    }

    ////////////////////////////////////////
    // INVARIANTS OF ANNOTATED SPECS
    ////////////////////////////////////////

    function {:opaque} AnnotatedReachables<State(!new), Step(!new)>(spec:AnnotatedBehaviorSpec<State, Step>) : iset<State>
    {
        iset ab | AnnotatedBehaviorSatisfiesSpec(ab, spec) :: last(ab.states)
    }

    lemma lemma_AnnotatedReachablesPremiumProperties<State, Step>(
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        ensures var rs := AnnotatedReachables(spec);
                && (forall s {:trigger s in spec.init} {:trigger s in rs} ::
                        s in spec.init ==> s in rs)
                && (forall s, s', step {:trigger s in rs, ActionTuple(s, s', step) in spec.next} ::
                        s in rs && ActionTuple(s, s', step) in spec.next ==> s' in rs)
                && (forall s' {:trigger s' in rs, s' in spec.init} ::
                        s' in rs && s' !in spec.init ==>
                        exists s, step :: s in rs && ActionTuple(s, s', step) in spec.next)
                && (forall ab, s {:trigger AnnotatedBehaviorSatisfiesSpec(ab, spec), s in ab.states}
				                 {:trigger AnnotatedBehaviorSatisfiesSpec(ab, spec), s in rs} ::
                        AnnotatedBehaviorSatisfiesSpec(ab, spec) && s in ab.states ==> s in rs);
    {
        reveal AnnotatedReachables();
        var rs := AnnotatedReachables(spec);

        forall s | s in spec.init
            ensures s in rs;
        {
            var ab := AnnotatedBehavior([s], []);
            assert AnnotatedBehaviorSatisfiesSpec(ab, spec);
        }

        forall s, s', step | s in rs && ActionTuple(s, s', step) in spec.next
            ensures s' in rs;
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && s == last(ab.states);
            var ab' := AnnotatedBehavior(ab.states + [s'], ab.trace + [step]);
            assert AnnotatedBehaviorSatisfiesSpec(ab', spec);
        }

        forall s' | s' in rs && s' !in spec.init
            ensures exists s, step :: s in rs && ActionTuple(s, s', step) in spec.next;
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && s' == last(ab.states);
            assert |ab.states| > 1;
            var ab' := AnnotatedBehavior(all_but_last(ab.states), all_but_last(ab.trace));
            assert AnnotatedBehaviorSatisfiesSpec(ab', spec);
            var s := last(ab'.states);
            var penult := |ab.states|-2;
            var step := ab.trace[penult];
            assert s == ab.states[penult];
            assert s' == ab.states[penult+1];
            assert s in rs && ActionTuple(s, s', step) in spec.next;
        }

        forall ab, s | AnnotatedBehaviorSatisfiesSpec(ab, spec) && s in ab.states
            ensures s in rs;
        {
            var i :| 0 <= i < |ab.states| && s == ab.states[i];
            var ab' := AnnotatedBehavior(ab.states[..i+1], ab.trace[..i]);
            assert AnnotatedBehaviorSatisfiesSpec(ab', spec);
            assert s == last(ab'.states);
        }
    }

    function AnnotatedReachablesPremium<State(!new), Step(!new)>(
        spec:AnnotatedBehaviorSpec<State, Step>
        ) : (rs:iset<State>)
        ensures rs == AnnotatedReachables(spec)
        ensures forall s {:trigger s in spec.init} {:trigger s in rs} ::
                        s in spec.init ==> s in rs;
        ensures forall s, s', step {:trigger s in rs, ActionTuple(s, s', step) in spec.next} ::
                        s in rs && ActionTuple(s, s', step) in spec.next ==> s' in rs;
        ensures forall s' {:trigger s' in rs, s' in spec.init} ::
                        s' in rs && !(s' in spec.init) ==>
                        exists s, step :: s in rs && ActionTuple(s, s', step) in spec.next;
        ensures forall ab, s {:trigger AnnotatedBehaviorSatisfiesSpec(ab, spec), s in ab.states}
                             {:trigger AnnotatedBehaviorSatisfiesSpec(ab, spec), s in rs} ::
                        AnnotatedBehaviorSatisfiesSpec(ab, spec) && s in ab.states ==> s in rs;
    {
        lemma_AnnotatedReachablesPremiumProperties(spec);
        AnnotatedReachables(spec)
    }

    lemma lemma_InitStateInAnnotatedReachables<State, Step>(
        s:State,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires s in spec.init
        ensures  s in AnnotatedReachables(spec)
    {
        assert AnnotatedReachables(spec) == AnnotatedReachablesPremium(spec);
    }

    lemma lemma_NextMaintainsAnnotatedReachables<State, Step>(
        s:State,
        s':State,
        step:Step,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires s in AnnotatedReachables(spec)
        requires ActionTuple(s, s', step) in spec.next
        ensures  s' in AnnotatedReachables(spec)
    {
        assert AnnotatedReachables(spec) == AnnotatedReachablesPremium(spec);
    }

    lemma lemma_StateNextSeqMaintainsAnnotatedReachables<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires StateNextSeq(states, trace, spec.next)
        requires states[0] in AnnotatedReachables(spec)
        ensures  forall s :: s in states ==> s in AnnotatedReachables(spec)
    {
        var pos := 0;
        while pos < |states|-1
            invariant 0 <= pos < |states|
            invariant forall i :: 0 <= i <= pos ==> states[i] in AnnotatedReachables(spec)
        {
            assert states[pos] in AnnotatedReachables(spec);
            lemma_NextMaintainsAnnotatedReachables(states[pos], states[pos+1], trace[pos], spec);
            pos := pos + 1;
        }
    }

    predicate IsInvariantOfSpec<State(==), Step>(
        inv:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        AnnotatedReachables(spec) <= inv
    }

    predicate ConditionsForInvariance<State(==, !new), Step(!new)>(
        inv:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> s in inv)
        && (forall s, s', step :: s in inv && ActionTuple(s, s', step) in spec.next ==> s' in inv)
    }

    predicate ConditionsForInvarianceDeduction<State(==, !new), Step(!new)>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> s in inv_unknown)
        && (forall s, s', step :: && s in inv_known
                                   && s in inv_unknown
                                   && ActionTuple(s, s', step) in spec.next
                                   ==> s' in inv_unknown)
    }

    predicate ConditionsForInvarianceDeductionBeforeAndAfter<State(==, !new), Step(!new)>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> s in inv_unknown)
        && (forall s, s', step :: && s in inv_known
                                   && s' in inv_known
                                   && s in inv_unknown
                                   && ActionTuple(s, s', step) in spec.next
                                   ==> s' in inv_unknown)
    }

    function ExtendAnnotatedBehaviorSpecWithInvariant<State(==, !new), Step(!new)>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:iset<State>
        ) : AnnotatedBehaviorSpec<State, Step>
    {
        AnnotatedBehaviorSpec(spec.init,
                              iset s, s', step | ActionTuple(s, s', step) in spec.next && s in inv
                                                      :: ActionTuple(s, s', step))
    }

    lemma lemma_EstablishInvariantPure<State(==), Step>(
        inv:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires ConditionsForInvariance(inv, spec)
        ensures  IsInvariantOfSpec(inv, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures r in inv;
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            assert ab.states[0] in spec.init;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|;
                invariant ab.states[i] in inv;
            {
                assert ab.states[i] in inv;
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                assert ab.states[i+1] in inv;
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_EstablishInvariantUsingInvariant<State(==), Step>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires IsInvariantOfSpec(inv_known, spec)
        requires ConditionsForInvarianceDeduction(inv_unknown, inv_known, spec)
        ensures  IsInvariantOfSpec(inv_unknown, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures r in inv_unknown;
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|;
                invariant ab.states[i] in inv_unknown;
            {
                assert AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(ab.states[..i+1], ab.trace[..i]), spec);
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_EstablishInvariantUsingInvariantBeforeAndAfter<State(==), Step>(
        inv_unknown:iset<State>,
        inv_known:iset<State>,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires IsInvariantOfSpec(inv_known, spec)
        requires ConditionsForInvarianceDeductionBeforeAndAfter(inv_unknown, inv_known, spec)
        ensures  IsInvariantOfSpec(inv_unknown, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures r in inv_unknown;
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|;
                invariant ab.states[i] in inv_unknown;
            {
                assert AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(ab.states[..i+1], ab.trace[..i]), spec);
                assert AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(ab.states[..i+1+1], ab.trace[..i+1]), spec);
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_InvariantHoldsAtStart<State(==), Step>(
        s:State,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:iset<State>
        )
        requires s in spec.init
        requires IsInvariantOfSpec(inv, spec)
        ensures  s in inv
    {
        var rs := AnnotatedReachablesPremium(spec);
    }

    lemma lemma_InvariantHoldsAtStep<State(==), Step>(
        ab:AnnotatedBehavior<State, Step>,
        t:int,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:iset<State>
        )
        requires AnnotatedBehaviorSatisfiesSpec(ab, spec)
        requires 0 <= t < |ab.states|
        requires IsInvariantOfSpec(inv, spec)
        ensures  ab.states[t] in inv
    {
        reveal AnnotatedReachables();
        var ab' := AnnotatedBehavior(ab.states[..t+1], ab.trace[..t]);
        assert AnnotatedBehaviorSatisfiesSpec(ab', spec);
    }

    lemma lemma_AnnotatedReachablesSatisfyConditionsForInvariance<State(==), Step>(
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        ensures ConditionsForInvariance(AnnotatedReachables(spec), spec);
    {
        var rs := AnnotatedReachablesPremium(spec);
    }

    lemma lemma_ConditionsForInvarianceTransferAcrossStateNextSeq<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:iset<State>
        )
        requires ConditionsForInvariance(inv, spec)
        requires StateNextSeq(states, trace, spec.next)
        requires states[0] in inv
        ensures  forall s :: s in states ==> s in inv
    {
        var j := 1;
        while j < |states|
            invariant 0 <= j <= |states|;
            invariant forall i :: 0 <= i < j ==> states[i] in inv;
        {
            var prev := j-1;
            assert ActionTuple(states[prev], states[prev+1], trace[prev]) in spec.next;
            j := j + 1;
        }
    }

    lemma lemma_ConjunctionOfInvariantsIsInvariant<State, Step>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        invs:seq<State->bool>,
        aggregate_inv:State->bool
        )
        requires forall inv :: inv in invs ==> IsInvariantPredicateOfSpec(inv, spec)
        requires forall s :: (forall inv :: inv in invs ==> inv(s)) ==> aggregate_inv(s)
        ensures  IsInvariantPredicateOfSpec(aggregate_inv, spec)
    {
    }

    lemma lemma_ExtendingAnnotatedSpecWithInvariantProducesEquivalentSpec<State(==), Step>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:iset<State>,
        ab:AnnotatedBehavior<State, Step>
        )
        requires IsInvariantOfSpec(inv, spec)
        ensures  AnnotatedBehaviorSatisfiesSpec(ab, spec) <==>
                 AnnotatedBehaviorSatisfiesSpec(ab, ExtendAnnotatedBehaviorSpecWithInvariant(spec, inv))
    {
        var espec := ExtendAnnotatedBehaviorSpecWithInvariant(spec, inv);

        if AnnotatedBehaviorSatisfiesSpec(ab, spec) {
            lemma_AnnotatedReachablesPremiumProperties(spec);
            assert AnnotatedBehaviorSatisfiesSpec(ab, espec);
        }

        if AnnotatedBehaviorSatisfiesSpec(ab, espec) {
            forall i | 0 <= i < |ab.trace|
                ensures ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in espec.next
            {
            }
            assert AnnotatedBehaviorSatisfiesSpec(ab, spec);
        }
    }

    predicate IsInvariantPredicateOfSpec<State(==), Step>(
        inv:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        forall s :: s in AnnotatedReachables(spec) ==> inv(s)
    }

    predicate ConditionsForInvariancePredicate<State(==, !new), Step(!new)>(
        inv:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> inv(s))
        && (forall s, s', step :: inv(s) && ActionTuple(s, s', step) in spec.next ==> inv(s'))
    }

    predicate ConditionsForInvariancePredicateDeduction<State(==, !new), Step(!new)>(
        inv_unknown:State->bool,
        inv_known:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> inv_unknown(s))
        && (forall s, s', step :: && inv_known(s)
                                   && inv_unknown(s)
                                   && ActionTuple(s, s', step) in spec.next
                                   ==> inv_unknown(s'))
    }

    predicate ConditionsForInvariancePredicateDeductionBeforeAndAfter<State(==, !new), Step(!new)>(
        inv_unknown:State->bool,
        inv_known:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
    {
        && (forall s :: s in spec.init ==> inv_unknown(s))
        && (forall s, s', step :: && inv_known(s)
                                   && inv_known(s')
                                   && inv_unknown(s)
                                   && ActionTuple(s, s', step) in spec.next
                                   ==> inv_unknown(s'))
    }

    function ExtendAnnotatedBehaviorSpecWithInvariantPredicate<State(==, !new), Step(!new)>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:State->bool
        ) : AnnotatedBehaviorSpec<State, Step>
    {
        AnnotatedBehaviorSpec(spec.init,
                              iset s, s', step | ActionTuple(s, s', step) in spec.next && inv(s) :: ActionTuple(s, s', step))
    }

    lemma lemma_EstablishInvariantPredicatePure<State(==), Step>(
        inv:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires ConditionsForInvariancePredicate(inv, spec)
        ensures  IsInvariantPredicateOfSpec(inv, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures inv(r);
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            assert ab.states[0] in spec.init;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|;
                invariant inv(ab.states[i]);
            {
                assert inv(ab.states[i]);
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                assert inv(ab.states[i+1]);
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_EstablishInvariantPredicateUsingInvariantPredicate<State(==), Step>(
        inv_unknown:State->bool,
        inv_known:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires IsInvariantPredicateOfSpec(inv_known, spec)
        requires ConditionsForInvariancePredicateDeduction(inv_unknown, inv_known, spec)
        ensures  IsInvariantPredicateOfSpec(inv_unknown, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures inv_unknown(r);
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|
                invariant inv_unknown(ab.states[i])
            {
                lemma_InvariantPredicateHoldsAtStep(ab, i, spec, inv_known);
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                assert inv_unknown(ab.states[i+1]);
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_EstablishInvariantPredicateUsingInvariantPredicateBeforeAndAfter<State(==), Step>(
        inv_unknown:State->bool,
        inv_known:State->bool,
        spec:AnnotatedBehaviorSpec<State, Step>
        )
        requires IsInvariantPredicateOfSpec(inv_known, spec)
        requires ConditionsForInvariancePredicateDeductionBeforeAndAfter(inv_unknown, inv_known, spec)
        ensures  IsInvariantPredicateOfSpec(inv_unknown, spec)
    {
        var rs := AnnotatedReachables(spec);
        reveal AnnotatedReachables();

        forall r | r in rs
            ensures inv_unknown(r);
        {
            var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == r;
            var i := 0;
            while i < |ab.states|-1
                invariant 0 <= i < |ab.states|
                invariant inv_unknown(ab.states[i])
            {
                assert AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(ab.states[..i+1], ab.trace[..i]), spec);
                assert AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(ab.states[..i+1+1], ab.trace[..i+1]), spec);
                assert ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in spec.next;
                i := i + 1;
            }
            assert i == |ab.states|-1;
            assert ab.states[i] == r;
        }
    }

    lemma lemma_InvariantPredicateHoldsAtStart<State(==), Step>(
        s:State,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:State->bool
        )
        requires s in spec.init
        requires IsInvariantPredicateOfSpec(inv, spec)
        ensures  inv(s)
    {
        var rs := AnnotatedReachablesPremium(spec);
    }

    lemma lemma_InvariantPredicateHoldsAtStep<State(==), Step>(
        ab:AnnotatedBehavior<State, Step>,
        t:int,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:State->bool
        )
        requires AnnotatedBehaviorSatisfiesSpec(ab, spec)
        requires 0 <= t < |ab.states|
        requires IsInvariantPredicateOfSpec(inv, spec)
        ensures  inv(ab.states[t])
    {
        reveal AnnotatedReachables();
        var ab' := AnnotatedBehavior(ab.states[..t+1], ab.trace[..t]);
        assert AnnotatedBehaviorSatisfiesSpec(ab', spec);
    }

    lemma lemma_ConditionsForInvariancePredicateTransferAcrossStateNextSeq<State, Step>(
        states:seq<State>,
        trace:seq<Step>,
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:State->bool
        )
        requires ConditionsForInvariancePredicate(inv, spec)
        requires StateNextSeq(states, trace, spec.next)
        requires inv(states[0])
        ensures  forall s :: s in states ==> inv(s)
    {
        var j := 1;
        while j < |states|
            invariant 0 <= j <= |states|;
            invariant forall i :: 0 <= i < j ==> inv(states[i])
        {
            var prev := j-1;
            assert ActionTuple(states[prev], states[prev+1], trace[prev]) in spec.next;
            j := j + 1;
        }
    }

    lemma lemma_ExtendingAnnotatedSpecWithInvariantPredicateProducesEquivalentSpec<State(==), Step>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        inv:State->bool,
        ab:AnnotatedBehavior<State, Step>
        )
        requires IsInvariantPredicateOfSpec(inv, spec)
        ensures  AnnotatedBehaviorSatisfiesSpec(ab, spec) <==>
                 AnnotatedBehaviorSatisfiesSpec(ab, ExtendAnnotatedBehaviorSpecWithInvariantPredicate(spec, inv))
    {
        var espec := ExtendAnnotatedBehaviorSpecWithInvariantPredicate(spec, inv);

        if AnnotatedBehaviorSatisfiesSpec(ab, spec) {
            lemma_AnnotatedReachablesPremiumProperties(spec);
            assert AnnotatedBehaviorSatisfiesSpec(ab, espec);
        }

        if AnnotatedBehaviorSatisfiesSpec(ab, espec) {
            forall i | 0 <= i < |ab.trace|
                ensures ActionTuple(ab.states[i], ab.states[i+1], ab.trace[i]) in espec.next
            {
            }
            assert AnnotatedBehaviorSatisfiesSpec(ab, spec);
        }
    }

    lemma lemma_StateInAnnotatedBehaviorInAnnotatedReachables<State, Step>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        ab:AnnotatedBehavior<State, Step>,
        pos:int
        )
        requires AnnotatedBehaviorSatisfiesSpec(ab, spec)
        requires 0 <= pos < |ab.states|
        ensures  ab.states[pos] in AnnotatedReachables(spec)
    {
        assert AnnotatedReachables(spec) == AnnotatedReachablesPremium(spec);
        lemma_StateNextSeqMaintainsAnnotatedReachables(ab.states, ab.trace, spec);
        assert ab.states[pos] in ab.states;
    }

}
