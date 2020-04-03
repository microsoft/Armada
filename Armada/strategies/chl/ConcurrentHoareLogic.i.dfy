include "ConcurrentHoareLogicLemmas2.i.dfy"

module ConcurrentHoareLogicModule {

    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened ConcurrentHoareLogicSpecModule
    import opened ConcurrentHoareLogicLemmasModule
    import opened ConcurrentHoareLogicLemmas2Module
    import opened util_collections_seqs_s

    lemma lemma_CHLGlobalInvariantHoldsAtStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 <= pos < |b.states|
        ensures  cr.global_inv(b.states[pos])
    {
        if pos == 0 {
            return;
        }

        var prev := pos-1;
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

        if forall any_actor :: any_actor !in cr.actor_info(b.states[pos]) {
            // If *no* actor is present in this position, then we only care about the global invariant.
            // Use the StraightlineSpecPreservesGlobalInvariantOnTermination property to prove it.
            // That property states that, if we get rid of all actors (i.e., terminate the process)
            // in some step, we maintain the global invariant in that step.

            lemma_CHLGlobalInvariantHoldsAtStep(cr, b, pos-1);
            lemma_InvariantPredicateHoldsAtStep(b, pos-1, cr.spec, cr.established_inv);
        }
        else {
            // If the actor isn't present, all we care about is the global invariant.
            // Use any actor that happens to still be present to establish it.

            var actor :| actor in cr.actor_info(b.states[pos]);
            var pc := cr.actor_info(b.states[pos])[actor].pc;
            var proc := cr.pc_to_proc(pc);
            var overlay := lemma_GetStraightlineBehavior(cr, b, pos, actor, proc);
            lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay, |overlay.positions|-1);
        }
    }

    lemma lemma_CHLLocalInvariantHoldsAtStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 <= pos < |b.states|
        requires actor in cr.actor_info(b.states[pos])
        ensures  cr.local_inv(b.states[pos], actor)
    {
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);

        if pos == 0 {
            return;
        }

        var prev := pos-1;
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

        var pc := cr.actor_info(b.states[pos])[actor].pc;
        var proc := cr.pc_to_proc(pc);
        var overlay := lemma_GetStraightlineBehavior(cr, b, pos, actor, proc);
        assert cr.local_inv(last(overlay.sb.states).state, actor);
        assert last(overlay.sb.states).state == b.states[pos];
    }

    lemma lemma_CHLEnablementConditionHoldsAtStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 <= pos < |b.trace|
        requires cr.idmap(b.trace[pos]).Some?
        requires cr.idmap(b.trace[pos]).v == actor
        ensures  cr.enablement_condition(b.states[pos], actor)
    {
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);

        assert ActionTuple(b.states[pos], b.states[pos+1], b.trace[pos]) in cr.spec.next;

        var pc := cr.actor_info(b.states[pos])[actor].pc;
        var proc := cr.pc_to_proc(pc);
        var overlay := lemma_GetStraightlineBehavior(cr, b, pos, actor, proc);
        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay, |overlay.positions|-1);
    }

    lemma lemma_AllCHLInvariantsHoldAtStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 <= pos < |b.states|
        ensures  cr.established_inv(b.states[pos])
        ensures  cr.global_inv(b.states[pos])
        ensures  actor in cr.actor_info(b.states[pos]) ==> cr.local_inv(b.states[pos], actor)
        ensures  pos < |b.trace| && cr.idmap(b.trace[pos]).Some? && cr.idmap(b.trace[pos]).v == actor ==> cr.enablement_condition(b.states[pos], actor)
    {
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
        lemma_CHLGlobalInvariantHoldsAtStep(cr, b, pos);
        if actor in cr.actor_info(b.states[pos]) {
            lemma_CHLLocalInvariantHoldsAtStep(cr, b, pos, actor);
        }
        if pos < |b.trace| && cr.idmap(b.trace[pos]).Some? && cr.idmap(b.trace[pos]).v == actor {
            lemma_CHLEnablementConditionHoldsAtStep(cr, b, pos, actor);
        }
    }

    lemma lemma_CHLGlobalInvariantAlwaysSatisfied<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        ensures  forall pos :: 0 <= pos < |b.states| ==> cr.global_inv(b.states[pos])
    {
        forall pos | 0 <= pos < |b.states|
            ensures cr.global_inv(b.states[pos])
        {
            lemma_CHLGlobalInvariantHoldsAtStep(cr, b, pos);
        }
    }

    lemma lemma_CHLLocalInvariantAlwaysSatisfied<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        ensures  forall pos, actor {:trigger actor in cr.actor_info(b.states[pos])} ::
                    (&& 0 <= pos < |b.states|
                     && actor in cr.actor_info(b.states[pos]))
                    ==> cr.local_inv(b.states[pos], actor)
    {
        forall pos, actor |
            && 0 <= pos < |b.states|
            && actor in cr.actor_info(b.states[pos])
            ensures cr.local_inv(b.states[pos], actor)
        {
            lemma_CHLLocalInvariantHoldsAtStep(cr, b, pos, actor);
        }
    }

    lemma lemma_CHLEnablementConditionAlwaysSatisfied<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        ensures  forall pos, actor :: 0 <= pos < |b.trace| && cr.idmap(b.trace[pos]).Some? && cr.idmap(b.trace[pos]).v == actor
                                ==> cr.enablement_condition(b.states[pos], actor)
    {
        forall pos, actor | 0 <= pos < |b.trace| && cr.idmap(b.trace[pos]).Some? && cr.idmap(b.trace[pos]).v == actor
            ensures cr.enablement_condition(b.states[pos], actor)
        {
            lemma_CHLEnablementConditionHoldsAtStep(cr, b, pos, actor);
        }
    }

    lemma lemma_CHLAllInvariantsAlwaysSatisfied<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        ensures  forall pos, actor {:trigger actor in cr.actor_info(b.states[pos])} ::
                    (&& 0 <= pos < |b.states|
                     && actor in cr.actor_info(b.states[pos]))
                    ==> cr.local_inv(b.states[pos], actor)
        ensures  forall pos :: 0 <= pos < |b.states| ==> cr.established_inv(b.states[pos]) && cr.global_inv(b.states[pos])
    {
        forall pos |
            && 0 <= pos < |b.states|
            ensures cr.established_inv(b.states[pos])
            ensures cr.global_inv(b.states[pos])
        {
            lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
            lemma_CHLGlobalInvariantHoldsAtStep(cr, b, pos);
        }

        forall pos, actor |
            && 0 <= pos < |b.states|
            && actor in cr.actor_info(b.states[pos])
            ensures cr.local_inv(b.states[pos], actor)
        {
            lemma_CHLLocalInvariantHoldsAtStep(cr, b, pos, actor);
        }
    }

}
