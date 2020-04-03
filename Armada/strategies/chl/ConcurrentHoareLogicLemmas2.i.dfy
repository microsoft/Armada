include "ConcurrentHoareLogicLemmas.i.dfy"

module ConcurrentHoareLogicLemmas2Module {

    import opened ConcurrentHoareLogicSpecModule
    import opened util_collections_maps_s
    import opened util_collections_seqs_s
    import opened util_option_s
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened ConcurrentHoareLogicLemmasModule

    lemma lemma_GetStraightlineBehaviorCaseBehaviorStart<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires actor in cr.actor_info(b.states[0])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[0])[actor].pc)
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == 0
    {
        var positions := [0, 0];
        var s := b.states[0];

        var state0 := StraightlineState(s, map [], false);
        var state1 := StraightlineState(s, map [], true);
        var sstep := StraightlineStepStart();
        var sb := AnnotatedBehavior([state0, state1], [sstep]);
        lemma_InvariantPredicateHoldsAtStart(s, cr.spec, cr.established_inv);

        assert StraightlineSpecInit(cr, sb.states[0], actor, proc);

        overlay := StraightlineOverlay(sb, [0, 0]);

        lemma_EstablishPreviousStepIsCallOrForkViaStart(cr, b, actor, 0);
    }

    lemma lemma_GetStraightlineBehaviorCaseForkHelper<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos])
        requires actor !in cr.actor_info(b.states[pos-1])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v != actor
        ensures  cr.global_inv(b.states[pos])
        ensures  cr.requires_clauses(proc, b.states[pos], actor)
        decreases pos, 0
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var pc' := cr.actor_info(s')[actor].pc;
        var forker_actor := cr.idmap(step).v;
        var forker_pc := cr.actor_info(s)[forker_actor].pc;
        var forker_proc := cr.pc_to_proc(forker_pc);
        var forker_overlay := lemma_GetStraightlineBehavior(cr, b, pos-1, forker_actor, forker_proc);
        var forker_overlay_extended := lemma_ExtendOverlayWithStatement(cr, b, pos, forker_actor, forker_proc, forker_overlay);
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
        var forker_state := last(forker_overlay_extended.sb.states).state;
        assert cr.established_inv(forker_state) && cr.global_inv(forker_state) && cr.local_inv(forker_state, forker_actor);
        assert cr.global_inv(b.states[pos]);

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, forker_actor, forker_proc, forker_overlay, |forker_overlay.sb.states|-1);

        var myb := forker_overlay.sb;
        assert AnnotatedBehaviorSatisfiesSpec(myb, GetStraightlineSpec(cr, forker_actor, forker_proc));
        assert last(myb.states).started;
        assert s == last(myb.states).state;
        assert ActionTuple(s, s', step) in cr.spec.next;
        assert cr.idmap(step).v == forker_actor;
        assert forker_actor in cr.actor_info(s);
        assert forker_actor in cr.actor_info(s');
        assert actor !in cr.actor_info(s);
        assert actor in cr.actor_info(s');
        assert cr.pc_type(forker_pc).ForkSite?;
        assert StraightlineSpecSatisfiesPreconditionsForForks(cr);
        assert pc' == cr.actor_info(s')[actor].pc;
        assert proc == cr.pc_to_proc(pc');
        assert cr.requires_clauses(proc, s', actor);
    }

    lemma lemma_GetStraightlineBehaviorCaseFork<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos])
        requires actor !in cr.actor_info(b.states[pos-1])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v != actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        lemma_GetStraightlineBehaviorCaseForkHelper(cr, b, pos, actor, proc);

        var state0 := StraightlineState(s', map [], false);
        var state1 := StraightlineState(s', map [], true);
        var sstep := StraightlineStepStart();

        overlay := StraightlineOverlay(AnnotatedBehavior([state0, state1], [sstep]), [pos, pos]);
        lemma_InvariantPredicateHoldsAtStep(b, pos-1, cr.spec, cr.established_inv);
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);

        lemma_EstablishPreviousStepIsCallOrForkViaFork(cr, b, actor, pos);
        assert StraightlineSpecInit(cr, state0, actor, proc);
        assert StraightlineSpecNextStart(cr, state0, state1, actor, proc);
        assert StraightlineOverlayValid(cr, overlay, b, actor, proc);
    }

    lemma lemma_GetStraightlineBehaviorCaseOtherActorStepHelper1<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        other_actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == other_actor
        requires other_actor != actor
        requires other_actor in cr.actor_info(b.states[pos-1])
        ensures  cr.yield_pred(b.states[pos-1], b.states[pos], actor)
        ensures  cr.actor_info(b.states[pos-1])[actor] == cr.actor_info(b.states[pos])[actor]
        ensures  cr.established_inv(b.states[pos])
        ensures  cr.global_inv(b.states[pos])
        decreases pos, 0
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var other_pc := cr.actor_info(s)[other_actor].pc;
        var other_proc := cr.pc_to_proc(other_pc);

        var overlay_other := lemma_GetStraightlineBehavior(cr, b, pos-1, other_actor, other_proc);
        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, other_actor, other_proc, overlay_other, |overlay_other.sb.states|-1);

        assert cr.yield_pred(last(overlay_other.sb.states).state, s', actor);
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    }

    lemma lemma_GetStraightlineBehaviorCaseOtherActorStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v != actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var other_actor := cr.idmap(step).v;
        var other_pc := cr.actor_info(s)[other_actor].pc;
        var other_proc := cr.pc_to_proc(other_pc);

        lemma_GetStraightlineBehaviorCaseOtherActorStepHelper1(cr, b, pos, actor, other_actor);

        var overlay_prev := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, proc);

        var num_states := |overlay_prev.sb.states|;
        var states := overlay_prev.sb.states[num_states-1 :=
                          StraightlineState(b.states[pos], last(overlay_prev.sb.states).visited_loops, true)];
        var positions := overlay_prev.positions[num_states-1 := pos];
        overlay := StraightlineOverlay(AnnotatedBehavior(states, overlay_prev.sb.trace), positions);

        lemma_GetStraightlineBehaviorCaseNoOrOtherActorStepHelper2(cr, b, pos, actor, proc, overlay_prev, overlay.sb);
    }

    lemma lemma_GetStraightlineBehaviorCaseNoActorStepHelper1<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires cr.idmap(b.trace[pos-1]).None?
        requires cr.established_inv(b.states[pos-1])
        requires cr.global_inv(b.states[pos-1])
        requires cr.local_inv(b.states[pos-1], actor)
        ensures  cr.yield_pred(b.states[pos-1], b.states[pos], actor)
        ensures  cr.actor_info(b.states[pos-1])[actor] == cr.actor_info(b.states[pos])[actor]
        ensures  cr.established_inv(b.states[pos])
        ensures  cr.global_inv(b.states[pos])
        decreases pos, 0
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        assert ActorlessActionsMaintainYieldPredicateAndGlobalInvariant(cr);
        assert cr.yield_pred(s, s', actor);
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    }

    lemma lemma_GetStraightlineBehaviorCaseNoOrOtherActorStepHelper2<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>,
        sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<State, Step>>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]) != Some(actor)
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires cr.yield_pred(b.states[pos-1], b.states[pos], actor)
        requires cr.actor_info(b.states[pos-1])[actor] == cr.actor_info(b.states[pos])[actor]
        requires cr.established_inv(b.states[pos])
        requires cr.global_inv(b.states[pos])
        requires sb.states == overlay_prev.sb.states[
                                  |overlay_prev.sb.states|-1 :=
                                  StraightlineState(b.states[pos], last(overlay_prev.sb.states).visited_loops, true)]
        requires sb.trace == overlay_prev.sb.trace
        ensures  AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var sspec := GetStraightlineSpec(cr, actor, proc);

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);

        forall i | 0 <= i < |sb.trace|
            ensures ActionTuple(sb.states[i], sb.states[i+1], sb.trace[i]) in sspec.next
        {
            assert ActionTuple(overlay_prev.sb.states[i], overlay_prev.sb.states[i+1], overlay_prev.sb.trace[i]) in sspec.next;
            if i == |overlay_prev.sb.trace|-1 {
                assert sb.states[i] == overlay_prev.sb.states[i];
                assert sb.states[i+1] == StraightlineState(b.states[pos], last(overlay_prev.sb.states).visited_loops, true);
                assert sb.trace[i] == overlay_prev.sb.trace[i];
                lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
                assert cr.yield_pred(b.states[pos-1], b.states[pos], actor);
                match sb.trace[i]
                    case StraightlineStepStart() =>
                    {
                        assert cr.yield_pred(overlay_prev.sb.states[i].state, b.states[pos-1], actor);
                        assert StraightlineSpecNextStart(cr, sb.states[i], sb.states[i+1], actor, proc);
                    }
                    case StraightlineStepNormal(post_stmt_state, step) =>
                    {
                        assert cr.yield_pred(post_stmt_state, b.states[pos-1], actor);
                        assert StraightlineSpecNextNormal(cr, sb.states[i], sb.states[i+1], actor, proc, post_stmt_state, step);
                    }
                    case StraightlineStepCall(post_call_state, pre_return_state, post_return_state, call_step, return_step) =>
                    {
                        assert cr.yield_pred(post_return_state, b.states[pos-1], actor);
                        assert StraightlineSpecNextCall(cr, sb.states[i], sb.states[i+1], actor, proc, post_call_state,
                                                        pre_return_state, post_return_state, call_step, return_step);
                    }
                    case StraightlineStepLoop(post_loops_state, post_guard_state, guard_step) =>
                    {
                        assert cr.yield_pred(post_guard_state, b.states[pos-1], actor);
                        assert StraightlineSpecNextLoop(cr, sb.states[i], sb.states[i+1], actor, proc, post_loops_state,
                                                        post_guard_state, guard_step);
                    }
                assert StraightlineSpecNext(cr, sb.states[i], sb.states[i+1], sb.trace[i], actor, proc);
            }
        }
    }

    lemma lemma_GetStraightlineBehaviorCaseNoActorStep<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).None?
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        assert cr.idmap(step) != Some(actor);
        assert cr.actor_info(s)[actor] == cr.actor_info(s')[actor];

        var overlay_prev := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, proc);

        lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
        lemma_GetStraightlineBehaviorCaseNoActorStepHelper1(cr, b, pos, actor);

        var num_states := |overlay_prev.sb.states|;
        var states := overlay_prev.sb.states[num_states-1 :=
                          StraightlineState(b.states[pos], last(overlay_prev.sb.states).visited_loops, true)];
        var positions := overlay_prev.positions[num_states-1 := pos];
        overlay := StraightlineOverlay(AnnotatedBehavior(states, overlay_prev.sb.trace), positions);

        lemma_GetStraightlineBehaviorCaseNoOrOtherActorStepHelper2(cr, b, pos, actor, proc, overlay_prev, overlay.sb);
    }

    lemma lemma_GetStraightlineBehaviorCaseCallHelper<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).CallSite?
        ensures  cr.global_inv(b.states[pos])
        ensures  cr.requires_clauses(proc, b.states[pos], actor)
        decreases pos, 0
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var caller_pc := cr.actor_info(s)[actor].pc;
        var caller_proc := cr.pc_to_proc(caller_pc);
        var caller_overlay := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, caller_proc);

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, caller_proc, caller_overlay, |caller_overlay.sb.states|-1);

        var myb := caller_overlay.sb;
        assert AnnotatedBehaviorSatisfiesSpec(myb, GetStraightlineSpec(cr, actor, caller_proc));
        assert last(myb.states).started;
        assert s == last(myb.states).state;
        assert ActionTuple(s, s', step) in cr.spec.next;
        assert cr.idmap(step).v == actor;
        assert actor in cr.actor_info(s);
        assert actor in cr.actor_info(s');
        assert cr.pc_type(caller_pc).CallSite?;
        assert StraightlineSpecSatisfiesPreconditionsForCalls(cr);

        assert cr.global_inv(s');
        assert cr.requires_clauses(proc, s', actor);
    }

    lemma lemma_GetStraightlineBehaviorCaseCall<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).CallSite?
        requires cr.actor_info(b.states[pos])[actor].stack != cr.actor_info(b.states[pos-1])[actor].stack
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        var pc' := cr.actor_info(s')[actor].pc;

        var state0 := StraightlineState(s', map [], false);
        var state1 := StraightlineState(s', map [], true);
        var sstep := StraightlineStepStart();

        overlay := StraightlineOverlay(AnnotatedBehavior([state0, state1], [sstep]), [pos, pos]);

        assert ActionTuple(s, s', step) in cr.spec.next;
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
        lemma_GetStraightlineBehaviorCaseCallHelper(cr, b, pos, actor, proc);

        assert StraightlineSpecInit(cr, state0, actor, proc);
        assert StraightlineSpecNextStart(cr, state0, state1, actor, proc);

        lemma_EstablishPreviousStepIsCallOrForkViaCall(cr, b, actor, pos);
        assert StraightlineOverlayValid(cr, overlay, b, actor, proc);
    }

    lemma lemma_UsePreviousStepIsCallOrForkToEstablishCallWhenStackNonempty<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires PreviousStepIsCallOrFork(cr, b, actor, pos)
        requires 1 <= pos <= |b.trace|
        requires actor in cr.actor_info(b.states[pos])
        requires |cr.actor_info(b.states[pos])[actor].stack| > 0
        ensures  IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[pos-1], b.states[pos], b.trace[pos-1])
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;
        lemma_UsePreviousStepIsCallOrFork(cr, b, actor, pos);
    }

    lemma {:timeLimitMultiplier 2} lemma_GetStraightlineBehaviorCaseReturnHelper1<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        callee_proc:ProcName,
        overlay_callee:StraightlineOverlay<State, Step, PC>
        ) returns (
        call_pos:int,
        call_s:State,
        call_s':State,
        call_step:Step,
        caller_pc:PC
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?
        requires cr.actor_info(b.states[pos])[actor].stack != cr.actor_info(b.states[pos-1])[actor].stack
        requires callee_proc == cr.pc_to_proc(cr.actor_info(b.states[pos-1])[actor].pc)
        requires StraightlineOverlayValid(cr, overlay_callee, b, actor, callee_proc)
        requires last(overlay_callee.positions) == pos-1
        ensures  overlay_callee.positions[0] > 0
        ensures  call_pos == overlay_callee.positions[0]-1
        ensures  call_s == b.states[call_pos]
        ensures  call_s' == b.states[call_pos+1]
        ensures  call_step == b.trace[call_pos]
        ensures  actor in cr.actor_info(call_s)
        ensures  caller_pc == cr.actor_info(call_s)[actor].pc
        ensures  cr.idmap(call_step).Some?
        ensures  cr.idmap(call_step).v == actor
        ensures  cr.pc_type(caller_pc).CallSite?
        ensures  cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?
        ensures  cr.pc_to_proc(cr.actor_info(call_s')[actor].pc) == callee_proc
        ensures  cr.pc_to_proc(cr.actor_info(b.states[pos-1])[actor].pc) == callee_proc
        ensures  |cr.actor_info(call_s')[actor].stack| > 0
        ensures  cr.actor_info(call_s')[actor].stack[1..] == cr.actor_info(call_s)[actor].stack
        ensures  cr.actor_info(call_s')[actor].stack == cr.actor_info(b.states[pos-1])[actor].stack
        ensures  proc == cr.pc_to_proc(caller_pc)
        ensures  cr.enablement_condition(b.states[pos-1], actor);
        ensures  cr.established_inv(b.states[pos-1])
        ensures  cr.global_inv(b.states[pos-1])
        ensures  cr.local_inv(b.states[pos-1], actor)
        ensures  cr.established_inv(b.states[pos])
        ensures  cr.global_inv(b.states[pos])
        decreases pos, 0
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];

        assert ActionTuple(s, s', step) in cr.spec.next;

        var PCStack(pc, stack) := cr.actor_info(s)[actor];
        var PCStack(pc', stack') := cr.actor_info(s')[actor];
        var callee_proc := cr.pc_to_proc(pc);
        assert cr.pc_type(pc).ReturnSite?;

        var entry_pos := overlay_callee.positions[0];

        lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_callee.sb, actor, callee_proc, |overlay_callee.sb.states|-1);
        var stack_on_entry := cr.actor_info(b.states[entry_pos])[actor].stack;
        assert stack_on_entry == stack;
        assert |stack_on_entry| > 0;
        assert overlay_callee.positions[0] > 0;

        call_pos := entry_pos-1;
        call_s := b.states[entry_pos-1];
        call_s' := b.states[entry_pos];
        assert entry_pos == call_pos+1 && call_s' == b.states[call_pos+1];
        call_step := b.trace[entry_pos-1];

        lemma_UsePreviousStepIsCallOrForkToEstablishCallWhenStackNonempty(cr, b, entry_pos, actor);
        assert IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[entry_pos-1], b.states[entry_pos], b.trace[entry_pos-1]);
        assert IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, call_s, call_s', call_step);

        assert ActionTuple(b.states[call_pos], b.states[call_pos+1], b.trace[call_pos]) in cr.spec.next;
        assert ActionTuple(call_s, call_s', call_step) in cr.spec.next;
        caller_pc := cr.actor_info(call_s)[actor].pc;
        assert cr.pc_type(caller_pc).CallSite?;

        calc {
            pc';
            stack[0];
            stack_on_entry[0];
            cr.actor_info(call_s')[actor].stack[0];
        }

        assert proc == cr.pc_to_proc(caller_pc);
        lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, callee_proc, overlay_callee, |overlay_callee.positions|-1);
        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, callee_proc, overlay_callee, |overlay_callee.positions|-1);
    }

    lemma lemma_GetStraightlineBehaviorCaseReturnHelper2<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        callee_proc:ProcName,
        call_pos:int,
        call_s:State,
        call_s':State,
        call_step:Step,
        caller_pc:PC,
        overlay_prev:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires 0 <= call_pos < pos
        requires call_s == b.states[call_pos]
        requires call_s' == b.states[call_pos+1]
        requires call_step == b.trace[call_pos]
        requires actor in cr.actor_info(call_s)
        requires actor in cr.actor_info(call_s')
        requires caller_pc == cr.actor_info(call_s)[actor].pc
        requires cr.idmap(call_step).Some?
        requires cr.idmap(call_step).v == actor
        requires cr.pc_type(caller_pc).CallSite?
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?
        requires cr.actor_info(b.states[pos])[actor].stack != cr.actor_info(b.states[pos-1])[actor].stack
        requires cr.pc_to_proc(cr.actor_info(call_s')[actor].pc) == callee_proc
        requires cr.pc_to_proc(cr.actor_info(b.states[pos-1])[actor].pc) == callee_proc
        requires cr.actor_info(call_s')[actor].stack == cr.actor_info(b.states[pos-1])[actor].stack
        requires proc == cr.pc_to_proc(caller_pc)
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == call_pos
        requires cr.ensures_clauses(callee_proc, call_s', b.states[pos-1], actor)
        ensures  cr.established_inv(call_s')
        ensures  cr.global_inv(call_s')
        ensures  cr.requires_clauses(callee_proc, call_s', actor)
    {
        var prev := pos-1;
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
        assert ActionTuple(b.states[call_pos], b.states[call_pos+1], b.trace[call_pos]) in cr.spec.next;
        assert && var s := last(overlay_prev.sb.states).state;
               && last(overlay_prev.sb.states).started
               && ActionTuple(s, call_s', call_step) in cr.spec.next
               && cr.idmap(call_step).Some?
               && cr.idmap(call_step).v == actor
               && actor in cr.actor_info(s)
               && actor in cr.actor_info(call_s')
               && var pc := cr.actor_info(s)[actor].pc;
               && cr.pc_type(pc).CallSite?;
        assert cr.global_inv(call_s');
        assert cr.requires_clauses(cr.pc_to_proc(cr.actor_info(call_s')[actor].pc), call_s', actor);
        assert callee_proc == cr.pc_to_proc(cr.actor_info(call_s')[actor].pc);
        assert cr.requires_clauses(callee_proc, call_s', actor);
        lemma_InvariantPredicateHoldsAtStep(b, call_pos+1, cr.spec, cr.established_inv);
    }

    lemma {:timeLimitMultiplier 2} lemma_GetStraightlineBehaviorCaseReturnHelper3<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        callee_proc:ProcName,
        call_pos:int,
        call_s:State,
        call_s':State,
        call_step:Step,
        caller_pc:PC,
        overlay_prev:StraightlineOverlay<State, Step, PC>,
        next_state:StraightlineState<State, PC>,
        sstep:StraightlineStep<State, Step>,
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires 0 <= call_pos < pos
        requires call_s == b.states[call_pos]
        requires call_s' == b.states[call_pos+1]
        requires call_step == b.trace[call_pos]
        requires actor in cr.actor_info(call_s)
        requires actor in cr.actor_info(call_s')
        requires caller_pc == cr.actor_info(call_s)[actor].pc
        requires cr.idmap(call_step).Some?
        requires cr.idmap(call_step).v == actor
        requires cr.pc_type(caller_pc).CallSite?
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?
        requires cr.actor_info(b.states[pos])[actor].stack != cr.actor_info(b.states[pos-1])[actor].stack
        requires cr.pc_to_proc(cr.actor_info(call_s')[actor].pc) == callee_proc
        requires cr.pc_to_proc(cr.actor_info(b.states[pos-1])[actor].pc) == callee_proc
        requires |cr.actor_info(call_s')[actor].stack| > 0
        requires cr.actor_info(call_s')[actor].stack[1..] == cr.actor_info(call_s)[actor].stack
        requires cr.actor_info(call_s')[actor].stack == cr.actor_info(b.states[pos-1])[actor].stack
        requires proc == cr.pc_to_proc(caller_pc)
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == call_pos
        requires callee_proc == cr.pc_to_proc(cr.actor_info(b.states[pos-1])[actor].pc)
        requires cr.ensures_clauses(callee_proc, call_s', b.states[pos-1], actor)
        requires next_state.state == b.states[pos]
        requires next_state.visited_loops == last(overlay_prev.sb.states).visited_loops
        requires next_state.started
        requires overlay.sb.states == overlay_prev.sb.states + [next_state]
        requires sstep == StraightlineStepCall(call_s', b.states[pos-1], b.states[pos], call_step, b.trace[pos-1]);
        requires overlay.sb.trace == overlay_prev.sb.trace + [sstep]
        requires overlay.positions == overlay_prev.positions + [pos]
        requires cr.enablement_condition(b.states[pos-1], actor);
        requires cr.established_inv(b.states[pos-1])
        requires cr.global_inv(b.states[pos-1])
        requires cr.local_inv(b.states[pos-1], actor)
        requires cr.established_inv(call_s')
        requires cr.global_inv(call_s')
        requires cr.requires_clauses(callee_proc, call_s', actor)
        requires cr.established_inv(b.states[pos])
        requires cr.global_inv(b.states[pos])
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
    {
        var prev := pos-1;
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

        assert ActionTuple(b.states[call_pos], b.states[call_pos+1], b.trace[call_pos]) in cr.spec.next;

        assert caller_pc == cr.actor_info(call_s)[actor].pc;
        var caller_stack := cr.actor_info(call_s)[actor].stack;
        var callee_stack := cr.actor_info(call_s')[actor].stack;
        assert b.states[call_pos] == call_s;
        assert b.states[call_pos+1] == call_s';
        assert b.trace[call_pos] == call_step;
        assert cr.idmap(call_step).Some?;
        assert cr.idmap(call_step).v == actor;
        assert callee_stack[1..] == caller_stack;

        var sspec := GetStraightlineSpec(cr, actor, proc);
        forall i | 0 <= i < |overlay.sb.trace|
            ensures ActionTuple(overlay.sb.states[i], overlay.sb.states[i+1], overlay.sb.trace[i]) in sspec.next
        {
            if i == |overlay.sb.trace|-1 {
                assert overlay.sb.states[i] == last(overlay_prev.sb.states);
                assert overlay.sb.states[i].state == call_s;
                assert overlay.sb.states[i+1] == next_state;
                assert overlay.sb.trace[i] == sstep;
                lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, i);
                lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
                assert overlay_prev.sb.states[i].state == call_s;
                assert caller_pc == cr.actor_info(overlay_prev.sb.states[i].state)[actor].pc;
                lemma_VisitedLoopsOnlyContainsLoopHeads(cr, b, actor, proc, overlay_prev, caller_pc, i);
                assert StraightlineSpecNextCommon(cr, overlay.sb.states[i], overlay.sb.states[i+1], actor, proc);
                assert cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?;
                assert cr.enablement_condition(overlay.sb.states[i].state, actor);
                assert cr.requires_clauses(callee_proc, call_s', actor);
                assert StraightlineSpecNextCall(cr, overlay.sb.states[i], overlay.sb.states[i+1], actor, proc,
                                                call_s', b.states[pos-1], b.states[pos], call_step, b.trace[pos-1]);
            }
        }
    }

    lemma lemma_GetStraightlineBehaviorCaseReturn<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).ReturnSite?
        requires cr.actor_info(b.states[pos])[actor].stack != cr.actor_info(b.states[pos-1])[actor].stack
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;
        assert s' == b.states[pos];

        var PCStack(pc, stack) := cr.actor_info(s)[actor];
        var PCStack(pc', stack') := cr.actor_info(s')[actor];
        var callee_proc := cr.pc_to_proc(pc);
        assert cr.pc_type(pc).ReturnSite?;
        assert pc' == stack[0];
        assert stack' == stack[1..];

        var overlay_callee := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, callee_proc);
        var entry_pos := overlay_callee.positions[0];
        var call_pos, call_s, call_s', call_step, caller_pc :=
                lemma_GetStraightlineBehaviorCaseReturnHelper1(cr, b, pos, actor, proc, callee_proc, overlay_callee);

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, callee_proc, overlay_callee, |overlay_callee.sb.states|-1);
        assert cr.ensures_clauses(callee_proc, overlay_callee.sb.states[0].state, last(overlay_callee.sb.states).state, actor);
        
        var sspec := GetStraightlineSpec(cr, actor, callee_proc);

        var overlay_prev := lemma_GetStraightlineBehavior(cr, b, call_pos, actor, proc);
        var post_call_state := call_s';
        var pre_return_state := s;
        var post_return_state := s';
        var return_step := step;
        var sstep := StraightlineStepCall(post_call_state, pre_return_state, post_return_state, call_step, return_step);
        var next_state := StraightlineState(s', last(overlay_prev.sb.states).visited_loops, true);

        overlay := StraightlineOverlay(AnnotatedBehavior(overlay_prev.sb.states + [next_state], overlay_prev.sb.trace + [sstep]),
                                       overlay_prev.positions + [pos]);
        lemma_GetStraightlineBehaviorCaseReturnHelper2(cr, b, pos, actor, proc, callee_proc, call_pos, call_s, call_s', call_step,
                                                       caller_pc, overlay_prev);
        lemma_GetStraightlineBehaviorCaseReturnHelper3(cr, b, pos, actor, proc, callee_proc, call_pos, call_s, call_s', call_step,
                                                       caller_pc, overlay_prev, next_state, sstep, overlay);
    }

    lemma lemma_GetStraightlineBehaviorCaseGuardEvaluation<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var pc := cr.actor_info(s)[actor].pc;
        var pc' := cr.actor_info(s')[actor].pc;
        assert cr.pc_to_proc(pc') == cr.pc_to_proc(pc);

        var overlay_prev := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, proc);
        overlay := lemma_ExtendOverlayWithGuardEvaluation(cr, b, pos, actor, proc, overlay_prev);
    }

    lemma lemma_GetStraightlineBehaviorCaseNormalStatement<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires cr.actor_info(b.states[pos])[actor].stack == cr.actor_info(b.states[pos-1])[actor].stack
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires !cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 1
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;

        var pc := cr.actor_info(s)[actor].pc;
        var pc' := cr.actor_info(s')[actor].pc;
        assert cr.pc_to_proc(pc') == cr.pc_to_proc(pc);

        var overlay_prev := lemma_GetStraightlineBehavior(cr, b, pos-1, actor, proc);
        overlay := lemma_ExtendOverlayWithStatement(cr, b, pos, actor, proc, overlay_prev);
    }

    lemma lemma_GetStraightlineBehavior<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 <= pos < |b.states|
        requires actor in cr.actor_info(b.states[pos])
        requires proc == cr.pc_to_proc(cr.actor_info(b.states[pos])[actor].pc)
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        decreases pos, 2
    {
        if pos == 0 {
            overlay := lemma_GetStraightlineBehaviorCaseBehaviorStart(cr, b, actor, proc);
            return;
        }

        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        
        if actor !in cr.actor_info(s) {
            overlay := lemma_GetStraightlineBehaviorCaseFork(cr, b, pos, actor, proc);
            return;
        }
        if cr.idmap(step).None? {
            overlay := lemma_GetStraightlineBehaviorCaseNoActorStep(cr, b, pos, actor, proc);
            return;
        }
        if cr.idmap(step).v != actor {
            overlay := lemma_GetStraightlineBehaviorCaseOtherActorStep(cr, b, pos, actor, proc);
            return;
        }

        var PCStack(pc, stack) := cr.actor_info(s)[actor];
        if cr.pc_type(pc).LoopHead? {
            overlay := lemma_GetStraightlineBehaviorCaseGuardEvaluation(cr, b, pos, actor, proc);
        }
        else if actor in cr.actor_info(s') && cr.actor_info(s')[actor].stack == cr.actor_info(s)[actor].stack {
            overlay := lemma_GetStraightlineBehaviorCaseNormalStatement(cr, b, pos, actor, proc);
        }
        else if cr.pc_type(pc).CallSite? {
            overlay := lemma_GetStraightlineBehaviorCaseCall(cr, b, pos, actor, proc);
        }
        else if cr.pc_type(pc).ReturnSite? {
            overlay := lemma_GetStraightlineBehaviorCaseReturn(cr, b, pos, actor, proc);
        }
        else {
            assert false;
        }
    }
}
