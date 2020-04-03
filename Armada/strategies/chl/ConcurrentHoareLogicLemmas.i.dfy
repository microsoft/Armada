include "ConcurrentHoareLogicSpec.i.dfy"

module ConcurrentHoareLogicLemmasModule {

    import opened ConcurrentHoareLogicSpecModule
    import opened util_collections_maps_s
    import opened util_collections_seqs_s
    import opened util_option_s
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule

    datatype StraightlineOverlay<State, Step, PC> = StraightlineOverlay(
        sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<State, Step>>,
        positions:seq<int>
        )

    predicate IsCallStep<State, Actor, Step, PC>(
        idmap:Step->Option<Actor>,
        actor_info:State->imap<Actor, PCStack<PC>>,
        pc_type:PC->PCType<PC>,
        actor:Actor,
        s:State,
        s':State,
        step:Step
        )
    {
        && idmap(step).Some?
        && idmap(step).v == actor
        && actor in actor_info(s)
        && actor in actor_info(s')
        && var PCStack(pc, stack) := actor_info(s)[actor];
        && var stack' := actor_info(s')[actor].stack;
        && pc_type(pc).CallSite?
        && |stack'| > 0
        && stack == stack'[1..]
    }

    predicate IsForkStep<State, Actor, Step, PC>(
        idmap:Step->Option<Actor>,
        actor_info:State->imap<Actor, PCStack<PC>>,
        pc_type:PC->PCType<PC>,
        actor:Actor,
        s:State,
        s':State,
        step:Step
        )
    {
        && idmap(step).Some?
        && idmap(step).v != actor
        && actor !in actor_info(s)
        && actor in actor_info(s')
        && idmap(step).v in actor_info(s)
        && var pc := actor_info(s)[idmap(step).v].pc;
        && var stack' := actor_info(s')[actor].stack;
        && pc_type(pc).ForkSite?
        && |stack'| == 0
    }

    predicate {:opaque} PreviousStepIsCallOrFork<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        pos:int
        )
    {
        1 <= pos <= |b.trace| < |b.states|
        ==> var s := b.states[pos-1];
            var s' := b.states[pos];
            var step := b.trace[pos-1];
            (|| IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, s, s', step)
             || IsForkStep(cr.idmap, cr.actor_info, cr.pc_type, actor, s, s', step))
    }

    lemma lemma_UsePreviousStepIsCallOrFork<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        pos:int
        )
        requires PreviousStepIsCallOrFork(cr, b, actor, pos)
        requires 1 <= pos <= |b.trace| < |b.states|
        ensures || IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[pos-1], b.states[pos], b.trace[pos-1])
                || IsForkStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[pos-1], b.states[pos], b.trace[pos-1])
    {
        reveal_PreviousStepIsCallOrFork();
        var s := b.states[pos-1];
        var s' := b.states[pos];
        var step := b.trace[pos-1];
        assert || IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, s, s', step)
               || IsForkStep(cr.idmap, cr.actor_info, cr.pc_type, actor, s, s', step);
    }

    lemma lemma_EstablishPreviousStepIsCallOrForkViaStart<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        pos:int
        )
        requires pos == 0
        ensures  PreviousStepIsCallOrFork(cr, b, actor, pos)
    {
        reveal_PreviousStepIsCallOrFork();
    }

    lemma lemma_EstablishPreviousStepIsCallOrForkViaCall<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        pos:int
        )
        requires 1 <= pos <= |b.trace| < |b.states|
        requires IsCallStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[pos-1], b.states[pos], b.trace[pos-1])
        ensures  PreviousStepIsCallOrFork(cr, b, actor, pos)
    {
        reveal_PreviousStepIsCallOrFork();
    }

    lemma lemma_EstablishPreviousStepIsCallOrForkViaFork<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        pos:int
        )
        requires 1 <= pos <= |b.trace| < |b.states|
        requires IsForkStep(cr.idmap, cr.actor_info, cr.pc_type, actor, b.states[pos-1], b.states[pos], b.trace[pos-1])
        ensures  PreviousStepIsCallOrFork(cr, b, actor, pos)
    {
        reveal_PreviousStepIsCallOrFork();
    }

    predicate SequenceMonotonic(positions:seq<int>)
    {
        forall i, j :: 0 <= i <= j < |positions| ==> positions[i] <= positions[j]
    }

    predicate StraightlineOverlayValid<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        overlay:StraightlineOverlay<State, Step, PC>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName
        )
    {
        && AnnotatedBehaviorSatisfiesSpec(overlay.sb, GetStraightlineSpec(cr, actor, proc))
        && |overlay.positions| == |overlay.sb.states|
        && |overlay.positions| >= 2
        && SequenceMonotonic(overlay.positions)
        && (forall i :: 0 <= i < |overlay.positions| ==>
               && 0 <= overlay.positions[i] < |b.states|
               && b.states[overlay.positions[i]] == overlay.sb.states[i].state)
        && PreviousStepIsCallOrFork(cr, b, actor, overlay.positions[0])
    }

    lemma lemma_StraightlineBehaviorNeverChangesStack<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<State, Step>>,
        actor:Actor,
        proc:ProcName,
        pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
        requires 0 <= pos < |sb.states|
        ensures  actor in cr.actor_info(sb.states[0].state)
        ensures  actor in cr.actor_info(sb.states[pos].state)
        ensures  cr.pc_to_proc(cr.actor_info(sb.states[pos].state)[actor].pc) == proc
        ensures  cr.actor_info(sb.states[pos].state)[actor].stack == cr.actor_info(sb.states[0].state)[actor].stack
        decreases pos
    {
        if pos == 0 {
            return;
        }

        var prev := pos-1;
        var s := sb.states[prev];
        var s' := sb.states[prev+1];
        var step := sb.trace[prev];

        var sspec := GetStraightlineSpec(cr, actor, proc);
        assert ActionTuple(s, s', step) in sspec.next;
        
        lemma_StraightlineBehaviorNeverChangesStack(cr, sb, actor, proc, pos-1);
        assert StraightlineSpecNext(cr, s, s', step, actor, proc);
    }

    lemma lemma_NonInitialStateOfValidOverlayIsStarted<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName,
        overlay:StraightlineOverlay<State, Step, PC>,
        pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires StraightlineOverlayValid(cr, overlay, b, actor, proc)
        requires 0 < pos < |overlay.positions|
        ensures  overlay.sb.states[pos].started
    {
        var prev := pos-1;
        var s := overlay.sb.states[prev];
        var s' := overlay.sb.states[prev+1];
        var step := overlay.sb.trace[prev];

        var sspec := GetStraightlineSpec(cr, actor, proc);
        assert ActionTuple(s, s', step) in sspec.next;
    }

    lemma lemma_StateOfValidOverlaySatisfiesGlobalInvariant<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName,
        overlay:StraightlineOverlay<State, Step, PC>,
        overlay_pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires StraightlineOverlayValid(cr, overlay, b, actor, proc)
        requires 0 <= overlay_pos < |overlay.positions|
        ensures  cr.established_inv(overlay.sb.states[overlay_pos].state)
        ensures  cr.global_inv(overlay.sb.states[overlay_pos].state)
    {
        lemma_InvariantPredicateHoldsAtStep(b, overlay.positions[overlay_pos], cr.spec, cr.established_inv);

        var sspec := GetStraightlineSpec(cr, actor, proc);

        if overlay_pos == 0 {
            assert StraightlineSpecInit(cr, overlay.sb.states[overlay_pos], actor, proc);
            assert cr.global_inv(overlay.sb.states[overlay_pos].state);
        }
        else {
            var prev := overlay_pos - 1;
            assert ActionTuple(overlay.sb.states[prev], overlay.sb.states[prev+1], overlay.sb.trace[prev]) in sspec.next;
            assert StraightlineSpecNext(cr, overlay.sb.states[prev], overlay.sb.states[prev+1], overlay.sb.trace[prev], actor, proc);
            assert cr.global_inv(overlay.sb.states[prev+1].state);
        }
    }

    lemma lemma_VisitedLoopsOnlyContainsLoopHeads<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName,
        overlay:StraightlineOverlay<State, Step, PC>,
        pc:PC,
        pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires StraightlineOverlayValid(cr, overlay, b, actor, proc)
        requires 0 <= pos < |overlay.positions|
        requires !cr.pc_type(pc).LoopHead?
        ensures  pc !in overlay.sb.states[pos].visited_loops
    {
        if (pos == 0) {
            return;
        }

        lemma_VisitedLoopsOnlyContainsLoopHeads(cr, b, actor, proc, overlay, pc, pos-1);

        var prev := pos-1;
        var s := overlay.sb.states[prev];
        var s' := overlay.sb.states[prev+1];
        var step := overlay.sb.trace[prev];

        var sspec := GetStraightlineSpec(cr, actor, proc);
        assert ActionTuple(s, s', step) in sspec.next;
    }

    lemma lemma_FindWhenLoopBegan<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        actor:Actor,
        proc:ProcName,
        overlay:StraightlineOverlay<State, Step, PC>,
        pc:PC,
        pos:int
        ) returns (
        earlier_pos:int
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires StraightlineOverlayValid(cr, overlay, b, actor, proc)
        requires 0 <= pos < |overlay.sb.states|
        requires pc in overlay.sb.states[pos].visited_loops
        requires actor in cr.actor_info(overlay.sb.states[pos].state)
        ensures  1 <= earlier_pos < pos
        ensures  cr.pc_type(pc).LoopHead?
        ensures  actor in cr.actor_info(overlay.sb.states[earlier_pos].state)
        ensures  cr.actor_info(overlay.sb.states[earlier_pos].state)[actor].pc == pc
        ensures  pc !in overlay.sb.states[earlier_pos].visited_loops
        ensures  pc in overlay.sb.states[earlier_pos+1].visited_loops
        ensures  overlay.sb.states[earlier_pos+1].visited_loops[pc] == overlay.sb.states[pos].visited_loops[pc]
        ensures  overlay.sb.states[earlier_pos+1].visited_loops[pc] == overlay.sb.states[earlier_pos].state
        ensures  overlay.sb.trace[earlier_pos].StraightlineStepLoop?
        ensures  cr.enablement_condition(overlay.sb.states[earlier_pos].state, actor)
    {
        if pos == 0 {
            assert false;
            return;
        }

        var sspec := GetStraightlineSpec(cr, actor, proc);
        var prev := pos-1;
        assert ActionTuple(overlay.sb.states[prev], overlay.sb.states[prev+1], overlay.sb.trace[prev]) in sspec.next;
        var current_pc := cr.actor_info(overlay.sb.states[pos].state)[actor].pc;
        var prev_pc := cr.actor_info(overlay.sb.states[prev].state)[actor].pc;

        if prev_pc == pc {
            earlier_pos := prev;
            if earlier_pos == 0 {
                assert ActionTuple(b.states[0], b.states[0+1], b.trace[0]) in cr.spec.next;
            }
            return;
        }

        earlier_pos := lemma_FindWhenLoopBegan(cr, b, actor, proc, overlay, pc, pos-1);
    }

    lemma lemma_ExtendOverlayWithGuardEvaluationFirstTime<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires actor in cr.actor_info(b.states[pos-1])
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        requires cr.actor_info(b.states[pos-1])[actor].pc !in last(overlay_prev.sb.states).visited_loops
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        ensures  actor in cr.actor_info(b.states[pos])
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;
        var pc := cr.actor_info(s)[actor].pc;
        var pc' := cr.actor_info(s')[actor].pc;

        var visited_loops := last(overlay_prev.sb.states).visited_loops;
        var new_visited_loops := visited_loops[pc := s];
        var next_state := StraightlineState(s', new_visited_loops, true);

        var states := overlay_prev.sb.states + [next_state];
        var sstep := StraightlineStepLoop(s, s', step);
        var trace := overlay_prev.sb.trace + [sstep];
        var positions := overlay_prev.positions + [pos];
        var sb := AnnotatedBehavior(states, trace);

        var sspec := GetStraightlineSpec(cr, actor, proc);
        forall i | 0 <= i < |sb.trace|
            ensures ActionTuple(sb.states[i], sb.states[i+1], sb.trace[i]) in sspec.next
        {
            if i < |sb.trace|-1 {
                assert ActionTuple(overlay_prev.sb.states[i], overlay_prev.sb.states[i+1], overlay_prev.sb.trace[i]) in sspec.next;
            }
            else {
                assert i == |sb.trace|-1;
                assert sb.states[i].state == s;
                assert sb.states[i+1] == next_state;
                assert sb.trace[i] == sstep;
                lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
                lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, i);
                lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, i);
                assert !cr.pc_type(pc).CallSite?;
                assert !cr.pc_type(pc).ReturnSite?;
                lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
                assert StraightlineSpecNextLoop(cr, sb.states[i], sb.states[i+1], actor, proc, s, s', step);
                assert StraightlineSpecNext(cr, sb.states[i], sb.states[i+1], sb.trace[i], actor, proc);
            }
        }
        assert AnnotatedBehaviorSatisfiesSpec(sb, sspec);

        overlay := StraightlineOverlay(sb, positions);
    }

    lemma lemma_ExtendOverlayWithGuardEvaluationRepeatingHelper<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>,
        pc:PC,
        earlier_pos:int,
        next_state:StraightlineState<State, PC>,
        sstep:StraightlineStep<State, Step>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires actor in cr.actor_info(b.states[pos-1])
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        requires cr.actor_info(b.states[pos-1])[actor].pc in last(overlay_prev.sb.states).visited_loops
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        requires pc == cr.actor_info(b.states[pos-1])[actor].pc
        requires 1 <= earlier_pos < |overlay_prev.sb.states|-1
        requires actor in cr.actor_info(overlay_prev.sb.states[earlier_pos].state)
        requires cr.actor_info(overlay_prev.sb.states[earlier_pos].state)[actor].pc == pc
        requires pc !in overlay_prev.sb.states[earlier_pos].visited_loops
        requires pc in overlay_prev.sb.states[earlier_pos+1].visited_loops
        requires cr.enablement_condition(overlay_prev.sb.states[earlier_pos].state, actor)
        requires overlay_prev.sb.states[earlier_pos+1].visited_loops[pc] == last(overlay_prev.sb.states).visited_loops[pc]
        requires overlay_prev.sb.states[earlier_pos+1].visited_loops[pc] == overlay_prev.sb.states[earlier_pos].state
        requires next_state == StraightlineState(b.states[pos], overlay_prev.sb.states[earlier_pos].visited_loops[pc := overlay_prev.sb.states[earlier_pos].state], true)
        requires sstep == StraightlineStepLoop(b.states[pos-1], b.states[pos], b.trace[pos-1])

        ensures  StraightlineSpecNext(cr, overlay_prev.sb.states[earlier_pos], next_state, sstep, actor, proc)
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

        lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
        lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, 0);
        lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, earlier_pos);
        lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, |overlay_prev.sb.states|-1);
        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, earlier_pos);
        assert !cr.pc_type(pc).CallSite?;
        assert !cr.pc_type(pc).ReturnSite?;

        var earlier_s := overlay_prev.sb.states[earlier_pos].state;
        var sspec := GetStraightlineSpec(cr, actor, proc);

        forall ensures cr.established_inv(earlier_s) && cr.global_inv(earlier_s)
        {
            lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, earlier_pos);
        }

        forall ensures cr.local_inv(earlier_s, actor)
        {
            var truncated_ab := AnnotatedBehavior(overlay_prev.sb.states[..earlier_pos+1], overlay_prev.sb.trace[..earlier_pos]);
            var truncated_overlay_prev := StraightlineOverlay(truncated_ab, overlay_prev.positions[..earlier_pos+1]);
            assert StraightlineOverlayValid(cr, truncated_overlay_prev, b, actor, proc);
            assert AnnotatedBehaviorSatisfiesSpec(truncated_ab, sspec);
            assert cr.local_inv(last(truncated_ab.states).state, actor);
            calc {
                last(truncated_ab.states);
                last(truncated_overlay_prev.sb.states);
                last(overlay_prev.sb.states[..earlier_pos+1]);
                overlay_prev.sb.states[earlier_pos];
            }
        }

        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
        assert cr.enablement_condition(overlay_prev.sb.states[earlier_pos].state, actor);
        assert cr.enablement_condition(sstep.post_loops_state, actor);
        lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
        assert StraightlineSpecNextLoop(cr, overlay_prev.sb.states[earlier_pos], next_state, actor, proc, sstep.post_loops_state,
                                        sstep.post_guard_state, sstep.guard_step);
        assert StraightlineSpecNext(cr, overlay_prev.sb.states[earlier_pos], next_state, sstep, actor, proc);
    }

    lemma {:timeLimitMultiplier 2} lemma_ExtendOverlayWithGuardEvaluationRepeating<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires actor in cr.actor_info(b.states[pos-1])
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        requires cr.actor_info(b.states[pos-1])[actor].pc in last(overlay_prev.sb.states).visited_loops
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        ensures  actor in cr.actor_info(b.states[pos])
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;
        var pc := cr.actor_info(s)[actor].pc;
        var pc' := cr.actor_info(s')[actor].pc;

        var earlier_pos := lemma_FindWhenLoopBegan(cr, b, actor, proc, overlay_prev, pc, |overlay_prev.sb.states|-1);
        assert overlay_prev.sb.states[earlier_pos+1].visited_loops[pc] ==
                   overlay_prev.sb.states[|overlay_prev.sb.states|-1].visited_loops[pc];
        assert overlay_prev.sb.states[earlier_pos+1].visited_loops[pc] == last(overlay_prev.sb.states).visited_loops[pc];

        var visited_loops := overlay_prev.sb.states[earlier_pos].visited_loops;
        var new_visited_loops := visited_loops[pc := overlay_prev.sb.states[earlier_pos].state];
        var next_state := StraightlineState(s', new_visited_loops, true);
        var states := overlay_prev.sb.states[..earlier_pos+1] + [next_state];
        var sstep := StraightlineStepLoop(s, s', step);
        var trace := overlay_prev.sb.trace[..earlier_pos] + [sstep];
        var positions := overlay_prev.positions[..earlier_pos+1] + [pos];
        var sb := AnnotatedBehavior(states, trace);

        var sspec := GetStraightlineSpec(cr, actor, proc);
        forall i | 0 <= i < |sb.trace|
            ensures ActionTuple(sb.states[i], sb.states[i+1], sb.trace[i]) in sspec.next
        {
            if i < |sb.trace|-1 {
                assert ActionTuple(overlay_prev.sb.states[i], overlay_prev.sb.states[i+1], overlay_prev.sb.trace[i]) in sspec.next;
            }
            else {
                assert i == |sb.trace|-1;
                assert sb.states[i].state == overlay_prev.sb.states[earlier_pos].state;
                assert sb.states[i+1] == next_state;
                assert sb.trace[i] == sstep;
                lemma_ExtendOverlayWithGuardEvaluationRepeatingHelper(cr, b, pos, actor, proc, overlay_prev, pc, earlier_pos,
                    next_state, sstep);
            }
        }
        assert AnnotatedBehaviorSatisfiesSpec(sb, sspec);

        overlay := StraightlineOverlay(sb, positions);

        assert |overlay.positions| == earlier_pos + 2;
        lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay, |overlay.positions|-1);
    }

    lemma lemma_ExtendOverlayWithGuardEvaluation<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires actor in cr.actor_info(b.states[pos-1])
        requires cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        ensures  actor in cr.actor_info(b.states[pos])
    {
        if cr.actor_info(b.states[pos-1])[actor].pc !in last(overlay_prev.sb.states).visited_loops {
            overlay := lemma_ExtendOverlayWithGuardEvaluationFirstTime(cr, b, pos, actor, proc, overlay_prev);
        }
        else {
            overlay := lemma_ExtendOverlayWithGuardEvaluationRepeating(cr, b, pos, actor, proc, overlay_prev);
        }
    }

    lemma lemma_ExtendOverlayWithStatement<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        b:AnnotatedBehavior<State, Step>,
        pos:int,
        actor:Actor,
        proc:ProcName,
        overlay_prev:StraightlineOverlay<State, Step, PC>
        ) returns (
        overlay:StraightlineOverlay<State, Step, PC>
        )
        requires IsValidConcurrentHoareLogicRequest(cr)
        requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
        requires 0 < pos < |b.states|
        requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
        requires last(overlay_prev.positions) == pos-1
        requires actor in cr.actor_info(b.states[pos-1])
        requires actor in cr.actor_info(b.states[pos])
        requires cr.actor_info(b.states[pos])[actor].stack == cr.actor_info(b.states[pos-1])[actor].stack
        requires !cr.pc_type(cr.actor_info(b.states[pos-1])[actor].pc).LoopHead?
        requires cr.idmap(b.trace[pos-1]).Some?
        requires cr.idmap(b.trace[pos-1]).v == actor
        ensures  StraightlineOverlayValid(cr, overlay, b, actor, proc)
        ensures  last(overlay.positions) == pos
        ensures  actor in cr.actor_info(b.states[pos])
    {
        var prev := pos-1;
        var s := b.states[prev];
        var s' := b.states[prev+1];
        var step := b.trace[prev];
        assert ActionTuple(s, s', step) in cr.spec.next;
        var pc := cr.actor_info(s)[actor].pc;
        var pc' := cr.actor_info(s')[actor].pc;

        var visited_loops := last(overlay_prev.sb.states).visited_loops;
        var new_visited_loops := if cr.pc_type(pc).LoopHead? then visited_loops[pc := s] else visited_loops;
        var next_state := StraightlineState(s', new_visited_loops, true);

        var states := overlay_prev.sb.states + [next_state];
        var sstep := StraightlineStepNormal(s', step);
        var trace := overlay_prev.sb.trace + [sstep];
        var positions := overlay_prev.positions + [pos];
        var sb := AnnotatedBehavior(states, trace);

        var sspec := GetStraightlineSpec(cr, actor, proc);
        forall i | 0 <= i < |sb.trace|
            ensures ActionTuple(sb.states[i], sb.states[i+1], sb.trace[i]) in sspec.next
        {
            if i < |sb.trace|-1 {
                assert ActionTuple(overlay_prev.sb.states[i], overlay_prev.sb.states[i+1], overlay_prev.sb.trace[i]) in sspec.next;
            }
            else {
                assert i == |sb.trace|-1;
                assert sb.states[i].state == s;
                assert sb.states[i+1] == next_state;
                assert sb.trace[i] == sstep;
                lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
                lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, i);
                lemma_NonInitialStateOfValidOverlayIsStarted(cr, b, actor, proc, overlay_prev, i);
                assert !cr.pc_type(pc).LoopHead?;
                lemma_VisitedLoopsOnlyContainsLoopHeads(cr, b, actor, proc, overlay_prev, pc, i);
                lemma_StateOfValidOverlaySatisfiesGlobalInvariant(cr, b, actor, proc, overlay_prev, |overlay_prev.positions|-1);
                assert StraightlineSpecNextNormal(cr, sb.states[i], sb.states[i+1], actor, proc, s', step);
                assert StraightlineSpecNext(cr, sb.states[i], sb.states[i+1], sb.trace[i], actor, proc);
            }
        }
        assert AnnotatedBehaviorSatisfiesSpec(sb, sspec);

        overlay := StraightlineOverlay(sb, positions);
    }
}
