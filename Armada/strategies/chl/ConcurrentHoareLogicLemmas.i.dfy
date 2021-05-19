include "ConcurrentHoareLogicSpec.i.dfy"

module ConcurrentHoareLogicLemmasModule {

  import opened util_collections_maps_s
  import opened util_collections_seqs_s
  import opened util_option_s
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ConcurrentHoareLogicSpecModule

  ///////////////////////////////////////////
  // Sequence monotonicity
  ///////////////////////////////////////////

  predicate {:opaque} SequenceMonotonic(s:seq<int>)
  {
    forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
  }

  lemma lemma_TakeSequenceMonotonic(s:seq<int>, n:int)
    requires SequenceMonotonic(s)
    requires 0 <= n < |s|
    ensures  SequenceMonotonic(s[..n])
  {
    reveal SequenceMonotonic();
  }

  lemma lemma_ExtendSequenceMonotonic(s:seq<int>, n:int)
    requires SequenceMonotonic(s)
    requires |s| > 0 ==> n >= last(s)
    ensures  SequenceMonotonic(s + [n])
  {
    reveal SequenceMonotonic();
  }

  lemma lemma_UseSequenceMonotonic(s:seq<int>, i:int, j:int)
    requires SequenceMonotonic(s)
    requires 0 <= i <= j < |s|
    ensures  s[i] <= s[j]
  {
    reveal SequenceMonotonic();
  }

  lemma lemma_EstablishSequenceMonotonic(s:seq<int>)
    requires forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
    ensures  SequenceMonotonic(s)
  {
    reveal SequenceMonotonic();
  }

  lemma lemma_ReplaceLastSequenceMonotonic(s:seq<int>, n:int)
    requires SequenceMonotonic(s)
    requires |s| > 0
    requires n >= last(s)
    ensures  SequenceMonotonic(all_but_last(s) + [n])
  {
    reveal SequenceMonotonic();
  }

  ///////////////////////////////////////////
  // Overlay validity
  ///////////////////////////////////////////

  datatype HowStarted = HowStartedInit | HowStartedCall | HowStartedFork

  datatype StraightlineOverlay<State, Step, PC, Proc> = StraightlineOverlay(
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    how_started:HowStarted,
    positions:seq<int>
    )

  predicate IsCallStep<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    actor:Actor,
    step:Step
    )
  {
    var step_actor := cr.step_to_actor(step);
    var effect := cr.step_to_effect(step);
    && step_actor.Some?
    && step_actor.v == actor
    && (effect.CHLStepEffectCall? || effect.CHLStepEffectReturnThenCall?)
  }

  predicate IsForkStep<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    actor:Actor,
    s:State
    )
  {
    cr.get_actor_pc_stack(s, actor).None?
  }

  predicate StraightlineOverlayValid<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    overlay:StraightlineOverlay<State, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc
    )
  {
    && AnnotatedBehaviorSatisfiesSpec(overlay.sb, GetStraightlineSpec(cr, actor, proc))
    && |overlay.positions| == |overlay.sb.states|
    && |overlay.positions| > 0
    && SequenceMonotonic(overlay.positions)
    && (forall i :: 0 <= i < |overlay.positions| ==>
         && 0 <= overlay.positions[i] < |b.states|
         && b.states[overlay.positions[i]] == overlay.sb.states[i].state)
    && (var pos := overlay.positions[0];
       match overlay.how_started
         case HowStartedInit => pos == 0
         case HowStartedCall => 0 < pos <= |b.trace| && IsCallStep(cr, actor, b.trace[pos-1])
         case HowStartedFork => 0 < pos <= |b.trace| && IsForkStep(cr, actor, b.states[pos-1]))
  }

  predicate StraightlineOverlayLeadsToPos<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    overlay:StraightlineOverlay<State, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc,
    pos:int
    )
  {
    && StraightlineOverlayValid(cr, overlay, b, actor, proc)
    && last(overlay.positions) == pos
  }

  ///////////////////////////////////////////
  // Lemmas about straightline behaviors
  ///////////////////////////////////////////

  predicate ActorInProc<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    actor:Actor,
    proc:Proc
    )
  {
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
      cr.pc_to_proc(pc) == proc
  }

  lemma lemma_StraightlineBehaviorSatisfiesGlobalInvariant<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc,
    pos:int
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    requires 0 <= pos < |sb.states|
    ensures  cr.global_inv(sb.states[pos].state)
    ensures  cr.state_ok(sb.states[pos].state)
  {
    if pos == 0 {
      return;
    }

    var sspec := GetStraightlineSpec(cr, actor, proc);
    var prev := pos-1;
    var ss := sb.states[prev];
    var ss' := sb.states[prev+1];
    var sstep := sb.trace[prev];
    assert ActionTuple(ss, ss', sstep) in sspec.next;
    assert StraightlineSpecNext(cr, ss, ss', sstep, actor, proc);
    assert StraightlineSpecNextCommon(cr, ss, ss', sstep, actor);
    assert cr.global_inv(ss'.state);
  }

  lemma lemma_StraightlineBehaviorNeverChangesStack<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc,
    pos:int
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    requires 0 <= pos < |sb.states|
    ensures  var ss0 := sb.states[0];
             var ss' := sb.states[pos];
             var s0 := ss0.state;
             var StraightlineState(s', aux') := ss';
             && cr.get_actor_pc_stack(s0, actor).Some?
             && cr.get_actor_pc_stack(s', actor).Some?
             && var PCStack(pc0, stack0) := cr.get_actor_pc_stack(s0, actor).v;
               var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
               if aux'.phase.StraightlinePhaseCalled? || aux'.phase.StraightlinePhaseEnsured? then
                 && |stack'| > 0
                 && stack'[0] == proc
                 && stack'[1..] == stack0
               else
                 && cr.pc_to_proc(pc') == proc
                 && stack' == stack0
    decreases pos
  {
    if pos == 0 {
      return;
    }

    var prev := pos-1;
    var ss := sb.states[prev];
    var ss' := sb.states[prev+1];
    var sstep := sb.trace[prev];

    var sspec := GetStraightlineSpec(cr, actor, proc);
    assert ActionTuple(ss, ss', sstep) in sspec.next;

    lemma_StraightlineBehaviorNeverChangesStack(cr, sb, actor, proc, pos-1);
    assert StraightlineSpecNext(cr, ss, ss', sstep, actor, proc);
  }

  lemma lemma_VisitedLoopsOnlyContainsLoopHeads<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc,
    pc:PC,
    pos:int
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    requires 0 <= pos < |sb.states|
    ensures  pc in sb.states[pos].aux.visited_loops ==> cr.is_loop_head(pc)
  {
    if pos == 0 {
      return;
    }

    var prev := pos-1;
    var ss := sb.states[prev];
    var ss' := sb.states[prev+1];
    var step := sb.trace[prev];

    var sspec := GetStraightlineSpec(cr, actor, proc);
    assert ActionTuple(ss, ss', step) in sspec.next;
    lemma_VisitedLoopsOnlyContainsLoopHeads(cr, sb, actor, proc, pc, prev);
  }

  lemma lemma_PCVisitedIfInLoopedPhase<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc,
    pos:int
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    requires 0 <= pos < |sb.states|
    ensures  cr.get_actor_pc_stack(sb.states[pos].state, actor).Some?
    ensures  var StraightlineState(s, aux) := sb.states[pos];
             var pc := cr.get_actor_pc_stack(s, actor).v.pc;
             var phase := aux.phase;
             && (cr.is_loop_head(pc) && phase.StraightlinePhaseLooped? ==> pc in aux.visited_loops)
             && (pc in aux.visited_loops ==> cr.is_loop_head(pc))
  {
    if pos == 0 {
      return;
    }

    var prev := pos-1;
    lemma_PCVisitedIfInLoopedPhase(cr, sb, actor, proc, prev);

    var sspec := GetStraightlineSpec(cr, actor, proc);
    assert ActionTuple(sb.states[prev], sb.states[prev+1], sb.trace[prev]) in sspec.next;
    var pc := cr.get_actor_pc_stack(sb.states[pos].state, actor).v.pc;
    lemma_VisitedLoopsOnlyContainsLoopHeads(cr, sb, actor, proc, pc, pos);
  }

  ///////////////////////////////////////////
  // Lemmas about overlays
  ///////////////////////////////////////////

  lemma lemma_FindWhenLoopBegan<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc,
    overlay:StraightlineOverlay<State, Step, PC, Proc>,
    pc:PC,
    pos:int
    ) returns (
    earlier_pos:int
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires StraightlineOverlayValid(cr, overlay, b, actor, proc)
    requires 0 <= pos < |overlay.sb.states|
    requires pc in overlay.sb.states[pos].aux.visited_loops
    requires cr.get_actor_pc_stack(overlay.sb.states[pos].state, actor).Some?
    ensures  0 <= earlier_pos < pos
    ensures  cr.is_loop_head(pc)
    ensures  cr.get_actor_pc_stack(overlay.sb.states[earlier_pos].state, actor).Some?
    ensures  cr.get_actor_pc_stack(overlay.sb.states[earlier_pos].state, actor).v.pc == pc
    ensures  overlay.sb.states[earlier_pos].aux.phase.StraightlinePhaseYielded?
    ensures  pc !in overlay.sb.states[earlier_pos].aux.visited_loops
    ensures  pc in overlay.sb.states[earlier_pos+1].aux.visited_loops
    ensures  overlay.sb.states[earlier_pos+1].aux.visited_loops[pc] == overlay.sb.states[pos].aux.visited_loops[pc]
               == overlay.sb.states[earlier_pos].state
    ensures  overlay.sb.trace[earlier_pos] == StraightlineStepLoopModifies(pc)
  {
    if pos == 0 {
      assert false;
      return;
    }

    lemma_VisitedLoopsOnlyContainsLoopHeads(cr, overlay.sb, actor, proc, pc, pos);
    var sspec := GetStraightlineSpec(cr, actor, proc);
    var prev := pos-1;
    assert ActionTuple(overlay.sb.states[prev], overlay.sb.states[prev+1], overlay.sb.trace[prev]) in sspec.next;
    lemma_PCVisitedIfInLoopedPhase(cr, overlay.sb, actor, proc, prev);

    if pc !in overlay.sb.states[prev].aux.visited_loops {
      earlier_pos := prev;
      return;
    }

    earlier_pos := lemma_FindWhenLoopBegan(cr, b, actor, proc, overlay, pc, pos-1);
  }

  lemma lemma_ExtendYieldingOverlayOneStep<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc,
    pos:int,
    overlay_prev:StraightlineOverlay<State, Step, PC, Proc>
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires StraightlineOverlayLeadsToPos(cr, overlay_prev, b, actor, proc, pos-1)
    requires last(overlay_prev.sb.states).aux.phase.StraightlinePhaseYielded?
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires cr.yield_pred(b.states[pos-1], b.states[pos], actor)
    requires cr.global_inv(b.states[pos])
    requires cr.get_actor_pc_stack(b.states[pos], actor) == cr.get_actor_pc_stack(b.states[pos-1], actor)
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
  {
    var s' := b.states[pos];
    var sspec := GetStraightlineSpec(cr, actor, proc);
    var opos := |overlay_prev.sb.trace| - 1;
    var ss := overlay_prev.sb.states[opos];
    var ss' := overlay_prev.sb.states[opos+1];
    var sstep := overlay_prev.sb.trace[opos];
    assert ActionTuple(ss, ss', sstep) in sspec.next;
    assert StraightlineSpecNextYield(cr, ss, ss', sstep, actor, proc);

    var new_aux' := StraightlineUpdateAux(cr, ss, actor, sstep, s');
    var new_ss' := StraightlineState(s', new_aux');
    var sstates := all_but_last(overlay_prev.sb.states) + [new_ss'];
    lemma_InvariantPredicateHoldsAtStep(b, overlay_prev.positions[opos], cr.spec, cr.established_inv);
    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, opos);
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    assert StraightlineSpecNextYield(cr, ss, new_ss', sstep, actor, proc);
    assert StraightlineSpecNext(cr, ss, new_ss', sstep, actor, proc);

    lemma_ReplaceStateOnlyStateNextSeqRight(overlay_prev.sb.states, overlay_prev.sb.trace, sspec.next, new_ss');
    lemma_ReplaceLastSequenceMonotonic(overlay_prev.positions, pos);
    overlay := overlay_prev.(sb := overlay_prev.sb.(states := sstates), positions := all_but_last(overlay_prev.positions) + [pos]);
  }

  lemma lemma_ExtendOverlayWithYielding<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc,
    pos:int,
    overlay_prev:StraightlineOverlay<State, Step, PC, Proc>
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
    requires last(overlay_prev.positions) == pos
    requires last(overlay_prev.sb.states).aux.phase.StraightlinePhaseNormal?
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
  {
    var ss := last(overlay_prev.sb.states);
    var StraightlineState(s, aux) := ss;
    var phase := aux.phase;
    var overlay_pos := |overlay_prev.sb.trace|;
    lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, overlay_pos);
    var pc := cr.get_actor_pc_stack(s, actor).v.pc;

    var sspec := GetStraightlineSpec(cr, actor, proc);
    var AnnotatedBehavior(sstates, strace) := overlay_prev.sb;
    var positions := overlay_prev.positions;

    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, overlay_pos);
    lemma_InvariantPredicateHoldsAtStep(b, last(overlay_prev.positions), cr.spec, cr.established_inv);

    var sstep := StraightlineStepYield();
    var aux2 := StraightlineUpdateAux(cr, last(sstates), actor, sstep, s);
    var sstate' := StraightlineState(s, aux2);
    assert StraightlineSpecNextYield(cr, last(sstates), sstate', sstep, actor, proc);
    assert StraightlineSpecNext(cr, last(sstates), sstate', sstep, actor, proc);
    lemma_ExtendStateNextSeqRight(sstates, strace, sspec.next, sstate', sstep);
    sstates := sstates + [sstate'];
    strace := strace + [sstep];
    lemma_ExtendSequenceMonotonic(positions, pos);
    positions := positions + [pos];

    overlay := overlay_prev.(sb := AnnotatedBehavior(sstates, strace), positions := positions);
  }

  lemma lemma_ExtendOverlayWithLooping<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc,
    pos:int,
    overlay_prev:StraightlineOverlay<State, Step, PC, Proc>
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires StraightlineOverlayValid(cr, overlay_prev, b, actor, proc)
    requires last(overlay_prev.positions) == pos
    requires last(overlay_prev.sb.states).aux.phase.StraightlinePhaseYielded?
    requires cr.get_actor_pc_stack(last(overlay_prev.sb.states).state, actor).Some?
    requires var s := last(overlay_prev.sb.states).state;
             var pc := cr.get_actor_pc_stack(s, actor).v.pc;
             cr.is_loop_head(pc)
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseLooped?
  {
    var ss := last(overlay_prev.sb.states);
    var StraightlineState(s, aux) := ss;
    var phase := aux.phase;
    var overlay_pos := |overlay_prev.sb.trace|;
    lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, overlay_pos);
    var pc := cr.get_actor_pc_stack(s, actor).v.pc;

    var sspec := GetStraightlineSpec(cr, actor, proc);
    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, overlay_pos);

    if pc in aux.visited_loops {
      lemma_VisitedLoopsOnlyContainsLoopHeads(cr, overlay_prev.sb, actor, proc, pc, overlay_pos);
      assert StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions(cr, overlay_prev.sb, actor, proc);
      var earlier_pos := lemma_FindWhenLoopBegan(cr, b, actor, proc, overlay_prev, pc, overlay_pos);
      var ss_earlier := overlay_prev.sb.states[earlier_pos];
      var sstep := overlay_prev.sb.trace[earlier_pos];
      var aux_new := StraightlineUpdateAux(cr, ss_earlier, actor, sstep, s);
      var ss_new := StraightlineState(s, aux_new);

      var states := overlay_prev.sb.states[..earlier_pos + 1] + [ss_new];
      var trace := overlay_prev.sb.trace[..earlier_pos] + [sstep];
      var positions := overlay_prev.positions[..earlier_pos + 1] + [pos];
      lemma_TakeSequenceMonotonic(overlay_prev.positions, earlier_pos + 1);
      lemma_UseSequenceMonotonic(overlay_prev.positions, earlier_pos, |overlay_prev.positions|-1);
      lemma_ExtendSequenceMonotonic(overlay_prev.positions[..earlier_pos + 1], pos);

      lemma_TakeStateNextSeq(overlay_prev.sb.states, overlay_prev.sb.trace, sspec.next, earlier_pos);

      lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
      lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, 0);
      lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, earlier_pos);
      lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_prev.sb, actor, proc, |overlay_prev.sb.states|-1);

      assert StraightlineSpecNextLoopModifies(cr, ss_earlier, ss_new, sstep, actor, proc, pc);
      assert StraightlineSpecNext(cr, ss_earlier, ss_new, sstep, actor, proc);
      lemma_ExtendStateNextSeqRight(overlay_prev.sb.states[..earlier_pos + 1], overlay_prev.sb.trace[..earlier_pos], sspec.next,
                                    ss_new, sstep);
      var sb := AnnotatedBehavior(states, trace);
      assert AnnotatedBehaviorSatisfiesSpec(sb, sspec);

      overlay := StraightlineOverlay(sb, overlay_prev.how_started, positions);
    }
    else {
      var AnnotatedBehavior(sstates, strace) := overlay_prev.sb;
      var positions := overlay_prev.positions;
      var sstep0 := StraightlineStepLoopModifies(pc);
      var aux1 := StraightlineUpdateAux(cr, last(sstates), actor, sstep0, s);
      var sstate1 := StraightlineState(s, aux1);

      lemma_InvariantPredicateHoldsAtStep(b, last(overlay_prev.positions), cr.spec, cr.established_inv);

      assert StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions(cr, overlay_prev.sb, actor, proc);
      assert StraightlineSpecNextLoopModifies(cr, last(sstates), sstate1, sstep0, actor, proc, pc);
      assert StraightlineSpecNext(cr, last(sstates), sstate1, sstep0, actor, proc);
      lemma_ExtendStateNextSeqRight(sstates, strace, sspec.next, sstate1, sstep0);
      sstates := sstates + [sstate1];
      strace := strace + [sstep0];
      lemma_ExtendSequenceMonotonic(positions, pos);
      positions := positions + [pos];

      overlay := overlay_prev.(sb := AnnotatedBehavior(sstates, strace), positions := positions);
    }
  }

  ///////////////////////////////////////////////
  // Cases of obtaining straightline behaviors
  ///////////////////////////////////////////////

  lemma lemma_GetStraightlineBehaviorCaseInit<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires cr.get_actor_pc_stack(b.states[0], actor).Some?
    requires ActorInProc(cr, b.states[0], actor, proc)
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, 0)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
  {
    var positions := [0];
    lemma_EstablishSequenceMonotonic(positions);
    var s := b.states[0];

    assert ActorsBeginAtEntryPointsWithEmptyStacksConditions(cr, s, actor);
    assert RequiresClausesSatisfiedInitiallyConditions(cr, s, actor);

    var ss := StraightlineState(s, StraightlineInitAux());
    var sb := AnnotatedBehavior([ss], []);
    lemma_InvariantPredicateHoldsAtStart(s, cr.spec, cr.established_inv);

    assert StraightlineSpecInit(cr, sb.states[0], actor, proc);

    var overlay_prev := StraightlineOverlay(sb, HowStartedInit, [0]);
    overlay := lemma_ExtendOverlayWithYielding(cr, b, actor, proc, 0, overlay_prev);
  }

  lemma lemma_GetStraightlineBehaviorCaseNormal<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.step_to_actor(b.trace[pos-1]).Some?
    requires cr.step_to_actor(b.trace[pos-1]).v == actor
    requires cr.step_to_effect(b.trace[pos-1]).CHLStepEffectNormal?
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 1
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    assert ActionTuple(s, s', step) in cr.spec.next;

    var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    var pc' := cr.get_actor_pc_stack(s', actor).v.pc;
    assert cr.pc_to_proc(pc') == cr.pc_to_proc(pc);

    var overlay_prev := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos-1, actor, proc);
    assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_prev.sb, step, s');
    assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, overlay_prev.sb, step, s');
    if cr.is_loop_head(pc) {
      overlay_prev := lemma_ExtendOverlayWithLooping(cr, b, actor, proc, pos-1, overlay_prev);
    }

    var sspec := GetStraightlineSpec(cr, actor, proc);
    var sstates := overlay_prev.sb.states;
    var strace := overlay_prev.sb.trace;
    var ss := last(sstates);
    var sstep := StraightlineStepNormal(step);
    var aux := ss.aux;
    var aux' := StraightlineUpdateAux(cr, ss, actor, sstep, s');
    var ss' := StraightlineState(s', aux');
    var overlay_pos := |overlay_prev.sb.states| - 1;

    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, overlay_pos);
    lemma_PCVisitedIfInLoopedPhase(cr, overlay_prev.sb, actor, proc, overlay_pos);
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    assert StraightlineSpecNextNormal(cr, last(sstates), ss', sstep, actor, proc, step);
    lemma_ExtendStateNextSeqRight(sstates, strace, sspec.next, ss', sstep);
    var sb_next := AnnotatedBehavior(sstates + [ss'], strace + [sstep]);
    var positions := overlay_prev.positions + [pos];
    lemma_ExtendSequenceMonotonic(overlay_prev.positions, pos);
    var overlay_next := StraightlineOverlay(sb_next, overlay_prev.how_started, positions);
    
    overlay := lemma_ExtendOverlayWithYielding(cr, b, actor, proc, pos, overlay_next);
  }

  lemma lemma_GetStraightlineBehaviorCaseFork<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires cr.get_actor_pc_stack(b.states[pos-1], actor).None?
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires cr.step_to_actor(b.trace[pos-1]).Some?
    requires cr.step_to_actor(b.trace[pos-1]).v != actor
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 0
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    var effect := cr.step_to_effect(step);
    assert ActionTuple(s, s', step) in cr.spec.next;

    var pc' := cr.get_actor_pc_stack(s', actor).v.pc;
    var forker_actor := cr.step_to_actor(step).v;
    var PCStack(forker_pc, forker_stack) := cr.get_actor_pc_stack(s, forker_actor).v;

    assert ForkedActorsStartAtEntryPointsWithEmptyStacksConditions(cr, s, s', step, actor);
    assert !effect.CHLStepEffectExit?;
    var forker_proc, forker_overlay;
    if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? {
      var overlay_alt := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, prev, forker_actor, cr.pc_to_proc(forker_pc));
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_alt.sb, step, s');
      forker_proc := forker_stack[0];
      forker_overlay := lemma_GetStraightlineBehaviorForCallerProc(cr, b, prev, forker_actor, forker_proc);
    }
    else {
      forker_proc := cr.step_to_proc(step);
      forker_overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, prev, forker_actor, forker_proc);
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, forker_overlay.sb, step, s');
    }

    assert StraightlineBehaviorsSatisfyPreconditionsForForksConditions(cr, forker_overlay.sb, step, s', actor);
    assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, forker_overlay.sb, step, s');
    assert cr.global_inv(s');

    var myb := forker_overlay.sb;
    assert AnnotatedBehaviorSatisfiesSpec(myb, GetStraightlineSpec(cr, forker_actor, forker_proc));
    assert ActionTuple(s, s', step) in cr.spec.next;
    assert cr.step_to_actor(step).v == forker_actor;
    assert cr.get_actor_pc_stack(s, forker_actor).Some?;
    assert cr.get_actor_pc_stack(s, actor).None?;
    assert cr.get_actor_pc_stack(s', actor).Some?;
    assert pc' == cr.get_actor_pc_stack(s', actor).v.pc;
    assert proc == cr.pc_to_proc(pc');
    assert cr.requires_clauses(proc, s', actor);

    var ss := StraightlineState(s', StraightlineInitAux());
    var overlay_prev := StraightlineOverlay(AnnotatedBehavior([ss], []), HowStartedFork, [pos]);
    lemma_EstablishSequenceMonotonic(overlay_prev.positions);
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);

    assert IsForkStep(cr, actor, s);
    assert StraightlineSpecInit(cr, ss, actor, proc);
    assert StraightlineOverlayValid(cr, overlay_prev, b, actor, proc);

    overlay := lemma_ExtendOverlayWithYielding(cr, b, actor, proc, pos, overlay_prev);
  }

  lemma lemma_GetStraightlineBehaviorCaseOtherActor<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.step_to_actor(b.trace[pos-1]).Some?
    requires cr.step_to_actor(b.trace[pos-1]).v != actor
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 1
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    assert ActionTuple(s, s', step) in cr.spec.next;

    if cr.get_actor_pc_stack(s, actor).None? {
      overlay := lemma_GetStraightlineBehaviorCaseFork(cr, b, pos, actor, proc);
      return;
    }

    var other_actor := cr.step_to_actor(step).v;
    var PCStack(other_pc, other_stack) := cr.get_actor_pc_stack(s, other_actor).v;
    var effect := cr.step_to_effect(step);

    var other_proc, overlay_other;
    if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? {
      var overlay_alt := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos - 1, other_actor, cr.pc_to_proc(other_pc));
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_alt.sb, step, s');
      other_proc := other_stack[0];
      overlay_other := lemma_GetStraightlineBehaviorForCallerProc(cr, b, pos - 1, other_actor, other_proc);
    }
    else {
      other_proc := cr.step_to_proc(step);
      overlay_other := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos - 1, other_actor, other_proc);
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_other.sb, step, s');
    }

    assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, overlay_other.sb, step, s');
    assert StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, overlay_other.sb, step, s', actor);
    assert StepsDontChangeOtherActorsExceptViaForkConditions(cr, s, s', step, actor);
    var overlay_prev := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos - 1, actor, proc);

    overlay := lemma_ExtendYieldingOverlayOneStep(cr, b, actor, proc, pos, overlay_prev);
  }

  lemma lemma_GetStraightlineBehaviorCaseActorless<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.step_to_actor(b.trace[pos-1]).None?
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 1
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    assert ActionTuple(s, s', step) in cr.spec.next;

    lemma_InvariantPredicateHoldsAtStep(b, prev, cr.spec, cr.established_inv);
    assert ActorlessStepsDontChangeActorsConditions(cr, s, s', step, actor);
    var overlay_prev := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos-1, actor, proc);

    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, |overlay_prev.sb.states|-1);
    assert ActorlessStepsMaintainYieldPredicateAndGlobalInvariantConditions(cr, s, s', step, actor);

    overlay := lemma_ExtendYieldingOverlayOneStep(cr, b, actor, proc, pos, overlay_prev);
  }

  lemma lemma_GetStraightlineBehaviorCaseCall<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.step_to_actor(b.trace[pos-1]).Some?
    requires cr.step_to_actor(b.trace[pos-1]).v == actor
    requires var effect := cr.step_to_effect(b.trace[pos-1]); effect.CHLStepEffectCall? || effect.CHLStepEffectReturnThenCall?
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 1
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    assert ActionTuple(s, s', step) in cr.spec.next;
    var effect := cr.step_to_effect(step);
    var pc' := cr.get_actor_pc_stack(s', actor).v.pc;

    var caller_pc := cr.get_actor_pc_stack(s, actor).v.pc;
    var caller_proc := cr.step_to_proc(step);
    var caller_overlay;
    if effect.CHLStepEffectCall? {
      caller_overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos-1, actor, caller_proc);
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, caller_overlay.sb, step, s');
    }
    else {
      var overlay_alt := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos-1, actor, cr.pc_to_proc(caller_pc));
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_alt.sb, step, s');
      caller_overlay := lemma_GetStraightlineBehaviorForCallerProc(cr, b, pos-1, actor, caller_proc);
    }

    assert StraightlineBehaviorsSatisfyPreconditionsForCallsConditions(cr, caller_overlay.sb, step, s');
    assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, caller_overlay.sb, step, s');
    assert cr.requires_clauses(proc, s', actor);
    assert cr.global_inv(s');

    var positions := [pos];
    lemma_EstablishSequenceMonotonic(positions);

    var ss := StraightlineState(s', StraightlineInitAux());
    var sb := AnnotatedBehavior([ss], []);
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);

    var overlay_prev := StraightlineOverlay(sb, HowStartedCall, positions);
    assert StraightlineSpecInit(cr, ss, actor, proc);
    overlay := lemma_ExtendOverlayWithYielding(cr, b, actor, proc, pos, overlay_prev);
  }

  lemma lemma_GetStraightlineBehaviorCaseReturn<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 < pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires ActorInProc(cr, b.states[pos], actor, proc)
    requires cr.step_to_actor(b.trace[pos-1]).Some?
    requires cr.step_to_actor(b.trace[pos-1]).v == actor
    requires cr.step_to_effect(b.trace[pos-1]).CHLStepEffectReturn?
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 1
  {
    var prev := pos-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    assert ActionTuple(s, s', step) in cr.spec.next;
    assert s' == b.states[pos];

    var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
    var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;

    var caller_proc := cr.pc_to_proc(pc);
    var caller_overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos-1, actor, caller_proc);
    assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, caller_overlay.sb, step, s');

    var overlay_prev := lemma_GetStraightlineBehaviorForCallerProc(cr, b, pos-1, actor, proc);

    var sspec := GetStraightlineSpec(cr, actor, proc);
    var sstates := overlay_prev.sb.states;
    var strace := overlay_prev.sb.trace;
    var ss := last(sstates);
    var aux := ss.aux;
    var sstep := StraightlineStepReturn(step);
    var aux' := StraightlineUpdateAux(cr, ss, actor, sstep, s');
    var ss' := StraightlineState(s', aux');
    var overlay_pos := |overlay_prev.sb.states| - 1;

    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_prev.sb, actor, proc, overlay_pos);
    lemma_PCVisitedIfInLoopedPhase(cr, overlay_prev.sb, actor, proc, overlay_pos);
    assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, overlay_prev.sb, step, s');
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    assert StraightlineSpecNextReturn(cr, last(sstates), ss', sstep, actor, proc, step);
    lemma_ExtendStateNextSeqRight(sstates, strace, sspec.next, ss', sstep);
    var sb_next := AnnotatedBehavior(sstates + [ss'], strace + [sstep]);
    var positions := overlay_prev.positions + [pos];
    lemma_ExtendSequenceMonotonic(overlay_prev.positions, pos);
    var overlay_next := StraightlineOverlay(sb_next, overlay_prev.how_started, positions);
    
    overlay := lemma_ExtendOverlayWithYielding(cr, b, actor, proc, pos, overlay_next);
  }

  ///////////////////////////////////////////
  // Obtaining straightline behaviors
  ///////////////////////////////////////////

  lemma lemma_GetStraightlineBehaviorForCallerProc<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 <= pos < |b.states|
    requires cr.state_ok(b.states[pos])
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires var PCStack(pc, stack) := cr.get_actor_pc_stack(b.states[pos], actor).v;
             |stack| > 0 && stack[0] == proc && cr.is_return_site(pc)
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseEnsured?
    decreases pos, 3
  {
    var s := b.states[pos];
    var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
    var callee := cr.pc_to_proc(pc);
    var overlay_alt := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos, actor, callee);
    lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_alt.sb, actor, callee, 0);
    lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_alt.sb, actor, callee, |overlay_alt.sb.states|-1);

    var call_pos := overlay_alt.positions[0] - 1;

    if overlay_alt.how_started.HowStartedInit? {
      assert ActorsBeginAtEntryPointsWithEmptyStacksConditions(cr, b.states[overlay_alt.positions[0]], actor);
      assert false;
    }

    var call_s := b.states[call_pos];
    var call_s' := b.states[call_pos+1];
    var call_step := b.trace[call_pos];
    assert ActionTuple(call_s, call_s', call_step) in cr.spec.next;
    
    if overlay_alt.how_started.HowStartedFork? {
      assert ForkedActorsStartAtEntryPointsWithEmptyStacksConditions(cr, call_s, call_s', call_step, actor);
      assert false;
    }

    assert overlay_alt.how_started.HowStartedCall?;
    assert IsCallStep(cr, actor, call_step);

    assert proc == cr.step_to_proc(call_step);
    var call_effect := cr.step_to_effect(call_step);
    assert call_effect.CHLStepEffectCall? || call_effect.CHLStepEffectReturnThenCall?;
    var simple_call := call_effect.CHLStepEffectCall?;

    assert cr.requires_clauses(callee, call_s', actor);

    assert StraightlineBehaviorsSatisfyPostconditionsConditions(cr, overlay_alt.sb, actor, callee);
    assert cr.ensures_clauses(callee, overlay_alt.sb.states[0].state, last(overlay_alt.sb.states).state, actor);
    assert cr.ensures_clauses(callee, call_s', s, actor);

    lemma_UseSequenceMonotonic(overlay_alt.positions, 0, |overlay_alt.positions|-1);
    lemma_StraightlineBehaviorNeverChangesStack(cr, overlay_alt.sb, actor, callee, |overlay_alt.sb.states| - 1);
    var overlay_prev;
    if simple_call {
      overlay_prev := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, call_pos, actor, proc);
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay_prev.sb, call_step, call_s');
      assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, overlay_prev.sb, call_step, call_s');
      if cr.is_loop_head(cr.get_actor_pc_stack(call_s, actor).v.pc) {
        overlay_prev := lemma_ExtendOverlayWithLooping(cr, b, actor, proc, call_pos, overlay_prev);
      }
    }
    else {
      var caller_pc := cr.get_actor_pc_stack(call_s, actor).v.pc;
      var caller_proc := cr.pc_to_proc(caller_pc);
      var caller_overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, call_pos, actor, caller_proc);
      assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, caller_overlay.sb, call_step, call_s');
      overlay_prev := lemma_GetStraightlineBehaviorForCallerProc(cr, b, call_pos, actor, proc);
      assert StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, overlay_prev.sb, call_step, call_s');
    }

    var sspec := GetStraightlineSpec(cr, actor, proc);
    var sstates := overlay_prev.sb.states;
    var strace := overlay_prev.sb.trace;
    var positions := overlay_prev.positions;

    var sstep0;
    if simple_call {
      sstep0 := StraightlineStepCall(call_step);
    }
    else {
      sstep0 := StraightlineStepReturnThenCall(call_step);
    }
    var aux0 := StraightlineUpdateAux(cr, last(sstates), actor, sstep0, call_s');
    var sstate0 := StraightlineState(call_s', aux0);

    var sstep1 := StraightlineStepEnsures(callee);
    var aux1 := StraightlineUpdateAux(cr, sstate0, actor, sstep1, s);
    var sstate1 := StraightlineState(s, aux1);

    var overlay_pos := |overlay_prev.sb.states| - 1;
    lemma_ExtendSequenceMonotonic(positions, call_pos + 1);
    lemma_PCVisitedIfInLoopedPhase(cr, overlay_prev.sb, actor, proc, overlay_pos);
    if simple_call {
      assert StraightlineSpecNextCall(cr, last(sstates), sstate0, sstep0, actor, proc, call_step);
    }
    else {
      assert StraightlineSpecNextReturnThenCall(cr, last(sstates), sstate0, sstep0, actor, proc, call_step);
    }
    assert StraightlineSpecNext(cr, last(sstates), sstate0, sstep0, actor, proc);
    lemma_ExtendStateNextSeqRight(sstates, strace, sspec.next, sstate0, sstep0);

    lemma_ExtendSequenceMonotonic(positions + [call_pos + 1], pos);
    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay_alt.sb, actor, callee, |overlay_alt.sb.states| - 1);
    lemma_InvariantPredicateHoldsAtStep(b, pos, cr.spec, cr.established_inv);
    assert StraightlineSpecNextEnsures(cr, sstate0, sstate1, sstep1, actor, proc, callee);
    assert StraightlineSpecNext(cr, sstate0, sstate1, sstep1, actor, proc);
    lemma_ExtendStateNextSeqRight(sstates + [sstate0], strace + [sstep0], sspec.next, sstate1, sstep1);

    var sb := AnnotatedBehavior(sstates + [sstate0] + [sstate1], strace + [sstep0] + [sstep1]);
    overlay := StraightlineOverlay(sb, overlay_prev.how_started, positions + [call_pos + 1] + [pos]);
  }

  lemma lemma_GetStraightlineBehaviorForCurrentProc<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    actor:Actor,
    proc:Proc
    ) returns (
    overlay:StraightlineOverlay<State, Step, PC, Proc>
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 <= pos < |b.states|
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires cr.state_ok(b.states[pos])
    requires ActorInProc(cr, b.states[pos], actor, proc)
    ensures  StraightlineOverlayLeadsToPos(cr, overlay, b, actor, proc, pos)
    ensures  last(overlay.sb.states).aux.phase.StraightlinePhaseYielded?
    decreases pos, 2
  {
    if pos == 0 {
      overlay := lemma_GetStraightlineBehaviorCaseInit(cr, b, actor, proc);
      return;
    }

    var prev := pos-1;
    var step := b.trace[prev];
    
    if cr.step_to_actor(step).Some? && cr.step_to_actor(step).v != actor {
      overlay := lemma_GetStraightlineBehaviorCaseOtherActor(cr, b, pos, actor, proc);
      return;
    }

    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cr.spec.next;

    var effect := cr.step_to_effect(step);
    match effect {
      case CHLStepEffectNormal =>            overlay := lemma_GetStraightlineBehaviorCaseNormal(cr, b, pos, actor, proc);
      case CHLStepEffectCall(_) =>           overlay := lemma_GetStraightlineBehaviorCaseCall(cr, b, pos, actor, proc);
      case CHLStepEffectReturnThenCall(_) => overlay := lemma_GetStraightlineBehaviorCaseCall(cr, b, pos, actor, proc);
      case CHLStepEffectReturn =>            overlay := lemma_GetStraightlineBehaviorCaseReturn(cr, b, pos, actor, proc);
      case CHLStepEffectActorless =>         overlay := lemma_GetStraightlineBehaviorCaseActorless(cr, b, pos, actor, proc);
      case CHLStepEffectExit =>              assert false;
    }
  }

}
