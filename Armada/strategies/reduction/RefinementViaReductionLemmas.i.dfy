/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains lemmas useful in effecting a refinement via reduction on a behavior.  They
// support lemma_PerformRefinementViaReduction (in RefinementViaReduction.i.dfy).
//
// The general strategy is as follows.  We create a cross-level specification that bridges the gap
// between the low-level spec and the high-level spec.  We then:
// (1) Lift the given low-level behavior to produce a cross-level behavior.
// (2) Use the Cohen-Lamport reduction library to reduce that to another cross-level behavior.
// (3) Lift the resulting cross-level behavior to produce a high-level behavior.
//
// The cross-level specification has two types of steps: Low and Reducible.  A Low step consists of
// a single low-level step, while a Reducible step consists of a reducible sequence of low-level
// steps.
//
// It's easy to lift a low-level behavior to produce a cross-level behavior, since it just involves
// converting every step into a Low step.
//
// The cross-level specification satisfies the conditions required by the Cohen-Lamport reduction
// library, since it provides the ability to lift any reducible sequence of steps to another step in
// the same specification (by turning them into a Reducible step).
//
// Finally, once the Cohen-Lamport reduction library has finished with the cross-level behavior,
// it's easy to lift it to the high-level spec.  After all, all the non-liftable steps (the ones
// that start or end in phase 1 or 2) have been eliminated.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "RefinementViaReductionSpec.i.dfy"
include "CohenLamportReductionSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"

module RefinementViaReductionLemmasModule {

  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened RefinementViaReductionSpecModule
  import opened CohenLamportReductionSpecModule
  import opened util_collections_seqs_i

  ///////////////////////////////////////////
  // CrossLevel spec
  ///////////////////////////////////////////

  datatype PhaseType = PhaseType1 | PhaseType2 | PhaseTypeNeither
  datatype MoverType = MoverTypeRight | MoverTypeLeft | MoverTypeNonmover | MoverTypeExternal | MoverTypeImpossible

  datatype CrossLevelStep<State, Actor, LStep> =
    | Low(actor:Actor, step:LStep)
    | Reducible(actor:Actor, states:seq<State>, trace:seq<LStep>)

  predicate ValidReducibleCrossLevelStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<LStep>,
    actor:Actor
    )
  {
    && StateNextSeq(states, trace, rr.lspec.next)
    && (forall step :: step in trace ==> rr.idmap(step) == actor)
    && |states| > 1
    && !rr.phase1(states[0], actor)
    && !rr.phase2(states[0], actor)
    && (var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor))
    && (forall i :: 0 <= i < |trace| ==> !rr.crashed(states[i]))
    && (forall i :: 0 < i < |trace| ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor))
  }

  predicate CrossLevelNext<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    s':State,
    cstep:CrossLevelStep<State, Actor, LStep>
    )
  {
    match cstep
      case Low(actor, step) =>
        !rr.crashed(s) && ActionTuple(s, s', step) in rr.lspec.next && actor == rr.idmap(step)
      case Reducible(actor, states, trace) =>
        ValidReducibleCrossLevelStep(rr, states, trace, actor) && states[0] == s && last(states) == s'
  }

  function GetCrossLevelSpec<State(!new), Actor(!new), LStep(!new), HStep(!new)>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    ) : AnnotatedBehaviorSpec<State, CrossLevelStep<State, Actor, LStep>>
  {
    AnnotatedBehaviorSpec(rr.lspec.init,
                          iset s, s', step | CrossLevelNext(rr, s, s', step) :: ActionTuple(s, s', step))
  }

  function GetIdentityRelation<State(!new)>() : RefinementRelation<State, State>
  {
    iset s | true :: RefinementPair(s, s)
  }

  lemma lemma_StateInCrossLevelBehaviorReachableInBaseSpec<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    b:AnnotatedBehavior<State, CrossLevelStep<State, Actor, LStep>>,
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires AnnotatedBehaviorSatisfiesSpec(b, GetCrossLevelSpec(rr))
    requires 0 <= pos < |b.states|
    ensures  b.states[pos] in AnnotatedReachables(rr.lspec)
    decreases pos
  {
    var cspec := GetCrossLevelSpec(rr);

    if pos == 0 {
      assert b.states[pos] in cspec.init;
      assert b.states[pos] in rr.lspec.init;
      assert AnnotatedReachables(rr.lspec) == AnnotatedReachablesPremium(rr.lspec);
      return;
    }

    var prev := pos-1;
    lemma_StateInCrossLevelBehaviorReachableInBaseSpec(rr, b, prev);
    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in cspec.next;
    if b.trace[prev].Low? {
      lemma_NextMaintainsAnnotatedReachables(b.states[prev], b.states[prev+1], b.trace[prev].step, rr.lspec);
    }
    else {
      lemma_StateNextSeqMaintainsAnnotatedReachables(b.trace[prev].states, b.trace[prev].trace, rr.lspec);
      assert last(b.trace[prev].states) == b.states[prev+1];
      assert b.states[prev+1] in b.trace[prev].states;
    }
  }

  lemma lemma_AnnotatedReachablesOfCrossLevelSpec<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    ensures  AnnotatedReachables(GetCrossLevelSpec(rr)) == AnnotatedReachables(rr.lspec)
  {
    var cspec := GetCrossLevelSpec(rr);
    reveal AnnotatedReachables();

    forall s | s in AnnotatedReachables(rr.lspec)
      ensures s in AnnotatedReachables(cspec)
    {
      var ab :| AnnotatedBehaviorSatisfiesSpec(ab, rr.lspec) && last(ab.states) == s;
      var cb := lemma_LiftBehaviorToCrossLevel(rr, ab);
      assert AnnotatedBehaviorSatisfiesSpec(cb, cspec);
      var relation := GetIdentityRelation<State>();
      var ac_map :| BehaviorRefinesBehaviorUsingRefinementMap(ab.states, cb.states, relation, ac_map);
      assert last(ac_map).last == |cb.states|-1;
      assert RefinementPair(last(ab.states), last(cb.states)) in relation;
    }

    forall s | s in AnnotatedReachables(cspec)
      ensures s in AnnotatedReachables(rr.lspec)
    {
      var cb :| AnnotatedBehaviorSatisfiesSpec(cb, cspec) && last(cb.states) == s;
      lemma_StateInCrossLevelBehaviorReachableInBaseSpec(rr, cb, |cb.states|-1);
    }
  }

  function LiftStepToCrossLevel<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    s':State,
    step:LStep
    ) : CrossLevelStep<State, Actor, LStep>
  {
    Low(rr.idmap(step), step)
  }

  lemma lemma_LiftStateNextSeqToCrossLevel<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    states:seq<State>,
    ltrace:seq<LStep>
    ) returns (
    htrace:seq<CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires StateNextSeq(states, ltrace, rr.lspec.next)
    requires !rr.crashed(last(states))
    ensures  StateNextSeq(states, htrace, clrr.spec.next)
    ensures  forall state :: state in states ==> !rr.crashed(state)
    ensures  forall i :: 0 <= i < |htrace| ==> htrace[i] == Low(rr.idmap(ltrace[i]), ltrace[i])
  {
    forall i | 0 <= i < |states|
      ensures !rr.crashed(states[i])
    {
      if rr.crashed(states[i]) {
        lemma_AllStatesFollowingCrashedStateSame(rr, states, ltrace, i);
        assert states[i] == last(states);
        assert false;
      }
    }

    htrace := MapSeqToSeq(ltrace, x => Low(rr.idmap(x), x));

    forall i {:trigger ActionTuple(states[i], states[i+1], htrace[i]) in clrr.spec.next} | 0 <= i < |htrace|
      ensures ActionTuple(states[i], states[i+1], htrace[i]) in clrr.spec.next
    {
      assert ActionTuple(states[i], states[i+1], ltrace[i]) in rr.lspec.next;
      assert htrace[i].Low?;
      assert !rr.crashed(states[i]);
      assert htrace[i].actor == rr.idmap(htrace[i].step);
      assert CrossLevelNext(rr, states[i], states[i+1], htrace[i]);
    }
  }

  lemma lemma_FindFirstCrashingState<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<LStep>
    ) returns (
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, rr.lspec.next)
    ensures  0 <= pos <= |states|
    ensures  forall i :: 0 <= i < pos ==> !rr.crashed(states[i])
    ensures  pos < |states| ==> rr.crashed(states[pos])
    ensures  pos < |states| ==> forall i :: pos < i < |states| ==> states[i] == states[pos]
  {
    pos := 0;

    while pos < |trace| && !rr.crashed(states[pos])
      invariant 0 <= pos <= |trace|
      invariant forall i :: 0 <= i < pos ==> !rr.crashed(states[i])
    {
      assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rr.lspec.next;
      pos := pos + 1;
    }

    if pos == |trace| {
      if !rr.crashed(states[pos]) {
        pos := pos + 1;
      }
      return;
    }

    var j := pos;
    while j < |trace|
      invariant pos <= j <= |trace|
      invariant forall i :: pos <= i <= j ==> states[i] == states[pos]
    {
      assert ActionTuple(states[j], states[j+1], trace[j]) in rr.lspec.next;
      j := j + 1;
    }
  }

  lemma lemma_LiftBehaviorToCrossLevel<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    lb:AnnotatedBehavior<State, LStep>
    ) returns (
    hb:AnnotatedBehavior<State, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, rr.lspec)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, GetIdentityRelation<State>())
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, GetCrossLevelSpec(rr))
  {
    var pos := lemma_FindFirstCrashingState(rr, lb.states, lb.trace);
    var relation := GetIdentityRelation<State>();

    if pos == |lb.states| {
      var htrace := ConvertMapToSeq(|lb.trace|,
                                    map i | 0 <= i < |lb.trace| :: LiftStepToCrossLevel(rr, lb.states[i], lb.states[i+1], lb.trace[i]));
      hb := AnnotatedBehavior(lb.states, htrace);
      var lh_map := ConvertMapToSeq(|lb.states|, map i | 0 <= i < |lb.states| :: RefinementRange(i, i));
      assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, relation, lh_map);
    }
    else {
      var htrace := ConvertMapToSeq(pos, map i | 0 <= i < pos :: LiftStepToCrossLevel(rr, lb.states[i], lb.states[i+1], lb.trace[i]));
      hb := AnnotatedBehavior(lb.states[..pos+1], htrace);
      var lh_map := ConvertMapToSeq(|lb.states|,
                                    map i | 0 <= i < |lb.states| :: if i <= pos then RefinementRange(i, i) else RefinementRange(pos, pos));
      assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, relation, lh_map);
    }
  }

  lemma lemma_LiftBehaviorToHighLayer<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    cb:AnnotatedBehavior<State, CrossLevelStep<State, Actor, LStep>>
    ) returns (
    hb:AnnotatedBehavior<State, HStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires AnnotatedBehaviorSatisfiesSpec(cb, GetCrossLevelSpec(rr))
    requires forall i, actor :: 0 <= i < |cb.states| ==> var s := cb.states[i]; !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    ensures  hb.states == cb.states
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, rr.hspec)
  {
    var cspec := GetCrossLevelSpec(rr);
    var htrace := [];
    var n := 0;

    assert |cb.states| == |cb.trace| + 1;

    while n < |cb.trace|
      invariant 0 <= n <= |cb.trace|
      invariant |htrace| == n
      invariant forall i :: 0 <= i < n ==> ActionTuple(cb.states[i], cb.states[i+1], htrace[i]) in rr.hspec.next
    {
      assert ActionTuple(cb.states[n], cb.states[n+1], cb.trace[n]) in cspec.next;
      var cstep := cb.trace[n];
      var states:seq<State>, trace:seq<LStep>, actor:Actor;

      if cstep.Low? {
        states := [cb.states[n], cb.states[n+1]];
        trace := [cstep.step];
        actor := rr.idmap(cstep.step);
      }
      else {
        states := cstep.states;
        trace := cstep.trace;
        actor := cstep.actor;
      }

      assert RefinementViaReductionSpecModule.ActionSequencesLiftableConditions(rr, states, trace, actor);
      var hstep :| ActionTuple(states[0], last(states), hstep) in rr.hspec.next;
      htrace := htrace + [hstep];
      n := n + 1;
    }

    hb := AnnotatedBehavior(cb.states, htrace);
  }

  lemma lemma_StateInCSpecBehaviorAmongAnnotatedReachables<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    b:AnnotatedBehavior<State, CrossLevelStep<State, Actor, LStep>>,
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires AnnotatedBehaviorSatisfiesSpec(b, GetCrossLevelSpec(rr))
    requires 0 <= pos < |b.states|
    ensures  b.states[pos] in AnnotatedReachables(GetCrossLevelSpec(rr))
    ensures  b.states[pos] in AnnotatedReachables(rr.lspec)
  {
    var cspec := GetCrossLevelSpec(rr);
    var ar := AnnotatedReachablesPremium(cspec);

    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);

    if pos > 0 {
      var prev_pos := pos - 1;
      assert ActionTuple(b.states[prev_pos], b.states[prev_pos+1], b.trace[prev_pos]) in cspec.next;
      lemma_StateInCSpecBehaviorAmongAnnotatedReachables(rr, b, prev_pos);
      assert b.states[prev_pos] in AnnotatedReachables(cspec);
      assert b.states[prev_pos+1] in AnnotatedReachables(cspec);
    }
  }

  ///////////////////////////////////////////
  // GENERAL CRASH LEMMAS
  ///////////////////////////////////////////

  lemma lemma_StateNextSeqPreservesCrash<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, rr.lspec.next)
    requires rr.crashed(states[0])
    ensures  last(states) == states[0]
  {
    if |states| > 1 {
      var zero := 0;
      assert ActionTuple(states[zero], states[zero+1], trace[zero]) in rr.lspec.next;
      assert rr.crashed(states[zero+1]);
      assert states[zero+1] == states[zero];

      var states' := states[1..];
      var trace' := trace[1..];

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in rr.lspec.next} | 0 <= i < |trace'|
        ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in rr.lspec.next
      {
        var iplus := i+1;
        assert states'[i] == states[iplus];
        assert states'[i+1] == states[iplus+1];
        assert trace'[i] == trace[iplus];
        assert ActionTuple(states[iplus], states[iplus+1], trace[iplus]) in rr.lspec.next;
      }
      
      lemma_StateNextSeqPreservesCrash(rr, states', trace');
    }
  }

  lemma lemma_CSpecNextPreservesCrash<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    s':State,
    step:CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires ActionTuple(s, s', step) in GetCrossLevelSpec(rr).next
    requires rr.crashed(s)
    ensures  s' == s
  {
    if step.Reducible? {
      lemma_StateNextSeqPreservesCrash(rr, step.states, step.trace);
    }
  }

  lemma lemma_AllStatesFollowingCrashedStateSame<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<LStep>,
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, rr.lspec.next)
    requires 0 <= pos < |states|
    requires rr.crashed(states[pos])
    ensures  forall i :: pos <= i < |states| ==> states[i] == states[pos]
    decreases |states|-pos
  {
    if pos < |states|-1 {
      assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rr.lspec.next;
      assert rr.crashed(states[pos+1]);
      assert states[pos+1] == states[pos];
      lemma_AllStatesFollowingCrashedStateSame(rr, states, trace, pos+1);
    }
  }

  lemma lemma_AllCSpecStatesFollowingCrashedStateSame<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<CrossLevelStep<State, Actor, LStep>>,
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, GetCrossLevelSpec(rr).next)
    requires 0 <= pos < |states|
    requires rr.crashed(states[pos])
    ensures  forall i :: pos <= i < |states| ==> states[i] == states[pos]
    decreases |states|-pos
  {
    var cspec := GetCrossLevelSpec(rr);
    if pos < |states|-1 {
      lemma_CSpecNextPreservesCrash(rr, states[pos], states[pos+1], trace[pos]);
      assert rr.crashed(states[pos+1]);
      lemma_AllCSpecStatesFollowingCrashedStateSame(rr, states, trace, pos+1);
    }
  }

  lemma lemma_CSpecNextPreservesNoncrashBackward<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    s':State,
    step:CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires ActionTuple(s, s', step) in GetCrossLevelSpec(rr).next
    requires !rr.crashed(s')
    ensures  !rr.crashed(s)
  {
    if rr.crashed(s) {
      lemma_CSpecNextPreservesCrash(rr, s, s', step);
      assert false;
    }
  }

  lemma lemma_IfStateNextSeqDoesntCrashNoStateDoes<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    states:seq<State>,
    trace:seq<LStep>,
    pos:int
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, rr.lspec.next)
    requires !rr.crashed(last(states))
    requires 0 <= pos < |states|
    ensures  !rr.crashed(states[pos])
  {
    if pos < |states|-1 {
      var penult := |states|-2;
      assert ActionTuple(states[penult], states[penult+1], trace[penult]) in rr.lspec.next;
      assert !rr.crashed(states[penult]);
      lemma_LastOfAllButLast(states);
      lemma_IfStateNextSeqDoesntCrashNoStateDoes(rr, all_but_last(states), all_but_last(trace), pos);
    }
  }

  ///////////////////////////////////////////
  // CohenLamportReductionRequest
  ///////////////////////////////////////////

  function GetCohenLamportReductionIdmap<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    ) : CrossLevelStep<State, Actor, LStep>->Actor
  {
    (s:CrossLevelStep<State, Actor, LStep>) => s.actor
  }

  function GetCohenLamportReductionRequest<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    ) : CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
  {
    CohenLamportReductionRequest(GetCrossLevelSpec(rr), rr.relation, GetCohenLamportReductionIdmap(rr), rr.phase1,
                                 rr.phase2, rr.crashed)
  }

  /////////////////////////////////////////////////////////////////
  // Proof that CohenLamportReductionRequest is valid
  /////////////////////////////////////////////////////////////////

  /////////////////////////
  // UTILITY LEMMAS
  /////////////////////////

  predicate PhasesMatch<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s1:State,
    s2:State,
    actor:Actor
    )
  {
    && (rr.crashed(s1) <==> rr.crashed(s2))
    && (rr.phase1(s1, actor) <==> rr.phase1(s2, actor))
    && (rr.phase2(s1, actor) <==> rr.phase2(s2, actor))
  }

  lemma lemma_ReducibleStepStartsAndEndsOutOfPhase<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    s':State,
    step:CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires CrossLevelNext(rr, s, s', step)
    requires step.Reducible?
    ensures  !rr.phase1(s, step.actor)
    ensures  !rr.phase2(s, step.actor)
    ensures  !rr.crashed(s') ==> !rr.phase1(s', step.actor) && !rr.phase2(s', step.actor)
  {
  }

  lemma lemma_StateNextSeqByOtherActorCausesPhasesMatch<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    states:seq<State>,
    trace:seq<LStep>,
    pos:int,
    step_actor:Actor,
    other_actor:Actor
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires StateNextSeq(states, trace, rr.lspec.next)
    requires forall step :: step in trace ==> rr.idmap(step) == step_actor
    requires step_actor != other_actor
    requires 0 <= pos < |states|
    requires !rr.crashed(states[pos])
    ensures  PhasesMatch(rr, states[0], states[pos], other_actor)
  {
    if pos > 0 {
      var prev := pos-1;
      assert ActionTuple(states[prev], states[prev+1], trace[prev]) in rr.lspec.next;
      assert rr.idmap(trace[prev]) == step_actor;
      assert PhasesMatch(rr, states[prev], states[prev+1], other_actor);
      lemma_StateNextSeqByOtherActorCausesPhasesMatch(rr, clrr, states, trace, pos-1, step_actor, other_actor);
    }
  }

  /////////////////////////////////////
  // PhaseUnaffectedByOtherActors
  /////////////////////////////////////

  lemma lemma_DemonstratePhaseUnaffectedByOtherActors<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    s:State,
    s':State,
    step:CrossLevelStep<State, Actor, LStep>,
    actor:Actor
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires ActionTuple(s, s', step) in clrr.spec.next
    requires clrr.idmap(step) != actor
    ensures  clrr.phase1(s, actor) <==> clrr.phase1(s', actor)
    ensures  clrr.phase2(s, actor) <==> clrr.phase2(s', actor)
  {
    if step.Low? {
      return;
    }

    var pos := 0;
    while pos < |step.trace|
      invariant 0 <= pos <= |step.trace|
      invariant clrr.phase1(s, actor) <==> clrr.phase1(step.states[pos], actor)
      invariant clrr.phase2(s, actor) <==> clrr.phase2(step.states[pos], actor)
    {
      assert ActionTuple(step.states[pos], step.states[pos+1], step.trace[pos]) in rr.lspec.next;
      pos := pos + 1;
    }
  }

  lemma lemma_PhaseUnaffectedByOtherActors<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.PhaseUnaffectedByOtherActors(clrr)
  {
    forall s, s', step, actor | ActionTuple(s, s', step) in clrr.spec.next && clrr.idmap(step) != actor
      ensures clrr.phase1(s, actor) <==> clrr.phase1(s', actor)
    {
      lemma_DemonstratePhaseUnaffectedByOtherActors(rr, clrr, s, s', step, actor);
    }

    forall s, s', step, actor | ActionTuple(s, s', step) in clrr.spec.next && clrr.idmap(step) != actor
      ensures clrr.phase2(s, actor) <==> clrr.phase2(s', actor)
    {
      lemma_DemonstratePhaseUnaffectedByOtherActors(rr, clrr, s, s', step, actor);
    }
  }

  /////////////////////////////////////
  // ActionSequencesLiftable
  /////////////////////////////////////

  lemma lemma_DemonstrateActionSequencesLiftable<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    states:seq<State>,
    trace:seq<CrossLevelStep<State, Actor, LStep>>,
    actor:Actor
    ) returns (
    hstep:CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires StateNextSeq(states, trace, clrr.spec.next)
    requires forall step :: step in trace ==> clrr.idmap(step) == actor
    requires |states| > 1
    requires !clrr.crashed(states[0])
    requires !clrr.phase1(states[0], actor)
    requires !clrr.phase2(states[0], actor)
    requires var s := last(states); !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: 0 < i < |trace| ==> clrr.phase1(states[i], actor) || clrr.phase2(states[i], actor)
    ensures  ActionTuple(states[0], last(states), hstep) in clrr.spec.next
    ensures  clrr.idmap(hstep) == actor
  {
    var zero := 0;
    assert ActionTuple(states[zero], states[zero+1], trace[zero]) in clrr.spec.next;

    if |trace| == 1 {
      hstep := trace[0];
      return;
    }

    if rr.crashed(states[1]) {
      lemma_AllCSpecStatesFollowingCrashedStateSame(rr, states, trace, 1);
      assert states[1] == last(states);
      hstep := trace[0];
      return;
    }

    forall i | 0 <= i < |trace|
      ensures  trace[i].Low?
      ensures  rr.idmap(trace[i].step) == actor
      ensures  ActionTuple(states[i], states[i+1], trace[i].step) in rr.lspec.next
      ensures  !rr.crashed(states[i])
    {
      assert ActionTuple(states[i], states[i+1], trace[i]) in clrr.spec.next;
      assert clrr.idmap(trace[i]) == actor;
      assert trace[i].actor == actor;
      assert !rr.crashed(states[i]);
      if trace[i].Reducible? {
        assert CrossLevelNext(rr, states[i], states[i+1], trace[i]);
        assert && ValidReducibleCrossLevelStep(rr, trace[i].states, trace[i].trace, trace[i].actor)
               && trace[i].states[0] == states[i]
               && last(trace[i].states) == states[i+1];
        if i == 0 {
          var iplus := i+1;
          assert 0 < iplus < |trace|;
          var s' := states[iplus];
          assert clrr.phase1(s', actor) || clrr.phase2(s', actor);
          assert var s := last(trace[i].states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor);
          assert last(trace[i].states) == states[iplus] == states[1];
          assert !rr.crashed(states[1]);
          assert false;
        }
        else {
          assert 0 < i < |trace|;
          var s := states[i];
          assert clrr.phase1(s, actor) || clrr.phase2(s, actor);
          assert var s := trace[i].states[0]; !rr.crashed(s) && !rr.phase1(s, actor) && !rr.phase2(s, actor);
          assert false;
        }
      }  
      assert trace[i].Low?;
    }

    var random_step:LStep :| true;
    var htrace := MapSeqToSeq(trace, (s:CrossLevelStep<State, Actor, LStep>) => if s.Low? then s.step else random_step);
    hstep := Reducible(actor, states, htrace);

    forall step | step in htrace
      ensures rr.idmap(step) == actor
    {
      var s :| s in trace && step == s.step;
      assert clrr.idmap(s) == actor;
      assert rr.idmap(step) == actor;
    }
    
    assert ValidReducibleCrossLevelStep(rr, states, htrace, actor);
  }

  lemma lemma_ActionSequencesLiftable<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.ActionSequencesLiftable(clrr)
  {
    forall states, trace, actor
      {:trigger CohenLamportReductionSpecModule.ActionSequencesLiftableConditions(clrr, states, trace, actor)}
      | CohenLamportReductionSpecModule.ActionSequencesLiftableConditions(clrr, states, trace, actor)
      ensures exists hstep :: ActionTuple(states[0], last(states), hstep) in clrr.spec.next && clrr.idmap(hstep) == actor
    {
      var hstep := lemma_DemonstrateActionSequencesLiftable(rr, clrr, states, trace, actor);
    }
  }

  /////////////////////////////////////
  // RightMoversCommute
  /////////////////////////////////////

  lemma lemma_DemonstrateRightMoverCommutesCaseOneStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_step:LStep
    ) returns (
    new_middle_state:State,
    other_step':LStep,
    right_mover':LStep
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    requires rr.idmap(right_mover) != rr.idmap(other_step)
    requires rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    requires !rr.crashed(state_after_both_steps)

    ensures  ActionTuple(initial_state, new_middle_state, other_step') in rr.lspec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, right_mover') in rr.lspec.next
    ensures  rr.idmap(other_step') == rr.idmap(other_step)
    ensures  rr.idmap(right_mover') == rr.idmap(right_mover)
    ensures  PhasesMatch(rr, initial_state, state_after_right_mover, rr.idmap(other_step))
    ensures  PhasesMatch(rr, new_middle_state, state_after_both_steps, rr.idmap(other_step))
    ensures  PhasesMatch(rr, initial_state, new_middle_state, rr.idmap(right_mover))
    ensures  PhasesMatch(rr, state_after_right_mover, state_after_both_steps, rr.idmap(right_mover))
  {
    assert RefinementViaReductionSpecModule.RightMoversCommuteConditions(rr, initial_state, state_after_right_mover, state_after_both_steps,
                                                                         right_mover, other_step);
    new_middle_state, other_step', right_mover' :|
      && ActionTuple(initial_state, new_middle_state, other_step') in rr.lspec.next
      && ActionTuple(new_middle_state, state_after_both_steps, right_mover') in rr.lspec.next
      && rr.idmap(other_step') == rr.idmap(other_step)
      && rr.idmap(right_mover') == rr.idmap(right_mover);
  }

  lemma lemma_DemonstrateRightMoverCommutesCaseMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_states:seq<State>,
    other_steps:seq<LStep>,
    other_actor:Actor
    ) returns (
    new_middle_state:State,
    other_states':seq<State>,
    other_steps':seq<LStep>,
    right_mover':LStep
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    requires StateNextSeq(other_states, other_steps, rr.lspec.next)
    requires forall step :: step in other_steps ==> rr.idmap(step) == other_actor
    requires other_states[0] == state_after_right_mover
    requires last(other_states) == state_after_both_steps
    requires rr.idmap(right_mover) != other_actor
    requires rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    requires !rr.crashed(state_after_both_steps)

    ensures  StateNextSeq(other_states', other_steps', rr.lspec.next)
    ensures  other_states'[0] == initial_state
    ensures  last(other_states') == new_middle_state
    ensures  forall step :: step in other_steps' ==> rr.idmap(step) == other_actor
    ensures  ActionTuple(new_middle_state, state_after_both_steps, right_mover') in rr.lspec.next
    ensures  rr.idmap(right_mover') == rr.idmap(right_mover)
    ensures  PhasesMatch(rr, initial_state, new_middle_state, rr.idmap(right_mover))
    ensures  PhasesMatch(rr, state_after_right_mover, state_after_both_steps, rr.idmap(right_mover))
    ensures  |other_states'| == |other_states|
    ensures  forall i :: 0 <= i < |other_states| ==> PhasesMatch(rr, other_states[i], other_states'[i], other_actor)
  {
    if |other_steps| == 0 {
      new_middle_state := initial_state;
      other_states' := [initial_state];
      other_steps' := [];
      right_mover' := right_mover;
      return;
    }

    var zero := 0;
    assert ActionTuple(other_states[zero], other_states[zero+1], other_steps[zero]) in rr.lspec.next;
    lemma_IfStateNextSeqDoesntCrashNoStateDoes(rr, other_states, other_steps, zero+1);
    var new_middle_state_mid, other_step_mid, right_mover_mid :=
      lemma_DemonstrateRightMoverCommutesCaseOneStep(
        rr, clrr, initial_state, state_after_right_mover, other_states[zero+1], right_mover, other_steps[zero]);

    lemma_NextMaintainsAnnotatedReachables(initial_state, new_middle_state_mid, other_step_mid, rr.lspec);

    lemma_ReduceStateNextSeqLeft(other_states, other_steps, rr.lspec.next);
    var other_states_next, other_steps_next;
    lemma_LastOfDropIsLast(other_states, 1);

    forall step | step in other_steps[1..]
      ensures rr.idmap(step) == other_actor
    {
      assert step in other_steps;
    }

    new_middle_state, other_states_next, other_steps_next, right_mover' :=
      lemma_DemonstrateRightMoverCommutesCaseMultipleSteps(
        rr, clrr, new_middle_state_mid, other_states[zero+1], state_after_both_steps, right_mover_mid,
        other_states[1..], other_steps[1..], other_actor);

    other_states' := [initial_state] + other_states_next;
    other_steps' := [other_step_mid] + other_steps_next;
    lemma_ExtendStateNextSeqLeft(other_states_next, other_steps_next, rr.lspec.next, initial_state, other_step_mid);
    lemma_LastOfConcatenationIsLastOfLatter([initial_state], other_states_next);

    forall i | 0 <= i < |other_states|
      ensures PhasesMatch(rr, other_states[i], other_states'[i], other_actor)
    {
      if i == 0 {
        assert other_states[i] == state_after_right_mover;
        assert other_states'[i] == initial_state;
        assert PhasesMatch(rr, other_states[i], other_states'[i], other_actor);
      }
      else {
        var iminus := i-1;
        lemma_IndexIntoConcatenation([initial_state], other_states_next, i);
        assert other_states'[i] == other_states_next[i-1];
        calc {
          other_states[i];
            { assert i == 1+(i-1); }
          other_states[1+(i-1)];
            { lemma_IndexIntoDrop(other_states, 1, i-1); }
          other_states[1..][i-1];
        }
        assert PhasesMatch(rr, other_states_next[iminus], other_states[1..][iminus], other_actor);
      }
    }

    forall step | step in other_steps'
      ensures rr.idmap(step) == other_actor
    {
      if step in other_steps_next {
        assert rr.idmap(step) == other_actor;
      }
      else {
        assert step == other_step_mid;
      }
    }
  }

  lemma lemma_DemonstrateRightMoverCommutesCaseLow<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    other_step':CrossLevelStep<State, Actor, LStep>,
    right_mover':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires !clrr.crashed(state_after_both_steps)
    requires right_mover.Low?
    requires other_step.Low?

    ensures  ActionTuple(initial_state, new_middle_state, other_step') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, right_mover') in clrr.spec.next
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  clrr.idmap(right_mover') == clrr.idmap(right_mover)
  {
    var other_step_single, right_mover_single;
    new_middle_state, other_step_single, right_mover_single :=
      lemma_DemonstrateRightMoverCommutesCaseOneStep(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover.step, other_step.step);
    other_step' := Low(rr.idmap(other_step_single), other_step_single);
    right_mover' := Low(rr.idmap(right_mover_single), right_mover_single);
  }

  lemma lemma_DemonstrateRightMoverCommutesCaseReducible<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    other_step':CrossLevelStep<State, Actor, LStep>,
    right_mover':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires !clrr.crashed(state_after_both_steps)
    requires right_mover.Low?
    requires other_step.Reducible?

    ensures  ActionTuple(initial_state, new_middle_state, other_step') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, right_mover') in clrr.spec.next
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  clrr.idmap(right_mover') == clrr.idmap(right_mover)
  {
    var other_states', other_steps', right_mover_single;
    new_middle_state, other_states', other_steps', right_mover_single :=
      lemma_DemonstrateRightMoverCommutesCaseMultipleSteps(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover.step, other_step.states, other_step.trace,
        other_step.actor);
    other_step' := Reducible(other_step.actor, other_states', other_steps');
    right_mover' := Low(rr.idmap(right_mover_single), right_mover_single);
    assert ValidReducibleCrossLevelStep(rr, other_states', other_steps', other_step.actor);
    assert CrossLevelNext(rr, initial_state, new_middle_state, other_step');
    assert CrossLevelNext(rr, new_middle_state, state_after_both_steps, right_mover');
  }

  lemma lemma_DemonstrateRightMoverCommutes<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    other_step':CrossLevelStep<State, Actor, LStep>,
    right_mover':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(clrr.spec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires !clrr.crashed(state_after_both_steps)

    ensures  ActionTuple(initial_state, new_middle_state, other_step') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, right_mover') in clrr.spec.next
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  clrr.idmap(right_mover') == clrr.idmap(right_mover)
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    assert initial_state in AnnotatedReachables(rr.lspec);
    if right_mover.Reducible? {
      lemma_ReducibleStepStartsAndEndsOutOfPhase(rr, initial_state, state_after_right_mover, right_mover);
      assert false;
    }
    
    if other_step.Low? {
      new_middle_state, other_step', right_mover' := lemma_DemonstrateRightMoverCommutesCaseLow(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
    else {
      new_middle_state, other_step', right_mover' := lemma_DemonstrateRightMoverCommutesCaseReducible(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
  }

  lemma lemma_RightMoversCommute<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.RightMoversCommute(clrr)
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger CohenLamportReductionSpecModule.RightMoversCommuteConditions(clrr, initial_state, state_after_right_mover,
                                                                             state_after_both_steps, right_mover, other_step)}
      | CohenLamportReductionSpecModule.RightMoversCommuteConditions(clrr, initial_state, state_after_right_mover,
                                                                     state_after_both_steps, right_mover, other_step)
      && initial_state in AnnotatedReachables(clrr.spec)
      && ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
      && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
      && clrr.idmap(right_mover) != clrr.idmap(other_step)
      && clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
      && !clrr.crashed(state_after_both_steps)
      ensures exists new_middle_state, other_step', right_mover' ::
                && ActionTuple(initial_state, new_middle_state, other_step') in clrr.spec.next
                && ActionTuple(new_middle_state, state_after_both_steps, right_mover') in clrr.spec.next
                && clrr.idmap(other_step') == clrr.idmap(other_step)
                && clrr.idmap(right_mover') == clrr.idmap(right_mover)
    {
      var new_middle_state, other_step', right_mover' :=
        lemma_DemonstrateRightMoverCommutes(
          rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
  }

  /////////////////////////////////////
  // LeftMoversCommute
  /////////////////////////////////////

  lemma lemma_DemonstrateLeftMoverCommutesCaseOneStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:LStep,
    left_mover:LStep
    ) returns (
    new_middle_state:State,
    left_mover':LStep,
    other_step':LStep
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    requires rr.idmap(other_step) != rr.idmap(left_mover)
    requires rr.phase2(state_after_other_step, rr.idmap(left_mover))
    requires !rr.crashed(state_after_both_steps)

    ensures  ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, other_step') in rr.lspec.next
    ensures  rr.idmap(left_mover') == rr.idmap(left_mover)
    ensures  rr.idmap(other_step') == rr.idmap(other_step)
    ensures  PhasesMatch(rr, initial_state, state_after_other_step, rr.idmap(left_mover))
    ensures  PhasesMatch(rr, new_middle_state, state_after_both_steps, rr.idmap(left_mover))
    ensures  PhasesMatch(rr, initial_state, new_middle_state, rr.idmap(other_step))
    ensures  PhasesMatch(rr, state_after_other_step, state_after_both_steps, rr.idmap(other_step))
  {
    assert RefinementViaReductionSpecModule.LeftMoversCommuteConditions(rr, initial_state, state_after_other_step, state_after_both_steps,
                                                                        other_step, left_mover);
    new_middle_state, left_mover', other_step' :|
      && ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
      && ActionTuple(new_middle_state, state_after_both_steps, other_step') in rr.lspec.next
      && rr.idmap(left_mover') == rr.idmap(left_mover)
      && rr.idmap(other_step') == rr.idmap(other_step);
  }

  lemma lemma_DemonstrateLeftMoverCommutesCaseMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_states:seq<State>,
    other_steps:seq<LStep>,
    other_actor:Actor,
    left_mover:LStep
    ) returns (
    new_middle_state:State,
    left_mover':LStep,
    other_states':seq<State>,
    other_steps':seq<LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires StateNextSeq(other_states, other_steps, rr.lspec.next)
    requires forall step :: step in other_steps ==> rr.idmap(step) == other_actor
    requires other_states[0] == initial_state
    requires last(other_states) == state_after_other_step
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    requires rr.idmap(left_mover) != other_actor
    requires rr.phase2(state_after_other_step, rr.idmap(left_mover))
    requires !rr.crashed(state_after_both_steps)

    ensures  ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
    ensures  StateNextSeq(other_states', other_steps', rr.lspec.next)
    ensures  other_states'[0] == new_middle_state
    ensures  last(other_states') == state_after_both_steps
    ensures  forall step :: step in other_steps' ==> rr.idmap(step) == other_actor
    ensures  rr.idmap(left_mover') == rr.idmap(left_mover)
    ensures  PhasesMatch(rr, initial_state, state_after_other_step, rr.idmap(left_mover))
    ensures  PhasesMatch(rr, new_middle_state, state_after_both_steps, rr.idmap(left_mover))
    ensures  |other_states'| == |other_states|
    ensures  forall i :: 0 <= i < |other_states| ==> PhasesMatch(rr, other_states[i], other_states'[i], other_actor)

    decreases |other_states|
  {
    if |other_steps| == 0 {
      new_middle_state := state_after_both_steps;
      left_mover' := left_mover;
      other_states' := [state_after_both_steps];
      other_steps' := [];
      return;
    }

    var penult := |other_states|-2;
    assert ActionTuple(other_states[penult], other_states[penult+1], other_steps[penult]) in rr.lspec.next;
    lemma_StateNextSeqMaintainsAnnotatedReachables(other_states, other_steps, rr.lspec);
    assert other_states[penult] in other_states;
    assert other_states[penult] in AnnotatedReachables(rr.lspec);

    calc {
      other_states[penult+1];
        { assert penult+1 == |other_states|-1; }
      last(other_states);
      state_after_other_step;
    }

    var new_middle_state_mid, left_mover_mid, other_step_mid :=
      lemma_DemonstrateLeftMoverCommutesCaseOneStep(
        rr, clrr, other_states[penult], other_states[penult+1], state_after_both_steps, other_steps[penult], left_mover);

    lemma_ReduceStateNextSeqRight(other_states, other_steps, rr.lspec.next);
    forall step | step in all_but_last(other_steps)
      ensures rr.idmap(step) == other_actor
    {
      assert step in other_steps;
    }
    lemma_LastOfAllButLast(other_states);

    var other_states_next, other_steps_next;
    new_middle_state, left_mover', other_states_next, other_steps_next :=
      lemma_DemonstrateLeftMoverCommutesCaseMultipleSteps(
        rr, clrr, initial_state, other_states[penult], new_middle_state_mid, all_but_last(other_states), all_but_last(other_steps),
        other_actor, left_mover_mid);
    other_states' := other_states_next + [state_after_both_steps];
    other_steps' := other_steps_next + [other_step_mid];

    lemma_ExtendStateNextSeqRight(other_states_next, other_steps_next, rr.lspec.next, state_after_both_steps, other_step_mid);
    lemma_IndexIntoConcatenation(other_states_next, [state_after_both_steps], |other_states'|-1);

    forall step | step in other_steps'
      ensures rr.idmap(step) == other_actor
    {
      if step in other_steps_next {
        assert rr.idmap(step) == other_actor;
      }
      else {
        assert step == other_step_mid;
      }
    }

    forall i | 0 <= i < |other_states|
      ensures PhasesMatch(rr, other_states[i], other_states'[i], other_actor)
    {
      if i < |other_states_next| {
        assert other_states[i] == all_but_last(other_states)[i];
        assert other_states'[i] == other_states_next[i];
        assert PhasesMatch(rr, all_but_last(other_states)[i], other_states_next[i], other_actor);
      }
      else {
        assert |other_states_next| == |all_but_last(other_states)| == |other_states|-1;
        assert i == |other_states|-1;
        assert other_states[i] == last(other_states) == state_after_other_step;
        assert other_states'[i] == state_after_both_steps;
        assert PhasesMatch(rr, state_after_other_step, state_after_both_steps, other_actor);
      }
    }
  }

  lemma lemma_DemonstrateLeftMoverCommutesCaseLow<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    left_mover':CrossLevelStep<State, Actor, LStep>,
    other_step':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires clrr.idmap(other_step) != clrr.idmap(left_mover)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires !clrr.crashed(state_after_both_steps)
    requires other_step.Low?
    requires left_mover.Low?

    ensures  ActionTuple(initial_state, new_middle_state, left_mover') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, other_step') in clrr.spec.next
    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
  {
    var left_mover_single, other_step_single;
    new_middle_state, left_mover_single, other_step_single :=
      lemma_DemonstrateLeftMoverCommutesCaseOneStep(
        rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step.step, left_mover.step);
    left_mover' := Low(rr.idmap(left_mover_single), left_mover_single);
    other_step' := Low(rr.idmap(other_step_single), other_step_single);
  }

  lemma lemma_DemonstrateLeftMoverCommutesCaseReducible<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    left_mover':CrossLevelStep<State, Actor, LStep>,
    other_step':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires clrr.idmap(other_step) != clrr.idmap(left_mover)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires !clrr.crashed(state_after_both_steps)
    requires other_step.Reducible?
    requires left_mover.Low?

    ensures  ActionTuple(initial_state, new_middle_state, left_mover') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, other_step') in clrr.spec.next
    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
  {
    var left_mover_single, other_states', other_steps';
    new_middle_state, left_mover_single, other_states', other_steps' :=
      lemma_DemonstrateLeftMoverCommutesCaseMultipleSteps(
        rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step.states, other_step.trace,
        other_step.actor, left_mover.step);
    left_mover' := Low(rr.idmap(left_mover_single), left_mover_single);
    other_step' := Reducible(other_step.actor, other_states', other_steps');
    assert ValidReducibleCrossLevelStep(rr, other_states', other_steps', other_step.actor);
    assert CrossLevelNext(rr, new_middle_state, state_after_both_steps, other_step');
    assert CrossLevelNext(rr, initial_state, new_middle_state, left_mover');
  }

  lemma lemma_DemonstrateLeftMoverCommutes<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    new_middle_state:State,
    left_mover':CrossLevelStep<State, Actor, LStep>,
    other_step':CrossLevelStep<State, Actor, LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(clrr.spec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires clrr.idmap(other_step) != clrr.idmap(left_mover)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires !clrr.crashed(state_after_both_steps)

    ensures  ActionTuple(initial_state, new_middle_state, left_mover') in clrr.spec.next
    ensures  ActionTuple(new_middle_state, state_after_both_steps, other_step') in clrr.spec.next
    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    assert initial_state in AnnotatedReachables(rr.lspec);
    if left_mover.Reducible? {
      lemma_ReducibleStepStartsAndEndsOutOfPhase(rr, state_after_other_step, state_after_both_steps, left_mover);
      assert false;
    }

    if other_step.Low? {
      new_middle_state, left_mover', other_step' :=
        lemma_DemonstrateLeftMoverCommutesCaseLow(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
    else {
      new_middle_state, left_mover', other_step' :=
        lemma_DemonstrateLeftMoverCommutesCaseReducible(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
  }

  lemma lemma_LeftMoversCommute<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.LeftMoversCommute(clrr)
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger CohenLamportReductionSpecModule.LeftMoversCommuteConditions(clrr, initial_state, state_after_other_step,
                                                                            state_after_both_steps, other_step, left_mover)}
      | CohenLamportReductionSpecModule.LeftMoversCommuteConditions(clrr, initial_state, state_after_other_step,
                                                                    state_after_both_steps, other_step, left_mover)
      && initial_state in AnnotatedReachables(clrr.spec)
      && ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
      && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
      && clrr.idmap(other_step) != clrr.idmap(left_mover)
      && clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
      && !clrr.crashed(state_after_both_steps)
      ensures exists new_middle_state, left_mover', other_step' ::
                && ActionTuple(initial_state, new_middle_state, left_mover') in clrr.spec.next
                && ActionTuple(new_middle_state, state_after_both_steps, other_step') in clrr.spec.next
                && clrr.idmap(left_mover') == clrr.idmap(left_mover)
                && clrr.idmap(other_step') == clrr.idmap(other_step)
    {
      var new_middle_state, left_mover', other_step' :=
        lemma_DemonstrateLeftMoverCommutes(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
  }

  ////////////////////////////////////////
  // LeftMoversAlwaysEnabled
  ////////////////////////////////////////

  lemma lemma_DemonstrateLeftMoversAlwaysEnabled<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    s:State,
    actor:Actor
    ) returns (
    states:seq<State>,
    trace:seq<CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires s in AnnotatedReachables(clrr.spec)
    requires clrr.phase2(s, actor)
    requires !clrr.crashed(s)
    ensures  StateNextSeq(states, trace, clrr.spec.next)
    ensures  states[0] == s
    ensures  clrr.crashed(last(states)) || !clrr.phase2(last(states), actor)
    ensures  forall i :: 0 <= i < |states|-1 ==> clrr.phase2(states[i], actor)
    ensures  forall step :: step in trace ==> clrr.idmap(step) == actor
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    assert RefinementViaReductionSpecModule.LeftMoversAlwaysEnabledConditions(rr, s, actor);
    var states_mid, trace_mid :|
      && StateNextSeq(states_mid, trace_mid, rr.lspec.next)
      && states_mid[0] == s
      && (rr.crashed(last(states_mid)) || !rr.phase2(last(states_mid), actor))
      && (forall i :: 0 <= i < |states_mid|-1 ==> rr.phase2(states_mid[i], actor))
      && (forall step :: step in trace_mid ==> rr.idmap(step) == actor);

    var pos := lemma_FindFirstCrashingState(rr, states_mid, trace_mid);
    if pos < |states_mid| {
      states := states_mid[..pos+1];
      trace := MapSeqToSeq(trace_mid[..pos], x => Low(rr.idmap(x), x));
      assert last(states) == states_mid[pos] == last(states_mid);
    }
    else {
      states := states_mid;
      trace := MapSeqToSeq(trace_mid, x => Low(rr.idmap(x), x));
    }

    assert forall i :: 0 <= i < |trace| ==> trace[i] == Low(rr.idmap(trace_mid[i]), trace_mid[i]);
    assert forall i :: 0 <= i < |trace| ==> !rr.crashed(states[i]);
    assert last(states) == last(states_mid);

    forall i {:trigger ActionTuple(states[i], states[i+1], trace[i]) in clrr.spec.next} | 0 <= i < |trace|
      ensures ActionTuple(states[i], states[i+1], trace[i]) in clrr.spec.next
    {
      assert ActionTuple(states[i], states[i+1], trace_mid[i]) in rr.lspec.next;
      assert trace[i].Low?;
      assert !rr.crashed(states[i]);
      assert trace[i].actor == rr.idmap(trace[i].step);
      assert CrossLevelNext(rr, states[i], states[i+1], trace[i]);
    }
  }

  lemma lemma_LeftMoversAlwaysEnabled<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.LeftMoversAlwaysEnabled(clrr)
  {
    forall s, actor
      {:trigger CohenLamportReductionSpecModule.LeftMoversAlwaysEnabledConditions(clrr, s, actor)}
      | CohenLamportReductionSpecModule.LeftMoversAlwaysEnabledConditions(clrr, s, actor)
      ensures exists states, trace ::
                && StateNextSeq(states, trace, clrr.spec.next)
                && states[0] == s
                && (clrr.crashed(last(states)) || !clrr.phase2(last(states), actor))
                && (forall i :: 0 <= i < |states|-1 ==> clrr.phase2(states[i], actor))
                && (forall step :: step in trace ==> clrr.idmap(step) == actor)
    {
      var states, trace := lemma_DemonstrateLeftMoversAlwaysEnabled(rr, clrr, s, actor);
    }
  }

  ////////////////////////////////////////
  // LeftMoversEnabledBeforeCrash
  ////////////////////////////////////////

  lemma lemma_MoveMultipleLeftMoversAcrossMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_states:seq<State>,
    other_steps:seq<LStep>,
    other_actor:Actor,
    left_mover_states:seq<State>,
    left_mover_steps:seq<LStep>,
    left_mover_actor:Actor
    ) returns (
    new_middle_state:State,
    left_mover_states':seq<State>,
    left_mover_steps':seq<LStep>,
    other_states':seq<State>,
    other_steps':seq<LStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires StateNextSeq(other_states, other_steps, rr.lspec.next)
    requires forall step :: step in other_steps ==> rr.idmap(step) == other_actor
    requires other_states[0] == initial_state
    requires last(other_states) == state_after_other_step
    requires StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    requires left_mover_states[0] == state_after_other_step
    requires last(left_mover_states) == state_after_both_steps
    requires forall step :: step in left_mover_steps ==> rr.idmap(step) == left_mover_actor
    requires forall i :: 0 <= i < |left_mover_states|-1 ==> rr.phase2(left_mover_states[i], left_mover_actor)
    requires left_mover_actor != other_actor
    requires !rr.crashed(state_after_both_steps)

    ensures  StateNextSeq(left_mover_states', left_mover_steps', rr.lspec.next)
    ensures  left_mover_states'[0] == initial_state
    ensures  last(left_mover_states') == new_middle_state
    ensures  forall step :: step in left_mover_steps' ==> rr.idmap(step) == left_mover_actor
    ensures  |left_mover_states'| == |left_mover_states|
    ensures  forall i :: 0 <= i < |left_mover_states| ==> PhasesMatch(rr, left_mover_states[i], left_mover_states'[i], left_mover_actor)
    ensures  StateNextSeq(other_states', other_steps', rr.lspec.next)
    ensures  other_states'[0] == new_middle_state
    ensures  last(other_states') == state_after_both_steps
    ensures  forall step :: step in other_steps' ==> rr.idmap(step) == other_actor
    ensures  |other_states'| == |other_states|
    ensures  forall i :: 0 <= i < |other_states| ==> PhasesMatch(rr, other_states[i], other_states'[i], other_actor)

    decreases |left_mover_states|
  {
    if |left_mover_steps| == 0 {
      lemma_StateNextSeqByOtherActorCausesPhasesMatch(rr, clrr, other_states, other_steps, |other_steps|, other_actor, left_mover_actor);
      new_middle_state := initial_state;
      left_mover_states' := [initial_state];
      left_mover_steps' := [];
      other_states' := other_states;
      other_steps' := other_steps;
      return;
    }

    var zero := 0;
    assert ActionTuple(left_mover_states[zero], left_mover_states[zero+1], left_mover_steps[zero]) in rr.lspec.next;
    lemma_IfStateNextSeqDoesntCrashNoStateDoes(rr, left_mover_states, left_mover_steps, zero+1);
    var new_middle_state_mid, left_mover_mid, other_states_mid, other_steps_mid :=
      lemma_DemonstrateLeftMoverCommutesCaseMultipleSteps(
        rr, clrr, initial_state, state_after_other_step, left_mover_states[zero+1], other_states, other_steps, other_actor,
        left_mover_steps[zero]);

    lemma_ReduceStateNextSeqLeft(left_mover_states, left_mover_steps, rr.lspec.next);
    lemma_NextMaintainsAnnotatedReachables(initial_state, new_middle_state_mid, left_mover_mid, rr.lspec);
    var left_mover_states_next, left_mover_steps_next;
    new_middle_state, left_mover_states_next, left_mover_steps_next, other_states', other_steps' :=
      lemma_MoveMultipleLeftMoversAcrossMultipleSteps(
        rr, clrr, new_middle_state_mid, left_mover_states[zero+1], last(left_mover_states), other_states_mid, other_steps_mid,
        other_actor, left_mover_states[1..], left_mover_steps[1..], left_mover_actor);

    left_mover_states' := [initial_state] + left_mover_states_next;
    left_mover_steps' := [left_mover_mid] + left_mover_steps_next;
    lemma_ExtendStateNextSeqLeft(left_mover_states_next, left_mover_steps_next, rr.lspec.next, initial_state, left_mover_mid);

    forall i | 0 <= i < |left_mover_states|
      ensures PhasesMatch(rr, left_mover_states[i], left_mover_states'[i], left_mover_actor)
    {
      if i > 0 {
        var iminus := i-1;
        assert 0 <= iminus < |left_mover_states[1..]|;
        lemma_IndexIntoConcatenation([initial_state], left_mover_states_next, i);
        assert left_mover_states'[i] == left_mover_states_next[iminus];
        calc {
          left_mover_states[i];
            { assert i == 1+iminus; }
          left_mover_states[1+iminus];
            { lemma_IndexIntoDrop(left_mover_states, 1, iminus); }
           left_mover_states[1..][iminus];
        }
        assert PhasesMatch(rr, left_mover_states[1..][iminus], left_mover_states_next[iminus], left_mover_actor);
      }
      else {
        assert left_mover_states'[i] == initial_state;
        lemma_StateNextSeqByOtherActorCausesPhasesMatch(rr, clrr, other_states, other_steps, |other_steps|, other_actor, left_mover_actor);
      }
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseOneStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    post_crash_state:State,
    crash_step:LStep,
    left_mover_actor:Actor
    ) returns (
    left_mover_states:seq<State>,
    left_mover_steps:seq<LStep>,
    crash_step':LStep,
    post_crash_state':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, post_crash_state, crash_step) in rr.lspec.next
    requires !clrr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires rr.idmap(crash_step) != left_mover_actor
    requires rr.phase2(initial_state, left_mover_actor)

    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  !rr.crashed(last(left_mover_states))
    ensures  !rr.phase2(last(left_mover_states), left_mover_actor)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> rr.phase2(left_mover_states[i], left_mover_actor)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == left_mover_actor
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_step') in rr.lspec.next
    ensures  rr.idmap(crash_step') == rr.idmap(crash_step)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    assert RefinementViaReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_step,
                                                                                   left_mover_actor);
    left_mover_states, left_mover_steps, crash_step', post_crash_state' :|
           && StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
           && left_mover_states[0] == initial_state
           && !rr.crashed(last(left_mover_states))
           && !rr.phase2(last(left_mover_states), left_mover_actor)
           && (forall i :: 0 <= i < |left_mover_states|-1 ==> rr.phase2(left_mover_states[i], left_mover_actor))
           && (forall step :: step in left_mover_steps ==> rr.idmap(step) == left_mover_actor)
           && ActionTuple(last(left_mover_states), post_crash_state', crash_step') in rr.lspec.next
           && rr.idmap(crash_step') == rr.idmap(crash_step)
           && rr.crashed(post_crash_state')
           && RefinementPair(post_crash_state, post_crash_state') in rr.relation;
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseLow<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    post_crash_state:State,
    crash_step:CrossLevelStep<State, Actor, LStep>,
    left_mover_actor:Actor
    ) returns (
    left_mover_states:seq<State>,
    left_mover_steps:seq<CrossLevelStep<State, Actor, LStep>>,
    crash_step':CrossLevelStep<State, Actor, LStep>,
    post_crash_state':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, post_crash_state, crash_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires clrr.crashed(post_crash_state)
    requires clrr.idmap(crash_step) != left_mover_actor
    requires clrr.phase2(initial_state, left_mover_actor)
    requires crash_step.Low?

    ensures  StateNextSeq(left_mover_states, left_mover_steps, clrr.spec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  !clrr.crashed(last(left_mover_states))
    ensures  !clrr.phase2(last(left_mover_states), left_mover_actor)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> clrr.phase2(left_mover_states[i], left_mover_actor)
    ensures  forall step :: step in left_mover_steps ==> clrr.idmap(step) == left_mover_actor
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_step') in clrr.spec.next
    ensures  clrr.idmap(crash_step') == clrr.idmap(crash_step)
    ensures  clrr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in clrr.relation
  {
    var ltrace, crash_step_single;
    left_mover_states, ltrace, crash_step_single, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseOneStep(
        rr, clrr, initial_state, post_crash_state, crash_step.step, left_mover_actor);
    crash_step' := Low(rr.idmap(crash_step_single), crash_step_single);
    left_mover_steps := lemma_LiftStateNextSeqToCrossLevel(rr, clrr, left_mover_states, ltrace);
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    post_crash_state:State,
    crash_states:seq<State>,
    crash_steps:seq<LStep>,
    crash_actor:Actor,
    left_mover_actor:Actor
    ) returns (
    left_mover_states:seq<State>,
    left_mover_steps:seq<LStep>,
    crash_states':seq<State>,
    crash_steps':seq<LStep>,
    post_crash_state':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires StateNextSeq(crash_states, crash_steps, rr.lspec.next)
    requires crash_states[0] == initial_state
    requires last(crash_states) == post_crash_state
    requires forall step :: step in crash_steps ==> rr.idmap(step) == crash_actor
    requires !clrr.crashed(initial_state)
    requires clrr.crashed(post_crash_state)
    requires crash_actor != left_mover_actor
    requires rr.phase2(initial_state, left_mover_actor)

    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  !rr.crashed(last(left_mover_states))
    ensures  !rr.phase2(last(left_mover_states), left_mover_actor)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> rr.phase2(left_mover_states[i], left_mover_actor)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == left_mover_actor
    ensures  StateNextSeq(crash_states', crash_steps', rr.lspec.next)
    ensures  crash_states'[0] == last(left_mover_states)
    ensures  last(crash_states') == post_crash_state'
    ensures  forall step :: step in crash_steps' ==> rr.idmap(step) == crash_actor
    ensures  clrr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in clrr.relation
    ensures  |crash_states'| <= |crash_states|
    ensures  forall i :: 0 <= i < |crash_states'|-1 ==> PhasesMatch(rr, crash_states[i], crash_states'[i], crash_actor)
  {
    var pos := lemma_FindFirstCrashingState(rr, crash_states, crash_steps);
    assert 0 < pos < |crash_states|;
    var prev := pos-1;
    assert post_crash_state == last(crash_states) == crash_states[pos];

    assert ActionTuple(crash_states[prev], crash_states[prev+1], crash_steps[prev]) in rr.lspec.next;
    lemma_StateNextSeqMaintainsAnnotatedReachables(crash_states, crash_steps, rr.lspec);
    assert crash_states[prev] in crash_states;
    assert crash_states[prev] in AnnotatedReachables(rr.lspec);
    lemma_StateNextSeqByOtherActorCausesPhasesMatch(rr, clrr, crash_states, crash_steps, prev, crash_actor, left_mover_actor);

    var left_mover_states_mid, left_mover_steps_mid, crash_step_mid;
    left_mover_states_mid, left_mover_steps_mid, crash_step_mid, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseOneStep(
        rr, clrr, crash_states[prev], crash_states[prev+1], crash_steps[prev], left_mover_actor);

    lemma_TakeStateNextSeq(crash_states, crash_steps, rr.lspec.next, prev);
    var new_middle_state, other_states, other_steps;
    new_middle_state, left_mover_states, left_mover_steps, other_states, other_steps :=
      lemma_MoveMultipleLeftMoversAcrossMultipleSteps(
        rr, clrr, initial_state, crash_states[prev], last(left_mover_states_mid), crash_states[..prev+1], crash_steps[..prev],
        crash_actor, left_mover_states_mid, left_mover_steps_mid, left_mover_actor);

    crash_states' := other_states + [post_crash_state'];
    crash_steps' := other_steps + [crash_step_mid];
    lemma_ExtendStateNextSeqRight(other_states, other_steps, rr.lspec.next, post_crash_state', crash_step_mid);

    forall i | 0 <= i < |left_mover_states|-1
      ensures rr.phase2(left_mover_states[i], left_mover_actor)
    {
      assert PhasesMatch(rr, left_mover_states_mid[i], left_mover_states[i], left_mover_actor);
    }

    forall i | 0 <= i < |crash_states'|-1
      ensures PhasesMatch(rr, crash_states[i], crash_states'[i], crash_actor)
    {
      assert crash_states[i] == crash_states[..prev+1][i];
      assert crash_states'[i] == other_states[i];
      assert PhasesMatch(rr, crash_states[..prev+1][i], other_states[i], crash_actor);
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseReducible<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    post_crash_state:State,
    crash_step:CrossLevelStep<State, Actor, LStep>,
    left_mover_actor:Actor
    ) returns (
    left_mover_states:seq<State>,
    left_mover_steps:seq<CrossLevelStep<State, Actor, LStep>>,
    crash_step':CrossLevelStep<State, Actor, LStep>,
    post_crash_state':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, post_crash_state, crash_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires clrr.crashed(post_crash_state)
    requires clrr.idmap(crash_step) != left_mover_actor
    requires clrr.phase2(initial_state, left_mover_actor)
    requires crash_step.Reducible?

    ensures  StateNextSeq(left_mover_states, left_mover_steps, clrr.spec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  !clrr.crashed(last(left_mover_states))
    ensures  !clrr.phase2(last(left_mover_states), left_mover_actor)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> clrr.phase2(left_mover_states[i], left_mover_actor)
    ensures  forall step :: step in left_mover_steps ==> clrr.idmap(step) == left_mover_actor
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_step') in clrr.spec.next
    ensures  clrr.idmap(crash_step') == clrr.idmap(crash_step)
    ensures  clrr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in clrr.relation
  {
    var ltrace, crash_states', crash_steps';
    left_mover_states, ltrace, crash_states', crash_steps', post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseMultipleSteps(
        rr, clrr, initial_state, post_crash_state, crash_step.states, crash_step.trace, crash_step.actor, left_mover_actor);
    crash_step' := Reducible(crash_step.actor, crash_states', crash_steps');
    left_mover_steps := lemma_LiftStateNextSeqToCrossLevel(rr, clrr, left_mover_states, ltrace);
    assert ValidReducibleCrossLevelStep(rr, crash_states', crash_steps', crash_step.actor);
    assert CrossLevelNext(rr, last(left_mover_states), post_crash_state', crash_step');
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrash<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    post_crash_state:State,
    crash_step:CrossLevelStep<State, Actor, LStep>,
    left_mover_actor:Actor
    ) returns (
    left_mover_states:seq<State>,
    left_mover_steps:seq<CrossLevelStep<State, Actor, LStep>>,
    crash_step':CrossLevelStep<State, Actor, LStep>,
    post_crash_state':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(clrr.spec)
    requires ActionTuple(initial_state, post_crash_state, crash_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires clrr.crashed(post_crash_state)
    requires clrr.idmap(crash_step) != left_mover_actor
    requires clrr.phase2(initial_state, left_mover_actor)

    ensures  StateNextSeq(left_mover_states, left_mover_steps, clrr.spec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  !clrr.crashed(last(left_mover_states))
    ensures  !clrr.phase2(last(left_mover_states), left_mover_actor)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> clrr.phase2(left_mover_states[i], left_mover_actor)
    ensures  forall step :: step in left_mover_steps ==> clrr.idmap(step) == left_mover_actor
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_step') in clrr.spec.next
    ensures  clrr.idmap(crash_step') == clrr.idmap(crash_step)
    ensures  clrr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in clrr.relation
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    if crash_step.Low? {
      left_mover_states, left_mover_steps, crash_step', post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseLow(rr, clrr, initial_state, post_crash_state, crash_step, left_mover_actor);
    }
    else {
      left_mover_states, left_mover_steps, crash_step', post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrashCaseReducible(rr, clrr, initial_state, post_crash_state, crash_step, left_mover_actor);
    }
  }

  lemma lemma_LeftMoversEnabledBeforeCrash<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.LeftMoversEnabledBeforeCrash(clrr)
  {
    forall initial_state, post_crash_state, crash_step, actor
      {:trigger CohenLamportReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(clrr, initial_state, post_crash_state,
                                                                                       crash_step, actor)}
      | CohenLamportReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(clrr, initial_state, post_crash_state, crash_step, actor)
      ensures exists states, trace, crash_step', post_crash_state' ::
                && StateNextSeq(states, trace, clrr.spec.next)
                && states[0] == initial_state
                && !clrr.crashed(last(states))
                && !clrr.phase2(last(states), actor)
                && (forall i :: 0 <= i < |states|-1 ==> clrr.phase2(states[i], actor))
                && (forall step :: step in trace ==> clrr.idmap(step) == actor)
                && ActionTuple(last(states), post_crash_state', crash_step') in clrr.spec.next
                && clrr.idmap(crash_step') == clrr.idmap(crash_step)
                && clrr.crashed(post_crash_state')
                && RefinementPair(post_crash_state, post_crash_state') in clrr.relation
    {
      var states, trace, crash_step', post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrash(rr, clrr, initial_state, post_crash_state, crash_step, actor);
    }
  }

  ////////////////////////////////////////
  // RightMoverCrashPreservation
  ////////////////////////////////////////

  lemma lemma_DemonstrateRightMoverCrashPreservationCaseOneStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_step:LStep
    ) returns (
    other_step':LStep,
    state_after_other_step':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    requires rr.idmap(right_mover) != rr.idmap(other_step)

    ensures  rr.idmap(other_step') == rr.idmap(other_step)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step') in rr.lspec.next
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  {
    assert RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover,
                                                                                  state_after_both_steps, right_mover, other_step);
    other_step', state_after_other_step' :|
      && rr.idmap(other_step') == rr.idmap(other_step)
      && ActionTuple(initial_state, state_after_other_step', other_step') in rr.lspec.next
      && rr.crashed(state_after_other_step')
      && RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation;
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationCaseMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_states:seq<State>,
    other_steps:seq<LStep>,
    other_actor:Actor
    ) returns (
    other_states':seq<State>,
    other_steps':seq<LStep>,
    state_after_other_step':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    requires StateNextSeq(other_states, other_steps, rr.lspec.next)
    requires other_states[0] == state_after_right_mover
    requires last(other_states) == state_after_both_steps
    requires forall step :: step in other_steps ==> rr.idmap(step) == other_actor
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    requires rr.idmap(right_mover) != other_actor

    ensures  StateNextSeq(other_states', other_steps', rr.lspec.next)
    ensures  other_states'[0] == initial_state
    ensures  last(other_states') == state_after_other_step'
    ensures  forall step :: step in other_steps' ==> rr.idmap(step) == other_actor
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
    ensures  |other_states'| <= |other_states|
    ensures  forall i :: 0 <= i < |other_states'|-1 ==> PhasesMatch(rr, other_states[i], other_states'[i], other_actor)
  {
    var pos := lemma_FindFirstCrashingState(rr, other_states, other_steps);
    assert 0 < pos < |other_states|;
    var prev := pos-1;
    assert state_after_both_steps == last(other_states) == other_states[pos];

    assert ActionTuple(other_states[prev], other_states[prev+1], other_steps[prev]) in rr.lspec.next;

    lemma_TakeStateNextSeq(other_states, other_steps, rr.lspec.next, prev);
    var new_middle_state, other_states_next, other_steps_next, right_mover' :=
      lemma_DemonstrateRightMoverCommutesCaseMultipleSteps(
        rr, clrr, initial_state, state_after_right_mover, other_states[prev], right_mover,
        other_states[..prev+1], other_steps[..prev], other_actor);

    lemma_StateNextSeqMaintainsAnnotatedReachables(other_states_next, other_steps_next, rr.lspec);
    assert new_middle_state == last(other_states_next);
    assert new_middle_state in other_states_next;
    assert new_middle_state in AnnotatedReachables(rr.lspec);
    assert RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, new_middle_state, other_states[prev],
                                                                                  other_states[prev+1], right_mover', other_steps[prev]);

    var other_step';
    other_step', state_after_other_step' :|
      && rr.idmap(other_step') == rr.idmap(other_steps[prev])
      && ActionTuple(new_middle_state, state_after_other_step', other_step') in rr.lspec.next
      && rr.crashed(state_after_other_step')
      && RefinementPair(other_states[prev+1], state_after_other_step') in rr.relation;

    other_states' := other_states_next + [state_after_other_step'];
    other_steps' := other_steps_next + [other_step'];
    lemma_ExtendStateNextSeqRight(other_states_next, other_steps_next, rr.lspec.next, state_after_other_step', other_step');
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationCaseLow<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    other_step':CrossLevelStep<State, Actor, LStep>,
    state_after_other_step':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_right_mover)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)
    requires right_mover.Low?
    requires other_step.Low?

    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step') in clrr.spec.next
    ensures  clrr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in clrr.relation
  {
    var other_step_single;
    other_step_single, state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationCaseOneStep(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover.step, other_step.step);
    other_step' := Low(rr.idmap(other_step_single), other_step_single);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationCaseReducible<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    other_step':CrossLevelStep<State, Actor, LStep>,
    state_after_other_step':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_right_mover)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)
    requires right_mover.Low?
    requires other_step.Reducible?

    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step') in clrr.spec.next
    ensures  clrr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in clrr.relation
  {
    var other_states', other_steps';
    other_states', other_steps', state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationCaseMultipleSteps(
        rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover.step,
        other_step.states, other_step.trace, other_step.actor);
    other_step' := Reducible(other_step.actor, other_states', other_steps');
    assert ValidReducibleCrossLevelStep(rr, other_states', other_steps', other_step.actor);
    assert CrossLevelNext(rr, initial_state, state_after_other_step', other_step');
  }

  lemma lemma_DemonstrateRightMoverCrashPreservation<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:CrossLevelStep<State, Actor, LStep>,
    other_step:CrossLevelStep<State, Actor, LStep>
    ) returns (
    other_step':CrossLevelStep<State, Actor, LStep>,
    state_after_other_step':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(clrr.spec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_right_mover)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    requires clrr.idmap(right_mover) != clrr.idmap(other_step)

    ensures  clrr.idmap(other_step') == clrr.idmap(other_step)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step') in clrr.spec.next
    ensures  clrr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in clrr.relation
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    assert initial_state in AnnotatedReachables(rr.lspec);
    if right_mover.Reducible? {
      lemma_ReducibleStepStartsAndEndsOutOfPhase(rr, initial_state, state_after_right_mover, right_mover);
      assert false;
    }

    if other_step.Low? {
      other_step', state_after_other_step' :=
        lemma_DemonstrateRightMoverCrashPreservationCaseLow(
          rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
    else {
      other_step', state_after_other_step' :=
        lemma_DemonstrateRightMoverCrashPreservationCaseReducible(
          rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
  }

  lemma lemma_RightMoverCrashPreservation<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.RightMoverCrashPreservation(clrr)
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger CohenLamportReductionSpecModule.RightMoverCrashPreservationConditions(clrr, initial_state, state_after_right_mover,
                                                                                      state_after_both_steps, right_mover, other_step)}
      | CohenLamportReductionSpecModule.RightMoverCrashPreservationConditions(clrr, initial_state, state_after_right_mover,
                                                                              state_after_both_steps, right_mover, other_step)
      ensures exists other_step', state_after_other_step' ::
                && clrr.idmap(other_step') == clrr.idmap(other_step)
                && ActionTuple(initial_state, state_after_other_step', other_step') in clrr.spec.next
                && clrr.crashed(state_after_other_step')
                && RefinementPair(state_after_both_steps, state_after_other_step') in clrr.relation
    {
      var other_step', state_after_other_step' :=
        lemma_DemonstrateRightMoverCrashPreservation(
          rr, clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step);
    }
  }

  ////////////////////////////////////////
  // LeftMoverSelfCrashPreservation
  ////////////////////////////////////////

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationCaseOneStep<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:LStep,
    left_mover:LStep
    ) returns (
    left_mover':LStep,
    state_after_left_mover':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires rr.phase2(state_after_other_step, rr.idmap(left_mover))
    requires rr.idmap(left_mover) != rr.idmap(other_step)

    ensures  rr.idmap(left_mover') == rr.idmap(left_mover)
    ensures  ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
    ensures  rr.crashed(state_after_left_mover')
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation
  {
    assert RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_step,
                                                                                     state_after_both_steps, other_step, left_mover);
    left_mover', state_after_left_mover' :|
      && rr.idmap(left_mover') == rr.idmap(left_mover)
      && ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
      && rr.crashed(state_after_left_mover')
      && RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation;
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationCaseLow<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    left_mover':CrossLevelStep<State, Actor, LStep>,
    state_after_left_mover':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_other_step)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires clrr.idmap(left_mover) != clrr.idmap(other_step)
    requires other_step.Low?
    requires left_mover.Low?

    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  ActionTuple(initial_state, state_after_left_mover', left_mover') in clrr.spec.next
    ensures  clrr.crashed(state_after_left_mover')
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation
  {
    var left_mover_single;
    left_mover_single, state_after_left_mover' :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationCaseOneStep(
        rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step.step, left_mover.step);
    left_mover' := Low(rr.idmap(left_mover_single), left_mover_single);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationCaseMultipleSteps<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_states:seq<State>,
    other_steps:seq<LStep>,
    other_actor:Actor,
    left_mover:LStep
    ) returns (
    left_mover':LStep,
    state_after_left_mover':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires |other_states| > 1
    requires StateNextSeq(other_states, other_steps, rr.lspec.next)
    requires other_states[0] == initial_state
    requires last(other_states) == state_after_other_step
    requires forall step :: step in other_steps ==> rr.idmap(step) == other_actor
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires rr.phase2(state_after_other_step, rr.idmap(left_mover))
    requires rr.idmap(left_mover) != other_actor

    ensures  rr.idmap(left_mover') == rr.idmap(left_mover)
    ensures  ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
    ensures  rr.crashed(state_after_left_mover')
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation

    decreases |other_states|
  {
    var penult := |other_states|-2;
    assert ActionTuple(other_states[penult], other_states[penult+1], other_steps[penult]) in rr.lspec.next;
    lemma_StateNextSeqMaintainsAnnotatedReachables(other_states, other_steps, rr.lspec);
    assert RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, other_states[penult], other_states[penult+1],
                                                                                     state_after_both_steps, other_steps[penult],
                                                                                     left_mover);
    var left_mover_mid, state_after_left_mover_mid :|
      && rr.idmap(left_mover_mid) == rr.idmap(left_mover)
      && ActionTuple(other_states[penult], state_after_left_mover_mid, left_mover_mid) in rr.lspec.next
      && rr.crashed(state_after_left_mover_mid)
      && RefinementPair(state_after_both_steps, state_after_left_mover_mid) in rr.relation;

    if penult == 0 {
      left_mover' := left_mover_mid;
      state_after_left_mover' := state_after_left_mover_mid;
    }
    else {
      lemma_ReduceStateNextSeqRight(other_states, other_steps, rr.lspec.next);
      left_mover', state_after_left_mover' :=
        lemma_DemonstrateLeftMoverSelfCrashPreservationCaseMultipleSteps(
          rr, clrr, initial_state, other_states[penult], state_after_left_mover_mid, all_but_last(other_states),
          all_but_last(other_steps), other_actor, left_mover_mid);
    }
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationCaseReducible<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    left_mover':CrossLevelStep<State, Actor, LStep>,
    state_after_left_mover':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_other_step)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires clrr.idmap(left_mover) != clrr.idmap(other_step)
    requires other_step.Reducible?
    requires left_mover.Low?

    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  ActionTuple(initial_state, state_after_left_mover', left_mover') in clrr.spec.next
    ensures  clrr.crashed(state_after_left_mover')
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation

  {
    var left_mover_single;
    left_mover_single, state_after_left_mover' :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationCaseMultipleSteps(
        rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step.states, other_step.trace,
        other_step.actor, left_mover.step);
    left_mover' := Low(rr.idmap(left_mover_single), left_mover_single);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservation<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:CrossLevelStep<State, Actor, LStep>,
    left_mover:CrossLevelStep<State, Actor, LStep>
    ) returns (
    left_mover':CrossLevelStep<State, Actor, LStep>,
    state_after_left_mover':State
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    requires initial_state in AnnotatedReachables(clrr.spec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    requires !clrr.crashed(initial_state)
    requires !clrr.crashed(state_after_other_step)
    requires clrr.crashed(state_after_both_steps)
    requires clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    requires clrr.idmap(left_mover) != clrr.idmap(other_step)

    ensures  clrr.idmap(left_mover') == clrr.idmap(left_mover)
    ensures  ActionTuple(initial_state, state_after_left_mover', left_mover') in clrr.spec.next
    ensures  clrr.crashed(state_after_left_mover')
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation
  {
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    assert initial_state in AnnotatedReachables(rr.lspec);
    if left_mover.Reducible? {
      lemma_ReducibleStepStartsAndEndsOutOfPhase(rr, state_after_other_step, state_after_both_steps, left_mover);
      assert false;
    }

    if other_step.Low? {
      left_mover', state_after_left_mover' :=
        lemma_DemonstrateLeftMoverSelfCrashPreservationCaseLow(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
    else {
      left_mover', state_after_left_mover' :=
        lemma_DemonstrateLeftMoverSelfCrashPreservationCaseReducible(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
  }

  lemma lemma_LeftMoverSelfCrashPreservation<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    clrr:CohenLamportReductionRequest<State, Actor, CrossLevelStep<State, Actor, LStep>>
    )
    requires ValidRefinementViaReductionRequest(rr)
    requires clrr == GetCohenLamportReductionRequest(rr)
    ensures  CohenLamportReductionSpecModule.LeftMoverSelfCrashPreservation(clrr)
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger CohenLamportReductionSpecModule.LeftMoverSelfCrashPreservationConditions(clrr, initial_state, state_after_other_step,
                                                                                         state_after_both_steps, other_step, left_mover)}
      | CohenLamportReductionSpecModule.LeftMoverSelfCrashPreservationConditions(clrr, initial_state, state_after_other_step,
                                                                                 state_after_both_steps, other_step, left_mover)
      ensures exists left_mover', state_after_left_mover' ::
                && clrr.idmap(left_mover') == clrr.idmap(left_mover)
                && ActionTuple(initial_state, state_after_left_mover', left_mover') in clrr.spec.next
                && clrr.crashed(state_after_left_mover')
                && RefinementPair(state_after_both_steps, state_after_left_mover') in clrr.relation
    {
      var left_mover', state_after_left_mover' :=
        lemma_DemonstrateLeftMoverSelfCrashPreservation(
          rr, clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover);
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  // Final demonstration that CohenLamportReductionRequest is valid
  ///////////////////////////////////////////////////////////////////////////

  lemma lemma_IsValidCohenLamportReductionRequest<State, Actor, LStep, HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
    requires ValidRefinementViaReductionRequest(rr)
    ensures  ValidCohenLamportReductionRequest(GetCohenLamportReductionRequest(rr))
  {
    var clrr := GetCohenLamportReductionRequest(rr);
    lemma_AnnotatedReachablesOfCrossLevelSpec(rr);
    lemma_PhaseUnaffectedByOtherActors(rr, clrr);
    lemma_RightMoversCommute(rr, clrr);
    lemma_LeftMoversCommute(rr, clrr);
    lemma_LeftMoversAlwaysEnabled(rr, clrr);
    lemma_LeftMoversEnabledBeforeCrash(rr, clrr);
    lemma_RightMoverCrashPreservation(rr, clrr);
    lemma_LeftMoverSelfCrashPreservation(rr, clrr);
    lemma_ActionSequencesLiftable(rr, clrr);
  }

}
