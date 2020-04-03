/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains lemmas useful in effecting a Cohen-Lamport reduction on a behavior.  They
// support lemma_PerformCohenLamportReduction (in CohenLamportReduction.i.dfy).
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "CohenLamportReductionSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"

module CohenLamportReductionLemmasModule {

  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened CohenLamportReductionSpecModule
  import opened util_collections_seqs_i

  lemma lemma_InstantiateLeftMoversBeforeCrash<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    post_crash_state:State,
    crash_step:Step,
    actor:Actor
    ) returns (
    states:seq<State>,
    trace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires LeftMoversEnabledBeforeCrashConditions(clrr, initial_state, post_crash_state, crash_step, actor)
    ensures  StateNextSeq(states, trace, clrr.spec.next)
    ensures  |states| > 2
    ensures  states[0] == initial_state
    ensures  !clrr.crashed(states[|states|-2])
    ensures  !clrr.phase2(states[|states|-2], actor)
    ensures  forall i :: 0 <= i < |states|-2 ==> clrr.phase2(states[i], actor)
    ensures  forall i :: 0 <= i < |trace|-1 ==> clrr.idmap(trace[i]) == actor
    ensures  clrr.idmap(last(trace)) != actor
    ensures  clrr.crashed(last(states))
    ensures  BehaviorRefinesBehavior([initial_state, post_crash_state], states, clrr.relation)
  {
    var mover_states, mover_trace, crash_step', post_crash_state' :|
      && StateNextSeq(mover_states, mover_trace, clrr.spec.next)
      && mover_states[0] == initial_state
      && !clrr.crashed(last(mover_states))
      && !clrr.phase2(last(mover_states), actor)
      && (forall i :: 0 <= i < |mover_states|-1 ==> clrr.phase2(mover_states[i], actor))
      && (forall step :: step in mover_trace ==> clrr.idmap(step) == actor)
      && ActionTuple(last(mover_states), post_crash_state', crash_step') in clrr.spec.next
      && clrr.idmap(crash_step') == clrr.idmap(crash_step)
      && clrr.crashed(post_crash_state')
      && RefinementPair(post_crash_state, post_crash_state') in clrr.relation;

    var pos := 0;
    while pos < |mover_trace|
      invariant 0 <= pos <= |mover_trace|
      invariant forall i :: 0 <= i <= pos ==> RefinementPair(initial_state, mover_states[i]) in clrr.relation
    {
      assert RefinementPair(initial_state, mover_states[pos]) in clrr.relation;
      assert ActionTuple(mover_states[pos], mover_states[pos+1], mover_trace[pos]) in clrr.spec.next;
      assert RefinementPair(mover_states[pos], mover_states[pos+1]) in clrr.relation;
      assert RefinementPair(initial_state, mover_states[pos+1]) in clrr.relation;
      pos := pos + 1;
    }

    states := mover_states + [post_crash_state'];
    trace := mover_trace + [crash_step'];
    var lm_map := [RefinementRange(0, |mover_states|-1), RefinementRange(|mover_states|, |mover_states|)];
    assert BehaviorRefinesBehaviorUsingRefinementMap([initial_state, post_crash_state], states, clrr.relation, lm_map);
  }

  lemma lemma_CreateLeftMoversBeforeCrash<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires !clrr.phase1(lstates[0], step_actor)
    requires !clrr.crashed(lstates[0])
    requires forall i :: 0 <= i < |ltrace| ==> clrr.idmap(ltrace[i]) != step_actor
    requires clrr.phase2(last(lstates), step_actor)
    requires clrr.crashed(last(lstates))
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  |hstates| > |lstates|
    ensures  forall i :: 0 <= i < |ltrace| ==> hstates[i] == lstates[i]
    ensures  forall i :: 0 <= i < |ltrace|-1 ==> htrace[i] == ltrace[i]
    ensures  forall i :: |ltrace|-1 <= i < |htrace|-1 ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: |ltrace|-1 <= i < |htrace|-1 ==> clrr.phase2(hstates[i], step_actor)
    ensures  clrr.idmap(last(htrace)) != step_actor
    ensures  !clrr.phase2(hstates[|htrace|-1], step_actor)
    ensures  !clrr.crashed(hstates[|hstates|-2])
    ensures  clrr.crashed(last(hstates))
  {
    var penult := |ltrace|-1;
    assert ActionTuple(lstates[penult], lstates[penult+1], ltrace[penult]) in clrr.spec.next;

    lemma_StateNextSeqMaintainsAnnotatedReachables(lstates, ltrace, clrr.spec);
    assert lstates[penult] in lstates;
    assert LeftMoversEnabledBeforeCrashConditions(clrr, lstates[penult], lstates[penult+1], ltrace[penult], step_actor);
    var end_states', end_trace' :=
      lemma_InstantiateLeftMoversBeforeCrash(clrr, lstates[penult], lstates[penult+1], ltrace[penult], step_actor);
    assert clrr.idmap(last(end_trace')) != step_actor;

    assert lstates[penult..] == [lstates[penult], lstates[penult+1]];
    lemma_ExtendBehaviorRefinesBehaviorLeft(lstates[penult..], end_states', clrr.relation, lstates[..penult]);
    hstates := lstates[..penult] + end_states';
    htrace := ltrace[..penult] + end_trace';
    lemma_LastOfConcatenationIsLastOfLatter(ltrace[..penult], end_trace');
    assert last(htrace) == last(end_trace');
    lemma_TakePlusDropIsSeq(lstates, penult);
    assert BehaviorRefinesBehavior(lstates, hstates, clrr.relation);

    assert |lstates[..penult]| == penult;
    assert |ltrace[..penult]| == penult;

    forall i {:trigger ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next} | 0 <= i < |htrace|
      ensures ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next
    {
      lemma_IndexIntoConcatenation(lstates[..penult], end_states', i);
      lemma_IndexIntoConcatenation(lstates[..penult], end_states', i+1);
      lemma_IndexIntoConcatenation(ltrace[..penult], end_trace', i);

      if i < penult-1 {
        assert hstates[i] == lstates[i];
        assert hstates[i+1] == lstates[i+1];
        assert htrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
      else if i == penult - 1 {
        assert hstates[i] == lstates[i];
        assert hstates[i+1] == end_states'[0] == lstates[penult] == lstates[i+1];
        assert htrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
      else {
        var iadj := i - penult;
        assert hstates[i] == end_states'[iadj];
        calc {
          hstates[i+1];
          end_states'[i+1-penult];
            { assert i+1-penult == iadj+1; }
          end_states'[iadj+1];
        }
        assert htrace[i] == end_trace'[iadj];
        assert ActionTuple(end_states'[iadj], end_states'[iadj+1], end_trace'[iadj]) in clrr.spec.next;
      }
    }
    assert StateNextSeq(hstates, htrace, clrr.spec.next);

    forall i | 0 <= i < |ltrace|
      ensures hstates[i] == lstates[i]
    {
      lemma_IndexIntoConcatenation(lstates[..penult], end_states', i);

      if i < penult {
        assert hstates[i] == lstates[..penult][i] == lstates[i];
      }
      else {
        assert i == penult;
        assert hstates[i] == end_states'[0] == lstates[penult] == lstates[i];
      }
    }

    forall i | 0 <= i < |ltrace|-1
      ensures htrace[i] == ltrace[i]
    {
      lemma_IndexIntoConcatenation(lstates[..penult], end_states', i);

      assert htrace[i] == ltrace[..penult][i] == ltrace[i];
    }
  }

  lemma lemma_BringLeftMoversToStartByCreatingLeftMoversBeforeCrash<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires !clrr.phase1(lstates[0], step_actor)
    requires !clrr.crashed(lstates[0])
    requires forall i :: 0 <= i < |ltrace| ==> clrr.idmap(ltrace[i]) != step_actor
    requires clrr.phase2(last(lstates), step_actor)
    requires clrr.crashed(last(lstates))
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates| + end_pos
    ensures  0 <= end_pos < |hstates|
    ensures  var s := hstates[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: 0 <= i < end_pos ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: 0 <= i < end_pos ==> clrr.phase2(hstates[i], step_actor)
  {
    var mstates, mtrace := lemma_CreateLeftMoversBeforeCrash(clrr, lstates, ltrace, step_actor);

    var hstates_trunc, htrace_trunc;
    hstates_trunc, htrace_trunc, end_pos :=
      lemma_BringLeftMoversToStartAfterCreatingLeftMovers(clrr, all_but_last(mstates), all_but_last(mtrace), step_actor, |ltrace|-1);
    assert !clrr.crashed(last(all_but_last(mstates)));
    assert last(hstates_trunc) == last(all_but_last(mstates));

    lemma_ExtendBehaviorRefinesBehaviorRightOne(all_but_last(mstates), hstates_trunc, clrr.relation, last(mstates));
    assert BehaviorRefinesBehavior(all_but_last(mstates) + [last(mstates)], hstates_trunc + [last(mstates)], clrr.relation);
    hstates := hstates_trunc + [last(mstates)];
    htrace := htrace_trunc + [last(mtrace)];
    lemma_AllButLastPlusLastIsSeq(mstates);
    assert BehaviorRefinesBehavior(mstates, hstates, clrr.relation);

    forall i {:trigger ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next} | 0 <= i < |htrace|
      ensures ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next
    {
      if i < |htrace|-1 {
        assert hstates[i] == hstates_trunc[i];
        assert hstates[i+1] == hstates_trunc[i+1];
        assert htrace[i] == htrace_trunc[i];
        assert ActionTuple(hstates_trunc[i], hstates_trunc[i+1], htrace_trunc[i]) in clrr.spec.next;
      }
      else {
        var j := |mstates|-2;
        assert hstates[i] == last(hstates_trunc) == last(all_but_last(mstates)) == mstates[j];
        assert hstates[i+1] == last(mstates) == mstates[j+1];
        assert htrace[i] == last(mtrace) == mtrace[j];
        assert ActionTuple(mstates[j], mstates[j+1], mtrace[j]) in clrr.spec.next;
      }
    }

    assert StateNextSeq(hstates, htrace, clrr.spec.next);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
  }

  lemma lemma_BringLeftMoversToStartAfterCreatingLeftMovers<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    left_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= left_mover_pos < |ltrace|
    requires forall i :: 0 <= i < left_mover_pos ==> clrr.idmap(ltrace[i]) != step_actor
    requires forall i :: left_mover_pos <= i < |ltrace| ==> clrr.idmap(ltrace[i]) == step_actor
    requires forall i :: left_mover_pos <= i < |ltrace| ==> clrr.phase2(lstates[i], step_actor)
    requires clrr.crashed(last(lstates)) || !clrr.phase2(last(lstates), step_actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates|
    ensures  end_pos == |ltrace| - left_mover_pos
    ensures  0 <= end_pos < |hstates|
    ensures  var s := hstates[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: 0 <= i < end_pos ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: 0 <= i < end_pos ==> clrr.phase2(hstates[i], step_actor)
    ensures  !clrr.crashed(last(lstates)) ==> last(hstates) == last(lstates)
    decreases |lstates|
  {
    end_pos := |ltrace| - left_mover_pos;

    var mstates, mtrace := lemma_BringLeftMoverToStart(clrr, lstates, ltrace, step_actor, left_mover_pos);

    if left_mover_pos == |ltrace|-1 {
      hstates := mstates;
      htrace := mtrace;
      return;
    }

    var pos_plus := left_mover_pos+1;
    assert ActionTuple(lstates[pos_plus], lstates[pos_plus+1], ltrace[pos_plus]) in clrr.spec.next;

    lemma_ReduceStateNextSeqLeft(mstates, mtrace, clrr.spec.next);
    lemma_StateNextSeqMaintainsAnnotatedReachables(mstates, mtrace, clrr.spec);
    assert mstates[1..][0] in mstates;
    var hstates_trunc, htrace_trunc, end_pos_trunc :=
      lemma_BringLeftMoversToStartAfterCreatingLeftMovers(clrr, mstates[1..], mtrace[1..], step_actor, left_mover_pos);

    hstates := [mstates[0]] + hstates_trunc;
    htrace := [mtrace[0]] + htrace_trunc;
    lemma_ExtendStateNextSeqLeft(hstates_trunc, htrace_trunc, clrr.spec.next, mstates[0], mtrace[0]);
    lemma_ExtendBehaviorRefinesBehaviorLeftOne(mstates[1..], hstates_trunc, clrr.relation, mstates[0]);
    lemma_SequenceIsCarPlusCdr(mstates);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
  }

  lemma lemma_BringLeftMoversToStartByCreatingLeftMoversAtEnd<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires forall i :: 0 <= i < |ltrace| ==> clrr.idmap(ltrace[i]) != step_actor
    requires clrr.phase2(last(lstates), step_actor)
    requires !clrr.crashed(last(lstates))
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates| + end_pos
    ensures  0 <= end_pos < |hstates|
    ensures  var s := hstates[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: 0 <= i < end_pos ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: 0 <= i < end_pos ==> clrr.phase2(hstates[i], step_actor)
  {
    lemma_StateNextSeqMaintainsAnnotatedReachables(lstates, ltrace, clrr.spec);
    assert last(lstates) in lstates;
    assert LeftMoversAlwaysEnabledConditions(clrr, last(lstates), step_actor);

    var end_states', end_trace' :|
          && StateNextSeq(end_states', end_trace', clrr.spec.next)
          && end_states'[0] == last(lstates)
          && (clrr.crashed(last(end_states')) || !clrr.phase2(last(end_states'), step_actor))
          && (forall i :: 0 <= i < |end_states'|-1 ==> clrr.phase2(end_states'[i], step_actor))
          && (forall step :: step in end_trace' ==> clrr.idmap(step) == step_actor);

    var pos := 0;
    while pos < |end_trace'|
      invariant 0 <= pos <= |end_trace'|
      invariant forall i :: 0 <= i <= pos ==> RefinementPair(last(lstates), end_states'[i]) in clrr.relation
    {
      assert RefinementPair(last(lstates), end_states'[pos]) in clrr.relation;
      assert ActionTuple(end_states'[pos], end_states'[pos+1], end_trace'[pos]) in clrr.spec.next;
      assert RefinementPair(end_states'[pos], end_states'[pos+1]) in clrr.relation;
      assert RefinementPair(last(lstates), end_states'[pos+1]) in clrr.relation;
      pos := pos + 1;
    }

    var end_states := [last(lstates)];
    var lm_map := [RefinementRange(0, |end_trace'|)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(end_states, end_states', clrr.relation, lm_map);
    assert BehaviorRefinesBehavior(end_states, end_states', clrr.relation);
    lemma_ExtendBehaviorRefinesBehaviorLeft(end_states, end_states', clrr.relation, all_but_last(lstates));

    var mstates := all_but_last(lstates) + end_states';
    var mtrace := ltrace + end_trace';
    lemma_AllButLastPlusLastIsSeq(lstates);
    assert BehaviorRefinesBehavior(lstates, mstates, clrr.relation);

    forall i {:trigger ActionTuple(mstates[i], mstates[i+1], mtrace[i]) in clrr.spec.next} | 0 <= i < |mtrace|
      ensures ActionTuple(mstates[i], mstates[i+1], mtrace[i]) in clrr.spec.next
    {
      if i < |ltrace| {
        assert mstates[i] == lstates[i];
        assert mstates[i+1] == lstates[i+1];
        assert mtrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
      else {
        var iminus := i - |ltrace|;
        assert mstates[i] == end_states'[iminus];
        assert mstates[i+1] == end_states'[iminus+1];
        assert mtrace[i] == end_trace'[iminus];
        assert ActionTuple(end_states'[iminus], end_states'[iminus+1], end_trace'[iminus]) in clrr.spec.next;
      }
    }
    assert StateNextSeq(mstates, mtrace, clrr.spec.next);

    hstates, htrace, end_pos :=
      lemma_BringLeftMoversToStartAfterCreatingLeftMovers(clrr, mstates, mtrace, step_actor, |ltrace|);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
  }

  lemma lemma_BringLeftMoversToStartByCreatingLeftMovers<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires !clrr.phase1(lstates[0], step_actor)
    requires !clrr.crashed(lstates[0])
    requires clrr.phase2(lstates[0], step_actor)
    requires forall i :: 0 <= i < |ltrace| ==> clrr.idmap(ltrace[i]) != step_actor
    requires clrr.phase2(last(lstates), step_actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates| + end_pos
    ensures  0 <= end_pos < |hstates|
    ensures  var s := hstates[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: 0 <= i < end_pos ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: 0 <= i < end_pos ==> clrr.phase2(hstates[i], step_actor)
  {
    if clrr.crashed(last(lstates)) {
      hstates, htrace, end_pos :=
        lemma_BringLeftMoversToStartByCreatingLeftMoversBeforeCrash(clrr, lstates, ltrace, step_actor);
    }
    else {
      hstates, htrace, end_pos :=
        lemma_BringLeftMoversToStartByCreatingLeftMoversAtEnd(clrr, lstates, ltrace, step_actor);
    }
  }

  lemma lemma_BringLeftMoverLeftOneCaseCrashing<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires |ltrace| == 2
    requires clrr.idmap(ltrace[0]) != step_actor
    requires clrr.idmap(ltrace[1]) == step_actor
    requires clrr.phase2(lstates[1], step_actor)
    requires clrr.crashed(lstates[2])
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates|
    ensures  |htrace| == 1
    ensures  clrr.crashed(hstates[1])
    ensures  clrr.idmap(htrace[0]) == step_actor
    ensures  clrr.phase2(hstates[0], step_actor)
  {
    var zero := 0;
    assert ActionTuple(lstates[zero], lstates[zero+1], ltrace[zero]) in clrr.spec.next;
    var one := 1;
    assert ActionTuple(lstates[one], lstates[one+1], ltrace[one]) in clrr.spec.next;
    assert LeftMoverSelfCrashPreservationConditions(clrr, lstates[0], lstates[1], lstates[2], ltrace[0], ltrace[1]);
    var left_mover', state_after_left_mover' :|
          && clrr.idmap(left_mover') == clrr.idmap(ltrace[1])
          && ActionTuple(lstates[0], state_after_left_mover', left_mover') in clrr.spec.next
          && clrr.crashed(state_after_left_mover')
          && RefinementPair(lstates[2], state_after_left_mover') in clrr.relation;

    hstates := [lstates[0], state_after_left_mover'];
    htrace := [left_mover'];

    var lh_map := [RefinementRange(0, 0), RefinementRange(1, 1), RefinementRange(1, 1)];
    forall i, j {:trigger RefinementPair(lstates[i], hstates[j]) in clrr.relation}
      | 0 <= i < |lstates| && lh_map[i].first <= j <= lh_map[i].last
      ensures RefinementPair(lstates[i], hstates[j]) in clrr.relation
    {
      if i == 0 && j == 0 {
        assert lstates[i] == lstates[0];
        assert hstates[j] == lstates[0];
        assert RefinementPair(lstates[0], lstates[0]) in clrr.relation;
      }
      else if i == 1 && j == 1 {
        assert lstates[i] == lstates[1];
        assert hstates[j] == state_after_left_mover';
        assert ActionTuple(lstates[1], lstates[2], ltrace[1]) in clrr.spec.next;
        assert RefinementPair(lstates[1], lstates[2]) in clrr.relation;
        assert RefinementPair(lstates[2], state_after_left_mover') in clrr.relation;
        assert RefinementPair(lstates[1], state_after_left_mover') in clrr.relation;
      }
      else {
        assert i == 2 && j == 1;
        assert lstates[i] == lstates[2];
        assert hstates[j] == state_after_left_mover';
        assert RefinementPair(lstates[2], state_after_left_mover') in clrr.relation;
      }
    }
    assert BehaviorRefinesBehaviorUsingRefinementMap(lstates, hstates, clrr.relation, lh_map);
    assert BehaviorRefinesBehavior(lstates, hstates, clrr.relation);
  }

  lemma lemma_BringLeftMoverLeftOneCaseNotCrashing<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires |ltrace| >= 2
    requires clrr.idmap(ltrace[0]) != step_actor
    requires clrr.idmap(ltrace[1]) == step_actor
    requires clrr.phase2(lstates[1], step_actor)
    requires !clrr.crashed(lstates[2])
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| == |lstates|
    ensures  !clrr.crashed(hstates[1])
    ensures  !clrr.crashed(hstates[2])
    ensures  hstates[2..] == lstates[2..]
    ensures  htrace[2..] == ltrace[2..]
    ensures  clrr.idmap(htrace[0]) == step_actor
    ensures  clrr.idmap(htrace[1]) != step_actor
    ensures  clrr.phase2(hstates[0], step_actor)
    ensures  clrr.phase2(hstates[1], step_actor) <==> clrr.phase2(lstates[2], step_actor)
  {
    var zero := 0;
    assert ActionTuple(lstates[zero], lstates[zero+1], ltrace[zero]) in clrr.spec.next;
    var one := 1;
    assert ActionTuple(lstates[one], lstates[one+1], ltrace[one]) in clrr.spec.next;
    assert LeftMoversCommuteConditions(clrr, lstates[0], lstates[1], lstates[2], ltrace[0], ltrace[1]);
    var new_middle_state, left_mover', other_step' :|
          && ActionTuple(lstates[0], new_middle_state, left_mover') in clrr.spec.next
          && ActionTuple(new_middle_state, lstates[2], other_step') in clrr.spec.next
          && clrr.idmap(left_mover') == clrr.idmap(ltrace[1])
          && clrr.idmap(other_step') == clrr.idmap(ltrace[0]);

    var hstates_init := [lstates[0], new_middle_state, lstates[2]];
    var htrace_init := [left_mover', other_step'];
    assert StateNextSeq(hstates_init, htrace_init, clrr.spec.next);

    hstates := hstates_init + lstates[3..];
    htrace := htrace_init + ltrace[2..];
    assert StateNextSeq(hstates, htrace, clrr.spec.next);

    var lh_map := [RefinementRange(0, 1), RefinementRange(2, 2), RefinementRange(2, 2)];
    var lstates_init := lstates[..3];
    forall i, j {:trigger RefinementPair(lstates_init[i], hstates_init[j]) in clrr.relation}
      | 0 <= i < |lstates_init| && lh_map[i].first <= j <= lh_map[i].last
      ensures RefinementPair(lstates_init[i], hstates_init[j]) in clrr.relation
    {
      if i == 0 && j == 0 {
        assert lstates_init[i] == lstates[0];
        assert hstates_init[j] == lstates[0];
        assert RefinementPair(lstates[0], lstates[0]) in clrr.relation;
      }
      else if i == 0 && j == 1 {
        assert lstates_init[i] == lstates[0];
        assert hstates_init[j] == new_middle_state;
        assert ActionTuple(lstates[0], new_middle_state, left_mover') in clrr.spec.next;
        assert RefinementPair(lstates[0], new_middle_state) in clrr.relation;
      }
      else if i == 1 && j == 2 {
        assert lstates_init[i] == lstates[1];
        assert hstates_init[j] == lstates[2];
        assert ActionTuple(lstates[1], lstates[2], ltrace[1]) in clrr.spec.next;
        assert RefinementPair(lstates[1], lstates[2]) in clrr.relation;
      }
      else {
        assert i == 2 && j == 2;
        assert lstates_init[i] == lstates[2];
        assert hstates_init[j] == lstates[2];
        assert RefinementPair(lstates[2], lstates[2]) in clrr.relation;
      }
    }
    assert BehaviorRefinesBehaviorUsingRefinementMap(lstates_init, hstates_init, clrr.relation, lh_map);
    assert BehaviorRefinesBehavior(lstates_init, hstates_init, clrr.relation);
    lemma_ExtendBehaviorRefinesBehaviorRight(lstates_init, hstates_init, clrr.relation, lstates[3..]);
    lemma_TakePlusDropIsSeq(lstates, 3);
  }

  lemma lemma_BringLeftMoverLeftOne<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires |ltrace| >= 2
    requires clrr.idmap(ltrace[0]) != step_actor
    requires clrr.idmap(ltrace[1]) == step_actor
    requires clrr.phase2(lstates[1], step_actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates|
    ensures  |htrace| > 0
    ensures  !clrr.phase1(hstates[1], step_actor)
    ensures  if clrr.crashed(lstates[2]) then
               && |hstates| == 2
               && clrr.crashed(hstates[1])
             else
               && |hstates| == |lstates|
               && hstates[2..] == lstates[2..]
               && htrace[2..] == ltrace[2..]
               && !clrr.crashed(hstates[1])
               && (clrr.phase2(hstates[1], step_actor) <==> clrr.phase2(lstates[2], step_actor))
               && clrr.idmap(htrace[1]) != step_actor
    ensures  clrr.idmap(htrace[0]) == step_actor
    ensures  clrr.phase2(hstates[0], step_actor)
  {
    if clrr.crashed(lstates[2]) {
      if 2 < |ltrace| {
        var two := 2;
        assert ActionTuple(lstates[two], lstates[two+1], ltrace[two]) in clrr.spec.next;
        assert false;
      }
      hstates, htrace := lemma_BringLeftMoverLeftOneCaseCrashing(clrr, lstates, ltrace, step_actor);
    }
    else {
      hstates, htrace := lemma_BringLeftMoverLeftOneCaseNotCrashing(clrr, lstates, ltrace, step_actor);
    }
  }
   
  lemma lemma_BringLeftMoverToStart<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    left_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= left_mover_pos < |ltrace|
    requires forall i :: 0 <= i < left_mover_pos ==> clrr.idmap(ltrace[i]) != step_actor
    requires clrr.idmap(ltrace[left_mover_pos]) == step_actor
    requires clrr.phase2(lstates[left_mover_pos], step_actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates|
    ensures  |htrace| > 0
    ensures  clrr.idmap(htrace[0]) == step_actor
    ensures  !clrr.phase1(hstates[1], step_actor)
    ensures  clrr.phase2(hstates[0], step_actor)
    ensures  if clrr.crashed(lstates[left_mover_pos+1]) then
               && |hstates| == 2
               && clrr.crashed(hstates[1])
             else
               && |hstates| == |lstates|
               && !clrr.crashed(hstates[1])
               && hstates[left_mover_pos+1..] == lstates[left_mover_pos+1..]
               && htrace[left_mover_pos+1..] == ltrace[left_mover_pos+1..]
               && (clrr.phase2(hstates[1], step_actor) <==> clrr.phase2(lstates[left_mover_pos+1], step_actor))
               && (forall i :: 1 <= i <= left_mover_pos ==> clrr.idmap(htrace[i]) != step_actor)
    decreases left_mover_pos
  {
    if clrr.crashed(lstates[left_mover_pos+1]) && |ltrace| > left_mover_pos+1 {
      var pos_plus := left_mover_pos + 1;
      assert ActionTuple(lstates[pos_plus], lstates[pos_plus+1], ltrace[pos_plus]) in clrr.spec.next;
      assert false;
    }

    if left_mover_pos == 0 {
      hstates := lstates;
      htrace := ltrace;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lstates, clrr.relation);
      return;
    }

    var prev := left_mover_pos-1;
    lemma_DropStateNextSeq(lstates, ltrace, clrr.spec.next, prev);
    lemma_StateNextSeqMaintainsAnnotatedReachables(lstates, ltrace, clrr.spec);
    assert lstates[prev..][0] in lstates;
    var mstates_trunc, mtrace_trunc := lemma_BringLeftMoverLeftOne(clrr, lstates[prev..], ltrace[prev..], step_actor);

    if !clrr.crashed(lstates[left_mover_pos+1]) {
      assert !clrr.crashed(lstates[prev..][2]);
      assert |mstates_trunc| == |lstates[prev..]| == |lstates| - prev;
      assert mtrace_trunc[2..] == ltrace[prev..][2..] == ltrace[left_mover_pos+1..];
    }

    var mstates := lstates[..prev] + mstates_trunc;
    var mtrace := ltrace[..prev] + mtrace_trunc;
    lemma_ExtendBehaviorRefinesBehaviorLeft(lstates[prev..], mstates_trunc, clrr.relation, lstates[..prev]);
    lemma_TakePlusDropIsSeq(lstates, prev);
    lemma_TakePlusDropIsSeq(ltrace, prev);
    assert BehaviorRefinesBehavior(lstates, mstates, clrr.relation);

    forall i {:trigger ActionTuple(mstates[i], mstates[i+1], mtrace[i]) in clrr.spec.next} | 0 <= i < |mtrace|
      ensures ActionTuple(mstates[i], mstates[i+1], mtrace[i]) in clrr.spec.next
    {
      if i < prev-1 {
        assert mstates[i] == lstates[i];
        assert mstates[i+1] == lstates[i+1];
        assert mtrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
      else if i == prev-1 {
        assert mstates[i] == lstates[i];
        assert mstates[i+1] == mstates_trunc[0] == lstates[prev..][0] == lstates[prev] == lstates[i+1];
        assert mtrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
      else {
        var iminus := i-prev;
        assert mstates[i] == mstates_trunc[iminus];
        assert mstates[i+1] == mstates_trunc[iminus+1];
        assert mtrace[i] == mtrace_trunc[iminus];
        assert ActionTuple(mstates_trunc[iminus], mstates_trunc[iminus+1], mtrace_trunc[iminus]) in clrr.spec.next;
      }
    }
    assert StateNextSeq(mstates, mtrace, clrr.spec.next);

    hstates, htrace := lemma_BringLeftMoverToStart(clrr, mstates, mtrace, step_actor, left_mover_pos-1);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
  }

  lemma lemma_FindFirstLeftMover<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    states:seq<State>,
    trace:seq<Step>,
    step_actor:Actor
    ) returns (
    pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(states, trace, clrr.spec.next)
    requires states[0] in AnnotatedReachables(clrr.spec)
    requires clrr.phase2(states[0], step_actor)

    ensures  0 <= pos <= |trace|
    ensures  forall i :: 0 <= i < pos ==> clrr.idmap(trace[i]) != step_actor
    ensures  clrr.phase2(states[pos], step_actor)
    ensures  pos < |trace| ==> clrr.idmap(trace[pos]) == step_actor
  {
    pos := 0;
    while pos < |trace| && clrr.idmap(trace[pos]) != step_actor
      invariant 0 <= pos <= |trace|
      invariant forall i :: 0 <= i < pos ==> clrr.idmap(trace[i]) != step_actor
      invariant clrr.phase2(states[pos], step_actor)
    {
      assert ActionTuple(states[pos], states[pos+1], trace[pos]) in clrr.spec.next;
      pos := pos + 1;
    }
  }

  lemma lemma_BringLeftMoversToStart<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires clrr.crashed(lstates[0]) || !clrr.phase1(lstates[0], step_actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |hstates| <= |lstates| + end_pos
    ensures  0 <= end_pos < |hstates|
    ensures  var s := hstates[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: 0 <= i < end_pos ==> clrr.idmap(htrace[i]) == step_actor
    ensures  forall i :: 0 <= i < end_pos ==> clrr.phase2(hstates[i], step_actor)
    decreases |lstates|
  {
    if clrr.crashed(lstates[0]) || !clrr.phase2(lstates[0], step_actor) {
      hstates := lstates;
      htrace := ltrace;
      end_pos := 0;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lstates, clrr.relation);
      return;
    }

    var left_mover_pos := lemma_FindFirstLeftMover(clrr, lstates, ltrace, step_actor);
    if left_mover_pos == |ltrace| {
      hstates, htrace, end_pos := lemma_BringLeftMoversToStartByCreatingLeftMovers(clrr, lstates, ltrace, step_actor);
      return;
    }

    var mstates, mtrace := lemma_BringLeftMoverToStart(clrr, lstates, ltrace, step_actor, left_mover_pos);

    var zero := 0;
    assert ActionTuple(mstates[zero], mstates[zero+1], mtrace[zero]) in clrr.spec.next;
    lemma_NextMaintainsAnnotatedReachables(mstates[zero], mstates[zero+1], mtrace[zero], clrr.spec);
    lemma_ReduceStateNextSeqLeft(mstates, mtrace, clrr.spec.next);
    var m2states, m2trace, m2end_pos := lemma_BringLeftMoversToStart(clrr, mstates[1..], mtrace[1..], step_actor);

    hstates := [mstates[0]] + m2states;
    htrace := [mtrace[0]] + m2trace;
    lemma_ExtendStateNextSeqLeft(m2states, m2trace, clrr.spec.next, mstates[0], mtrace[0]);
    lemma_ExtendBehaviorRefinesBehaviorLeftOne(mstates[1..], m2states, clrr.relation, mstates[0]);
    lemma_SequenceIsCarPlusCdr(mstates);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
    end_pos := m2end_pos + 1;
  }

  lemma lemma_EarlierStateInBehaviorAlsoNotCrashed<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    pos2:int,
    pos1:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= pos1 <= pos2 < |lb.states|
    requires !clrr.crashed(lb.states[pos2])
    ensures  !clrr.crashed(lb.states[pos1])
  {
    if pos1 < pos2 {
      var pos := pos2-1;
      assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in clrr.spec.next;
      lemma_EarlierStateInBehaviorAlsoNotCrashed(clrr, lb, pos, pos1);
    }
  }

  lemma lemma_EstablishBehaviorRefinesBehaviorAfterMovingRightMoverRight<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires 0 <= right_mover_pos < |lb.trace|-1
    requires clrr.idmap(lb.trace[right_mover_pos]) == step_actor
    requires forall i :: right_mover_pos < i < |lb.trace| ==> clrr.idmap(lb.trace[i]) != step_actor
    requires clrr.phase1(lb.states[right_mover_pos+1], step_actor)
    requires ActionTuple(lb.states[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lb.states[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(lb.trace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(lb.trace[right_mover_pos])
    requires hb.states == lb.states[..right_mover_pos+1] + [new_middle_state] + lb.states[right_mover_pos+2..]
    requires hb.trace == lb.trace[..right_mover_pos] + [other_step', right_mover'] + lb.trace[right_mover_pos+2..]

    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  last(hb.states) == last(lb.states)
    ensures  |hb.states| == |lb.states|
    ensures  |hb.trace| == |lb.trace|
    ensures  clrr.idmap(hb.trace[right_mover_pos+1]) == step_actor
  {
    var lb2 := lb.states[right_mover_pos..right_mover_pos+3];
    var hb2 := [lb.states[right_mover_pos], new_middle_state, lb.states[right_mover_pos+2]];

    var right_mover_pos_plus := right_mover_pos+1;

    forall ensures RefinementPair(lb2[2], hb2[1]) in clrr.relation
    {
      assert ActionTuple(new_middle_state, lb.states[right_mover_pos+2], right_mover') in clrr.spec.next;
      assert clrr.idmap(right_mover') == step_actor;
      assert ActionTuple(lb.states[right_mover_pos_plus], lb.states[right_mover_pos_plus+1], lb.trace[right_mover_pos_plus])
               in clrr.spec.next;
      assert clrr.idmap(lb.trace[right_mover_pos_plus]) != step_actor;
      assert clrr.phase1(lb.states[right_mover_pos_plus+1], step_actor);
      lemma_EarlierStateInBehaviorAlsoNotCrashed(clrr, lb, |lb.states|-1, right_mover_pos+2);
      assert !clrr.crashed(lb.states[right_mover_pos+2]);
      assert RefinementPair(lb.states[right_mover_pos+2], new_middle_state) in clrr.relation;
    }

    forall ensures RefinementPair(lb2[1], hb2[0]) in clrr.relation
    {
      assert ActionTuple(lb.states[right_mover_pos], lb.states[right_mover_pos+1], lb.trace[right_mover_pos]) in clrr.spec.next;
      assert clrr.idmap(lb.trace[right_mover_pos]) == step_actor;
      lemma_EarlierStateInBehaviorAlsoNotCrashed(clrr, lb, |lb.states|-1, right_mover_pos+1);
      assert !clrr.crashed(lb.states[right_mover_pos+1]);
      assert RefinementPair(lb.states[right_mover_pos+1], lb.states[right_mover_pos]) in clrr.relation;
    }

    forall ensures RefinementPair(lb2[0], hb2[0]) in clrr.relation
    {
      assert hb2[0] == lb2[0];
    }

    forall ensures RefinementPair(lb2[2], hb2[2]) in clrr.relation
    {
      assert hb2[2] == lb2[2];
    }

    var lh_map := [RefinementRange(0, 0), RefinementRange(0, 0), RefinementRange(1, 2)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb2, hb2, clrr.relation, lh_map);

    lemma_ExtendBehaviorRefinesBehaviorLeft(lb2, hb2, clrr.relation, lb.states[..right_mover_pos]);
    lemma_ExtendBehaviorRefinesBehaviorRight(lb.states[..right_mover_pos] + lb2, lb.states[..right_mover_pos] + hb2, clrr.relation,
                                             lb.states[right_mover_pos+3..]);
    assert BehaviorRefinesBehavior(lb.states[..right_mover_pos] + lb2 + lb.states[right_mover_pos+3..],
                                   lb.states[..right_mover_pos] + hb2 + lb.states[right_mover_pos+3..], clrr.relation);
    lemma_SeqEqualsThreeWayConcatentation(lb.states, right_mover_pos, right_mover_pos+3);

    assert hb.states == lb.states[..right_mover_pos] + hb2 + lb.states[right_mover_pos+3..];
  }

  lemma lemma_EstablishBehaviorSatisfiesSpecAfterMovingRightMoverRight<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires 0 <= right_mover_pos < |lb.trace|-1
    requires clrr.idmap(lb.trace[right_mover_pos]) == step_actor
    requires forall i :: right_mover_pos < i < |lb.trace| ==> clrr.idmap(lb.trace[i]) != step_actor
    requires clrr.phase1(lb.states[right_mover_pos+1], step_actor)
    requires ActionTuple(lb.states[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lb.states[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(lb.trace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(lb.trace[right_mover_pos])
    requires hb.states == lb.states[..right_mover_pos+1] + [new_middle_state] + lb.states[right_mover_pos+2..]
    requires hb.trace == lb.trace[..right_mover_pos] + [other_step', right_mover'] + lb.trace[right_mover_pos+2..]

    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
  {
    forall i {:trigger ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in clrr.spec.next}
      | 0 <= i < |hb.trace|
      ensures ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in clrr.spec.next
    {
      if i == right_mover_pos {
        assert hb.states[i] == lb.states[right_mover_pos];
        assert hb.states[i+1] == new_middle_state;
        assert hb.trace[i] == other_step';
        assert ActionTuple(lb.states[right_mover_pos], new_middle_state, other_step') in clrr.spec.next;
      }
      else if i == right_mover_pos + 1 {
        assert hb.states[i] == new_middle_state;
        assert hb.states[i+1] == lb.states[right_mover_pos+2];
        assert hb.trace[i] == right_mover';
        assert ActionTuple(new_middle_state, lb.states[right_mover_pos+2], right_mover') in clrr.spec.next;
      }
      else {
        assert hb.states[i] == lb.states[i];
        assert hb.states[i+1] == lb.states[i+1];
        assert hb.trace[i] == lb.trace[i];
        assert ActionTuple(lb.states[i], lb.states[i+1], lb.trace[i]) in clrr.spec.next;
      }
    }
  }

  lemma lemma_EstablishStillNoNonmoversAfterMovingRightMoverRight<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires 0 <= right_mover_pos < |lb.trace|-1
    requires clrr.idmap(lb.trace[right_mover_pos]) == step_actor
    requires forall i :: right_mover_pos < i < |lb.trace| ==> clrr.idmap(lb.trace[i]) != step_actor
    requires clrr.phase1(lb.states[right_mover_pos+1], step_actor)
    requires ActionTuple(lb.states[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lb.states[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(lb.trace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(lb.trace[right_mover_pos])
    requires hb.states == lb.states[..right_mover_pos+1] + [new_middle_state] + lb.states[right_mover_pos+2..]
    requires hb.trace == lb.trace[..right_mover_pos] + [other_step', right_mover'] + lb.trace[right_mover_pos+2..]

    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
  {
    var right_mover_pos_plus := right_mover_pos + 1;

    lemma_EarlierStateInBehaviorAlsoNotCrashed(clrr, lb, |lb.states|-1, right_mover_pos+2);

    forall i | 0 <= i < |hb.trace|
      ensures !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    {
      if i == right_mover_pos {
        assert hb.states[i] == lb.states[right_mover_pos];
        assert hb.states[i+1] == new_middle_state;
        assert !IsNonmoverPos(clrr, lb.states, lb.trace, right_mover_pos_plus);
        assert ActionTuple(lb.states[right_mover_pos], lb.states[right_mover_pos+1], lb.trace[right_mover_pos]) in clrr.spec.next;
        assert ActionTuple(new_middle_state, lb.states[right_mover_pos_plus+1], right_mover') in clrr.spec.next;
        assert !IsNonmoverStep(clrr, lb.states[right_mover_pos], new_middle_state, clrr.idmap(hb.trace[i]));
      }
      else if i == right_mover_pos + 1 {
        assert hb.states[i] == new_middle_state;
        assert hb.states[i+1] == lb.states[right_mover_pos+2];
      }
      else {
        assert !IsNonmoverPos(clrr, lb.states, lb.trace, i);
      }
    }
  }

  lemma lemma_MoveRightMoverRight<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires 0 <= right_mover_pos < |lb.trace|-1
    requires clrr.idmap(lb.trace[right_mover_pos]) == step_actor
    requires forall i :: right_mover_pos < i < |lb.trace| ==> clrr.idmap(lb.trace[i]) != step_actor
    requires clrr.phase1(lb.states[right_mover_pos+1], step_actor)

    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  last(hb.states) == last(lb.states)
    ensures  |hb.states| == |lb.states|
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    ensures  clrr.idmap(hb.trace[right_mover_pos+1]) == step_actor
    ensures  clrr.phase1(hb.states[right_mover_pos+2], step_actor)
    ensures  forall i :: right_mover_pos + 1 < i < |hb.trace| ==> clrr.idmap(hb.trace[i]) != step_actor
  {
    assert ActionTuple(lb.states[right_mover_pos], lb.states[right_mover_pos+1], lb.trace[right_mover_pos]) in clrr.spec.next;
    var right_mover_pos_plus := right_mover_pos + 1;
    assert ActionTuple(lb.states[right_mover_pos_plus], lb.states[right_mover_pos_plus+1], lb.trace[right_mover_pos_plus]) in clrr.spec.next;
    lemma_StateInAnnotatedBehaviorInAnnotatedReachables(clrr.spec, lb, right_mover_pos);
    lemma_EarlierStateInBehaviorAlsoNotCrashed(clrr, lb, |lb.states|-1, right_mover_pos_plus+1);
    assert RightMoversCommuteConditions(clrr, lb.states[right_mover_pos], lb.states[right_mover_pos+1],
                                        lb.states[right_mover_pos_plus+1], lb.trace[right_mover_pos],
                                        lb.trace[right_mover_pos+1]);
    var new_middle_state, other_step', right_mover' :|
      && ActionTuple(lb.states[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
      && ActionTuple(new_middle_state, lb.states[right_mover_pos_plus+1], right_mover') in clrr.spec.next
      && clrr.idmap(other_step') == clrr.idmap(lb.trace[right_mover_pos+1])
      && clrr.idmap(right_mover') == clrr.idmap(lb.trace[right_mover_pos]);

    var hstates := lb.states[..right_mover_pos+1] + [new_middle_state] + lb.states[right_mover_pos+2..];
    var htrace := lb.trace[..right_mover_pos] + [other_step', right_mover'] + lb.trace[right_mover_pos+2..];
    hb := AnnotatedBehavior(hstates, htrace);

    lemma_EstablishBehaviorRefinesBehaviorAfterMovingRightMoverRight(
      clrr, lb, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hb);
    lemma_EstablishBehaviorSatisfiesSpecAfterMovingRightMoverRight(
      clrr, lb, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hb);
    lemma_EstablishStillNoNonmoversAfterMovingRightMoverRight(
      clrr, lb, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hb);
  }

  lemma lemma_MoveRightMoverToEnd<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires 0 <= right_mover_pos < |lb.trace|
    requires clrr.idmap(lb.trace[right_mover_pos]) == step_actor
    requires forall i :: right_mover_pos < i < |lb.trace| ==> clrr.idmap(lb.trace[i]) != step_actor
    requires clrr.phase1(lb.states[right_mover_pos+1], step_actor)

    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  last(hb.states) == last(lb.states)
    ensures  |hb.states| == |lb.states|
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    ensures  clrr.idmap(last(hb.trace)) == step_actor

    decreases |lb.trace| - right_mover_pos
  {
    if right_mover_pos == |lb.trace|-1 {
      hb := lb;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
      return;
    }

    var mb := lemma_MoveRightMoverRight(clrr, lb, step_actor, right_mover_pos);
    hb := lemma_MoveRightMoverToEnd(clrr, mb, step_actor, right_mover_pos+1);
    lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);
  }

  lemma lemma_BringRightMoversToEnd<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    step_actor:Actor
    ) returns (
    hb:AnnotatedBehavior<State, Step>,
    start_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires !clrr.crashed(last(lb.states))
    requires !clrr.phase2(last(lb.states), step_actor)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  last(hb.states) == last(lb.states)
    ensures  |hb.states| == |lb.states|
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    ensures  0 <= start_pos < |hb.states|
    ensures  !clrr.crashed(hb.states[start_pos])
    ensures  !clrr.phase1(hb.states[start_pos], step_actor)
    ensures  !clrr.phase2(hb.states[start_pos], step_actor)
    ensures  forall i :: start_pos <= i < |hb.trace| ==> clrr.idmap(hb.trace[i]) == step_actor
    ensures  forall i :: start_pos < i < |hb.states| ==> clrr.phase1(hb.states[i], step_actor)
    decreases |lb.states|
  {
    if !clrr.phase1(last(lb.states), step_actor) {
      start_pos := |lb.states| - 1;
      hb := lb;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
      return;
    }

    var right_mover_pos := lemma_FindLastRightMover(clrr, lb, step_actor);
    var mb := lemma_MoveRightMoverToEnd(clrr, lb, step_actor, right_mover_pos);

    assert BehaviorRefinesBehavior(lb.states, mb.states, clrr.relation);

    var mb_trunc := AnnotatedBehavior(all_but_last(mb.states), all_but_last(mb.trace));
    lemma_ReduceStateNextSeqRight(mb.states, mb.trace, clrr.spec.next);

    forall i | 0 <= i < |mb_trunc.states|-1
      ensures !IsNonmoverPos(clrr, mb_trunc.states, mb_trunc.trace, i)
    {
      assert !IsNonmoverPos(clrr, mb.states, mb.trace, i);
    }

    forall ensures !clrr.crashed(last(mb_trunc.states))
    {
      var penult := |mb.states|-2;
      assert ActionTuple(mb.states[penult], mb.states[penult+1], mb.trace[penult]) in clrr.spec.next;
    }

    var mb2;
    mb2, start_pos := lemma_BringRightMoversToEnd(clrr, mb_trunc, step_actor);
    assert BehaviorRefinesBehavior(mb_trunc.states, mb2.states, clrr.relation);

    hb := AnnotatedBehavior(mb2.states + [last(mb.states)], mb2.trace + [last(mb.trace)]);
    lemma_ExtendBehaviorRefinesBehaviorRightOne(mb_trunc.states, mb2.states, clrr.relation, last(mb.states));
    lemma_AllButLastPlusLastIsSeq(mb.states);

    lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);
    lemma_ExtendStateNextSeqRight(mb2.states, mb2.trace, clrr.spec.next, last(mb.states), last(mb.trace));

    forall i | 0 <= i < |hb.trace|
      ensures !IsNonmoverPos(clrr, hb.states, hb.trace, i);
    {
      if i < |mb2.states|-1 {
        assert !IsNonmoverPos(clrr, mb2.states, mb2.trace, i);
      }
      else {
        assert i == |mb2.states|-1 == |mb.states|-2;
        assert hb.states[i] == last(mb2.states) == last(mb_trunc.states) == mb.states[|mb.states|-2];
        assert hb.states[i+1] == last(mb.states);
        assert !IsNonmoverPos(clrr, mb.states, mb.trace, i);
      }
    }
  }

  lemma lemma_FindLastRightMover<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    b:AnnotatedBehavior<State, Step>,
    step_actor:Actor
    ) returns (
    pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(b, clrr.spec)
    requires !clrr.crashed(last(b.states))
    requires clrr.phase1(last(b.states), step_actor)
    requires !clrr.phase2(last(b.states), step_actor)
    ensures  0 <= pos < |b.trace|
    ensures  clrr.idmap(b.trace[pos]) == step_actor
    ensures  forall i :: pos < i < |b.trace| ==> clrr.idmap(b.trace[i]) != step_actor
    ensures  clrr.phase1(b.states[pos+1], step_actor)
  {
    pos := |b.trace|;
    while pos > 0 && clrr.idmap(b.trace[pos-1]) != step_actor
      invariant 0 <= pos <= |b.trace|
      invariant clrr.phase1(b.states[pos], step_actor)
      invariant forall i :: pos <= i < |b.trace| ==> clrr.idmap(b.trace[i]) != step_actor
      invariant forall i :: pos <= i < |b.states| ==> clrr.phase1(b.states[i], step_actor)
      decreases pos
    {
      var prev := pos-1;
      assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in clrr.spec.next;
      pos := pos - 1;
    }

    assert pos != 0;
    pos := pos - 1;
  }

  lemma lemma_StateNextSeqCausesPhaseMatch<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    states:seq<State>,
    trace:seq<Step>,
    step_actor:Actor,
    other_actor:Actor
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(states, trace, clrr.spec.next)
    requires forall step :: step in trace ==> clrr.idmap(step) == step_actor
    requires step_actor != other_actor
    ensures  clrr.phase1(states[0], other_actor) <==> clrr.phase1(last(states), other_actor)
    ensures  clrr.phase2(states[0], other_actor) <==> clrr.phase2(last(states), other_actor)
  {
    if |trace| > 0 {
      var zero := 0;
      assert ActionTuple(states[zero], states[zero+1], trace[zero]) in clrr.spec.next;
      lemma_ReduceStateNextSeqLeft(states, trace, clrr.spec.next);
      lemma_StateNextSeqCausesPhaseMatch(clrr, states[1..], trace[1..], step_actor, other_actor);
    }
  }

  lemma lemma_ShowBehaviorRefinementAfterLifting<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    start_pos:int,
    nonmover_pos:int,
    end_pos:int,
    step_actor:Actor,
    hstep:Step,
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= start_pos <= nonmover_pos < end_pos < |lb.states|
    requires forall i :: start_pos <= i < end_pos ==> clrr.idmap(lb.trace[i]) == step_actor
    requires forall i :: start_pos < i <= nonmover_pos ==> clrr.phase1(lb.states[i], step_actor)
    requires forall i :: nonmover_pos < i < end_pos ==> clrr.phase2(lb.states[i], step_actor)
    requires ActionTuple(lb.states[start_pos], lb.states[end_pos], hstep) in clrr.spec.next
    requires hb.states == lb.states[..start_pos+1] + lb.states[end_pos..]
    requires hb.trace == lb.trace[..start_pos] + [hstep] + lb.trace[end_pos..]
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
  {
    var pos := start_pos;
    while pos < nonmover_pos
      invariant start_pos <= pos <= nonmover_pos
      invariant forall i :: start_pos <= i <= pos ==> RefinementPair(lb.states[i], lb.states[start_pos]) in clrr.relation
    {
      assert RefinementPair(lb.states[pos], lb.states[start_pos]) in clrr.relation;
      assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in clrr.spec.next;
      assert clrr.phase1(lb.states[pos+1], step_actor);
      var pos_plus := pos+1;
      assert ActionTuple(lb.states[pos_plus], lb.states[pos_plus+1], lb.trace[pos_plus]) in clrr.spec.next;
      assert !clrr.crashed(lb.states[pos+1]);
      assert RefinementPair(lb.states[pos+1], lb.states[pos]) in clrr.relation;
      assert RefinementPair(lb.states[pos+1], lb.states[start_pos]) in clrr.relation;
      pos := pos + 1;
    }

    pos := end_pos;
    while pos > nonmover_pos + 1
      invariant nonmover_pos < pos <= end_pos
      invariant forall i :: pos <= i <= end_pos ==> RefinementPair(lb.states[i], lb.states[end_pos]) in clrr.relation
    {
      assert RefinementPair(lb.states[pos], lb.states[end_pos]) in clrr.relation;
      var prev := pos-1;
      assert ActionTuple(lb.states[prev], lb.states[prev+1], lb.trace[prev]) in clrr.spec.next;
      assert clrr.phase2(lb.states[prev], step_actor);
      assert RefinementPair(lb.states[prev], lb.states[prev+1]) in clrr.relation;
      assert RefinementPair(lb.states[prev], lb.states[end_pos]) in clrr.relation;
      pos := prev;
    }

    var lb2 := lb.states[start_pos..end_pos+1];
    var hb2 := hb.states[start_pos..start_pos+2];
    assert hb2[0] == lb.states[start_pos];
    assert hb2[1] == lb.states[end_pos];
    var lh_map1 := RepeatingValue(RefinementRange(0, 0), nonmover_pos - start_pos + 1); 
    var lh_map2 := RepeatingValue(RefinementRange(1, 1), end_pos - nonmover_pos);
    var lh_map := lh_map1 + lh_map2;

    lemma_IndexIntoConcatenation(lh_map1, lh_map2, end_pos-start_pos);
    forall i | 0 <= i < |lh_map| - 1
      ensures lh_map[i+1].first == lh_map[i].last || lh_map[i+1].first == lh_map[i].last + 1
    {
      lemma_IndexIntoConcatenation(lh_map1, lh_map2, i);
      lemma_IndexIntoConcatenation(lh_map1, lh_map2, i+1);
    }

    assert BehaviorRefinesBehaviorUsingRefinementMap(lb2, hb2, clrr.relation, lh_map);

    lemma_ExtendBehaviorRefinesBehaviorLeft(lb2, hb2, clrr.relation, lb.states[..start_pos]);
    assert hb.states[..start_pos] == lb.states[..start_pos];
    lemma_ExtendBehaviorRefinesBehaviorRight(lb.states[..start_pos] + lb2, hb.states[..start_pos] + hb2, clrr.relation,
                                             lb.states[end_pos+1..]);
    assert hb.states[start_pos+2..] == lb.states[end_pos+1..];
    lemma_SeqEqualsThreeWayConcatentation(lb.states, start_pos, end_pos+1);
    lemma_SeqEqualsThreeWayConcatentation(hb.states, start_pos, start_pos+2);
  }

  lemma lemma_ShowBehaviorSatisfiesSpecAfterLifting<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    start_pos:int,
    nonmover_pos:int,
    end_pos:int,
    step_actor:Actor,
    hstep:Step,
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= start_pos <= nonmover_pos < end_pos < |lb.states|
    requires forall i :: start_pos <= i < end_pos ==> clrr.idmap(lb.trace[i]) == step_actor
    requires forall i :: start_pos < i <= nonmover_pos ==> clrr.phase1(lb.states[i], step_actor)
    requires forall i :: nonmover_pos < i < end_pos ==> clrr.phase2(lb.states[i], step_actor)
    requires ActionTuple(lb.states[start_pos], lb.states[end_pos], hstep) in clrr.spec.next
    requires hb.states == lb.states[..start_pos+1] + lb.states[end_pos..]
    requires hb.trace == lb.trace[..start_pos] + [hstep] + lb.trace[end_pos..]
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
  {
    assert hb.states[0] == lb.states[0];

    forall i | 0 <= i < |hb.trace|
      ensures ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in clrr.spec.next
    {
      if i < start_pos {
        assert hb.states[i] == lb.states[i];
        assert hb.states[i+1] == lb.states[i+1];
        assert hb.trace[i] == lb.trace[i];
        assert ActionTuple(lb.states[i], lb.states[i+1], lb.trace[i]) in clrr.spec.next;
      }
      else if i == start_pos {
        assert hb.states[i] == lb.states[start_pos];
        assert hb.states[i+1] == lb.states[end_pos];
        assert hb.trace[i] == hstep;
        assert ActionTuple(lb.states[start_pos], lb.states[end_pos], hstep) in clrr.spec.next;
      }
      else {
        var iadj := i + (end_pos - start_pos - 1);
        assert hb.states[i] == lb.states[iadj];
        assert hb.states[i+1] == lb.states[iadj+1];
        assert hb.trace[i] == lb.trace[iadj];
        assert ActionTuple(lb.states[iadj], lb.states[iadj+1], lb.trace[iadj]) in clrr.spec.next;
      }
    }
  }

  lemma lemma_LiftActionSequence<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    states:seq<State>,
    trace:seq<Step>,
    actor:Actor
    ) returns (
    hstep:Step
    )
    requires ActionSequencesLiftable(clrr)
    requires ActionSequencesLiftableConditions(clrr, states, trace, actor)
    ensures  ActionTuple(states[0], last(states), hstep) in clrr.spec.next
    ensures  clrr.idmap(hstep) == actor
  {
    hstep :| ActionTuple(states[0], last(states), hstep) in clrr.spec.next && clrr.idmap(hstep) == actor;
  }

  lemma lemma_RemoveNonmoverAtPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    nonmover_pos:int,
    step_actor:Actor
    ) returns (
    hb:AnnotatedBehavior<State, Step>,
    pos_past_nonmovers:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= nonmover_pos < |lb.trace|
    requires forall i :: 0 <= i < nonmover_pos ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires clrr.idmap(lb.trace[nonmover_pos]) == step_actor
    requires IsNonmoverPos(clrr, lb.states, lb.trace, nonmover_pos)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  |hb.states| - pos_past_nonmovers < |lb.states| - nonmover_pos
    ensures  0 <= pos_past_nonmovers < |hb.states|
    ensures  forall i :: 0 <= i < pos_past_nonmovers ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
  {
    var mb, start_pos, end_pos := lemma_BringMoversCloseToNonmoverAtPos(clrr, lb, nonmover_pos, step_actor);

    var states := mb.states[start_pos..end_pos+1];
    var trace := mb.trace[start_pos..end_pos];

    forall i | 0 <= i < |trace|
      ensures ActionTuple(states[i], states[i+1], trace[i]) in clrr.spec.next
      ensures !clrr.crashed(states[i])
    {
      var pos := start_pos+i;
      assert ActionTuple(mb.states[pos], mb.states[pos+1], mb.trace[pos]) in clrr.spec.next;
    }
    
    assert ActionSequencesLiftableConditions(clrr, states, trace, step_actor);
    var hstep := lemma_LiftActionSequence(clrr, states, trace, step_actor);

    var hstates := mb.states[..start_pos+1] + mb.states[end_pos..];
    var htrace := mb.trace[..start_pos] + [hstep] + mb.trace[end_pos..];
    hb := AnnotatedBehavior(hstates, htrace);
    pos_past_nonmovers := start_pos + 1;

    lemma_ShowBehaviorRefinementAfterLifting(clrr, mb, start_pos, nonmover_pos, end_pos, step_actor, hstep, hb);
    lemma_ShowBehaviorSatisfiesSpecAfterLifting(clrr, mb, start_pos, nonmover_pos, end_pos, step_actor, hstep, hb);
    lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);

    forall i | 0 <= i < pos_past_nonmovers
      ensures !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    {
      if i < start_pos {
        assert hb.states[i] == mb.states[i];
        assert hb.states[i+1] == mb.states[i+1];
        assert !IsNonmoverPos(clrr, mb.states, mb.trace, i);
      }
      else {
        assert hb.states[i] == mb.states[start_pos] == states[0];
        assert hb.states[i+1] == mb.states[end_pos] == last(states);
        assert ActionTuple(states[0], last(states), hstep) in clrr.spec.next;
        assert !IsNonmoverStep(clrr, states[0], last(states), step_actor);
      }
    }
  }

  lemma lemma_BringMoversCloseToNonmoverAtPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    nonmover_pos:int,
    step_actor:Actor
    ) returns (
    hb:AnnotatedBehavior<State, Step>,
    start_pos:int,
    end_pos:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= nonmover_pos < |lb.trace|
    requires forall i :: 0 <= i < nonmover_pos ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires clrr.idmap(lb.trace[nonmover_pos]) == step_actor
    requires IsNonmoverPos(clrr, lb.states, lb.trace, nonmover_pos)

    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  |hb.states| < |lb.states| + (end_pos - nonmover_pos)
    ensures  0 <= start_pos <= nonmover_pos < end_pos < |hb.states|
    ensures  forall i :: 0 <= i < nonmover_pos ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    ensures  !clrr.crashed(hb.states[start_pos])
    ensures  !clrr.phase1(hb.states[start_pos], step_actor)
    ensures  !clrr.phase2(hb.states[start_pos], step_actor)
    ensures  hb.states[nonmover_pos] == lb.states[nonmover_pos]
    ensures  hb.states[nonmover_pos+1] == lb.states[nonmover_pos+1]
    ensures  var s := hb.states[end_pos]; !clrr.crashed(s) ==> !clrr.phase1(s, step_actor) && !clrr.phase2(s, step_actor)
    ensures  forall i :: start_pos <= i < end_pos ==> clrr.idmap(hb.trace[i]) == step_actor
    ensures  forall i :: start_pos < i <= nonmover_pos ==> clrr.phase1(hb.states[i], step_actor)
    ensures  forall i :: nonmover_pos < i < end_pos ==> clrr.phase2(hb.states[i], step_actor)
  {
    lemma_TakeStateNextSeq(lb.states, lb.trace, clrr.spec.next, nonmover_pos);
    var pre_nonmover_behavior := AnnotatedBehavior(lb.states[..nonmover_pos+1], lb.trace[..nonmover_pos]);

    forall i | 0 <= i < |pre_nonmover_behavior.states|-1
      ensures !IsNonmoverPos(clrr, pre_nonmover_behavior.states, pre_nonmover_behavior.trace, i)
    {
      assert pre_nonmover_behavior.states[i] == lb.states[i];
      assert pre_nonmover_behavior.states[i+1] == lb.states[i+1];
      assert pre_nonmover_behavior.trace[i] == lb.trace[i];
      assert !IsNonmoverPos(clrr, lb.states, lb.trace, i);
    }
    assert ActionTuple(lb.states[nonmover_pos], lb.states[nonmover_pos+1], lb.trace[nonmover_pos]) in clrr.spec.next;

    var pre_nonmover_behavior';
    pre_nonmover_behavior', start_pos := lemma_BringRightMoversToEnd(clrr, pre_nonmover_behavior, step_actor);

    lemma_DropStateNextSeq(lb.states, lb.trace, clrr.spec.next, nonmover_pos+1);
    lemma_StateInAnnotatedBehaviorInAnnotatedReachables(clrr.spec, lb, nonmover_pos+1);
    var post_nonmover_states', post_nonmover_trace', end_pos_relative :=
      lemma_BringLeftMoversToStart(clrr, lb.states[nonmover_pos+1..], lb.trace[nonmover_pos+1..], step_actor);

    var hstates' := pre_nonmover_behavior'.states + post_nonmover_states';
    var htrace' := pre_nonmover_behavior'.trace + [lb.trace[nonmover_pos]] + post_nonmover_trace';
    end_pos := nonmover_pos + 1 + end_pos_relative;
    hb := AnnotatedBehavior(hstates', htrace');

    lemma_ConcatenatingBehaviorsPreservesRefinement(lb.states[..nonmover_pos+1], lb.states[nonmover_pos+1..],
                                                    pre_nonmover_behavior'.states, post_nonmover_states', clrr.relation);
    lemma_TakePlusDropIsSeq(lb.states, nonmover_pos+1);

    forall i | 0 <= i < |htrace'|
      ensures ActionTuple(hstates'[i], hstates'[i+1], htrace'[i]) in clrr.spec.next
    {
      if i < |pre_nonmover_behavior'.trace| {
        assert hstates'[i] == pre_nonmover_behavior'.states[i];
        assert hstates'[i+1] == pre_nonmover_behavior'.states[i+1];
        assert htrace'[i] == pre_nonmover_behavior'.trace[i];
        assert ActionTuple(pre_nonmover_behavior'.states[i], pre_nonmover_behavior'.states[i+1], pre_nonmover_behavior'.trace[i])
               in clrr.spec.next;
      }
      else if i == |pre_nonmover_behavior'.trace| {
        assert hstates'[i] == last(pre_nonmover_behavior'.states) == lb.states[nonmover_pos];
        assert hstates'[i+1] == post_nonmover_states'[0] == lb.states[nonmover_pos+1];
        assert htrace'[i] == lb.trace[nonmover_pos];
        assert ActionTuple(lb.states[nonmover_pos], lb.states[nonmover_pos+1], lb.trace[nonmover_pos]) in clrr.spec.next;
      }
      else {
        var j := i - |pre_nonmover_behavior'.states|;
        assert hstates'[i] == post_nonmover_states'[j];
        assert hstates'[i+1] == post_nonmover_states'[j+1];
        assert htrace'[i] == post_nonmover_trace'[j];
        assert ActionTuple(post_nonmover_states'[j], post_nonmover_states'[j+1], post_nonmover_trace'[j]) in clrr.spec.next;
      }
    }

    forall i | 0 <= i < nonmover_pos
      ensures !IsNonmoverPos(clrr, hb.states, hb.trace, i);
    {
      assert hb.states[i] == pre_nonmover_behavior'.states[i];
      assert hb.states[i+1] == pre_nonmover_behavior'.states[i+1];
      assert hb.trace[i] == pre_nonmover_behavior'.trace[i];
      assert !IsNonmoverPos(clrr, pre_nonmover_behavior'.states, pre_nonmover_behavior'.trace, i);
    }
  }

  lemma lemma_RemoveAnyNonmoverAtPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    nonmover_pos:int
    ) returns (
    hb:AnnotatedBehavior<State, Step>,
    pos_past_nonmovers:int
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= nonmover_pos < |lb.trace|
    requires forall i :: 0 <= i < nonmover_pos ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  |hb.states| - pos_past_nonmovers < |lb.states| - nonmover_pos
    ensures  0 <= pos_past_nonmovers < |hb.states|
    ensures  forall i :: 0 <= i < pos_past_nonmovers ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
  {
    assert ActionTuple(lb.states[nonmover_pos], lb.states[nonmover_pos+1], lb.trace[nonmover_pos]) in clrr.spec.next;
    var step_actor := clrr.idmap(lb.trace[nonmover_pos]);

    if !IsNonmoverPos(clrr, lb.states, lb.trace, nonmover_pos) {
      hb := lb;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
      pos_past_nonmovers := nonmover_pos + 1;
      return;
    }

    hb, pos_past_nonmovers := lemma_RemoveNonmoverAtPos(clrr, lb, nonmover_pos, step_actor);
  }

  lemma lemma_RemoveAllNonmoversFromPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    nonmover_pos:int
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires 0 <= nonmover_pos < |lb.states|
    requires forall i :: 0 <= i < nonmover_pos ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    decreases |lb.states| - nonmover_pos
  {
    if nonmover_pos == |lb.trace| {
      hb := lb;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
    }
    else {
      var mb, pos_past_nonmovers := lemma_RemoveAnyNonmoverAtPos(clrr, lb, nonmover_pos);
      hb := lemma_RemoveAllNonmoversFromPos(clrr, mb, pos_past_nonmovers);
      lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);
    }
  }

  predicate IsNonmoverStep<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    s:State,
    s':State,
    actor:Actor
    )
  {
    || (!clrr.phase1(s, actor) && !clrr.phase2(s, actor) && clrr.phase2(s', actor) && !clrr.crashed(s'))
    || (clrr.phase1(s, actor) && !clrr.phase1(s', actor))
    || (clrr.phase1(s, actor) && clrr.crashed(s'))
  }

  predicate IsNonmoverPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    states:seq<State>,
    trace:seq<Step>,
    pos:int
    )
    requires 0 <= pos < |trace| < |states|
  {
    IsNonmoverStep(clrr, states[pos], states[pos+1], clrr.idmap(trace[pos]))
  }

  lemma lemma_RemoveAllNonmovers<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
  {
    hb := lemma_RemoveAllNonmoversFromPos(clrr, lb, 0);
  }

  lemma lemma_RemoveRightMoverFromPosCaseBeforeCrash<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|-1
    requires !clrr.crashed(lstates[right_mover_pos+1])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires clrr.crashed(lstates[right_mover_pos+2])
    requires forall i :: 0 <= i < |ltrace| ==> !IsNonmoverPos(clrr, lstates, ltrace, i)
    requires forall i :: 0 <= i < right_mover_pos ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: right_mover_pos < i < |ltrace| ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |htrace| <= |ltrace|
    ensures  forall i :: 0 <= i < |htrace| ==> !IsNonmoverPos(clrr, hstates, htrace, i)
    ensures  forall i :: 0 <= i < |htrace| ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
  {
    assert ActionTuple(lstates[right_mover_pos], lstates[right_mover_pos+1], ltrace[right_mover_pos]) in clrr.spec.next;
    var pos_plus := right_mover_pos + 1;
    assert ActionTuple(lstates[pos_plus], lstates[pos_plus+1], ltrace[pos_plus]) in clrr.spec.next;
    if |ltrace| != right_mover_pos + 2 {
      var pos_plus_2 := right_mover_pos + 2;
      assert ActionTuple(lstates[pos_plus_2], lstates[pos_plus_2+1], ltrace[pos_plus_2]) in clrr.spec.next;
      assert false;
    }
    lemma_StateNextSeqMaintainsAnnotatedReachables(lstates, ltrace, clrr.spec);
    assert lstates[right_mover_pos] in lstates;
    assert !IsNonmoverPos(clrr, lstates, ltrace, right_mover_pos+1);
    assert RightMoverCrashPreservationConditions(clrr, lstates[right_mover_pos], lstates[right_mover_pos+1], lstates[right_mover_pos+2],
                                                 ltrace[right_mover_pos], ltrace[right_mover_pos+1]);
    var other_step', state_after_other_step' :|
          && clrr.idmap(other_step') == clrr.idmap(ltrace[right_mover_pos+1])
          && ActionTuple(lstates[right_mover_pos], state_after_other_step', other_step') in clrr.spec.next
          && clrr.crashed(state_after_other_step')
          && RefinementPair(lstates[right_mover_pos+2], state_after_other_step') in clrr.relation;

    hstates := lstates[..right_mover_pos+1] + [state_after_other_step'];
    htrace := ltrace[..right_mover_pos] + [other_step'];
    assert StateNextSeq(hstates, htrace, clrr.spec.next);

    var lh_map := ConvertMapToSeq(
                    |lstates|,
                    map i | 0 <= i < |lstates| ::
                      if i <= right_mover_pos then RefinementRange(i, i)
                      else if i == right_mover_pos+1 then RefinementRange(right_mover_pos, right_mover_pos)
                      else RefinementRange(right_mover_pos+1, right_mover_pos+1));

    forall i, j {:trigger RefinementPair(lstates[i], hstates[j]) in clrr.relation}
      | 0 <= i < |lstates| && lh_map[i].first <= j <= lh_map[i].last
      ensures RefinementPair(lstates[i], hstates[j]) in clrr.relation
    {
      if i <= right_mover_pos {
        assert j == i;
        assert hstates[j] == lstates[i];
        assert RefinementPair(lstates[i], lstates[i]) in clrr.relation;
      }
      else if i == right_mover_pos+1 {
        assert j == right_mover_pos;
        assert hstates[j] == lstates[right_mover_pos];
        assert ActionTuple(lstates[right_mover_pos], lstates[right_mover_pos+1], ltrace[right_mover_pos]) in clrr.spec.next;
        assert !clrr.crashed(lstates[right_mover_pos+1]);
        assert clrr.idmap(ltrace[right_mover_pos]) == step_actor;
        assert clrr.phase1(lstates[right_mover_pos+1], step_actor);
        assert RefinementPair(lstates[right_mover_pos+1], lstates[right_mover_pos]) in clrr.relation;
      }
      else {
        assert i == right_mover_pos+2;
        assert j == right_mover_pos+1;
        assert hstates[j] == state_after_other_step';
        assert RefinementPair(lstates[right_mover_pos+2], state_after_other_step') in clrr.relation;
      }
    }
    assert BehaviorRefinesBehaviorUsingRefinementMap(lstates, hstates, clrr.relation, lh_map);

    forall i | 0 <= i < |htrace|
      ensures !IsNonmoverPos(clrr, hstates, htrace, i)
    {
      if i < right_mover_pos {
        assert !IsNonmoverPos(clrr, lstates, ltrace, i);
      }
      else {
        assert hstates[i] == lstates[right_mover_pos];
        assert hstates[i+1] == state_after_other_step';
        assert htrace[i] == other_step';
      }
    }
  }

  lemma lemma_RemoveRightMoverFromPosCaseAtEnd<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires |ltrace| > 0
    requires right_mover_pos == |ltrace|-1;
    requires !clrr.crashed(lstates[right_mover_pos+1])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires forall i :: 0 <= i < |ltrace| ==> !IsNonmoverPos(clrr, lstates, ltrace, i)
    requires forall i :: 0 <= i < right_mover_pos ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: right_mover_pos < i < |ltrace| ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |htrace| <= |ltrace|
    ensures  forall i :: 0 <= i < |htrace| ==> !IsNonmoverPos(clrr, hstates, htrace, i)
    ensures  forall i :: 0 <= i < |htrace| ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
  {
    hstates := all_but_last(lstates);
    htrace := all_but_last(ltrace);
    lemma_ReduceStateNextSeqRight(lstates, ltrace, clrr.spec.next);

    var lh_map := ConvertMapToSeq(|lstates|, map i | 0 <= i < |lstates| :: if i < |ltrace| then RefinementRange(i, i)
                                                                                         else RefinementRange(|hstates|-1, |hstates|-1));
    forall i, j {:trigger RefinementPair(lstates[i], hstates[j]) in clrr.relation}
      | 0 <= i < |lstates| && lh_map[i].first <= j <= lh_map[i].last
      ensures RefinementPair(lstates[i], hstates[j]) in clrr.relation
    {
      if i < |ltrace| {
        assert j == i;
        assert hstates[j] == lstates[i];
        assert RefinementPair(lstates[i], lstates[i]) in clrr.relation;
      }
      else {
        var ult := |ltrace|-1;
        assert lstates[i] == lstates[ult+1];
        assert j == |hstates|-1 == |ltrace|-1 == ult;
        assert hstates[j] == lstates[ult];
        assert ActionTuple(lstates[ult], lstates[ult+1], ltrace[ult]) in clrr.spec.next;
        assert clrr.idmap(ltrace[ult]) == step_actor;
        assert clrr.phase1(lstates[ult+1], step_actor);
        assert RefinementPair(lstates[ult+1], lstates[ult]) in clrr.relation;
      }
    }

    assert BehaviorRefinesBehaviorUsingRefinementMap(lstates, hstates, clrr.relation, lh_map);

    forall i | 0 <= i < |htrace|
      ensures !IsNonmoverPos(clrr, hstates, htrace, i)
    {
      assert !IsNonmoverPos(clrr, lstates, ltrace, i);
    }
  }

  lemma lemma_EstablishBehaviorRefinesBehaviorAfterMovingRightMoverForRemoval<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|-1
    requires !clrr.crashed(lstates[right_mover_pos+2])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires clrr.idmap(ltrace[right_mover_pos+1]) != step_actor
    requires ActionTuple(lstates[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(ltrace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(ltrace[right_mover_pos])
    requires hstates == lstates[..right_mover_pos+1] + [new_middle_state] + lstates[right_mover_pos+2..]
    requires htrace == ltrace[..right_mover_pos] + [other_step', right_mover'] + ltrace[right_mover_pos+2..]
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  last(hstates) == last(lstates)
    ensures  |hstates| == |lstates|
    ensures  |htrace| == |ltrace|
    ensures  clrr.idmap(htrace[right_mover_pos+1]) == step_actor
  {
    var lb2 := lstates[right_mover_pos..right_mover_pos+3];
    var hb2 := [lstates[right_mover_pos], new_middle_state, lstates[right_mover_pos+2]];

    var right_mover_pos_plus := right_mover_pos+1;
    assert ActionTuple(lstates[right_mover_pos_plus], lstates[right_mover_pos_plus+1], ltrace[right_mover_pos_plus]) in clrr.spec.next;
    assert !clrr.crashed(lstates[right_mover_pos_plus]);

    forall ensures RefinementPair(lb2[2], hb2[1]) in clrr.relation
    {
      assert ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next;
      assert clrr.idmap(right_mover') == step_actor;
      assert ActionTuple(lstates[right_mover_pos_plus], lstates[right_mover_pos_plus+1], ltrace[right_mover_pos_plus])
               in clrr.spec.next;
      assert clrr.idmap(ltrace[right_mover_pos_plus]) != step_actor;
      assert clrr.phase1(lstates[right_mover_pos_plus+1], step_actor);
      assert !clrr.crashed(lstates[right_mover_pos+2]);
      assert RefinementPair(lstates[right_mover_pos+2], new_middle_state) in clrr.relation;
    }

    forall ensures RefinementPair(lb2[1], hb2[0]) in clrr.relation
    {
      assert ActionTuple(lstates[right_mover_pos], lstates[right_mover_pos+1], ltrace[right_mover_pos]) in clrr.spec.next;
      assert clrr.idmap(ltrace[right_mover_pos]) == step_actor;
      assert !clrr.crashed(lstates[right_mover_pos+1]);
      assert RefinementPair(lstates[right_mover_pos+1], lstates[right_mover_pos]) in clrr.relation;
    }

    forall ensures RefinementPair(lb2[0], hb2[0]) in clrr.relation
    {
      assert hb2[0] == lb2[0];
    }

    forall ensures RefinementPair(lb2[2], hb2[2]) in clrr.relation
    {
      assert hb2[2] == lb2[2];
    }

    var lh_map := [RefinementRange(0, 0), RefinementRange(0, 0), RefinementRange(1, 2)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb2, hb2, clrr.relation, lh_map);

    lemma_ExtendBehaviorRefinesBehaviorLeft(lb2, hb2, clrr.relation, lstates[..right_mover_pos]);
    lemma_ExtendBehaviorRefinesBehaviorRight(lstates[..right_mover_pos] + lb2, lstates[..right_mover_pos] + hb2, clrr.relation,
                                             lstates[right_mover_pos+3..]);
    assert BehaviorRefinesBehavior(lstates[..right_mover_pos] + lb2 + lstates[right_mover_pos+3..],
                                   lstates[..right_mover_pos] + hb2 + lstates[right_mover_pos+3..], clrr.relation);
    lemma_SeqEqualsThreeWayConcatentation(lstates, right_mover_pos, right_mover_pos+3);

    assert hstates == lstates[..right_mover_pos] + hb2 + lstates[right_mover_pos+3..];
  }

  lemma lemma_EstablishBehaviorSatisfiesSpecAfterMovingRightMoverForRemoval<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|-1
    requires !clrr.crashed(lstates[right_mover_pos+2])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires ActionTuple(lstates[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(ltrace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(ltrace[right_mover_pos])
    requires hstates == lstates[..right_mover_pos+1] + [new_middle_state] + lstates[right_mover_pos+2..]
    requires htrace == ltrace[..right_mover_pos] + [other_step', right_mover'] + ltrace[right_mover_pos+2..]
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
  {
    forall i {:trigger ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next}
      | 0 <= i < |htrace|
      ensures ActionTuple(hstates[i], hstates[i+1], htrace[i]) in clrr.spec.next
    {
      if i == right_mover_pos {
        assert hstates[i] == lstates[right_mover_pos];
        assert hstates[i+1] == new_middle_state;
        assert htrace[i] == other_step';
        assert ActionTuple(lstates[right_mover_pos], new_middle_state, other_step') in clrr.spec.next;
      }
      else if i == right_mover_pos + 1 {
        assert hstates[i] == new_middle_state;
        assert hstates[i+1] == lstates[right_mover_pos+2];
        assert htrace[i] == right_mover';
        assert ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next;
      }
      else {
        assert hstates[i] == lstates[i];
        assert hstates[i+1] == lstates[i+1];
        assert htrace[i] == ltrace[i];
        assert ActionTuple(lstates[i], lstates[i+1], ltrace[i]) in clrr.spec.next;
      }
    }
  }

  lemma lemma_EstablishStillNoNonmoversAfterMovingRightMoverForRemoval<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int,
    new_middle_state:State,
    other_step':Step,
    right_mover':Step,
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|-1
    requires !clrr.crashed(lstates[right_mover_pos+2])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires clrr.idmap(ltrace[right_mover_pos+1]) != step_actor
    requires forall i :: 0 <= i < |ltrace| ==> !IsNonmoverPos(clrr, lstates, ltrace, i)
    requires forall i :: 0 <= i < right_mover_pos ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: right_mover_pos < i < |ltrace| ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires ActionTuple(lstates[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
    requires ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next
    requires clrr.idmap(other_step') == clrr.idmap(ltrace[right_mover_pos+1])
    requires clrr.idmap(right_mover') == clrr.idmap(ltrace[right_mover_pos])
    requires hstates == lstates[..right_mover_pos+1] + [new_middle_state] + lstates[right_mover_pos+2..]
    requires htrace == ltrace[..right_mover_pos] + [other_step', right_mover'] + ltrace[right_mover_pos+2..]
    ensures  forall i :: 0 <= i < |htrace| ==> !IsNonmoverPos(clrr, hstates, htrace, i)
    ensures  forall i :: 0 <= i <= right_mover_pos ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  forall i :: right_mover_pos+1 < i < |htrace| ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
  {
    var right_mover_pos_plus := right_mover_pos + 1;

    forall i | 0 <= i < |htrace|
      ensures !IsNonmoverPos(clrr, hstates, htrace, i)
    {
      if i == right_mover_pos {
        assert hstates[i] == lstates[right_mover_pos];
        assert hstates[i+1] == new_middle_state;
        assert !IsNonmoverPos(clrr, lstates, ltrace, right_mover_pos_plus);
        assert ActionTuple(lstates[right_mover_pos], lstates[right_mover_pos+1], ltrace[right_mover_pos]) in clrr.spec.next;
        assert ActionTuple(new_middle_state, lstates[right_mover_pos_plus+1], right_mover') in clrr.spec.next;
        assert !IsNonmoverStep(clrr, lstates[right_mover_pos], new_middle_state, clrr.idmap(htrace[i]));
      }
      else if i == right_mover_pos + 1 {
        assert hstates[i] == new_middle_state;
        assert hstates[i+1] == lstates[right_mover_pos+2];
      }
      else {
        assert !IsNonmoverPos(clrr, lstates, ltrace, i);
      }
    }

    forall i | 0 <= i <= right_mover_pos
      ensures var actor := clrr.idmap(htrace[i]);
              var s := hstates[i+1];
              !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    {
      if i < right_mover_pos {
        assert htrace[i] == ltrace[i];
        assert hstates[i+1] == lstates[i+1];
        assert var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor);
      }
      else {
        assert i == right_mover_pos;
        assert htrace[i] == other_step';
        var other_actor := clrr.idmap(other_step');
        assert other_actor == clrr.idmap(ltrace[right_mover_pos+1]);
        assert hstates[i+1] == new_middle_state;
        assert ActionTuple(new_middle_state, lstates[right_mover_pos+2], right_mover') in clrr.spec.next;
        assert clrr.idmap(right_mover') != other_actor;
        assert clrr.phase1(new_middle_state, other_actor) <==> clrr.phase1(lstates[right_mover_pos+2], other_actor);
        assert clrr.phase2(new_middle_state, other_actor) <==> clrr.phase2(lstates[right_mover_pos+2], other_actor);
        assert var actor := clrr.idmap(ltrace[right_mover_pos_plus]);
               var s := lstates[right_mover_pos_plus+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor);
      }
    }
  }

  lemma lemma_MoveRightMoverRightForRemoval<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|-1
    requires !clrr.crashed(lstates[right_mover_pos+2])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires forall i :: 0 <= i < |ltrace| ==> !IsNonmoverPos(clrr, lstates, ltrace, i)
    requires forall i :: 0 <= i < right_mover_pos ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: right_mover_pos < i < |ltrace| ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |htrace| == |ltrace|
    ensures  forall i :: 0 <= i < |htrace| ==> !IsNonmoverPos(clrr, hstates, htrace, i)
    ensures  forall i :: 0 <= i <= right_mover_pos ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  forall i :: right_mover_pos+1 < i < |htrace| ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  clrr.idmap(htrace[right_mover_pos+1]) == step_actor
    ensures  clrr.phase1(hstates[right_mover_pos+2], step_actor)
    ensures  !clrr.crashed(hstates[right_mover_pos+2])
  {
    assert ActionTuple(lstates[right_mover_pos], lstates[right_mover_pos+1], ltrace[right_mover_pos]) in clrr.spec.next;
    var right_mover_pos_plus := right_mover_pos + 1;
    assert ActionTuple(lstates[right_mover_pos_plus], lstates[right_mover_pos_plus+1], ltrace[right_mover_pos_plus]) in clrr.spec.next;
    lemma_StateNextSeqMaintainsAnnotatedReachables(lstates, ltrace, clrr.spec);
    assert !IsNonmoverPos(clrr, lstates, ltrace, right_mover_pos+1);
    assert RightMoversCommuteConditions(clrr, lstates[right_mover_pos], lstates[right_mover_pos+1],
                                        lstates[right_mover_pos_plus+1], ltrace[right_mover_pos],
                                        ltrace[right_mover_pos+1]);
    var new_middle_state, other_step', right_mover' :|
      && ActionTuple(lstates[right_mover_pos], new_middle_state, other_step') in clrr.spec.next
      && ActionTuple(new_middle_state, lstates[right_mover_pos_plus+1], right_mover') in clrr.spec.next
      && clrr.idmap(other_step') == clrr.idmap(ltrace[right_mover_pos+1])
      && clrr.idmap(right_mover') == clrr.idmap(ltrace[right_mover_pos]);

    hstates := lstates[..right_mover_pos+1] + [new_middle_state] + lstates[right_mover_pos+2..];
    htrace := ltrace[..right_mover_pos] + [other_step', right_mover'] + ltrace[right_mover_pos+2..];
    lemma_EstablishBehaviorRefinesBehaviorAfterMovingRightMoverForRemoval(
      clrr, lstates, ltrace, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hstates, htrace);
    lemma_EstablishBehaviorSatisfiesSpecAfterMovingRightMoverForRemoval(
      clrr, lstates, ltrace, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hstates, htrace);
    lemma_EstablishStillNoNonmoversAfterMovingRightMoverForRemoval(
      clrr, lstates, ltrace, step_actor, right_mover_pos, new_middle_state, other_step', right_mover', hstates, htrace);
  }

  lemma lemma_RemoveRightMoverFromPos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lstates:seq<State>,
    ltrace:seq<Step>,
    step_actor:Actor,
    right_mover_pos:int
    ) returns (
    hstates:seq<State>,
    htrace:seq<Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires StateNextSeq(lstates, ltrace, clrr.spec.next)
    requires lstates[0] in AnnotatedReachables(clrr.spec)
    requires 0 <= right_mover_pos < |ltrace|
    requires !clrr.crashed(lstates[right_mover_pos+1])
    requires clrr.phase1(lstates[right_mover_pos+1], step_actor)
    requires clrr.idmap(ltrace[right_mover_pos]) == step_actor
    requires forall i :: 0 <= i < |ltrace| ==> !IsNonmoverPos(clrr, lstates, ltrace, i)
    requires forall i :: 0 <= i < right_mover_pos ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    requires forall i :: right_mover_pos < i < |ltrace| ==>
               var actor := clrr.idmap(ltrace[i]);
               var s := lstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  BehaviorRefinesBehavior(lstates, hstates, clrr.relation)
    ensures  StateNextSeq(hstates, htrace, clrr.spec.next)
    ensures  hstates[0] == lstates[0]
    ensures  |htrace| <= |ltrace|
    ensures  forall i :: 0 <= i < |htrace| ==> !IsNonmoverPos(clrr, hstates, htrace, i)
    ensures  forall i :: 0 <= i < |htrace| ==>
               var actor := clrr.idmap(htrace[i]);
               var s := hstates[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    decreases |lstates| - right_mover_pos
  {
    if right_mover_pos == |ltrace|-1 {
      hstates, htrace := lemma_RemoveRightMoverFromPosCaseAtEnd(clrr, lstates, ltrace, step_actor, right_mover_pos);
      return;
    }

    if clrr.crashed(lstates[right_mover_pos+2]) {
      hstates, htrace := lemma_RemoveRightMoverFromPosCaseBeforeCrash(clrr, lstates, ltrace, step_actor, right_mover_pos);
      return;
    }

    var mstates, mtrace := lemma_MoveRightMoverRightForRemoval(clrr, lstates, ltrace, step_actor, right_mover_pos);
    hstates, htrace := lemma_RemoveRightMoverFromPos(clrr, mstates, mtrace, step_actor, right_mover_pos+1);
    lemma_RefinementConvolutionTransitive(lstates, mstates, hstates, clrr.relation);
  }

  lemma lemma_NoNonmoversMeansNoPhase2<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    b:AnnotatedBehavior<State, Step>,
    pos:int,
    step_actor:Actor
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(b, clrr.spec)
    requires forall i :: 0 <= i < |b.trace| ==> !IsNonmoverPos(clrr, b.states, b.trace, i)
    requires 0 <= pos < |b.states|
    ensures  !clrr.crashed(b.states[pos]) ==> !clrr.phase2(b.states[pos], step_actor)
    decreases pos
  {
    if pos > 0 {
      var prev := pos - 1;
      assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in clrr.spec.next;
      lemma_NoNonmoversMeansNoPhase2(clrr, b, prev, step_actor);
      assert !IsNonmoverPos(clrr, b.states, b.trace, prev);
    }
  }

  lemma lemma_RemoveAllRightMoversAtOrBeforePos<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>,
    right_mover_pos:int
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    requires 0 <= right_mover_pos < |lb.trace|
    requires forall i :: right_mover_pos < i < |lb.trace| ==>
               var actor := clrr.idmap(lb.trace[i]);
               var s := lb.states[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  forall i :: 0 <= i < |hb.trace| ==> !IsNonmoverPos(clrr, hb.states, hb.trace, i)
    ensures  forall i :: 0 <= i < |hb.trace| ==>
               var actor := clrr.idmap(hb.trace[i]);
               var s := hb.states[i+1];
               !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    decreases right_mover_pos;
  {
    var step_actor := clrr.idmap(lb.trace[right_mover_pos]);
    var s := lb.states[right_mover_pos];
    var s' := lb.states[right_mover_pos+1];

    lemma_NoNonmoversMeansNoPhase2(clrr, lb, right_mover_pos+1, step_actor);

    if clrr.crashed(s') || !clrr.phase1(s', step_actor) {
      if right_mover_pos == 0 {
        hb := lb;
        lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
      }
      else {
        hb := lemma_RemoveAllRightMoversAtOrBeforePos(clrr, lb, right_mover_pos-1);
      }
      return;
    }

    var lstates_trunc := lb.states[right_mover_pos..];
    var ltrace_trunc := lb.trace[right_mover_pos..];
    forall i | 0 <= i < |ltrace_trunc|
      ensures !IsNonmoverPos(clrr, lstates_trunc, ltrace_trunc, i)
    {
      lemma_IndexIntoDrop(lb.states, right_mover_pos, i);
      lemma_IndexIntoDrop(lb.states, right_mover_pos, i+1);
      assert lstates_trunc[i] == lb.states[right_mover_pos+i];
      assert lstates_trunc[i+1] == lb.states[right_mover_pos+i+1];
      assert !IsNonmoverPos(clrr, lb.states, lb.trace, right_mover_pos+i);
    }

    lemma_StateInAnnotatedBehaviorInAnnotatedReachables(clrr.spec, lb, right_mover_pos);
    var mstates_trunc, mtrace_trunc := lemma_RemoveRightMoverFromPos(clrr, lstates_trunc, ltrace_trunc, step_actor, 0);

    lemma_ExtendBehaviorRefinesBehaviorLeft(lb.states[right_mover_pos..], mstates_trunc, clrr.relation, lb.states[..right_mover_pos]);
    lemma_TakePlusDropIsSeq(lb.states, right_mover_pos);

    var mb := AnnotatedBehavior(lb.states[..right_mover_pos] + mstates_trunc, lb.trace[..right_mover_pos] + mtrace_trunc);
    assert BehaviorRefinesBehavior(lb.states, mb.states, clrr.relation);
    assert StateNextSeq(mb.states, mb.trace, clrr.spec.next);

    forall i | 0 <= i < |mb.trace|
      ensures !IsNonmoverPos(clrr, mb.states, mb.trace, i)
    {
      if i < right_mover_pos-1 {
        assert mb.states[i] == lb.states[i];
        assert mb.states[i+1] == lb.states[i+1];
        assert mb.trace[i] == lb.trace[i];
        assert !IsNonmoverPos(clrr, lb.states, lb.trace, i);
      }
      else if i == right_mover_pos-1 {
        assert mb.states[i] == lb.states[i];
        assert mb.states[i+1] == mstates_trunc[0] == lstates_trunc[0] == lb.states[right_mover_pos] == lb.states[i+1];
        assert mb.trace[i] == lb.trace[i];
        assert !IsNonmoverPos(clrr, lb.states, lb.trace, i);
      }
      else {
        var iadj := i - right_mover_pos;
        assert mb.states[i] == mstates_trunc[iadj];
        assert mb.states[i+1] == mstates_trunc[iadj+1];
        assert mb.trace[i] == mtrace_trunc[iadj];
        assert !IsNonmoverPos(clrr, mstates_trunc, mtrace_trunc, iadj);
      }
    }

    if right_mover_pos == 0 {
      hb := mb;
    }
    else {
      hb := lemma_RemoveAllRightMoversAtOrBeforePos(clrr, mb, right_mover_pos-1);
      lemma_RefinementConvolutionTransitive(lb.states, mb.states, hb.states, clrr.relation);
    }
  }

  lemma lemma_RemoveAllRightMovers<State, Actor, Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    lb:AnnotatedBehavior<State, Step>
    ) returns (
    hb:AnnotatedBehavior<State, Step>
    )
    requires ValidCohenLamportReductionRequest(clrr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, clrr.spec)
    requires forall i :: 0 <= i < |lb.trace| ==> !IsNonmoverPos(clrr, lb.states, lb.trace, i)
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, clrr.relation)
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, clrr.spec)
    ensures  forall i, actor :: 0 <= i < |hb.states| ==> var s := hb.states[i]; !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
  {
    if |lb.trace| == 0 {
      hb := lb;
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb.states, clrr.relation);
    }
    else {
      hb := lemma_RemoveAllRightMoversAtOrBeforePos(clrr, lb, |lb.trace|-1);
    }

    forall j, actor | 0 <= j < |hb.states|
      ensures var s := hb.states[j]; !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
    {
      var pos := 0;
      while pos < |hb.trace|
        invariant 0 <= pos <= |hb.trace|
        invariant forall i :: 0 <= i <= pos ==> var s := hb.states[i]; !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor)
      {
        var s := hb.states[pos];
        var s' := hb.states[pos+1];
        if clrr.idmap(hb.trace[pos]) == actor {
          assert !clrr.crashed(s') ==> !clrr.phase1(s', actor) && !clrr.phase2(s', actor);
        }
        else {
          assert ActionTuple(hb.states[pos], hb.states[pos+1], hb.trace[pos]) in clrr.spec.next;
          assert !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor);
          assert clrr.phase1(s, actor) <==> clrr.phase1(s', actor);
          assert clrr.phase2(s, actor) <==> clrr.phase2(s', actor);
        }
        pos := pos + 1;
      }
    }
  }

}
