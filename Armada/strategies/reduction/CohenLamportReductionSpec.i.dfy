/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file is the specification for a request to perform a Cohen-Lamport reduction on a behavior.
// Such a reduction takes a behavior where some states are in phase 1 or 2, and returns a behavior
// in which no state (except possibly the last, crashing state) is in phase 1 or 2.  That resulting
// behavior satisfies the same specification, but is a refinement of the original behavior.
//
// To use this specification, first create a request r of type CohenLamportReductionRequest.  Then,
// prove that it's a valid request, i.e., that ValidCohenLamportReductionRequest(r).  Finally, call
// lemma_PerformCohenLamportReduction (in CohenLamportReduction.i.dfy).
//
// The request specification allows behaviors that crash as their final step.  But, the request
// specification also demands that action sequences be reducible if they crash in the middle, i.e.,
// even if the actor performing those action sequences executes a step that crashes while in phase 1
// or 2.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "../../util/collections/seqs.s.dfy"
include "../../spec/refinement.s.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"

module CohenLamportReductionSpecModule {

  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule

  datatype CohenLamportReductionRequest<!State(==), !Actor(==), !Step> = CohenLamportReductionRequest(
    spec:AnnotatedBehaviorSpec<State, Step>,
    relation:RefinementRelation<State, State>,
    idmap:Step->Actor,
    phase1:(State, Actor)->bool,
    phase2:(State, Actor)->bool,
    crashed:State->bool
    )

  predicate PhaseUnaffectedByOtherActors<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    && (forall s, s', step, actor :: ActionTuple(s, s', step) in clrr.spec.next && clrr.idmap(step) != actor ==>
                              (clrr.phase1(s, actor) <==> clrr.phase1(s', actor)))
    && (forall s, s', step, actor :: ActionTuple(s, s', step) in clrr.spec.next && clrr.idmap(step) != actor ==>
                              (clrr.phase2(s, actor) <==> clrr.phase2(s', actor)))
  }

  predicate CantGoDirectlyFromPhase2ToPhase1<State(!new), Actor, Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall s, s', step :: ActionTuple(s, s', step) in clrr.spec.next && clrr.phase2(s, clrr.idmap(step)) ==> !clrr.phase1(s', clrr.idmap(step))
  }

  predicate RightMoversPreserveStateRefinement<State(!new), Actor, Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall s, s', step ::
      && ActionTuple(s, s', step) in clrr.spec.next
      && clrr.phase1(s', clrr.idmap(step))
      && !clrr.crashed(s')
      ==> RefinementPair(s', s) in clrr.relation
  }

  predicate LeftMoversPreserveStateRefinement<State(!new), Actor, Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall s, s', step ::
      && ActionTuple(s, s', step) in clrr.spec.next
      && clrr.phase2(s, clrr.idmap(step))
      ==> RefinementPair(s, s') in clrr.relation
  }

  predicate NoStepsAfterCrash<State(!new), Actor(!new), Step(!new)(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall s, s', step :: ActionTuple(s, s', step) in clrr.spec.next ==> !clrr.crashed(s)
  }

  predicate RightMoversCommuteConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:Step,
    other_step:Step
    )
  {
    && initial_state in AnnotatedReachables(clrr.spec)
    && ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    && clrr.idmap(right_mover) != clrr.idmap(other_step)
    && clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    && !clrr.crashed(state_after_both_steps)
  }

  predicate RightMoversCommute<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RightMoversCommuteConditions(clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step)}
      :: RightMoversCommuteConditions(clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step)
      ==> exists new_middle_state, other_step', right_mover' ::
            && ActionTuple(initial_state, new_middle_state, other_step') in clrr.spec.next
            && ActionTuple(new_middle_state, state_after_both_steps, right_mover') in clrr.spec.next
            && clrr.idmap(other_step') == clrr.idmap(other_step)
            && clrr.idmap(right_mover') == clrr.idmap(right_mover)
  }

  predicate LeftMoversCommuteConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:Step,
    left_mover:Step
    )
  {
    && initial_state in AnnotatedReachables(clrr.spec)
    && ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    && clrr.idmap(other_step) != clrr.idmap(left_mover)
    && clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    && !clrr.crashed(state_after_both_steps)
  }

  predicate LeftMoversCommute<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger LeftMoversCommuteConditions(clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)}
      :: LeftMoversCommuteConditions(clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)
      ==> exists new_middle_state, left_mover', other_step' ::
            && ActionTuple(initial_state, new_middle_state, left_mover') in clrr.spec.next
            && ActionTuple(new_middle_state, state_after_both_steps, other_step') in clrr.spec.next
            && clrr.idmap(left_mover') == clrr.idmap(left_mover)
            && clrr.idmap(other_step') == clrr.idmap(other_step)
  }

  predicate LeftMoversAlwaysEnabledConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    s:State,
    actor:Actor
    )
  {
    && s in AnnotatedReachables(clrr.spec)
    && clrr.phase2(s, actor)
    && !clrr.crashed(s)
  }

  predicate LeftMoversAlwaysEnabled<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall s, actor
      {:trigger LeftMoversAlwaysEnabledConditions(clrr, s, actor)}
      :: LeftMoversAlwaysEnabledConditions(clrr, s, actor)
      ==> exists states, trace ::
             && StateNextSeq(states, trace, clrr.spec.next)
             && states[0] == s
             && (clrr.crashed(last(states)) || !clrr.phase2(last(states), actor))
             && (forall i :: 0 <= i < |states|-1 ==> clrr.phase2(states[i], actor))
             && (forall step :: step in trace ==> clrr.idmap(step) == actor)
  }

  predicate LeftMoversEnabledBeforeCrashConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    post_crash_state:State,
    crash_step:Step,
    actor:Actor
    )
  {
    && initial_state in AnnotatedReachables(clrr.spec)
    && ActionTuple(initial_state, post_crash_state, crash_step) in clrr.spec.next
    && !clrr.crashed(initial_state)
    && clrr.crashed(post_crash_state)
    && clrr.idmap(crash_step) != actor
    && clrr.phase2(initial_state, actor)
  }

  predicate LeftMoversEnabledBeforeCrash<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall initial_state, post_crash_state, crash_step, actor
      {:trigger LeftMoversEnabledBeforeCrashConditions(clrr, initial_state, post_crash_state, crash_step, actor)}
      :: LeftMoversEnabledBeforeCrashConditions(clrr, initial_state, post_crash_state, crash_step, actor)
      ==> exists states, trace, crash_step', post_crash_state' ::
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
  }

  predicate RightMoverCrashPreservationConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:Step,
    other_step:Step
    )
  {
    && initial_state in AnnotatedReachables(clrr.spec)
    && ActionTuple(initial_state, state_after_right_mover, right_mover) in clrr.spec.next
    && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in clrr.spec.next
    && !clrr.crashed(initial_state)
    && !clrr.crashed(state_after_right_mover)
    && clrr.crashed(state_after_both_steps)
    && clrr.phase1(state_after_right_mover, clrr.idmap(right_mover))
    && clrr.idmap(right_mover) != clrr.idmap(other_step)
  }

  predicate RightMoverCrashPreservation<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RightMoverCrashPreservationConditions(clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover,
                                                      other_step)}
      :: RightMoverCrashPreservationConditions(clrr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step)
      ==> exists other_step', state_after_other_step' ::
            && clrr.idmap(other_step') == clrr.idmap(other_step)
            && ActionTuple(initial_state, state_after_other_step', other_step') in clrr.spec.next
            && clrr.crashed(state_after_other_step')
            && RefinementPair(state_after_both_steps, state_after_other_step') in clrr.relation
  }

  predicate LeftMoverSelfCrashPreservationConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:Step,
    left_mover:Step
    )
  {
    && initial_state in AnnotatedReachables(clrr.spec)
    && ActionTuple(initial_state, state_after_other_step, other_step) in clrr.spec.next
    && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in clrr.spec.next
    && !clrr.crashed(initial_state)
    && !clrr.crashed(state_after_other_step)
    && clrr.crashed(state_after_both_steps)
    && clrr.phase2(state_after_other_step, clrr.idmap(left_mover))
    && clrr.idmap(left_mover) != clrr.idmap(other_step)
  }

  predicate LeftMoverSelfCrashPreservation<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger LeftMoverSelfCrashPreservationConditions(clrr, initial_state, state_after_other_step, state_after_both_steps, other_step,
                                                         left_mover)}
      :: LeftMoverSelfCrashPreservationConditions(clrr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)
      ==> exists left_mover', state_after_left_mover' ::
            && clrr.idmap(left_mover') == clrr.idmap(left_mover)
            && ActionTuple(initial_state, state_after_left_mover', left_mover') in clrr.spec.next
            && clrr.crashed(state_after_left_mover')
            && RefinementPair(state_after_both_steps, state_after_left_mover') in clrr.relation
  }

  predicate ActionSequencesLiftableConditions<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>,
    states:seq<State>,
    trace:seq<Step>,
    actor:Actor
    )
  {
    && StateNextSeq(states, trace, clrr.spec.next)
    && (forall step :: step in trace ==> clrr.idmap(step) == actor)
    && |states| > 1
    && !clrr.phase1(states[0], actor)
    && !clrr.phase2(states[0], actor)
    && (var s := last(states); !clrr.crashed(s) ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor))
    && (forall i :: 0 <= i < |trace| ==> !clrr.crashed(states[i]))
    && (forall i :: 0 < i < |trace| ==> var s := states[i]; clrr.phase1(s, actor) || clrr.phase2(s, actor))
  }

  predicate ActionSequencesLiftable<State(!new), Actor(!new), Step(!new)>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    forall states, trace, actor
      {:trigger ActionSequencesLiftableConditions(clrr, states, trace, actor)}
      :: ActionSequencesLiftableConditions(clrr, states, trace, actor)
      ==> exists hstep :: ActionTuple(states[0], last(states), hstep) in clrr.spec.next && clrr.idmap(hstep) == actor
  }

  predicate ValidCohenLamportReductionRequest<State(!new), Actor(!new), Step>(
    clrr:CohenLamportReductionRequest<State, Actor, Step>
    )
  {
    && RefinementRelationReflexive(clrr.relation)
    && RefinementRelationTransitive(clrr.relation)
    && (forall s, actor :: s in clrr.spec.init ==> !clrr.phase1(s, actor) && !clrr.phase2(s, actor))
    && (forall s, actor :: clrr.phase1(s, actor) ==> !clrr.phase2(s, actor))
    && CantGoDirectlyFromPhase2ToPhase1(clrr)
    && PhaseUnaffectedByOtherActors(clrr)
    && RightMoversPreserveStateRefinement(clrr)
    && LeftMoversPreserveStateRefinement(clrr)
    && NoStepsAfterCrash(clrr)
    && RightMoversCommute(clrr)
    && LeftMoversCommute(clrr)
    && LeftMoversAlwaysEnabled(clrr)
    && LeftMoversEnabledBeforeCrash(clrr)
    && RightMoverCrashPreservation(clrr)
    && LeftMoverSelfCrashPreservation(clrr)
    && ActionSequencesLiftable(clrr)
  }
}
