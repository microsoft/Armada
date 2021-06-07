/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file is the specification for a request to perform refinement via a Cohen-Lamport reduction
// on a behavior. Such a reduction takes a behavior where some states are in phase 1 or 2, and
// returns a behavior satisfying a higher-level specification that lacks those phases.  It does
// so by lifting sequences of steps in the lower-level specification to atomic steps in the
// higher-level specification.
//
// To use this specification, first create a request r of type RefinementViaReductionRequest.  Then,
// prove that it's a valid request, i.e., that ValidRefinementViaReductionRequest(r).  Finally, call
// lemma_PerformRefinementViaReduction (in RefinementViaReduction.i.dfy).
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

module RefinementViaReductionSpecModule {

  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule

  datatype RefinementViaReductionRequest<!State(==), !Actor(==), !LStep, HStep> = RefinementViaReductionRequest(
    lspec:AnnotatedBehaviorSpec<State, LStep>,
    hspec:AnnotatedBehaviorSpec<State, HStep>,
    relation:RefinementRelation<State, State>,
    idmap:LStep->Actor,
    phase1:(State, Actor)->bool,
    phase2:(State, Actor)->bool,
    crashed:State->bool
    )

  predicate PhaseUnaffectedByOtherActors<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    && (forall s, s', step, actor :: ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor ==>
                              (rr.phase1(s, actor) <==> rr.phase1(s', actor)))
    && (forall s, s', step, actor :: ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor ==>
                              (rr.phase2(s, actor) <==> rr.phase2(s', actor)))
  }

  predicate CantGoDirectlyFromPhase2ToPhase1<State(!new), Actor, LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall s, s', step :: ActionTuple(s, s', step) in rr.lspec.next && rr.phase2(s, rr.idmap(step)) ==> !rr.phase1(s', rr.idmap(step))
  }

  predicate RightMoversPreserveStateRefinement<State(!new), Actor, LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall s, s', step ::
      && ActionTuple(s, s', step) in rr.lspec.next
      && rr.phase1(s', rr.idmap(step))
      && !rr.crashed(s')
      ==> RefinementPair(s', s) in rr.relation
  }

  predicate LeftMoversPreserveStateRefinement<State(!new), Actor, LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall s, s', step ::
      && ActionTuple(s, s', step) in rr.lspec.next
      && rr.phase2(s, rr.idmap(step))
      ==> RefinementPair(s, s') in rr.relation
  }

  predicate PostCrashStepsStutter<State(!new), Actor(!new), LStep(!new), HStep(!new)>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall s, s', step :: rr.crashed(s) && ActionTuple(s, s', step) in rr.lspec.next ==> s' == s
  }

  predicate RightMoversCommuteConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_step:LStep
    )
  {
    && initial_state in AnnotatedReachables(rr.lspec)
    && ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    && rr.idmap(right_mover) != rr.idmap(other_step)
    && rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    && !rr.crashed(state_after_both_steps)
  }

  predicate RightMoversCommute<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RightMoversCommuteConditions(rr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step)}
      :: RightMoversCommuteConditions(rr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step)
      ==> exists new_middle_state, other_step', right_mover' ::
            && ActionTuple(initial_state, new_middle_state, other_step') in rr.lspec.next
            && ActionTuple(new_middle_state, state_after_both_steps, right_mover') in rr.lspec.next
            && rr.idmap(other_step') == rr.idmap(other_step)
            && rr.idmap(right_mover') == rr.idmap(right_mover)
  }

  predicate LeftMoversCommuteConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:LStep,
    left_mover:LStep
    )
  {
    && initial_state in AnnotatedReachables(rr.lspec)
    && ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
    && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    && rr.idmap(other_step) != rr.idmap(left_mover)
    && rr.phase2(state_after_other_step, rr.idmap(left_mover))
    && !rr.crashed(state_after_both_steps)
  }

  predicate LeftMoversCommute<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger LeftMoversCommuteConditions(rr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)}
      :: LeftMoversCommuteConditions(rr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)
      ==> exists new_middle_state, left_mover', other_step' ::
            && ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
            && ActionTuple(new_middle_state, state_after_both_steps, other_step') in rr.lspec.next
            && rr.idmap(left_mover') == rr.idmap(left_mover)
            && rr.idmap(other_step') == rr.idmap(other_step)
  }

  predicate LeftMoversAlwaysEnabledConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    s:State,
    actor:Actor
    )
  {
    && s in AnnotatedReachables(rr.lspec)
    && rr.phase2(s, actor)
    && !rr.crashed(s)
  }

  predicate LeftMoversAlwaysEnabled<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall s, actor
      {:trigger LeftMoversAlwaysEnabledConditions(rr, s, actor)}
      :: LeftMoversAlwaysEnabledConditions(rr, s, actor)
      ==> exists states, trace ::
             && StateNextSeq(states, trace, rr.lspec.next)
             && states[0] == s
             && (rr.crashed(last(states)) || !rr.phase2(last(states), actor))
             && (forall i :: 0 <= i < |states|-1 ==> rr.phase2(states[i], actor))
             && (forall step :: step in trace ==> rr.idmap(step) == actor)
  }

  predicate LeftMoversEnabledBeforeCrashConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    initial_state:State,
    post_crash_state:State,
    crash_step:LStep,
    actor:Actor
    )
  {
    && initial_state in AnnotatedReachables(rr.lspec)
    && ActionTuple(initial_state, post_crash_state, crash_step) in rr.lspec.next
    && !rr.crashed(initial_state)
    && rr.crashed(post_crash_state)
    && rr.idmap(crash_step) != actor
    && rr.phase2(initial_state, actor)
  }

  predicate LeftMoversEnabledBeforeCrash<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall initial_state, post_crash_state, crash_step, actor
      {:trigger LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_step, actor)}
      :: LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_step, actor)
      ==> exists states, trace, crash_step', post_crash_state' ::
             && StateNextSeq(states, trace, rr.lspec.next)
             && states[0] == initial_state
             && !rr.crashed(last(states))
             && !rr.phase2(last(states), actor)
             && (forall i :: 0 <= i < |states|-1 ==> rr.phase2(states[i], actor))
             && (forall step :: step in trace ==> rr.idmap(step) == actor)
             && ActionTuple(last(states), post_crash_state', crash_step') in rr.lspec.next
             && rr.idmap(crash_step') == rr.idmap(crash_step)
             && rr.crashed(post_crash_state')
             && RefinementPair(post_crash_state, post_crash_state') in rr.relation
  }

  predicate RightMoverCrashPreservationConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    initial_state:State,
    state_after_right_mover:State,
    state_after_both_steps:State,
    right_mover:LStep,
    other_step:LStep
    )
  {
    && initial_state in AnnotatedReachables(rr.lspec)
    && ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    && !rr.crashed(initial_state)
    && !rr.crashed(state_after_right_mover)
    && rr.crashed(state_after_both_steps)
    && rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    && rr.idmap(right_mover) != rr.idmap(other_step)
  }

  predicate RightMoverCrashPreservation<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover, state_after_both_steps, right_mover,
                                                      other_step)}
      :: RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step) 
      ==> exists other_step', state_after_other_step' ::
            && rr.idmap(other_step') == rr.idmap(other_step)
            && ActionTuple(initial_state, state_after_other_step', other_step') in rr.lspec.next
            && rr.crashed(state_after_other_step')
            && RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  }

  predicate LeftMoverSelfCrashPreservationConditions<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>,
    initial_state:State,
    state_after_other_step:State,
    state_after_both_steps:State,
    other_step:LStep,
    left_mover:LStep
    )
  {
    && initial_state in AnnotatedReachables(rr.lspec)
    && ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
    && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    && !rr.crashed(initial_state)
    && !rr.crashed(state_after_other_step)
    && rr.crashed(state_after_both_steps)
    && rr.phase2(state_after_other_step, rr.idmap(left_mover))
    && rr.idmap(left_mover) != rr.idmap(other_step)
  }

  predicate LeftMoverSelfCrashPreservation<State(!new), Actor(!new), LStep(!new), HStep>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_step, state_after_both_steps, other_step,
                left_mover)}
      :: LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover)
      ==> exists left_mover', state_after_left_mover' ::
            && rr.idmap(left_mover') == rr.idmap(left_mover)
            && ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
            && rr.crashed(state_after_left_mover')
            && RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation
  }

  predicate ActionSequencesLiftableConditions<State(!new), Actor(!new), LStep(!new), HStep(!new)>(
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
    && (forall i :: 0 < i < |trace| ==> var s := states[i]; rr.phase1(s, actor) || rr.phase2(s, actor))
  }

  predicate ActionSequencesLiftable<State(!new), Actor(!new), LStep(!new), HStep(!new)>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    forall states, trace, actor
      {:trigger ActionSequencesLiftableConditions(rr, states, trace, actor)}
      :: ActionSequencesLiftableConditions(rr, states, trace, actor)
      ==> exists hstep :: ActionTuple(states[0], last(states), hstep) in rr.hspec.next
  }

  predicate ValidRefinementViaReductionRequest<State(!new), Actor(!new), LStep(!new), HStep(!new)>(
    rr:RefinementViaReductionRequest<State, Actor, LStep, HStep>
    )
  {
    && RefinementRelationReflexive(rr.relation)
    && RefinementRelationTransitive(rr.relation)
    && rr.hspec.init == rr.lspec.init
    && (forall s, actor :: s in rr.lspec.init ==> !rr.phase1(s, actor) && !rr.phase2(s, actor))
    && (forall s, actor :: rr.phase1(s, actor) ==> !rr.phase2(s, actor))
    && CantGoDirectlyFromPhase2ToPhase1(rr)
    && PhaseUnaffectedByOtherActors(rr)
    && RightMoversPreserveStateRefinement(rr)
    && LeftMoversPreserveStateRefinement(rr)
    && PostCrashStepsStutter(rr)
    && RightMoversCommute(rr)
    && LeftMoversCommute(rr)
    && LeftMoversAlwaysEnabled(rr)
    && LeftMoversEnabledBeforeCrash(rr)
    && RightMoverCrashPreservation(rr)
    && LeftMoverSelfCrashPreservation(rr)
    && ActionSequencesLiftable(rr)
  }
}
