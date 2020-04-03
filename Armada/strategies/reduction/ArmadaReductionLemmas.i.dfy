/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains lemmas useful in effecting a refinement via reduction on an Armada behavior.
// They support lemma_PerformArmadaReduction (in ArmadaReduction.i.dfy).
//
// The general strategy is to show that the Armada state machine, despite all its complexity having
// to do with things like tau operations and multisteps, nevertheless satisfies the conditions
// required by the more generic lemma_PerformRefinementViaReduction (in
// RefinementViaReduction.i.dfy).  These conditions are satisfied by creating a
// RefinementViaReductionRequest and proving that it satisfies ValidRefinementViaReductionRequest.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "ArmadaReductionSpec.i.dfy"
include "RefinementViaReductionSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"
include "../generic/GenericArmadaLemmas.i.dfy"

module ArmadaReductionLemmasModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaReductionSpecModule
  import opened RefinementViaReductionSpecModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened ArmadaCommonDefinitions

  //////////////////////////////////////////////////////////
  // FUNCTIONS FOR BUILDING CRASHING REDUCTION REQUEST
  //////////////////////////////////////////////////////////

  predicate IsNonyieldingOrInPhase<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    arr.l.state_ok(s) && pc.Some? && (arr.l.is_pc_nonyielding(pc.v) || arr.is_phase1(pc.v) || arr.is_phase2(pc.v))
  }

  predicate GenericNextReduced<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && Armada_NextMultipleSteps(arr.l, s, s', steps)
    && (forall step :: step in steps ==> arr.l.step_to_thread(step) == tid)
    && (forall step :: step in steps ==> arr.l.is_step_tau(step) == tau)
    && if tau then |steps| <= 1 else |steps| > 0 ==> (
        && !IsNonyieldingOrInPhase(arr, s, tid)
        && !IsNonyieldingOrInPhase(arr, s', tid)
        && (var states := Armada_GetStateSequence(arr.l, s, steps);
           forall i :: 0 < i < |steps| ==> IsNonyieldingOrInPhase(arr, states[i], tid))
      )
  }

  predicate RefinementViaReductionLSpecNext<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:Armada_Multistep<LOneStep>
    )
  {
    Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau)
  }

  function GetRefinementViaReductionLSpec<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : AnnotatedBehaviorSpec<LState, Armada_Multistep<LOneStep>>
  {
    AnnotatedBehaviorSpec(
      iset s | arr.l.init(s),
      iset s, s', step | RefinementViaReductionLSpecNext(arr, s, s', step) :: ActionTuple(s, s', step))
  }

  predicate RefinementViaReductionHSpecNext<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:Armada_Multistep<LOneStep>
    )
  {
    GenericNextReduced(arr, s, s', step.steps, step.tid, step.tau)
  }

  function GetRefinementViaReductionHSpec<LState(!new), LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : AnnotatedBehaviorSpec<LState, Armada_Multistep<LOneStep>>
  {
    AnnotatedBehaviorSpec(
      iset s | arr.l.init(s),
      iset s, s', step | RefinementViaReductionHSpecNext(arr, s, s', step) :: ActionTuple(s, s', step))
  }

  function RefinementViaReductionIdmap<LState, LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    step:Armada_Multistep<LOneStep>
    ) : Option<Armada_ThreadHandle>
  {
    if step.tau then None else Some(step.tid)
  }

  function GetRefinementViaReductionIdmap<LState, LOneStep(!new), LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : Armada_Multistep<LOneStep>->Option<Armada_ThreadHandle>
  {
    step => RefinementViaReductionIdmap(arr, step)
  }

  predicate RefinementViaReductionPhase1<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Option<Armada_ThreadHandle>
    )
  {
    && tid.Some?
    && var pc := arr.l.get_thread_pc(s, tid.v);
      pc.Some? && arr.is_phase1(pc.v)
  }

  function GetRefinementViaReductionPhase1<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : (LState, Option<Armada_ThreadHandle>)->bool
  {
    (s:LState, tid:Option<Armada_ThreadHandle>) => RefinementViaReductionPhase1(arr, s, tid)
  }

  predicate RefinementViaReductionPhase2<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Option<Armada_ThreadHandle>
    )
  {
    && tid.Some?
    && var pc := arr.l.get_thread_pc(s, tid.v);
      pc.Some? && arr.is_phase2(pc.v)
  }

  function GetRefinementViaReductionPhase2<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : (LState, Option<Armada_ThreadHandle>)->bool
  {
    (s:LState, tid:Option<Armada_ThreadHandle>) => RefinementViaReductionPhase2(arr, s, tid)
  }

  function GetRefinementViaReductionCrashedPred<LState(!new), LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : LState->bool
  {
    (s:LState) => !arr.l.state_ok(s)
  }

  function GetRefinementViaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    ) : RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>
  {
    RefinementViaReductionRequest(GetRefinementViaReductionLSpec(arr), GetRefinementViaReductionHSpec(arr), arr.self_relation,
                                  GetRefinementViaReductionIdmap(arr), GetRefinementViaReductionPhase1(arr),
                                  GetRefinementViaReductionPhase2(arr), GetRefinementViaReductionCrashedPred(arr))
  }

  //////////////////////////////
  // UTILITY PREDICATES
  //////////////////////////////

  predicate IsPhase1<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.is_phase1(pc.v)
  }

  predicate IsPhase2<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.is_phase2(pc.v)
  }

  predicate IsNonyielding<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.l.is_pc_nonyielding(pc.v)
  }

  predicate PCTypesMatch<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    tid:Armada_ThreadHandle
    )
  {
    && IsPhase1(arr, s', tid) == IsPhase1(arr, s, tid)
    && IsPhase2(arr, s', tid) == IsPhase2(arr, s, tid)
    && IsNonyielding(arr, s', tid) == IsNonyielding(arr, s, tid)
  }

  predicate OKAndPCTypesMatch<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    tid:Armada_ThreadHandle
    )
  {
    && arr.l.state_ok(s') == arr.l.state_ok(s)
    && PCTypesMatch(arr, s, s', tid)
  }

  //////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////

  lemma lemma_SpecificSequenceCaseA<T>(s1:seq<T>, s2:seq<T>, x:T, i:int)
    requires |s2| > 0
    requires 0 <= i - |s1 + [x]| + 1 < |s2[1..]|
    ensures  s2[1..][i - |s1 + [x]| + 1] == s2[i - |s1| + 1]
  {
  }

  lemma lemma_SpecificSequenceCaseB<T>(s1:seq<T>, x:T, i:int)
    requires |s1| > 0
    requires i == |s1| - 1
    ensures  (s1 + [x])[i] == last(s1)
  {
  }

  lemma lemma_SpecificSequenceCaseC<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, i:int)
    requires |s1| > 0
    requires |s3| > 0
    requires |s1| <= i + 1 < |s1| + |s2|
    ensures  s2[(i-|all_but_last(s1)|+1)-|[last(s3)]|] == s2[i-|s1|+1]
  {
  }

  lemma lemma_ExtendingStateSequenceWorks<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    states:seq<LState>,
    next_step:LOneStep,
    next_state:LState
    )
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires states == Armada_GetStateSequence(arr.l, s, steps)
    requires arr.l.step_valid(s', next_step)
    requires next_state == arr.l.step_next(s', next_step)
    ensures  Armada_NextMultipleSteps(arr.l, s, next_state, steps + [next_step])
    ensures  states + [next_state] == Armada_GetStateSequence(arr.l, s, steps + [next_step])
    decreases |steps|
  {
    if |steps| > 0 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_ExtendingStateSequenceWorks(arr, s_mid, s', steps[1..], states[1..], next_step, next_state);
      assert steps + [next_step] == [steps[0]] + (steps[1..] + [next_step]);
      assert states + [next_state] == [states[0]] + (states[1..] + [next_state]);
    }
  }

  lemma lemma_AllButLastPreservesArmadaNextMultipleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    states:seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires states == Armada_GetStateSequence(arr.l, s, steps)
    requires |steps| > 0
    ensures  all_but_last(states) == Armada_GetStateSequence(arr.l, s, all_but_last(steps))
    ensures  Armada_NextMultipleSteps(arr.l, s, states[|states|-2], all_but_last(steps))
  {
    if |steps| > 1 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, s_mid, s', steps[1..], states[1..]);
      assert all_but_last(states[1..]) == Armada_GetStateSequence(arr.l, s_mid, all_but_last(steps[1..]));
      assert Armada_NextMultipleSteps(arr.l, s_mid, states[1..][|states[1..]|-2], all_but_last(steps[1..]));
      assert states[1..][|states[1..]|-2] == states[|states|-2];

      var abl := [steps[0]] + all_but_last(steps[1..]);
      assert abl[0] == steps[0];
      assert abl[1..] == all_but_last(steps[1..]);
      assert abl == all_but_last(steps);

      calc {
        all_but_last(states);
        [states[0]] + all_but_last(states[1..]);
        [states[0]] + Armada_GetStateSequence(arr.l, s_mid, all_but_last(steps[1..]));
        Armada_GetStateSequence(arr.l, s, [steps[0]] + all_but_last(steps[1..]));
        Armada_GetStateSequence(arr.l, s, all_but_last(steps));
      }
    }
  }

  lemma lemma_IfMultistepEndsInPhase1ThenEachStepDoes<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:Armada_Multistep<LOneStep>,
    states:seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires !step.tau
    requires Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau)
    requires states == Armada_GetStateSequence(arr.l, s, step.steps)
    requires IsPhase1(arr, s', step.tid)
    ensures  forall s :: s in states ==> arr.l.get_thread_pc(s, step.tid).Some?
    ensures  forall i :: 0 < i < |states| ==> arr.is_phase1(arr.l.get_thread_pc(states[i], step.tid).v)
  {
    var pos := |states|-1;
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
    while pos > 0
      invariant 0 <= pos < |states|
      invariant arr.l.get_thread_pc(states[pos], step.tid).Some?
      invariant pos > 0 ==> arr.is_phase1(arr.l.get_thread_pc(states[pos], step.tid).v)
      invariant forall i :: pos <= i < |states| ==> arr.l.get_thread_pc(states[i], step.tid).Some?
      invariant forall i :: pos < i < |states| ==> arr.is_phase1(arr.l.get_thread_pc(states[i], step.tid).v)
      decreases pos
    {
      var prev_pos := pos-1;
      lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, prev_pos);
      var pc := arr.l.get_thread_pc(states[prev_pos], step.tid);
      var pc' := arr.l.get_thread_pc(states[prev_pos+1], step.tid);
      assert pc'.Some? && arr.is_phase1(pc'.v);
      assert arr.l.step_valid(states[prev_pos], step.steps[prev_pos]);
      assert states[prev_pos+1] == arr.l.step_next(states[prev_pos], step.steps[prev_pos]);
      assert pc.Some?;
      if prev_pos > 0 {
        assert arr.is_phase1(pc.v);
        assert IsPhase1(arr, states[prev_pos], step.tid);
      }
      pos := prev_pos;
    }
  }

  lemma lemma_IfMultistepStartsInPhase2ThenEachStepDoes<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:Armada_Multistep<LOneStep>,
    states:seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires !step.tau
    requires Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau)
    requires states == Armada_GetStateSequence(arr.l, s, step.steps)
    requires IsPhase2(arr, s, step.tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], step.tid)
  {
    if |states| == 1 {
      return;
    }

    var pos := 0;
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
    while pos < |states|-2
      invariant 0 <= pos <= |states|-2
      invariant arr.l.get_thread_pc(states[pos], step.tid).Some?
      invariant arr.is_phase2(arr.l.get_thread_pc(states[pos], step.tid).v)
      invariant forall i :: 0 <= i <= pos ==> arr.l.get_thread_pc(states[i], step.tid).Some?
      invariant forall i :: 0 <= i <= pos ==> arr.is_phase2(arr.l.get_thread_pc(states[i], step.tid).v)
      decreases |states|-pos
    {
      lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, pos);
      var pc := arr.l.get_thread_pc(states[pos], step.tid);
      var pc' := arr.l.get_thread_pc(states[pos+1], step.tid);
      assert pc.Some? && arr.is_phase2(pc.v);
      assert arr.l.step_valid(states[pos], step.steps[pos]);
      assert states[pos+1] == arr.l.step_next(states[pos], step.steps[pos]);
      var next_pos := pos+1;
      assert 0 < next_pos < |step.steps|;
      assert arr.l.get_thread_pc(states[next_pos], step.tid).Some?
               && arr.l.is_pc_nonyielding(arr.l.get_thread_pc(states[next_pos], step.tid).v);
      assert pc'.Some?;
      assert arr.is_phase2(pc'.v);
      pos := pos + 1;
    }
  }

  lemma lemma_StateAmongAnnotatedReachablesHasThreadYielding<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires s in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    ensures  arr.l.state_ok(s) ==> Armada_ThreadYielding(arr.l, s, tid)
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    reveal_AnnotatedReachables();
    var ab :| AnnotatedBehaviorSatisfiesSpec(ab, rspec) && last(ab.states) == s;
    var pos := 0;
    while pos < |ab.states|-1
      invariant 0 <= pos < |ab.states|
      invariant arr.l.state_ok(ab.states[pos]) ==> Armada_ThreadYielding(arr.l, ab.states[pos], tid)
      decreases |ab.states|-pos
    {
      var subpos := 0;
      var s := ab.states[pos];
      var s' := ab.states[pos+1];
      var step := ab.trace[pos];
      assert ActionTuple(ab.states[pos], ab.states[pos+1], ab.trace[pos]) in rspec.next;
      lemma_TakingMultistepKeepsThreadYielding(arr.l, ab.states[pos], ab.states[pos+1], ab.trace[pos], tid);
      pos := pos + 1;
    }
  }

  lemma lemma_ArmadaNextMultipleStepsTransitive<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    steps1:seq<LOneStep>,
    steps2:seq<LOneStep>
    )
    requires Armada_NextMultipleSteps(arr.l, s1, s2, steps1)
    requires Armada_NextMultipleSteps(arr.l, s2, s3, steps2)
    ensures  Armada_NextMultipleSteps(arr.l, s1, s3, steps1 + steps2)
  {
    if |steps1| > 0 {
      var s_mid := arr.l.step_next(s1, steps1[0]);
      lemma_ArmadaNextMultipleStepsTransitive(arr, s_mid, s2, s3, steps1[1..], steps2);
      assert Armada_NextMultipleSteps(arr.l, s_mid, s3, steps1[1..] + steps2);
      var steps3 := steps1 + steps2;
      assert steps3[0] == steps1[0];
      assert steps3[1..] == steps1[1..] + steps2;
    }
    else {
      assert s1 == s2;
      assert steps1 + steps2 == steps2;
    }
  }

  lemma lemma_ExecutingStepOfOtherActorDoesntChangePCType<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:LOneStep,
    tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.l.step_valid(s, step)
    requires s' == arr.l.step_next(s, step)
    requires arr.l.step_to_thread(step) != tid || arr.l.is_step_tau(step)
    ensures  PCTypesMatch(arr, s, s', tid)
  {
  }

  lemma lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    tau:bool,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires forall step :: step in steps ==> arr.l.step_to_thread(step) == tid
    requires forall step :: step in steps ==> arr.l.is_step_tau(step) == tau
    requires tau || tid != other_tid
    ensures  PCTypesMatch(arr, s, s', other_tid)
    decreases |steps|
  {
    if |steps| > 0 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, s, s_mid, steps[0], other_tid);
      lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, s_mid, s', steps[1..], tau, tid, other_tid);
    }
  }

  lemma lemma_ExecutingStepOfOtherActorDoesntRemovePC<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    step:LOneStep,
    tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.l.step_valid(s, step)
    requires s' == arr.l.step_next(s, step)
    requires arr.l.step_to_thread(step) != tid || arr.l.is_step_tau(step)
    ensures  arr.l.get_thread_pc(s, tid).Some? ==> arr.l.get_thread_pc(s', tid).Some?
  {
  }

  lemma lemma_ExecutingStepSequenceOfOtherActorDoesntRemovePC<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    tau:bool,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires forall step :: step in steps ==> arr.l.step_to_thread(step) == tid
    requires forall step :: step in steps ==> arr.l.is_step_tau(step) == tau
    requires tau || tid != other_tid
    ensures  arr.l.get_thread_pc(s, other_tid).Some? ==> arr.l.get_thread_pc(s', other_tid).Some?
    decreases |steps|
  {
    if |steps| > 0 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_ExecutingStepOfOtherActorDoesntRemovePC(arr, s, s_mid, steps[0], other_tid);
      lemma_ExecutingStepSequenceOfOtherActorDoesntRemovePC(arr, s_mid, s', steps[1..], tau, tid, other_tid);
    }
  }

  //////////////////////////////
  // LEMMA-SPECIFIC PREDICATES
  //////////////////////////////

  predicate PerformRightMoveTrigger(i:int)
  {
    true
  }

  predicate PerformRightMoveThroughPredicate<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    other_tid:Armada_ThreadHandle,
    other_states_before:seq<LState>,
    other_states_after:seq<LState>,
    other_states':seq<LState>
    )
    requires |other_states_before| > 0
    requires |other_states_after| > 0
    requires |other_states'| == |other_states_before| + |other_states_after| - 1
  {
    && (forall i {:trigger PerformRightMoveTrigger(i)} ::
             PerformRightMoveTrigger(i) && 0 <= i < |other_states_before| ==>
             OKAndPCTypesMatch(arr, other_states'[i], other_states_before[i], other_tid))
    && (forall i {:trigger PerformRightMoveTrigger(i)} ::
             PerformRightMoveTrigger(i) && |other_states_before|-1 <= i < |other_states'| ==>
             OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid))
  }

  predicate PerformRightMoveRemainingPredicate<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    mover_states_before:seq<LState>,
    mover_states_after:seq<LState>,
    mover_states':seq<LState>
    )
    requires |mover_states_before| > 0
    requires |mover_states_after| > 0
    requires |mover_states'| == |mover_states_before| + |mover_states_after| - 1
  {
    && (forall i {:trigger PerformRightMoveTrigger(i)} ::
          PerformRightMoveTrigger(i) && 0 <= i < |mover_states_before| ==>
          OKAndPCTypesMatch(arr, mover_states'[i], mover_states_before[i], mover_tid))
    && (forall i {:trigger PerformRightMoveTrigger(i)} ::
          PerformRightMoveTrigger(i) && |mover_states_before|-1 <= i < |mover_states'| ==>
          OKAndPCTypesMatch(arr, mover_states'[i], mover_states_after[i-|mover_states_before|+1], mover_tid))
  }

  //////////////////////////////////////////
  // LEMMAS SUPPORTING PERFORM-RIGHT-MOVE
  //////////////////////////////////////////

  lemma lemma_PerformRightMoveSingle<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    s1:LState,
    s2:LState,
    s3:LState,
    mover_step:LOneStep,
    other_step:LOneStep
    ) returns (
    s2':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires arr.inv(s1)
    requires arr.l.state_ok(s3)

    requires arr.l.step_to_thread(other_step) == other_tid
    requires arr.l.is_step_tau(other_step) == other_tau
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)

    requires arr.l.step_valid(s1, mover_step)
    requires s2 == arr.l.step_next(s1, mover_step)
    requires arr.l.step_valid(s2, other_step)
    requires s3 == arr.l.step_next(s2, other_step)

    requires arr.l.get_thread_pc(s1, mover_tid).Some?
    requires arr.l.get_thread_pc(s2, mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(s2, mover_tid).v)

    ensures  arr.l.step_valid(s1, other_step)
    ensures  s2' == arr.l.step_next(s1, other_step)
    ensures  arr.l.step_valid(s2', mover_step)
    ensures  s3 == arr.l.step_next(s2', mover_step)
    ensures  OKAndPCTypesMatch(arr, s2', s1, mover_tid)
  {
    assert ArmadaReductionSpecModule.RightMoversCommuteConditions(arr, s1, mover_step, other_step);
    s2' := arr.l.step_next(s1, other_step);
  }

  lemma lemma_PerformRightMoveThroughHelper<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_step:LOneStep,
    other_steps_before:seq<LOneStep>,
    other_states_before:seq<LState>,
    other_steps_after:seq<LOneStep>,
    other_states_after:seq<LState>,
    s2':LState,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |other_states_before| > 0
    requires arr.inv(other_states_before[0])

    requires other_states_before == Armada_GetStateSequence(arr.l, other_states_before[0], other_steps_before)
    requires forall step :: step in other_steps_before ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps_before ==> arr.l.is_step_tau(step) == other_tau
    requires Armada_NextMultipleSteps(arr.l, other_states_before[0], last(other_states_before), other_steps_before)

    requires |other_states_after| > 0
    requires arr.l.state_ok(last(other_states_after))
    requires other_states_after == Armada_GetStateSequence(arr.l, other_states_after[0], other_steps_after)
    requires forall step :: step in other_steps_after ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps_after ==> arr.l.is_step_tau(step) == other_tau
    requires Armada_NextMultipleSteps(arr.l, other_states_after[0], last(other_states_after), other_steps_after)

    requires arr.l.step_valid(last(other_states_before), mover_step)
    requires other_states_after[0] == arr.l.step_next(last(other_states_before), mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)
    requires arr.l.get_thread_pc(other_states_before[0], mover_tid).Some?
    requires arr.l.get_thread_pc(other_states_after[0], mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(other_states_after[0], mover_tid).v)

    requires |other_steps_after| > 0
    requires |other_states_after| > 1

    requires arr.l.step_valid(last(other_states_before), other_steps_after[0])
    requires s2' == arr.l.step_next(last(other_states_before), other_steps_after[0])
    requires arr.l.step_valid(s2', mover_step)
    requires other_states_after[1] == arr.l.step_next(s2', mover_step)
    requires OKAndPCTypesMatch(arr, s2', last(other_states_before), mover_tid)

    requires |other_states'| == |(other_states_before + [s2'])| + |other_states_after[1..]| - 1
    requires other_states'[0] == (other_states_before + [s2'])[0]
    requires other_states' == Armada_GetStateSequence(arr.l, other_states'[0],
                                                     (other_steps_before + [other_steps_after[0]]) + other_steps_after[1..])
    requires Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'),
                                       (other_steps_before + [other_steps_after[0]]) + other_steps_after[1..])
    requires !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before + [s2'], other_states_after[1..],
                                                             other_states')
    requires OKAndPCTypesMatch(arr, last(other_states'), last((other_states_before + [s2'])), mover_tid)
    requires arr.l.step_valid(last(other_states'), mover_step)
    requires last(other_states_after[1..]) == arr.l.step_next(last(other_states'), mover_step)

    ensures  |other_states'| == |other_states_before| + |other_states_after| - 1
    ensures  other_states'[0] == other_states_before[0]
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps_before + other_steps_after)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps_before + other_steps_after)
    ensures  !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before, other_states_after, other_states')
    ensures  OKAndPCTypesMatch(arr, last(other_states'), last(other_states_before), mover_tid)
    ensures  arr.l.step_valid(last(other_states'), mover_step)
    ensures  last(other_states_after) == arr.l.step_next(last(other_states'), mover_step)
  {
    calc {
      other_steps_before + other_steps_after;
        { lemma_SequenceIsCarPlusCdr(other_steps_after); }
      other_steps_before + ([other_steps_after[0]] + other_steps_after[1..]);
        { lemma_SequenceConcatenationAssociative(other_steps_before, [other_steps_after[0]], other_steps_after[1..]); }
      (other_steps_before + [other_steps_after[0]]) + other_steps_after[1..];
    }

    if !other_tau {
      forall i | |other_states_before|-1 <= i < |other_states'|
        ensures OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid)
      {
        if i >= |other_states_before + [s2']|-1 {
          assert PerformRightMoveTrigger(i);
          assert OKAndPCTypesMatch(arr, other_states'[i], other_states_after[1..][i-|other_states_before + [s2']|+1], other_tid);
          calc {
            arr.l.get_thread_pc(other_states_after[1..][i-|other_states_before + [s2']|+1], other_tid);
              { lemma_SpecificSequenceCaseA(other_states_before, other_states_after, s2', i); }
            arr.l.get_thread_pc(other_states_after[i-|other_states_before|+1], other_tid);
          }
          assert OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid);
        }
        else {
          assert i == |other_states_before|-1;
          assert i < |other_states_before + [s2']|-1;
          assert PerformRightMoveTrigger(i);
          assert OKAndPCTypesMatch(arr, other_states'[i], (other_states_before + [s2'])[i], other_tid);
          calc {
            arr.l.get_thread_pc((other_states_before + [s2'])[i], other_tid);
              { lemma_SpecificSequenceCaseB(other_states_before, s2', i); }
            arr.l.get_thread_pc(last(other_states_before), other_tid);
          }
          lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, last(other_states_before), other_states_after[0], mover_step,
                                                            other_tid);
          calc {
            arr.l.get_thread_pc(other_states_after[0], other_tid);
              { assert i - |other_states_before| + 1 == 0; }
            arr.l.get_thread_pc(other_states_after[i-|other_states_before|+1], other_tid);
          }
          assert OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid);
        }
      }
    }
  }

  lemma lemma_PerformRightMoveThrough<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_step:LOneStep,
    other_steps_before:seq<LOneStep>,
    other_states_before:seq<LState>,
    other_steps_after:seq<LOneStep>,
    other_states_after:seq<LState>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |other_states_before| > 0
    requires arr.inv(other_states_before[0])

    requires other_states_before == Armada_GetStateSequence(arr.l, other_states_before[0], other_steps_before)
    requires forall step :: step in other_steps_before ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps_before ==> arr.l.is_step_tau(step) == other_tau
    requires Armada_NextMultipleSteps(arr.l, other_states_before[0], last(other_states_before), other_steps_before)

    requires |other_states_after| > 0
    requires arr.l.state_ok(last(other_states_after))
    requires other_states_after == Armada_GetStateSequence(arr.l, other_states_after[0], other_steps_after)
    requires forall step :: step in other_steps_after ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps_after ==> arr.l.is_step_tau(step) == other_tau
    requires Armada_NextMultipleSteps(arr.l, other_states_after[0], last(other_states_after), other_steps_after)

    requires arr.l.step_valid(last(other_states_before), mover_step)
    requires other_states_after[0] == arr.l.step_next(last(other_states_before), mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)
    requires arr.l.get_thread_pc(other_states_before[0], mover_tid).Some?
    requires arr.l.get_thread_pc(other_states_after[0], mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(other_states_after[0], mover_tid).v)

    ensures  |other_states'| == |other_states_before| + |other_states_after| - 1
    ensures  other_states'[0] == other_states_before[0]
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps_before + other_steps_after)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps_before + other_steps_after)
    ensures  !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before, other_states_after, other_states')

    ensures  OKAndPCTypesMatch(arr, last(other_states'), last(other_states_before), mover_tid)
    ensures  arr.l.step_valid(last(other_states'), mover_step)
    ensures  last(other_states_after) == arr.l.step_next(last(other_states'), mover_step)
    decreases |other_steps_after|
  {
    lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, other_states_before[0], last(other_states_before),
                                                              other_steps_before, other_tau, other_tid, mover_tid);
    if |other_steps_after| == 0 {
      other_states' := other_states_before;
      assert other_steps_before + other_steps_after == other_steps_before;
      if !other_tau {
        forall i | |other_states_before|-1 <= i < |other_states'|
          ensures OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid)
        {
          assert i == |other_states_before|-1;
          assert other_states'[i] == last(other_states_before);
          assert other_states_after[i-|other_states_before|+1] == other_states_after[0];
          lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, last(other_states_before), other_states_after[0], mover_step, other_tid);
        }
      }
    }
    else {
      lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, other_states_before[0], last(other_states_before), other_steps_before,
                                              other_states_before, |other_states_before|-1);
      var s2' := lemma_PerformRightMoveSingle(arr, mover_tid, other_tid, other_tau, last(other_states_before), other_states_after[0],
                                              other_states_after[1], mover_step, other_steps_after[0]);
      lemma_ExtendingStateSequenceWorks(arr, other_states_before[0], last(other_states_before), other_steps_before,
                                        other_states_before, other_steps_after[0], s2');
      other_states' := lemma_PerformRightMoveThrough(arr, mover_tid, other_tid, other_tau, mover_step,
                                                     other_steps_before + [other_steps_after[0]],
                                                     other_states_before + [s2'],
                                                     other_steps_after[1..], other_states_after[1..]);
      lemma_PerformRightMoveThroughHelper(arr, mover_tid, other_tid, other_tau, mover_step, other_steps_before,
                                          other_states_before, other_steps_after, other_states_after, s2', other_states');
    }
  }

  lemma lemma_PerformRightMoveOne<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_step:LOneStep,
    initial_state:LState,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires arr.inv(initial_state)

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires IsPhase1(arr, other_states[0], mover_tid)
    requires arr.l.step_valid(initial_state, mover_step)
    requires other_states[0] == arr.l.step_next(initial_state, mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)

    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == initial_state
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  OKAndPCTypesMatch(arr, last(other_states'), initial_state, mover_tid)
    ensures  arr.l.step_valid(last(other_states'), mover_step)
    ensures  last(other_states) == arr.l.step_next(last(other_states'), mover_step)
  {
    other_states' := lemma_PerformRightMoveThrough(arr, mover_tid, other_tid, other_tau, mover_step, [], [initial_state],
                                                   other_steps, other_states);
    assert [] + other_steps == other_steps;

    if !other_tau {
      forall i | 0 <= i < |other_states|
        ensures OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
      {
        assert PerformRightMoveTrigger(i);
      }
    }
  }

  lemma lemma_PerformRightMoveRemainingHelper1<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_steps_before:seq<LOneStep>,
    mover_states_before:seq<LState>,
    mover_steps_after:seq<LOneStep>,
    mover_states_after:seq<LState>,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>,
    other_states_mid:seq<LState>,
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == Armada_GetStateSequence(arr.l, mover_states_before[0], mover_steps_before)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_before[0], last(mover_states_before), mover_steps_before)
    requires forall step :: step in mover_steps_before ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_before ==> !arr.l.is_step_tau(step)

    requires |mover_states_after| > 0
    requires mover_states_after == Armada_GetStateSequence(arr.l, mover_states_after[0], mover_steps_after)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_steps_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_after[0], last(mover_states_after), mover_steps_after)
    requires forall step :: step in mover_steps_after ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_after ==> !arr.l.is_step_tau(step)

    requires |other_states| > 0
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    requires |mover_steps_before| > 0
    requires |other_states_mid| == |other_states|
    requires other_states_mid[0] == mover_states_before[|mover_steps_before|-1]
    requires other_states_mid == Armada_GetStateSequence(arr.l, other_states_mid[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states_mid[0], last(other_states_mid), other_steps)
    requires !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states_mid[i], other_states[i], other_tid)
  
    requires |other_states'| == |other_states_mid|
    requires other_states'[0] == all_but_last(mover_states_before)[0]
    requires other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    requires !other_tau ==> forall i :: 0 <= i < |other_states_mid| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states_mid[i], other_tid)
    requires |mover_states'| == |all_but_last(mover_states_before)| + |([last(other_states_mid)] + mover_states_after)| - 1
    requires mover_states'[0] == last(other_states')
    requires last(mover_states') == last(([last(other_states_mid)] + mover_states_after))
    requires mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0],
                                                      all_but_last(mover_steps_before) + ([last(mover_steps_before)] + mover_steps_after))
    requires Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'),
                                      all_but_last(mover_steps_before) + ([last(mover_steps_before)] + mover_steps_after))

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states_before[0]
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    ensures  |mover_states'| == |mover_states_before| + |mover_states_after| - 1
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(mover_states_after)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0], mover_steps_before + mover_steps_after)
    ensures  Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'), mover_steps_before + mover_steps_after)
  {
    calc {
      all_but_last(mover_steps_before) + ([last(mover_steps_before)] + mover_steps_after);
        { lemma_SequenceConcatenationAssociative(all_but_last(mover_steps_before), [last(mover_steps_before)], mover_steps_after); }
      (all_but_last(mover_steps_before) + [last(mover_steps_before)]) + mover_steps_after;
        { lemma_AllButLastPlusLastIsSeq(mover_steps_before); }
      mover_steps_before + mover_steps_after;
    }
    lemma_LastOfConcatenationIsLastOfLatter([last(other_states_mid)], mover_states_after);
  }

  lemma lemma_PerformRightMoveRemainingHelper2<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_steps_before:seq<LOneStep>,
    mover_states_before:seq<LState>,
    mover_steps_after:seq<LOneStep>,
    mover_states_after:seq<LState>,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>,
    other_states_mid:seq<LState>,
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == Armada_GetStateSequence(arr.l, mover_states_before[0], mover_steps_before)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_before[0], last(mover_states_before), mover_steps_before)
    requires forall step :: step in mover_steps_before ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_before ==> !arr.l.is_step_tau(step)

    requires |mover_states_after| > 0
    requires mover_states_after == Armada_GetStateSequence(arr.l, mover_states_after[0], mover_steps_after)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_steps_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_after[0], last(mover_states_after), mover_steps_after)
    requires forall step :: step in mover_steps_after ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_after ==> !arr.l.is_step_tau(step)

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    requires |mover_steps_before| > 0
    requires |other_states_mid| == |other_states|
    requires other_states_mid[0] == mover_states_before[|mover_steps_before|-1]
    requires other_states_mid == Armada_GetStateSequence(arr.l, other_states_mid[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states_mid[0], last(other_states_mid), other_steps)
    requires !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states_mid[i], other_states[i], other_tid)
  
    requires |other_states'| == |other_states_mid|
    requires other_states'[0] == all_but_last(mover_states_before)[0]
    requires other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    requires !other_tau ==> forall i :: 0 <= i < |other_states_mid| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states_mid[i], other_tid)
    requires |mover_states'| == |all_but_last(mover_states_before)| + |([last(other_states_mid)] + mover_states_after)| - 1
    requires mover_states'[0] == last(other_states')
    requires last(mover_states') == last(([last(other_states_mid)] + mover_states_after))
    requires mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0],
                                                     all_but_last(mover_steps_before) + ([last(mover_steps_before)] + mover_steps_after))
    requires Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'),
                                     all_but_last(mover_steps_before) + ([last(mover_steps_before)] + mover_steps_after))
    requires PerformRightMoveRemainingPredicate(arr, mover_tid, all_but_last(mover_states_before),
                                                [last(other_states_mid)] + mover_states_after, mover_states')

    ensures  PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states')
  {
    forall i | 0 <= i < |mover_states_before|
      ensures OKAndPCTypesMatch(arr, mover_states'[i], mover_states_before[i], mover_tid)
    {
      assert PerformRightMoveTrigger(i);
      if i < |all_but_last(mover_states_before)| {
        assert OKAndPCTypesMatch(arr, mover_states'[i], all_but_last(mover_states_before)[i], mover_tid);
        calc {
          arr.l.get_thread_pc(all_but_last(mover_states_before)[i], mover_tid);
          arr.l.get_thread_pc(mover_states_before[i], mover_tid);
        }
      }
      else {
        assert i == |all_but_last(mover_states_before)|;
        assert |all_but_last(mover_states_before)|-1 <= i < |mover_states'|;
        assert OKAndPCTypesMatch(arr, mover_states'[i], ([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1],
                            mover_tid);
        calc {
          arr.l.get_thread_pc(([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1], mover_tid);
          arr.l.get_thread_pc(([last(other_states_mid)] + mover_states_after)[1], mover_tid);
          arr.l.get_thread_pc(mover_states_after[0], mover_tid);
        }
        lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, last(mover_states_before), mover_states_after[0],
                                                                  other_steps, other_tau, other_tid, mover_tid);
        assert last(mover_states_before) == mover_states_before[i];
      }
    }

    forall i | |mover_states_before|-1 <= i < |mover_states'|
      ensures OKAndPCTypesMatch(arr, mover_states'[i], mover_states_after[i-|mover_states_before|+1], mover_tid)
    {
      assert PerformRightMoveTrigger(i);
      assert |all_but_last(mover_states_before)|-1 <= i < |mover_states'|;
      assert OKAndPCTypesMatch(arr, mover_states'[i], ([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1],
                          mover_tid);
      calc {
        arr.l.get_thread_pc(([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1], mover_tid);
          { lemma_IndexIntoConcatenation([last(other_states_mid)], mover_states_after, i-|all_but_last(mover_states_before)|+1); }
        arr.l.get_thread_pc(mover_states_after[(i-|all_but_last(mover_states_before)|+1)-|[last(other_states_mid)]|], mover_tid);
          { lemma_SpecificSequenceCaseC(mover_states_before, mover_states_after, other_states_mid, i); }
        arr.l.get_thread_pc(mover_states_after[i-|mover_states_before|+1], mover_tid);
      }
    }
  }

  lemma lemma_PerformRightMoveRemaining<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_steps_before:seq<LOneStep>,
    mover_states_before:seq<LState>,
    mover_steps_after:seq<LOneStep>,
    mover_states_after:seq<LState>,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == Armada_GetStateSequence(arr.l, mover_states_before[0], mover_steps_before)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_before[0], last(mover_states_before), mover_steps_before)
    requires forall step :: step in mover_steps_before ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_before ==> !arr.l.is_step_tau(step)

    requires |mover_states_after| > 0
    requires mover_states_after == Armada_GetStateSequence(arr.l, mover_states_after[0], mover_steps_after)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_steps_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states_after[0], last(mover_states_after), mover_steps_after)
    requires forall step :: step in mover_steps_after ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps_after ==> !arr.l.is_step_tau(step)

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states_before[0]
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  |mover_states'| == |mover_states_before| + |mover_states_after| - 1
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(mover_states_after)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0], mover_steps_before + mover_steps_after)
    ensures  Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'), mover_steps_before + mover_steps_after)
    ensures  PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states')

    decreases |mover_steps_before|
  {
    lemma_ExecutingStepSequenceOfOtherActorDoesntRemovePC(arr, other_states[0], last(other_states), other_steps, other_tau,
                                                          other_tid, mover_tid);
    lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, other_states[0], last(other_states), other_steps, other_tau,
                                                              other_tid, mover_tid);
    if |mover_steps_before| == 0 {
      mover_states' := mover_states_after;
      other_states' := other_states;
      assert mover_steps_before + mover_steps_after == mover_steps_after;
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states');
    }
    else {
      lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, mover_states_before[0], last(mover_states_before), mover_steps_before,
                                              mover_states_before, |mover_steps_before|-1);
      assert arr.inv(mover_states_before[|mover_steps_before|-1]);
      lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, mover_states_before[0], last(mover_states_before), mover_steps_before,
                                                  mover_states_before, |mover_steps_before|-1);
      assert arr.l.step_valid(mover_states_before[|mover_steps_before|-1], mover_steps_before[|mover_steps_before|-1]);
      assert arr.l.step_valid(mover_states_before[|mover_steps_before|-1], last(mover_steps_before));

      var other_states_mid :=
        lemma_PerformRightMoveOne(arr, mover_tid, other_tid, other_tau, last(mover_steps_before),
                                  mover_states_before[|mover_steps_before|-1], other_steps, other_states);

      lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, mover_states_before[0], last(mover_states_before), mover_steps_before,
                                                       mover_states_before);
      calc {
        other_states_mid[0];
        mover_states_before[|mover_steps_before|-1];
        last(all_but_last(mover_states_before));
      }

      var mover_states_after' := [last(other_states_mid)] + mover_states_after;
      var mover_steps_after' := [last(mover_steps_before)] + mover_steps_after;
      assert mover_states_after'[0] == last(other_states_mid);
      assert mover_states_after'[1..] == mover_states_after;
      assert mover_steps_after'[0] == last(mover_steps_before);
      assert mover_steps_after'[1..] == mover_steps_after;
      assert Armada_NextMultipleSteps(arr.l, mover_states_after'[0], last(mover_states_after'), mover_steps_after');

      mover_states', other_states' :=
        lemma_PerformRightMoveRemaining(arr, mover_tid, other_tid, other_tau, all_but_last(mover_steps_before),
                                        all_but_last(mover_states_before), [last(mover_steps_before)] + mover_steps_after,
                                        [last(other_states_mid)] + mover_states_after, other_steps, other_states_mid);
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, all_but_last(mover_states_before),
                                                [last(other_states_mid)] + mover_states_after, mover_states');
      lemma_PerformRightMoveRemainingHelper1(arr, mover_tid, other_tid, other_tau, mover_steps_before, mover_states_before,
                                             mover_steps_after, mover_states_after, other_steps, other_states, other_states_mid,
                                             mover_states', other_states');
      lemma_PerformRightMoveRemainingHelper2(arr, mover_tid, other_tid, other_tau, mover_steps_before, mover_states_before,
                                             mover_steps_after, mover_states_after, other_steps, other_states, other_states_mid,
                                             mover_states', other_states');
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states');
    }
  }

  lemma lemma_PerformRightMoveAll<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_steps:seq<LOneStep>,
    mover_states:seq<LState>,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states| > 0
    requires arr.inv(mover_states[0])
    requires arr.l.get_thread_pc(mover_states[0], mover_tid).Some?
    requires mover_states == Armada_GetStateSequence(arr.l, mover_states[0], mover_steps)
    requires forall s :: s in mover_states ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states[i], mover_tid).v)
    requires Armada_NextMultipleSteps(arr.l, mover_states[0], last(mover_states), mover_steps)
    requires forall step :: step in mover_steps ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps ==> !arr.l.is_step_tau(step)

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states)
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states[0]
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  |mover_states'| == |mover_states|
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(other_states)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0], mover_steps)
    ensures  Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'), mover_steps)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
  {
    lemma_ExecutingStepSequenceOfOtherActorDoesntRemovePC(arr, other_states[0], last(other_states), other_steps, other_tau,
                                                          other_tid, mover_tid);
    lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, other_states[0], last(other_states), other_steps, other_tau,
                                                              other_tid, mover_tid);

    mover_states', other_states' := lemma_PerformRightMoveRemaining(arr, mover_tid, other_tid, other_tau, mover_steps,
                                                                    mover_states, [], [last(other_states)], other_steps, other_states);
    assert mover_steps + [] == mover_steps;

    if !other_tau {
      forall i | 0 <= i < |other_states|
        ensures OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
      {
        assert PerformRightMoveTrigger(i);
      }
    }

    forall i | 0 <= i < |mover_states|
      ensures OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
    {
      assert PerformRightMoveTrigger(i);
    }
  }

  lemma lemma_PerformRightMove<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    step1:Armada_Multistep<LOneStep>,
    step2:Armada_Multistep<LOneStep>
    ) returns (
    s2':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires s1 in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    requires arr.l.state_ok(s3)
    requires Armada_NextMultistep(arr.l, s1, s2, step1.steps, step1.tid, step1.tau)
    requires Armada_NextMultistep(arr.l, s2, s3, step2.steps, step2.tid, step2.tau)
    requires !step1.tau
    requires step2.tau || step2.tid != step1.tid
    requires IsPhase1(arr, s2, step1.tid)
    ensures  Armada_NextMultistep(arr.l, s1, s2', step2.steps, step2.tid, step2.tau)
    ensures  Armada_NextMultistep(arr.l, s2', s3, step1.steps, step1.tid, step1.tau)
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, s1);
    assert arr.inv(s1);
    var mover_states := Armada_GetStateSequence(arr.l, s1, step1.steps);
    lemma_IfMultistepEndsInPhase1ThenEachStepDoes(arr, s1, s2, step1, mover_states);
    var other_states := Armada_GetStateSequence(arr.l, s2, step2.steps);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s1, s2, step1.steps, mover_states);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s2, s3, step2.steps, other_states);
    var mover_states', other_states' :=
      lemma_PerformRightMoveAll(arr, step1.tid, step2.tid, step2.tau, step1.steps, mover_states, step2.steps, other_states);
    s2' := last(other_states');
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s2', s3, step1.steps, mover_states');
  }

  //////////////////////////////////////////
  // LEFT-MOVER ENABLEMENT LEMMAS
  //////////////////////////////////////////

  lemma lemma_GenerateLeftMoverSequenceOfSubsteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    ) returns (
    states:seq<LState>,
    trace:seq<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.inv(s)
    requires arr.l.state_ok(s)
    requires IsPhase2(arr, s, tid)
    requires Armada_ThreadYielding(arr.l, s, tid)
    ensures  states == Armada_GetStateSequence(arr.l, s, trace)
    ensures  Armada_NextMultipleSteps(arr.l, s, last(states), trace)
    ensures  states[0] == s
    ensures  arr.l.state_ok(last(states)) ==> !IsPhase2(arr, last(states), tid) && Armada_ThreadYielding(arr.l, last(states), tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    ensures  forall step :: step in trace ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
  {
    states := [s];
    trace := [];

    while arr.l.state_ok(last(states)) && IsPhase2(arr, last(states), tid)
      invariant states == Armada_GetStateSequence(arr.l, s, trace)
      invariant Armada_NextMultipleSteps(arr.l, s, last(states), trace)
      invariant states[0] == s
      invariant arr.inv(last(states))
      invariant arr.l.state_ok(last(states)) && !Armada_ThreadYielding(arr.l, last(states), tid) ==> IsPhase2(arr, last(states), tid)
      invariant forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
      invariant forall step :: step in trace ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
      decreases arr.left_mover_generation_progress(last(states), tid)
    {
      var states_current := states;
      forall i | 0 <= i < |states_current|
        ensures IsPhase2(arr, states_current[i], tid)
      {
        if i < |states|-1 {
          assert IsPhase2(arr, states[i], tid);
        }
        else {
          assert states_current[i] == last(states);
        }
      }

      var s_current := last(states);
      var step := arr.generate_left_mover(s_current, tid);
      assert ArmadaReductionSpecModule.LeftMoversAlwaysEnabledConditions(arr, s_current, tid);
      assert arr.l.step_valid(s_current, step) && arr.l.step_to_thread(step) == tid && !arr.l.is_step_tau(step);
      var s_next := arr.l.step_next(s_current, step);
      assert 0 <= arr.left_mover_generation_progress(s_next, tid) < arr.left_mover_generation_progress(s_current, tid);
      lemma_ExtendingStateSequenceWorks(arr, s, s_current, trace, states, step, s_next);
      trace := trace + [step];
      states := states + [s_next];

      forall i | 0 <= i < |states|-1
        ensures IsPhase2(arr, states[i], tid)
      {
        assert states[i] == states_current[i];
      }
    }
  }

  lemma lemma_GenerateLeftMoverSequence<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    ) returns (
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.inv(s)
    requires arr.l.state_ok(s)
    requires IsPhase2(arr, s, tid)
    requires Armada_ThreadYielding(arr.l, s, tid)
    ensures  StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    ensures  states[0] == s
    ensures  arr.l.state_ok(last(states)) ==> !IsPhase2(arr, last(states), tid) && Armada_ThreadYielding(arr.l, last(states), tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    ensures  forall step :: step in trace ==> !step.tau && step.tid == tid
  {
    var rspec := GetRefinementViaReductionLSpec(arr);
    var single_states, single_trace := lemma_GenerateLeftMoverSequenceOfSubsteps(arr, s, tid);

    states := [s];
    trace := [];
    var partial_steps := [];
    var partial_states := [s];

    var pos := 0;

    assert !arr.l.state_ok(single_states[pos]) || Armada_ThreadYielding(arr.l, single_states[pos], tid) ==> |partial_steps| == 0;
    while pos < |single_trace|
      invariant 0 <= pos <= |single_trace|
      invariant |states| > 0
      invariant states[0] == s
      invariant StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
      invariant if pos < |single_trace| then
                  (forall state :: state in states ==> IsPhase2(arr, state, tid))
                else
                  (forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid))
      invariant forall step :: step in trace ==> !step.tau && step.tid == tid
      invariant !arr.l.state_ok(last(states)) || Armada_ThreadYielding(arr.l, last(states), tid)
      invariant !arr.l.state_ok(single_states[pos]) || Armada_ThreadYielding(arr.l, single_states[pos], tid) ==> |partial_steps| == 0
      invariant Armada_NextMultipleSteps(arr.l, last(states), single_states[pos], partial_steps)
      invariant partial_states == Armada_GetStateSequence(arr.l, last(states), partial_steps)
      invariant forall i :: 0 < i < |partial_states| ==> !Armada_ThreadYielding(arr.l, partial_states[i], tid)
      invariant forall step :: step in partial_steps ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
      decreases |single_trace| - pos
    {
      var s_current := single_states[pos];
      var s_next := single_states[pos+1];
      var next_step := single_trace[pos];

      lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, single_states[0], last(single_states), single_trace, single_states, pos);
      assert arr.l.step_valid(s_current, next_step);
      assert s_next == arr.l.step_next(s_current, next_step);

      lemma_ExtendingStateSequenceWorks(arr, last(states), s_current, partial_steps, partial_states, next_step, s_next);

      var upper := |partial_states|;
      assert forall i :: 0 < i < upper ==> !Armada_ThreadYielding(arr.l, partial_states[i], tid);
      partial_steps := partial_steps + [next_step];
      partial_states := partial_states + [s_next];
      assert upper == |partial_steps|;
      assert forall i :: 0 < i < |partial_steps| ==> !Armada_ThreadYielding(arr.l, partial_states[i], tid);

      if !arr.l.state_ok(s_next) || Armada_ThreadYielding(arr.l, s_next, tid) {
        var multistep := Armada_Multistep(partial_steps, tid, false);

        assert Armada_NextMultistep(arr.l, last(states), s_next, multistep.steps, multistep.tid, multistep.tau);
        assert ActionTuple(last(states), s_next, multistep) in rspec.next;

        var states_next := states + [s_next];
        var trace_next := trace + [multistep];

        forall i | 0 <= i < |trace_next|
          ensures ActionTuple(states_next[i], states_next[i+1], trace_next[i]) in rspec.next
        {
          if i < |trace| {
            assert ActionTuple(states[i], states[i+1], trace[i]) in rspec.next;
            assert states_next[i] == states[i];
            assert states_next[i+1] == states[i+1];
            assert trace_next[i] == trace[i];
          }
          else {
            assert i == |trace| == |states|-1;
            assert states_next[i] == states[i] == last(states);
            assert states_next[i+1] == s_next;
            assert trace_next[i] == multistep;
          }
        }

        states := states_next;
        trace := trace_next;
        partial_steps := [];
        partial_states := [s_next];
           
        assert StateNextSeq(states, trace, rspec.next);
      }
      pos := pos + 1;
      assert Armada_NextMultipleSteps(arr.l, last(states), single_states[pos], partial_steps);
    }

    assert |partial_steps| == 0;
    assert pos == |single_trace|;
    assert last(states) == single_states[pos] == last(single_states);
  }

  lemma lemma_LeftMoversAlwaysEnabled<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoversAlwaysEnabled(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, actor |
      && s in AnnotatedReachables(rr.lspec)
      && rr.phase2(s, actor)
      && !rr.crashed(s)
      ensures exists states, trace ::
                 && StateNextSeq(states, trace, rr.lspec.next)
                 && states[0] == s
                 && (!arr.l.state_ok(last(states)) || !rr.phase2(last(states), actor))
                 && (forall i :: 0 <= i < |states|-1 ==> rr.phase2(states[i], actor))
                 && (forall step :: step in trace ==> rr.idmap(step) == actor)
    {
      lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, s);
      assert actor.Some?;
      lemma_StateAmongAnnotatedReachablesHasThreadYielding(arr, s, actor.v);
      var states, trace := lemma_GenerateLeftMoverSequence(arr, s, actor.v);
    }
  }

  ////////////////////////////////////////////
  // LEMMAS ABOUT LIFTING ACTION SEQUENCES
  ////////////////////////////////////////////

  function CombineMultisteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    trace:seq<Armada_Multistep<LOneStep>>
    ) : seq<LOneStep>
  {
    if |trace| == 0 then [] else trace[0].steps + CombineMultisteps(arr, trace[1..])
  }

  lemma lemma_CombineMultistepsEffectOnGetStateSequence<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    tid:Armada_ThreadHandle
    )
    requires ValidArmadaReductionRequest(arr)
    requires |trace| > 0
    requires |states| == |trace| + 1
    requires forall i :: 0 <= i < |trace| ==> Armada_NextMultipleSteps(arr.l, states[i], states[i+1], trace[i].steps)
    ensures  Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace)) ==
             Armada_GetStateSequence(arr.l, states[0], trace[0].steps) +
             Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]))[1..]
    decreases |trace[0].steps|
  {
    var pos := 0;
    assert Armada_NextMultipleSteps(arr.l, states[pos], states[pos+1], trace[pos].steps);
    var astep := trace[0];

    if |astep.steps| == 0 {
      calc {
        Armada_GetStateSequence(arr.l, states[0], trace[0].steps) +
          Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]))[1..];
         { assert trace[0].steps == [];
           assert Armada_GetStateSequence(arr.l, states[0], trace[0].steps) == [states[0]]; }
        [states[0]] + Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]))[1..];
          { assert states[1] == states[0]; }
        [states[0]] + Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]))[1..];
          { assert Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]))[0] == states[0]; }
        Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]));
          { assert CombineMultisteps(arr, trace) == CombineMultisteps(arr, trace[1..]); }
        Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace));
      }
    }
    else {
      var s_mid := arr.l.step_next(states[0], astep.steps[0]);
      var new_trace0 := astep.(steps := astep.steps[1..]);
      var states' := states[0 := s_mid];
      var trace' := trace[0 := new_trace0];

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in GetRefinementViaReductionLSpec(arr).next} | 0 <= i < |trace'|
        ensures Armada_NextMultipleSteps(arr.l, states'[i], states'[i+1], trace'[i].steps);
      {
        assert Armada_NextMultipleSteps(arr.l, states[i], states[i+1], trace[i].steps);
        if i == 0 {
          assert states'[i] == s_mid;
          assert states'[i+1] == states[1];
          assert trace'[i] == new_trace0;
        }
        else {
          assert states'[i] == states[i];
          assert states'[i+1] == states[i+1];
          assert trace'[i] == trace[i];
        }
      }

      lemma_CombineMultistepsEffectOnGetStateSequence(arr, states', trace', tid);
      assert Armada_GetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace')) ==
             Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
             Armada_GetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]))[1..];

      calc {
        CombineMultisteps(arr, trace');
        trace'[0].steps + CombineMultisteps(arr, trace'[1..]);
        new_trace0.steps + CombineMultisteps(arr, trace'[1..]);
        astep.steps[1..] + CombineMultisteps(arr, trace[1..]);
          { lemma_DroppingHeadOfConcatenation(astep.steps, CombineMultisteps(arr, trace[1..])); }
        (astep.steps + CombineMultisteps(arr, trace[1..]))[1..];
        CombineMultisteps(arr, trace)[1..];
      }

      calc {
        Armada_GetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace));
        [states[0]] + Armada_GetStateSequence(arr.l, s_mid, CombineMultisteps(arr, trace)[1..]);
        [states[0]] + Armada_GetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace)[1..]);
          { assert CombineMultisteps(arr, trace') == CombineMultisteps(arr, trace)[1..]; }
        [states[0]] + Armada_GetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace'));
          { assert Armada_GetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace')) ==
                   Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
                   Armada_GetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]))[1..]; }
        [states[0]] + (Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
                       Armada_GetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]))[1..]);
          { lemma_SequenceConcatenationAssociative(
              [states[0]],
              Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps),
              Armada_GetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]))[1..]); }
        [states[0]] + Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
             Armada_GetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]))[1..];
        [states[0]] + Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
             Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace'[1..]))[1..];
        [states[0]] + Armada_GetStateSequence(arr.l, states'[0], trace'[0].steps) +
             Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]))[1..];
        Armada_GetStateSequence(arr.l, states[0], trace[0].steps) +
          Armada_GetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]))[1..];

      }
    }
  }

  lemma lemma_CombineMultistepsCreatesValidHStepHelper<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    astep:Armada_Multistep<LOneStep>,
    states:seq<LState>,
    i:int
    )
    requires states == Armada_GetStateSequence(arr.l, s, astep.steps)
    requires !astep.tau
    requires Armada_NextMultistep(arr.l, s, s', astep.steps, astep.tid, astep.tau)
    requires 0 < i < |states|
    requires i == |states|-1 ==> arr.l.state_ok(s')
    requires i == |states|-1 ==> IsPhase1(arr, s', astep.tid) || IsPhase2(arr, s', astep.tid)
    ensures  IsNonyieldingOrInPhase(arr, states[i], astep.tid)
  {
    var pc := arr.l.get_thread_pc(states[i], astep.tid);
    if i < |states|-1 {
      assert pc.Some? && arr.l.is_pc_nonyielding(pc.v);
    }
    else {
      assert i == |states|-1;
      assert states[i] == last(states);
      lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', astep.steps, states);
      assert last(states) == s';
      assert IsPhase1(arr, states[i], astep.tid) || IsPhase2(arr, states[i], astep.tid);
      assert pc.Some? && (arr.is_phase1(pc.v) || arr.is_phase2(pc.v));
    }
    assert IsNonyieldingOrInPhase(arr, states[i], astep.tid);
  }

  lemma lemma_CombineMultistepsCreatesValidHStep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    tid:Armada_ThreadHandle,
    combined:seq<LOneStep>,
    all_states:seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> !step.tau && step.tid == tid
    requires combined == CombineMultisteps(arr, trace)
    requires forall i :: 0 < i < |trace| ==> arr.l.state_ok(states[i])
    requires forall i :: 0 < i < |trace| ==> IsPhase1(arr, states[i], tid) || IsPhase2(arr, states[i], tid)
    requires all_states == Armada_GetStateSequence(arr.l, states[0], combined)
    ensures  forall i :: 0 < i < |combined| ==> IsNonyieldingOrInPhase(arr, all_states[i], tid)
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    if |trace| > 0 {
      forall i | 0 <= i < |trace|
        ensures Armada_NextMultipleSteps(arr.l, states[i], states[i+1], trace[i].steps)
      {
        assert ActionTuple(states[i], states[i+1], trace[i]) in rspec.next;
      }
      
      lemma_CombineMultistepsEffectOnGetStateSequence(arr, states, trace, tid);

      var states' := states[1..];
      var trace' := trace[1..];
      var combined' := CombineMultisteps(arr, trace');
      var all_states' := Armada_GetStateSequence(arr.l, states'[0], combined');

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next} | 0 <= i < |trace'|
        ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next
      {
        var next := i+1;
        assert ActionTuple(states[next], states[next+1], trace[next]) in rspec.next;
      }

      lemma_CombineMultistepsCreatesValidHStep(arr, states[1..], trace[1..], tid, combined', all_states');

      var astep := trace[0];
      assert astep.tid == tid;
      var first_states := Armada_GetStateSequence(arr.l, states[0], astep.steps);
      assert all_states == first_states + all_states'[1..];
      forall i | 0 < i < |combined|
        ensures IsNonyieldingOrInPhase(arr, all_states[i], tid)
      {
        if i < |first_states| {
          var zero := 0;
          assert ActionTuple(states[zero], states[zero+1], trace[zero]) in rspec.next;
          assert Armada_NextMultistep(arr.l, states[zero], states[zero+1], astep.steps, astep.tid, astep.tau);
          var one := zero+1;
          lemma_ArmadaNextMultipleStepsLastElement(arr.l, states[zero], states[zero+1], astep.steps, first_states);
          assert all_states[i] == first_states[i];
          if i == |first_states|-1 {
            assert |combined| > |combined'|;
            assert |states| > 2;
            assert 0 < one < |trace|;
            assert arr.l.state_ok(states[one]);
            assert IsPhase1(arr, states[one], tid) || IsPhase2(arr, states[one], tid);
          }
          lemma_CombineMultistepsCreatesValidHStepHelper(arr, states[zero], states[one], astep, first_states, i);
          assert IsNonyieldingOrInPhase(arr, all_states[i], tid);
        }
        else {
          calc {
            all_states[i];
            (first_states + all_states'[1..])[i];
              { lemma_IndexIntoConcatenation(first_states, all_states'[1..], i); }
            all_states'[1..][i - |first_states|];
              { lemma_IndexIntoDrop(all_states', 1, i - |first_states|); }
            all_states'[1 + i - |first_states|];
          }
          var pos := 1 + i - |first_states|;
          assert 0 < pos < |combined'|;
          assert IsNonyieldingOrInPhase(arr, all_states'[pos], tid);
          assert IsNonyieldingOrInPhase(arr, all_states[i], tid);
        }
      }
    }
  }

  lemma lemma_CombineMultistepsPreservesStateNextSeq<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    tid:Armada_ThreadHandle,
    combined:seq<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> !step.tau && step.tid == tid
    requires combined == CombineMultisteps(arr, trace)
    ensures  Armada_NextMultipleSteps(arr.l, states[0], last(states), combined)
    ensures  forall step :: step in combined ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    if |trace| > 0 {
      var pos := 0;
      assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rspec.next;
      var astep := trace[0];
      assert Armada_NextMultistep(arr.l, states[pos], states[pos+1], astep.steps, astep.tid, astep.tau);

      var states' := states[1..];
      var trace' := trace[1..];

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next} | 0 <= i < |trace'|
        ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next
      {
        var next := i+1;
        assert ActionTuple(states[next], states[next+1], trace[next]) in rspec.next;
        assert states'[i] == states[next];
        assert states'[i+1] == states[next+1];
        assert trace'[i] == trace[next];
      }

      var combined' := CombineMultisteps(arr, trace');
      lemma_CombineMultistepsPreservesStateNextSeq(arr, states', trace', tid, combined');
      lemma_ArmadaNextMultipleStepsTransitive(arr, states[0], states[1], last(states), astep.steps, combined');
    }
  }

  lemma lemma_LiftActionSequenceCaseMultipleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hstep:Armada_Multistep<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> rr.idmap(step) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 0 < i < |trace| ==> !rr.crashed(states[i])
    requires forall i :: 0 < i < |trace| ==> var s := states[i]; rr.phase1(s, actor) || rr.phase2(s, actor)
    requires |trace| > 1
    requires actor.Some?
    ensures  ActionTuple(states[0], last(states), hstep) in rr.hspec.next
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    var pos := 0;
    assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rspec.next;
    assert rr.idmap(trace[pos]) == actor;
    assert !IsNonyieldingOrInPhase(arr, states[0], actor.v);

    pos := |trace|-1;
    assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rspec.next;
    assert rr.idmap(trace[pos]) == actor;
    assert !IsNonyieldingOrInPhase(arr, last(states), actor.v);

    var steps := CombineMultisteps(arr, trace);
    hstep := Armada_Multistep(steps, actor.v, false);
    lemma_CombineMultistepsPreservesStateNextSeq(arr, states, trace, actor.v, steps);

    var all_states := Armada_GetStateSequence(arr.l, states[0], steps);
    forall i | 1 <= i < |states|-1
      ensures IsPhase1(arr, states[i], actor.v) || IsPhase2(arr, states[i], actor.v)
    {
      assert rr.phase1(states[i], actor) || rr.phase2(states[i], actor);
    }

    lemma_CombineMultistepsCreatesValidHStep(arr, states, trace, actor.v, steps, all_states);
    assert GenericNextReduced(arr, states[0], last(states), steps, actor.v, false);
  }

  lemma lemma_LiftActionSequenceCaseOneStep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hstep:Armada_Multistep<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> rr.idmap(step) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 1 <= i < |states|-1 ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    requires |trace| == 1
    ensures  ActionTuple(states[0], last(states), hstep) in rr.hspec.next
  {
    var s := states[0];
    var s' := last(states);
    hstep := trace[0];
    var pos := 0;
    assert ActionTuple(states[pos], states[pos+1], trace[pos]) in GetRefinementViaReductionLSpec(arr).next;
    assert Armada_NextMultistep(arr.l, states[0], states[0+1], hstep.steps, hstep.tid, hstep.tau);
    assert rr.idmap(trace[0]) == actor;
    assert !hstep.tau ==> actor == Some(hstep.tid);
    assert GenericNextReduced(arr, s, s', hstep.steps, hstep.tid, hstep.tau);
  }

  lemma lemma_LiftActionSequenceCaseTau<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hstep:Armada_Multistep<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> rr.idmap(step) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 1 <= i < |states|-1 ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    requires |trace| > 1
    requires actor.None?
    ensures  ActionTuple(states[0], last(states), hstep) in rr.hspec.next
  {
    var pos := 1;
    assert 1 <= pos < |states|-1;
    assert rr.phase1(states[pos], actor) || rr.phase2(states[pos], actor);
    assert false;
  }

  lemma lemma_LiftActionSequence<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LOneStep>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hstep:Armada_Multistep<LOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall step :: step in trace ==> rr.idmap(step) == actor
    requires |states| > 1
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 0 < i < |trace| ==> !rr.crashed(states[i])
    requires forall i :: 0 < i < |trace| ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    ensures  ActionTuple(states[0], last(states), hstep) in rr.hspec.next
  {
    if |trace| == 1 {
      hstep := lemma_LiftActionSequenceCaseOneStep(arr, rr, states, trace, actor);
    }
    else if actor.None? {
      hstep := lemma_LiftActionSequenceCaseTau(arr, rr, states, trace, actor);
    }
    else {
      hstep := lemma_LiftActionSequenceCaseMultipleSteps(arr, rr, states, trace, actor);
    }
  }

  lemma lemma_ActionSequencesLiftable<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  ActionSequencesLiftable(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall states, trace, actor
      {:trigger RefinementViaReductionSpecModule.ActionSequencesLiftableConditions(rr, states, trace, actor)}
      | RefinementViaReductionSpecModule.ActionSequencesLiftableConditions(rr, states, trace, actor)
      ensures exists hstep :: ActionTuple(states[0], last(states), hstep) in rr.hspec.next
    {
      var hstep := lemma_LiftActionSequence(arr, rr, states, trace, actor);
    }
  }

  //////////////////////////////////////////////////////////////////////////
  // LEMMAS PROVING VALIDITY OF GENERATED CRASHING REDUCTION REQUEST
  //////////////////////////////////////////////////////////////////////////

  lemma lemma_IfArmadaReductionRequestValidThenCrashingCantGoDirectlyFromPhase2ToPhase1<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  CantGoDirectlyFromPhase2ToPhase1(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', step | ActionTuple(s, s', step) in rr.lspec.next && rr.phase2(s, rr.idmap(step))
      ensures !rr.phase1(s', rr.idmap(step))
    {
      assert Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau);
      var tid := step.tid;
      if |step.steps| > 0 {
        var states := Armada_GetStateSequence(arr.l, s, step.steps);
        var pos := 0;
        while pos < |step.steps|-1
          invariant 0 <= pos < |step.steps|
          invariant IsPhase2(arr, states[pos], tid)
          decreases |step.steps| - pos
        {
          lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, pos);
          assert arr.l.step_valid(states[pos], step.steps[pos]);
          assert states[pos+1] == arr.l.step_next(states[pos], step.steps[pos]);
          var next_pos := pos+1;
          var pc := arr.l.get_thread_pc(states[next_pos], tid).v;
          assert arr.l.is_pc_nonyielding(pc);
          pos := pos+1;
        }
        lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, pos);
        lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
      }
    }
  }

  lemma lemma_IfArmadaReductionRequestValidThenCrashingPhaseUnaffectedByOtherActorsHelper<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  var rr := GetRefinementViaReductionRequest(arr);
             forall s, s', step, actor :: ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor
                ==> && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
                    && (rr.phase2(s, actor) <==> rr.phase2(s', actor))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', step, actor | ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor
      ensures rr.phase1(s, actor) <==> rr.phase1(s', actor)
      ensures rr.phase2(s, actor) <==> rr.phase2(s', actor)
    {
      if actor.Some? {
        assert Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau);
        var tid := actor.v;
        var states := Armada_GetStateSequence(arr.l, s, step.steps);
        var pc := arr.l.get_thread_pc(s, tid);
        var phase1 := pc.Some? && arr.is_phase1(pc.v);
        var phase2 := pc.Some? && arr.is_phase2(pc.v);
        var pos := 0;
        while pos < |step.steps|
          invariant 0 <= pos <= |step.steps|
          invariant phase1 <==> IsPhase1(arr, states[pos], tid)
          invariant phase2 <==> IsPhase2(arr, states[pos], tid)
          decreases |step.steps| - pos
        {
          lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, pos);
          assert arr.l.step_valid(states[pos], step.steps[pos]);
          assert states[pos+1] == arr.l.step_next(states[pos], step.steps[pos]);
          var pc1 := arr.l.get_thread_pc(states[pos], tid);
          var pc2 := arr.l.get_thread_pc(states[pos+1], tid);
          assert pc1 != pc2 ==> pc1.None? && !arr.is_phase1(pc2.v) && !arr.is_phase2(pc2.v);
          var next_pos := pos+1;
          pos := pos+1;
        }
        lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
      }
    }
  }

  lemma lemma_IfArmadaReductionRequestValidThenCrashingPhaseUnaffectedByOtherActors<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.PhaseUnaffectedByOtherActors(GetRefinementViaReductionRequest(arr))
  {
    lemma_IfArmadaReductionRequestValidThenCrashingPhaseUnaffectedByOtherActorsHelper(arr);
    var rr := GetRefinementViaReductionRequest(arr);

    forall s, s', step, actor | ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor
      ensures rr.phase1(s, actor) <==> rr.phase1(s', actor)
    {
      assert && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
             && (rr.phase2(s, actor) <==> rr.phase2(s', actor));
    }

    forall s, s', step, actor | ActionTuple(s, s', step) in rr.lspec.next && rr.idmap(step) != actor
      ensures rr.phase2(s, actor) <==> rr.phase2(s', actor)
    {
      assert && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
             && (rr.phase2(s, actor) <==> rr.phase2(s', actor));
    }
  }

  lemma lemma_PostCrashStepsStutter<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  PostCrashStepsStutter(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', step | rr.crashed(s) && ActionTuple(s, s', step) in SpecFunctionsToSpec(arr.l).next
      ensures s' == s
    {
      assert Armada_NextMultipleSteps(arr.l, s, s', step.steps);
      if |step.steps| > 0 {
        assert arr.l.step_valid(s, step.steps[0]);
        assert !arr.l.state_ok(s);
        assert !arr.l.step_valid(s, step.steps[0]);
        assert false;
      }
      else {
        assert s' == s;
      }
    }
  }

  lemma lemma_RightMoversPreserveStateRefinement<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoversPreserveStateRefinement(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', step |
      && ActionTuple(s, s', step) in rr.lspec.next
      && rr.phase1(s', rr.idmap(step))
      && arr.l.state_ok(s')
      ensures RefinementPair(s', s) in rr.relation
    {
      assert !step.tau;
      assert Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau);
      var tid := step.tid;
      var states := Armada_GetStateSequence(arr.l, s, step.steps);
      lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
      var pos := |step.steps|;
      while pos > 0
        invariant 0 <= pos <= |step.steps|
        invariant pos > 0 ==> IsPhase1(arr, states[pos], tid)
        invariant arr.l.state_ok(states[pos])
        invariant RefinementPair(s', states[pos]) in rr.relation
        decreases pos
      {
        var prev_pos := pos-1;
        lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, prev_pos);
        assert arr.l.step_valid(states[prev_pos], step.steps[prev_pos]);
        assert states[prev_pos+1] == arr.l.step_next(states[prev_pos], step.steps[prev_pos]);
        assert RefinementPair(states[prev_pos+1], states[prev_pos]) in arr.self_relation;
        assert RefinementPair(s', states[pos]) in arr.self_relation;
        assert RefinementPair(s', states[prev_pos]) in arr.self_relation;
        if prev_pos > 0 {
          var pc := arr.l.get_thread_pc(states[prev_pos], tid);
          assert pc.Some? && arr.l.is_pc_nonyielding(pc.v);
          assert !arr.is_phase2(pc.v);
          assert arr.is_phase1(pc.v);
        }
        pos := pos-1;
      }
    }
  }

  lemma lemma_LeftMoversPreserveStateRefinement<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoversPreserveStateRefinement(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', step |
      && ActionTuple(s, s', step) in rr.lspec.next
      && rr.phase2(s, rr.idmap(step))
      ensures RefinementPair(s, s') in rr.relation
    {
      assert !step.tau;
      assert Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau);
      var tid := step.tid;
      var states := Armada_GetStateSequence(arr.l, s, step.steps);
      var pos := 0;
      while pos < |step.steps|
        invariant 0 <= pos <= |step.steps|
        invariant pos < |step.steps| ==> IsPhase2(arr, states[pos], tid)
        invariant RefinementPair(s, states[pos]) in rr.relation
        decreases |step.steps| - pos
      {
        lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, pos);
        assert arr.l.step_valid(states[pos], step.steps[pos]);
        assert states[pos+1] == arr.l.step_next(states[pos], step.steps[pos]);
        assert RefinementPair(states[pos], states[pos+1]) in arr.self_relation;
        pos := pos+1;
      }
      lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
    }
  }

  lemma lemma_StateAmongAnnotatedReachablesSatisfiesInv<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires s in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    ensures  arr.inv(s)
  {
    var rspec := GetRefinementViaReductionLSpec(arr);
    reveal_AnnotatedReachables();
    var ab :| AnnotatedBehaviorSatisfiesSpec(ab, rspec) && last(ab.states) == s;
    var pos := 0;
    while pos < |ab.states|-1
      invariant 0 <= pos < |ab.states|
      invariant arr.inv(ab.states[pos])
      decreases |ab.states|-pos
    {
      var subpos := 0;
      var s := ab.states[pos];
      var s' := ab.states[pos+1];
      var step := ab.trace[pos];
      assert ActionTuple(ab.states[pos], ab.states[pos+1], ab.trace[pos]) in rspec.next;
      assert Armada_NextMultistep(arr.l, s, s', step.steps, step.tid, step.tau);
      var states := Armada_GetStateSequence(arr.l, s, step.steps);
      while subpos < |step.steps|
        invariant 0 <= subpos <= |step.steps|
        invariant arr.inv(states[subpos])
        decreases |step.steps|-subpos
      {
        lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, s, s', step.steps, states, subpos);
        subpos := subpos + 1;
      }
      lemma_ArmadaNextMultipleStepsLastElement(arr.l, s, s', step.steps, states);
      pos := pos+1;
    }
  }

  lemma lemma_MoveLeftMoverLeftOneAsSingleStep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    mover_step:LOneStep,
    other_step:LOneStep
    ) returns (
    state_after_mover_step:LState
    )
    requires ValidArmadaReductionRequest(arr)

    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, other_step)
    requires state_after_other_step == arr.l.step_next(initial_state, other_step)
    requires arr.l.step_to_thread(other_step) == other_tid
    requires arr.l.is_step_tau(other_step) == other_tau

    requires arr.l.step_valid(state_after_other_step, mover_step)
    requires state_after_both_steps == arr.l.step_next(state_after_other_step, mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(state_after_both_steps)

    requires IsPhase2(arr, state_after_other_step, mover_tid)

    ensures  arr.l.step_valid(initial_state, mover_step)
    ensures  state_after_mover_step == arr.l.step_next(initial_state, mover_step)
    ensures  arr.l.step_valid(state_after_mover_step, other_step)
    ensures  state_after_both_steps == arr.l.step_next(state_after_mover_step, other_step)
    ensures  OKAndPCTypesMatch(arr, state_after_mover_step, state_after_both_steps, mover_tid)
    ensures  !other_tau ==> OKAndPCTypesMatch(arr, state_after_other_step, state_after_both_steps, other_tid)
  {
    state_after_mover_step := arr.l.step_next(initial_state, mover_step);
    assert ArmadaReductionSpecModule.LeftMoversCommuteConditions(arr, initial_state, other_step, mover_step);

    if !other_tau {
      lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, state_after_other_step, state_after_both_steps, mover_step, other_tid);
    }
    lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, state_after_mover_step, state_after_both_steps, other_step, mover_tid);
  }

  lemma {:timeLimitMultiplier 2} lemma_MoveLeftMoverLeftAsSingleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    post_mover_state:LState,
    mover_step:LOneStep,
    other_states:seq<LState>,
    other_steps:seq<LOneStep>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    requires arr.l.step_valid(last(other_states), mover_step)
    requires post_mover_state == arr.l.step_next(last(other_states), mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !arr.l.is_step_tau(mover_step)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(post_mover_state)

    requires IsPhase2(arr, last(other_states), mover_tid)

    ensures  |other_states'| == |other_states|
    ensures  last(other_states') == post_mover_state
    ensures  arr.l.step_valid(other_states[0], mover_step)
    ensures  other_states'[0] == arr.l.step_next(other_states[0], mover_step)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  OKAndPCTypesMatch(arr, other_states[0], last(other_states), mover_tid)
    ensures  OKAndPCTypesMatch(arr, other_states'[0], post_mover_state, mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    decreases |other_states|
  {
    if |other_steps| == 0 {
      other_states' := [post_mover_state];
      return;
    }

    var pos := |other_states|-2;
    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, other_states[0], last(other_states), other_steps, other_states, pos);
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, other_states[0], last(other_states), other_steps, other_states, pos);
    var state_after_mover_step :=
      lemma_MoveLeftMoverLeftOneAsSingleStep(
        arr,  mover_tid, other_tid, other_tau, other_states[pos], other_states[pos+1], post_mover_state, mover_step, other_steps[pos]);

    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, other_states[0], last(other_states), other_steps, other_states);
    assert last(all_but_last(other_states)) == other_states[pos];
    var other_states_next :=
      lemma_MoveLeftMoverLeftAsSingleSteps(
        arr, mover_tid, other_tid, other_tau, state_after_mover_step, mover_step,
        all_but_last(other_states), all_but_last(other_steps));
    other_states' := other_states_next + [post_mover_state];

    lemma_ExtendingStateSequenceWorks(arr, other_states_next[0], last(other_states_next), all_but_last(other_steps), other_states_next,
                                      last(other_steps), post_mover_state);
    lemma_AllButLastPlusLastIsSeq(other_steps);

    if !other_tau {
      forall i | 0 <= i < |other_states|
        ensures OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
      {
        if i < |other_states_next| {
          assert other_states'[i] == other_states_next[i];
          assert OKAndPCTypesMatch(arr, other_states_next[i], other_states[i], other_tid);
        }
        else {
          assert |other_states_next| == |all_but_last(other_states)| == |other_states|-1 == i;
          assert other_states'[i] == post_mover_state;
          assert other_states[i] == last(other_states);
          lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, last(other_states), post_mover_state, mover_step, other_tid);
          assert OKAndPCTypesMatch(arr, post_mover_state, last(other_states), other_tid);
        }
      }
    }
  }

  lemma lemma_MoveLeftMoversLeftAsSingleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_states:seq<LState>,
    mover_steps:seq<LOneStep>,
    other_states:seq<LState>,
    other_steps:seq<LOneStep>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    requires |mover_states| > 1
    requires last(other_states) == mover_states[0]
    requires Armada_NextMultipleSteps(arr.l, mover_states[0], last(mover_states), mover_steps)
    requires mover_states == Armada_GetStateSequence(arr.l, mover_states[0], mover_steps)
    requires forall step :: step in mover_steps ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps ==> !arr.l.is_step_tau(step)

    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(last(mover_states))

    ensures  |mover_states'| == |mover_states|
    ensures  |other_states'| == |other_states|
    ensures  mover_states'[0] == other_states[0]
    ensures  last(mover_states') == other_states'[0]
    ensures  last(other_states') == last(mover_states)
    ensures  Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'), mover_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0], mover_steps)
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    decreases |mover_states|
  {
    assert |mover_steps| > 0;
    var pos := 0;
    assert mover_states[pos+1] == arr.l.step_next(mover_states[pos], mover_steps[pos]);
    var other_states_mid :=
      lemma_MoveLeftMoverLeftAsSingleSteps(
        arr, mover_tid, other_tid, other_tau, mover_states[pos+1], mover_steps[pos], other_states, other_steps);
    if |mover_steps| == 1 {
      mover_states' := [other_states[0], other_states_mid[0]];
      other_states' := other_states_mid;
    }
    else {
      var mover_states_next;
      lemma_LastOfDropIsLast(mover_states, 1);
      mover_states_next, other_states' :=
        lemma_MoveLeftMoversLeftAsSingleSteps(
          arr, mover_tid, other_tid, other_tau, mover_states[1..], mover_steps[1..], other_states_mid, other_steps);
      mover_states' := [other_states[0]] + mover_states_next;
      lemma_LastOfConcatenationIsLastOfLatter([other_states[0]], mover_states_next);
      calc {
        last(other_states');
        last(mover_states[1..]);
        last(mover_states);
      }
      forall i | 0 <= i < |mover_states|
        ensures OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
      {
        if i > 0 {
          var j := i-1;
          assert OKAndPCTypesMatch(arr, mover_states_next[j], mover_states[1..][j], mover_tid);
          assert mover_states'[i] == mover_states_next[j];
          assert mover_states[i] == mover_states[1..][j];
        }
        else {
          assert mover_states'[i] == other_states[0];
          assert mover_states[i] == mover_states[0];
        }
      }
      if !other_tau {
        forall i | 0 <= i < |other_states|
          ensures OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
        {
          assert OKAndPCTypesMatch(arr, other_states'[i], other_states_mid[i], other_tid);
          assert OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid);
        }
      }
    }
  }

  lemma lemma_PerformLeftMoveAll<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_steps:seq<LOneStep>,
    mover_states:seq<LState>,
    other_steps:seq<LOneStep>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )

    requires ValidArmadaReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires Armada_NextMultipleSteps(arr.l, other_states[0], last(other_states), other_steps)
    requires other_states == Armada_GetStateSequence(arr.l, other_states[0], other_steps)
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau

    requires |mover_states| > 0
    requires last(other_states) == mover_states[0]
    requires Armada_NextMultipleSteps(arr.l, mover_states[0], last(mover_states), mover_steps)
    requires mover_states == Armada_GetStateSequence(arr.l, mover_states[0], mover_steps)
    requires forall step :: step in mover_steps ==> arr.l.step_to_thread(step) == mover_tid
    requires forall step :: step in mover_steps ==> !arr.l.is_step_tau(step)

    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(last(mover_states))

    ensures  |mover_states'| == |mover_states|
    ensures  |other_states'| == |other_states|
    ensures  mover_states'[0] == other_states[0]
    ensures  last(mover_states') == other_states'[0]
    ensures  last(other_states') == last(mover_states)
    ensures  Armada_NextMultipleSteps(arr.l, mover_states'[0], last(mover_states'), mover_steps)
    ensures  Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), other_steps)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, mover_states'[0], mover_steps)
    ensures  other_states' == Armada_GetStateSequence(arr.l, other_states'[0], other_steps)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
  {
    if |mover_states| == 1 {
     lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, other_states[0], last(other_states), other_steps, other_tau,
                                                              other_tid, mover_tid);
      mover_states' := [other_states[0]];
      other_states' := other_states;
    }
    else
    {
      mover_states', other_states' := lemma_MoveLeftMoversLeftAsSingleSteps
      (arr, mover_tid, other_tid, other_tau, mover_states, mover_steps, other_states, other_steps);
    } 
  }

  lemma lemma_PerformLeftMove<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    step1:Armada_Multistep<LOneStep>,
    step2:Armada_Multistep<LOneStep>
    ) returns (
    s2':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires s1 in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    requires arr.l.state_ok(s3)
    requires Armada_NextMultistep(arr.l, s1, s2, step1.steps, step1.tid, step1.tau)
    requires Armada_NextMultistep(arr.l, s2, s3, step2.steps, step2.tid, step2.tau)
    requires !step2.tau
    requires step1.tau || step1.tid != step2.tid
    requires IsPhase2(arr, s2, step2.tid)
    ensures  Armada_NextMultistep(arr.l, s1, s2', step2.steps, step2.tid, step2.tau)
    ensures  Armada_NextMultistep(arr.l, s2', s3, step1.steps, step1.tid, step1.tau)
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, s1);
    assert arr.inv(s1);
    var mover_states := Armada_GetStateSequence(arr.l, s2, step2.steps);
    lemma_IfMultistepStartsInPhase2ThenEachStepDoes(arr,s2,s3,step2, mover_states);
    var other_states := Armada_GetStateSequence(arr.l, s1, step1.steps);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s1, s2, step1.steps, other_states);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s2, s3, step2.steps, mover_states);
    var mover_states', other_states' :=
      lemma_PerformLeftMoveAll(arr, step2.tid, step1.tid, step1.tau, step2.steps, mover_states, step1.steps, other_states);
    s2' := last(mover_states');
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, s2', s3, step1.steps, other_states');
  }

  lemma lemma_RightMoversCommute<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoversCommute(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    var idmap := rr.idmap;
    var phase1 := rr.phase1;
    var phase2 := rr.phase2;

    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RefinementViaReductionSpecModule.RightMoversCommuteConditions(rr, initial_state, state_after_right_mover,
                                                                              state_after_both_steps, right_mover, other_step)}
      | RefinementViaReductionSpecModule.RightMoversCommuteConditions(rr, initial_state, state_after_right_mover, state_after_both_steps,
                                                                      right_mover, other_step)
      ensures exists new_middle_state, other_step', right_mover' ::
                && ActionTuple(initial_state, new_middle_state, other_step') in rr.lspec.next
                && ActionTuple(new_middle_state, state_after_both_steps, right_mover') in rr.lspec.next
                && rr.idmap(other_step') == rr.idmap(other_step)
                && rr.idmap(right_mover') == rr.idmap(right_mover)
    {
      var new_middle_state:LState;
      new_middle_state := lemma_PerformRightMove(arr, initial_state, state_after_right_mover, state_after_both_steps,
                                                 right_mover, other_step);
      assert ActionTuple(initial_state, new_middle_state, other_step) in rr.lspec.next;
      assert ActionTuple(new_middle_state, state_after_both_steps, right_mover) in rr.lspec.next;
    }
  }

  lemma lemma_LeftMoversCommute<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoversCommute(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    var idmap := rr.idmap;
    var phase1 := rr.phase1;
    var phase2 := rr.phase2;

    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger RefinementViaReductionSpecModule.LeftMoversCommuteConditions(rr, initial_state, state_after_other_step,
                                                                             state_after_both_steps, other_step, left_mover)}
      | RefinementViaReductionSpecModule.LeftMoversCommuteConditions(rr, initial_state, state_after_other_step, state_after_both_steps,
                                                                     other_step, left_mover)
      ensures exists new_middle_state, left_mover', other_step' ::
                && ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
                && ActionTuple(new_middle_state, state_after_both_steps, other_step') in rr.lspec.next
                && rr.idmap(left_mover') == rr.idmap(left_mover)
                && rr.idmap(other_step') == rr.idmap(other_step)
    {
      var new_middle_state:LState;
      new_middle_state := lemma_PerformLeftMove(arr, initial_state, state_after_other_step, state_after_both_steps,
                                                other_step, left_mover);
      assert ActionTuple(initial_state, new_middle_state, left_mover) in rr.lspec.next;
      assert ActionTuple(new_middle_state, state_after_both_steps, other_step) in rr.lspec.next;
    }
  }

  //////////////////////////////////////
  // RIGHT MOVER CRASH PRESERVATION
  //////////////////////////////////////

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverStepOtherStepSequence<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    right_mover:LOneStep,
    right_mover_tid:Armada_ThreadHandle,
    other_step_steps:seq<LOneStep>,
    other_step_tid:Armada_ThreadHandle,
    other_step_tau:bool,
    other_step_states:seq<LState>
    ) returns (
    state_after_other_step':LState,
    other_step_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, right_mover)
    requires state_after_right_mover == arr.l.step_next(initial_state, right_mover)
    requires arr.l.step_to_thread(right_mover) == right_mover_tid
    requires !arr.l.is_step_tau(right_mover)
    requires Armada_NextMultipleSteps(arr.l, state_after_right_mover, state_after_both_steps, other_step_steps)
    requires forall step :: step in other_step_steps ==> arr.l.step_to_thread(step) == other_step_tid
    requires forall step :: step in other_step_steps ==> arr.l.is_step_tau(step) == other_step_tau
    requires other_step_states == Armada_GetStateSequence(arr.l, state_after_right_mover, other_step_steps)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires other_step_tau || other_step_tid != right_mover_tid
    ensures  Armada_NextMultipleSteps(arr.l, initial_state, state_after_other_step', other_step_steps)
    ensures  other_step_states' == Armada_GetStateSequence(arr.l, initial_state, other_step_steps)
    ensures  |other_step_states'| == |other_step_states|
    ensures  !other_step_tau ==>
             forall i :: 0 <= i < |other_step_states|-1 ==> OKAndPCTypesMatch(arr, other_step_states'[i], other_step_states[i], other_step_tid)
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  {
    assert |other_step_steps| > 0;
    assert arr.l.step_valid(state_after_right_mover, other_step_steps[0]);
    assert other_step_states[1] == arr.l.step_next(state_after_right_mover, other_step_steps[0]);

    if !other_step_tau {
      lemma_ExecutingStepOfOtherActorDoesntChangePCType(arr, initial_state, state_after_right_mover, right_mover, other_step_tid);
    }

    if |other_step_steps| == 1 {
      other_step_states' := Armada_GetStateSequence(arr.l, initial_state, other_step_steps);
      state_after_other_step' := arr.l.step_next(initial_state, other_step_steps[0]);
      assert ArmadaReductionSpecModule.RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_step_steps[0]);
      return;
    }

    assert ArmadaReductionSpecModule.RightMoversCommuteConditions(arr, initial_state, right_mover, other_step_steps[0]);
    assert arr.l.step_valid(initial_state, other_step_steps[0]);
    var s2' := arr.l.step_next(initial_state, other_step_steps[0]);
    assert arr.l.step_valid(s2', right_mover);
    assert other_step_states[1] == arr.l.step_next(s2', right_mover);

    var other_step_states_mid;
    state_after_other_step', other_step_states_mid :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverStepOtherStepSequence(
        arr, rr, s2', other_step_states[1], state_after_both_steps, right_mover,
        right_mover_tid, other_step_steps[1..], other_step_tid, other_step_tau,
        other_step_states[1..]);

    other_step_states' := [initial_state] + other_step_states_mid;
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherArmada_Multistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    other_step:Armada_Multistep<LOneStep>,
    right_mover:LOneStep,
    right_mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_other_step':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, right_mover)
    requires state_after_right_mover == arr.l.step_next(initial_state, right_mover)
    requires arr.l.step_to_thread(right_mover) == right_mover_tid
    requires !arr.l.is_step_tau(right_mover)
    requires Armada_NextMultistep(arr.l, state_after_right_mover, state_after_both_steps, other_step.steps, other_step.tid, other_step.tau)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires other_step.tau || other_step.tid != right_mover_tid
    ensures  Armada_NextMultistep(arr.l, initial_state, state_after_other_step', other_step.steps, other_step.tid, other_step.tau)
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  {
    var other_step_states := Armada_GetStateSequence(arr.l, state_after_right_mover, other_step.steps);
    var other_step_states';
    state_after_other_step', other_step_states' :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverStepOtherStepSequence(
        arr, rr, initial_state, state_after_right_mover, state_after_both_steps,
        right_mover, right_mover_tid, other_step.steps, other_step.tid, other_step.tau,
        other_step_states);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    other_step:Armada_Multistep<LOneStep>,
    right_mover:LOneStep,
    right_mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_other_step':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, right_mover)
    requires state_after_right_mover == arr.l.step_next(initial_state, right_mover)
    requires arr.l.step_to_thread(right_mover) == right_mover_tid
    requires !arr.l.is_step_tau(right_mover)
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires rr.idmap(other_step) != Some(right_mover_tid)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step) in rr.lspec.next
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  {
    state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherArmada_Multistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_steps,
        other_step, right_mover, right_mover_tid);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationRightMoverStepSequenceOtherMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    other_step:Armada_Multistep<LOneStep>,
    right_mover_steps:seq<LOneStep>,
    right_mover_tid:Armada_ThreadHandle,
    right_mover_states:seq<LState>
    ) returns (
    state_after_other_step':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultipleSteps(arr.l, initial_state, state_after_right_mover, right_mover_steps)
    requires forall step :: step in right_mover_steps ==> arr.l.step_to_thread(step) == right_mover_tid
    requires forall step :: step in right_mover_steps ==> !arr.l.is_step_tau(step)
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires right_mover_states == Armada_GetStateSequence(arr.l, initial_state, right_mover_steps)
    requires forall i :: 0 < i < |right_mover_states| ==> IsPhase1(arr, right_mover_states[i], right_mover_tid)
    requires rr.idmap(other_step) != Some(right_mover_tid)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step) in rr.lspec.next
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
    decreases |right_mover_steps|
  {
    if |right_mover_steps| == 0 {
      state_after_other_step' := state_after_both_steps;
      return;
    }

    var pos := |right_mover_states|-2;
    var penultimate_state := right_mover_states[pos];
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, initial_state, state_after_right_mover, right_mover_steps, right_mover_states, pos);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, initial_state, state_after_right_mover, right_mover_steps, right_mover_states);
    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, state_after_right_mover, right_mover_steps, right_mover_states, pos);
    var state_after_other_step_mid :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherMultistep(
        arr, rr, penultimate_state, state_after_right_mover, state_after_both_steps,
        other_step, last(right_mover_steps), right_mover_tid);

    if |right_mover_steps| == 1 {
      state_after_other_step' := state_after_other_step_mid;
      return;
    }

    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, initial_state, state_after_right_mover, right_mover_steps, right_mover_states);
    assert 0 < pos < |right_mover_states|;
    assert IsPhase1(arr, penultimate_state, right_mover_tid);
    state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverStepSequenceOtherMultistep(
        arr, rr, initial_state, penultimate_state, state_after_other_step_mid,
        other_step, all_but_last(right_mover_steps), right_mover_tid,
        all_but_last(right_mover_states));
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationRightMoverArmada_MultistepOtherMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    right_mover:Armada_Multistep<LOneStep>,
    other_step:Armada_Multistep<LOneStep>
    ) returns (
    state_after_other_step':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultistep(arr.l, initial_state, state_after_right_mover, right_mover.steps, right_mover.tid, right_mover.tau)
    requires ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase1(arr, state_after_right_mover, right_mover.tid)
    requires !right_mover.tau
    requires rr.idmap(other_step) != Some(right_mover.tid)
    ensures  ActionTuple(initial_state, state_after_other_step', other_step) in rr.lspec.next
    ensures  rr.crashed(state_after_other_step')
    ensures  RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
  {
    var right_mover_states := Armada_GetStateSequence(arr.l, initial_state, right_mover.steps);
    lemma_IfMultistepEndsInPhase1ThenEachStepDoes(arr, initial_state, state_after_right_mover, right_mover, right_mover_states);
    state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverStepSequenceOtherMultistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_steps,
        other_step, right_mover.steps, right_mover.tid, right_mover_states);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservation<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_steps:LState,
    right_mover:Armada_Multistep<LOneStep>,
    other_step:Armada_Multistep<LOneStep>
    ) returns (
    other_step':Armada_Multistep<LOneStep>,
    state_after_other_step':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
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
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    other_step' := other_step;
    state_after_other_step' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverArmada_MultistepOtherMultistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_steps,
        right_mover, other_step);
  }

  lemma lemma_RightMoverCrashPreservation<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoverCrashPreservation(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);

    forall initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step
      {:trigger RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover,
                                                                                       state_after_both_steps, right_mover, other_step)}
      | RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover,
                                                                               state_after_both_steps, right_mover, other_step)
      && initial_state in AnnotatedReachables(rr.lspec)
      && ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
      && ActionTuple(state_after_right_mover, state_after_both_steps, other_step) in rr.lspec.next
      && !rr.crashed(initial_state)
      && !rr.crashed(state_after_right_mover)
      && rr.crashed(state_after_both_steps)
      && rr.phase1(state_after_right_mover, rr.idmap(right_mover))
      && rr.idmap(right_mover) != rr.idmap(other_step)
      ensures exists other_step', state_after_other_step' ::
                && rr.idmap(other_step') == rr.idmap(other_step)
                && ActionTuple(initial_state, state_after_other_step', other_step') in rr.lspec.next
                && rr.crashed(state_after_other_step')
                && RefinementPair(state_after_both_steps, state_after_other_step') in rr.relation
    {
      var other_step', state_after_other_step' :=
        lemma_DemonstrateRightMoverCrashPreservation(arr, rr, initial_state, state_after_right_mover, state_after_both_steps,
                                                     right_mover, other_step);
    }
  }

  //////////////////////////////////////
  // LEFT MOVERS ENABLED BEFORE CRASH
  //////////////////////////////////////

  lemma lemma_CombineLeftMoverSubstepsIntoStepsOneIteration<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    tid:Armada_ThreadHandle,
    states:seq<LState>,
    steps:seq<LOneStep>,
    pos:int,
    multistates:seq<LState>,
    multisteps:seq<Armada_Multistep<LOneStep>>,
    partial_steps:seq<LOneStep>,
    partial_multistates:seq<LState>
    ) returns (
    pos':int,
    multistates':seq<LState>,
    multisteps':seq<Armada_Multistep<LOneStep>>,
    partial_steps':seq<LOneStep>,
    partial_multistates':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires |states| > 0
    requires Armada_NextMultipleSteps(arr.l, states[0], last(states), steps)
    requires states == Armada_GetStateSequence(arr.l, states[0], steps)
    requires arr.inv(states[0])
    requires IsPhase2(arr, states[0], tid)
    requires Armada_ThreadYielding(arr.l, states[0], tid)
    requires forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    requires !IsPhase2(arr, last(states), tid)
    requires Armada_ThreadYielding(arr.l, last(states), tid)
    requires forall step :: step in steps ==> arr.l.step_to_thread(step) == tid
    requires forall step :: step in steps ==> !arr.l.is_step_tau(step)

    requires 0 <= pos < |steps|
    requires |multistates| > 0
    requires multistates[0] == states[0]
    requires StateNextSeq(multistates, multisteps, rr.lspec.next)
    requires forall step :: step in multisteps ==> !step.tau && step.tid == tid
    requires Armada_ThreadYielding(arr.l, last(multistates), tid)
    requires Armada_ThreadYielding(arr.l, states[pos], tid) ==> |partial_steps| == 0
    requires Armada_NextMultipleSteps(arr.l, last(multistates), states[pos], partial_steps)
    requires partial_multistates == Armada_GetStateSequence(arr.l, last(multistates), partial_steps)
    requires forall i :: 0 < i < |partial_multistates| ==> !Armada_ThreadYielding(arr.l, partial_multistates[i], tid)
    requires forall step :: step in partial_steps ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
    requires if pos < |steps| then (
                 forall s :: s in multistates ==> IsPhase2(arr, s, tid)
             ) else (
                 forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
             )

    ensures  pos' == pos + 1
    ensures  |multistates'| > 0
    ensures  multistates'[0] == states[0]
    ensures  StateNextSeq(multistates', multisteps', rr.lspec.next)
    ensures  forall step :: step in multisteps' ==> !step.tau && step.tid == tid
    ensures  Armada_ThreadYielding(arr.l, last(multistates'), tid)
    ensures  Armada_ThreadYielding(arr.l, states[pos'], tid) ==> |partial_steps'| == 0
    ensures  Armada_NextMultipleSteps(arr.l, last(multistates'), states[pos'], partial_steps')
    ensures  partial_multistates' == Armada_GetStateSequence(arr.l, last(multistates'), partial_steps')
    ensures  forall i :: 0 < i < |partial_multistates'| ==> !Armada_ThreadYielding(arr.l, partial_multistates'[i], tid)
    ensures  forall step :: step in partial_steps' ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
    ensures  if pos' < |steps| then (
                 forall s :: s in multistates' ==> IsPhase2(arr, s, tid)
             ) else (
                 forall i :: 0 <= i < |multistates'|-1 ==> IsPhase2(arr, multistates'[i], tid)
             )
  {
    var s_current := states[pos];
    var s_next := states[pos+1];
    var next_step := steps[pos];

    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, states[0], last(states), steps, states, pos);
    assert arr.l.step_valid(s_current, next_step);
    assert s_next == arr.l.step_next(s_current, next_step);
    var pc' := arr.l.get_thread_pc(s_next, tid);

    lemma_ExtendingStateSequenceWorks(arr, last(multistates), s_current, partial_steps, partial_multistates, next_step, s_next);

    var upper := |partial_multistates|;
    assert forall i :: 0 < i < upper ==> !Armada_ThreadYielding(arr.l, partial_multistates[i], tid);

    partial_steps' := partial_steps + [next_step];
    partial_multistates' := partial_multistates + [s_next];

    assert upper == |partial_steps'|;
    assert forall i :: 0 < i < |partial_steps'| ==> !Armada_ThreadYielding(arr.l, partial_multistates'[i], tid);

    if Armada_ThreadYielding(arr.l, s_next, tid) {
      var multistep := Armada_Multistep(partial_steps', tid, false);

      assert Armada_NextMultistep(arr.l, last(multistates), s_next, multistep.steps, multistep.tid, multistep.tau);
      assert ActionTuple(last(multistates), s_next, multistep) in rr.lspec.next;

      multistates' := multistates + [s_next];
      multisteps' := multisteps + [multistep];

      forall i | 0 <= i < |multisteps'|
        ensures ActionTuple(multistates'[i], multistates'[i+1], multisteps'[i]) in rr.lspec.next
      {
        if i < |multisteps| {
          assert ActionTuple(multistates[i], multistates[i+1], multisteps[i]) in rr.lspec.next;
          assert multistates'[i] == multistates[i];
          assert multistates'[i+1] == multistates[i+1];
          assert multisteps'[i] == multisteps[i];
        }
        else {
          assert i == |multisteps| == |multistates|-1;
          assert multistates'[i] == multistates[i] == last(multistates);
          assert multistates'[i+1] == s_next;
          assert multisteps'[i] == multistep;
        }
      }

      assert StateNextSeq(multistates', multisteps', rr.lspec.next);

      partial_steps' := [];
      partial_multistates' := [s_next];
    }
    else {
      multistates' := multistates;
      multisteps' := multisteps;
    }

    pos' := pos + 1;
    assert Armada_NextMultipleSteps(arr.l, last(multistates'), states[pos'], partial_steps');
  }

  lemma lemma_CombineLeftMoverSubstepsIntoSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    tid:Armada_ThreadHandle,
    states:seq<LState>,
    steps:seq<LOneStep>
    ) returns (
    multistates:seq<LState>,
    multisteps:seq<Armada_Multistep<LOneStep>>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires |states| > 0
    requires Armada_NextMultipleSteps(arr.l, states[0], last(states), steps)
    requires states == Armada_GetStateSequence(arr.l, states[0], steps)
    requires arr.inv(states[0])
    requires Armada_ThreadYielding(arr.l, states[0], tid)
    requires IsPhase2(arr, states[0], tid)
    requires forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    requires !IsPhase2(arr, last(states), tid)
    requires Armada_ThreadYielding(arr.l, last(states), tid)
    requires forall step :: step in steps ==> arr.l.step_to_thread(step) == tid
    requires forall step :: step in steps ==> !arr.l.is_step_tau(step)
    ensures  StateNextSeq(multistates, multisteps, rr.lspec.next)
    ensures  |multistates| > 0
    ensures  multistates[0] == states[0]
    ensures  last(multistates) == last(states)
    ensures  forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
    ensures  forall multistep :: multistep in multisteps ==> !multistep.tau && multistep.tid == tid
  {
    multistates := [states[0]];
    multisteps := [];
    var partial_steps := [];
    var partial_multistates := [states[0]];

    var pos := 0;

    assert Armada_ThreadYielding(arr.l, states[pos], tid) ==> |partial_steps| == 0;
    while pos < |steps|
      invariant 0 <= pos <= |steps|
      invariant |multistates| > 0
      invariant multistates[0] == states[0]
      invariant StateNextSeq(multistates, multisteps, rr.lspec.next)
      invariant forall step :: step in multisteps ==> !step.tau && step.tid == tid
      invariant Armada_ThreadYielding(arr.l, last(multistates), tid)
      invariant Armada_ThreadYielding(arr.l, states[pos], tid) ==> |partial_steps| == 0
      invariant Armada_NextMultipleSteps(arr.l, last(multistates), states[pos], partial_steps)
      invariant partial_multistates == Armada_GetStateSequence(arr.l, last(multistates), partial_steps)
      invariant forall i :: 0 < i < |partial_multistates| ==> !Armada_ThreadYielding(arr.l, partial_multistates[i], tid)
      invariant forall step :: step in partial_steps ==> !arr.l.is_step_tau(step) && arr.l.step_to_thread(step) == tid
      invariant if pos < |steps| then (
                    forall s :: s in multistates ==> IsPhase2(arr, s, tid)
                ) else (
                    forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
                )
      decreases |steps| - pos
    {
      pos, multistates, multisteps, partial_steps, partial_multistates :=
        lemma_CombineLeftMoverSubstepsIntoStepsOneIteration(
          arr, rr, tid, states, steps, pos, multistates, multisteps, partial_steps, partial_multistates);
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashStepSequencePart2<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_step_steps:seq<LOneStep>,
    crash_step_tid:Armada_ThreadHandle,
    crash_step_tau:bool,
    crash_step_states:seq<LState>,
    left_mover_tid:Armada_ThreadHandle,
    left_mover_states_mid:seq<LState>,
    left_mover_steps_mid:seq<LOneStep>,
    post_crash_state':LState
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_steps:seq<Armada_Multistep<LOneStep>>,
    crash_step_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultipleSteps(arr.l, initial_state, post_crash_state, crash_step_steps)
    requires forall step :: step in crash_step_steps ==> arr.l.step_to_thread(step) == crash_step_tid
    requires forall step :: step in crash_step_steps ==> arr.l.is_step_tau(step) == crash_step_tau
    requires crash_step_states == Armada_GetStateSequence(arr.l, initial_state, crash_step_steps)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_step_tau || crash_step_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires Armada_ThreadYielding(arr.l, initial_state, left_mover_tid)
    requires |left_mover_states_mid| > 1
    requires Armada_NextMultipleSteps(arr.l, crash_step_states[|crash_step_states|-2], last(left_mover_states_mid), left_mover_steps_mid)
    requires left_mover_states_mid == Armada_GetStateSequence(arr.l, crash_step_states[|crash_step_states|-2], left_mover_steps_mid)
    requires arr.l.state_ok(last(left_mover_states_mid))
    requires !IsPhase2(arr, last(left_mover_states_mid), left_mover_tid)
    requires Armada_ThreadYielding(arr.l, last(left_mover_states_mid), left_mover_tid)
    requires forall i :: 0 <= i < |left_mover_states_mid|-1 ==> IsPhase2(arr, left_mover_states_mid[i], left_mover_tid)
    requires forall step :: step in left_mover_steps_mid ==> arr.l.step_to_thread(step) == left_mover_tid
    requires forall step :: step in left_mover_steps_mid ==> !arr.l.is_step_tau(step)
    requires arr.l.step_valid(last(left_mover_states_mid), last(crash_step_steps))
    requires post_crash_state' == arr.l.step_next(last(left_mover_states_mid), last(crash_step_steps));
    requires rr.crashed(post_crash_state')
    requires RefinementPair(post_crash_state, post_crash_state') in rr.relation

    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == Some(left_mover_tid)
    ensures  Armada_NextMultipleSteps(arr.l, last(left_mover_states), post_crash_state', crash_step_steps)
    ensures  crash_step_states' == Armada_GetStateSequence(arr.l, last(left_mover_states), crash_step_steps)
    ensures  |crash_step_states'| == |crash_step_states|
    ensures  !crash_step_tau ==>
               forall i :: 0 <= i < |crash_step_states|-1 ==> OKAndPCTypesMatch(arr, crash_step_states'[i], crash_step_states[i], crash_step_tid)
  {
    var pos := |crash_step_states|-2;
    var penultimate_state := crash_step_states[pos];
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, initial_state, post_crash_state, crash_step_steps, crash_step_states, pos);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, initial_state, post_crash_state, crash_step_steps, crash_step_states);
    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, post_crash_state, crash_step_steps, crash_step_states, pos);
    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, initial_state, post_crash_state, crash_step_steps, crash_step_states);

    var mover_states', other_states' :=
      lemma_MoveLeftMoversLeftAsSingleSteps(
        arr, left_mover_tid, crash_step_tid, crash_step_tau, left_mover_states_mid, left_mover_steps_mid,
        all_but_last(crash_step_states), all_but_last(crash_step_steps));

    left_mover_states, left_mover_steps :=
      lemma_CombineLeftMoverSubstepsIntoSteps(arr, rr, left_mover_tid, mover_states', left_mover_steps_mid);

    assert last(left_mover_states) == last(mover_states') == other_states'[0];
    assert Armada_NextMultipleSteps(arr.l, other_states'[0], last(other_states'), all_but_last(crash_step_steps));
    assert last(other_states') == last(left_mover_states_mid);

    lemma_ExtendingStateSequenceWorks(arr, last(left_mover_states), last(left_mover_states_mid), all_but_last(crash_step_steps),
                                      other_states', last(crash_step_steps), post_crash_state');
    lemma_AllButLastPlusLastIsSeq(crash_step_steps);
    assert Armada_NextMultipleSteps(arr.l, last(left_mover_states), post_crash_state', crash_step_steps);

    crash_step_states' := other_states' + [post_crash_state'];
    if !crash_step_tau {
      forall i | 0 <= i < |crash_step_states|-1
        ensures OKAndPCTypesMatch(arr, crash_step_states'[i], crash_step_states[i], crash_step_tid)
      {
        assert crash_step_states'[i] == other_states'[i];
        assert all_but_last(crash_step_states)[i] == crash_step_states[i];
      }
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashOneStep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_step:LOneStep,
    crash_step_tid:Armada_ThreadHandle,
    crash_step_tau:bool,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_steps:seq<LOneStep>,
    post_crash_state':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, crash_step)
    requires post_crash_state == arr.l.step_next(initial_state, crash_step)
    requires arr.l.step_to_thread(crash_step) == crash_step_tid
    requires arr.l.is_step_tau(crash_step) == crash_step_tau
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_step_tau || crash_step_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    ensures  |left_mover_states| > 0
    ensures  Armada_NextMultipleSteps(arr.l, initial_state, last(left_mover_states), left_mover_steps)
    ensures  left_mover_states == Armada_GetStateSequence(arr.l, initial_state, left_mover_steps)
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  Armada_ThreadYielding(arr.l, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  |left_mover_steps| > 0
    ensures  forall step :: step in left_mover_steps ==> arr.l.step_to_thread(step) == left_mover_tid
    ensures  forall step :: step in left_mover_steps ==> !arr.l.is_step_tau(step)
    ensures  arr.l.step_valid(last(left_mover_states), crash_step)
    ensures  post_crash_state' == arr.l.step_next(last(left_mover_states), crash_step)
    ensures  !crash_step_tau ==> OKAndPCTypesMatch(arr, last(left_mover_states), initial_state, crash_step_tid)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
    decreases arr.left_mover_generation_progress(initial_state, left_mover_tid)
  {
    assert ArmadaReductionSpecModule.LeftMoversAlwaysEnabledConditions(arr, initial_state, left_mover_tid);
    var left_mover_step := arr.generate_left_mover(initial_state, left_mover_tid);
    var state_after_left_mover := arr.l.step_next(initial_state, left_mover_step);
    assert && arr.l.step_valid(initial_state, left_mover_step)
           && arr.l.step_to_thread(left_mover_step) == left_mover_tid
           && !arr.l.is_step_tau(left_mover_step)
           && 0 <= arr.left_mover_generation_progress(state_after_left_mover, left_mover_tid)
               < arr.left_mover_generation_progress(initial_state, left_mover_tid);

    assert ArmadaReductionSpecModule.LeftMoverCrashPreservationConditions(arr, initial_state, left_mover_step, crash_step);
    var state_after_both_steps := arr.l.step_next(state_after_left_mover, crash_step);
    assert && arr.l.step_valid(state_after_left_mover, crash_step)
           && !arr.l.state_ok(state_after_both_steps)
           && RefinementPair(post_crash_state, state_after_both_steps) in arr.self_relation;

    if !IsPhase2(arr, state_after_left_mover, left_mover_tid) {
      assert Armada_ThreadYielding(arr.l, state_after_left_mover, left_mover_tid);
      left_mover_states := [initial_state, state_after_left_mover];
      left_mover_steps := [left_mover_step];
      post_crash_state' := state_after_both_steps;
    }
    else {
      var left_mover_states_next, left_mover_steps_next;
      left_mover_states_next, left_mover_steps_next, post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashOneStep(
          arr, rr, state_after_left_mover, state_after_both_steps, crash_step, crash_step_tid, crash_step_tau, left_mover_tid);
      left_mover_states := [initial_state] + left_mover_states_next;
      left_mover_steps := [left_mover_step] + left_mover_steps_next;
      lemma_LastOfConcatenationIsLastOfLatter([initial_state], left_mover_states_next);
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashStepSequence
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_step_steps:seq<LOneStep>,
    crash_step_tid:Armada_ThreadHandle,
    crash_step_tau:bool,
    crash_step_states:seq<LState>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_steps:seq<Armada_Multistep<LOneStep>>,
    crash_step_states':seq<LState>,
    post_crash_state':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultipleSteps(arr.l, initial_state, post_crash_state, crash_step_steps)
    requires forall step :: step in crash_step_steps ==> arr.l.step_to_thread(step) == crash_step_tid
    requires forall step :: step in crash_step_steps ==> arr.l.is_step_tau(step) == crash_step_tau
    requires crash_step_states == Armada_GetStateSequence(arr.l, initial_state, crash_step_steps)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_step_tau || crash_step_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires Armada_ThreadYielding(arr.l, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == Some(left_mover_tid)
    ensures  Armada_NextMultipleSteps(arr.l, last(left_mover_states), post_crash_state', crash_step_steps)
    ensures  crash_step_states' == Armada_GetStateSequence(arr.l, last(left_mover_states), crash_step_steps)
    ensures  |crash_step_states'| == |crash_step_states|
    ensures  !crash_step_tau ==>
               forall i :: 0 <= i < |crash_step_states|-1 ==> OKAndPCTypesMatch(arr, crash_step_states'[i], crash_step_states[i], crash_step_tid)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    assert |crash_step_steps| > 0;

    var pos := |crash_step_states|-2;
    var penultimate_state := crash_step_states[pos];
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, initial_state, post_crash_state, crash_step_steps, crash_step_states, pos);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, initial_state, post_crash_state, crash_step_steps, crash_step_states);
    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, post_crash_state, crash_step_steps, crash_step_states, pos);
    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, initial_state, post_crash_state, crash_step_steps, crash_step_states);
    lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, initial_state, penultimate_state, all_but_last(crash_step_steps),
                                                              crash_step_tau, crash_step_tid, left_mover_tid);

    var left_mover_states_mid, left_mover_steps_mid;
    left_mover_states_mid, left_mover_steps_mid, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashOneStep(
        arr, rr, penultimate_state, post_crash_state, last(crash_step_steps), crash_step_tid, crash_step_tau, left_mover_tid);

    left_mover_states, left_mover_steps, crash_step_states' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashStepSequencePart2(
        arr, rr, initial_state, post_crash_state, crash_step_steps, crash_step_tid, crash_step_tau, crash_step_states,
        left_mover_tid, left_mover_states_mid, left_mover_steps_mid, post_crash_state');
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashArmada_Multistep
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_step:Armada_Multistep<LOneStep>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_steps:seq<Armada_Multistep<LOneStep>>,
    post_crash_state':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultistep(arr.l, initial_state, post_crash_state, crash_step.steps, crash_step.tid, crash_step.tau)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_step.tau || crash_step.tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires Armada_ThreadYielding(arr.l, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == Some(left_mover_tid)
    ensures  Armada_NextMultistep(arr.l, last(left_mover_states), post_crash_state', crash_step.steps, crash_step.tid, crash_step.tau)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    var crash_step_states := Armada_GetStateSequence(arr.l, initial_state, crash_step.steps);
    var crash_step_states';
    left_mover_states, left_mover_steps, crash_step_states', post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashStepSequence(
        arr, rr, initial_state, post_crash_state, crash_step.steps, crash_step.tid, crash_step.tau, crash_step_states,
        left_mover_tid);
  } 

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrash<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_step:Armada_Multistep<LOneStep>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_steps:seq<Armada_Multistep<LOneStep>>,
    post_crash_state':LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, post_crash_state, crash_step) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires rr.idmap(crash_step) != Some(left_mover_tid)
    requires IsPhase2(arr, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_steps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall step :: step in left_mover_steps ==> rr.idmap(step) == Some(left_mover_tid)
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_step) in rr.lspec.next
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    lemma_StateAmongAnnotatedReachablesHasThreadYielding(arr, initial_state, left_mover_tid);
    left_mover_states, left_mover_steps, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashArmada_Multistep(
        arr, rr, initial_state, post_crash_state, crash_step, left_mover_tid);
    assert Armada_NextMultistep(arr.l, last(left_mover_states), post_crash_state', crash_step.steps, crash_step.tid, crash_step.tau);
    assert ActionTuple(last(left_mover_states), post_crash_state', crash_step) in rr.lspec.next;
  }

  lemma lemma_LeftMoversEnabledBeforeCrash<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  LeftMoversEnabledBeforeCrash(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall initial_state, post_crash_state, crash_step, actor
      {:trigger RefinementViaReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_step,
                                                                                        actor)}
      | RefinementViaReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_step, actor)
      ensures exists states, trace, crash_step', post_crash_state' ::
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
    {
      var states, trace, post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrash(arr, rr, initial_state, post_crash_state, crash_step, actor.v);
    }
  }

  //////////////////////////////////////////
  // LEFT MOVER SELF CRASH PRESERVATION
  //////////////////////////////////////////

  lemma lemma_DemonstrateLeftMoverSingleStepSelfCrashPreservationAcrossSingleStep
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    other_step:LOneStep,
    mover_step:LOneStep,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.step_valid(initial_state, other_step)
    requires state_after_other_step == arr.l.step_next(initial_state, other_step)
    requires arr.l.is_step_tau(other_step) == other_tau
    requires arr.l.step_to_thread(other_step) == other_tid
    requires arr.l.step_valid(state_after_other_step, mover_step)
    requires state_after_both_steps == arr.l.step_next(state_after_other_step, mover_step)
    requires !arr.l.is_step_tau(mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase2(arr, state_after_other_step, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  arr.l.step_valid(initial_state, mover_step)
    ensures  state_after_left_mover == arr.l.step_next(initial_state, mover_step)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover) in rr.relation
  {
    assert ArmadaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(arr, initial_state, mover_step, other_step);
    state_after_left_mover := arr.l.step_next(initial_state, mover_step);
  }

  lemma lemma_DemonstrateLeftMoverSingleStepSelfCrashPreservationAcrossStepSequence
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    other_steps:seq<LOneStep>,
    mover_step:LOneStep,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultipleSteps(arr.l, initial_state, state_after_other_step, other_steps)
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires arr.l.step_valid(state_after_other_step, mover_step)
    requires state_after_both_steps == arr.l.step_next(state_after_other_step, mover_step)
    requires !arr.l.is_step_tau(mover_step)
    requires arr.l.step_to_thread(mover_step) == mover_tid
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase2(arr, state_after_other_step, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  arr.l.step_valid(initial_state, mover_step)
    ensures  state_after_left_mover == arr.l.step_next(initial_state, mover_step)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover) in rr.relation
  {
    if |other_steps| == 0 {
      state_after_left_mover := state_after_both_steps;
      return;
    }

    var other_states := Armada_GetStateSequence(arr.l, initial_state, other_steps);
    var pos := |other_states|-2;
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, initial_state, state_after_other_step, other_steps, other_states, pos);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, initial_state, state_after_other_step, other_steps, other_states);
    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, initial_state, state_after_other_step, other_steps, other_states);
    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, state_after_other_step, other_steps, other_states, pos);
    var state_after_left_mover_mid :=
      lemma_DemonstrateLeftMoverSingleStepSelfCrashPreservationAcrossSingleStep(
        arr, rr, other_states[pos], other_states[pos+1], state_after_both_steps, last(other_steps), mover_step,
        mover_tid, other_tau, other_tid);

    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSingleStepSelfCrashPreservationAcrossStepSequence(
        arr, rr, initial_state, other_states[pos], state_after_left_mover_mid, all_but_last(other_steps), mover_step,
        mover_tid, other_tau, other_tid);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationStepSequence<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    other_steps:seq<LOneStep>,
    mover_steps:seq<LOneStep>,
    mover_states:seq<LState>,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState,
    mover_states':seq<LState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultipleSteps(arr.l, initial_state, state_after_other_step, other_steps)
    requires forall step :: step in other_steps ==> arr.l.is_step_tau(step) == other_tau
    requires forall step :: step in other_steps ==> arr.l.step_to_thread(step) == other_tid
    requires Armada_NextMultipleSteps(arr.l, state_after_other_step, state_after_both_steps, mover_steps)
    requires mover_states == Armada_GetStateSequence(arr.l, state_after_other_step, mover_steps)
    requires forall step :: step in mover_steps ==> !arr.l.is_step_tau(step)
    requires forall step :: step in mover_steps ==> arr.l.step_to_thread(step) == mover_tid
    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase2(arr, state_after_other_step, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  Armada_NextMultipleSteps(arr.l, initial_state, state_after_left_mover, mover_steps)
    ensures  mover_states' == Armada_GetStateSequence(arr.l, initial_state, mover_steps)
    ensures  |mover_states'| == |mover_states|
    ensures  forall i :: 0 <= i < |mover_states|-1 ==> OKAndPCTypesMatch(arr, mover_states[i], mover_states'[i], mover_tid)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover) in rr.relation
  {
    assert state_after_both_steps != state_after_other_step;
    assert |mover_steps| > 0;

    var pos := |mover_states|-2;
    lemma_ArmadaNextMultipleStepsImpliesValidStep(arr.l, state_after_other_step, state_after_both_steps, mover_steps, mover_states, pos);
    assert !rr.crashed(mover_states[pos]);

    var other_states := Armada_GetStateSequence(arr.l, initial_state, other_steps);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, initial_state, state_after_other_step, other_steps, other_states);
    lemma_ArmadaNextMultipleStepsLastElement(arr.l, state_after_other_step, state_after_both_steps, mover_steps, mover_states);
    lemma_AllButLastPreservesArmadaNextMultipleSteps(arr, state_after_other_step, state_after_both_steps, mover_steps, mover_states);

    var mover_states_mid, other_states_mid;
    if |mover_steps| == 1 {
      mover_states_mid := [initial_state];
      other_states_mid := other_states;
      forall i | 0 <= i < |all_but_last(mover_states)|
        ensures OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid)
      {
        assert mover_states_mid[i] == initial_state;
        assert all_but_last(mover_states)[i] == state_after_other_step;
        lemma_ExecutingStepSequenceOfOtherActorDoesntChangePCType(arr, initial_state, state_after_other_step, other_steps, other_tau,
                                                                  other_tid, mover_tid);
      }
    }
    else {
      mover_states_mid, other_states_mid :=
        lemma_MoveLeftMoversLeftAsSingleSteps(arr, mover_tid, other_tid, other_tau, all_but_last(mover_states),
                                              all_but_last(mover_steps), other_states, other_steps);
    }
    assert forall i :: 0 <= i < |all_but_last(mover_states)| ==> OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid);

    lemma_InvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, last(mover_states_mid), all_but_last(mover_steps), mover_states_mid,
                                            |mover_states_mid|-1);
    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSingleStepSelfCrashPreservationAcrossStepSequence(
        arr, rr, last(mover_states_mid), last(other_states_mid), last(mover_states), other_steps, last(mover_steps),
        mover_tid, other_tau, other_tid);
    mover_states' := mover_states_mid + [state_after_left_mover];
    lemma_ExtendingStateSequenceWorks(arr, initial_state, last(mover_states_mid), all_but_last(mover_steps), mover_states_mid,
                                      last(mover_steps), state_after_left_mover);
    lemma_AllButLastPlusLastIsSeq(mover_steps);

    forall i | 0 <= i < |mover_states|-1
      ensures OKAndPCTypesMatch(arr, mover_states[i], mover_states'[i], mover_tid)
    {
      assert mover_states'[i] == mover_states_mid[i];
      assert 0 <= i < |all_but_last(mover_states)|;
      assert OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid);
      assert all_but_last(mover_states)[i] == mover_states[i];
    }
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationArmadaMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    other_step:Armada_Multistep<LOneStep>,
    mover_step:Armada_Multistep<LOneStep>,
    mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires Armada_NextMultistep(arr.l, initial_state, state_after_other_step, other_step.steps, other_step.tid, other_step.tau)
    requires Armada_NextMultistep(arr.l, state_after_other_step, state_after_both_steps, mover_step.steps, mover_step.tid, mover_step.tau)
    requires mover_step.tid == mover_tid
    requires !mover_step.tau
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase2(arr, state_after_other_step, mover_tid)
    requires other_step.tau || other_step.tid != mover_tid
    ensures  Armada_NextMultistep(arr.l, initial_state, state_after_left_mover, mover_step.steps, mover_step.tid, mover_step.tau)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover) in rr.relation
  {
    var mover_states := Armada_GetStateSequence(arr.l, state_after_other_step, mover_step.steps);
    lemma_IfMultistepStartsInPhase2ThenEachStepDoes(arr, state_after_other_step, state_after_both_steps, mover_step, mover_states);
    var mover_states';
    state_after_left_mover, mover_states' :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationStepSequence(
        arr, rr, initial_state, state_after_other_step, state_after_both_steps, other_step.steps, mover_step.steps, mover_states,
        mover_tid, other_step.tau, other_step.tid);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservation<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LOneStep>, Armada_Multistep<LOneStep>>,
    initial_state:LState,
    state_after_other_step:LState,
    state_after_both_steps:LState,
    other_step:Armada_Multistep<LOneStep>,
    left_mover:Armada_Multistep<LOneStep>,
    mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidArmadaReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
    requires ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_step)
    requires rr.crashed(state_after_both_steps)
    requires IsPhase2(arr, state_after_other_step, mover_tid)
    requires rr.idmap(left_mover) == Some(mover_tid)
    requires rr.idmap(other_step) != Some(mover_tid)
    ensures  ActionTuple(initial_state, state_after_left_mover, left_mover) in rr.lspec.next
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_steps, state_after_left_mover) in rr.relation
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationArmadaMultistep(
        arr, rr, initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover, mover_tid);
  }

  lemma lemma_LeftMoverSelfCrashPreservation<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservation(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);

    forall initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover
      {:trigger RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_step,
                                                                                          state_after_both_steps, other_step, left_mover)}
      | RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_step,
                                                                                  state_after_both_steps, other_step, left_mover)
      && initial_state in AnnotatedReachables(rr.lspec)
      && ActionTuple(initial_state, state_after_other_step, other_step) in rr.lspec.next
      && ActionTuple(state_after_other_step, state_after_both_steps, left_mover) in rr.lspec.next
      && !rr.crashed(initial_state)
      && !rr.crashed(state_after_other_step)
      && rr.crashed(state_after_both_steps)
      && rr.phase2(state_after_other_step, rr.idmap(left_mover))
      && rr.idmap(left_mover) != rr.idmap(other_step)
      ensures exists left_mover', state_after_left_mover' ::
                 && rr.idmap(left_mover') == rr.idmap(left_mover)
                 && ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
                 && rr.crashed(state_after_left_mover')
                 && RefinementPair(state_after_both_steps, state_after_left_mover') in rr.relation
    {
      var state_after_left_mover :=
        lemma_DemonstrateLeftMoverSelfCrashPreservation(arr, rr, initial_state, state_after_other_step, state_after_both_steps,
                                                        other_step, left_mover, rr.idmap(left_mover).v);
    }
  }

  //////////////////////////////////////
  // REDUCTION REQUEST VALID
  //////////////////////////////////////

  lemma lemma_IfArmadaReductionRequestValidThenRefinementViaReductionRequestValid
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>
    )
    requires ValidArmadaReductionRequest(arr)
    ensures  ValidRefinementViaReductionRequest(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    assert RefinementRelationReflexive(rr.relation);
    assert RefinementRelationTransitive(rr.relation);
    assert rr.hspec.init == rr.lspec.init;
    assert forall s, actor :: s in rr.lspec.init ==> !rr.phase1(s, actor) && !rr.phase2(s, actor);
    assert forall s, actor :: rr.phase1(s, actor) ==> !rr.phase2(s, actor);
    lemma_IfArmadaReductionRequestValidThenCrashingCantGoDirectlyFromPhase2ToPhase1(arr);
    lemma_IfArmadaReductionRequestValidThenCrashingPhaseUnaffectedByOtherActors(arr);
    lemma_PostCrashStepsStutter(arr);
    lemma_RightMoversPreserveStateRefinement(arr);
    lemma_LeftMoversPreserveStateRefinement(arr);
    lemma_RightMoversCommute(arr);
    lemma_LeftMoversCommute(arr);
    lemma_RightMoverCrashPreservation(arr);
    lemma_LeftMoverSelfCrashPreservation(arr);
    lemma_ActionSequencesLiftable(arr);
    lemma_LeftMoversAlwaysEnabled(arr);
    lemma_LeftMoversEnabledBeforeCrash(arr);
  }

  //////////////////////////////
  // UTILITY FUNCTIONS
  //////////////////////////////

  function LMultistepToHMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    lmultistep:Armada_Multistep<LOneStep>
    ) : Armada_Multistep<HOneStep>
  {
    Armada_Multistep(MapSeqToSeq(lmultistep.steps, arr.lonestep_to_honestep), lmultistep.tid, lmultistep.tau)
  }

  //////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////

  lemma lemma_ArmadaGetStateSequenceLastElement<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    states:seq<LState>
    )
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires states == Armada_GetStateSequence(arr.l, s, steps)
    ensures  last(states) == s'
  {
    if |steps| > 0 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_ArmadaGetStateSequenceLastElement(arr, s_mid, s', steps[1..], states[1..]);
    }
  }

  /////////////////////////////////////////////
  // SHIM BETWEEN ARMADA AND COHEN-LAMPORT
  /////////////////////////////////////////////

  lemma lemma_IfBehaviorSatisfiesGenericSpecThenItSatisfiesRefinementViaReductionLSpec
    <LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    b:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>
    )
    requires ValidArmadaReductionRequest(arr)
    requires AnnotatedBehaviorSatisfiesSpec(b, SpecFunctionsToSpec(arr.l))
    ensures  AnnotatedBehaviorSatisfiesSpec(b, GetRefinementViaReductionLSpec(arr))
  {
    var rspec := GetRefinementViaReductionLSpec(arr);
    forall i {:trigger ActionTuple(b.states[i], b.states[i+1], b.trace[i]) in rspec.next} | 0 <= i < |b.trace|
      ensures ActionTuple(b.states[i], b.states[i+1], b.trace[i]) in rspec.next
    {
      assert ActionTuple(b.states[i], b.states[i+1], b.trace[i]) in SpecFunctionsToSpec(arr.l).next;
    }
  }

  lemma lemma_LHMaintainsNextMultipleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lsteps:seq<LOneStep>,
    lstates:seq<LState>,
    hs:HState,
    hs':HState,
    hsteps:seq<HOneStep>,
    hstates:seq<HState>
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.inv(ls)
    requires Armada_NextMultipleSteps(arr.l, ls, ls', lsteps)
    requires lstates == Armada_GetStateSequence(arr.l, ls, lsteps)
    requires hs == arr.lstate_to_hstate(ls)
    requires hs' == arr.lstate_to_hstate(ls')
    requires hsteps == MapSeqToSeq(lsteps, arr.lonestep_to_honestep)
    requires hstates == Armada_GetStateSequence(arr.h, hs, hsteps)
    ensures  Armada_NextMultipleSteps(arr.h, hs, hs', hsteps)
    ensures  |hstates| == |lstates|
    ensures  forall i :: 0 <= i < |lstates| ==> hstates[i] == arr.lstate_to_hstate(lstates[i])
  {
    if |lsteps| > 0 {
      var ls_next := arr.l.step_next(ls, lsteps[0]);
      var hs_next := arr.h.step_next(hs, hsteps[0]);
      assert hs_next == arr.lstate_to_hstate(ls_next);
      lemma_LHMaintainsNextMultipleSteps(arr, ls_next, ls', lsteps[1..], lstates[1..], hs_next, hs', hsteps[1..], hstates[1..]);
    }
  }

  lemma lemma_LHMaintainsNext<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    ls:LState,
    ls':LState,
    lmultistep:Armada_Multistep<LOneStep>,
    hs:HState,
    hs':HState,
    hmultistep:Armada_Multistep<HOneStep>
    )
    requires ValidArmadaReductionRequest(arr)
    requires arr.inv(ls)
    requires ActionTuple(ls, ls', lmultistep) in GetRefinementViaReductionHSpec(arr).next;
    requires hs == arr.lstate_to_hstate(ls)
    requires hs' == arr.lstate_to_hstate(ls')
    requires hmultistep == LMultistepToHMultistep(arr, lmultistep)
    ensures  ActionTuple(hs, hs', hmultistep) in SpecFunctionsToSpec(arr.h).next
  {
    assert GenericNextReduced(arr, ls, ls', lmultistep.steps, lmultistep.tid, lmultistep.tau);
    var hsteps := MapSeqToSeq(lmultistep.steps, arr.lonestep_to_honestep);
    var hmultistep := Armada_Multistep(hsteps, lmultistep.tid, lmultistep.tau);
    var lstates := Armada_GetStateSequence(arr.l, ls, lmultistep.steps);
    var hstates := Armada_GetStateSequence(arr.h, hs, hmultistep.steps);
    lemma_LHMaintainsNextMultipleSteps(arr, ls, ls', lmultistep.steps, lstates, hs, hs', hmultistep.steps, hstates);
    assert Armada_NextMultistep(arr.h, hs, hs', hsteps, hmultistep.tid, hmultistep.tau);
    assert ActionTuple(hs, hs', hmultistep) in SpecFunctionsToSpec(arr.h).next;
  }

  lemma lemma_InvariantHoldsAtIntermediateStateArmadaNextMultipleSteps<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    s:LState,
    s':LState,
    steps:seq<LOneStep>,
    states:seq<LState>,
    pos:int
    )
    requires ValidArmadaReductionRequest(arr)
    requires Armada_NextMultipleSteps(arr.l, s, s', steps)
    requires states == Armada_GetStateSequence(arr.l, s, steps)
    requires 0 <= pos < |states|
    requires arr.inv(states[0])
    ensures  arr.inv(states[pos])
    decreases pos
  {
    if pos > 0 {
      var s_mid := arr.l.step_next(s, steps[0]);
      lemma_InvariantHoldsAtIntermediateStateArmadaNextMultipleSteps(arr, s_mid, s', steps[1..], states[1..], pos-1);
    }
  }

  lemma lemma_GenericNextReducedBehaviorSatisfiesInv<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    arr:ArmadaReductionRequest<LState, LOneStep, LPC, HState, HOneStep, HPC>,
    b:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>,
    i:int
    )
    requires ValidArmadaReductionRequest(arr)
    requires AnnotatedBehaviorSatisfiesSpec(b, GetRefinementViaReductionHSpec(arr))
    requires 0 <= i < |b.states|
    ensures  arr.inv(b.states[i])
  {
    if i == 0 {
      return;
    }

    lemma_GenericNextReducedBehaviorSatisfiesInv(arr, b, i-1);

    var spec := GetRefinementViaReductionHSpec(arr);
    var prev := i-1;
    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];
    var steps := step.steps;
    var states := Armada_GetStateSequence(arr.l, s, steps);

    assert s' == b.states[i];
    assert 0 <= prev < |b.trace|;
    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in spec.next;
    assert GenericNextReduced(arr, s, s', steps, step.tid, step.tau);
    assert Armada_NextMultipleSteps(arr.l, s, s', steps);
    lemma_InvariantHoldsAtIntermediateStateArmadaNextMultipleSteps(arr, s, s', steps, states, |states|-1);
    assert arr.inv(states[|states|-1]);
    assert arr.inv(last(states));
    lemma_ArmadaGetStateSequenceLastElement(arr, s, s', steps, states);
    assert last(states) == s';
    assert arr.inv(s');
  }

}
