include "GenericArmadaSpec.i.dfy"

module GenericArmadaLemmasModule {

  import opened util_collections_seqs_s
  import opened GenericArmadaSpecModule
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions

  lemma lemma_ArmadaGetStateSequenceOnePos<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>,
    pos:int
    )
    requires 0 <= pos < |steps|
    ensures  var states := Armada_GetStateSequence(asf, s, steps); states[pos+1] == asf.step_next(states[pos], steps[pos])
  {
    if |steps| > 0 && pos > 0 {
      lemma_ArmadaGetStateSequenceOnePos(asf, asf.step_next(s, steps[0]), steps[1..], pos-1);
    }
  }

  lemma lemma_ArmadaGetStateSequenceDrop<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>,
    states:seq<State>
    )
    requires states == Armada_GetStateSequence(asf, s, steps)
    requires |steps| > 0
    ensures  |states| > 0
    ensures  states[1..] == Armada_GetStateSequence(asf, asf.step_next(s, steps[0]), steps[1..])
  {
  }

  lemma lemma_ArmadaGetStateSequenceDropMultiple<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>,
    states:seq<State>,
    pos:int
    )
    requires states == Armada_GetStateSequence(asf, s, steps)
    requires 0 <= pos <= |steps|
    ensures  |states| > pos
    ensures  states[pos..] == Armada_GetStateSequence(asf, states[pos], steps[pos..])
  {
    if pos > 0 {
      lemma_ArmadaGetStateSequenceDropMultiple(asf, s, steps, states, pos-1);
    }
  }

  lemma lemma_ArmadaNextMultipleStepsDropMultiple<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>,
    pos:int
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires states == Armada_GetStateSequence(asf, s, steps)
    requires 0 <= pos <= |steps|
    ensures  |states| > pos
    ensures  Armada_NextMultipleSteps(asf, states[pos], s', steps[pos..])
    ensures  states[pos..] == Armada_GetStateSequence(asf, states[pos], steps[pos..])
  {
    if pos > 0 {
      lemma_ArmadaNextMultipleStepsDropMultiple(asf, s, s', steps, states, pos-1);
    }
  }

  lemma lemma_ExtendArmadaGetStateSequence<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>,
    states:seq<State>,
    s':State,
    step:OneStep
    )
    requires states == Armada_GetStateSequence(asf, s, steps)
    requires s' == asf.step_next(last(states), step)
    ensures  states + [s'] == Armada_GetStateSequence(asf, s, steps + [step])
    decreases |steps|
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0]);
      lemma_ExtendArmadaGetStateSequence(asf, s_next, steps[1..], states[1..], s', step);
      var all_steps := steps + [step];
      assert all_steps[0] == steps[0];
      assert all_steps[1..] == steps[1..] + [step];
      assert states[1..] + [s'] == Armada_GetStateSequence(asf, s_next, steps[1..] + [step]);
    }
  }

  lemma lemma_CombineArmadaNextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    s'':State,
    steps1:seq<OneStep>,
    steps2:seq<OneStep>
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps1)
    requires Armada_NextMultipleSteps(asf, s', s'', steps2)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps1 + steps2)
    decreases |steps2|
  {
    if |steps2| == 0 {
      assert s'' == s';
      assert steps1 + steps2 == steps1;
      return;
    }

    var s_next := asf.step_next(s', steps2[0]);
    lemma_ExtendArmadaNextMultipleSteps(asf, s, s', s_next, steps1, steps2[0]);
    lemma_CombineArmadaNextMultipleSteps(asf, s, s_next, s'', steps1 + [steps2[0]], steps2[1..]);

    calc {
      steps1 + steps2;
      steps1 + ([steps2[0]] + steps2[1..]);
      (steps1 + [steps2[0]]) + steps2[1..];
    }
  }

  lemma lemma_CombineArmadaGetStateSequence<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    s'':State,
    steps1:seq<OneStep>,
    steps2:seq<OneStep>,
    states1:seq<State>,
    states2:seq<State>
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps1)
    requires Armada_NextMultipleSteps(asf, s', s'', steps2)
    requires states1 == Armada_GetStateSequence(asf, s, steps1)
    requires states2 == Armada_GetStateSequence(asf, s', steps2)
    ensures  Armada_GetStateSequence(asf, s, steps1 + steps2) == all_but_last(states1) + states2 == states1 + states2[1..]
    decreases |steps2|
  {
    lemma_ArmadaNextMultipleStepsLastElement(asf, s, s', steps1, states1);
    assert last(states1) == states2[0];

    if |steps2| == 0 {
      assert all_but_last(states1) + states2 == states1;
      assert steps1 + steps2 == steps1;
      return;
    }

    var s_next := asf.step_next(s', steps2[0]);
    lemma_ExtendArmadaNextMultipleSteps(asf, s, s', states2[1], steps1, steps2[0]);
    lemma_ExtendArmadaGetStateSequence(asf, s, steps1, states1, states2[1], steps2[0]);
    lemma_CombineArmadaGetStateSequence(asf, s, s_next, s'', steps1 + [steps2[0]], steps2[1..], states1 + [s_next], states2[1..]);

    calc {
      steps1 + steps2;
      steps1 + ([steps2[0]] + steps2[1..]);
      (steps1 + [steps2[0]]) + steps2[1..];
    }

    calc {
      all_but_last(states1) + states2;
      states1 + states2[1..];
      all_but_last(states1 + [states2[0]]) + states2[1..];
      Armada_GetStateSequence(asf, s, (steps1 + [steps2[0]]) + steps2[1..]);
      Armada_GetStateSequence(asf, s, steps1 + steps2);
    }
  }

  lemma lemma_ArmadaNextMultipleStepsImpliesValidStep<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>,
    i:int
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires 0 <= i < |steps|
    requires states == Armada_GetStateSequence(asf, s, steps)
    ensures  asf.step_valid(states[i], steps[i])
    ensures  states[i+1] == asf.step_next(states[i], steps[i])
  {
    if i > 0 {
      var s_mid := asf.step_next(s, steps[0]);
      lemma_ArmadaNextMultipleStepsImpliesValidStep(asf, s_mid, s', steps[1..], states[1..], i-1);
    }
  }

  lemma lemma_ArmadaNextMultipleStepsLastElement<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires states == Armada_GetStateSequence(asf, s, steps)
    ensures  last(states) == s'
  {
    if |steps| > 0 {
      var s_mid := asf.step_next(s, steps[0]);
      lemma_ArmadaNextMultipleStepsLastElement(asf, s_mid, s', steps[1..], states[1..]);
    }
  }

  lemma lemma_ExtendArmadaNextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    s'':State,
    steps:seq<OneStep>,
    step:OneStep
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires asf.step_valid(s', step)
    requires s'' == asf.step_next(s', step)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps + [step])
    decreases |steps|
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0]);
      lemma_ExtendArmadaNextMultipleSteps(asf, s_next, s', s'', steps[1..], step);
      var all_steps := steps + [step];
      assert all_steps[0] == steps[0];
      assert all_steps[1..] == steps[1..] + [step];
      assert Armada_NextMultipleSteps(asf, s_next, s'', all_steps[1..]);
    }
  }

  lemma lemma_InvariantHoldsAtIntermediateState<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>,
    pos:int
    )
    requires OneStepPreservesInv(asf, inv)
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires states == Armada_GetStateSequence(asf, s, steps)
    requires 0 <= pos < |states|
    requires inv(states[0])
    ensures  inv(states[pos])
    decreases pos
  {
    if pos > 0 {
      var s_mid := asf.step_next(s, steps[0]);
      lemma_InvariantHoldsAtIntermediateState(asf, inv, s_mid, s', steps[1..], states[1..], pos-1);
    }
  }

  lemma lemma_MultistepNextMaintainsInv<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool,
    s:State,
    s':State,
    step:Armada_Multistep<OneStep>
    )
    requires OneStepPreservesInv(asf, inv)
    requires inv(s)
    requires ActionTuple(s, s', step) in SpecFunctionsToSpec(asf).next
    ensures  inv(s')
  {
    var states := Armada_GetStateSequence(asf, s, step.steps);
    lemma_InvariantHoldsAtIntermediateState(asf, inv, s, s', step.steps, states, |step.steps|);
    lemma_ArmadaNextMultipleStepsLastElement(asf, s, s', step.steps, states);
  }

  lemma lemma_TakingMultistepKeepsThreadYielding<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    multistep:Armada_Multistep<OneStep>,
    tid:Armada_ThreadHandle
    )
    requires TauLeavesPCUnchanged(asf)
    requires ThreadCantAffectOtherThreadPCExceptViaFork(asf)
    requires OneStepRequiresOK(asf)
    requires ActionTuple(s, s', multistep) in SpecFunctionsToSpec(asf).next
    requires asf.state_ok(s) ==> Armada_ThreadYielding(asf, s, tid)
    ensures  asf.state_ok(s') ==> Armada_ThreadYielding(asf, s', tid)
  {
    var pc' := asf.get_thread_pc(s', tid);
    var states := Armada_GetStateSequence(asf, s, multistep.steps);
    lemma_ArmadaNextMultipleStepsLastElement(asf, s, s', multistep.steps, states);
    assert Armada_NextMultistep(asf, s, s', multistep.steps, multistep.tid, multistep.tau);

    if multistep.tau {
      return;
    }

    if multistep.tid == tid {
      return;
    }

    var pos := 0;
    while pos < |multistep.steps|
      invariant 0 <= pos <= |multistep.steps|
      invariant asf.state_ok(states[pos]) ==> Armada_ThreadYielding(asf, states[pos], tid)
      decreases |multistep.steps|-pos
    {
      lemma_ArmadaNextMultipleStepsImpliesValidStep(asf, s, s', multistep.steps, states, pos);
      pos := pos + 1;
    }
  }

  lemma lemma_TakingMultistepKeepsAllThreadsYielding<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    multistep:Armada_Multistep<OneStep>
    )
    requires TauLeavesPCUnchanged(asf)
    requires ThreadCantAffectOtherThreadPCExceptViaFork(asf)
    requires OneStepRequiresOK(asf)
    requires ActionTuple(s, s', multistep) in SpecFunctionsToSpec(asf).next
    requires forall tid :: asf.state_ok(s) ==> Armada_ThreadYielding(asf, s, tid)
    ensures  forall tid :: asf.state_ok(s') ==> Armada_ThreadYielding(asf, s', tid)
  {
    forall tid
      ensures asf.state_ok(s') ==> Armada_ThreadYielding(asf, s', tid)
    {
      lemma_TakingMultistepKeepsThreadYielding(asf, s, s', multistep, tid);
    }
  }

  lemma lemma_ThreadYieldingAtPos<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    b:AnnotatedBehavior<State, Armada_Multistep<OneStep>>,
    pos:int,
    tid:Armada_ThreadHandle
    )
    requires TauLeavesPCUnchanged(asf)
    requires ThreadCantAffectOtherThreadPCExceptViaFork(asf)
    requires OneStepRequiresOK(asf)
    requires InitImpliesYielding(asf)
    requires AnnotatedBehaviorSatisfiesSpec(b, SpecFunctionsToSpec(asf))
    requires 0 <= pos < |b.states|
    ensures  asf.state_ok(b.states[pos]) ==> Armada_ThreadYielding(asf, b.states[pos], tid)
  {
    if pos == 0 {
      return;
    }

    var prev := pos-1;
    lemma_ThreadYieldingAtPos(asf, b, pos-1, tid);
    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in SpecFunctionsToSpec(asf).next;
    lemma_TakingMultistepKeepsThreadYielding(asf, b.states[prev], b.states[prev+1], b.trace[prev], tid);
  }

  lemma lemma_AllThreadsYieldingAtPos<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    b:AnnotatedBehavior<State, Armada_Multistep<OneStep>>,
    pos:int
    )
    requires TauLeavesPCUnchanged(asf)
    requires ThreadCantAffectOtherThreadPCExceptViaFork(asf)
    requires OneStepRequiresOK(asf)
    requires InitImpliesYielding(asf)
    requires AnnotatedBehaviorSatisfiesSpec(b, SpecFunctionsToSpec(asf))
    requires 0 <= pos < |b.states|
    ensures  forall tid :: asf.state_ok(b.states[pos]) ==> Armada_ThreadYielding(asf, b.states[pos], tid)
  {
    forall tid
      ensures asf.state_ok(b.states[pos]) ==> Armada_ThreadYielding(asf, b.states[pos], tid)
    {
      lemma_ThreadYieldingAtPos(asf, b, pos, tid);
    }
  }

  lemma lemma_IfAllStepsValidThenArmadaNextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    states:seq<State>,
    steps:seq<OneStep>
    )
    requires |states| == |steps| + 1
    requires forall i :: 0 <= i < |steps| ==> asf.step_valid(states[i], steps[i])
    requires forall i :: 0 <= i < |steps| ==> states[i+1] == asf.step_next(states[i], steps[i])
    ensures  Armada_NextMultipleSteps(asf, states[0], last(states), steps)
  {
    if |steps| > 0 {
      lemma_IfAllStepsValidThenArmadaNextMultipleSteps(asf, states[1..], steps[1..]);
    }
  }

}
