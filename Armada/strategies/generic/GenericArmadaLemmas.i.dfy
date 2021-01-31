include "GenericArmadaSpec.i.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"

module GenericArmadaLemmasModule {

  import opened util_collections_seqs_s
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened GenericArmadaSpecModule

  lemma lemma_BehaviorToAnnotatedBehavior<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    b:seq<State>
    ) returns (
    ab:AnnotatedBehavior<State, Armada_Multistep<OneStep>>
    )
    requires BehaviorSatisfiesSpec(b, Armada_SpecFunctionsToSpec(asf))
    ensures  AnnotatedBehaviorSatisfiesSpec(ab, SpecFunctionsToAnnotatedSpec(asf))
    ensures  ab.states == b
  {
    var spec := Armada_SpecFunctionsToSpec(asf);
    var aspec := SpecFunctionsToAnnotatedSpec(asf);
    var pos := 0;
    var trace := [];
    while pos < |b|-1
      invariant pos == |trace|
      invariant pos < |b|
      invariant AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(b[..pos+1], trace), aspec)
    {
      var s := b[pos];
      var s' := b[pos+1];
      assert StatePair(s, s') in spec.next;
      var steps, tid, tau :| Armada_NextMultistep(asf, s, s', steps, tid, tau);
      var multistep := Armada_Multistep(steps, tid, tau);
      assert StatePair(b[pos], b[pos+1]) in spec.next;
      lemma_ExtendStateNextSeqRight(b[..pos+1], trace, aspec.next, b[pos+1], multistep);
      assert b[..(pos+1)+1] == b[..pos+1] + [b[pos+1]];
      trace := trace + [multistep];
      pos := pos + 1;
    }
    return AnnotatedBehavior(b, trace);
  }

  lemma lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    ab:AnnotatedBehavior<State, Armada_Multistep<OneStep>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(ab, SpecFunctionsToAnnotatedSpec(asf))
    ensures  BehaviorSatisfiesSpec(ab.states, Armada_SpecFunctionsToSpec(asf))
  {
    var aspec := SpecFunctionsToAnnotatedSpec(asf);
    var spec := Armada_SpecFunctionsToSpec(asf);
    forall pos | 0 <= pos < |ab.states|-1
      ensures StatePair(ab.states[pos], ab.states[pos+1]) in spec.next
    {
      assert ActionTuple(ab.states[pos], ab.states[pos+1], ab.trace[pos]) in aspec.next;
    }
  }

  lemma lemma_ExtendArmadaNextMultipleSteps<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    s'': State,
    steps: seq<OneStep>,
    step: OneStep,
    tid: Armada_ThreadHandle
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps, tid)
    requires asf.step_valid(s', step, tid)
    requires s'' == asf.step_next(s', step, tid)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps + [step], tid)
    decreases |steps|
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0], tid);
      lemma_ExtendArmadaNextMultipleSteps(asf, s_next, s', s'', steps[1..], step, tid);
      var all_steps := steps + [step];
      assert all_steps[0] == steps[0];
      assert all_steps[1..] == steps[1..] + [step];
      assert Armada_NextMultipleSteps(asf, s_next, s'', all_steps[1..], tid);
    }
  }

  lemma lemma_ExtendArmadaStepsStartNonyielding<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    s'': State,
    steps: seq<OneStep>,
    step: OneStep,
    tid: Armada_ThreadHandle
    )
    requires Armada_StepsStartNonyielding(asf, s, s', steps, tid)
    requires Armada_NextMultipleSteps(asf, s, s', steps, tid)
    requires !Armada_ThreadYielding(asf, s', tid)
    requires !asf.is_step_tau(step)
    requires asf.step_valid(s', step, tid)
    requires s'' == asf.step_next(s', step, tid)
    ensures  Armada_StepsStartNonyielding(asf, s, s'', steps + [step], tid)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps + [step], tid)
    decreases |steps|
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0], tid);
      lemma_ExtendArmadaStepsStartNonyielding(asf, s_next, s', s'', steps[1..], step, tid);
      var all_steps := steps + [step];
      assert all_steps[0] == steps[0];
      assert all_steps[1..] == steps[1..] + [step];
      assert Armada_StepsStartNonyielding(asf, s_next, s'', all_steps[1..], tid);
      assert Armada_StepsStartNonyielding(asf, s, s'', steps + [step], tid);
      assert Armada_NextMultipleSteps(asf, s, s'', steps + [step], tid);
    }
    else {
      assert Armada_StepsStartNonyielding(asf, s, s'', steps + [step], tid);
      assert Armada_NextMultipleSteps(asf, s, s'', steps + [step], tid);
    }
  }

  lemma lemma_CombineArmadaNextMultipleSteps<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    s'': State,
    steps1: seq<OneStep>,
    steps2: seq<OneStep>,
    tid: Armada_ThreadHandle
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps1, tid)
    requires Armada_NextMultipleSteps(asf, s', s'', steps2, tid)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps1 + steps2, tid)
    decreases |steps2|
  {
    if |steps2| == 0 {
      assert s'' == s';
      assert steps1 + steps2 == steps1;
      return;
    }

    var s_next := asf.step_next(s', steps2[0], tid);
    lemma_ExtendArmadaNextMultipleSteps(asf, s, s', s_next, steps1, steps2[0], tid);
    lemma_CombineArmadaNextMultipleSteps(asf, s, s_next, s'', steps1 + [steps2[0]], steps2[1..], tid);

    calc {
      steps1 + steps2;
      steps1 + ([steps2[0]] + steps2[1..]);
      (steps1 + [steps2[0]]) + steps2[1..];
    }
  }

  lemma lemma_CombineArmadaStepsStartNonyielding<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    s'': State,
    steps1: seq<OneStep>,
    steps2: seq<OneStep>,
    tid: Armada_ThreadHandle
    )
    requires Armada_StepsStartNonyielding(asf, s, s', steps1, tid)
    requires Armada_NextMultipleSteps(asf, s, s', steps1, tid)
    requires Armada_StepsStartNonyielding(asf, s', s'', steps2, tid)
    requires Armada_NextMultipleSteps(asf, s', s'', steps2, tid)
    ensures  Armada_StepsStartNonyielding(asf, s, s'', steps1 + steps2, tid)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps1 + steps2, tid)
    decreases |steps2|
  {
    if |steps2| == 0 {
      assert s'' == s';
      assert steps1 + steps2 == steps1;
      return;
    }

    var s_next := asf.step_next(s', steps2[0], tid);
    lemma_ExtendArmadaStepsStartNonyielding(asf, s, s', s_next, steps1, steps2[0], tid);
    lemma_CombineArmadaStepsStartNonyielding(asf, s, s_next, s'', steps1 + [steps2[0]], steps2[1..], tid);

    calc {
      steps1 + steps2;
      steps1 + ([steps2[0]] + steps2[1..]);
      (steps1 + [steps2[0]]) + steps2[1..];
    }
  }

}
