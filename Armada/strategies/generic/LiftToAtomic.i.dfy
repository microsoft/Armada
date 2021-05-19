include "GenericArmadaAtomic.i.dfy"

module LiftToAtomicModule
{
  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GenericArmadaSpecModule
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened InvariantsModule
  import opened GenericArmadaLemmasModule
  import opened GenericArmadaAtomicModule

  //////////////////////////////////////////////
  // LIFTING TO ATOMIC
  //////////////////////////////////////////////

  predicate ThreadYieldingOrRecurrent<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    tid: Armada_ThreadHandle
    )
  {
    Armada_ThreadYielding(asf, s, tid) || is_recurrent_pc(asf.get_thread_pc(s, tid).v)
  }

  predicate LInitImpliesHInit<State(!new), OneStep, Path, PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s :: lasf.init(s) ==> hasf.init(s)
  }

  predicate StateOKsMatch<State(!new), OneStep, Path, PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s :: lasf.state_ok(s) == hasf.state_ok(s)
  }

  predicate NonyieldingPCsMatch<State, OneStep, Path, PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall pc :: lasf.is_pc_nonyielding(pc) <==> hasf.is_pc_nonyielding(pc)
  }

  predicate ThreadPCsMatch<State(!new), OneStep, Path, PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, tid :: lasf.get_thread_pc(s, tid) == hasf.get_thread_pc(s, tid)
  }

  predicate TausLiftableConditions<State(!new), OneStep(!new), PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    step: OneStep,
    tid: Armada_ThreadHandle
    )
  {
    && lasf.step_valid(s, step, tid)
    && s' == lasf.step_next(s, step, tid)
    && lasf.is_step_tau(step)
  }

  predicate TausLiftable<State(!new), OneStep(!new), Path(!new), PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, s', lstep, tid {:trigger TausLiftableConditions(lasf, s, s', lstep, tid)} ::
      TausLiftableConditions(lasf, s, s', lstep, tid)
      ==> exists hpath ::
            && hasf.path_valid(s, hpath, tid)
            && hasf.path_type(hpath).AtomicPathType_Tau? 
            && s' == hasf.path_next(s, hpath, tid)
  }

  predicate SequencesCompressibleConditions<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    )
  {
    && |steps| > 0
    && !asf.is_step_tau(steps[0])
    && asf.step_valid(s, steps[0], tid)
    && ThreadYieldingOrRecurrent(asf, is_recurrent_pc, s, tid)
    && ThreadYieldingOrRecurrent(asf, is_recurrent_pc, s', tid)
    && StepsStartNonyieldingNonrecurrent(asf, is_recurrent_pc, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
  }

  predicate SequencesCompressibleConclusions<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    tid: Armada_ThreadHandle,
    path: Path
    )
  {
    && asf.path_valid(s, path, tid)
    && s' == asf.path_next(s, path, tid)
    && !asf.path_type(path).AtomicPathType_Tau?
    && AtomicPathTypeMatchesPCTypes(asf, s, path, tid)
  }

  predicate SequencesCompressible<State(!new), OneStep(!new), Path(!new), PC>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool
    )
  {
    forall s, s', lsteps, tid {:trigger SequencesCompressibleConditions(lasf, is_recurrent_pc, s, s', lsteps, tid)} ::
      SequencesCompressibleConditions(lasf, is_recurrent_pc, s, s', lsteps, tid)
      ==> exists hpath :: SequencesCompressibleConclusions(hasf, s, s', tid, hpath)
  }

  predicate RequirementsForLiftingToAtomic<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool
    )
  {
    && LInitImpliesHInit(lasf, hasf)
    && StateOKsMatch(lasf, hasf)
    && NonyieldingPCsMatch(lasf, hasf)
    && ThreadPCsMatch(lasf, hasf)
    && TausLiftable(lasf, hasf)
    && SequencesCompressible(lasf, hasf, is_recurrent_pc)
  }

  predicate StepsEndNonyieldingNonrecurrent<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    )
  {
    if |steps| == 0 then
      s' == s
    else
      var s_next := asf.step_next(s, steps[0], tid);
      && !Armada_ThreadYielding(asf, s_next, tid)
      && !is_recurrent_pc(asf.get_thread_pc(s_next, tid).v)
      && !asf.is_step_tau(steps[0])
      && StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s_next, s', steps[1..], tid)
  }

  predicate StepsStartNonyieldingNonrecurrent<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    )
  {
    if |steps| == 0 then
      s' == s
    else
      var s_next := asf.step_next(s, steps[0], tid);
      && asf.step_valid(s, steps[0], tid)
      && !Armada_ThreadYielding(asf, s, tid)
      && !is_recurrent_pc(asf.get_thread_pc(s, tid).v)
      && !asf.is_step_tau(steps[0])
      && StepsStartNonyieldingNonrecurrent(asf, is_recurrent_pc, s_next, s', steps[1..], tid)
  }

  lemma lemma_ExtendStepsEndNonyieldingNonrecurrent<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    s'': State,
    steps: seq<OneStep>,
    step: OneStep,
    tid: Armada_ThreadHandle
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps, tid)
    requires StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s, s', steps, tid)
    requires !asf.is_step_tau(step)
    requires asf.step_valid(s', step, tid)
    requires s'' == asf.step_next(s', step, tid)
    requires !Armada_ThreadYielding(asf, s'', tid)
    requires !is_recurrent_pc(asf.get_thread_pc(s'', tid).v)
    ensures  Armada_NextMultipleSteps(asf, s, s'', steps + [step], tid)
    ensures  StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s, s'', steps + [step], tid);
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0], tid);
      lemma_ExtendStepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s_next, s', s'', steps[1..], step, tid);
      var all_steps := steps + [step];
      assert all_steps[0] == steps[0];
      assert all_steps[1..] == steps[1..] + [step];
      assert StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s_next, s'', all_steps[1..], tid);
      assert StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s, s'', all_steps, tid);
    }
  }

  lemma lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    s'': State,
    steps: seq<OneStep>,
    step: OneStep,
    tid: Armada_ThreadHandle
    )
    requires Armada_NextMultipleSteps(asf, s, s', steps, tid)
    requires StepsEndNonyieldingNonrecurrent(asf, is_recurrent_pc, s, s', steps, tid)
    requires !asf.is_step_tau(step)
    requires asf.step_valid(s', step, tid)
    requires s'' == asf.step_next(s', step, tid)
    ensures  var new_steps := steps + [step];
             StepsStartNonyieldingNonrecurrent(asf, is_recurrent_pc, asf.step_next(s, new_steps[0], tid), s'', new_steps[1..], tid)
  {
    if |steps| == 0 {
      return;
    }

    var s_next := asf.step_next(s, steps[0], tid);
    lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding(asf, is_recurrent_pc, s_next, s', s'', steps[1..], step, tid);
    var new_steps := steps + [step];
    assert new_steps[0] == steps[0];
    assert new_steps[1..] == steps[1..] + [step];
  }

  lemma lemma_ExtendAtomicValidPathSequence<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    s'': State,
    rrs: seq<Path>,
    rr: Path,
    tid: Armada_ThreadHandle
    )
    requires AtomicValidPathSequence(asf, s, rrs, tid)
    requires s' == AtomicGetStateAfterPaths(asf, s, rrs, tid)
    requires asf.path_valid(s', rr, tid)
    requires s'' == asf.path_next(s', rr, tid)
    requires asf.path_type(rr).AtomicPathType_RR?
    ensures  AtomicValidPathSequence(asf, s, rrs + [rr], tid)
    ensures  s'' == AtomicGetStateAfterPaths(asf, s, rrs + [rr], tid)
  {
    if |rrs| > 0 {
      var s_next := asf.path_next(s, rrs[0], tid);
      lemma_ExtendAtomicValidPathSequence(asf, s_next, s', s'', rrs[1..], rr, tid);
      assert (rrs + [rr])[0] == rrs[0];
      assert (rrs + [rr])[1..] == rrs[1..] + [rr];
    }
  }

  lemma lemma_LiftMultistepToAtomicGivenYRRRs<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    pos_after_rrs: int,
    pos_mid: int,
    yr: Path,
    rrs: seq<Path>,
    state_after_yr: State,
    state_after_rrs: State,
    s_mid: State
    ) returns (
    entry: AtomicTraceEntry<Path>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    requires 0 <= pos_after_rrs <= pos_mid < |steps|
    requires hasf.path_type(yr).AtomicPathType_YR?
    requires state_after_yr == hasf.path_next(s, yr, tid)
    requires state_after_rrs == AtomicGetStateAfterPaths(hasf, state_after_yr, rrs, tid)
    requires hasf.path_valid(s, yr, tid)
    requires AtomicValidPathSequence(hasf, state_after_yr, rrs, tid)
    requires Armada_NextMultipleSteps(lasf, state_after_rrs, s_mid, steps[pos_after_rrs..pos_mid], tid)
    requires Armada_NextMultipleSteps(lasf, s_mid, s', steps[pos_mid..], tid)
    requires StepsEndNonyieldingNonrecurrent(lasf, is_recurrent_pc, state_after_rrs, s_mid, steps[pos_after_rrs..pos_mid], tid)
    requires Armada_NextMultipleSteps(lasf, state_after_rrs, s', steps[pos_after_rrs..], tid)
    requires Armada_StepsStartNonyielding(lasf, s_mid, s', steps[pos_mid..], tid)
    requires Armada_NextMultipleSteps(lasf, s_mid, s', steps[pos_mid..], tid)
    requires Armada_StepsStartNonyielding(lasf, s_mid, s', steps[pos_mid..], tid)
    requires !Armada_ThreadYielding(lasf, state_after_rrs, tid)
    requires is_recurrent_pc(lasf.get_thread_pc(state_after_rrs, tid).v)
    requires Armada_ThreadYielding(lasf, s', tid)
    ensures  AtomicNext(hasf, s, s', entry)
    decreases |steps| - pos_mid
  {
    var s_next := lasf.step_next(s_mid, steps[pos_mid], tid);
    if pos_mid == |steps|-1 {
      assert s_next == s';
      lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding(lasf, is_recurrent_pc, state_after_rrs, s_mid, s_next,
                                                                             steps[pos_after_rrs..pos_mid], steps[pos_mid], tid);
      assert steps[pos_after_rrs..pos_mid] + [steps[pos_mid]] == steps[pos_after_rrs..];
      assert SequencesCompressibleConditions(lasf, is_recurrent_pc, state_after_rrs, s', steps[pos_after_rrs..], tid);
      var rx :| SequencesCompressibleConclusions(hasf, state_after_rrs, s', tid, rx);
      entry := AtomicTraceEntry_Recurrent(tid, yr, rrs, rx);
      assert AtomicValidRecursiveStep(hasf, s, tid, yr, rrs, rx);
      return;
    }

    assert !Armada_ThreadYielding(lasf, s_next, tid);
    assert steps[pos_after_rrs..pos_mid+1] == steps[pos_after_rrs..pos_mid] + [steps[pos_mid]];
    var pc := lasf.get_thread_pc(s_next, tid).v;
    if !is_recurrent_pc(pc) {
      lemma_ExtendStepsEndNonyieldingNonrecurrent(lasf, is_recurrent_pc, state_after_rrs, s_mid, s_next, steps[pos_after_rrs..pos_mid],
                                                  steps[pos_mid], tid);
      entry := lemma_LiftMultistepToAtomicGivenYRRRs(lasf, hasf, is_recurrent_pc, s, s', steps, tid, pos_after_rrs, pos_mid + 1, yr, rrs,
                                                     state_after_yr, state_after_rrs, s_next);
      return;
    }

    lemma_ExtendArmadaNextMultipleSteps(lasf, state_after_rrs, s_mid, s_next, steps[pos_after_rrs..pos_mid], steps[pos_mid], tid);
    lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding(lasf, is_recurrent_pc, state_after_rrs, s_mid, s_next,
                                                                           steps[pos_after_rrs..pos_mid], steps[pos_mid], tid);
    assert SequencesCompressibleConditions(lasf, is_recurrent_pc, state_after_rrs, s_next, steps[pos_after_rrs..pos_mid+1], tid);
    var rr :| SequencesCompressibleConclusions(hasf, state_after_rrs, s_next, tid, rr);
    lemma_ExtendAtomicValidPathSequence(hasf, state_after_yr, state_after_rrs, s_next, rrs, rr, tid);
    entry := lemma_LiftMultistepToAtomicGivenYRRRs(lasf, hasf, is_recurrent_pc, s, s', steps, tid,
                                                   pos_mid + 1, pos_mid + 1, yr, rrs + [rr], state_after_yr, s_next, s_next);
  }

  lemma lemma_LiftMultistepToAtomicGivenInitialSteps<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    pos: int,
    s_mid: State
    ) returns (
    entry: AtomicTraceEntry<Path>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    requires 0 <= pos < |steps|
    requires Armada_NextMultipleSteps(lasf, s, s_mid, steps[..pos], tid)
    requires Armada_NextMultipleSteps(lasf, s_mid, s', steps[pos..], tid)
    requires !lasf.is_step_tau(steps[pos])
    requires lasf.step_valid(s_mid, steps[pos], tid)
    requires StepsEndNonyieldingNonrecurrent(lasf, is_recurrent_pc, s, s_mid, steps[..pos], tid)
    requires Armada_StepsStartNonyielding(lasf, lasf.step_next(s_mid, steps[pos], tid), s', steps[pos+1..], tid)
    requires Armada_ThreadYielding(lasf, s, tid)
    requires Armada_ThreadYielding(lasf, s', tid)
    ensures  AtomicNext(hasf, s, s', entry)
    decreases |steps| - pos
  {
    var s_next := lasf.step_next(s_mid, steps[pos], tid);
    if pos == |steps|-1 {
      assert s_next == s';
      lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding(lasf, is_recurrent_pc, s, s_mid, s_next, steps[..pos],
                                                                             steps[pos], tid);
      assert steps == steps[..pos] + [steps[pos]];
      assert SequencesCompressibleConditions(lasf, is_recurrent_pc, s, s', steps, tid);
      var hpath :| SequencesCompressibleConclusions(hasf, s, s', tid, hpath);
      entry := AtomicTraceEntry_Normal(tid, hpath);
      return;
    }

    assert !Armada_ThreadYielding(lasf, s_next, tid);
    assert steps[..pos+1] == steps[..pos] + [steps[pos]];
    var pc := lasf.get_thread_pc(s_next, tid).v;
    if !is_recurrent_pc(pc) {
      lemma_ExtendStepsEndNonyieldingNonrecurrent(lasf, is_recurrent_pc, s, s_mid, s_next, steps[..pos], steps[pos], tid);
      entry := lemma_LiftMultistepToAtomicGivenInitialSteps(lasf, hasf, is_recurrent_pc, s, s', steps, tid, pos + 1, s_next);
      return;
    }

    lemma_ExtendArmadaNextMultipleSteps(lasf, s, s_mid, s_next, steps[..pos], steps[pos], tid);
    lemma_IfStepsEndNonyieldingNonrecurrentThenShiftedTheyStartNonyielding(lasf, is_recurrent_pc, s, s_mid, s_next, steps[..pos],
                                                                           steps[pos], tid);
    assert steps[..pos] + [steps[pos]] == steps[..pos+1];
    assert SequencesCompressibleConditions(lasf, is_recurrent_pc, s, s_next, steps[..pos+1], tid);
    var yr :| SequencesCompressibleConclusions(hasf, s, s_next, tid, yr);
    entry := lemma_LiftMultistepToAtomicGivenYRRRs(lasf, hasf, is_recurrent_pc, s, s', steps, tid,
                                                   pos + 1, pos + 1, yr, [], s_next, s_next, s_next);
  }

  lemma lemma_LiftMultistepToAtomicRegular<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    ) returns (
    entry: AtomicTraceEntry<Path>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    requires |steps| > 0
    requires !lasf.is_step_tau(steps[0])
    requires Armada_ThreadYielding(lasf, s, tid)
    requires Armada_ThreadYielding(lasf, s', tid)
    requires Armada_NextMultipleSteps(lasf, s, s', steps, tid)
    requires Armada_StepsStartNonyielding(lasf, lasf.step_next(s, steps[0], tid), s', steps[1..], tid)
    ensures  AtomicNext(hasf, s, s', entry)
  {
    entry := lemma_LiftMultistepToAtomicGivenInitialSteps(lasf, hasf, is_recurrent_pc, s, s', steps, tid, 0, s);
  }

  lemma lemma_LiftMultistepToAtomic<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    tau: bool
    ) returns (
    entry: AtomicTraceEntry<Path>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    requires Armada_NextMultistep(lasf, s, s', steps, tid, tau)
    ensures  AtomicNext(hasf, s, s', entry)
  {
    if |steps| == 0 {
      entry := AtomicTraceEntry_Stutter();
    }
    else if tau {
      assert Armada_NextMultipleSteps(lasf, lasf.step_next(s, steps[0], tid), s', steps[1..], tid);
      assert TausLiftableConditions(lasf, s, s', steps[0], tid);
      var hpath :| && hasf.path_valid(s, hpath, tid)
                   && hasf.path_type(hpath).AtomicPathType_Tau? 
                   && s' == hasf.path_next(s, hpath, tid);
      entry := AtomicTraceEntry_Tau(tid, hpath);
    }
    else {
      entry := lemma_LiftMultistepToAtomicRegular(lasf, hasf, is_recurrent_pc, s, s', steps, tid);
    }
  }

  lemma lemma_LiftToAtomic<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool,
    b: seq<State>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    requires BehaviorSatisfiesSpec(b, Armada_SpecFunctionsToSpec(lasf))
    ensures  BehaviorSatisfiesSpec(b, AtomicSpec(hasf))
    decreases |b|
  {
    forall pos | 0 <= pos < |b|-1
      ensures StatePair(b[pos], b[pos+1]) in AtomicSpec(hasf).next
    {
      var s := b[pos];
      var s' := b[pos+1];
      assert StatePair(s, s') in Armada_SpecFunctionsToSpec(lasf).next;
      var steps, tid, tau :| Armada_NextMultistep(lasf, s, s', steps, tid, tau);
      var entry := lemma_LiftMultistepToAtomic(lasf, hasf, is_recurrent_pc, s, s', steps, tid, tau);
    }
  }

  lemma lemma_SpecRefinesAtomicSpec<State(!new), OneStep(!new), Path(!new), PC(!new)>(
    lasf: Armada_SpecFunctions<State, OneStep, PC>,
    hasf: AtomicSpecFunctions<State, Path, PC>,
    is_recurrent_pc: PC->bool
    ) returns (
    refinement_relation: RefinementRelation<State, State>
    )
    requires RequirementsForLiftingToAtomic(lasf, hasf, is_recurrent_pc)
    ensures  SpecRefinesSpec(Armada_SpecFunctionsToSpec(lasf), AtomicSpec(hasf), refinement_relation)
    ensures  refinement_relation == iset s: State | true :: RefinementPair(s, s)
  {
    refinement_relation := iset s: State | true :: RefinementPair(s, s);

    forall lb | BehaviorSatisfiesSpec(lb, Armada_SpecFunctionsToSpec(lasf))
      ensures exists hb :: BehaviorRefinesBehavior(lb, hb, refinement_relation) && BehaviorSatisfiesSpec(hb, AtomicSpec(hasf))
    {
      lemma_LiftToAtomic(lasf, hasf, is_recurrent_pc, lb);
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb, refinement_relation);
      assert BehaviorRefinesBehavior(lb, lb, refinement_relation);
      assert BehaviorSatisfiesSpec(lb, AtomicSpec(hasf));
    }
  }
}
