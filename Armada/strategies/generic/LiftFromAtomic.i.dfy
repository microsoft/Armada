include "GenericArmadaAtomic.i.dfy"

module LiftFromAtomicModule
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
  // LIFTING FROM ATOMIC
  //////////////////////////////////////////////

  predicate AtomicLiftPathFromAtomicPossible<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    path: Path,
    tid: Armada_ThreadHandle
    )
  {
    && asf.path_valid(s, path, tid)
    && s' == asf.path_next(s, path, tid)
  }

  predicate AtomicStepsLiftPathFromAtomic<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    startsYielding: bool,
    mustEndYielding: bool,
    ok: bool
    )
  {
    && |steps| > 0
    && !asf.is_step_tau(steps[0])
    && (startsYielding == Armada_ThreadYielding(asf, s, tid))
    && (mustEndYielding ==> Armada_ThreadYielding(asf, s', tid))
    && Armada_StepsStartNonyielding(asf, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
    && asf.state_ok(s') == ok
  }

  predicate AtomicLiftPathFromAtomicSuccessful<State, OneStep, Path, PC>(
    lasf: AtomicSpecFunctions<State, Path, PC>,
    hasf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    path: Path,
    tid: Armada_ThreadHandle,
    steps: seq<OneStep>
    )
  {
    && Armada_NextMultipleSteps(hasf, s, s', steps, tid)
    && match lasf.path_type(path)
        case AtomicPathType_Tau => |steps| == 1 && hasf.is_step_tau(steps[0])
        case AtomicPathType_YY  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, true, true, true)
        case AtomicPathType_YS  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, true, true, false)
        case AtomicPathType_YR  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, true, false, true)
        case AtomicPathType_RY  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, true, true)
        case AtomicPathType_RS  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, true, false)
        case AtomicPathType_RR  => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, false, true)
  }
  lemma lemma_LiftRecurrentEntryFromAtomic<State, OneStep, Path, PC>(
    lasf: AtomicSpecFunctions<State, Path, PC>,
    hasf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    tid: Armada_ThreadHandle,
    yr: Path,
    rrs: seq<Path>,
    rx: Path
    ) returns (
    hsteps: seq<OneStep>
    )
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires AtomicValidRecursiveStep(lasf, s, tid, yr, rrs, rx)
    requires s' == lasf.path_next(AtomicGetStateAfterPaths(lasf, lasf.path_next(s, yr, tid), rrs, tid), rx, tid)
    requires forall ls, ls', path :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path, tid) ==>
               exists hsteps' :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, tid, hsteps')
    ensures  Armada_NextMultistep(hasf, s, s', hsteps, tid, false)
  {
    var ls1 := lasf.path_next(s, yr, tid);
    assert AtomicLiftPathFromAtomicPossible(lasf, s, ls1, yr, tid);
    var hsteps_yr :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, ls1, yr, tid, hsteps_yr);

    var hstep0 := hsteps_yr[0];
    var hsteps_current := hsteps_yr[1..];
    var s_next := hasf.step_next(s, hstep0, tid);

    var current_state := ls1;
    var rrs_remaining := rrs;
    var ls2 := AtomicGetStateAfterPaths(lasf, ls1, rrs, tid);

    while |rrs_remaining| > 0
      invariant AtomicValidPathSequence(lasf, current_state, rrs_remaining, tid)
      invariant ls2 == AtomicGetStateAfterPaths(lasf, current_state, rrs_remaining, tid)
      invariant Armada_StepsStartNonyielding(hasf, s_next, current_state, hsteps_current, tid)
      invariant Armada_NextMultipleSteps(hasf, s_next, current_state, hsteps_current, tid)
    {
      var next_state := lasf.path_next(current_state, rrs_remaining[0], tid);
      assert AtomicLiftPathFromAtomicPossible(lasf, current_state, next_state, rrs_remaining[0], tid);
      var hsteps_next :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, current_state, next_state, rrs_remaining[0], tid, hsteps_next);

      lemma_CombineArmadaStepsStartNonyielding(hasf, s_next, current_state, next_state, hsteps_current, hsteps_next, tid);
      assert Armada_StepsStartNonyielding(hasf, s_next, next_state, hsteps_current + hsteps_next, tid);

      hsteps_current := hsteps_current + hsteps_next;
      rrs_remaining := rrs_remaining[1..];
      current_state := next_state;
    }

    assert current_state == ls2;

    assert AtomicLiftPathFromAtomicPossible(lasf, ls2, s', rx, tid);
    var hsteps_next :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls2, s', rx, tid, hsteps_next);

    lemma_CombineArmadaStepsStartNonyielding(hasf, s_next, ls2, s', hsteps_current, hsteps_next, tid);

    assert Armada_StepsStartNonyielding(hasf, s_next, s', hsteps_current + hsteps_next, tid);
    assert Armada_NextMultipleSteps(hasf, s_next, s', hsteps_current + hsteps_next, tid);

    hsteps := [hstep0] + (hsteps_current + hsteps_next);
    assert hsteps[0] == hstep0;
    assert hsteps[1..] == hsteps_current + hsteps_next;
    assert Armada_NextMultistep(hasf, s, s', hsteps, tid, false);
  }

  lemma lemma_LiftEntryFromAtomic<State, OneStep, Path, PC>(
    lasf: AtomicSpecFunctions<State, Path, PC>,
    hasf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    lentry: AtomicTraceEntry<Path>
    ) returns (
    hsteps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    tau: bool
    )
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires AtomicNext(lasf, s, s', lentry)
    requires forall ls, ls', path, tid :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path, tid) ==>
               exists hsteps' :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, tid, hsteps')
    ensures  Armada_NextMultistep(hasf, s, s', hsteps, tid, tau)
  {
    match lentry
    {
      case AtomicTraceEntry_Stutter =>
        hsteps := [];
        // No need to set tid, since the tid used for a stutter can be arbitrary.
        tau := false;

      case AtomicTraceEntry_Tau(tau_tid, path) =>
        tid := tau_tid;
        assert AtomicLiftPathFromAtomicPossible(lasf, s, s', path, tid);
        hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, tid, hsteps);
        tau := true;

      case AtomicTraceEntry_Normal(normal_tid, path) =>
        tid := normal_tid;
        assert AtomicLiftPathFromAtomicPossible(lasf, s, s', path, tid);
        hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, tid, hsteps);
        tau := false;

      case AtomicTraceEntry_Recurrent(entry_tid, yr, rrs, rx) =>
        tid := entry_tid;
        hsteps := lemma_LiftRecurrentEntryFromAtomic(lasf, hasf, s, s', tid, yr, rrs, rx);
        tau := false;
    }
  }

  lemma lemma_LiftBehaviorFromAtomic<State, OneStep, Path, PC>(
    lasf: AtomicSpecFunctions<State, Path, PC>,
    hasf: Armada_SpecFunctions<State, OneStep, PC>,
    b: seq<State>
    )
    requires BehaviorSatisfiesSpec(b, AtomicSpec(lasf))
    requires forall s :: lasf.init(s) ==> hasf.init(s)
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires forall ls, ls', path, tid :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path, tid) ==>
               exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, tid, hsteps)
    ensures  BehaviorSatisfiesSpec(b, Armada_SpecFunctionsToSpec(hasf))
  {
    var lspec := AtomicSpec(lasf);
    var hspec := Armada_SpecFunctionsToSpec(hasf);

    forall i {:trigger StatePair(b[i], b[i + 1]) in hspec.next} | 0 <= i < |b| - 1
      ensures StatePair(b[i], b[i + 1]) in hspec.next
    {
      assert StatePair(b[i], b[i + 1]) in lspec.next;
      var lentry :| AtomicNext(lasf, b[i], b[i + 1], lentry);
      var hsteps, tid, tau := lemma_LiftEntryFromAtomic(lasf, hasf, b[i], b[i + 1], lentry);
      assert StatePair(b[i], b[i + 1]) in hspec.next;
    }
  }

  lemma lemma_AtomicSpecRefinesSpec<State, OneStep, Path, PC>(
    lasf: AtomicSpecFunctions<State, Path, PC>,
    hasf: Armada_SpecFunctions<State, OneStep, PC>
    ) returns (
    refinement_relation: RefinementRelation<State, State>
    )
    requires forall s :: lasf.init(s) ==> hasf.init(s)
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires forall ls, ls', path, tid :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path, tid) ==>
               exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, tid, hsteps)
    ensures  SpecRefinesSpec(AtomicSpec(lasf), Armada_SpecFunctionsToSpec(hasf), refinement_relation)
    ensures  refinement_relation == iset s | true :: RefinementPair(s, s)
  {
    refinement_relation := iset s | true :: RefinementPair(s, s);
    forall lb | BehaviorSatisfiesSpec(lb, AtomicSpec(lasf))
      ensures BehaviorRefinesSpec(lb, Armada_SpecFunctionsToSpec(hasf), refinement_relation)
    {
      lemma_LiftBehaviorFromAtomic(lasf, hasf, lb);
      lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself(lb, refinement_relation);
      assert BehaviorRefinesBehavior(lb, lb, refinement_relation) && BehaviorSatisfiesSpec(lb, Armada_SpecFunctionsToSpec(hasf));
    }
  }

}
