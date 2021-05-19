include "GenericArmadaAtomic.i.dfy"

module LiftAtomicToAtomicModule
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
  // LIFTING BETWEEN TWO ATOMIC SPECS
  //////////////////////////////////////////////

  predicate LiftAtomicPathSuccessful<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    ls: LState,
    lpath: LPath,
    tid: Armada_ThreadHandle,
    hs: HState,
    hpath: HPath
    )
  {
    var ls' := lasf.path_next(ls, lpath, tid);
    var hs' := hasf.path_next(hs, hpath, tid);
    && inv(ls')
    && hasf.path_valid(hs, hpath, tid)
    && relation(ls', hs')
    && hasf.path_type(hpath) == lasf.path_type(lpath)
    && lasf.state_ok(ls') == hasf.state_ok(hs')
  }

  predicate LiftAtomicTraceEntrySuccessful<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    ls: LState,
    lentry: AtomicTraceEntry<LPath>,
    hs: HState,
    hentry: AtomicTraceEntry<HPath>
    )
  {
    var ls' := AtomicGetNextStateAlways(lasf, ls, lentry);
    && inv(ls')
    && AtomicValidStep(hasf, hs, hentry)
    && relation(ls', AtomicGetNextStateAlways(hasf, hs, hentry))
  }

  predicate AtomicPathSkippable<LState, LPath, LPC, HState>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    ls: LState,
    lpath: LPath,
    tid: Armada_ThreadHandle,
    hs: HState
    )
  {
    var ls' := lasf.path_next(ls, lpath, tid);
    var ty := lasf.path_type(lpath);
    && inv(ls')
    && relation(ls', hs)
    && lasf.state_ok(ls')
    && (ty.AtomicPathType_Tau? || ty.AtomicPathType_YY? || ty.AtomicPathType_YS? || ty.AtomicPathType_RR?)
  }

  predicate ProgressMade(value: (int, int), value': (int, int))
  {
    var (x, y) := value;
    var (x', y') := value';
    && 0 <= x
    && 0 <= x'
    && 0 <= y
    && 0 <= y'
    && (x' < x || (x' == x && y' < y))
  }

  predicate AtomicPathIntroduced<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    ls: LState,
    lpath: LPath,
    tid: Armada_ThreadHandle,
    hs: HState,
    hpath: HPath
    )
  {
    var lty := lasf.path_type(lpath);
    var hty := hasf.path_type(hpath);
    var hs' := hasf.path_next(hs, hpath, tid);
    && hasf.path_valid(hs, hpath, tid)
    && relation(ls, hs')
    && hasf.state_ok(hs')
    && ProgressMade(progress_measure(hs, lpath, tid), progress_measure(hs', lpath, tid))
    && match lty
        case AtomicPathType_Tau => hty.AtomicPathType_Tau?
        case AtomicPathType_YY => hty.AtomicPathType_YY? || hty.AtomicPathType_Tau?
        case AtomicPathType_YS => hty.AtomicPathType_YY? || hty.AtomicPathType_Tau?
        case AtomicPathType_YR => hty.AtomicPathType_YY? || hty.AtomicPathType_Tau?
        case AtomicPathType_RY => hty.AtomicPathType_RR?
        case AtomicPathType_RS => hty.AtomicPathType_RR?
        case AtomicPathType_RR => hty.AtomicPathType_RR?
  }

  function GetTraceEntryProgressMeasure<LPath, HState>(
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    hs: HState,
    entry: AtomicTraceEntry<LPath>
    ) : (int, int)
  {
    match entry
      case AtomicTraceEntry_Stutter() => (0, 0)
      case AtomicTraceEntry_Tau(tid, path) => progress_measure(hs, path, tid)
      case AtomicTraceEntry_Normal(tid, path) => progress_measure(hs, path, tid)
      case AtomicTraceEntry_Recurrent(tid, yr, _, _) => progress_measure(hs, yr, tid)
  }

  predicate IntroduceAtomicTraceEntrySuccessful<LState, LPath, HState, HPath, HPC>(
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    ls: LState,
    lentry: AtomicTraceEntry<LPath>,
    hs: HState,
    hentry: AtomicTraceEntry<HPath>
    )
  {
    var hs' := AtomicGetNextStateAlways(hasf, hs, hentry);
    && AtomicValidStep(hasf, hs, hentry)
    && relation(ls, hs')
    && ProgressMade(GetTraceEntryProgressMeasure(progress_measure, hs, lentry),
                   GetTraceEntryProgressMeasure(progress_measure, hs', lentry))
  }

  lemma lemma_LiftPathSequenceGivenAtomicPathsLiftable<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    ls: LState,
    tid: Armada_ThreadHandle,
    lpaths: seq<LPath>,
    hs: HState
    ) returns (
    hpaths: seq<HPath>
    )
    requires forall ls0, lpath0, hs0 ::
               && inv(ls0)
               && relation(ls0, hs0)
               && lasf.path_valid(ls0, lpath0, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls0, lpath0, tid, hs0)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls0, lpath0, tid, hs0, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls0, lpath0, tid, hs0, hpath)
    requires inv(ls)
    requires relation(ls, hs)
    requires AtomicValidPathSequence(lasf, ls, lpaths, tid)
    ensures  inv(AtomicGetStateAfterPaths(lasf, ls, lpaths, tid))
    ensures  AtomicValidPathSequence(hasf, hs, hpaths, tid)
    ensures  relation(AtomicGetStateAfterPaths(lasf, ls, lpaths, tid), AtomicGetStateAfterPaths(hasf, hs, hpaths, tid))
    decreases |lpaths|,
              if |lpaths| > 0 then progress_measure(hs, lpaths[0], tid).0 else 0,
              if |lpaths| > 0 then progress_measure(hs, lpaths[0], tid).1 else 0
  {
    if |lpaths| == 0 {
      hpaths := [];
      return;
    }

    var ls_next := lasf.path_next(ls, lpaths[0], tid);

    if AtomicPathSkippable(lasf, inv, relation, ls, lpaths[0], tid, hs) {
      hpaths := lemma_LiftPathSequenceGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure, ls_next, tid, lpaths[1..], hs);
      return;
    }

    var hpath0 :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpaths[0], tid, hs, hpath0)
                  || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpaths[0], tid, hs, hpath0);

    var lty := lasf.path_type(lpaths[0]);
    var hty := hasf.path_type(hpath0);

    var hs_next := hasf.path_next(hs, hpath0, tid);

    if AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpaths[0], tid, hs, hpath0) {
      var hpaths_next :=
        lemma_LiftPathSequenceGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure, ls, tid, lpaths, hs_next);
      hpaths := [hpath0] + hpaths_next;
      assert hpaths[0] == hpath0;
      assert hpaths[1..] == hpaths_next;
      return;
    }

    var hpaths_next := lemma_LiftPathSequenceGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure, ls_next,
                                                                      tid, lpaths[1..], hs_next);
    hpaths := [hpath0] + hpaths_next;
    assert hpaths[0] == hpath0;
    assert hpaths[1..] == hpaths_next;
  }

  lemma lemma_LiftRecurrentAtomicTraceEntryGivenAtomicPathsLiftable<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    ls: LState,
    tid: Armada_ThreadHandle,
    lyr: LPath,
    lrrs: seq<LPath>,
    lrx: LPath,
    hs: HState,
    hyr: HPath
    ) returns (
    hrrs: seq<HPath>,
    hrx: HPath
    )
    requires forall ls0, lpath0, hs0 ::
               && inv(ls0)
               && relation(ls0, hs0)
               && lasf.path_valid(ls0, lpath0, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls0, lpath0, tid, hs0)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls0, lpath0, tid, hs0, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls0, lpath0, tid, hs0, hpath)
    requires inv(ls)
    requires relation(ls, hs)
    requires AtomicValidRecursiveStep(lasf, ls, tid, lyr, lrrs, lrx)
    requires LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lyr, tid, hs, hyr)
    ensures  AtomicValidRecursiveStep(hasf, hs, tid, hyr, hrrs, hrx)
    ensures  var ls1 := lasf.path_next(ls, lyr, tid);
             var ls2 := AtomicGetStateAfterPaths(lasf, ls1, lrrs, tid);
             var ls3 := lasf.path_next(ls2, lrx, tid);
             var hs1 := hasf.path_next(hs, hyr, tid);
             var hs2 := AtomicGetStateAfterPaths(hasf, hs1, hrrs, tid);
             var hs3 := hasf.path_next(hs2, hrx, tid);
             inv(ls3) && relation(ls3, hs3)
  {
    var ls1 := lasf.path_next(ls, lyr, tid);
    var ls2 := AtomicGetStateAfterPaths(lasf, ls1, lrrs, tid);
    var ls3 := lasf.path_next(ls2, lrx, tid);
    var hs1 := hasf.path_next(hs, hyr, tid);
    hrrs := lemma_LiftPathSequenceGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure, ls1, tid, lrrs, hs1);
    var hs2 := AtomicGetStateAfterPaths(hasf, hs1, hrrs, tid);

    hrx :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls2, lrx, tid, hs2, hrx)
           || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls2, lrx, tid, hs2, hrx);

    while AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls2, lrx, tid, hs2, hrx)
      invariant AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls2, lrx, tid, hs2, hrx)
                || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls2, lrx, tid, hs2, hrx);
      invariant AtomicValidPathSequence(hasf, hs1, hrrs, tid)
      invariant hs2 == AtomicGetStateAfterPaths(hasf, hs1, hrrs, tid)
      invariant relation(ls2, hs2)
      decreases progress_measure(hs2, lrx, tid).0, progress_measure(hs2, lrx, tid).1
    {
      assert AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls2, lrx, tid, hs2, hrx);
      if lasf.path_type(lrx).AtomicPathType_RY? {
        assert hasf.path_type(hrx).AtomicPathType_RR?;
      }
      else {
        assert lasf.path_type(lrx).AtomicPathType_RS?;
        assert hasf.path_type(hrx).AtomicPathType_RR?;
      }
      lemma_ExtendAtomicGetStateAfterPaths(hasf, hs1, hs2, hrrs, tid, hrx);
      lemma_ExtendAtomicValidPathSequence(hasf, hs1, hs2, hrrs, tid, hrx);
      hrrs := hrrs + [hrx];
      hs2 := hasf.path_next(hs2, hrx, tid);
      hrx :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls2, lrx, tid, hs2, hrx)
             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls2, lrx, tid, hs2, hrx);
    }

    var hs3 := hasf.path_next(hs2, hrx, tid);
  }

  lemma lemma_LiftAtomicTraceEntryGivenAtomicPathsLiftable<LState, LPath, LPC, HState, HPath, HPC>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    ls: LState,
    lentry: AtomicTraceEntry<LPath>,
    hs: HState
    ) returns (
    hentry: AtomicTraceEntry<HPath>
    )
    requires forall ls0, lpath0, hs0, tid ::
               && inv(ls0)
               && relation(ls0, hs0)
               && lasf.path_valid(ls0, lpath0, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls0, lpath0, tid, hs0)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls0, lpath0, tid, hs0, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls0, lpath0, tid, hs0, hpath)
    requires inv(ls)
    requires relation(ls, hs)
    requires AtomicValidStep(lasf, ls, lentry)
    ensures  AtomicValidStep(hasf, hs, hentry)
    ensures  || IntroduceAtomicTraceEntrySuccessful(hasf, inv, relation, progress_measure, ls, lentry, hs, hentry)
             || LiftAtomicTraceEntrySuccessful(lasf, hasf, inv, relation, ls, lentry, hs, hentry)
  {
    match lentry
    {
      case AtomicTraceEntry_Stutter() =>
        hentry := AtomicTraceEntry_Stutter();

      case AtomicTraceEntry_Tau(tid, lpath) =>
        if AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs) {
          hentry := AtomicTraceEntry_Stutter();
        }
        else {
          var hpath :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
                       || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath);
          hentry := AtomicTraceEntry_Tau(tid, hpath);
        }

      case AtomicTraceEntry_Normal(tid, lpath) =>
        if AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs) {
          hentry := AtomicTraceEntry_Stutter();
        }
        else {
          var hpath :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
                       || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath);
          if AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath) {
            if hasf.path_type(hpath).AtomicPathType_Tau? {
              hentry := AtomicTraceEntry_Tau(tid, hpath);
            }
            else {
              hentry := AtomicTraceEntry_Normal(tid, hpath);
            }
          }
          else {
            hentry := AtomicTraceEntry_Normal(tid, hpath);
          }
        }

      case AtomicTraceEntry_Recurrent(tid, lyr, lrrs, lrx) =>
        var hpath :| AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lyr, tid, hs, hpath)
                     || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lyr, tid, hs, hpath);
        if AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lyr, tid, hs, hpath) {
          if hasf.path_type(hpath).AtomicPathType_Tau? {
            hentry := AtomicTraceEntry_Tau(tid, hpath);
          }
          else {
            hentry := AtomicTraceEntry_Normal(tid, hpath);
          }
        }
        else {
          var hrrs, hrx :=
            lemma_LiftRecurrentAtomicTraceEntryGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure,
                                                                        ls, tid, lyr, lrrs, lrx, hs, hpath);
          hentry := AtomicTraceEntry_Recurrent(tid, hpath, hrrs, hrx);
        }
    }
  }

  lemma lemma_LiftAtomicBehaviorGivenAtomicPathsLiftableGeneral<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    lb: AnnotatedBehavior<LState, AtomicTraceEntry<LPath>>,
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    refinement_relation: RefinementRelation<LState, HState>
    ) returns (
    hb: AnnotatedBehavior<HState, AtomicTraceEntry<HPath>>
    )
    requires forall ls, lpath, hs, tid ::
               && inv(ls)
               && relation(ls, hs)
               && lasf.path_valid(ls, lpath, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
    requires AtomicInitImpliesInv(lasf, inv)
    requires forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
    requires forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
    requires AnnotatedBehaviorSatisfiesSpec(lb, AtomicAnnotatedSpec(lasf))
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, AtomicAnnotatedSpec(hasf))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, refinement_relation)
  {
    var hs0 :| hasf.init(hs0) && relation(lb.states[0], hs0);
    hb := AnnotatedBehavior([hs0], []);
    var pos := 0;
    var lh_map := [RefinementRange(0, 0)];

    assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hb.states, refinement_relation, lh_map);

    while pos < |lb.trace|
      invariant 0 <= pos <= |lb.trace|
      invariant |hb.states| > 0
      invariant BehaviorRefinesBehavior(lb.states[..pos+1], hb.states, refinement_relation)
      invariant AnnotatedBehaviorSatisfiesSpec(hb, AtomicAnnotatedSpec(hasf))
      invariant relation(lb.states[pos], last(hb.states))
      invariant inv(lb.states[pos])
      decreases |lb.states| - pos,
                if pos < |lb.trace| then GetTraceEntryProgressMeasure(progress_measure, last(hb.states), lb.trace[pos]).0 else 0,
                if pos < |lb.trace| then GetTraceEntryProgressMeasure(progress_measure, last(hb.states), lb.trace[pos]).1 else 0
    {
      var ls := lb.states[pos];
      var ls' := lb.states[pos+1];
      var lentry := lb.trace[pos];
      var hs := last(hb.states);
      assert ActionTuple(ls, ls', lentry) in AtomicAnnotatedSpec(lasf).next;
      var hentry := lemma_LiftAtomicTraceEntryGivenAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure, ls, lentry, hs);
      var hs' := AtomicGetNextStateAlways(hasf, hs, hentry);
      if LiftAtomicTraceEntrySuccessful(lasf, hasf, inv, relation, ls, lentry, hs, hentry) {
        lemma_ExtendBehaviorRefinesBehaviorRightOne_LH(lb.states[..pos+1], hb.states, refinement_relation, ls', hs');
        assert lb.states[..pos+1] + [ls'] == lb.states[..pos+1+1];
        pos := pos + 1;
      }
      else {
        lemma_ExtendBehaviorRefinesBehaviorRightOne_LStutter(lb.states[..pos+1], hb.states, refinement_relation, hs');
      }
      hb := AnnotatedBehavior(hb.states + [hs'], hb.trace + [hentry]);
    }

    assert lb.states[..pos+1] == lb.states;
    assert BehaviorRefinesBehavior(lb.states, hb.states, refinement_relation);
  }

  lemma lemma_AtomicBehaviorToAnnotatedBehavior<State(!new), Path(!new), PC(!new)>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    b: seq<State>
    ) returns (
    ab: AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    )
    requires BehaviorSatisfiesSpec(b, AtomicSpec(asf))
    ensures  AnnotatedBehaviorSatisfiesSpec(ab, AtomicAnnotatedSpec(asf))
    ensures  ab.states == b
  {
    var pos := 0;
    var trace := [];
    while pos < |b| - 1
      invariant 0 <= pos <= |b| - 1
      invariant |trace| == pos
      invariant AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(b[..pos + 1], trace), AtomicAnnotatedSpec(asf))
    {
      assert StatePair(b[pos], b[pos+1]) in AtomicSpec(asf).next;
      var entry :| AtomicNext(asf, b[pos], b[pos + 1], entry);
      lemma_ExtendStateNextSeqRight(b[..pos + 1], trace, AtomicAnnotatedSpec(asf).next, b[pos + 1], entry);
      assert b[..pos + 1] + [b[pos + 1]] == b[..(pos + 1) + 1];
      trace := trace + [entry];
      pos := pos + 1;
    }
    assert b[..pos + 1] == b;
    ab := AnnotatedBehavior(b, trace);
  }

  lemma lemma_AtomicAnnotatedBehaviorSatisfiesAtomicSpec<State(!new), Path(!new), PC(!new)>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    ab: AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(ab, AtomicAnnotatedSpec(asf))
    ensures  BehaviorSatisfiesSpec(ab.states, AtomicSpec(asf))
  {
    forall pos | 0 <= pos < |ab.trace|
      ensures StatePair(ab.states[pos], ab.states[pos + 1]) in AtomicSpec(asf).next
    {
      assert ActionTuple(ab.states[pos], ab.states[pos + 1], ab.trace[pos]) in AtomicAnnotatedSpec(asf).next;
    }
  }

  lemma lemma_LiftAtomicToAtomicGivenAtomicPathsLiftableGeneral<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    refinement_relation: RefinementRelation<LState, HState>
    )
    requires forall ls, lpath, hs, tid ::
               && inv(ls)
               && relation(ls, hs)
               && lasf.path_valid(ls, lpath, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
    requires AtomicInitImpliesInv(lasf, inv)
    requires forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
    requires forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
    ensures  SpecRefinesSpec(AtomicSpec(lasf), AtomicSpec(hasf), refinement_relation)
  {
    forall lb | BehaviorSatisfiesSpec(lb, AtomicSpec(lasf))
      ensures exists hb :: BehaviorRefinesBehavior(lb, hb, refinement_relation) && BehaviorSatisfiesSpec(hb, AtomicSpec(hasf))
    {
      var alb := lemma_AtomicBehaviorToAnnotatedBehavior(lasf, lb);
      var ahb := lemma_LiftAtomicBehaviorGivenAtomicPathsLiftableGeneral(alb, lasf, hasf, inv, relation, progress_measure,
                                                                         refinement_relation);
      lemma_AtomicAnnotatedBehaviorSatisfiesAtomicSpec(hasf, ahb);
      var hb := ahb.states;
      assert BehaviorRefinesBehavior(lb, hb, refinement_relation) && BehaviorSatisfiesSpec(hb, AtomicSpec(hasf));
    }
  }

  lemma lemma_LiftAtomicToAtomicGivenAtomicPathsLiftable<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    refinement_relation: RefinementRelation<LState, HState>
    )
    requires forall ls, lpath, hs, tid ::
               && inv(ls)
               && relation(ls, hs)
               && lasf.path_valid(ls, lpath, tid)
               ==> exists hpath :: LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
    requires AtomicInitImpliesInv(lasf, inv)
    requires forall ls, hs :: relation(ls, hs) ==> lasf.state_ok(ls) == hasf.state_ok(hs)
    requires forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
    requires forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
    ensures  SpecRefinesSpec(AtomicSpec(lasf), AtomicSpec(hasf), refinement_relation)
  {
    var progress_measure:(HState, LPath, Armada_ThreadHandle)->(int, int) := (hs: HState, ls: LPath, tid: Armada_ThreadHandle) => (0, 0);
    lemma_LiftAtomicToAtomicGivenAtomicPathsLiftableGeneral(lasf, hasf, inv, relation, progress_measure, refinement_relation);
  }

  lemma lemma_LiftAtomicToAtomicGivenAtomicPathsSkippablyLiftable<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    refinement_relation: RefinementRelation<LState, HState>
    )
    requires forall ls, lpath, hs, tid ::
               && inv(ls)
               && relation(ls, hs)
               && lasf.path_valid(ls, lpath, tid)
               && !AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs)
               ==> exists hpath :: LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
    requires AtomicInitImpliesInv(lasf, inv)
    requires forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
    requires forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
    ensures  SpecRefinesSpec(AtomicSpec(lasf), AtomicSpec(hasf), refinement_relation)
  {
    var progress_measure:(HState, LPath, Armada_ThreadHandle)->(int, int) := (hs: HState, ls: LPath, tid: Armada_ThreadHandle) => (0, 0);
    lemma_LiftAtomicToAtomicGivenAtomicPathsLiftableGeneral(lasf, hasf, inv, relation, progress_measure, refinement_relation);
  }

  lemma lemma_LiftAtomicToAtomicGivenAtomicPathsIntroduciblyLiftable<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    lasf: AtomicSpecFunctions<LState, LPath, LPC>,
    hasf: AtomicSpecFunctions<HState, HPath, HPC>,
    inv: LState->bool,
    relation: (LState, HState)->bool,
    progress_measure: (HState, LPath, Armada_ThreadHandle)->(int, int),
    refinement_relation: RefinementRelation<LState, HState>
    )
    requires forall ls, lpath, hs, tid ::
               && inv(ls)
               && relation(ls, hs)
               && lasf.path_valid(ls, lpath, tid)
               ==> exists hpath :: AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
                             || LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
    requires AtomicInitImpliesInv(lasf, inv)
    requires forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
    requires forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
    ensures  SpecRefinesSpec(AtomicSpec(lasf), AtomicSpec(hasf), refinement_relation)
  {
    lemma_LiftAtomicToAtomicGivenAtomicPathsLiftableGeneral(lasf, hasf, inv, relation, progress_measure, refinement_relation);
  }

}
