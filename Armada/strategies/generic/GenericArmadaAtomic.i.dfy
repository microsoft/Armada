include "GenericArmadaSpec.i.dfy"
include "GenericArmadaLemmas.i.dfy"
include "../invariants.i.dfy"

module GenericArmadaAtomicModule {

  import opened util_collections_seqs_s
  import opened util_option_s
  import opened GenericArmadaSpecModule
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions
  import opened GeneralRefinementModule
  import opened InvariantsModule
  import opened GenericArmadaLemmasModule

  //////////////////////////////////////////////
  // DEFINITIONS
  //////////////////////////////////////////////

  datatype AtomicPathType = AtomicPathType_Tau
                          | AtomicPathType_YY
                          | AtomicPathType_YN
                          | AtomicPathType_YR
                          | AtomicPathType_RY
                          | AtomicPathType_RN
                          | AtomicPathType_RR

  datatype AtomicTraceEntry<Path> =
      AtomicTraceEntry_Stutter()
    | AtomicTraceEntry_Tau(path: Path)
    | AtomicTraceEntry_Normal(path: Path)
    | AtomicTraceEntry_Stopping(path: Path)
    | AtomicTraceEntry_Recurrent(tid: Armada_ThreadHandle, paths: seq<Path>)

  datatype AtomicSpecFunctions<!State, !Path, !PC> =
    AtomicSpecFunctions(
      init:State->bool,
      path_valid:(State, Path)->bool,
      path_next:(State, Path)->State,
      path_to_thread:Path->Armada_ThreadHandle,
      state_ok:State->bool,
      path_type:Path->AtomicPathType,
      get_thread_pc:(State, Armada_ThreadHandle)->Option<PC>,
      is_pc_nonyielding:PC->bool
      )

  predicate AtomicValidPathSequence<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    paths:seq<Path>
    )
  {
    |paths| > 0 ==> asf.path_valid(s, paths[0]) && AtomicValidPathSequence(asf, asf.path_next(s, paths[0]), paths[1..])
  }

  function AtomicGetStateAfterPaths<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    paths:seq<Path>
    ) : State
  {
    if |paths| == 0 then s else AtomicGetStateAfterPaths(asf, asf.path_next(s, paths[0]), paths[1..])
  }

  function AtomicGetStateSequence<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    paths:seq<Path>
    ) : (states:seq<State>)
    ensures |states| == |paths| + 1
  {
    if |paths| == 0 then [s] else [s] + AtomicGetStateSequence(asf, asf.path_next(s, paths[0]), paths[1..])
  }

  function AtomicGetNextStateAlways<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    entry:AtomicTraceEntry<Path>
    ) : State
  {
    match entry
      case AtomicTraceEntry_Stutter() => s
      case AtomicTraceEntry_Tau(path) => asf.path_next(s, path)
      case AtomicTraceEntry_Normal(path) => asf.path_next(s, path)
      case AtomicTraceEntry_Stopping(path) => asf.path_next(s, path)
      case AtomicTraceEntry_Recurrent(_, paths) => AtomicGetStateAfterPaths(asf, s, paths)
  }

  predicate AtomicRecursiveValidStep<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    tid:Armada_ThreadHandle,
    paths:seq<Path>
    )
  {
    && AtomicValidPathSequence(asf, s, paths)
    && (forall p :: p in paths ==> asf.path_to_thread(p) == tid)
    && |paths| > 0
    && asf.path_type(paths[0]).AtomicPathType_YR?
    && (forall i :: 0 < i < |paths|-1 ==> asf.path_type(paths[i]).AtomicPathType_RR?)
    && (|paths| > 1 ==> var t := asf.path_type(last(paths)); t.AtomicPathType_RY? || t.AtomicPathType_RN? || t.AtomicPathType_RR?)
    && (asf.path_type(last(paths)).AtomicPathType_RY? || !asf.state_ok(AtomicGetStateAfterPaths(asf, s, paths)))
  }

  predicate AtomicValidStep<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    entry:AtomicTraceEntry<Path>
    )
  {
    match entry
      case AtomicTraceEntry_Stutter() => true
      case AtomicTraceEntry_Tau(path) => asf.path_type(path).AtomicPathType_Tau? && asf.path_valid(s, path)
      case AtomicTraceEntry_Normal(path) => asf.path_type(path).AtomicPathType_YY? && asf.path_valid(s, path)
      case AtomicTraceEntry_Stopping(path) => asf.path_type(path).AtomicPathType_YN? && asf.path_valid(s, path)
      case AtomicTraceEntry_Recurrent(tid, paths) => AtomicRecursiveValidStep(asf, s, tid, paths)
  }

  predicate AtomicNext<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    entry:AtomicTraceEntry<Path>
    )
  {
    && AtomicValidStep(asf, s, entry)
    && s' == AtomicGetNextStateAlways(asf, s, entry)
  }

  function AtomicAnnotatedSpec<State(!new), Path(!new), PC>(asf:AtomicSpecFunctions<State, Path, PC>)
    : AnnotatedBehaviorSpec<State, AtomicTraceEntry<Path>>
  {
    AnnotatedBehaviorSpec(iset s | asf.init(s) :: s,
                          iset s, s', entry | AtomicNext(asf, s, s', entry) :: ActionTuple(s, s', entry))
  }

  function AtomicSpec<State(!new), Path(!new), PC>(asf:AtomicSpecFunctions<State, Path, PC>) : Spec<State>
  {
    Spec(iset s | asf.init(s) :: s,
         iset s, s', entry: AtomicTraceEntry<Path> | AtomicNext(asf, s, s', entry) :: StatePair(s, s'))
  }

  function AtomicSimplifiedSpec<State(!new), Path(!new), PC>(asf:AtomicSpecFunctions<State, Path, PC>)
    : AnnotatedBehaviorSpec<State, Path>
  {
    AnnotatedBehaviorSpec(iset s | asf.init(s) :: s,
                          iset s, s', path | asf.path_valid(s, path) && s' == asf.path_next(s, path) :: ActionTuple(s, s', path))
  }

  //////////////////////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////////////////////

  lemma lemma_AtomicGetStateSequenceOnePos<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    paths:seq<Path>,
    pos:int
    )
    requires 0 <= pos < |paths|
    ensures  var states := AtomicGetStateSequence(asf, s, paths); states[pos+1] == asf.path_next(states[pos], paths[pos])
  {
    if |paths| > 0 && pos > 0 {
      lemma_AtomicGetStateSequenceOnePos(asf, asf.path_next(s, paths[0]), paths[1..], pos-1);
    }
  }

  lemma lemma_AtomicValidPathSequenceImpliesValidPath<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    paths:seq<Path>,
    states:seq<State>,
    i:int
    )
    requires AtomicValidPathSequence(asf, s, paths)
    requires 0 <= i < |paths|
    requires states == AtomicGetStateSequence(asf, s, paths)
    ensures  asf.path_valid(states[i], paths[i])
    ensures  states[i+1] == asf.path_next(states[i], paths[i])
  {
    if i > 0 {
      var s_mid := asf.path_next(s, paths[0]);
      lemma_AtomicValidPathSequenceImpliesValidPath(asf, s_mid, s', paths[1..], states[1..], i-1);
    }
  }

  lemma lemma_AtomicNextLastElement<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    paths:seq<Path>,
    states:seq<State>
    )
    requires AtomicValidPathSequence(asf, s, paths)
    requires s' == AtomicGetStateAfterPaths(asf, s, paths)
    requires states == AtomicGetStateSequence(asf, s, paths)
    ensures  last(states) == s'
  {
    if |paths| > 0 {
      var s_mid := asf.path_next(s, paths[0]);
      lemma_AtomicNextLastElement(asf, s_mid, s', paths[1..], states[1..]);
    }
  }

  //////////////////////////////////////////////
  // PROVING INVARIANTS
  //////////////////////////////////////////////

  lemma lemma_SimplifyAtomicBehavior<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    b:AnnotatedBehavior<State, AtomicTraceEntry<Path>>,
    pos:int
    ) returns (
    sb:AnnotatedBehavior<State, Path>
    )
    requires AnnotatedBehaviorSatisfiesSpec(b, AtomicAnnotatedSpec(asf))
    requires 0 <= pos < |b.states|
    ensures  AnnotatedBehaviorSatisfiesSpec(sb, AtomicSimplifiedSpec(asf))
    ensures  last(sb.states) == b.states[pos]
  {
    var spec := AtomicAnnotatedSpec(asf);
    var sspec := AtomicSimplifiedSpec(asf);

    if pos == 0 {
      sb := AnnotatedBehavior([b.states[pos]], []);
      return;
    }

    var prev := pos-1;
    var sb_prev := lemma_SimplifyAtomicBehavior(asf, b, prev);
    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in spec.next;

    var s := b.states[prev];
    var s' := b.states[prev+1];
    var step := b.trace[prev];

    match step {
      case AtomicTraceEntry_Stutter() =>
        assert s' == s;
        sb := sb_prev;
        
      case AtomicTraceEntry_Tau(path) =>
        lemma_ExtendStateNextSeqRight(sb_prev.states, sb_prev.trace, sspec.next, s', path);
        sb := AnnotatedBehavior(sb_prev.states + [s'], sb_prev.trace + [path]);
      
      case AtomicTraceEntry_Normal(path) =>
        lemma_ExtendStateNextSeqRight(sb_prev.states, sb_prev.trace, sspec.next, s', path);
        sb := AnnotatedBehavior(sb_prev.states + [s'], sb_prev.trace + [path]);
      
      case AtomicTraceEntry_Stopping(path) =>
        lemma_ExtendStateNextSeqRight(sb_prev.states, sb_prev.trace, sspec.next, s', path);
        sb := AnnotatedBehavior(sb_prev.states + [s'], sb_prev.trace + [path]);
      
      case AtomicTraceEntry_Recurrent(_, paths) =>
        var states := AtomicGetStateSequence(asf, s, paths);
        sb := sb_prev;
        var pos := 0;
        while pos < |paths|
          invariant 0 <= pos <= |paths|
          invariant AnnotatedBehaviorSatisfiesSpec(sb, AtomicSimplifiedSpec(asf))
          invariant last(sb.states) == states[pos]
        {
          lemma_AtomicValidPathSequenceImpliesValidPath(asf, s, s', paths, states, pos);
          assert asf.path_valid(states[pos], paths[pos]);
          assert states[pos+1] == asf.path_next(states[pos], paths[pos]);
          lemma_ExtendStateNextSeqRight(sb.states, sb.trace, sspec.next, states[pos+1], paths[pos]);
          sb := AnnotatedBehavior(sb.states + [states[pos+1]], sb.trace + [paths[pos]]);
          pos := pos + 1;
        }
        lemma_AtomicNextLastElement(asf, s, s', paths, states);
    }
  }

  lemma lemma_InvariantOfSimplifiedSpecIsInvariantOfAnnotatedSpec<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    inv:State->bool
    )
    requires IsInvariantPredicateOfSpec(inv, AtomicSimplifiedSpec(asf))
    ensures  IsInvariantPredicateOfSpec(inv, AtomicAnnotatedSpec(asf))
  {
    var spec := AtomicAnnotatedSpec(asf);
    var sspec := AtomicSimplifiedSpec(asf);
    forall s | s in AnnotatedReachables(spec)
      ensures inv(s)
    {
      reveal_AnnotatedReachables();
      var ab :| AnnotatedBehaviorSatisfiesSpec(ab, spec) && last(ab.states) == s;
      var sb := lemma_SimplifyAtomicBehavior(asf, ab, |ab.states|-1);
      assert inv(last(sb.states));
    }
  }

  lemma lemma_EstablishAtomicInvariantViaPaths<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    inv:State->bool
    )
    requires forall s :: asf.init(s) ==> inv(s)
    requires forall s, s', path :: asf.path_valid(s, path) && s' == asf.path_next(s, path) && inv(s) ==> inv(s')
    ensures  IsInvariantPredicateOfSpec(inv, AtomicSimplifiedSpec(asf))
    ensures  IsInvariantPredicateOfSpec(inv, AtomicAnnotatedSpec(asf))
  {
    lemma_EstablishInvariantPredicatePure(inv, AtomicSimplifiedSpec(asf));
    lemma_InvariantOfSimplifiedSpecIsInvariantOfAnnotatedSpec(asf, inv);
  }

  lemma lemma_EstablishAtomicInvariantUsingInvariantViaPaths<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    inv_unknown:State->bool,
    inv_known:State->bool
    )
    requires IsInvariantPredicateOfSpec(inv_known, AtomicSimplifiedSpec(asf))
    requires forall s :: asf.init(s) ==> inv_unknown(s)
    requires forall s, s', path :: asf.path_valid(s, path) && s' == asf.path_next(s, path) && inv_known(s) && inv_unknown(s) ==> inv_unknown(s')
    ensures  IsInvariantPredicateOfSpec(inv_unknown, AtomicSimplifiedSpec(asf))
    ensures  IsInvariantPredicateOfSpec(inv_unknown, AtomicAnnotatedSpec(asf))
  {
    lemma_EstablishInvariantPredicateUsingInvariantPredicate(inv_unknown, inv_known, AtomicSimplifiedSpec(asf));
    lemma_InvariantOfSimplifiedSpecIsInvariantOfAnnotatedSpec(asf, inv_unknown);
  }

  //////////////////////////////////////////////
  // LIFTING TO ATOMIC
  //////////////////////////////////////////////

  lemma lemma_LiftToAtomic<State, OneStep, Path, PC>(
    lasf:Armada_SpecFunctions<State, OneStep, PC>,
    hasf:AtomicSpecFunctions<State, Path, PC>,
    lb:AnnotatedBehavior<State, Armada_Multistep<OneStep>>
    ) returns (
    hb:AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(lasf))
    requires forall s :: lasf.init(s) ==> hasf.init(s)
    requires forall s, s', lentry:Armada_Multistep<OneStep> ::
               Armada_NextMultistep(lasf, s, s', lentry.steps, lentry.tid, lentry.tau) ==> exists hentry :: AtomicNext(hasf, s, s', hentry)
    ensures  hb.states == lb.states
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, AtomicAnnotatedSpec(hasf))
    decreases |lb.states|
  {
    var lspec := SpecFunctionsToSpec(lasf);
    var hspec := AtomicAnnotatedSpec(hasf);

    if |lb.trace| == 0 {
      hb := AnnotatedBehavior(lb.states, []);
      return;
    }

    var pos := |lb.trace|-1;
    lemma_TakeStateNextSeq(lb.states, lb.trace, lspec.next, pos);
    var lb_prev := AnnotatedBehavior(lb.states[..pos+1], lb.trace[..pos]);
    var hb_prev := lemma_LiftToAtomic(lasf, hasf, lb_prev);

    assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in lspec.next;
    var lentry := lb.trace[pos];
    assert Armada_NextMultistep(lasf, lb.states[pos], lb.states[pos+1], lentry.steps, lentry.tid, lentry.tau);
    var hentry :| AtomicNext(hasf, lb.states[pos], lb.states[pos+1], hentry);
    lemma_ExtendStateNextSeqRight(hb_prev.states, hb_prev.trace, hspec.next, lb.states[pos+1], hentry);
    hb := AnnotatedBehavior(hb_prev.states + [lb.states[pos+1]], hb_prev.trace + [hentry]);
  }

  //////////////////////////////////////////////
  // LIFTING FROM ATOMIC
  //////////////////////////////////////////////

  predicate AtomicLiftPathFromAtomicPossible<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    path:Path
    )
  {
    && asf.path_valid(s, path)
    && s' == asf.path_next(s, path)
  }

  predicate AtomicStepsLiftPathFromAtomic<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle,
    tau:bool,
    startsYielding:bool,
    mustEndYielding:bool
    )
  {
    && Armada_NextMultipleSteps(asf, s, s', steps)
    && (forall step :: step in steps ==> asf.step_to_thread(step) == tid)
    && (forall step :: step in steps ==> asf.is_step_tau(step) == tau)
    && (forall i {:trigger Armada_GetStateSequence(asf, s, steps)[i]} ::
           0 < i < |steps| ==> !Armada_ThreadYielding(asf, Armada_GetStateSequence(asf, s, steps)[i], tid))
    && (if tau then |steps| <= 1 else startsYielding == Armada_ThreadYielding(asf, s, tid))
    && (mustEndYielding ==> Armada_ThreadYielding(asf, s', tid))
  }

  predicate AtomicLiftPathFromAtomicSuccessful<State, OneStep, Path, PC>(
    lasf:AtomicSpecFunctions<State, Path, PC>,
    hasf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    path:Path,
    steps:seq<OneStep>
    )
  {
    var tid := lasf.path_to_thread(path);
    match lasf.path_type(path)
      case AtomicPathType_Tau => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, true, false, false)
      case AtomicPathType_YY => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, true, true)
      case AtomicPathType_YN => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, true, true)
      case AtomicPathType_YR => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, true, false)
      case AtomicPathType_RY => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, false, true)
      case AtomicPathType_RN => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, false, true)
      case AtomicPathType_RR => AtomicStepsLiftPathFromAtomic(hasf, s, s', steps, tid, false, false, false)
  }

  lemma lemma_LiftRecurrentEntryFromAtomic<State, OneStep, Path, PC>(
    lasf:AtomicSpecFunctions<State, Path, PC>,
    hasf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    tid:Armada_ThreadHandle,
    paths:seq<Path>
    ) returns (
    hsteps:seq<OneStep>
    )
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires AtomicRecursiveValidStep(lasf, s, tid, paths)
    requires s' == AtomicGetStateAfterPaths(lasf, s, paths)
    requires forall ls, ls', path :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path) ==>
               exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, hsteps)
    ensures  Armada_NextMultistep(hasf, s, s', hsteps, tid, false)
  {
    var lstates := AtomicGetStateSequence(lasf, s, paths);
    lemma_AtomicGetStateSequenceOnePos(lasf, s, paths, 0);
    assert AtomicLiftPathFromAtomicPossible(lasf, s, lstates[1], paths[0]);
    hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, lstates[1], paths[0], hsteps);
    var hstates := Armada_GetStateSequence(hasf, s, hsteps);
    lemma_AtomicNextLastElement(lasf, s, s', paths, lstates);

    var pos := 1;
    if |paths| == 1 {
      assert !lasf.state_ok(s');
      assert !hasf.state_ok(s');
      lemma_ArmadaNextMultipleStepsLastElement(hasf, s, lstates[1], hsteps, hstates);
      assert Armada_ThreadYielding(hasf, last(hstates), tid);
    }

    while pos < |paths|
      invariant 1 <= pos <= |paths|
      invariant forall step :: step in hsteps ==> hasf.step_to_thread(step) == tid
      invariant forall step :: step in hsteps ==> hasf.is_step_tau(step) == false
      invariant AtomicValidPathSequence(lasf, lstates[pos], paths[pos..])
      invariant Armada_NextMultipleSteps(hasf, s, lstates[pos], hsteps)
      invariant hstates == Armada_GetStateSequence(hasf, s, hsteps)
      invariant forall i :: 0 < i < |hsteps| ==> !Armada_ThreadYielding(hasf, hstates[i], tid)
      invariant pos == |paths| ==> Armada_ThreadYielding(hasf, last(hstates), tid)
    {
      lemma_AtomicGetStateSequenceOnePos(lasf, s, paths, pos);
      assert AtomicLiftPathFromAtomicPossible(lasf, lstates[pos], lstates[pos+1], paths[pos]);
      var hsteps_next :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, lstates[pos], lstates[pos+1], paths[pos], hsteps_next);
      var hstates_next := Armada_GetStateSequence(hasf, lstates[pos], hsteps_next);
      lemma_ArmadaNextMultipleStepsLastElement(hasf, lstates[pos], lstates[pos+1], hsteps_next, hstates_next);

      var hsteps_new := hsteps + hsteps_next;
      var hstates_new := all_but_last(hstates) + hstates_next;

      forall i | 0 < i < |hsteps_new|
        ensures !Armada_ThreadYielding(hasf, hstates_new[i], tid)
      {
        if i < |hsteps| {
          assert hstates_new[i] == hstates[i];
          assert !Armada_ThreadYielding(hasf, hstates[i], tid);
        }
        else {
          var j := i - |hsteps|;
          assert hstates_new[i] == hstates_next[j];
          assert !Armada_ThreadYielding(hasf, hstates_next[j], tid);
        }
      }
      lemma_CombineArmadaNextMultipleSteps(hasf, s, lstates[pos], lstates[pos+1], hsteps, hsteps_next);
      lemma_CombineArmadaGetStateSequence(hasf, s, lstates[pos], lstates[pos+1], hsteps, hsteps_next, hstates, hstates_next);

      if pos == |paths|-1 {
        assert lasf.path_type(paths[pos]).AtomicPathType_RY? || !lasf.state_ok(AtomicGetStateAfterPaths(lasf, s, paths));
        assert s' == lstates[pos+1] == last(hstates_next) == last(hstates_new);
        assert Armada_ThreadYielding(hasf, last(hstates_new), tid);
      }

      hsteps := hsteps_new;
      hstates := hstates_new;
      pos := pos + 1;
    }

    assert pos == |paths| == |lstates|-1;
    lemma_ArmadaNextMultipleStepsLastElement(hasf, s, lstates[pos], hsteps, hstates);
    assert last(hstates) == lstates[pos] == last(lstates) == s';
  }

  lemma lemma_LiftEntryFromAtomic<State, OneStep, Path, PC>(
    lasf:AtomicSpecFunctions<State, Path, PC>,
    hasf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    lentry:AtomicTraceEntry<Path>
    ) returns (
    hsteps:seq<OneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires AtomicNext(lasf, s, s', lentry)
    requires forall ls, ls', path :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path) ==>
               exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, hsteps)
    ensures  Armada_NextMultistep(hasf, s, s', hsteps, tid, tau)
  {
    match lentry
    {
      case AtomicTraceEntry_Stutter =>
        hsteps := [];
        // No need to set tid, since tid used for a stutter can be arbitrary.
        tau := false;

      case AtomicTraceEntry_Tau(path) =>
        assert AtomicLiftPathFromAtomicPossible(lasf, s, s', path);
        hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, hsteps);
        tid := lasf.path_to_thread(path);
        tau := true;

      case AtomicTraceEntry_Normal(path) =>
        assert AtomicLiftPathFromAtomicPossible(lasf, s, s', path);
        hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, hsteps);
        tid := lasf.path_to_thread(path);
        tau := false;

      case AtomicTraceEntry_Stopping(path) =>
        assert AtomicLiftPathFromAtomicPossible(lasf, s, s', path);
        hsteps :| AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, hsteps);
        tid := lasf.path_to_thread(path);
        tau := false;

      case AtomicTraceEntry_Recurrent(entry_tid, paths) =>
        hsteps := lemma_LiftRecurrentEntryFromAtomic(lasf, hasf, s, s', entry_tid, paths);
        tid := entry_tid;
        tau := false;
    }
  }

  lemma lemma_LiftFromAtomicGivenEntriesLiftable<State, OneStep, Path, PC>(
    lasf:AtomicSpecFunctions<State, Path, PC>,
    hasf:Armada_SpecFunctions<State, OneStep, PC>,
    lb:AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    ) returns (
    hb:AnnotatedBehavior<State, Armada_Multistep<OneStep>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(lb, AtomicAnnotatedSpec(lasf))
    requires forall s :: lasf.init(s) ==> hasf.init(s)
    requires forall s, s', lentry:AtomicTraceEntry<Path> :: AtomicNext(lasf, s, s', lentry) ==>
               exists hentry:Armada_Multistep<OneStep> :: Armada_NextMultistep(hasf, s, s', hentry.steps, hentry.tid, hentry.tau)
               
    ensures  hb.states == lb.states
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
    decreases |lb.states|
  {
    var lspec := AtomicAnnotatedSpec(lasf);
    var hspec := SpecFunctionsToSpec(hasf);

    if |lb.trace| == 0 {
      hb := AnnotatedBehavior(lb.states, []);
      return;
    }

    var pos := |lb.trace|-1;
    lemma_TakeStateNextSeq(lb.states, lb.trace, lspec.next, pos);
    var lb_prev := AnnotatedBehavior(lb.states[..pos+1], lb.trace[..pos]);
    var hb_prev := lemma_LiftFromAtomicGivenEntriesLiftable(lasf, hasf, lb_prev);

    assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in lspec.next;
    var lentry := lb.trace[pos];
    assert AtomicNext(lasf, lb.states[pos], lb.states[pos+1], lentry);
    var hentry:Armada_Multistep<OneStep> :| Armada_NextMultistep(hasf, lb.states[pos], lb.states[pos+1],
                                                                 hentry.steps, hentry.tid, hentry.tau);
    lemma_ExtendStateNextSeqRight(hb_prev.states, hb_prev.trace, hspec.next, lb.states[pos+1], hentry);
    hb := AnnotatedBehavior(hb_prev.states + [lb.states[pos+1]], hb_prev.trace + [hentry]);
  }

  lemma lemma_LiftFromAtomic<State, OneStep, Path, PC>(
    lasf:AtomicSpecFunctions<State, Path, PC>,
    hasf:Armada_SpecFunctions<State, OneStep, PC>,
    lb:AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    ) returns (
    hb:AnnotatedBehavior<State, Armada_Multistep<OneStep>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(lb, AtomicAnnotatedSpec(lasf))
    requires forall s :: lasf.init(s) ==> hasf.init(s)
    requires forall s :: lasf.state_ok(s) <==> hasf.state_ok(s)
    requires forall ls, ls', path :: AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path) ==>
               exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, hsteps)
               
    ensures  hb.states == lb.states
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
    decreases |lb.states|
  {
    var lspec := AtomicAnnotatedSpec(lasf);
    var hspec := SpecFunctionsToSpec(hasf);

    forall s, s', lentry:AtomicTraceEntry<Path> | AtomicNext(lasf, s, s', lentry)
      ensures exists hentry:Armada_Multistep<OneStep> :: Armada_NextMultistep(hasf, s, s', hentry.steps, hentry.tid, hentry.tau)
    {
      var hsteps, tid, tau := lemma_LiftEntryFromAtomic(lasf, hasf, s, s', lentry);
      var hentry := Armada_Multistep(hsteps, tid, tau);
    }

    hb := lemma_LiftFromAtomicGivenEntriesLiftable(lasf, hasf, lb);
  }

}
