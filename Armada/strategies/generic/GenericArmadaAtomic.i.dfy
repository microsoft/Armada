include "GenericArmadaSpec.i.dfy"
include "GenericArmadaLemmas.i.dfy"
include "../invariants.i.dfy"
include "../../util/collections/seqs.i.dfy"
include "../../strategies/refinement/GeneralRefinementLemmas.i.dfy"

module GenericArmadaAtomicModule {

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

  //////////////////////////////////////////////
  // DEFINITIONS
  //////////////////////////////////////////////

  datatype AtomicPathType = AtomicPathType_Tau
                          | AtomicPathType_YY
                          | AtomicPathType_YS
                          | AtomicPathType_YR
                          | AtomicPathType_RY
                          | AtomicPathType_RS
                          | AtomicPathType_RR

  datatype AtomicTraceEntry<Path> =
      AtomicTraceEntry_Stutter()
    | AtomicTraceEntry_Tau(tau_tid: Armada_ThreadHandle, tau: Path)
    | AtomicTraceEntry_Normal(normal_tid: Armada_ThreadHandle, path: Path)
    | AtomicTraceEntry_Recurrent(recurrent_tid: Armada_ThreadHandle, yr: Path, rrs: seq<Path>, rx: Path)

  datatype AtomicSpecFunctions<!State, !Path, !PC> =
    AtomicSpecFunctions(
      init: State->bool,
      path_valid: (State, Path, Armada_ThreadHandle)->bool,
      path_next: (State, Path, Armada_ThreadHandle)->State,
      path_type: Path->AtomicPathType,
      state_ok: State->bool,
      get_thread_pc: (State, Armada_ThreadHandle)->Option<PC>,
      is_pc_nonyielding: PC->bool
      )

  predicate AtomicValidPathSequence<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    )
  {
    |paths| > 0 ==>
      && asf.path_type(paths[0]).AtomicPathType_RR?
      && asf.path_valid(s, paths[0], tid)
      && AtomicValidPathSequence(asf, asf.path_next(s, paths[0], tid), paths[1..], tid)
  }

  function AtomicGetStateAfterPaths<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    ) : State
  {
    if |paths| == 0 then s else AtomicGetStateAfterPaths(asf, asf.path_next(s, paths[0], tid), paths[1..], tid)
  }

  function AtomicGetStateSequence<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    ) : (states: seq<State>)
    ensures |states| == |paths| + 1
  {
    if |paths| == 0 then [s] else [s] + AtomicGetStateSequence(asf, asf.path_next(s, paths[0], tid), paths[1..], tid)
  }

  function AtomicGetNextStateAlways<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    entry: AtomicTraceEntry<Path>
    ) : State
  {
    match entry
      case AtomicTraceEntry_Stutter() => s
      case AtomicTraceEntry_Tau(tid, path) => asf.path_next(s, path, tid)
      case AtomicTraceEntry_Normal(tid, path) => asf.path_next(s, path, tid)
      case AtomicTraceEntry_Recurrent(tid, yr, rrs, rx) =>
        var s1 := asf.path_next(s, yr, tid);
        var s2 := AtomicGetStateAfterPaths(asf, s1, rrs, tid);
        asf.path_next(s2, rx, tid)
  }
  
  predicate AtomicValidRecursiveStep<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    tid: Armada_ThreadHandle,
    yr: Path,
    rrs: seq<Path>,
    rx: Path
    )
  {
    // The first path has the type YR
    && asf.path_type(yr).AtomicPathType_YR?

    // All the paths are valid
    && var s1 := asf.path_next(s, yr, tid);
      var s2 := AtomicGetStateAfterPaths(asf, s1, rrs, tid);
      var s3 := asf.path_next(s2, rx, tid);
    && asf.path_valid(s, yr, tid)
    && AtomicValidPathSequence(asf, s1, rrs, tid)
    && asf.path_valid(s2, rx, tid)

    // The final state has ok-ness matching the path type
    && (if asf.state_ok(s3) then asf.path_type(rx).AtomicPathType_RY? else asf.path_type(rx).AtomicPathType_RS?)
  }

  predicate AtomicValidStep<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    entry: AtomicTraceEntry<Path>
    )
  {
    match entry
      case AtomicTraceEntry_Stutter() =>
        true

      case AtomicTraceEntry_Tau(tid, path) =>
        && asf.path_type(path).AtomicPathType_Tau?
        && asf.path_valid(s, path, tid)

      case AtomicTraceEntry_Normal(tid, path) =>
        && asf.path_valid(s, path, tid)
        && (if asf.state_ok(asf.path_next(s, path, tid)) then asf.path_type(path).AtomicPathType_YY? else asf.path_type(path).AtomicPathType_YS?)

      case AtomicTraceEntry_Recurrent(tid, yr, rrs, rx) =>
        AtomicValidRecursiveStep(asf, s, tid, yr, rrs, rx)
  }

  predicate AtomicNext<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    entry: AtomicTraceEntry<Path>
    )
  {
    && AtomicValidStep(asf, s, entry)
    && s' == AtomicGetNextStateAlways(asf, s, entry)
  }

  function AtomicAnnotatedSpec<State(!new), Path(!new), PC>(asf: AtomicSpecFunctions<State, Path, PC>)
    : AnnotatedBehaviorSpec<State, AtomicTraceEntry<Path>>
  {
    AnnotatedBehaviorSpec(iset s | asf.init(s) :: s,
                          iset s, s', entry | AtomicNext(asf, s, s', entry) :: ActionTuple(s, s', entry))
  }

  function AtomicSpec<State(!new), Path(!new), PC>(asf: AtomicSpecFunctions<State, Path, PC>) : Spec<State>
  {
    Spec(iset s | asf.init(s) :: s,
         iset s, s', entry: AtomicTraceEntry<Path> | AtomicNext(asf, s, s', entry) :: StatePair(s, s'))
  }

  function GenericAtomicLiftTraceEntry<LPath, HPath>(lentry: AtomicTraceEntry<LPath>, pathLift: LPath->HPath) : AtomicTraceEntry<HPath>
  {
    match lentry
      case AtomicTraceEntry_Stutter() => AtomicTraceEntry_Stutter()
      case AtomicTraceEntry_Tau(tid, path) => AtomicTraceEntry_Tau(tid, pathLift(path))
      case AtomicTraceEntry_Normal(tid, path) => AtomicTraceEntry_Normal(tid, pathLift(path))
      case AtomicTraceEntry_Recurrent(tid, yr, rrs, rx) =>
        AtomicTraceEntry_Recurrent(tid, pathLift(yr), MapSeqToSeq(rrs, pathLift), pathLift(rx))
  }

  function GenericAtomicLiftPathSeqStateDependent<LState(!new), LPath(!new), LPC, HPath>(
    asf: AtomicSpecFunctions<LState, LPath, LPC>,
    ls: LState,
    paths: seq<LPath>,
    tid: Armada_ThreadHandle,
    lift_fn: (LState, LPath)-->HPath
    ) : seq<HPath>
    requires AtomicValidPathSequence(asf, ls, paths, tid)
    requires forall ls, lpath :: asf.path_valid(ls, lpath, tid) ==> lift_fn.requires(ls, lpath)
    decreases |paths|
  {
    if |paths| == 0 then
      []
    else
      var ls_next := asf.path_next(ls, paths[0], tid);
      [lift_fn(ls, paths[0])] + GenericAtomicLiftPathSeqStateDependent(asf, ls_next, paths[1..], tid, lift_fn)
  }

  function GenericAtomicLiftTraceEntryStateDependent<LState(!new), LPath(!new), LPC, HPath>(
    asf: AtomicSpecFunctions<LState, LPath, LPC>,
    ls: LState,
    lentry: AtomicTraceEntry<LPath>,
    lift_fn: (LState, LPath)-->HPath
    ) : AtomicTraceEntry<HPath>
    requires AtomicValidStep(asf, ls, lentry)
    requires forall ls, lpath, tid :: asf.path_valid(ls, lpath, tid) ==> lift_fn.requires(ls, lpath)
  {
    match lentry
      case AtomicTraceEntry_Stutter() => AtomicTraceEntry_Stutter()
      case AtomicTraceEntry_Tau(tid, path) => AtomicTraceEntry_Tau(tid, lift_fn(ls, path))
      case AtomicTraceEntry_Normal(tid, path) => AtomicTraceEntry_Normal(tid, lift_fn(ls, path))
      case AtomicTraceEntry_Recurrent(tid, yr, rrs, rx) =>
        var ls1 := asf.path_next(ls, yr, tid);
        var ls2 := AtomicGetStateAfterPaths(asf, ls1, rrs, tid);
        var rrs' := GenericAtomicLiftPathSeqStateDependent(asf, ls1, rrs, tid, lift_fn);
        AtomicTraceEntry_Recurrent(tid, lift_fn(ls, yr), rrs', lift_fn(ls2, rx))
  }

  predicate AtomicInitImpliesInv<State(!new), Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    inv: State->bool
    )
  {
    forall s :: asf.init(s) ==> inv(s)
  }

  predicate AtomicInitImpliesYielding<State(!new), Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, tid :: asf.init(s) && asf.get_thread_pc(s, tid).Some? ==> !asf.is_pc_nonyielding(asf.get_thread_pc(s, tid).v)
  }

  predicate AtomicInitImpliesOK<State(!new), Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s :: asf.init(s) ==> asf.state_ok(s)
  }

  predicate AtomicPathPreservesInv<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    inv: State->bool
    )
  {
    forall s, path, tid :: inv(s) && asf.path_valid(s, path, tid) ==> inv(asf.path_next(s, path, tid))
  }

  predicate AtomicPathRequiresOK<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, path, tid :: asf.path_valid(s, path, tid) ==> asf.state_ok(s)
  }

  predicate AtomicSteppingThreadHasPC<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, path, tid :: asf.path_valid(s, path, tid) ==> asf.get_thread_pc(s, tid).Some?
  }

  predicate AtomicTauLeavesPCUnchanged<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, path, tid :: asf.path_valid(s, path, tid) && asf.path_type(path).AtomicPathType_Tau? ==>
      var s' := asf.path_next(s, path, tid);
      asf.get_thread_pc(s', tid) == asf.get_thread_pc(s, tid)
  }

  predicate AtomicThreadYielding<State(!new), Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    tid: Armada_ThreadHandle
    )
  {
    var pc := asf.get_thread_pc(s, tid);
    !asf.state_ok(s) || pc.None? || !asf.is_pc_nonyielding(pc.v)
  }

  predicate AtomicThreadCantAffectOtherThreadPCExceptViaFork<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, path, tid, other_tid :: asf.path_valid(s, path, tid) && tid != other_tid
       ==> var s' := asf.path_next(s, path, tid);
           var pc := asf.get_thread_pc(s, other_tid);
           var pc' := asf.get_thread_pc(s', other_tid);
           (pc' != pc ==> pc.None? && !asf.is_pc_nonyielding(pc'.v))
  }

  predicate AtomicPathTypeMatchesPCTypes<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    path: Path,
    tid: Armada_ThreadHandle
    )
  {
    var s' := asf.path_next(s, path, tid);
    match asf.path_type(path)
      case AtomicPathType_Tau => true
      case AtomicPathType_YY => AtomicThreadYielding(asf, s, tid) && asf.state_ok(s') && AtomicThreadYielding(asf, s', tid)
      case AtomicPathType_YS => AtomicThreadYielding(asf, s, tid) && !asf.state_ok(s')
      case AtomicPathType_YR => AtomicThreadYielding(asf, s, tid) && !AtomicThreadYielding(asf, s', tid)
      case AtomicPathType_RY => !AtomicThreadYielding(asf, s, tid) && asf.state_ok(s') && AtomicThreadYielding(asf, s', tid)
      case AtomicPathType_RS => !AtomicThreadYielding(asf, s, tid) && !asf.state_ok(s')
      case AtomicPathType_RR => !AtomicThreadYielding(asf, s, tid) && !AtomicThreadYielding(asf, s', tid)
  }

  predicate AtomicPathTypeAlwaysMatchesPCTypes<State(!new), Path(!new), PC>(
    asf: AtomicSpecFunctions<State, Path, PC>
    )
  {
    forall s, path, tid :: asf.path_valid(s, path, tid) ==> AtomicPathTypeMatchesPCTypes(asf, s, path, tid)
  }

  //////////////////////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////////////////////

  lemma lemma_AtomicGetStateSequenceOnePos<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    pos: int
    )
    requires 0 <= pos < |paths|
    ensures  var states := AtomicGetStateSequence(asf, s, paths, tid); states[pos+1] == asf.path_next(states[pos], paths[pos], tid)
  {
    if |paths| > 0 && pos > 0 {
      lemma_AtomicGetStateSequenceOnePos(asf, asf.path_next(s, paths[0], tid), paths[1..], tid, pos-1);
    }
  }

  lemma lemma_AtomicValidPathSequenceImpliesValidPath<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    states: seq<State>,
    i: int
    )
    requires AtomicValidPathSequence(asf, s, paths, tid)
    requires 0 <= i < |paths|
    requires states == AtomicGetStateSequence(asf, s, paths, tid)
    ensures  asf.path_valid(states[i], paths[i], tid)
    ensures  states[i+1] == asf.path_next(states[i], paths[i], tid)
  {
    if i > 0 {
      var s_mid := asf.path_next(s, paths[0], tid);
      lemma_AtomicValidPathSequenceImpliesValidPath(asf, s_mid, s', paths[1..], tid, states[1..], i-1);
    }
  }

  lemma lemma_AtomicNextLastElement<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    states: seq<State>
    )
    requires s' == AtomicGetStateAfterPaths(asf, s, paths, tid)
    requires states == AtomicGetStateSequence(asf, s, paths, tid)
    ensures  last(states) == s'
  {
    if |paths| > 0 {
      var s_mid := asf.path_next(s, paths[0], tid);
      lemma_AtomicNextLastElement(asf, s_mid, s', paths[1..], tid, states[1..]);
    }
  }

  lemma lemma_ExtendAtomicGetStateAfterPaths<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    path: Path
    )
    requires s' == AtomicGetStateAfterPaths(asf, s, paths, tid)
    ensures  asf.path_next(s', path, tid) == AtomicGetStateAfterPaths(asf, s, paths + [path], tid)
    decreases |paths|
  {
    if |paths| > 0 {
      var s_next := asf.path_next(s, paths[0], tid);
      lemma_ExtendAtomicGetStateAfterPaths(asf, s_next, s', paths[1..], tid, path);
      assert paths + [path] == [paths[0]] + (paths[1..] + [path]);
    }
  }

  lemma lemma_ExtendAtomicValidPathSequence<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    path: Path
    )
    requires AtomicValidPathSequence(asf, s, paths, tid)
    requires s' == AtomicGetStateAfterPaths(asf, s, paths, tid)
    requires asf.path_valid(s', path, tid)
    requires asf.path_type(path).AtomicPathType_RR?
    ensures  AtomicValidPathSequence(asf, s, paths + [path], tid)
    decreases |paths|
  {
    if |paths| > 0 {
      var s_next := asf.path_next(s, paths[0], tid);
      lemma_ExtendAtomicValidPathSequence(asf, s_next, s', paths[1..], tid, path);
      assert paths + [path] == [paths[0]] + (paths[1..] + [path]);
    }
  }

  lemma lemma_AtomicBehaviorToAnnotatedBehavior<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    b:seq<State>
    ) returns (
    ab:AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    )
    requires BehaviorSatisfiesSpec(b, AtomicSpec(asf))
    ensures  AnnotatedBehaviorSatisfiesSpec(ab, AtomicAnnotatedSpec(asf))
    ensures  ab.states == b
  {
    var trace:seq<AtomicTraceEntry<Path>> := [];
    var pos := 0;

    while pos < |b| - 1
      invariant 0 <= pos < |b|
      invariant |trace| == pos
      invariant AnnotatedBehaviorSatisfiesSpec(AnnotatedBehavior(b[..pos + 1], trace), AtomicAnnotatedSpec(asf))
    {
      assert StatePair(b[pos], b[pos + 1]) in AtomicSpec(asf).next;
      var entry :| AtomicNext(asf, b[pos], b[pos + 1], entry);
      lemma_ExtendStateNextSeqRight(b[..pos + 1], trace, AtomicAnnotatedSpec(asf).next, b[pos + 1], entry);
      assert b[..pos + 1] + [b[pos + 1]] == b[..(pos + 1) + 1];
      trace := trace + [entry];
      pos := pos + 1;
    }

    assert b[..pos + 1] == b;
    ab := AnnotatedBehavior(b, trace);
  }

  lemma lemma_AtomicAnnotatedBehaviorSatisfiesAtomicSpec<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    ab:AnnotatedBehavior<State, AtomicTraceEntry<Path>>
    )
    requires AnnotatedBehaviorSatisfiesSpec(ab, AtomicAnnotatedSpec(asf))
    ensures  BehaviorSatisfiesSpec(ab.states, AtomicSpec(asf))
  {
    var b := ab.states;
    var spec := AtomicSpec(asf);
    forall i {:trigger StatePair(b[i], b[i + 1]) in spec.next} | 0 <= i < |b| - 1
      ensures StatePair(b[i], b[i + 1]) in spec.next
    {
      assert ActionTuple(ab.states[i], ab.states[i + 1], ab.trace[i]) in AtomicAnnotatedSpec(asf).next;
    }
  }

}
