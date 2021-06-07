/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file contains lemmas useful in effecting a refinement via reduction on an Armada atomic
// behavior.  They support lemma_PerformAtomicReduction (in AtomicReduction.i.dfy).
//
// The general strategy is to show that the Armada atomic state machine, despite all its complexity
// having to do with things like tau operations and recurrent trace entries, nevertheless satisfies
// the conditions required by the more generic lemma_PerformRefinementViaReduction (in
// RefinementViaReduction.i.dfy).  These conditions are satisfied by creating a
// RefinementViaReductionRequest and proving that it satisfies ValidRefinementViaReductionRequest.
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "AtomicReductionSpec.i.dfy"
include "RefinementViaReductionSpec.i.dfy"
include "../../util/collections/seqs.i.dfy"
include "../generic/GenericArmadaLemmas.i.dfy"

module AtomicReductionLemmasModule {

  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened util_option_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened AtomicReductionSpecModule
  import opened RefinementViaReductionSpecModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened GenericArmadaAtomicModule
  import opened ArmadaCommonDefinitions

  //////////////////////////////////////////////////////////
  // FUNCTIONS FOR BUILDING CRASHING REDUCTION REQUEST
  //////////////////////////////////////////////////////////

  predicate IsNonyieldingOrInPhase<LState, LPath, LPC, HState, HPath, HPC>(
    arr: AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s: LState,
    tid: Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    arr.l.state_ok(s) && pc.Some? && (arr.l.is_pc_nonyielding(pc.v) || arr.is_phase1(pc.v) || arr.is_phase2(pc.v))
  }

  predicate AtomicValidPathSequenceOfAnyType<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    )
  {
    |paths| > 0 ==>
      && asf.path_valid(s, paths[0], tid)
      && AtomicValidPathSequenceOfAnyType(asf, asf.path_next(s, paths[0], tid), paths[1..], tid)
  }

  predicate AtomicNextMultiplePaths<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    )
  {
    && AtomicValidPathSequenceOfAnyType(asf, s, paths, tid)
    && s' == AtomicGetStateAfterPaths(asf, s, paths, tid)
  }
    
  function GetReducedAtomicSpecFunctions<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : AtomicSpecFunctions<LState, LPath, LPC>
  {
    AtomicSpecFunctions(
      arr.l.init,
      arr.l.path_valid,
      arr.l.path_next,
      lpath => arr.h.path_type(arr.lpath_to_hpath(lpath)),
      arr.l.state_ok,
      arr.l.get_thread_pc,
      lpc => arr.h.is_pc_nonyielding(arr.lpc_to_hpc(lpc))
      )
  }

  predicate GenericNextReduced<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    && (forall path :: path in paths ==> arr.l.path_type(path).AtomicPathType_Tau? == tau)
    && if tau then |paths| <= 1 else |paths| > 0 ==> (
        && !IsNonyieldingOrInPhase(arr, s, tid)
        && !IsNonyieldingOrInPhase(arr, s', tid)
        && (var states := AtomicGetStateSequence(arr.l, s, paths, tid);
           forall i :: 0 < i < |paths| ==> IsNonyieldingOrInPhase(arr, states[i], tid))
      )
  }

  predicate AtomicNextMultistep<State(!new), Path(!new), PC(!new)>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    paths:seq<Path>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && AtomicNextMultiplePaths(asf, s, s', paths, tid)
    && (forall path :: path in paths ==> asf.path_type(path).AtomicPathType_Tau? == tau)
    && if tau then |paths| <= 1 else |paths| > 0 ==> (
        && AtomicThreadYielding(asf, s, tid)
        && AtomicThreadYielding(asf, s', tid)
        && (var states := AtomicGetStateSequence(asf, s, paths, tid);
           forall i :: 0 < i < |paths| ==> !AtomicThreadYielding(asf, states[i], tid))
      )
  }

  predicate RefinementViaReductionLSpecNext<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    multistep:Armada_Multistep<LPath>
    )
  {
    AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau)
  }

  function GetRefinementViaReductionLSpec<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : AnnotatedBehaviorSpec<LState, Armada_Multistep<LPath>>
  {
    AnnotatedBehaviorSpec(
      iset s | arr.l.init(s),
      iset s, s', multistep | RefinementViaReductionLSpecNext(arr, s, s', multistep) :: ActionTuple(s, s', multistep))
  }

  predicate RefinementViaReductionHSpecNext<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    multistep:Armada_Multistep<LPath>
    )
  {
    GenericNextReduced(arr, s, s', multistep.steps, multistep.tid, multistep.tau)
  }

  function GetRefinementViaReductionHSpec<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : AnnotatedBehaviorSpec<LState, Armada_Multistep<LPath>>
  {
    AnnotatedBehaviorSpec(
      iset s | arr.l.init(s),
      iset s, s', multistep | RefinementViaReductionHSpecNext(arr, s, s', multistep) :: ActionTuple(s, s', multistep))
  }

  function RefinementViaReductionIdmap<LState, LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    multistep:Armada_Multistep<LPath>
    ) : Option<Armada_ThreadHandle>
  {
    if multistep.tau then None else Some(multistep.tid)
  }

  function GetRefinementViaReductionIdmap<LState, LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : Armada_Multistep<LPath>->Option<Armada_ThreadHandle>
  {
    multistep => RefinementViaReductionIdmap(arr, multistep)
  }

  predicate RefinementViaReductionPhase1<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Option<Armada_ThreadHandle>
    )
  {
    && tid.Some?
    && var pc := arr.l.get_thread_pc(s, tid.v);
      pc.Some? && arr.is_phase1(pc.v)
  }

  function GetRefinementViaReductionPhase1<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : (LState, Option<Armada_ThreadHandle>)->bool
  {
    (s:LState, tid:Option<Armada_ThreadHandle>) => RefinementViaReductionPhase1(arr, s, tid)
  }

  predicate RefinementViaReductionPhase2<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Option<Armada_ThreadHandle>
    )
  {
    && tid.Some?
    && var pc := arr.l.get_thread_pc(s, tid.v);
      pc.Some? && arr.is_phase2(pc.v)
  }

  function GetRefinementViaReductionPhase2<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : (LState, Option<Armada_ThreadHandle>)->bool
  {
    (s:LState, tid:Option<Armada_ThreadHandle>) => RefinementViaReductionPhase2(arr, s, tid)
  }

  function GetRefinementViaReductionCrashedPred<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : LState->bool
  {
    (s:LState) => !arr.l.state_ok(s)
  }

  function GetRefinementViaReductionRequest<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    ) : RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>
  {
    RefinementViaReductionRequest(GetRefinementViaReductionLSpec(arr), GetRefinementViaReductionHSpec(arr), arr.self_relation,
                                  GetRefinementViaReductionIdmap(arr), GetRefinementViaReductionPhase1(arr),
                                  GetRefinementViaReductionPhase2(arr), GetRefinementViaReductionCrashedPred(arr))
  }

  //////////////////////////////
  // UTILITY PREDICATES
  //////////////////////////////

  predicate IsPhase1<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.is_phase1(pc.v)
  }

  predicate IsPhase2<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.is_phase2(pc.v)
  }

  predicate IsNonyielding<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    var pc := arr.l.get_thread_pc(s, tid);
    pc.Some? && arr.l.is_pc_nonyielding(pc.v)
  }

  predicate PCTypesMatch<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    tid:Armada_ThreadHandle
    )
  {
    && IsPhase1(arr, s', tid) == IsPhase1(arr, s, tid)
    && IsPhase2(arr, s', tid) == IsPhase2(arr, s, tid)
    && IsNonyielding(arr, s', tid) == IsNonyielding(arr, s, tid)
  }

  predicate OKAndPCTypesMatch<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
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

  lemma lemma_ConcatenationCommutesWithAllButLast<T>(s1:seq<T>, s2:seq<T>)
    requires |s2| > 0
    ensures  s1 + all_but_last(s2) == all_but_last(s1 + s2)
  {
  }

  lemma lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    s': State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    states: seq<State>,
    i: int
    )
    requires AtomicValidPathSequenceOfAnyType(asf, s, paths, tid)
    requires 0 <= i < |paths|
    requires states == AtomicGetStateSequence(asf, s, paths, tid)
    ensures  asf.path_valid(states[i], paths[i], tid)
    ensures  states[i+1] == asf.path_next(states[i], paths[i], tid)
  {
    if i > 0 {
      var s_mid := asf.path_next(s, paths[0], tid);
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(asf, s_mid, s', paths[1..], tid, states[1..], i-1);
    }
  }

  lemma lemma_ExtendingStateSequenceWorks<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    paths:seq<Path>,
    states:seq<State>,
    tid:Armada_ThreadHandle,
    next_path:Path,
    next_state:State
    )
    requires AtomicNextMultiplePaths(asf, s, s', paths, tid)
    requires states == AtomicGetStateSequence(asf, s, paths, tid)
    requires asf.path_valid(s', next_path, tid)
    requires next_state == asf.path_next(s', next_path, tid)
    ensures  AtomicNextMultiplePaths(asf, s, next_state, paths + [next_path], tid)
    ensures  states + [next_state] == AtomicGetStateSequence(asf, s, paths + [next_path], tid)
    decreases |paths|
  {
    if |paths| > 0 {
      var s_mid := asf.path_next(s, paths[0], tid);
      lemma_ExtendingStateSequenceWorks(asf, s_mid, s', paths[1..], states[1..], tid, next_path, next_state);
      assert paths + [next_path] == [paths[0]] + (paths[1..] + [next_path]);
      assert states + [next_state] == [states[0]] + (states[1..] + [next_state]);
    }
  }

  lemma lemma_AllButLastPreservesAtomicNextMultiplePaths<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    states:seq<LState>,
    tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    requires states == AtomicGetStateSequence(arr.l, s, paths, tid)
    requires |paths| > 0
    ensures  all_but_last(states) == AtomicGetStateSequence(arr.l, s, all_but_last(paths), tid)
    ensures  AtomicNextMultiplePaths(arr.l, s, states[|states|-2], all_but_last(paths), tid)
  {
    if |paths| > 1 {
      var s_mid := arr.l.path_next(s, paths[0], tid);
      lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, s_mid, s', paths[1..], states[1..], tid);
      assert all_but_last(states[1..]) == AtomicGetStateSequence(arr.l, s_mid, all_but_last(paths[1..]), tid);
      assert AtomicNextMultiplePaths(arr.l, s_mid, states[1..][|states[1..]|-2], all_but_last(paths[1..]), tid);
      assert states[1..][|states[1..]|-2] == states[|states|-2];

      var abl := [paths[0]] + all_but_last(paths[1..]);
      lemma_ConcatenationCommutesWithAllButLast([paths[0]], paths[1..]);
      lemma_SequenceIsCarPlusCdr(paths);
      assert abl == all_but_last(paths);

      calc {
        all_but_last(states);
        [states[0]] + all_but_last(states[1..]);
        [states[0]] + AtomicGetStateSequence(arr.l, s_mid, all_but_last(paths[1..]), tid);
        AtomicGetStateSequence(arr.l, s, [paths[0]] + all_but_last(paths[1..]), tid);
        AtomicGetStateSequence(arr.l, s, all_but_last(paths), tid);
      }
    }
  }

  lemma lemma_IfMultistepEndsInPhase1ThenEachPathDoes<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    multistep:Armada_Multistep<LPath>,
    states:seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires !multistep.tau
    requires AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau)
    requires states == AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid)
    requires IsPhase1(arr, s', multistep.tid)
    ensures  forall s :: s in states ==> arr.l.get_thread_pc(s, multistep.tid).Some?
    ensures  forall i :: 0 < i < |states| ==> arr.is_phase1(arr.l.get_thread_pc(states[i], multistep.tid).v)
  {
    var pos := |states|-1;
    lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
    while pos > 0
      invariant 0 <= pos < |states|
      invariant arr.l.get_thread_pc(states[pos], multistep.tid).Some?
      invariant pos > 0 ==> arr.is_phase1(arr.l.get_thread_pc(states[pos], multistep.tid).v)
      invariant forall i :: pos <= i < |states| ==> arr.l.get_thread_pc(states[i], multistep.tid).Some?
      invariant forall i :: pos < i < |states| ==> arr.is_phase1(arr.l.get_thread_pc(states[i], multistep.tid).v)
      decreases pos
    {
      var prev_pos := pos-1;
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, prev_pos);
      var pc := arr.l.get_thread_pc(states[prev_pos], multistep.tid);
      var pc' := arr.l.get_thread_pc(states[prev_pos+1], multistep.tid);
      assert pc'.Some? && arr.is_phase1(pc'.v);
      assert arr.l.path_valid(states[prev_pos], multistep.steps[prev_pos], multistep.tid);
      assert arr.l.state_ok(states[prev_pos]);
      assert states[prev_pos+1] == arr.l.path_next(states[prev_pos], multistep.steps[prev_pos], multistep.tid);
      assert pc.Some?;
      if prev_pos > 0 {
        assert arr.is_phase1(pc.v);
        assert IsPhase1(arr, states[prev_pos], multistep.tid);
      }
      pos := prev_pos;
    }
  }

  lemma lemma_IfMultistepStartsInPhase2ThenEachPathDoes<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    multistep:Armada_Multistep<LPath>,
    states:seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires !multistep.tau
    requires AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau)
    requires states == AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid)
    requires IsPhase2(arr, s, multistep.tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], multistep.tid)
  {
    if |states| == 1 {
      return;
    }

    var pos := 0;
    lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
    while pos < |states|-2
      invariant 0 <= pos <= |states|-2
      invariant arr.l.get_thread_pc(states[pos], multistep.tid).Some?
      invariant arr.is_phase2(arr.l.get_thread_pc(states[pos], multistep.tid).v)
      invariant forall i :: 0 <= i <= pos ==> arr.l.get_thread_pc(states[i], multistep.tid).Some?
      invariant forall i :: 0 <= i <= pos ==> arr.is_phase2(arr.l.get_thread_pc(states[i], multistep.tid).v)
      decreases |states|-pos
    {
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, pos);
      var pc := arr.l.get_thread_pc(states[pos], multistep.tid);
      var pc' := arr.l.get_thread_pc(states[pos+1], multistep.tid);
      assert pc.Some? && arr.is_phase2(pc.v);
      assert arr.l.path_valid(states[pos], multistep.steps[pos], multistep.tid);
      assert states[pos+1] == arr.l.path_next(states[pos], multistep.steps[pos], multistep.tid);
      var next_pos := pos+1;
      assert 0 < next_pos < |multistep.steps|;
      assert arr.l.get_thread_pc(states[next_pos], multistep.tid).Some?
               && arr.l.is_pc_nonyielding(arr.l.get_thread_pc(states[next_pos], multistep.tid).v);
      assert pc'.Some?;
      assert arr.is_phase2(pc'.v);
      pos := pos + 1;
    }
  }

  lemma lemma_TakingAtomicMultistepKeepsThreadYielding<State(!new), Path(!new), PC(!new)>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    multistep:Armada_Multistep<Path>,
    tid:Armada_ThreadHandle
    )
    requires AtomicTauLeavesPCUnchanged(asf)
    requires AtomicThreadCantAffectOtherThreadPCExceptViaFork(asf)
    requires AtomicPathRequiresOK(asf)
    requires AtomicNextMultistep(asf, s, s', multistep.steps, multistep.tid, multistep.tau)
    requires asf.state_ok(s) ==> AtomicThreadYielding(asf, s, tid)
    ensures  asf.state_ok(s') ==> AtomicThreadYielding(asf, s', tid)
  {
    var pc' := asf.get_thread_pc(s', tid);
    var states := AtomicGetStateSequence(asf, s, multistep.steps, multistep.tid);
    lemma_AtomicNextLastElement(asf, s, s', multistep.steps, multistep.tid, states);

    if multistep.tau {
      return;
    }

    if multistep.tid == tid {
      return;
    }

    var pos := 0;
    while pos < |multistep.steps|
      invariant 0 <= pos <= |multistep.steps|
      invariant asf.state_ok(states[pos]) ==> AtomicThreadYielding(asf, states[pos], tid)
      decreases |multistep.steps|-pos
    {
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(asf, s, s', multistep.steps, multistep.tid, states, pos);
      pos := pos + 1;
    }
  }

  lemma lemma_StateAmongAnnotatedReachablesHasThreadYielding<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires s in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    ensures  arr.l.state_ok(s) ==> AtomicThreadYielding(arr.l, s, tid)
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    reveal_AnnotatedReachables();
    var ab :| AnnotatedBehaviorSatisfiesSpec(ab, rspec) && last(ab.states) == s;
    var pos := 0;
    while pos < |ab.states|-1
      invariant 0 <= pos < |ab.states|
      invariant arr.l.state_ok(ab.states[pos]) ==> AtomicThreadYielding(arr.l, ab.states[pos], tid)
      decreases |ab.states|-pos
    {
      var subpos := 0;
      var s := ab.states[pos];
      var s' := ab.states[pos+1];
      var path := ab.trace[pos];
      assert ActionTuple(ab.states[pos], ab.states[pos+1], ab.trace[pos]) in rspec.next;
      lemma_TakingAtomicMultistepKeepsThreadYielding(arr.l, ab.states[pos], ab.states[pos+1], ab.trace[pos], tid);
      pos := pos + 1;
    }
  }

  lemma lemma_AtomicNextMultiplePathsTransitive<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    paths1:seq<LPath>,
    paths2:seq<LPath>,
    tid:Armada_ThreadHandle
    )
    requires AtomicNextMultiplePaths(arr.l, s1, s2, paths1, tid)
    requires AtomicNextMultiplePaths(arr.l, s2, s3, paths2, tid)
    ensures  AtomicNextMultiplePaths(arr.l, s1, s3, paths1 + paths2, tid)
  {
    if |paths1| > 0 {
      var s_mid := arr.l.path_next(s1, paths1[0], tid);
      lemma_AtomicNextMultiplePathsTransitive(arr, s_mid, s2, s3, paths1[1..], paths2, tid);
      assert AtomicNextMultiplePaths(arr.l, s_mid, s3, paths1[1..] + paths2, tid);
      var paths3 := paths1 + paths2;
      assert paths3[0] == paths1[0];
      assert paths3[1..] == paths1[1..] + paths2;
    }
    else {
      assert s1 == s2;
      assert paths1 + paths2 == paths2;
    }
  }

  lemma lemma_ExecutingPathDoesntChangeOtherActorPCType<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    path:LPath,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.l.path_valid(s, path, tid)
    requires s' == arr.l.path_next(s, path, tid)
    requires tid != other_tid || arr.l.path_type(path).AtomicPathType_Tau?
    ensures  PCTypesMatch(arr, s, s', other_tid)
  {
  }

  lemma lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    tau:bool,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    requires forall path :: path in paths ==> arr.l.path_type(path).AtomicPathType_Tau? == tau
    requires tau || tid != other_tid
    ensures  PCTypesMatch(arr, s, s', other_tid)
    decreases |paths|
  {
    if |paths| > 0 {
      var s_mid := arr.l.path_next(s, paths[0], tid);
      lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, s, s_mid, paths[0], tid, other_tid);
      lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, s_mid, s', paths[1..], tau, tid, other_tid);
    }
  }

  lemma lemma_ExecutingPathDoesntRemoveOtherActorPC<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    path:LPath,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.l.path_valid(s, path, tid)
    requires s' == arr.l.path_next(s, path, tid)
    requires tid != other_tid || arr.l.path_type(path).AtomicPathType_Tau?
    ensures  arr.l.get_thread_pc(s, other_tid).Some? ==> arr.l.get_thread_pc(s', other_tid).Some?
  {
  }

  lemma lemma_ExecutingPathSequenceDoesntRemoveOtherActorPC<LState, LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    tau:bool,
    tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    requires forall path :: path in paths ==> arr.l.path_type(path).AtomicPathType_Tau? == tau
    requires tau || tid != other_tid
    ensures  arr.l.get_thread_pc(s, other_tid).Some? ==> arr.l.get_thread_pc(s', other_tid).Some?
    decreases |paths|
  {
    if |paths| > 0 {
      var s_mid := arr.l.path_next(s, paths[0], tid);
      lemma_ExecutingPathDoesntRemoveOtherActorPC(arr, s, s_mid, paths[0], tid, other_tid);
      lemma_ExecutingPathSequenceDoesntRemoveOtherActorPC(arr, s_mid, s', paths[1..], tau, tid, other_tid);
    }
  }

  lemma lemma_StateAmongAnnotatedReachablesSatisfiesInv<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState
    )
    requires ValidAtomicReductionRequest(arr)
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
      var multistep := ab.trace[pos];
      assert ActionTuple(ab.states[pos], ab.states[pos+1], ab.trace[pos]) in rspec.next;
      assert AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau);
      var states := AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid);
      while subpos < |multistep.steps|
        invariant 0 <= subpos <= |multistep.steps|
        invariant arr.inv(states[subpos])
        decreases |multistep.steps|-subpos
      {
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, subpos);
        subpos := subpos + 1;
      }
      lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
      pos := pos+1;
    }
  }

  lemma lemma_AtomicInvariantHoldsAtIntermediateState<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    inv:State->bool,
    s:State,
    s':State,
    paths:seq<Path>,
    tid:Armada_ThreadHandle,
    states:seq<State>,
    pos:int
    )
    requires AtomicPathPreservesInv(asf, inv)
    requires AtomicNextMultiplePaths(asf, s, s', paths, tid)
    requires states == AtomicGetStateSequence(asf, s, paths, tid)
    requires 0 <= pos < |states|
    requires inv(states[0])
    ensures  inv(states[pos])
    decreases pos
  {
    if pos > 0 {
      var s_mid := asf.path_next(s, paths[0], tid);
      lemma_AtomicInvariantHoldsAtIntermediateState(asf, inv, s_mid, s', paths[1..], tid, states[1..], pos-1);
    }
  }

  //////////////////////////////
  // LEMMA-SPECIFIC PREDICATES
  //////////////////////////////

  predicate PerformRightMoveTrigger(i:int)
  {
    true
  }

  predicate PerformRightMoveThroughPredicate<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
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

  predicate PerformRightMoveRemainingPredicate<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
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

  lemma lemma_PerformRightMoveSingle<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    s1:LState,
    s2:LState,
    s3:LState,
    mover_path:LPath,
    other_path:LPath
    ) returns (
    s2':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires arr.inv(s1)
    requires arr.l.state_ok(s3)

    requires arr.l.path_type(other_path).AtomicPathType_Tau? == other_tau
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?

    requires arr.l.path_valid(s1, mover_path, mover_tid)
    requires s2 == arr.l.path_next(s1, mover_path, mover_tid)
    requires arr.l.path_valid(s2, other_path, other_tid)
    requires s3 == arr.l.path_next(s2, other_path, other_tid)

    requires arr.l.get_thread_pc(s1, mover_tid).Some?
    requires arr.l.get_thread_pc(s2, mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(s2, mover_tid).v)

    ensures  arr.l.path_valid(s1, other_path, other_tid)
    ensures  s2' == arr.l.path_next(s1, other_path, other_tid)
    ensures  arr.l.path_valid(s2', mover_path, mover_tid)
    ensures  s3 == arr.l.path_next(s2', mover_path, mover_tid)
    ensures  OKAndPCTypesMatch(arr, s2', s1, mover_tid)
  {
    assert AtomicReductionSpecModule.RightMoversCommuteConditions(arr, s1, mover_path, other_path, mover_tid, other_tid);
    s2' := arr.l.path_next(s1, other_path, other_tid);
  }

  lemma lemma_PerformRightMoveThroughHelper<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_path:LPath,
    other_paths_before:seq<LPath>,
    other_states_before:seq<LState>,
    other_paths_after:seq<LPath>,
    other_states_after:seq<LState>,
    s2':LState,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |other_states_before| > 0
    requires arr.inv(other_states_before[0])

    requires other_states_before == AtomicGetStateSequence(arr.l, other_states_before[0], other_paths_before, other_tid)
    requires forall path :: path in other_paths_before ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, other_states_before[0], last(other_states_before), other_paths_before, other_tid)

    requires |other_states_after| > 0
    requires arr.l.state_ok(last(other_states_after))
    requires other_states_after == AtomicGetStateSequence(arr.l, other_states_after[0], other_paths_after, other_tid)
    requires forall path :: path in other_paths_after ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, other_states_after[0], last(other_states_after), other_paths_after, other_tid)

    requires arr.l.path_valid(last(other_states_before), mover_path, mover_tid)
    requires other_states_after[0] == arr.l.path_next(last(other_states_before), mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?
    requires arr.l.get_thread_pc(other_states_before[0], mover_tid).Some?
    requires arr.l.get_thread_pc(other_states_after[0], mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(other_states_after[0], mover_tid).v)

    requires |other_paths_after| > 0
    requires |other_states_after| > 1

    requires arr.l.path_valid(last(other_states_before), other_paths_after[0], other_tid)
    requires s2' == arr.l.path_next(last(other_states_before), other_paths_after[0], other_tid)
    requires arr.l.path_valid(s2', mover_path, mover_tid)
    requires other_states_after[1] == arr.l.path_next(s2', mover_path, mover_tid)
    requires OKAndPCTypesMatch(arr, s2', last(other_states_before), mover_tid)

    requires |other_states'| == |(other_states_before + [s2'])| + |other_states_after[1..]| - 1
    requires other_states'[0] == (other_states_before + [s2'])[0]
    requires other_states' == AtomicGetStateSequence(arr.l, other_states'[0],
                                                     (other_paths_before + [other_paths_after[0]]) + other_paths_after[1..], other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'),
                                       (other_paths_before + [other_paths_after[0]]) + other_paths_after[1..], other_tid)
    requires !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before + [s2'], other_states_after[1..],
                                                             other_states')
    requires OKAndPCTypesMatch(arr, last(other_states'), last((other_states_before + [s2'])), mover_tid)
    requires arr.l.path_valid(last(other_states'), mover_path, mover_tid)
    requires last(other_states_after[1..]) == arr.l.path_next(last(other_states'), mover_path, mover_tid)

    ensures  |other_states'| == |other_states_before| + |other_states_after| - 1
    ensures  other_states'[0] == other_states_before[0]
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths_before + other_paths_after, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths_before + other_paths_after, other_tid)
    ensures  !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before, other_states_after, other_states')
    ensures  OKAndPCTypesMatch(arr, last(other_states'), last(other_states_before), mover_tid)
    ensures  arr.l.path_valid(last(other_states'), mover_path, mover_tid)
    ensures  last(other_states_after) == arr.l.path_next(last(other_states'), mover_path, mover_tid)
  {
    calc {
      other_paths_before + other_paths_after;
        { lemma_SequenceIsCarPlusCdr(other_paths_after); }
      other_paths_before + ([other_paths_after[0]] + other_paths_after[1..]);
        { lemma_SequenceConcatenationAssociative(other_paths_before, [other_paths_after[0]], other_paths_after[1..]); }
      (other_paths_before + [other_paths_after[0]]) + other_paths_after[1..];
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
          lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, last(other_states_before), other_states_after[0], mover_path,
                                                          mover_tid, other_tid);
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

  lemma lemma_PerformRightMoveThrough<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_path:LPath,
    other_paths_before:seq<LPath>,
    other_states_before:seq<LState>,
    other_paths_after:seq<LPath>,
    other_states_after:seq<LState>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |other_states_before| > 0
    requires arr.inv(other_states_before[0])

    requires other_states_before == AtomicGetStateSequence(arr.l, other_states_before[0], other_paths_before, other_tid)
    requires forall path :: path in other_paths_before ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, other_states_before[0], last(other_states_before), other_paths_before, other_tid)

    requires |other_states_after| > 0
    requires arr.l.state_ok(last(other_states_after))
    requires other_states_after == AtomicGetStateSequence(arr.l, other_states_after[0], other_paths_after, other_tid)
    requires forall path :: path in other_paths_after ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, other_states_after[0], last(other_states_after), other_paths_after, other_tid)

    requires arr.l.path_valid(last(other_states_before), mover_path, mover_tid)
    requires other_states_after[0] == arr.l.path_next(last(other_states_before), mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?
    requires arr.l.get_thread_pc(other_states_before[0], mover_tid).Some?
    requires arr.l.get_thread_pc(other_states_after[0], mover_tid).Some?
    requires arr.is_phase1(arr.l.get_thread_pc(other_states_after[0], mover_tid).v)

    ensures  |other_states'| == |other_states_before| + |other_states_after| - 1
    ensures  other_states'[0] == other_states_before[0]
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths_before + other_paths_after, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths_before + other_paths_after, other_tid)
    ensures  !other_tau ==> PerformRightMoveThroughPredicate(arr, other_tid, other_states_before, other_states_after, other_states')

    ensures  OKAndPCTypesMatch(arr, last(other_states'), last(other_states_before), mover_tid)
    ensures  arr.l.path_valid(last(other_states'), mover_path, mover_tid)
    ensures  last(other_states_after) == arr.l.path_next(last(other_states'), mover_path, mover_tid)
    decreases |other_paths_after|
  {
    lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, other_states_before[0], last(other_states_before),
                                                            other_paths_before, other_tau, other_tid, mover_tid);
    if |other_paths_after| == 0 {
      other_states' := other_states_before;
      assert other_paths_before + other_paths_after == other_paths_before;
      if !other_tau {
        forall i | |other_states_before|-1 <= i < |other_states'|
          ensures OKAndPCTypesMatch(arr, other_states'[i], other_states_after[i-|other_states_before|+1], other_tid)
        {
          assert i == |other_states_before|-1;
          assert other_states'[i] == last(other_states_before);
          assert other_states_after[i-|other_states_before|+1] == other_states_after[0];
          lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, last(other_states_before), other_states_after[0], mover_path, mover_tid,
                                                          other_tid);
        }
      }
    }
    else {
      lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, other_states_before[0], last(other_states_before), other_paths_before,
                                                    other_tid, other_states_before, |other_states_before|-1);
      forall ensures arr.l.state_ok(other_states_after[1]) {
        if |other_paths_after| == 1 {
          assert other_states_after[1] == last(other_states_after);
        }
        else {
          lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, other_states_after[0], last(other_states_after), other_paths_after,
                                                                 other_tid, other_states_after, 1);
        }
      }
      var s2' := lemma_PerformRightMoveSingle(arr, mover_tid, other_tid, other_tau, last(other_states_before), other_states_after[0],
                                              other_states_after[1], mover_path, other_paths_after[0]);
      lemma_ExtendingStateSequenceWorks(arr.l, other_states_before[0], last(other_states_before), other_paths_before,
                                        other_states_before, other_tid, other_paths_after[0], s2');
      other_states' := lemma_PerformRightMoveThrough(arr, mover_tid, other_tid, other_tau, mover_path,
                                                     other_paths_before + [other_paths_after[0]],
                                                     other_states_before + [s2'],
                                                     other_paths_after[1..], other_states_after[1..]);
      lemma_PerformRightMoveThroughHelper(arr, mover_tid, other_tid, other_tau, mover_path, other_paths_before,
                                          other_states_before, other_paths_after, other_states_after, s2', other_states');
    }
  }

  lemma lemma_PerformRightMoveOne<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_path:LPath,
    initial_state:LState,
    other_paths:seq<LPath>,
    other_states:seq<LState>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires arr.inv(initial_state)

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires IsPhase1(arr, other_states[0], mover_tid)
    requires arr.l.path_valid(initial_state, mover_path, mover_tid)
    requires other_states[0] == arr.l.path_next(initial_state, mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?

    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == initial_state
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  OKAndPCTypesMatch(arr, last(other_states'), initial_state, mover_tid)
    ensures  arr.l.path_valid(last(other_states'), mover_path, mover_tid)
    ensures  last(other_states) == arr.l.path_next(last(other_states'), mover_path, mover_tid)
  {
    other_states' := lemma_PerformRightMoveThrough(arr, mover_tid, other_tid, other_tau, mover_path, [], [initial_state],
                                                   other_paths, other_states);
    assert [] + other_paths == other_paths;

    if !other_tau {
      forall i | 0 <= i < |other_states|
        ensures OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
      {
        assert PerformRightMoveTrigger(i);
      }
    }
  }

  lemma lemma_PerformRightMoveRemainingHelper1<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_paths_before:seq<LPath>,
    mover_states_before:seq<LState>,
    mover_paths_after:seq<LPath>,
    mover_states_after:seq<LState>,
    other_paths:seq<LPath>,
    other_states:seq<LState>,
    other_states_mid:seq<LState>,
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == AtomicGetStateSequence(arr.l, mover_states_before[0], mover_paths_before, mover_tid)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_before[0], last(mover_states_before), mover_paths_before, mover_tid)
    requires forall path :: path in mover_paths_before ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |mover_states_after| > 0
    requires mover_states_after == AtomicGetStateSequence(arr.l, mover_states_after[0], mover_paths_after, mover_tid)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_paths_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_after[0], last(mover_states_after), mover_paths_after, mover_tid)
    requires forall path :: path in mover_paths_after ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |other_states| > 0
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    requires |mover_paths_before| > 0
    requires |other_states_mid| == |other_states|
    requires other_states_mid[0] == mover_states_before[|mover_paths_before|-1]
    requires other_states_mid == AtomicGetStateSequence(arr.l, other_states_mid[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states_mid[0], last(other_states_mid), other_paths, other_tid)
    requires !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states_mid[i], other_states[i], other_tid)
  
    requires |other_states'| == |other_states_mid|
    requires other_states'[0] == all_but_last(mover_states_before)[0]
    requires other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    requires !other_tau ==> forall i :: 0 <= i < |other_states_mid| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states_mid[i], other_tid)
    requires |mover_states'| == |all_but_last(mover_states_before)| + |([last(other_states_mid)] + mover_states_after)| - 1
    requires mover_states'[0] == last(other_states')
    requires last(mover_states') == last(([last(other_states_mid)] + mover_states_after))
    requires mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0],
                                                     all_but_last(mover_paths_before) + ([last(mover_paths_before)] + mover_paths_after),
                                                     mover_tid)
    requires AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'),
                                      all_but_last(mover_paths_before) + ([last(mover_paths_before)] + mover_paths_after), mover_tid)

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states_before[0]
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    ensures  |mover_states'| == |mover_states_before| + |mover_states_after| - 1
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(mover_states_after)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0], mover_paths_before + mover_paths_after, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'), mover_paths_before + mover_paths_after, mover_tid)
  {
    calc {
      all_but_last(mover_paths_before) + ([last(mover_paths_before)] + mover_paths_after);
        { lemma_SequenceConcatenationAssociative(all_but_last(mover_paths_before), [last(mover_paths_before)], mover_paths_after); }
      (all_but_last(mover_paths_before) + [last(mover_paths_before)]) + mover_paths_after;
        { lemma_AllButLastPlusLastIsSeq(mover_paths_before); }
      mover_paths_before + mover_paths_after;
    }
    lemma_LastOfConcatenationIsLastOfLatter([last(other_states_mid)], mover_states_after);
  }

  lemma lemma_PerformRightMoveRemainingHelper2<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_paths_before:seq<LPath>,
    mover_states_before:seq<LState>,
    mover_paths_after:seq<LPath>,
    mover_states_after:seq<LState>,
    other_paths:seq<LPath>,
    other_states:seq<LState>,
    other_states_mid:seq<LState>,
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == AtomicGetStateSequence(arr.l, mover_states_before[0], mover_paths_before, mover_tid)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_before[0], last(mover_states_before), mover_paths_before, mover_tid)
    requires forall path :: path in mover_paths_before ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |mover_states_after| > 0
    requires mover_states_after == AtomicGetStateSequence(arr.l, mover_states_after[0], mover_paths_after, mover_tid)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_paths_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_after[0], last(mover_states_after), mover_paths_after, mover_tid)
    requires forall path :: path in mover_paths_after ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    requires |mover_paths_before| > 0
    requires |other_states_mid| == |other_states|
    requires other_states_mid[0] == mover_states_before[|mover_paths_before|-1]
    requires other_states_mid == AtomicGetStateSequence(arr.l, other_states_mid[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states_mid[0], last(other_states_mid), other_paths, other_tid)
    requires !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states_mid[i], other_states[i], other_tid)
  
    requires |other_states'| == |other_states_mid|
    requires other_states'[0] == all_but_last(mover_states_before)[0]
    requires other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    requires !other_tau ==> forall i :: 0 <= i < |other_states_mid| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states_mid[i], other_tid)
    requires |mover_states'| == |all_but_last(mover_states_before)| + |([last(other_states_mid)] + mover_states_after)| - 1
    requires mover_states'[0] == last(other_states')
    requires last(mover_states') == last(([last(other_states_mid)] + mover_states_after))
    requires mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0],
                                                     all_but_last(mover_paths_before) + ([last(mover_paths_before)] + mover_paths_after),
                                                     mover_tid)
    requires AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'),
                                     all_but_last(mover_paths_before) + ([last(mover_paths_before)] + mover_paths_after), mover_tid)
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
        assert OKAndPCTypesMatch(arr, mover_states'[i],
                                 ([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1],
                                 mover_tid);
        calc {
          arr.l.get_thread_pc(([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1], mover_tid);
          arr.l.get_thread_pc(([last(other_states_mid)] + mover_states_after)[1], mover_tid);
          arr.l.get_thread_pc(mover_states_after[0], mover_tid);
        }
        lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, last(mover_states_before), mover_states_after[0],
                                                                  other_paths, other_tau, other_tid, mover_tid);
        assert last(mover_states_before) == mover_states_before[i];
      }
    }

    forall i | |mover_states_before|-1 <= i < |mover_states'|
      ensures OKAndPCTypesMatch(arr, mover_states'[i], mover_states_after[i-|mover_states_before|+1], mover_tid)
    {
      assert PerformRightMoveTrigger(i);
      assert |all_but_last(mover_states_before)|-1 <= i < |mover_states'|;
      assert OKAndPCTypesMatch(arr, mover_states'[i],
                               ([last(other_states_mid)] + mover_states_after)[i-|all_but_last(mover_states_before)|+1],
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

  lemma lemma_PerformRightMoveRemaining<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_paths_before:seq<LPath>,
    mover_states_before:seq<LState>,
    mover_paths_after:seq<LPath>,
    mover_states_after:seq<LState>,
    other_paths:seq<LPath>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states_before| > 0
    requires arr.inv(mover_states_before[0])
    requires arr.l.get_thread_pc(mover_states_before[0], mover_tid).Some?

    requires mover_states_before == AtomicGetStateSequence(arr.l, mover_states_before[0], mover_paths_before, mover_tid)
    requires forall s :: s in mover_states_before ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_before| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_before[i], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_before[0], last(mover_states_before), mover_paths_before, mover_tid)
    requires forall path :: path in mover_paths_before ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |mover_states_after| > 0
    requires mover_states_after == AtomicGetStateSequence(arr.l, mover_states_after[0], mover_paths_after, mover_tid)
    requires forall s :: s in mover_states_after ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states_after| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[i], mover_tid).v)
    requires |mover_paths_before| > 0 ==> arr.is_phase1(arr.l.get_thread_pc(mover_states_after[0], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states_after[0], last(mover_states_after), mover_paths_after, mover_tid)
    requires forall path :: path in mover_paths_after ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states_before)
    requires last(other_states) == mover_states_after[0]
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states_before[0]
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  |mover_states'| == |mover_states_before| + |mover_states_after| - 1
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(mover_states_after)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0], mover_paths_before + mover_paths_after, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'), mover_paths_before + mover_paths_after, mover_tid)
    ensures  PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states')

    decreases |mover_paths_before|
  {
    lemma_ExecutingPathSequenceDoesntRemoveOtherActorPC(arr, other_states[0], last(other_states), other_paths, other_tau,
                                                        other_tid, mover_tid);
    lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, other_states[0], last(other_states), other_paths, other_tau,
                                                            other_tid, mover_tid);
    if |mover_paths_before| == 0 {
      mover_states' := mover_states_after;
      other_states' := other_states;
      assert mover_paths_before + mover_paths_after == mover_paths_after;
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states');
    }
    else {
      lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, mover_states_before[0], last(mover_states_before), mover_paths_before,
                                                    mover_tid, mover_states_before, |mover_paths_before|-1);
      assert arr.inv(mover_states_before[|mover_paths_before|-1]);
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, mover_states_before[0], last(mover_states_before), mover_paths_before,
                                                             mover_tid, mover_states_before, |mover_paths_before|-1);
      assert arr.l.path_valid(mover_states_before[|mover_paths_before|-1], mover_paths_before[|mover_paths_before|-1], mover_tid);
      assert arr.l.path_valid(mover_states_before[|mover_paths_before|-1], last(mover_paths_before), mover_tid);

      var other_states_mid :=
        lemma_PerformRightMoveOne(arr, mover_tid, other_tid, other_tau, last(mover_paths_before),
                                  mover_states_before[|mover_paths_before|-1], other_paths, other_states);

      lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, mover_states_before[0], last(mover_states_before), mover_paths_before,
                                                       mover_states_before, mover_tid);
      calc {
        other_states_mid[0];
        mover_states_before[|mover_paths_before|-1];
        last(all_but_last(mover_states_before));
      }

      var mover_states_after' := [last(other_states_mid)] + mover_states_after;
      var mover_paths_after' := [last(mover_paths_before)] + mover_paths_after;
      assert mover_states_after'[0] == last(other_states_mid);
      assert mover_states_after'[1..] == mover_states_after;
      assert mover_paths_after'[0] == last(mover_paths_before);
      assert mover_paths_after'[1..] == mover_paths_after;
      assert AtomicNextMultiplePaths(arr.l, mover_states_after'[0], last(mover_states_after'), mover_paths_after', mover_tid);

      mover_states', other_states' :=
        lemma_PerformRightMoveRemaining(arr, mover_tid, other_tid, other_tau, all_but_last(mover_paths_before),
                                        all_but_last(mover_states_before), [last(mover_paths_before)] + mover_paths_after,
                                        [last(other_states_mid)] + mover_states_after, other_paths, other_states_mid);
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, all_but_last(mover_states_before),
                                                [last(other_states_mid)] + mover_states_after, mover_states');
      lemma_PerformRightMoveRemainingHelper1(arr, mover_tid, other_tid, other_tau, mover_paths_before, mover_states_before,
                                             mover_paths_after, mover_states_after, other_paths, other_states, other_states_mid,
                                             mover_states', other_states');
      lemma_PerformRightMoveRemainingHelper2(arr, mover_tid, other_tid, other_tau, mover_paths_before, mover_states_before,
                                             mover_paths_after, mover_states_after, other_paths, other_states, other_states_mid,
                                             mover_states', other_states');
      assert PerformRightMoveRemainingPredicate(arr, mover_tid, mover_states_before, mover_states_after, mover_states');
    }
  }

  lemma lemma_PerformRightMoveAll<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_paths:seq<LPath>,
    mover_states:seq<LState>,
    other_paths:seq<LPath>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires other_tau || other_tid != mover_tid

    requires |mover_states| > 0
    requires arr.inv(mover_states[0])
    requires arr.l.get_thread_pc(mover_states[0], mover_tid).Some?
    requires mover_states == AtomicGetStateSequence(arr.l, mover_states[0], mover_paths, mover_tid)
    requires forall s :: s in mover_states ==> arr.l.get_thread_pc(s, mover_tid).Some?
    requires forall i :: 0 < i < |mover_states| ==> arr.is_phase1(arr.l.get_thread_pc(mover_states[i], mover_tid).v)
    requires AtomicNextMultiplePaths(arr.l, mover_states[0], last(mover_states), mover_paths, mover_tid)
    requires forall path :: path in mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires |other_states| > 0
    requires arr.l.state_ok(last(other_states))
    requires other_states[0] == last(mover_states)
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    ensures  |other_states'| == |other_states|
    ensures  other_states'[0] == mover_states[0]
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)

    ensures  |mover_states'| == |mover_states|
    ensures  mover_states'[0] == last(other_states')
    ensures  last(mover_states') == last(other_states)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0], mover_paths, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'), mover_paths, mover_tid)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
  {
    lemma_ExecutingPathSequenceDoesntRemoveOtherActorPC(arr, other_states[0], last(other_states), other_paths, other_tau,
                                                        other_tid, mover_tid);
    lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, other_states[0], last(other_states), other_paths, other_tau,
                                                            other_tid, mover_tid);

    mover_states', other_states' := lemma_PerformRightMoveRemaining(arr, mover_tid, other_tid, other_tau, mover_paths,
                                                                    mover_states, [], [last(other_states)], other_paths, other_states);
    assert mover_paths + [] == mover_paths;

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

  lemma lemma_PerformRightMove<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    multistep1:Armada_Multistep<LPath>,
    multistep2:Armada_Multistep<LPath>
    ) returns (
    s2':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires s1 in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    requires arr.l.state_ok(s3)
    requires AtomicNextMultistep(arr.l, s1, s2, multistep1.steps, multistep1.tid, multistep1.tau)
    requires AtomicNextMultistep(arr.l, s2, s3, multistep2.steps, multistep2.tid, multistep2.tau)
    requires !multistep1.tau
    requires multistep2.tau || multistep2.tid != multistep1.tid
    requires IsPhase1(arr, s2, multistep1.tid)
    ensures  AtomicNextMultistep(arr.l, s1, s2', multistep2.steps, multistep2.tid, multistep2.tau)
    ensures  AtomicNextMultistep(arr.l, s2', s3, multistep1.steps, multistep1.tid, multistep1.tau)
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, s1);
    assert arr.inv(s1);
    var mover_states := AtomicGetStateSequence(arr.l, s1, multistep1.steps, multistep1.tid);
    lemma_IfMultistepEndsInPhase1ThenEachPathDoes(arr, s1, s2, multistep1, mover_states);
    var other_states := AtomicGetStateSequence(arr.l, s2, multistep2.steps, multistep2.tid);
    lemma_AtomicNextLastElement(arr.l, s1, s2, multistep1.steps, multistep1.tid, mover_states);
    lemma_AtomicNextLastElement(arr.l, s2, s3, multistep2.steps, multistep2.tid, other_states);
    var mover_states', other_states' :=
      lemma_PerformRightMoveAll(arr, multistep1.tid, multistep2.tid, multistep2.tau, multistep1.steps, mover_states,
                                multistep2.steps, other_states);
    s2' := last(other_states');
    lemma_AtomicNextLastElement(arr.l, s2', s3, multistep1.steps, multistep1.tid, mover_states');
  }

  //////////////////////////////////////////
  // LEFT-MOVER ENABLEMENT LEMMAS
  //////////////////////////////////////////

  lemma lemma_GenerateLeftMoverSequenceOfSubpaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    ) returns (
    states:seq<LState>,
    trace:seq<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.inv(s)
    requires arr.l.state_ok(s)
    requires IsPhase2(arr, s, tid)
    requires AtomicThreadYielding(arr.l, s, tid)
    ensures  states == AtomicGetStateSequence(arr.l, s, trace, tid)
    ensures  AtomicNextMultiplePaths(arr.l, s, last(states), trace, tid)
    ensures  states[0] == s
    ensures  arr.l.state_ok(last(states)) ==> !IsPhase2(arr, last(states), tid) && AtomicThreadYielding(arr.l, last(states), tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    ensures  forall path :: path in trace ==> !arr.l.path_type(path).AtomicPathType_Tau?
  {
    states := [s];
    trace := [];

    while arr.l.state_ok(last(states)) && IsPhase2(arr, last(states), tid)
      invariant states == AtomicGetStateSequence(arr.l, s, trace, tid)
      invariant AtomicNextMultiplePaths(arr.l, s, last(states), trace, tid)
      invariant states[0] == s
      invariant arr.inv(last(states))
      invariant arr.l.state_ok(last(states)) && !AtomicThreadYielding(arr.l, last(states), tid) ==> IsPhase2(arr, last(states), tid)
      invariant forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
      invariant forall path :: path in trace ==> !arr.l.path_type(path).AtomicPathType_Tau?
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
      var path := arr.generate_left_mover(s_current, tid);
      assert AtomicReductionSpecModule.LeftMoversAlwaysEnabledConditions(arr, s_current, tid);
      assert arr.l.path_valid(s_current, path, tid) && !arr.l.path_type(path).AtomicPathType_Tau?;
      var s_next := arr.l.path_next(s_current, path, tid);
      assert 0 <= arr.left_mover_generation_progress(s_next, tid) < arr.left_mover_generation_progress(s_current, tid);
      lemma_ExtendingStateSequenceWorks(arr.l, s, s_current, trace, states, tid, path, s_next);
      trace := trace + [path];
      states := states + [s_next];

      forall i | 0 <= i < |states|-1
        ensures IsPhase2(arr, states[i], tid)
      {
        assert states[i] == states_current[i];
      }
    }
  }

  lemma lemma_GenerateLeftMoverSequence<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    ) returns (
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.inv(s)
    requires arr.l.state_ok(s)
    requires IsPhase2(arr, s, tid)
    requires AtomicThreadYielding(arr.l, s, tid)
    ensures  StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    ensures  states[0] == s
    ensures  arr.l.state_ok(last(states)) ==> !IsPhase2(arr, last(states), tid) && AtomicThreadYielding(arr.l, last(states), tid)
    ensures  forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    ensures  forall multistep :: multistep in trace ==> !multistep.tau && multistep.tid == tid
  {
    var rspec := GetRefinementViaReductionLSpec(arr);
    var single_states, single_trace := lemma_GenerateLeftMoverSequenceOfSubpaths(arr, s, tid);

    states := [s];
    trace := [];
    var partial_paths := [];
    var partial_states := [s];

    var pos := 0;

    assert !arr.l.state_ok(single_states[pos]) || AtomicThreadYielding(arr.l, single_states[pos], tid) ==> |partial_paths| == 0;
    while pos < |single_trace|
      invariant 0 <= pos <= |single_trace|
      invariant |states| > 0
      invariant states[0] == s
      invariant StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
      invariant if pos < |single_trace| then
                  (forall state :: state in states ==> IsPhase2(arr, state, tid))
                else
                  (forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid))
      invariant forall multistep :: multistep in trace ==> !multistep.tau && multistep.tid == tid
      invariant !arr.l.state_ok(last(states)) || AtomicThreadYielding(arr.l, last(states), tid)
      invariant !arr.l.state_ok(single_states[pos]) || AtomicThreadYielding(arr.l, single_states[pos], tid) ==> |partial_paths| == 0
      invariant AtomicNextMultiplePaths(arr.l, last(states), single_states[pos], partial_paths, tid)
      invariant partial_states == AtomicGetStateSequence(arr.l, last(states), partial_paths, tid)
      invariant forall i :: 0 < i < |partial_states| ==> !AtomicThreadYielding(arr.l, partial_states[i], tid)
      invariant forall path :: path in partial_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
      decreases |single_trace| - pos
    {
      var s_current := single_states[pos];
      var s_next := single_states[pos+1];
      var next_path := single_trace[pos];

      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, single_states[0], last(single_states), single_trace, tid,
                                                             single_states, pos);
      assert arr.l.path_valid(s_current, next_path, tid);
      assert s_next == arr.l.path_next(s_current, next_path, tid);

      lemma_ExtendingStateSequenceWorks(arr.l, last(states), s_current, partial_paths, partial_states, tid, next_path, s_next);

      var upper := |partial_states|;
      assert forall i :: 0 < i < upper ==> !AtomicThreadYielding(arr.l, partial_states[i], tid);
      partial_paths := partial_paths + [next_path];
      partial_states := partial_states + [s_next];
      assert upper == |partial_paths|;
      assert forall i :: 0 < i < |partial_paths| ==> !AtomicThreadYielding(arr.l, partial_states[i], tid);

      if !arr.l.state_ok(s_next) || AtomicThreadYielding(arr.l, s_next, tid) {
        var multistep := Armada_Multistep(partial_paths, tid, false);

        assert AtomicNextMultistep(arr.l, last(states), s_next, multistep.steps, multistep.tid, multistep.tau);
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
        partial_paths := [];
        partial_states := [s_next];
           
        assert StateNextSeq(states, trace, rspec.next);
      }
      pos := pos + 1;
      assert AtomicNextMultiplePaths(arr.l, last(states), single_states[pos], partial_paths, tid);
    }

    assert |partial_paths| == 0;
    assert pos == |single_trace|;
    assert last(states) == single_states[pos] == last(single_states);
  }

  lemma lemma_LeftMoversAlwaysEnabled<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
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
                 && (forall path :: path in trace ==> rr.idmap(path) == actor)
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

  function CombineMultisteps<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    trace:seq<Armada_Multistep<LPath>>
    ) : seq<LPath>
  {
    if |trace| == 0 then [] else trace[0].steps + CombineMultisteps(arr, trace[1..])
  }

  lemma lemma_CombineMultistepsEffectOnGetStateSequence<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    tid:Armada_ThreadHandle
    )
    requires ValidAtomicReductionRequest(arr)
    requires |trace| > 0
    requires |states| == |trace| + 1
    requires forall i :: 0 <= i < |trace| ==> AtomicNextMultiplePaths(arr.l, states[i], states[i+1], trace[i].steps, tid)
    ensures  AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace), tid) ==
             AtomicGetStateSequence(arr.l, states[0], trace[0].steps, tid) +
             AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]), tid)[1..]
    decreases |trace[0].steps|
  {
    var pos := 0;
    assert AtomicNextMultiplePaths(arr.l, states[pos], states[pos+1], trace[pos].steps, tid);
    var multistep := trace[0];

    if |multistep.steps| == 0 {
      calc {
        AtomicGetStateSequence(arr.l, states[0], trace[0].steps, tid) +
          AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]), tid)[1..];
         { assert trace[0].steps == [];
           assert AtomicGetStateSequence(arr.l, states[0], trace[0].steps, tid) == [states[0]]; }
        [states[0]] + AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]), tid)[1..];
          { assert states[1] == states[0]; }
        [states[0]] + AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]), tid)[1..];
          { assert AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]), tid)[0] == states[0]; }
        AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace[1..]), tid);
          { assert CombineMultisteps(arr, trace) == CombineMultisteps(arr, trace[1..]); }
        AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace), tid);
      }
    }
    else {
      var s_mid := arr.l.path_next(states[0], multistep.steps[0], tid);
      var new_trace0 := multistep.(steps := multistep.steps[1..]);
      var states' := states[0 := s_mid];
      var trace' := trace[0 := new_trace0];

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in GetRefinementViaReductionLSpec(arr).next} | 0 <= i < |trace'|
        ensures AtomicNextMultiplePaths(arr.l, states'[i], states'[i+1], trace'[i].steps, tid);
      {
        assert AtomicNextMultiplePaths(arr.l, states[i], states[i+1], trace[i].steps, tid);
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
      assert AtomicGetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace'), tid) ==
             AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
             AtomicGetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]), tid)[1..];

      calc {
        CombineMultisteps(arr, trace');
        trace'[0].steps + CombineMultisteps(arr, trace'[1..]);
        new_trace0.steps + CombineMultisteps(arr, trace'[1..]);
        multistep.steps[1..] + CombineMultisteps(arr, trace[1..]);
          { lemma_DroppingHeadOfConcatenation(multistep.steps, CombineMultisteps(arr, trace[1..])); }
        (multistep.steps + CombineMultisteps(arr, trace[1..]))[1..];
        CombineMultisteps(arr, trace)[1..];
      }

      calc {
        AtomicGetStateSequence(arr.l, states[0], CombineMultisteps(arr, trace), tid);
        [states[0]] + AtomicGetStateSequence(arr.l, s_mid, CombineMultisteps(arr, trace)[1..], tid);
        [states[0]] + AtomicGetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace)[1..], tid);
          { assert CombineMultisteps(arr, trace') == CombineMultisteps(arr, trace)[1..]; }
        [states[0]] + AtomicGetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace'), tid);
          { assert AtomicGetStateSequence(arr.l, states'[0], CombineMultisteps(arr, trace'), tid) ==
                   AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
                   AtomicGetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]), tid)[1..]; }
        [states[0]] + (AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
                       AtomicGetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]), tid)[1..]);
          { lemma_SequenceConcatenationAssociative(
              [states[0]],
              AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid),
              AtomicGetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]), tid)[1..]); }
        [states[0]] + AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
             AtomicGetStateSequence(arr.l, states'[1], CombineMultisteps(arr, trace'[1..]), tid)[1..];
        [states[0]] + AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
             AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace'[1..]), tid)[1..];
        [states[0]] + AtomicGetStateSequence(arr.l, states'[0], trace'[0].steps, tid) +
             AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]), tid)[1..];
        AtomicGetStateSequence(arr.l, states[0], trace[0].steps, tid) +
          AtomicGetStateSequence(arr.l, states[1], CombineMultisteps(arr, trace[1..]), tid)[1..];

      }
    }
  }

  lemma lemma_CombineMultistepsCreatesValidHPathHelper<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    multistep:Armada_Multistep<LPath>,
    states:seq<LState>,
    i:int
    )
    requires states == AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid)
    requires !multistep.tau
    requires AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau)
    requires 0 < i < |states|
    requires i == |states|-1 ==> arr.l.state_ok(s')
    requires i == |states|-1 ==> IsPhase1(arr, s', multistep.tid) || IsPhase2(arr, s', multistep.tid)
    ensures  IsNonyieldingOrInPhase(arr, states[i], multistep.tid)
  {
    var pc := arr.l.get_thread_pc(states[i], multistep.tid);
    if i < |states|-1 {
      assert pc.Some? && arr.l.is_pc_nonyielding(pc.v);
    }
    else {
      assert i == |states|-1;
      assert states[i] == last(states);
      lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
      assert last(states) == s';
      assert IsPhase1(arr, states[i], multistep.tid) || IsPhase2(arr, states[i], multistep.tid);
      assert pc.Some? && (arr.is_phase1(pc.v) || arr.is_phase2(pc.v));
    }
    assert IsNonyieldingOrInPhase(arr, states[i], multistep.tid);
  }

  lemma lemma_CombineMultistepsCreatesValidHPath<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    tid:Armada_ThreadHandle,
    combined:seq<LPath>,
    all_states:seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> !multistep.tau && multistep.tid == tid
    requires combined == CombineMultisteps(arr, trace)
    requires forall i :: 0 < i < |trace| ==> arr.l.state_ok(states[i])
    requires forall i :: 0 < i < |trace| ==> IsPhase1(arr, states[i], tid) || IsPhase2(arr, states[i], tid)
    requires all_states == AtomicGetStateSequence(arr.l, states[0], combined, tid)
    ensures  forall i :: 0 < i < |combined| ==> IsNonyieldingOrInPhase(arr, all_states[i], tid)
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    if |trace| > 0 {
      forall i | 0 <= i < |trace|
        ensures AtomicNextMultiplePaths(arr.l, states[i], states[i+1], trace[i].steps, tid)
      {
        assert ActionTuple(states[i], states[i+1], trace[i]) in rspec.next;
      }
      
      lemma_CombineMultistepsEffectOnGetStateSequence(arr, states, trace, tid);

      var states' := states[1..];
      var trace' := trace[1..];
      var combined' := CombineMultisteps(arr, trace');
      var all_states' := AtomicGetStateSequence(arr.l, states'[0], combined', tid);

      forall i {:trigger ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next} | 0 <= i < |trace'|
        ensures ActionTuple(states'[i], states'[i+1], trace'[i]) in rspec.next
      {
        var next := i+1;
        assert ActionTuple(states[next], states[next+1], trace[next]) in rspec.next;
      }

      lemma_CombineMultistepsCreatesValidHPath(arr, states[1..], trace[1..], tid, combined', all_states');

      var multistep := trace[0];
      assert multistep.tid == tid;
      var first_states := AtomicGetStateSequence(arr.l, states[0], multistep.steps, tid);
      assert all_states == first_states + all_states'[1..];
      forall i | 0 < i < |combined|
        ensures IsNonyieldingOrInPhase(arr, all_states[i], tid)
      {
        if i < |first_states| {
          var zero := 0;
          assert ActionTuple(states[zero], states[zero+1], trace[zero]) in rspec.next;
          assert AtomicNextMultistep(arr.l, states[zero], states[zero+1], multistep.steps, multistep.tid, multistep.tau);
          var one := zero+1;
          lemma_AtomicNextLastElement(arr.l, states[zero], states[zero+1], multistep.steps, multistep.tid, first_states);
          assert all_states[i] == first_states[i];
          if i == |first_states|-1 {
            assert |combined| > |combined'|;
            assert |states| > 2;
            assert 0 < one < |trace|;
            assert arr.l.state_ok(states[one]);
            assert IsPhase1(arr, states[one], tid) || IsPhase2(arr, states[one], tid);
          }
          lemma_CombineMultistepsCreatesValidHPathHelper(arr, states[zero], states[one], multistep, first_states, i);
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

  lemma lemma_CombineMultistepsPreservesStateNextSeq<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    tid:Armada_ThreadHandle,
    combined:seq<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> !multistep.tau && multistep.tid == tid
    requires combined == CombineMultisteps(arr, trace)
    ensures  AtomicNextMultiplePaths(arr.l, states[0], last(states), combined, tid)
    ensures  forall path :: path in combined ==> !arr.l.path_type(path).AtomicPathType_Tau?
  {
    var rspec := GetRefinementViaReductionLSpec(arr);

    if |trace| > 0 {
      var pos := 0;
      assert ActionTuple(states[pos], states[pos+1], trace[pos]) in rspec.next;
      var multistep := trace[0];
      assert AtomicNextMultistep(arr.l, states[pos], states[pos+1], multistep.steps, multistep.tid, multistep.tau);

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
      lemma_AtomicNextMultiplePathsTransitive(arr, states[0], states[1], last(states), multistep.steps, combined', tid);
    }
  }

  lemma lemma_LiftActionSequenceCaseMultiplePaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hmultistep:Armada_Multistep<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> rr.idmap(multistep) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 0 < i < |trace| ==> !rr.crashed(states[i])
    requires forall i :: 0 < i < |trace| ==> var s := states[i]; rr.phase1(s, actor) || rr.phase2(s, actor)
    requires |trace| > 1
    requires actor.Some?
    ensures  ActionTuple(states[0], last(states), hmultistep) in rr.hspec.next
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

    var paths := CombineMultisteps(arr, trace);
    hmultistep := Armada_Multistep(paths, actor.v, false);
    lemma_CombineMultistepsPreservesStateNextSeq(arr, states, trace, actor.v, paths);

    var all_states := AtomicGetStateSequence(arr.l, states[0], paths, actor.v);
    forall i | 1 <= i < |states|-1
      ensures IsPhase1(arr, states[i], actor.v) || IsPhase2(arr, states[i], actor.v)
    {
      assert rr.phase1(states[i], actor) || rr.phase2(states[i], actor);
    }

    lemma_CombineMultistepsCreatesValidHPath(arr, states, trace, actor.v, paths, all_states);
    assert GenericNextReduced(arr, states[0], last(states), paths, actor.v, false);
  }

  lemma lemma_LiftActionSequenceCasePath<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hmultistep:Armada_Multistep<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> rr.idmap(multistep) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 1 <= i < |states|-1 ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    requires |trace| == 1
    ensures  ActionTuple(states[0], last(states), hmultistep) in rr.hspec.next
  {
    var s := states[0];
    var s' := last(states);
    hmultistep := trace[0];
    var pos := 0;
    assert ActionTuple(states[pos], states[pos+1], trace[pos]) in GetRefinementViaReductionLSpec(arr).next;
    assert AtomicNextMultistep(arr.l, states[0], states[0+1], hmultistep.steps, hmultistep.tid, hmultistep.tau);
    assert rr.idmap(trace[0]) == actor;
    assert !hmultistep.tau ==> actor == Some(hmultistep.tid);
    assert GenericNextReduced(arr, s, s', hmultistep.steps, hmultistep.tid, hmultistep.tau);
  }

  lemma lemma_LiftActionSequenceCaseTau<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hmultistep:Armada_Multistep<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> rr.idmap(multistep) == actor
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 1 <= i < |states|-1 ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    requires |trace| > 1
    requires actor.None?
    ensures  ActionTuple(states[0], last(states), hmultistep) in rr.hspec.next
  {
    var pos := 1;
    assert 1 <= pos < |states|-1;
    assert rr.phase1(states[pos], actor) || rr.phase2(states[pos], actor);
    assert false;
  }

  lemma lemma_LiftActionSequence<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    states:seq<LState>,
    trace:seq<Armada_Multistep<LPath>>,
    actor:Option<Armada_ThreadHandle>
    ) returns (
    hmultistep:Armada_Multistep<LPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires StateNextSeq(states, trace, GetRefinementViaReductionLSpec(arr).next)
    requires forall multistep :: multistep in trace ==> rr.idmap(multistep) == actor
    requires |states| > 1
    requires !rr.phase1(states[0], actor)
    requires !rr.phase2(states[0], actor)
    requires var s := last(states); !rr.crashed(s) ==> !rr.phase1(s, actor) && !rr.phase2(s, actor)
    requires forall i :: 0 < i < |trace| ==> !rr.crashed(states[i])
    requires forall i :: 0 < i < |trace| ==> rr.phase1(states[i], actor) || rr.phase2(states[i], actor)
    ensures  ActionTuple(states[0], last(states), hmultistep) in rr.hspec.next
  {
    if |trace| == 1 {
      hmultistep := lemma_LiftActionSequenceCasePath(arr, rr, states, trace, actor);
    }
    else if actor.None? {
      hmultistep := lemma_LiftActionSequenceCaseTau(arr, rr, states, trace, actor);
    }
    else {
      hmultistep := lemma_LiftActionSequenceCaseMultiplePaths(arr, rr, states, trace, actor);
    }
  }

  lemma lemma_ActionSequencesLiftable<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  ActionSequencesLiftable(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall states, trace, actor
      {:trigger RefinementViaReductionSpecModule.ActionSequencesLiftableConditions(rr, states, trace, actor)}
      | RefinementViaReductionSpecModule.ActionSequencesLiftableConditions(rr, states, trace, actor)
      ensures exists hmultistep :: ActionTuple(states[0], last(states), hmultistep) in rr.hspec.next
    {
      var hmultistep := lemma_LiftActionSequence(arr, rr, states, trace, actor);
    }
  }

  //////////////////////////////////////////////////////////////////////////
  // LEMMAS PROVING VALIDITY OF GENERATED CRASHING REDUCTION REQUEST
  //////////////////////////////////////////////////////////////////////////

  lemma lemma_IfAtomicReductionRequestValidThenCrashingCantGoDirectlyFromPhase2ToPhase1<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  CantGoDirectlyFromPhase2ToPhase1(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', multistep | ActionTuple(s, s', multistep) in rr.lspec.next && rr.phase2(s, rr.idmap(multistep))
      ensures !rr.phase1(s', rr.idmap(multistep))
    {
      assert AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau);
      var tid := multistep.tid;
      if |multistep.steps| > 0 {
        var states := AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid);
        var pos := 0;
        while pos < |multistep.steps|-1
          invariant 0 <= pos < |multistep.steps|
          invariant IsPhase2(arr, states[pos], tid)
          decreases |multistep.steps| - pos
        {
          lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, pos);
          assert arr.l.path_valid(states[pos], multistep.steps[pos], multistep.tid);
          assert states[pos+1] == arr.l.path_next(states[pos], multistep.steps[pos], multistep.tid);
          var next_pos := pos+1;
          var pc := arr.l.get_thread_pc(states[next_pos], tid).v;
          assert arr.l.is_pc_nonyielding(pc);
          pos := pos+1;
        }
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, pos);
        lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
      }
    }
  }

  lemma lemma_IfAtomicReductionRequestValidThenCrashingPhaseUnaffectedByOtherActorsHelper<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  var rr := GetRefinementViaReductionRequest(arr);
             forall s, s', multistep, actor :: ActionTuple(s, s', multistep) in rr.lspec.next && rr.idmap(multistep) != actor
                ==> && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
                    && (rr.phase2(s, actor) <==> rr.phase2(s', actor))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', multistep, actor | ActionTuple(s, s', multistep) in rr.lspec.next && rr.idmap(multistep) != actor
      ensures rr.phase1(s, actor) <==> rr.phase1(s', actor)
      ensures rr.phase2(s, actor) <==> rr.phase2(s', actor)
    {
      if actor.Some? {
        assert AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau);
        var tid := actor.v;
        var states := AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid);
        var pc := arr.l.get_thread_pc(s, tid);
        var phase1 := pc.Some? && arr.is_phase1(pc.v);
        var phase2 := pc.Some? && arr.is_phase2(pc.v);
        var pos := 0;
        while pos < |multistep.steps|
          invariant 0 <= pos <= |multistep.steps|
          invariant phase1 <==> IsPhase1(arr, states[pos], tid)
          invariant phase2 <==> IsPhase2(arr, states[pos], tid)
          decreases |multistep.steps| - pos
        {
          lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, pos);
          assert arr.l.path_valid(states[pos], multistep.steps[pos], multistep.tid);
          assert states[pos+1] == arr.l.path_next(states[pos], multistep.steps[pos], multistep.tid);
          var pc1 := arr.l.get_thread_pc(states[pos], tid);
          var pc2 := arr.l.get_thread_pc(states[pos+1], tid);
          assert pc1 != pc2 ==> pc1.None? && !arr.is_phase1(pc2.v) && !arr.is_phase2(pc2.v);
          var next_pos := pos+1;
          pos := pos+1;
        }
        lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
      }
    }
  }

  lemma lemma_IfAtomicReductionRequestValidThenCrashingPhaseUnaffectedByOtherActors<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.PhaseUnaffectedByOtherActors(GetRefinementViaReductionRequest(arr))
  {
    lemma_IfAtomicReductionRequestValidThenCrashingPhaseUnaffectedByOtherActorsHelper(arr);
    var rr := GetRefinementViaReductionRequest(arr);

    forall s, s', multistep, actor | ActionTuple(s, s', multistep) in rr.lspec.next && rr.idmap(multistep) != actor
      ensures rr.phase1(s, actor) <==> rr.phase1(s', actor)
    {
      assert && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
             && (rr.phase2(s, actor) <==> rr.phase2(s', actor));
    }

    forall s, s', multistep, actor | ActionTuple(s, s', multistep) in rr.lspec.next && rr.idmap(multistep) != actor
      ensures rr.phase2(s, actor) <==> rr.phase2(s', actor)
    {
      assert && (rr.phase1(s, actor) <==> rr.phase1(s', actor))
             && (rr.phase2(s, actor) <==> rr.phase2(s', actor));
    }
  }

  lemma lemma_PostCrashStepsStutter<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  PostCrashStepsStutter(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', multistep | rr.crashed(s) && ActionTuple(s, s', multistep) in GetRefinementViaReductionLSpec(arr).next
      ensures s' == s
    {
      assert AtomicNextMultiplePaths(arr.l, s, s', multistep.steps, multistep.tid);
      if |multistep.steps| > 0 {
        assert arr.l.path_valid(s, multistep.steps[0], multistep.tid);
        assert !arr.l.state_ok(s);
        assert !arr.l.path_valid(s, multistep.steps[0], multistep.tid);
        assert false;
      }
      else {
        assert s' == s;
      }
    }
  }

  lemma lemma_RightMoversPreserveStateRefinement<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoversPreserveStateRefinement(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', multistep |
      && ActionTuple(s, s', multistep) in rr.lspec.next
      && rr.phase1(s', rr.idmap(multistep))
      && arr.l.state_ok(s')
      ensures RefinementPair(s', s) in rr.relation
    {
      assert !multistep.tau;
      assert AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau);
      var tid := multistep.tid;
      var states := AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid);
      lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
      var pos := |multistep.steps|;
      while pos > 0
        invariant 0 <= pos <= |multistep.steps|
        invariant pos > 0 ==> IsPhase1(arr, states[pos], tid)
        invariant arr.l.state_ok(states[pos])
        invariant RefinementPair(s', states[pos]) in rr.relation
        decreases pos
      {
        var prev_pos := pos-1;
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, prev_pos);
        assert arr.l.path_valid(states[prev_pos], multistep.steps[prev_pos], multistep.tid);
        assert states[prev_pos+1] == arr.l.path_next(states[prev_pos], multistep.steps[prev_pos], multistep.tid);
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

  lemma lemma_LeftMoversPreserveStateRefinement<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoversPreserveStateRefinement(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall s, s', multistep |
      && ActionTuple(s, s', multistep) in rr.lspec.next
      && rr.phase2(s, rr.idmap(multistep))
      ensures RefinementPair(s, s') in rr.relation
    {
      assert !multistep.tau;
      assert AtomicNextMultistep(arr.l, s, s', multistep.steps, multistep.tid, multistep.tau);
      var tid := multistep.tid;
      var states := AtomicGetStateSequence(arr.l, s, multistep.steps, multistep.tid);
      var pos := 0;
      while pos < |multistep.steps|
        invariant 0 <= pos <= |multistep.steps|
        invariant pos < |multistep.steps| ==> IsPhase2(arr, states[pos], tid)
        invariant RefinementPair(s, states[pos]) in rr.relation
        decreases |multistep.steps| - pos
      {
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, s, s', multistep.steps, multistep.tid, states, pos);
        assert arr.l.path_valid(states[pos], multistep.steps[pos], multistep.tid);
        assert states[pos+1] == arr.l.path_next(states[pos], multistep.steps[pos], multistep.tid);
        assert RefinementPair(states[pos], states[pos+1]) in arr.self_relation;
        pos := pos+1;
      }
      lemma_AtomicNextLastElement(arr.l, s, s', multistep.steps, multistep.tid, states);
    }
  }

  lemma lemma_MoveLeftMoverLeftOneAsSinglePath<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    initial_state:LState,
    state_after_other_path:LState,
    state_after_both_paths:LState,
    mover_path:LPath,
    other_path:LPath
    ) returns (
    state_after_mover_path:LState
    )
    requires ValidAtomicReductionRequest(arr)

    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, other_path, other_tid)
    requires state_after_other_path == arr.l.path_next(initial_state, other_path, other_tid)
    requires arr.l.path_type(other_path).AtomicPathType_Tau? == other_tau

    requires arr.l.path_valid(state_after_other_path, mover_path, mover_tid)
    requires state_after_both_paths == arr.l.path_next(state_after_other_path, mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(state_after_both_paths)

    requires IsPhase2(arr, state_after_other_path, mover_tid)

    ensures  arr.l.path_valid(initial_state, mover_path, mover_tid)
    ensures  state_after_mover_path == arr.l.path_next(initial_state, mover_path, mover_tid)
    ensures  arr.l.path_valid(state_after_mover_path, other_path, other_tid)
    ensures  state_after_both_paths == arr.l.path_next(state_after_mover_path, other_path, other_tid)
    ensures  OKAndPCTypesMatch(arr, state_after_mover_path, state_after_both_paths, mover_tid)
    ensures  !other_tau ==> OKAndPCTypesMatch(arr, state_after_other_path, state_after_both_paths, other_tid)
  {
    state_after_mover_path := arr.l.path_next(initial_state, mover_path, mover_tid);
    assert AtomicReductionSpecModule.LeftMoversCommuteConditions(arr, initial_state, other_path, mover_path, mover_tid, other_tid);

    if !other_tau {
      lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, state_after_other_path, state_after_both_paths, mover_path, mover_tid, other_tid);
    }
    lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, state_after_mover_path, state_after_both_paths, other_path, other_tid, mover_tid);
  }

  lemma {:timeLimitMultiplier 2} lemma_MoveLeftMoverLeftAsSinglePaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    post_mover_state:LState,
    mover_path:LPath,
    other_states:seq<LState>,
    other_paths:seq<LPath>
    ) returns (
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    requires arr.l.path_valid(last(other_states), mover_path, mover_tid)
    requires post_mover_state == arr.l.path_next(last(other_states), mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(post_mover_state)

    requires IsPhase2(arr, last(other_states), mover_tid)

    ensures  |other_states'| == |other_states|
    ensures  last(other_states') == post_mover_state
    ensures  arr.l.path_valid(other_states[0], mover_path, mover_tid)
    ensures  other_states'[0] == arr.l.path_next(other_states[0], mover_path, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  OKAndPCTypesMatch(arr, other_states[0], last(other_states), mover_tid)
    ensures  OKAndPCTypesMatch(arr, other_states'[0], post_mover_state, mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    decreases |other_states|
  {
    if |other_paths| == 0 {
      other_states' := [post_mover_state];
      return;
    }

    var pos := |other_states|-2;
    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, other_states[0], last(other_states), other_paths, other_tid,
                                                  other_states, pos);
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, other_states[0], last(other_states), other_paths, other_tid,
                                                           other_states, pos);
    var state_after_mover_path :=
      lemma_MoveLeftMoverLeftOneAsSinglePath(
        arr,  mover_tid, other_tid, other_tau, other_states[pos], other_states[pos+1], post_mover_state, mover_path, other_paths[pos]);

    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, other_states[0], last(other_states), other_paths, other_states, other_tid);
    assert last(all_but_last(other_states)) == other_states[pos];
    var other_states_next :=
      lemma_MoveLeftMoverLeftAsSinglePaths(
        arr, mover_tid, other_tid, other_tau, state_after_mover_path, mover_path,
        all_but_last(other_states), all_but_last(other_paths));
    other_states' := other_states_next + [post_mover_state];

    lemma_ExtendingStateSequenceWorks(arr.l, other_states_next[0], last(other_states_next), all_but_last(other_paths), other_states_next,
                                      other_tid, last(other_paths), post_mover_state);
    lemma_AllButLastPlusLastIsSeq(other_paths);

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
          lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, last(other_states), post_mover_state, mover_path, mover_tid, other_tid);
          assert OKAndPCTypesMatch(arr, post_mover_state, last(other_states), other_tid);
        }
      }
    }
  }

  lemma lemma_MoveLeftMoversLeftAsSinglePaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_states:seq<LState>,
    mover_paths:seq<LPath>,
    other_states:seq<LState>,
    other_paths:seq<LPath>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    requires |mover_states| > 1
    requires last(other_states) == mover_states[0]
    requires AtomicNextMultiplePaths(arr.l, mover_states[0], last(mover_states), mover_paths, mover_tid)
    requires mover_states == AtomicGetStateSequence(arr.l, mover_states[0], mover_paths, mover_tid)
    requires forall path :: path in mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(last(mover_states))

    ensures  |mover_states'| == |mover_states|
    ensures  |other_states'| == |other_states|
    ensures  mover_states'[0] == other_states[0]
    ensures  last(mover_states') == other_states'[0]
    ensures  last(other_states') == last(mover_states)
    ensures  AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'), mover_paths, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0], mover_paths, mover_tid)
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
    decreases |mover_states|
  {
    assert |mover_paths| > 0;
    var pos := 0;
    assert mover_states[pos+1] == arr.l.path_next(mover_states[pos], mover_paths[pos], mover_tid);
    forall ensures arr.l.state_ok(mover_states[pos+1]) {
      if |mover_paths| == 1 {
        assert mover_states[pos+1] == last(mover_states);
      }
      else {
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, mover_states[0], last(mover_states), mover_paths, mover_tid,
                                                               mover_states, pos+1);
      }
    }
    var other_states_mid :=
      lemma_MoveLeftMoverLeftAsSinglePaths(
        arr, mover_tid, other_tid, other_tau, mover_states[pos+1], mover_paths[pos], other_states, other_paths);
    if |mover_paths| == 1 {
      mover_states' := [other_states[0], other_states_mid[0]];
      other_states' := other_states_mid;
    }
    else {
      var mover_states_next;
      lemma_LastOfDropIsLast(mover_states, 1);
      mover_states_next, other_states' :=
        lemma_MoveLeftMoversLeftAsSinglePaths(
          arr, mover_tid, other_tid, other_tau, mover_states[1..], mover_paths[1..], other_states_mid, other_paths);
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

  lemma lemma_PerformLeftMoveAll<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle,
    other_tau:bool,
    mover_paths:seq<LPath>,
    mover_states:seq<LState>,
    other_paths:seq<LPath>,
    other_states:seq<LState>
    ) returns (
    mover_states':seq<LState>,
    other_states':seq<LState>
    )

    requires ValidAtomicReductionRequest(arr)

    requires |other_states| > 0
    requires arr.inv(other_states[0])
    requires AtomicNextMultiplePaths(arr.l, other_states[0], last(other_states), other_paths, other_tid)
    requires other_states == AtomicGetStateSequence(arr.l, other_states[0], other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau

    requires |mover_states| > 0
    requires last(other_states) == mover_states[0]
    requires AtomicNextMultiplePaths(arr.l, mover_states[0], last(mover_states), mover_paths, mover_tid)
    requires mover_states == AtomicGetStateSequence(arr.l, mover_states[0], mover_paths, mover_tid)
    requires forall path :: path in mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)

    requires other_tau || other_tid != mover_tid
    requires arr.l.state_ok(last(mover_states))

    ensures  |mover_states'| == |mover_states|
    ensures  |other_states'| == |other_states|
    ensures  mover_states'[0] == other_states[0]
    ensures  last(mover_states') == other_states'[0]
    ensures  last(other_states') == last(mover_states)
    ensures  AtomicNextMultiplePaths(arr.l, mover_states'[0], last(mover_states'), mover_paths, mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), other_paths, other_tid)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, mover_states'[0], mover_paths, mover_tid)
    ensures  other_states' == AtomicGetStateSequence(arr.l, other_states'[0], other_paths, other_tid)
    ensures  forall i :: 0 <= i < |mover_states| ==> OKAndPCTypesMatch(arr, mover_states'[i], mover_states[i], mover_tid)
    ensures  !other_tau ==> forall i :: 0 <= i < |other_states| ==> OKAndPCTypesMatch(arr, other_states'[i], other_states[i], other_tid)
  {
    if |mover_states| == 1 {
     lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, other_states[0], last(other_states), other_paths, other_tau,
                                                             other_tid, mover_tid);
      mover_states' := [other_states[0]];
      other_states' := other_states;
    }
    else
    {
      mover_states', other_states' := lemma_MoveLeftMoversLeftAsSinglePaths
      (arr, mover_tid, other_tid, other_tau, mover_states, mover_paths, other_states, other_paths);
    } 
  }

  lemma lemma_PerformLeftMove<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s1:LState,
    s2:LState,
    s3:LState,
    multistep1:Armada_Multistep<LPath>,
    multistep2:Armada_Multistep<LPath>
    ) returns (
    s2':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires s1 in AnnotatedReachables(GetRefinementViaReductionLSpec(arr))
    requires arr.l.state_ok(s3)
    requires AtomicNextMultistep(arr.l, s1, s2, multistep1.steps, multistep1.tid, multistep1.tau)
    requires AtomicNextMultistep(arr.l, s2, s3, multistep2.steps, multistep2.tid, multistep2.tau)
    requires !multistep2.tau
    requires multistep1.tau || multistep1.tid != multistep2.tid
    requires IsPhase2(arr, s2, multistep2.tid)
    ensures  AtomicNextMultistep(arr.l, s1, s2', multistep2.steps, multistep2.tid, multistep2.tau)
    ensures  AtomicNextMultistep(arr.l, s2', s3, multistep1.steps, multistep1.tid, multistep1.tau)
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, s1);
    assert arr.inv(s1);
    var mover_states := AtomicGetStateSequence(arr.l, s2, multistep2.steps, multistep2.tid);
    lemma_IfMultistepStartsInPhase2ThenEachPathDoes(arr, s2, s3, multistep2, mover_states);
    var other_states := AtomicGetStateSequence(arr.l, s1, multistep1.steps, multistep1.tid);
    lemma_AtomicNextLastElement(arr.l, s1, s2, multistep1.steps, multistep1.tid, other_states);
    lemma_AtomicNextLastElement(arr.l, s2, s3, multistep2.steps, multistep2.tid, mover_states);
    var mover_states', other_states' :=
      lemma_PerformLeftMoveAll(arr, multistep2.tid, multistep1.tid, multistep1.tau, multistep2.steps, mover_states,
                               multistep1.steps, other_states);
    s2' := last(mover_states');
    lemma_AtomicNextLastElement(arr.l, s2', s3, multistep1.steps, multistep1.tid, other_states');
  }

  lemma lemma_RightMoversCommute<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoversCommute(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    var idmap := rr.idmap;
    var phase1 := rr.phase1;
    var phase2 := rr.phase2;

    forall initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_multistep
      {:trigger RefinementViaReductionSpecModule.RightMoversCommuteConditions(rr, initial_state, state_after_right_mover,
                                                                              state_after_both_paths, right_mover, other_multistep)}
      | RefinementViaReductionSpecModule.RightMoversCommuteConditions(rr, initial_state, state_after_right_mover, state_after_both_paths,
                                                                      right_mover, other_multistep)
      ensures exists new_middle_state, other_multistep', right_mover' ::
                && ActionTuple(initial_state, new_middle_state, other_multistep') in rr.lspec.next
                && ActionTuple(new_middle_state, state_after_both_paths, right_mover') in rr.lspec.next
                && rr.idmap(other_multistep') == rr.idmap(other_multistep)
                && rr.idmap(right_mover') == rr.idmap(right_mover)
    {
      var new_middle_state:LState;
      new_middle_state := lemma_PerformRightMove(arr, initial_state, state_after_right_mover, state_after_both_paths,
                                                 right_mover, other_multistep);
      assert ActionTuple(initial_state, new_middle_state, other_multistep) in rr.lspec.next;
      assert ActionTuple(new_middle_state, state_after_both_paths, right_mover) in rr.lspec.next;
    }
  }

  lemma lemma_LeftMoversCommute<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoversCommute(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    var idmap := rr.idmap;
    var phase1 := rr.phase1;
    var phase2 := rr.phase2;

    forall initial_state, state_after_other_multistep, state_after_both_paths, other_multistep, left_mover
      {:trigger RefinementViaReductionSpecModule.LeftMoversCommuteConditions(rr, initial_state, state_after_other_multistep,
                                                                             state_after_both_paths, other_multistep, left_mover)}
      | RefinementViaReductionSpecModule.LeftMoversCommuteConditions(rr, initial_state, state_after_other_multistep, state_after_both_paths,
                                                                     other_multistep, left_mover)
      ensures exists new_middle_state, left_mover', other_multistep' ::
                && ActionTuple(initial_state, new_middle_state, left_mover') in rr.lspec.next
                && ActionTuple(new_middle_state, state_after_both_paths, other_multistep') in rr.lspec.next
                && rr.idmap(left_mover') == rr.idmap(left_mover)
                && rr.idmap(other_multistep') == rr.idmap(other_multistep)
    {
      var new_middle_state:LState;
      new_middle_state := lemma_PerformLeftMove(arr, initial_state, state_after_other_multistep, state_after_both_paths,
                                                other_multistep, left_mover);
      assert ActionTuple(initial_state, new_middle_state, left_mover) in rr.lspec.next;
      assert ActionTuple(new_middle_state, state_after_both_paths, other_multistep) in rr.lspec.next;
    }
  }

  //////////////////////////////////////
  // RIGHT MOVER CRASH PRESERVATION
  //////////////////////////////////////

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverPathOtherPathSequence<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    right_mover:LPath,
    right_mover_tid:Armada_ThreadHandle,
    other_multistep_paths:seq<LPath>,
    other_multistep_tid:Armada_ThreadHandle,
    other_multistep_tau:bool,
    other_multistep_states:seq<LState>
    ) returns (
    state_after_other_multistep':LState,
    other_multistep_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, right_mover, right_mover_tid)
    requires state_after_right_mover == arr.l.path_next(initial_state, right_mover, right_mover_tid)
    requires !arr.l.path_type(right_mover).AtomicPathType_Tau?
    requires AtomicNextMultiplePaths(arr.l, state_after_right_mover, state_after_both_paths, other_multistep_paths, other_multistep_tid)
    requires forall path :: path in other_multistep_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_multistep_tau
    requires other_multistep_states == AtomicGetStateSequence(arr.l, state_after_right_mover, other_multistep_paths, other_multistep_tid)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires other_multistep_tau || other_multistep_tid != right_mover_tid
    ensures  AtomicNextMultiplePaths(arr.l, initial_state, state_after_other_multistep', other_multistep_paths, other_multistep_tid)
    ensures  other_multistep_states' == AtomicGetStateSequence(arr.l, initial_state, other_multistep_paths, other_multistep_tid)
    ensures  |other_multistep_states'| == |other_multistep_states|
    ensures  !other_multistep_tau ==>
             forall i :: 0 <= i < |other_multistep_states|-1 ==>
                   OKAndPCTypesMatch(arr, other_multistep_states'[i], other_multistep_states[i], other_multistep_tid)
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
  {
    assert |other_multistep_paths| > 0;
    assert arr.l.path_valid(state_after_right_mover, other_multistep_paths[0], other_multistep_tid);
    assert other_multistep_states[1] == arr.l.path_next(state_after_right_mover, other_multistep_paths[0], other_multistep_tid);

    if !other_multistep_tau {
      lemma_ExecutingPathDoesntChangeOtherActorPCType(arr, initial_state, state_after_right_mover, right_mover,
                                                      right_mover_tid, other_multistep_tid);
    }

    if |other_multistep_paths| == 1 {
      other_multistep_states' := AtomicGetStateSequence(arr.l, initial_state, other_multistep_paths, other_multistep_tid);
      state_after_other_multistep' := arr.l.path_next(initial_state, other_multistep_paths[0], other_multistep_tid);
      lemma_AtomicNextLastElement(arr.l, state_after_right_mover, state_after_both_paths,
                                  other_multistep_paths, other_multistep_tid, other_multistep_states);
      assert AtomicReductionSpecModule.RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_multistep_paths[0],
                                                                             right_mover_tid, other_multistep_tid);
      return;
    }

    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, state_after_right_mover, state_after_both_paths,
                                                           other_multistep_paths, other_multistep_tid, other_multistep_states, 1);
    assert AtomicReductionSpecModule.RightMoversCommuteConditions(arr, initial_state, right_mover, other_multistep_paths[0],
                                                                  right_mover_tid, other_multistep_tid);
    assert arr.l.path_valid(initial_state, other_multistep_paths[0], other_multistep_tid);
    var s2' := arr.l.path_next(initial_state, other_multistep_paths[0], other_multistep_tid);
    assert arr.l.path_valid(s2', right_mover, right_mover_tid);
    assert other_multistep_states[1] == arr.l.path_next(s2', right_mover, right_mover_tid);

    var other_multistep_states_mid;
    state_after_other_multistep', other_multistep_states_mid :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverPathOtherPathSequence(
        arr, rr, s2', other_multistep_states[1], state_after_both_paths, right_mover,
        right_mover_tid, other_multistep_paths[1..], other_multistep_tid, other_multistep_tau,
        other_multistep_states[1..]);

    other_multistep_states' := [initial_state] + other_multistep_states_mid;
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherArmada_Multistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    other_multistep:Armada_Multistep<LPath>,
    right_mover:LPath,
    right_mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_other_multistep':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, right_mover, right_mover_tid)
    requires state_after_right_mover == arr.l.path_next(initial_state, right_mover, right_mover_tid)
    requires !arr.l.path_type(right_mover).AtomicPathType_Tau?
    requires AtomicNextMultistep(arr.l, state_after_right_mover, state_after_both_paths, other_multistep.steps,
                                 other_multistep.tid, other_multistep.tau)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires other_multistep.tau || other_multistep.tid != right_mover_tid
    ensures  AtomicNextMultistep(arr.l, initial_state, state_after_other_multistep', other_multistep.steps, other_multistep.tid,
                                 other_multistep.tau)
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
  {
    var other_multistep_states := AtomicGetStateSequence(arr.l, state_after_right_mover, other_multistep.steps, other_multistep.tid);
    var other_multistep_states';
    state_after_other_multistep', other_multistep_states' :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverPathOtherPathSequence(
        arr, rr, initial_state, state_after_right_mover, state_after_both_paths,
        right_mover, right_mover_tid, other_multistep.steps, other_multistep.tid, other_multistep.tau,
        other_multistep_states);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherMultistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    other_multistep:Armada_Multistep<LPath>,
    right_mover:LPath,
    right_mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_other_multistep':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, right_mover, right_mover_tid)
    requires state_after_right_mover == arr.l.path_next(initial_state, right_mover, right_mover_tid)
    requires !arr.l.path_type(right_mover).AtomicPathType_Tau?
    requires ActionTuple(state_after_right_mover, state_after_both_paths, other_multistep) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires rr.idmap(other_multistep) != Some(right_mover_tid)
    ensures  ActionTuple(initial_state, state_after_other_multistep', other_multistep) in rr.lspec.next
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
  {
    state_after_other_multistep' :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherArmada_Multistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_paths,
        other_multistep, right_mover, right_mover_tid);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationRightMoverPathSequenceOtherMultistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    other_multistep:Armada_Multistep<LPath>,
    right_mover_paths:seq<LPath>,
    right_mover_tid:Armada_ThreadHandle,
    right_mover_states:seq<LState>
    ) returns (
    state_after_other_multistep':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultiplePaths(arr.l, initial_state, state_after_right_mover, right_mover_paths, right_mover_tid)
    requires forall path :: path in right_mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
    requires ActionTuple(state_after_right_mover, state_after_both_paths, other_multistep) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase1(arr, state_after_right_mover, right_mover_tid)
    requires right_mover_states == AtomicGetStateSequence(arr.l, initial_state, right_mover_paths, right_mover_tid)
    requires forall i :: 0 < i < |right_mover_states| ==> IsPhase1(arr, right_mover_states[i], right_mover_tid)
    requires rr.idmap(other_multistep) != Some(right_mover_tid)
    ensures  ActionTuple(initial_state, state_after_other_multistep', other_multistep) in rr.lspec.next
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
    decreases |right_mover_paths|
  {
    if |right_mover_paths| == 0 {
      state_after_other_multistep' := state_after_both_paths;
      return;
    }

    var pos := |right_mover_states|-2;
    var penultimate_state := right_mover_states[pos];
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, initial_state, state_after_right_mover, right_mover_paths,
                                                           right_mover_tid, right_mover_states, pos);
    lemma_AtomicNextLastElement(arr.l, initial_state, state_after_right_mover, right_mover_paths, right_mover_tid, right_mover_states);
    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, state_after_right_mover, right_mover_paths,
                                                  right_mover_tid, right_mover_states, pos);
    var state_after_other_multistep_mid :=
      lemma_DemonstrateRightMoverCrashPreservationOneRightMoverOtherMultistep(
        arr, rr, penultimate_state, state_after_right_mover, state_after_both_paths,
        other_multistep, last(right_mover_paths), right_mover_tid);

    if |right_mover_paths| == 1 {
      state_after_other_multistep' := state_after_other_multistep_mid;
      return;
    }

    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, initial_state, state_after_right_mover, right_mover_paths,
                                                     right_mover_states, right_mover_tid);
    assert 0 < pos < |right_mover_states|;
    assert IsPhase1(arr, penultimate_state, right_mover_tid);
    state_after_other_multistep' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverPathSequenceOtherMultistep(
        arr, rr, initial_state, penultimate_state, state_after_other_multistep_mid,
        other_multistep, all_but_last(right_mover_paths), right_mover_tid,
        all_but_last(right_mover_states));
  }

  lemma lemma_DemonstrateRightMoverCrashPreservationRightMoverArmada_MultistepOtherMultistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    right_mover:Armada_Multistep<LPath>,
    other_multistep:Armada_Multistep<LPath>
    ) returns (
    state_after_other_multistep':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultistep(arr.l, initial_state, state_after_right_mover, right_mover.steps, right_mover.tid, right_mover.tau)
    requires ActionTuple(state_after_right_mover, state_after_both_paths, other_multistep) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase1(arr, state_after_right_mover, right_mover.tid)
    requires !right_mover.tau
    requires rr.idmap(other_multistep) != Some(right_mover.tid)
    ensures  ActionTuple(initial_state, state_after_other_multistep', other_multistep) in rr.lspec.next
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
  {
    var right_mover_states := AtomicGetStateSequence(arr.l, initial_state, right_mover.steps, right_mover.tid);
    lemma_IfMultistepEndsInPhase1ThenEachPathDoes(arr, initial_state, state_after_right_mover, right_mover, right_mover_states);
    state_after_other_multistep' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverPathSequenceOtherMultistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_paths,
        other_multistep, right_mover.steps, right_mover.tid, right_mover_states);
  }

  lemma lemma_DemonstrateRightMoverCrashPreservation<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_right_mover:LState,
    state_after_both_paths:LState,
    right_mover:Armada_Multistep<LPath>,
    other_multistep:Armada_Multistep<LPath>
    ) returns (
    other_multistep':Armada_Multistep<LPath>,
    state_after_other_multistep':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
    requires ActionTuple(state_after_right_mover, state_after_both_paths, other_multistep) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_right_mover)
    requires rr.crashed(state_after_both_paths)
    requires rr.phase1(state_after_right_mover, rr.idmap(right_mover))
    requires rr.idmap(right_mover) != rr.idmap(other_multistep)
    ensures  rr.idmap(other_multistep') == rr.idmap(other_multistep)
    ensures  ActionTuple(initial_state, state_after_other_multistep', other_multistep') in rr.lspec.next
    ensures  rr.crashed(state_after_other_multistep')
    ensures  RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    other_multistep' := other_multistep;
    state_after_other_multistep' :=
      lemma_DemonstrateRightMoverCrashPreservationRightMoverArmada_MultistepOtherMultistep(
        arr, rr, initial_state, state_after_right_mover, state_after_both_paths,
        right_mover, other_multistep);
  }

  lemma lemma_RightMoverCrashPreservation<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.RightMoverCrashPreservation(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);

    forall initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_multistep
      {:trigger RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover,
                                                                                       state_after_both_paths, right_mover,
                                                                                       other_multistep)}
      | RefinementViaReductionSpecModule.RightMoverCrashPreservationConditions(rr, initial_state, state_after_right_mover,
                                                                               state_after_both_paths, right_mover, other_multistep)
      && initial_state in AnnotatedReachables(rr.lspec)
      && ActionTuple(initial_state, state_after_right_mover, right_mover) in rr.lspec.next
      && ActionTuple(state_after_right_mover, state_after_both_paths, other_multistep) in rr.lspec.next
      && !rr.crashed(initial_state)
      && !rr.crashed(state_after_right_mover)
      && rr.crashed(state_after_both_paths)
      && rr.phase1(state_after_right_mover, rr.idmap(right_mover))
      && rr.idmap(right_mover) != rr.idmap(other_multistep)
      ensures exists other_multistep', state_after_other_multistep' ::
                && rr.idmap(other_multistep') == rr.idmap(other_multistep)
                && ActionTuple(initial_state, state_after_other_multistep', other_multistep') in rr.lspec.next
                && rr.crashed(state_after_other_multistep')
                && RefinementPair(state_after_both_paths, state_after_other_multistep') in rr.relation
    {
      var other_multistep', state_after_other_multistep' :=
        lemma_DemonstrateRightMoverCrashPreservation(arr, rr, initial_state, state_after_right_mover, state_after_both_paths,
                                                     right_mover, other_multistep);
    }
  }

  //////////////////////////////////////
  // LEFT MOVERS ENABLED BEFORE CRASH
  //////////////////////////////////////

  lemma lemma_CombineLeftMoverSubpathsIntoPathsOneIteration<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    tid:Armada_ThreadHandle,
    states:seq<LState>,
    paths:seq<LPath>,
    pos:int,
    multistates:seq<LState>,
    multipaths:seq<Armada_Multistep<LPath>>,
    partial_paths:seq<LPath>,
    partial_multistates:seq<LState>
    ) returns (
    pos':int,
    multistates':seq<LState>,
    multipaths':seq<Armada_Multistep<LPath>>,
    partial_paths':seq<LPath>,
    partial_multistates':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires |states| > 0
    requires AtomicNextMultiplePaths(arr.l, states[0], last(states), paths, tid)
    requires states == AtomicGetStateSequence(arr.l, states[0], paths, tid)
    requires arr.inv(states[0])
    requires IsPhase2(arr, states[0], tid)
    requires AtomicThreadYielding(arr.l, states[0], tid)
    requires forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    requires !IsPhase2(arr, last(states), tid)
    requires AtomicThreadYielding(arr.l, last(states), tid)
    requires forall path :: path in paths ==> !arr.l.path_type(path).AtomicPathType_Tau?

    requires 0 <= pos < |paths|
    requires |multistates| > 0
    requires multistates[0] == states[0]
    requires StateNextSeq(multistates, multipaths, rr.lspec.next)
    requires forall multipath :: multipath in multipaths ==> !multipath.tau && multipath.tid == tid
    requires AtomicThreadYielding(arr.l, last(multistates), tid)
    requires AtomicThreadYielding(arr.l, states[pos], tid) ==> |partial_paths| == 0
    requires AtomicNextMultiplePaths(arr.l, last(multistates), states[pos], partial_paths, tid)
    requires partial_multistates == AtomicGetStateSequence(arr.l, last(multistates), partial_paths, tid)
    requires forall i :: 0 < i < |partial_multistates| ==> !AtomicThreadYielding(arr.l, partial_multistates[i], tid)
    requires forall path :: path in partial_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
    requires if pos < |paths| then (
                 forall s :: s in multistates ==> IsPhase2(arr, s, tid)
             ) else (
                 forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
             )

    ensures  pos' == pos + 1
    ensures  |multistates'| > 0
    ensures  multistates'[0] == states[0]
    ensures  StateNextSeq(multistates', multipaths', rr.lspec.next)
    ensures  forall multipath :: multipath in multipaths' ==> !multipath.tau && multipath.tid == tid
    ensures  AtomicThreadYielding(arr.l, last(multistates'), tid)
    ensures  AtomicThreadYielding(arr.l, states[pos'], tid) ==> |partial_paths'| == 0
    ensures  AtomicNextMultiplePaths(arr.l, last(multistates'), states[pos'], partial_paths', tid)
    ensures  partial_multistates' == AtomicGetStateSequence(arr.l, last(multistates'), partial_paths', tid)
    ensures  forall i :: 0 < i < |partial_multistates'| ==> !AtomicThreadYielding(arr.l, partial_multistates'[i], tid)
    ensures  forall path :: path in partial_paths' ==> !arr.l.path_type(path).AtomicPathType_Tau?
    ensures  if pos' < |paths| then (
                 forall s :: s in multistates' ==> IsPhase2(arr, s, tid)
             ) else (
                 forall i :: 0 <= i < |multistates'|-1 ==> IsPhase2(arr, multistates'[i], tid)
             )
  {
    var s_current := states[pos];
    var s_next := states[pos+1];
    var next_path := paths[pos];

    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, states[0], last(states), paths, tid, states, pos);
    assert arr.l.path_valid(s_current, next_path, tid);
    assert s_next == arr.l.path_next(s_current, next_path, tid);
    var pc' := arr.l.get_thread_pc(s_next, tid);

    lemma_ExtendingStateSequenceWorks(arr.l, last(multistates), s_current, partial_paths, partial_multistates, tid, next_path, s_next);

    var upper := |partial_multistates|;
    assert forall i :: 0 < i < upper ==> !AtomicThreadYielding(arr.l, partial_multistates[i], tid);

    partial_paths' := partial_paths + [next_path];
    partial_multistates' := partial_multistates + [s_next];

    assert upper == |partial_paths'|;
    assert forall i :: 0 < i < |partial_paths'| ==> !AtomicThreadYielding(arr.l, partial_multistates'[i], tid);

    if AtomicThreadYielding(arr.l, s_next, tid) {
      var multipath := Armada_Multistep(partial_paths', tid, false);

      assert AtomicNextMultistep(arr.l, last(multistates), s_next, multipath.steps, multipath.tid, multipath.tau);
      assert ActionTuple(last(multistates), s_next, multipath) in rr.lspec.next;

      multistates' := multistates + [s_next];
      multipaths' := multipaths + [multipath];

      forall i | 0 <= i < |multipaths'|
        ensures ActionTuple(multistates'[i], multistates'[i+1], multipaths'[i]) in rr.lspec.next
      {
        if i < |multipaths| {
          assert ActionTuple(multistates[i], multistates[i+1], multipaths[i]) in rr.lspec.next;
          assert multistates'[i] == multistates[i];
          assert multistates'[i+1] == multistates[i+1];
          assert multipaths'[i] == multipaths[i];
        }
        else {
          assert i == |multipaths| == |multistates|-1;
          assert multistates'[i] == multistates[i] == last(multistates);
          assert multistates'[i+1] == s_next;
          assert multipaths'[i] == multipath;
        }
      }

      assert StateNextSeq(multistates', multipaths', rr.lspec.next);

      partial_paths' := [];
      partial_multistates' := [s_next];
    }
    else {
      multistates' := multistates;
      multipaths' := multipaths;
    }

    pos' := pos + 1;
    assert AtomicNextMultiplePaths(arr.l, last(multistates'), states[pos'], partial_paths', tid);
  }

  lemma lemma_CombineLeftMoverSubpathsIntoPaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    tid:Armada_ThreadHandle,
    states:seq<LState>,
    paths:seq<LPath>
    ) returns (
    multistates:seq<LState>,
    multipaths:seq<Armada_Multistep<LPath>>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires |states| > 0
    requires AtomicNextMultiplePaths(arr.l, states[0], last(states), paths, tid)
    requires states == AtomicGetStateSequence(arr.l, states[0], paths, tid)
    requires arr.inv(states[0])
    requires AtomicThreadYielding(arr.l, states[0], tid)
    requires IsPhase2(arr, states[0], tid)
    requires forall i :: 0 <= i < |states|-1 ==> IsPhase2(arr, states[i], tid)
    requires !IsPhase2(arr, last(states), tid)
    requires AtomicThreadYielding(arr.l, last(states), tid)
    requires forall path :: path in paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
    ensures  StateNextSeq(multistates, multipaths, rr.lspec.next)
    ensures  |multistates| > 0
    ensures  multistates[0] == states[0]
    ensures  last(multistates) == last(states)
    ensures  forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
    ensures  forall multipath :: multipath in multipaths ==> !multipath.tau && multipath.tid == tid
  {
    multistates := [states[0]];
    multipaths := [];
    var partial_paths := [];
    var partial_multistates := [states[0]];

    var pos := 0;

    assert AtomicThreadYielding(arr.l, states[pos], tid) ==> |partial_paths| == 0;
    while pos < |paths|
      invariant 0 <= pos <= |paths|
      invariant |multistates| > 0
      invariant multistates[0] == states[0]
      invariant StateNextSeq(multistates, multipaths, rr.lspec.next)
      invariant forall multipath :: multipath in multipaths ==> !multipath.tau && multipath.tid == tid
      invariant AtomicThreadYielding(arr.l, last(multistates), tid)
      invariant AtomicThreadYielding(arr.l, states[pos], tid) ==> |partial_paths| == 0
      invariant AtomicNextMultiplePaths(arr.l, last(multistates), states[pos], partial_paths, tid)
      invariant partial_multistates == AtomicGetStateSequence(arr.l, last(multistates), partial_paths, tid)
      invariant forall i :: 0 < i < |partial_multistates| ==> !AtomicThreadYielding(arr.l, partial_multistates[i], tid)
      invariant forall path :: path in partial_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
      invariant if pos < |paths| then (
                    forall s :: s in multistates ==> IsPhase2(arr, s, tid)
                ) else (
                    forall i :: 0 <= i < |multistates|-1 ==> IsPhase2(arr, multistates[i], tid)
                )
      decreases |paths| - pos
    {
      pos, multistates, multipaths, partial_paths, partial_multistates :=
        lemma_CombineLeftMoverSubpathsIntoPathsOneIteration(
          arr, rr, tid, states, paths, pos, multistates, multipaths, partial_paths, partial_multistates);
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPathSequencePart2<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_path_paths:seq<LPath>,
    crash_path_tid:Armada_ThreadHandle,
    crash_path_tau:bool,
    crash_path_states:seq<LState>,
    left_mover_tid:Armada_ThreadHandle,
    left_mover_states_mid:seq<LState>,
    left_mover_paths_mid:seq<LPath>,
    post_crash_state':LState
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_paths:seq<Armada_Multistep<LPath>>,
    crash_path_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultiplePaths(arr.l, initial_state, post_crash_state, crash_path_paths, crash_path_tid)
    requires forall path :: path in crash_path_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == crash_path_tau
    requires crash_path_states == AtomicGetStateSequence(arr.l, initial_state, crash_path_paths, crash_path_tid)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_path_tau || crash_path_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires AtomicThreadYielding(arr.l, initial_state, left_mover_tid)
    requires |left_mover_states_mid| > 1
    requires AtomicNextMultiplePaths(arr.l, crash_path_states[|crash_path_states|-2], last(left_mover_states_mid), left_mover_paths_mid,
                                     left_mover_tid)
    requires left_mover_states_mid == AtomicGetStateSequence(arr.l, crash_path_states[|crash_path_states|-2], left_mover_paths_mid,
                                                             left_mover_tid)
    requires arr.l.state_ok(last(left_mover_states_mid))
    requires !IsPhase2(arr, last(left_mover_states_mid), left_mover_tid)
    requires AtomicThreadYielding(arr.l, last(left_mover_states_mid), left_mover_tid)
    requires forall i :: 0 <= i < |left_mover_states_mid|-1 ==> IsPhase2(arr, left_mover_states_mid[i], left_mover_tid)
    requires forall path :: path in left_mover_paths_mid ==> !arr.l.path_type(path).AtomicPathType_Tau?
    requires arr.l.path_valid(last(left_mover_states_mid), last(crash_path_paths), crash_path_tid)
    requires post_crash_state' == arr.l.path_next(last(left_mover_states_mid), last(crash_path_paths), crash_path_tid);
    requires rr.crashed(post_crash_state')
    requires RefinementPair(post_crash_state, post_crash_state') in rr.relation

    ensures  StateNextSeq(left_mover_states, left_mover_paths, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall path :: path in left_mover_paths ==> rr.idmap(path) == Some(left_mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, last(left_mover_states), post_crash_state', crash_path_paths, crash_path_tid)
    ensures  crash_path_states' == AtomicGetStateSequence(arr.l, last(left_mover_states), crash_path_paths, crash_path_tid)
    ensures  |crash_path_states'| == |crash_path_states|
    ensures  !crash_path_tau ==>
               forall i :: 0 <= i < |crash_path_states|-1 ==> OKAndPCTypesMatch(arr, crash_path_states'[i], crash_path_states[i], crash_path_tid)
  {
    var pos := |crash_path_states|-2;
    var penultimate_state := crash_path_states[pos];
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, initial_state, post_crash_state, crash_path_paths,
                                                           crash_path_tid, crash_path_states, pos);
    lemma_AtomicNextLastElement(arr.l, initial_state, post_crash_state, crash_path_paths, crash_path_tid, crash_path_states);
    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, post_crash_state, crash_path_paths,
                                                  crash_path_tid, crash_path_states, pos);
    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, initial_state, post_crash_state, crash_path_paths,
                                                     crash_path_states, crash_path_tid);

    var mover_states', other_states' :=
      lemma_MoveLeftMoversLeftAsSinglePaths(
        arr, left_mover_tid, crash_path_tid, crash_path_tau, left_mover_states_mid, left_mover_paths_mid,
        all_but_last(crash_path_states), all_but_last(crash_path_paths));

    left_mover_states, left_mover_paths :=
      lemma_CombineLeftMoverSubpathsIntoPaths(arr, rr, left_mover_tid, mover_states', left_mover_paths_mid);

    assert last(left_mover_states) == last(mover_states') == other_states'[0];
    assert AtomicNextMultiplePaths(arr.l, other_states'[0], last(other_states'), all_but_last(crash_path_paths), crash_path_tid);
    assert last(other_states') == last(left_mover_states_mid);

    lemma_ExtendingStateSequenceWorks(arr.l, last(left_mover_states), last(left_mover_states_mid), all_but_last(crash_path_paths),
                                      other_states', crash_path_tid, last(crash_path_paths), post_crash_state');
    lemma_AllButLastPlusLastIsSeq(crash_path_paths);
    assert AtomicNextMultiplePaths(arr.l, last(left_mover_states), post_crash_state', crash_path_paths, crash_path_tid);

    crash_path_states' := other_states' + [post_crash_state'];
    if !crash_path_tau {
      forall i | 0 <= i < |crash_path_states|-1
        ensures OKAndPCTypesMatch(arr, crash_path_states'[i], crash_path_states[i], crash_path_tid)
      {
        assert crash_path_states'[i] == other_states'[i];
        assert all_but_last(crash_path_states)[i] == crash_path_states[i];
      }
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPath<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_path:LPath,
    crash_path_tid:Armada_ThreadHandle,
    crash_path_tau:bool,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_paths:seq<LPath>,
    post_crash_state':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, crash_path, crash_path_tid)
    requires post_crash_state == arr.l.path_next(initial_state, crash_path, crash_path_tid)
    requires arr.l.path_type(crash_path).AtomicPathType_Tau? == crash_path_tau
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_path_tau || crash_path_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    ensures  |left_mover_states| > 0
    ensures  AtomicNextMultiplePaths(arr.l, initial_state, last(left_mover_states), left_mover_paths, left_mover_tid)
    ensures  left_mover_states == AtomicGetStateSequence(arr.l, initial_state, left_mover_paths, left_mover_tid)
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  AtomicThreadYielding(arr.l, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  |left_mover_paths| > 0
    ensures  forall path :: path in left_mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
    ensures  arr.l.path_valid(last(left_mover_states), crash_path, crash_path_tid)
    ensures  post_crash_state' == arr.l.path_next(last(left_mover_states), crash_path, crash_path_tid)
    ensures  !crash_path_tau ==> OKAndPCTypesMatch(arr, last(left_mover_states), initial_state, crash_path_tid)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
    decreases arr.left_mover_generation_progress(initial_state, left_mover_tid)
  {
    assert AtomicReductionSpecModule.LeftMoversAlwaysEnabledConditions(arr, initial_state, left_mover_tid);
    var left_mover_path := arr.generate_left_mover(initial_state, left_mover_tid);
    var state_after_left_mover := arr.l.path_next(initial_state, left_mover_path, left_mover_tid);
    assert && arr.l.path_valid(initial_state, left_mover_path, left_mover_tid)
           && !arr.l.path_type(left_mover_path).AtomicPathType_Tau?
           && 0 <= arr.left_mover_generation_progress(state_after_left_mover, left_mover_tid)
               < arr.left_mover_generation_progress(initial_state, left_mover_tid);

    assert AtomicReductionSpecModule.LeftMoverCrashPreservationConditions(arr, initial_state, left_mover_path, crash_path,
                                                                          left_mover_tid, crash_path_tid);
    var state_after_both_paths := arr.l.path_next(state_after_left_mover, crash_path, crash_path_tid);
    assert && arr.l.path_valid(state_after_left_mover, crash_path, crash_path_tid)
           && !arr.l.state_ok(state_after_both_paths)
           && RefinementPair(post_crash_state, state_after_both_paths) in arr.self_relation;

    if !IsPhase2(arr, state_after_left_mover, left_mover_tid) {
      assert AtomicThreadYielding(arr.l, state_after_left_mover, left_mover_tid);
      left_mover_states := [initial_state, state_after_left_mover];
      left_mover_paths := [left_mover_path];
      post_crash_state' := state_after_both_paths;
    }
    else {
      var left_mover_states_next, left_mover_paths_next;
      left_mover_states_next, left_mover_paths_next, post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPath(
          arr, rr, state_after_left_mover, state_after_both_paths, crash_path, crash_path_tid, crash_path_tau, left_mover_tid);
      left_mover_states := [initial_state] + left_mover_states_next;
      left_mover_paths := [left_mover_path] + left_mover_paths_next;
      lemma_LastOfConcatenationIsLastOfLatter([initial_state], left_mover_states_next);
    }
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPathSequence
    <LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_path_paths:seq<LPath>,
    crash_path_tid:Armada_ThreadHandle,
    crash_path_tau:bool,
    crash_path_states:seq<LState>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_paths:seq<Armada_Multistep<LPath>>,
    crash_path_states':seq<LState>,
    post_crash_state':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultiplePaths(arr.l, initial_state, post_crash_state, crash_path_paths, crash_path_tid)
    requires forall path :: path in crash_path_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == crash_path_tau
    requires crash_path_states == AtomicGetStateSequence(arr.l, initial_state, crash_path_paths, crash_path_tid)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_path_tau || crash_path_tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires AtomicThreadYielding(arr.l, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_paths, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall path :: path in left_mover_paths ==> rr.idmap(path) == Some(left_mover_tid)
    ensures  AtomicNextMultiplePaths(arr.l, last(left_mover_states), post_crash_state', crash_path_paths, crash_path_tid)
    ensures  crash_path_states' == AtomicGetStateSequence(arr.l, last(left_mover_states), crash_path_paths, crash_path_tid)
    ensures  |crash_path_states'| == |crash_path_states|
    ensures  !crash_path_tau ==>
               forall i :: 0 <= i < |crash_path_states|-1 ==> OKAndPCTypesMatch(arr, crash_path_states'[i], crash_path_states[i], crash_path_tid)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    assert |crash_path_paths| > 0;

    var pos := |crash_path_states|-2;
    var penultimate_state := crash_path_states[pos];
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, initial_state, post_crash_state, crash_path_paths,
                                                           crash_path_tid, crash_path_states, pos);
    lemma_AtomicNextLastElement(arr.l, initial_state, post_crash_state, crash_path_paths, crash_path_tid, crash_path_states);
    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, post_crash_state, crash_path_paths,
                                                  crash_path_tid, crash_path_states, pos);
    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, initial_state, post_crash_state, crash_path_paths, crash_path_states,
                                                     crash_path_tid);
    lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, initial_state, penultimate_state, all_but_last(crash_path_paths),
                                                            crash_path_tau, crash_path_tid, left_mover_tid);

    var left_mover_states_mid, left_mover_paths_mid;
    left_mover_states_mid, left_mover_paths_mid, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPath(
        arr, rr, penultimate_state, post_crash_state, last(crash_path_paths), crash_path_tid, crash_path_tau, left_mover_tid);

    left_mover_states, left_mover_paths, crash_path_states' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPathSequencePart2(
        arr, rr, initial_state, post_crash_state, crash_path_paths, crash_path_tid, crash_path_tau, crash_path_states,
        left_mover_tid, left_mover_states_mid, left_mover_paths_mid, post_crash_state');
  }

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashArmada_Multistep
    <LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_multistep:Armada_Multistep<LPath>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_multisteps:seq<Armada_Multistep<LPath>>,
    post_crash_state':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultistep(arr.l, initial_state, post_crash_state, crash_multistep.steps, crash_multistep.tid, crash_multistep.tau)
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires crash_multistep.tau || crash_multistep.tid != left_mover_tid
    requires IsPhase2(arr, initial_state, left_mover_tid)
    requires AtomicThreadYielding(arr.l, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_multisteps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall path :: path in left_mover_multisteps ==> rr.idmap(path) == Some(left_mover_tid)
    ensures  AtomicNextMultistep(arr.l, last(left_mover_states), post_crash_state', crash_multistep.steps, crash_multistep.tid,
                                 crash_multistep.tau)
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    var crash_multistep_states := AtomicGetStateSequence(arr.l, initial_state, crash_multistep.steps, crash_multistep.tid);
    var crash_multistep_states';
    left_mover_states, left_mover_multisteps, crash_multistep_states', post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashPathSequence(
        arr, rr, initial_state, post_crash_state, crash_multistep.steps, crash_multistep.tid, crash_multistep.tau, crash_multistep_states,
        left_mover_tid);
  } 

  lemma lemma_DemonstrateLeftMoversEnabledBeforeCrash<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    post_crash_state:LState,
    crash_multistep:Armada_Multistep<LPath>,
    left_mover_tid:Armada_ThreadHandle
    ) returns (
    left_mover_states:seq<LState>,
    left_mover_multisteps:seq<Armada_Multistep<LPath>>,
    post_crash_state':LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, post_crash_state, crash_multistep) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires rr.crashed(post_crash_state)
    requires rr.idmap(crash_multistep) != Some(left_mover_tid)
    requires IsPhase2(arr, initial_state, left_mover_tid)
    ensures  StateNextSeq(left_mover_states, left_mover_multisteps, rr.lspec.next)
    ensures  left_mover_states[0] == initial_state
    ensures  arr.l.state_ok(last(left_mover_states))
    ensures  !IsPhase2(arr, last(left_mover_states), left_mover_tid)
    ensures  forall i :: 0 <= i < |left_mover_states|-1 ==> IsPhase2(arr, left_mover_states[i], left_mover_tid)
    ensures  forall path :: path in left_mover_multisteps ==> rr.idmap(path) == Some(left_mover_tid)
    ensures  ActionTuple(last(left_mover_states), post_crash_state', crash_multistep) in rr.lspec.next
    ensures  rr.crashed(post_crash_state')
    ensures  RefinementPair(post_crash_state, post_crash_state') in rr.relation
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    lemma_StateAmongAnnotatedReachablesHasThreadYielding(arr, initial_state, left_mover_tid);
    left_mover_states, left_mover_multisteps, post_crash_state' :=
      lemma_DemonstrateLeftMoversEnabledBeforeCrashCrashArmada_Multistep(
        arr, rr, initial_state, post_crash_state, crash_multistep, left_mover_tid);
    assert AtomicNextMultistep(arr.l, last(left_mover_states), post_crash_state', crash_multistep.steps, crash_multistep.tid,
                               crash_multistep.tau);
    assert ActionTuple(last(left_mover_states), post_crash_state', crash_multistep) in rr.lspec.next;
  }

  lemma lemma_LeftMoversEnabledBeforeCrash<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  LeftMoversEnabledBeforeCrash(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    forall initial_state, post_crash_state, crash_multistep, actor
      {:trigger RefinementViaReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state,
                                                                                        crash_multistep, actor)}
      | RefinementViaReductionSpecModule.LeftMoversEnabledBeforeCrashConditions(rr, initial_state, post_crash_state, crash_multistep, actor)
      ensures exists states, trace, crash_multistep', post_crash_state' ::
                 && StateNextSeq(states, trace, rr.lspec.next)
                 && states[0] == initial_state
                 && !rr.crashed(last(states))
                 && !rr.phase2(last(states), actor)
                 && (forall i :: 0 <= i < |states|-1 ==> rr.phase2(states[i], actor))
                 && (forall path :: path in trace ==> rr.idmap(path) == actor)
                 && ActionTuple(last(states), post_crash_state', crash_multistep') in rr.lspec.next
                 && rr.idmap(crash_multistep') == rr.idmap(crash_multistep)
                 && rr.crashed(post_crash_state')
                 && RefinementPair(post_crash_state, post_crash_state') in rr.relation
    {
      var states, trace, post_crash_state' :=
        lemma_DemonstrateLeftMoversEnabledBeforeCrash(arr, rr, initial_state, post_crash_state, crash_multistep, actor.v);
    }
  }

  //////////////////////////////////////////
  // LEFT MOVER SELF CRASH PRESERVATION
  //////////////////////////////////////////

  lemma lemma_DemonstrateLeftMoverSinglePathSelfCrashPreservationAcrossSinglePath
    <LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_other_path:LState,
    state_after_both_paths:LState,
    other_path:LPath,
    mover_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires arr.l.path_valid(initial_state, other_path, other_tid)
    requires state_after_other_path == arr.l.path_next(initial_state, other_path, other_tid)
    requires arr.l.path_type(other_path).AtomicPathType_Tau? == other_tau
    requires arr.l.path_valid(state_after_other_path, mover_path, mover_tid)
    requires state_after_both_paths == arr.l.path_next(state_after_other_path, mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_path)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase2(arr, state_after_other_path, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  arr.l.path_valid(initial_state, mover_path, mover_tid)
    ensures  state_after_left_mover == arr.l.path_next(initial_state, mover_path, mover_tid)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_paths, state_after_left_mover) in rr.relation
  {
    assert AtomicReductionSpecModule.LeftMoverSelfCrashPreservationConditions(arr, initial_state, mover_path, other_path,
                                                                              mover_tid, other_tid);
    state_after_left_mover := arr.l.path_next(initial_state, mover_path, mover_tid);
  }

  lemma lemma_DemonstrateLeftMoverSinglePathSelfCrashPreservationAcrossPathSequence
    <LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_other_path:LState,
    state_after_both_paths:LState,
    other_paths:seq<LPath>,
    mover_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultiplePaths(arr.l, initial_state, state_after_other_path, other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires arr.l.path_valid(state_after_other_path, mover_path, mover_tid)
    requires state_after_both_paths == arr.l.path_next(state_after_other_path, mover_path, mover_tid)
    requires !arr.l.path_type(mover_path).AtomicPathType_Tau?
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_path)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase2(arr, state_after_other_path, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  arr.l.path_valid(initial_state, mover_path, mover_tid)
    ensures  state_after_left_mover == arr.l.path_next(initial_state, mover_path, mover_tid)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_paths, state_after_left_mover) in rr.relation
  {
    if |other_paths| == 0 {
      state_after_left_mover := state_after_both_paths;
      return;
    }

    var other_states := AtomicGetStateSequence(arr.l, initial_state, other_paths, other_tid);
    var pos := |other_states|-2;
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, initial_state, state_after_other_path, other_paths,
                                                           other_tid, other_states, pos);
    lemma_AtomicNextLastElement(arr.l, initial_state, state_after_other_path, other_paths, other_tid, other_states);
    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, initial_state, state_after_other_path, other_paths, other_states, other_tid);
    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, state_after_other_path, other_paths, other_tid,
                                                  other_states, pos);
    var state_after_left_mover_mid :=
      lemma_DemonstrateLeftMoverSinglePathSelfCrashPreservationAcrossSinglePath(
        arr, rr, other_states[pos], other_states[pos+1], state_after_both_paths, last(other_paths), mover_path,
        mover_tid, other_tau, other_tid);

    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSinglePathSelfCrashPreservationAcrossPathSequence(
        arr, rr, initial_state, other_states[pos], state_after_left_mover_mid, all_but_last(other_paths), mover_path,
        mover_tid, other_tau, other_tid);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationPathSequence<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_other_path:LState,
    state_after_both_paths:LState,
    other_paths:seq<LPath>,
    mover_paths:seq<LPath>,
    mover_states:seq<LState>,
    mover_tid:Armada_ThreadHandle,
    other_tau:bool,
    other_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState,
    mover_states':seq<LState>
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultiplePaths(arr.l, initial_state, state_after_other_path, other_paths, other_tid)
    requires forall path :: path in other_paths ==> arr.l.path_type(path).AtomicPathType_Tau? == other_tau
    requires AtomicNextMultiplePaths(arr.l, state_after_other_path, state_after_both_paths, mover_paths, mover_tid)
    requires mover_states == AtomicGetStateSequence(arr.l, state_after_other_path, mover_paths, mover_tid)
    requires forall path :: path in mover_paths ==> !arr.l.path_type(path).AtomicPathType_Tau?
    requires forall i :: 0 <= i < |mover_states|-1 ==> IsPhase2(arr, mover_states[i], mover_tid)
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_path)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase2(arr, state_after_other_path, mover_tid)
    requires other_tau || other_tid != mover_tid
    ensures  AtomicNextMultiplePaths(arr.l, initial_state, state_after_left_mover, mover_paths, mover_tid)
    ensures  mover_states' == AtomicGetStateSequence(arr.l, initial_state, mover_paths, mover_tid)
    ensures  |mover_states'| == |mover_states|
    ensures  forall i :: 0 <= i < |mover_states|-1 ==> OKAndPCTypesMatch(arr, mover_states[i], mover_states'[i], mover_tid)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_paths, state_after_left_mover) in rr.relation
  {
    assert state_after_both_paths != state_after_other_path;
    assert |mover_paths| > 0;

    var pos := |mover_states|-2;
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, state_after_other_path, state_after_both_paths, mover_paths,
                                                           mover_tid, mover_states, pos);
    assert !rr.crashed(mover_states[pos]);

    var other_states := AtomicGetStateSequence(arr.l, initial_state, other_paths, other_tid);
    lemma_AtomicNextLastElement(arr.l, initial_state, state_after_other_path, other_paths, other_tid, other_states);
    lemma_AtomicNextLastElement(arr.l, state_after_other_path, state_after_both_paths, mover_paths, mover_tid, mover_states);
    lemma_AllButLastPreservesAtomicNextMultiplePaths(arr, state_after_other_path, state_after_both_paths, mover_paths, mover_states,
                                                     mover_tid);

    var mover_states_mid, other_states_mid;
    if |mover_paths| == 1 {
      mover_states_mid := [initial_state];
      other_states_mid := other_states;
      forall i | 0 <= i < |all_but_last(mover_states)|
        ensures OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid)
      {
        assert mover_states_mid[i] == initial_state;
        assert all_but_last(mover_states)[i] == state_after_other_path;
        lemma_ExecutingPathSequenceDoesntChangeOtherActorPCType(arr, initial_state, state_after_other_path, other_paths, other_tau,
                                                                other_tid, mover_tid);
      }
    }
    else {
      mover_states_mid, other_states_mid :=
        lemma_MoveLeftMoversLeftAsSinglePaths(arr, mover_tid, other_tid, other_tau, all_but_last(mover_states),
                                              all_but_last(mover_paths), other_states, other_paths);
    }
    assert forall i :: 0 <= i < |all_but_last(mover_states)| ==>
                 OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid);

    lemma_AtomicInvariantHoldsAtIntermediateState(arr.l, arr.inv, initial_state, last(mover_states_mid), all_but_last(mover_paths),
                                                  mover_tid, mover_states_mid, |mover_states_mid|-1);
    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSinglePathSelfCrashPreservationAcrossPathSequence(
        arr, rr, last(mover_states_mid), last(other_states_mid), last(mover_states), other_paths, last(mover_paths),
        mover_tid, other_tau, other_tid);
    mover_states' := mover_states_mid + [state_after_left_mover];
    lemma_ExtendingStateSequenceWorks(arr.l, initial_state, last(mover_states_mid), all_but_last(mover_paths), mover_states_mid,
                                      mover_tid, last(mover_paths), state_after_left_mover);
    lemma_AllButLastPlusLastIsSeq(mover_paths);

    forall i | 0 <= i < |mover_states|-1
      ensures OKAndPCTypesMatch(arr, mover_states[i], mover_states'[i], mover_tid)
    {
      assert mover_states'[i] == mover_states_mid[i];
      assert 0 <= i < |all_but_last(mover_states)|;
      assert OKAndPCTypesMatch(arr, mover_states_mid[i], all_but_last(mover_states)[i], mover_tid);
      assert all_but_last(mover_states)[i] == mover_states[i];
    }
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservationArmadaMultistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_other_multistep:LState,
    state_after_both_paths:LState,
    other_multistep:Armada_Multistep<LPath>,
    mover_multistep:Armada_Multistep<LPath>,
    mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires arr.inv(initial_state)
    requires AtomicNextMultistep(arr.l, initial_state, state_after_other_multistep, other_multistep.steps,
                                 other_multistep.tid, other_multistep.tau)
    requires AtomicNextMultistep(arr.l, state_after_other_multistep, state_after_both_paths, mover_multistep.steps,
                                 mover_multistep.tid, mover_multistep.tau)
    requires mover_multistep.tid == mover_tid
    requires !mover_multistep.tau
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_multistep)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase2(arr, state_after_other_multistep, mover_tid)
    requires other_multistep.tau || other_multistep.tid != mover_tid
    ensures  AtomicNextMultistep(arr.l, initial_state, state_after_left_mover, mover_multistep.steps, mover_multistep.tid,
                                 mover_multistep.tau)
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_paths, state_after_left_mover) in rr.relation
  {
    var mover_states := AtomicGetStateSequence(arr.l, state_after_other_multistep, mover_multistep.steps, mover_multistep.tid);
    lemma_IfMultistepStartsInPhase2ThenEachPathDoes(arr, state_after_other_multistep, state_after_both_paths, mover_multistep,
                                                    mover_states);
    var mover_states';
    state_after_left_mover, mover_states' :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationPathSequence(
        arr, rr, initial_state, state_after_other_multistep, state_after_both_paths, other_multistep.steps, mover_multistep.steps,
        mover_states, mover_tid, other_multistep.tau, other_multistep.tid);
  }

  lemma lemma_DemonstrateLeftMoverSelfCrashPreservation<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    rr:RefinementViaReductionRequest<LState, Option<Armada_ThreadHandle>, Armada_Multistep<LPath>, Armada_Multistep<LPath>>,
    initial_state:LState,
    state_after_other_multistep:LState,
    state_after_both_paths:LState,
    other_multistep:Armada_Multistep<LPath>,
    left_mover:Armada_Multistep<LPath>,
    mover_tid:Armada_ThreadHandle
    ) returns (
    state_after_left_mover:LState
    )
    requires ValidAtomicReductionRequest(arr)
    requires rr == GetRefinementViaReductionRequest(arr)
    requires initial_state in AnnotatedReachables(rr.lspec)
    requires ActionTuple(initial_state, state_after_other_multistep, other_multistep) in rr.lspec.next
    requires ActionTuple(state_after_other_multistep, state_after_both_paths, left_mover) in rr.lspec.next
    requires !rr.crashed(initial_state)
    requires !rr.crashed(state_after_other_multistep)
    requires rr.crashed(state_after_both_paths)
    requires IsPhase2(arr, state_after_other_multistep, mover_tid)
    requires rr.idmap(left_mover) == Some(mover_tid)
    requires rr.idmap(other_multistep) != Some(mover_tid)
    ensures  ActionTuple(initial_state, state_after_left_mover, left_mover) in rr.lspec.next
    ensures  rr.crashed(state_after_left_mover)
    ensures  RefinementPair(state_after_both_paths, state_after_left_mover) in rr.relation
  {
    lemma_StateAmongAnnotatedReachablesSatisfiesInv(arr, initial_state);
    state_after_left_mover :=
      lemma_DemonstrateLeftMoverSelfCrashPreservationArmadaMultistep(
        arr, rr, initial_state, state_after_other_multistep, state_after_both_paths, other_multistep, left_mover, mover_tid);
  }

  lemma lemma_LeftMoverSelfCrashPreservation<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservation(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);

    forall initial_state, state_after_other_multistep, state_after_both_paths, other_multistep, left_mover
      {:trigger RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_multistep,
                                                                                          state_after_both_paths, other_multistep,
                                                                                          left_mover)}
      | RefinementViaReductionSpecModule.LeftMoverSelfCrashPreservationConditions(rr, initial_state, state_after_other_multistep,
                                                                                  state_after_both_paths, other_multistep, left_mover)
      && initial_state in AnnotatedReachables(rr.lspec)
      && ActionTuple(initial_state, state_after_other_multistep, other_multistep) in rr.lspec.next
      && ActionTuple(state_after_other_multistep, state_after_both_paths, left_mover) in rr.lspec.next
      && !rr.crashed(initial_state)
      && !rr.crashed(state_after_other_multistep)
      && rr.crashed(state_after_both_paths)
      && rr.phase2(state_after_other_multistep, rr.idmap(left_mover))
      && rr.idmap(left_mover) != rr.idmap(other_multistep)
      ensures exists left_mover', state_after_left_mover' ::
                 && rr.idmap(left_mover') == rr.idmap(left_mover)
                 && ActionTuple(initial_state, state_after_left_mover', left_mover') in rr.lspec.next
                 && rr.crashed(state_after_left_mover')
                 && RefinementPair(state_after_both_paths, state_after_left_mover') in rr.relation
    {
      var state_after_left_mover :=
        lemma_DemonstrateLeftMoverSelfCrashPreservation(arr, rr, initial_state, state_after_other_multistep, state_after_both_paths,
                                                        other_multistep, left_mover, rr.idmap(left_mover).v);
    }
  }

  //////////////////////////////////////
  // REDUCTION REQUEST VALID
  //////////////////////////////////////

  lemma lemma_IfAtomicReductionRequestValidThenRefinementViaReductionRequestValid
    <LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
    requires ValidAtomicReductionRequest(arr)
    ensures  ValidRefinementViaReductionRequest(GetRefinementViaReductionRequest(arr))
  {
    var rr := GetRefinementViaReductionRequest(arr);
    assert RefinementRelationReflexive(rr.relation);
    assert RefinementRelationTransitive(rr.relation);
    assert rr.hspec.init == rr.lspec.init;
    assert forall s, actor :: s in rr.lspec.init ==> !rr.phase1(s, actor) && !rr.phase2(s, actor);
    assert forall s, actor :: rr.phase1(s, actor) ==> !rr.phase2(s, actor);
    lemma_IfAtomicReductionRequestValidThenCrashingCantGoDirectlyFromPhase2ToPhase1(arr);
    lemma_IfAtomicReductionRequestValidThenCrashingPhaseUnaffectedByOtherActors(arr);
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

  function LMultistepToHMultistep<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    lmultipath:Armada_Multistep<LPath>
    ) : Armada_Multistep<HPath>
  {
    Armada_Multistep(MapSeqToSeq(lmultipath.steps, arr.lpath_to_hpath), lmultipath.tid, lmultipath.tau)
  }

  //////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////

  lemma lemma_ArmadaGetStateSequenceLastElement<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    states:seq<LState>,
    tid:Armada_ThreadHandle
    )
    requires AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    requires states == AtomicGetStateSequence(arr.l, s, paths, tid)
    ensures  last(states) == s'
  {
    if |paths| > 0 {
      var s_mid := arr.l.path_next(s, paths[0], tid);
      lemma_ArmadaGetStateSequenceLastElement(arr, s_mid, s', paths[1..], states[1..], tid);
    }
  }

  lemma lemma_AtomicValidPathSequenceImpliesOfAnyType<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle
    )
    requires AtomicValidPathSequence(asf, s, paths, tid)
    ensures  AtomicValidPathSequenceOfAnyType(asf, s, paths, tid)
  {
    if |paths| > 0 {
      var s_next := asf.path_next(s, paths[0], tid);
      lemma_AtomicValidPathSequenceImpliesOfAnyType(asf, s_next, paths[1..], tid);
    }
  }

  lemma lemma_AtomicValidPathSequenceImpliesRR<State, Path, PC>(
    asf: AtomicSpecFunctions<State, Path, PC>,
    s: State,
    paths: seq<Path>,
    tid: Armada_ThreadHandle,
    pos: int
    )
    requires AtomicValidPathSequence(asf, s, paths, tid)
    requires 0 <= pos < |paths|
    ensures  asf.path_type(paths[pos]).AtomicPathType_RR?
  {
    if pos > 0 {
      var s_next := asf.path_next(s, paths[0], tid);
      lemma_AtomicValidPathSequenceImpliesRR(asf, s_next, paths[1..], tid, pos-1);
    }
  }

  /////////////////////////////////////////////
  // SHIM BETWEEN ARMADA AND COHEN-LAMPORT
  /////////////////////////////////////////////

  function ConvertAtomicTraceEntryToMultistep<State, Path, PC>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    entry:AtomicTraceEntry<Path>
    ) : Armada_Multistep<Path>
  {
    match entry
      case AtomicTraceEntry_Stutter => Armada_Multistep([], 0, false)
      case AtomicTraceEntry_Tau(tid, path) => Armada_Multistep([path], tid, true)
      case AtomicTraceEntry_Normal(tid, path) => Armada_Multistep([path], tid, false)
      case AtomicTraceEntry_Recurrent(tid, yr, rrs, rx) => Armada_Multistep([yr] + rrs + [rx], tid, false)
  }

  function ConvertMultistepToAtomicTraceEntry<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    multistep:Armada_Multistep<LPath>
    ) : AtomicTraceEntry<HPath>
  {
    if |multistep.steps| == 0 then
      AtomicTraceEntry_Stutter()
    else
      var hpath0 := arr.lpath_to_hpath(multistep.steps[0]);
      if multistep.tau then
        AtomicTraceEntry_Tau(multistep.tid, hpath0)
      else if |multistep.steps| == 1 then
        AtomicTraceEntry_Normal(multistep.tid, hpath0)
      else
        AtomicTraceEntry_Recurrent(
          multistep.tid,
          hpath0,
          MapSeqToSeq(multistep.steps[1..|multistep.steps|-1], arr.lpath_to_hpath),
          arr.lpath_to_hpath(last(multistep.steps))
        )
  }

  lemma lemma_ConvertAtomicTraceEntryToMultistepMaintainsNext<State(!new), Path(!new), PC(!new)>(
    asf:AtomicSpecFunctions<State, Path, PC>,
    s:State,
    s':State,
    lentry:AtomicTraceEntry<Path>
    )
    requires AtomicPathRequiresOK(asf)
    requires AtomicPathTypeAlwaysMatchesPCTypes(asf)
    requires AtomicNext(asf, s, s', lentry)
    ensures  var hmultistep := ConvertAtomicTraceEntryToMultistep(asf, lentry);
             AtomicNextMultistep(asf, s, s', hmultistep.steps, hmultistep.tid, hmultistep.tau)
  {
    var hmultistep := ConvertAtomicTraceEntryToMultistep(asf, lentry);
    if !lentry.AtomicTraceEntry_Recurrent? {
      // Everything but the recurrent case is trivial
      return;
    }

    var tid, yr, rrs, rx := lentry.recurrent_tid, lentry.yr, lentry.rrs, lentry.rx;
    var s1 := asf.path_next(s, yr, tid);
    var s2 := AtomicGetStateAfterPaths(asf, s1, rrs, tid);
    lemma_AtomicValidPathSequenceImpliesOfAnyType(asf, s1, rrs, tid);

    var paths := [yr] + rrs + [rx];
    var states_mid := AtomicGetStateSequence(asf, s1, rrs, tid);
    var states := [s] + states_mid + [s'];

    forall i | 0 <= i < |paths|
      ensures asf.path_valid(states[i], paths[i], tid)
      ensures states[i+1] == asf.path_next(states[i], paths[i], tid)
      ensures !asf.path_type(paths[i]).AtomicPathType_Tau?
      ensures i > 0 ==> var ty := asf.path_type(paths[i]); ty.AtomicPathType_RY? || ty.AtomicPathType_RS? || ty.AtomicPathType_RR?
    {
      if i == 0 {
        assert states[i] == s;
        assert states[i+1] == s1;
        assert paths[i] == yr;
      }
      else if i < |paths|-1 {
        lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(asf, s1, s2, rrs, tid, states_mid, i-1);
        assert asf.path_valid(states_mid[i-1], rrs[i-1], tid);
        assert states_mid[i-1+1] == asf.path_next(states_mid[i-1], rrs[i-1], tid);
        assert states[i] == states_mid[i-1];
        assert states[i+1] == states_mid[i-1+1];
        lemma_AtomicValidPathSequenceImpliesRR(asf, s1, rrs, tid, i-1);
      }
      else {
        lemma_AtomicNextLastElement(asf, s1, s2, rrs, tid, states_mid);
        assert states[i] == s2;
        assert states[i+1] == s';
        assert paths[i] == rx;
      }
    }

    forall i | 0 < i < |paths|
      ensures !AtomicThreadYielding(asf, states[i], tid)
    {
      assert asf.path_valid(states[i], paths[i], tid);
      assert states[i+1] == asf.path_next(states[i], paths[i], tid);
      var ty := asf.path_type(paths[i]);
      assert ty.AtomicPathType_RY? || ty.AtomicPathType_RS? || ty.AtomicPathType_RR?;
      assert !AtomicThreadYielding(asf, states[i], tid);
    }

    var pos := 0;
    while pos < |paths|
      invariant 0 <= pos <= |paths|
      invariant AtomicNextMultiplePaths(asf, s, states[pos], paths[..pos], tid)
      invariant states[..pos+1] == AtomicGetStateSequence(asf, s, paths[..pos], tid)
    {
      lemma_ExtendingStateSequenceWorks(asf, s, states[pos], paths[..pos], states[..pos+1], tid, paths[pos], states[pos+1]);
      assert paths[..pos+1] == paths[..pos] + [paths[pos]];
      assert states[..pos+1+1] == states[..pos+1] + [states[pos+1]];
      pos := pos + 1;
    }

    assert s' == states[pos];
    assert paths[..pos] == paths;
    assert AtomicNextMultiplePaths(asf, s, s', paths, tid);
  }

  lemma lemma_IfBehaviorSatisfiesGenericSpecThenItSatisfiesRefinementViaReductionLSpec<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    lb:AnnotatedBehavior<LState, AtomicTraceEntry<LPath>>
    ) returns (
    hb:AnnotatedBehavior<LState, Armada_Multistep<LPath>>
    )
    requires ValidAtomicReductionRequest(arr)
    requires AnnotatedBehaviorSatisfiesSpec(lb, AtomicAnnotatedSpec(arr.l))
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, GetRefinementViaReductionLSpec(arr))
    ensures  hb.states == lb.states
  {
    var htrace := MapSeqToSeq(lb.trace, entry => ConvertAtomicTraceEntryToMultistep(arr.l, entry));
    hb := AnnotatedBehavior(lb.states, htrace);

    var lspec := AtomicAnnotatedSpec(arr.l);
    var hspec := GetRefinementViaReductionLSpec(arr);
    forall i {:trigger ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in hspec.next} | 0 <= i < |hb.trace|
      ensures ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in hspec.next
    {
      assert ActionTuple(lb.states[i], lb.states[i+1], lb.trace[i]) in AtomicAnnotatedSpec(arr.l).next;
      lemma_ConvertAtomicTraceEntryToMultistepMaintainsNext(arr.l, lb.states[i], lb.states[i+1], lb.trace[i]);
    }
  }

  lemma lemma_LHMaintainsNextRecurrent<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    ls:LState,
    ls':LState,
    lmultistep:Armada_Multistep<LPath>,
    hs:HState,
    hs':HState,
    hentry:AtomicTraceEntry<HPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.inv(ls)
    requires GenericNextReduced(arr, ls, ls', lmultistep.steps, lmultistep.tid, lmultistep.tau)
    requires !lmultistep.tau
    requires |lmultistep.steps| > 1
    requires hs == arr.lstate_to_hstate(ls)
    requires hs' == arr.lstate_to_hstate(ls')
    requires hentry == ConvertMultistepToAtomicTraceEntry(arr, lmultistep)
    requires hentry.AtomicTraceEntry_Recurrent?
    ensures  AtomicNext(arr.h, hs, hs', hentry)
  {
    var lpaths := lmultistep.steps;
    var tid, lyr, lrrs := lmultistep.tid, lpaths[0], lpaths[1..|lpaths|-1];
    var hyr, hrrs, hrx := hentry.yr, hentry.rrs, hentry.rx;

    var lstates := AtomicGetStateSequence(arr.l, ls, lpaths, tid);
    lemma_AtomicNextLastElement(arr.l, ls, ls', lpaths, tid, lstates);

    var hstates := MapSeqToSeq(lstates, arr.lstate_to_hstate);

    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, ls, ls', lpaths, tid, lstates, 0);
    assert arr.h.path_valid(hs, hyr, tid);
    assert hstates[1] == arr.h.path_next(hs, hyr, tid);

    assert !IsNonyieldingOrInPhase(arr, ls, tid);
    assert AtomicThreadYielding(arr.h, hs, tid);
    assert IsNonyieldingOrInPhase(arr, lstates[1], tid);
    assert !AtomicThreadYielding(arr.h, hstates[1], tid);

    var pos := 0;
    while pos < |hrrs|
      invariant 0 <= pos <= |hrrs|
      invariant forall p :: p in hrrs[..pos] ==> arr.h.path_type(p).AtomicPathType_RR?
      invariant AtomicValidPathSequence(arr.h, hstates[1], hrrs[..pos], tid)
      invariant hstates[pos+1] == AtomicGetStateAfterPaths(arr.h, hstates[1], hrrs[..pos], tid)
      invariant arr.inv(lstates[pos+1])
    {
      lemma_AtomicValidPathSequenceImpliesOfAnyType(arr.h, hstates[1], hrrs[..pos], tid);
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, ls, ls', lpaths, tid, lstates, pos+1);
      assert hrrs[pos] == arr.lpath_to_hpath(lpaths[pos+1]);
      assert hstates[pos+1] == arr.lstate_to_hstate(lstates[pos+1]);
      assert arr.h.path_valid(hstates[pos+1], hrrs[pos], tid);
      assert hstates[pos+1+1] == arr.h.path_next(hstates[pos+1], hrrs[pos], tid);
      lemma_ExtendAtomicGetStateAfterPaths(arr.h, hstates[1], hstates[pos+1], hrrs[..pos], tid, hrrs[pos]);
      assert hrrs[..pos+1] == hrrs[..pos] + [hrrs[pos]];
      lemma_ExtendAtomicValidPathSequence(arr.h, hstates[1], hstates[pos+1], hrrs[..pos], tid, hrrs[pos]);
      assert IsNonyieldingOrInPhase(arr, lstates[pos+1], tid);
      assert !AtomicThreadYielding(arr.h, hstates[pos+1], tid);
      assert IsNonyieldingOrInPhase(arr, lstates[pos+1+1], tid);
      assert !AtomicThreadYielding(arr.h, hstates[pos+1+1], tid);
      lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, ls, ls', lpaths, tid, lstates, pos+1+1);
      assert arr.h.path_type(hrrs[pos]).AtomicPathType_RR?;
      assert forall p :: p in hrrs[..pos+1] ==> p in hrrs[..pos] || p == hrrs[pos];
      pos := pos + 1;
    }

    assert hrrs[..pos] == hrrs;
    lemma_AtomicValidPathSequenceOfAnyTypeImpliesValidPath(arr.l, ls, ls', lpaths, tid, lstates, pos+1);
    assert AtomicValidRecursiveStep(arr.h, hs, tid, hyr, hrrs, hrx);
  }

  lemma lemma_LHMaintainsNext<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    ls:LState,
    ls':LState,
    lmultistep:Armada_Multistep<LPath>,
    hs:HState,
    hs':HState,
    hentry:AtomicTraceEntry<HPath>
    )
    requires ValidAtomicReductionRequest(arr)
    requires arr.inv(ls)
    requires ActionTuple(ls, ls', lmultistep) in GetRefinementViaReductionHSpec(arr).next;
    requires hs == arr.lstate_to_hstate(ls)
    requires hs' == arr.lstate_to_hstate(ls')
    requires hentry == ConvertMultistepToAtomicTraceEntry(arr, lmultistep)
    ensures  ActionTuple(hs, hs', hentry) in AtomicAnnotatedSpec(arr.h).next
  {
    assert GenericNextReduced(arr, ls, ls', lmultistep.steps, lmultistep.tid, lmultistep.tau);
    if |lmultistep.steps| == 0 {
      return;
    }

    var lstates := AtomicGetStateSequence(arr.l, ls, lmultistep.steps, lmultistep.tid);
    lemma_AtomicNextLastElement(arr.l, ls, ls', lmultistep.steps, lmultistep.tid, lstates);

    if lmultistep.tau {
      return;
    }

    if |lmultistep.steps| == 1 {
      return;
    }

    lemma_LHMaintainsNextRecurrent(arr, ls, ls', lmultistep, hs, hs', hentry);
  }

  lemma lemma_AtomicInvariantHoldsAtIntermediateStateAtomicNextMultiplePaths<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    s':LState,
    paths:seq<LPath>,
    tid:Armada_ThreadHandle,
    states:seq<LState>,
    pos:int
    )
    requires ValidAtomicReductionRequest(arr)
    requires AtomicNextMultiplePaths(arr.l, s, s', paths, tid)
    requires states == AtomicGetStateSequence(arr.l, s, paths, tid)
    requires 0 <= pos < |states|
    requires arr.inv(states[0])
    ensures  arr.inv(states[pos])
    decreases pos
  {
    if pos > 0 {
      var s_mid := arr.l.path_next(s, paths[0], tid);
      lemma_AtomicInvariantHoldsAtIntermediateStateAtomicNextMultiplePaths(arr, s_mid, s', paths[1..], tid, states[1..], pos-1);
    }
  }

  lemma lemma_GenericNextReducedBehaviorSatisfiesInv<LState(!new), LPath(!new), LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    b:AnnotatedBehavior<LState, Armada_Multistep<LPath>>,
    i:int
    )
    requires ValidAtomicReductionRequest(arr)
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
    var multistep := b.trace[prev];
    var paths := multistep.steps;
    var tid := multistep.tid;
    var states := AtomicGetStateSequence(arr.l, s, paths, tid);

    assert s' == b.states[i];
    assert 0 <= prev < |b.trace|;
    assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in spec.next;
    assert GenericNextReduced(arr, s, s', paths, multistep.tid, multistep.tau);
    assert AtomicNextMultiplePaths(arr.l, s, s', paths, tid);
    lemma_AtomicInvariantHoldsAtIntermediateStateAtomicNextMultiplePaths(arr, s, s', paths, tid, states, |states|-1);
    assert arr.inv(states[|states|-1]);
    assert arr.inv(last(states));
    lemma_ArmadaGetStateSequenceLastElement(arr, s, s', paths, states, tid);
    assert last(states) == s';
    assert arr.inv(s');
  }

}
