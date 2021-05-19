/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// This file is the specification for a request to perform refinement via a Cohen-Lamport reduction
// on an Armada atomic behavior.  Such a reduction takes a behavior satisfying a low-level spec, which
// allows threads to sometimes be in phase 1 or 2 between trace entries, and returns a behavior
// satisfying a higher-level specification that only allows those phases in the middle of
// trace entries.  It does so by lifting sequences of trace entries in the lower-level specification to
// single trace entries in the higher-level specification.
//
// To use this specification, first create a request r of type AtomicReductionRequest.  Then, prove
// that it's a valid request, i.e., that ValidAtomicReductionRequest(r).  Finally, call
// lemma_PerformArmadaReduction (in AtomicReduction.i.dfy).
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

include "../../util/option.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../generic/GenericArmadaSpec.i.dfy"
include "../generic/GenericArmadaAtomic.i.dfy"

module AtomicReductionSpecModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaAtomicModule
  import opened ArmadaCommonDefinitions

  datatype AtomicReductionRequest<!LState, !LPath, !LPC, !HState, !HPath, !HPC> =
    AtomicReductionRequest(
      l:AtomicSpecFunctions<LState, LPath, LPC>,
      h:AtomicSpecFunctions<HState, HPath, HPC>,
      relation:RefinementRelation<LState, HState>,
      inv:LState->bool,
      self_relation:RefinementRelation<LState, LState>,
      lstate_to_hstate:LState->HState,
      lpath_to_hpath:LPath->HPath,
      lpc_to_hpc:LPC->HPC,
      is_phase1:LPC->bool,
      is_phase2:LPC->bool,
      generate_left_mover:(LState, Armada_ThreadHandle)->LPath,
      left_mover_generation_progress:(LState,Armada_ThreadHandle)->int
      )

  predicate LInitImpliesHInit<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall ls :: arr.l.init(ls) ==> arr.h.init(arr.lstate_to_hstate(ls))
  }

  predicate LStateToHStateMapsPCsCorrectly<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall ls, tid :: var hs := arr.lstate_to_hstate(ls);
                var lpc := arr.l.get_thread_pc(ls, tid);
                var hpc := arr.h.get_thread_pc(hs, tid);
                hpc == if lpc.Some? then Some(arr.lpc_to_hpc(lpc.v)) else None()
  }

  predicate LHYieldingCorrespondence<LState, LPath, LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall lpc :: var hpc := arr.lpc_to_hpc(lpc);
            arr.h.is_pc_nonyielding(hpc) <==> (arr.l.is_pc_nonyielding(lpc) || arr.is_phase1(lpc) || arr.is_phase2(lpc))
  }

  predicate LHPathTypesMatchYR(lty:AtomicPathType, hty:AtomicPathType)
  {
    match lty
      case AtomicPathType_Tau => hty.AtomicPathType_Tau?
      case AtomicPathType_YY  =>
        hty.AtomicPathType_YY? || hty.AtomicPathType_YR? || hty.AtomicPathType_RY? || hty.AtomicPathType_RR?
      case AtomicPathType_YS  => hty.AtomicPathType_YS? || hty.AtomicPathType_RS?
      case AtomicPathType_YR  => hty.AtomicPathType_YR? || hty.AtomicPathType_RR?
      case AtomicPathType_RY  => hty.AtomicPathType_RY? || hty.AtomicPathType_RR?
      case AtomicPathType_RS  => hty.AtomicPathType_RS?
      case AtomicPathType_RR  => hty.AtomicPathType_RR?
  }

  predicate LHPathPropertiesMatch<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall lpath :: var hpath := arr.lpath_to_hpath(lpath);
              LHPathTypesMatchYR(arr.l.path_type(lpath), arr.h.path_type(hpath))
  }

  predicate LPathImpliesHPath<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall ls, lpath, tid ::
      arr.inv(ls) && arr.l.path_valid(ls, lpath, tid) ==>
      var ls' := arr.l.path_next(ls, lpath, tid);
      var hs := arr.lstate_to_hstate(ls);
      var hpath := arr.lpath_to_hpath(lpath);
      var hs' := arr.lstate_to_hstate(ls');
      && arr.h.path_valid(hs, hpath, tid)
      && hs' == arr.h.path_next(hs, hpath, tid)
  }

  predicate StateConversionPreservesOK<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall ls :: arr.h.state_ok(arr.lstate_to_hstate(ls)) == arr.l.state_ok(ls)
  }

  predicate StateConversionSatisfiesRelation<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall ls :: RefinementPair(ls, arr.lstate_to_hstate(ls)) in arr.relation
  }

  predicate ThreadsDontStartInAnyPhase<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, tid :: arr.l.init(s) && arr.l.get_thread_pc(s, tid).Some?
        ==> var pc := arr.l.get_thread_pc(s, tid).v;
            !arr.is_phase1(pc) && !arr.is_phase2(pc)
  }

  predicate PhasesDontOverlap<LState, LPath, LPC(!new), HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall pc :: arr.is_phase1(pc) ==> !arr.is_phase2(pc)
  }

  predicate ThreadCantAffectOtherThreadPhaseExceptViaFork
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, mover_tid, other_tid :: arr.l.path_valid(s, path, mover_tid) && mover_tid != other_tid
       ==> var s' := arr.l.path_next(s, path, mover_tid);
           var pc := arr.l.get_thread_pc(s, other_tid);
           var pc' := arr.l.get_thread_pc(s', other_tid);
           (pc' != pc ==> pc.None? && !arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v) && !arr.l.is_pc_nonyielding(pc'.v))
  }

  predicate PhasesPrecededByYielding<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, tid ::
      var s' := arr.l.path_next(s, path, tid);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.path_valid(s, path, tid)
      && pc'.Some?
      && (arr.is_phase1(pc'.v) || arr.is_phase2(pc'.v))
      && pc.Some?
      && (!arr.is_phase1(pc.v) && !arr.is_phase2(pc.v))
      ==> !arr.l.is_pc_nonyielding(pc.v)
  }

  predicate PhasesSucceededByYielding<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, tid ::
      var s' := arr.l.path_next(s, path, tid);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.path_valid(s, path, tid)
      && pc.Some?
      && (arr.is_phase1(pc.v) || arr.is_phase2(pc.v))
      && pc'.Some?
      && (!arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v))
      ==> !arr.l.is_pc_nonyielding(pc'.v)
  }

  predicate Phase2NotFollowedByPhase1<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, tid ::
      var s' := arr.l.path_next(s, path, tid);
      var pc := arr.l.get_thread_pc(s, tid);
      var pc' := arr.l.get_thread_pc(s', tid);
      && arr.l.path_valid(s, path, tid)
      && pc.Some?
      && arr.is_phase2(pc.v)
      && pc'.Some?
      && !arr.is_phase2(pc'.v)
      ==> !arr.is_phase1(pc'.v)
  }

  predicate RightMoversPreserveStateRefinement
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, tid :: arr.l.path_valid(s, path, tid) && !arr.l.path_type(path).AtomicPathType_Tau?
       ==> var s' := arr.l.path_next(s, path, tid);
           var pc' := arr.l.get_thread_pc(s', tid);
           (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
  }

  predicate LeftMoversPreserveStateRefinement
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, path, tid :: arr.l.path_valid(s, path, tid) && !arr.l.path_type(path).AtomicPathType_Tau?
       ==> var s' := arr.l.path_next(s, path, tid);
           var pc := arr.l.get_thread_pc(s, tid);
           (pc.Some? && arr.is_phase2(pc.v) ==> RefinementPair(s, s') in arr.self_relation)
  }

  predicate RightMoversCommuteConditions<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    initial_state:LState,
    right_mover:LPath,
    other_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
  {
    var other_tau := arr.l.path_type(other_path).AtomicPathType_Tau?;
    var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
    var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
    var pc := arr.l.get_thread_pc(state_after_right_mover, mover_tid);
    && arr.inv(initial_state)
    && !arr.l.path_type(right_mover).AtomicPathType_Tau?
    && arr.l.path_valid(initial_state, right_mover, mover_tid)
    && pc.Some?
    && arr.is_phase1(pc.v)
    && arr.l.path_valid(state_after_right_mover, other_path, other_tid)
    && arr.l.state_ok(state_after_both_paths)
    && (other_tau || other_tid != mover_tid)
  }

  predicate RightMoversCommute<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
      forall initial_state, right_mover, other_path, mover_tid, other_tid
        {:trigger RightMoversCommuteConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)}
        :: RightMoversCommuteConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)
        ==> var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
            var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
            var new_middle_state := arr.l.path_next(initial_state, other_path, other_tid);
            && arr.l.path_valid(initial_state, other_path, other_tid)
            && arr.l.path_valid(new_middle_state, right_mover, mover_tid)
            && state_after_both_paths == arr.l.path_next(new_middle_state, right_mover, mover_tid)
  }

  predicate LeftMoversCommuteConditions<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    initial_state:LState,
    other_path:LPath,
    left_mover:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
  {
    var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
    var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
    var pc := arr.l.get_thread_pc(state_after_other_path, mover_tid);
    && arr.inv(initial_state)
    && arr.l.path_valid(initial_state, other_path, other_tid)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && !arr.l.path_type(left_mover).AtomicPathType_Tau?
    && arr.l.path_valid(state_after_other_path, left_mover, mover_tid)
    && (arr.l.path_type(other_path).AtomicPathType_Tau? || other_tid != mover_tid)
    && arr.l.state_ok(state_after_both_paths)
  }

  predicate LeftMoversCommute<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall initial_state, other_path, left_mover, mover_tid, other_tid
      {:trigger LeftMoversCommuteConditions(arr, initial_state, other_path, left_mover, mover_tid, other_tid)}
      :: LeftMoversCommuteConditions(arr, initial_state, other_path, left_mover, mover_tid, other_tid)
        ==> var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
            var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
            var new_middle_state := arr.l.path_next(initial_state, left_mover, mover_tid);
            && arr.l.path_valid(initial_state, left_mover, mover_tid)
            && arr.l.path_valid(new_middle_state, other_path, other_tid)
            && state_after_both_paths == arr.l.path_next(new_middle_state, other_path, other_tid)
  }

  predicate LeftMoversAlwaysEnabledConditions
    <LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    s:LState,
    tid:Armada_ThreadHandle
    )
  {
    && arr.inv(s)
    && arr.l.state_ok(s)
    && arr.l.get_thread_pc(s, tid).Some?
    && arr.is_phase2(arr.l.get_thread_pc(s, tid).v)
  }

  predicate LeftMoversAlwaysEnabled<LState(!new), LPath, LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall s, tid
      {:trigger LeftMoversAlwaysEnabledConditions(arr, s, tid)}
      :: LeftMoversAlwaysEnabledConditions(arr, s, tid)
      ==> var path := arr.generate_left_mover(s, tid);
          && arr.l.path_valid(s, path, tid)
          && !arr.l.path_type(path).AtomicPathType_Tau?
          && var s' := arr.l.path_next(s, path, tid);
            0 <= arr.left_mover_generation_progress(s', tid) < arr.left_mover_generation_progress(s, tid)
  }

  predicate RightMoverCrashPreservationConditions
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    initial_state:LState,
    right_mover:LPath,
    other_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
  {
    var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
    var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
    var pc := arr.l.get_thread_pc(state_after_right_mover, mover_tid);
    var other_tau := arr.l.path_type(other_path).AtomicPathType_Tau?;
    && arr.inv(initial_state)
    && arr.l.path_valid(initial_state, right_mover, mover_tid)
    && arr.l.path_valid(state_after_right_mover, other_path, other_tid)
    && !arr.l.state_ok(state_after_both_paths)
    && !arr.l.path_type(right_mover).AtomicPathType_Tau?
    && pc.Some?
    && arr.is_phase1(pc.v)
    && (other_tau || other_tid != mover_tid)
  }
    
  predicate RightMoverCrashPreservation<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall initial_state, right_mover, other_path, mover_tid, other_tid
      {:trigger RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)}
      :: RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)
      ==> var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
          var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
          var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
          && arr.l.path_valid(initial_state, other_path, other_tid)
          && !arr.l.state_ok(state_after_other_path)
          && RefinementPair(state_after_both_paths, state_after_other_path) in arr.self_relation
  }

  predicate LeftMoverCrashPreservationConditions
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    initial_state:LState,
    left_mover:LPath,
    other_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
  {
    var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
    var pc := arr.l.get_thread_pc(initial_state, mover_tid);
    var other_tau := arr.l.path_type(other_path).AtomicPathType_Tau?;
    && arr.inv(initial_state)
    && !arr.l.path_type(left_mover).AtomicPathType_Tau?
    && arr.l.path_valid(initial_state, left_mover, mover_tid)
    && arr.l.path_valid(initial_state, other_path, other_tid)
    && arr.l.state_ok(initial_state)
    && !arr.l.state_ok(state_after_other_path)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && (other_tau || other_tid != mover_tid)
  }
  
  predicate LeftMoverCrashPreservation<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall initial_state, left_mover, other_path, mover_tid, other_tid
      {:trigger LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)}
      :: LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)
      ==> var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
          var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
          var state_after_both_paths := arr.l.path_next(state_after_left_mover, other_path, other_tid);
          && arr.l.path_valid(state_after_left_mover, other_path, other_tid)
          && !arr.l.state_ok(state_after_both_paths)
          && RefinementPair(state_after_other_path, state_after_both_paths) in arr.self_relation
  }

  predicate LeftMoverSelfCrashPreservationConditions
    <LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>,
    initial_state:LState,
    left_mover:LPath,
    other_path:LPath,
    mover_tid:Armada_ThreadHandle,
    other_tid:Armada_ThreadHandle
    )
  {
    var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
    var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
    var pc := arr.l.get_thread_pc(state_after_other_path, mover_tid);
    var other_tau := arr.l.path_type(other_path).AtomicPathType_Tau?;
    && arr.inv(initial_state)
    && !arr.l.path_type(left_mover).AtomicPathType_Tau?
    && arr.l.path_valid(initial_state, other_path, other_tid)
    && arr.l.path_valid(state_after_other_path, left_mover, mover_tid)
    && arr.l.state_ok(initial_state)
    && !arr.l.state_ok(state_after_both_paths)
    && pc.Some?
    && arr.is_phase2(pc.v)
    && (other_tau || other_tid != mover_tid)
  }
    
  predicate LeftMoverSelfCrashPreservation<LState(!new), LPath(!new), LPC, HState, HPath, HPC>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    forall initial_state, left_mover, other_path, mover_tid, other_tid
      {:trigger LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)}
      :: LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)
      ==> var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
          var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
          var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
          && arr.l.path_valid(initial_state, left_mover, mover_tid)
          && !arr.l.state_ok(state_after_left_mover)
          && RefinementPair(state_after_both_paths, state_after_left_mover) in arr.self_relation
  }

  predicate ValidAtomicReductionRequest<LState(!new), LPath(!new), LPC(!new), HState(!new), HPath(!new), HPC(!new)>(
    arr:AtomicReductionRequest<LState, LPath, LPC, HState, HPath, HPC>
    )
  {
    && RefinementRelationReflexive(arr.self_relation)
    && RefinementRelationTransitive(arr.self_relation)
    && RefinementRelationsConvolve(arr.self_relation, arr.relation, arr.relation)
    && LInitImpliesHInit(arr)
    && AtomicInitImpliesInv(arr.l, arr.inv)
    && AtomicPathPreservesInv(arr.l, arr.inv)
    && AtomicPathRequiresOK(arr.l)
    && AtomicInitImpliesYielding(arr.l)
    && AtomicInitImpliesOK(arr.l)
    && AtomicPathTypeAlwaysMatchesPCTypes(arr.l)
    && AtomicPathTypeAlwaysMatchesPCTypes(arr.h)
    && LStateToHStateMapsPCsCorrectly(arr)
    && LHYieldingCorrespondence(arr)
    && LHPathPropertiesMatch(arr)
    && LPathImpliesHPath(arr)
    && StateConversionPreservesOK(arr)
    && StateConversionSatisfiesRelation(arr)
    && ThreadsDontStartInAnyPhase(arr)
    && PhasesDontOverlap(arr)
    && PhasesPrecededByYielding(arr)
    && PhasesSucceededByYielding(arr)
    && Phase2NotFollowedByPhase1(arr)
    && AtomicSteppingThreadHasPC(arr.l)
    && AtomicTauLeavesPCUnchanged(arr.l)
    && ThreadCantAffectOtherThreadPhaseExceptViaFork(arr)
    && RightMoversPreserveStateRefinement(arr)
    && LeftMoversPreserveStateRefinement(arr)
    && RightMoversCommute(arr)
    && LeftMoversCommute(arr)
    && RightMoverCrashPreservation(arr)
    && LeftMoverCrashPreservation(arr)
    && LeftMoverSelfCrashPreservation(arr)
    && LeftMoversAlwaysEnabled(arr)
  }

}
