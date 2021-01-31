include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../generic/GenericArmadaAtomic.i.dfy"
include "ConcurrentHoareLogicSpec.i.dfy"

module AtomicConcurrentHoareLogicSpecModule {

  import opened util_option_s
  import opened GeneralRefinementModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaCommonDefinitions
  import opened GenericArmadaSpecModule
  import opened GenericArmadaAtomicModule
  import opened ConcurrentHoareLogicSpecModule

  datatype PathAndTid<Path> = PathAndTid(path: Path, tid: Armada_ThreadHandle)

  datatype AtomicConcurrentHoareLogicRequest<!LState, !LPath(==), !LPC, !LProc, !HState, !HPath, !HPC> =
    AtomicConcurrentHoareLogicRequest(
      cr:ConcurrentHoareLogicRequest<LState, Armada_ThreadHandle, PathAndTid<LPath>, LPC, LProc>,
      l:AtomicSpecFunctions<LState, LPath, LPC>,
      h:AtomicSpecFunctions<HState, HPath, HPC>,
      relation:RefinementRelation<LState, HState>,
      lstate_to_hstate:LState->HState,
      lpath_to_hpath:LPath->HPath,
      lpc_to_hpc:LPC->HPC
      )

  predicate LInitImpliesHInit<LState(!new), LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall ls :: ar.l.init(ls) ==> ar.h.init(ar.lstate_to_hstate(ls))
  }

  predicate LStateToHStateMapsPCsCorrectly<LState(!new), LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall ls, tid :: var hs := ar.lstate_to_hstate(ls);
                var lpc := ar.l.get_thread_pc(ls, tid);
                var hpc := ar.h.get_thread_pc(hs, tid);
                hpc == if lpc.Some? then Some(ar.lpc_to_hpc(lpc.v)) else None()
  }

  predicate LHPathPropertiesMatch<LState(!new), LPath(!new), LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall lpath :: var hpath := ar.lpath_to_hpath(lpath);
              ar.l.path_type(lpath) == ar.h.path_type(hpath)
  }

  predicate LPathImpliesHPathConditions<LState(!new), LPath(!new), LPC, LProc, HState, HPath, HPC>(
    ar: AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>,
    ls: LState,
    lpath: LPath,
    tid: Armada_ThreadHandle
    )
  {
    && ar.l.path_valid(ls, lpath, tid)
    && ar.cr.established_inv(ls)
    && (!ar.l.path_type(lpath).AtomicPathType_Tau? ==> ar.cr.local_inv(ls, tid))
    && ar.cr.global_inv(ls)
  }

  predicate LPathImpliesHPath<LState(!new), LPath(!new), LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall ls, lpath, tid {:trigger LPathImpliesHPathConditions(ar, ls, lpath, tid)} :: LPathImpliesHPathConditions(ar, ls, lpath, tid) ==>
      var ls' := ar.l.path_next(ls, lpath, tid);
      var hs := ar.lstate_to_hstate(ls);
      var hpath := ar.lpath_to_hpath(lpath);
      var hs' := ar.lstate_to_hstate(ls');
      && ar.h.path_valid(hs, hpath, tid)
      && hs' == ar.h.path_next(hs, hpath, tid)
  }

  predicate StateConversionPreservesOK<LState(!new), LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall ls :: ar.h.state_ok(ar.lstate_to_hstate(ls)) == ar.l.state_ok(ls)
  }

  predicate StateConversionSatisfiesRelation<LState(!new), LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    forall ls :: RefinementPair(ls, ar.lstate_to_hstate(ls)) in ar.relation
  }

  predicate EmbeddedRequestCorresponds<LState(!new), LPath(!new), LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    && (forall s :: ar.l.init(s) <==> s in ar.cr.spec.init)
    && (forall s :: ar.l.state_ok(s) <==> ar.cr.state_ok(s))
    && (forall s, s', path, tid :: ActionTuple(s, s', PathAndTid(path, tid)) in ar.cr.spec.next <==>
                            ar.l.path_valid(s, path, tid) && s' == ar.l.path_next(s, path, tid))
    && (forall path, tid :: ar.cr.step_to_actor(PathAndTid(path, tid)) ==
                     if ar.l.path_type(path).AtomicPathType_Tau? then None else Some(tid))
    && (forall s, tid :: ar.cr.get_actor_pc_stack(s, tid).Some? <==> ar.l.get_thread_pc(s, tid).Some?)
  }

  predicate IsValidAtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
  {
    && IsValidConcurrentHoareLogicRequest(ar.cr)
    && LPathImpliesHPath(ar)
    && EmbeddedRequestCorresponds(ar)
    && AtomicInitImpliesOK(ar.l)
    && AtomicPathRequiresOK(ar.l)
    && AtomicSteppingThreadHasPC(ar.l)
    && AtomicTauLeavesPCUnchanged(ar.l)
    && AtomicThreadCantAffectOtherThreadPCExceptViaFork(ar.l)
    && LInitImpliesHInit(ar)
    && LStateToHStateMapsPCsCorrectly(ar)
    && LHPathPropertiesMatch(ar)
    && StateConversionPreservesOK(ar)
    && StateConversionSatisfiesRelation(ar)
  }

}
