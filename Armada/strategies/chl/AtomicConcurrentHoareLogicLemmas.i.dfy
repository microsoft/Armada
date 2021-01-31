include "../../util/option.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../../util/collections/seqs.i.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../generic/GenericArmadaLemmas.i.dfy"
include "../generic/LiftAtomicToAtomic.i.dfy"
include "ConcurrentHoareLogic.i.dfy"
include "AtomicConcurrentHoareLogicSpec.i.dfy"

module AtomicConcurrentHoareLogicLemmasModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaCommonDefinitions
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened GenericArmadaAtomicModule
  import opened LiftAtomicToAtomicModule
  import opened ConcurrentHoareLogicSpecModule
  import opened ConcurrentHoareLogicLemmasModule
  import opened ConcurrentHoareLogicModule
  import opened AtomicConcurrentHoareLogicSpecModule

  function ExtractInv<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    ) : LState->bool
  {
    s => s in AnnotatedReachables(ar.cr.spec)
  }

  function ExtractLiftingRelation<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    ) : (LState, HState)->bool
  {
    (ls, hs) => hs == ar.lstate_to_hstate(ls)
  }

  lemma lemma_EstablishInitRequirements<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>,
    inv:LState->bool,
    relation:(LState, HState)->bool
    )
    requires IsValidAtomicConcurrentHoareLogicRequest(ar)
    requires inv == ExtractInv(ar)
    requires relation == ExtractLiftingRelation(ar)
    ensures  AtomicInitImpliesInv(ar.l, inv)
    ensures  forall ls :: ar.l.init(ls) ==> exists hs :: ar.h.init(hs) && relation(ls, hs)
  {
    forall ls | ar.l.init(ls)
      ensures inv(ls)
      ensures exists hs :: ar.h.init(hs) && relation(ls, hs)
    {
      lemma_InitStateInAnnotatedReachables(ls, ar.cr.spec);
      var hs := ar.lstate_to_hstate(ls);
      assert ar.h.init(hs) && relation(ls, hs);
    }
  }

  lemma lemma_EstablishAtomicPathsLiftable<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>,
    inv:LState->bool,
    relation:(LState, HState)->bool
    )
    requires IsValidAtomicConcurrentHoareLogicRequest(ar)
    requires inv == ExtractInv(ar)
    requires relation == ExtractLiftingRelation(ar)
    ensures  forall ls, lpath, tid, hs ::
               inv(ls) && relation(ls, hs) && ar.l.path_valid(ls, lpath, tid)
             ==> exists hpath :: LiftAtomicPathSuccessful(ar.l, ar.h, inv, relation, ls, lpath, tid, hs, hpath)
  {
    forall ls, lpath, tid, hs | inv(ls) && relation(ls, hs) && ar.l.path_valid(ls, lpath, tid)
      ensures exists hpath :: LiftAtomicPathSuccessful(ar.l, ar.h, inv, relation, ls, lpath, tid, hs, hpath)
    {
      assert ls in AnnotatedReachables(ar.cr.spec);
      var lb :| AnnotatedBehaviorSatisfiesSpec(lb, ar.cr.spec) && last(lb.states) == ls;

      var ls' := ar.l.path_next(ls, lpath, tid);

      var lpath_and_tid := PathAndTid(lpath, tid);
      lemma_ExtendStateNextSeqRight(lb.states, lb.trace, ar.cr.spec.next, ls', lpath_and_tid);
      var lb' := AnnotatedBehavior(lb.states + [ls'], lb.trace + [lpath_and_tid]);

      var pos := |lb.trace|;
      assert AnnotatedBehaviorSatisfiesSpec(lb', ar.cr.spec);
      assert lb'.states[pos] == ls;
      assert lb'.states[pos + 1] == ls';
      assert lb'.trace[pos] == lpath_and_tid;

      lemma_InvariantPredicateHoldsAtStep(lb', pos, ar.cr.spec, ar.cr.established_inv);

      var hpath := ar.lpath_to_hpath(lpath);
      assert CorrectCHLStepEffect(ar.cr, ls, ls', lpath_and_tid);
      assert ar.cr.state_ok(ls);
      lemma_CHLGlobalInvariantHoldsWhenActorPresent(ar.cr, lb', pos, tid);
      if !ar.l.path_type(lpath).AtomicPathType_Tau? {
        lemma_CHLLocalInvariantHoldsWhenActorAboutToStep(ar.cr, lb', pos, tid);
      }
      assert LPathImpliesHPathConditions(ar, ls, lpath, tid);
      assert LiftAtomicPathSuccessful(ar.l, ar.h, inv, relation, ls, lpath, tid, hs, hpath);
    }
  }

}
