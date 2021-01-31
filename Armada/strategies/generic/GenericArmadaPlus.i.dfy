include "GenericArmadaSpec.i.dfy"
include "GenericArmadaLemmas.i.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"

module GenericArmadaPlusModule
{
  import opened util_collections_seqs_s
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened GenericArmadaLemmasModule

  predicate InitsMatch<LState(!new), HState(!new), OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && ls == convert(hs)
  }

  predicate NextsMatch<LState(!new), HState(!new), OneStep(!new), PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall ls, hs, step, tid :: lasf.step_valid(ls, step, tid) && ls == convert(hs)
      ==> hasf.step_valid(hs, step, tid) && lasf.step_next(ls, step, tid) == convert(hasf.step_next(hs, step, tid))
  }

  predicate TausMatch<LState, HState, OneStep(!new), PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall step :: lasf.is_step_tau(step) <==> hasf.is_step_tau(step)
  }

  predicate ThreadPCsMatch<LState(!new), HState(!new), OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall ls, hs, tid :: ls == convert(hs) ==> lasf.get_thread_pc(ls, tid) == hasf.get_thread_pc(hs, tid)
  }

  predicate NonyieldingPCsMatch<LState, HState, OneStep, PC(!new)>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall pc :: lasf.is_pc_nonyielding(pc) <==> hasf.is_pc_nonyielding(pc)
  }

  predicate StateOKsMatch<LState(!new), HState(!new), OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    forall ls, hs :: ls == convert(hs) ==> lasf.state_ok(ls) == hasf.state_ok(hs)
  }

  predicate RequirementsForSpecRefinesPlusSpec<LState, HState, OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    )
  {
    && InitsMatch(lasf, hasf, convert)
    && NextsMatch(lasf, hasf, convert)
    && TausMatch(lasf, hasf, convert)
    && ThreadPCsMatch(lasf, hasf, convert)
    && NonyieldingPCsMatch(lasf, hasf, convert)
    && StateOKsMatch(lasf, hasf, convert)
  }

  lemma lemma_LiftStepsStartNonyielding<LState, HState, OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState,
    ls: LState,
    ls': LState,
    hs: HState,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    ) returns (
    hs': HState
    )
    requires RequirementsForSpecRefinesPlusSpec(lasf, hasf, convert)
    requires Armada_NextMultipleSteps(lasf, ls, ls', steps, tid)
    requires Armada_StepsStartNonyielding(lasf, ls, ls', steps, tid)
    requires ls == convert(hs)
    ensures  Armada_NextMultipleSteps(hasf, hs, hs', steps, tid)
    ensures  Armada_StepsStartNonyielding(hasf, hs, hs', steps, tid)
    ensures  ls' == convert(hs')
  {
    if |steps| == 0 {
      hs' := hs;
      return;
    }

    var step := steps[0];
    var ls_next := lasf.step_next(ls, step, tid);
    var hs_next := hasf.step_next(hs, step, tid);
    hs' := lemma_LiftStepsStartNonyielding(lasf, hasf, convert, ls_next, ls', hs_next, steps[1..], tid);
  }

  lemma lemma_LiftMultistep<LState, HState, OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState,
    ls: LState,
    ls': LState,
    hs: HState,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle,
    tau: bool
    ) returns (
    hs': HState
    )
    requires RequirementsForSpecRefinesPlusSpec(lasf, hasf, convert)
    requires Armada_NextMultistep(lasf, ls, ls', steps, tid, tau)
    requires ls == convert(hs)
    ensures  Armada_NextMultistep(hasf, hs, hs', steps, tid, tau)
    ensures  ls' == convert(hs')
  {
    if |steps| == 0 {
      hs' := hs;
      return;
    }

    var step := steps[0];
    var ls_next := lasf.step_next(ls, step, tid);
    var hs_next := hasf.step_next(hs, step, tid);

    if tau {
      hs' := hs_next;
      assert Armada_NextMultipleSteps(lasf, ls_next, ls', steps[1..], tid);
    }
    else {
      hs' := lemma_LiftStepsStartNonyielding(lasf, hasf, convert, ls_next, ls', hs_next, steps[1..], tid);
    }
  }

  lemma lemma_LiftBehavior<LState, HState, OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState,
    refinement_relation: RefinementRelation<LState, HState>,
    lb: seq<LState>
    ) returns (
    hb: seq<HState>
    )
    requires RequirementsForSpecRefinesPlusSpec(lasf, hasf, convert)
    requires BehaviorSatisfiesSpec(lb, Armada_SpecFunctionsToSpec(lasf))
    requires refinement_relation == iset ls, hs | ls == convert(hs) :: RefinementPair(ls, hs)
    ensures  BehaviorRefinesBehavior(lb, hb, refinement_relation)
    ensures  BehaviorSatisfiesSpec(hb, Armada_SpecFunctionsToSpec(hasf))
  {
    assert lasf.init(lb[0]);
    var hs0 :| hasf.init(hs0) && lb[0] == convert(hs0);
    hb := [hs0];
    var pos := 0;
    var lspec := Armada_SpecFunctionsToSpec(lasf);
    var hspec := Armada_SpecFunctionsToSpec(hasf);

    assert BehaviorRefinesBehaviorUsingRefinementMap(lb[..pos+1], hb, refinement_relation, [RefinementRange(0, 0)]);
    assert BehaviorRefinesBehavior(lb[..pos+1], hb, refinement_relation);

    while pos + 1 < |lb|
      invariant |hb| == pos + 1
      invariant pos < |lb|
      invariant BehaviorRefinesBehavior(lb[..pos+1], hb, refinement_relation)
      invariant BehaviorSatisfiesSpec(hb, hspec)
    {
      var ls := lb[pos];
      var ls' := lb[pos+1];
      var hs := hb[pos];
      assert RefinementPair(ls, hs) in refinement_relation;
      assert StatePair(ls, ls') in lspec.next;
      var steps, tid, tau :| Armada_NextMultistep(lasf, ls, ls', steps, tid, tau);
      var hs' := lemma_LiftMultistep(lasf, hasf, convert, ls, ls', hs, steps, tid, tau);
      assert Armada_NextMultistep(hasf, hs, hs', steps, tid, tau);
      assert StatePair(hs, hs') in hspec.next;
      lemma_ExtendBehaviorRefinesBehaviorRightOne_LH(lb[..pos+1], hb, refinement_relation, ls', hs');
      lemma_ExtendBehaviorSatisfiesSpecRightOne(hb, hspec, hs');
      assert lb[..(pos+1)+1] == lb[..pos+1] + [ls'];
      pos := pos + 1;
      hb := hb + [hs'];
    }

    assert lb[..pos+1] == lb;
  }

  lemma lemma_SpecRefinesPlusSpec<LState, HState, OneStep, PC>(
    lasf: Armada_SpecFunctions<LState, OneStep, PC>,
    hasf: Armada_SpecFunctions<HState, OneStep, PC>,
    convert: HState->LState
    ) returns (
    refinement_relation: RefinementRelation<LState, HState>
    )
    requires RequirementsForSpecRefinesPlusSpec(lasf, hasf, convert)
    ensures  SpecRefinesSpec(Armada_SpecFunctionsToSpec(lasf), Armada_SpecFunctionsToSpec(hasf), refinement_relation)
    ensures  refinement_relation == iset ls, hs | ls == convert(hs) :: RefinementPair(ls, hs)
  {
    refinement_relation := iset ls, hs | ls == convert(hs) :: RefinementPair(ls, hs);
    var hspec := Armada_SpecFunctionsToSpec(hasf);
    forall lb | BehaviorSatisfiesSpec(lb, Armada_SpecFunctionsToSpec(lasf))
      ensures exists hb :: BehaviorRefinesBehavior(lb, hb, refinement_relation) && BehaviorSatisfiesSpec(hb, hspec)
    {
      var hb := lemma_LiftBehavior(lasf, hasf, convert, refinement_relation, lb);
      assert BehaviorRefinesBehavior(lb, hb, refinement_relation) && BehaviorSatisfiesSpec(hb, hspec);
    }
  }
}
