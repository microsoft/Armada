include "GenericArmadaSpec.i.dfy"
include "GenericArmadaLemmas.i.dfy"
include "../../spec/refinement.s.dfy" 
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../invariants.i.dfy"
include "../../util/collections/seqs.s.dfy"

module GenericArmadaRefinementModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened AnnotatedBehaviorModule
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened InvariantsModule
  import opened ArmadaCommonDefinitions

  predicate Armada_NextPrefix<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && Armada_NextMultipleSteps(asf, s, s', steps)
    && (forall step {:trigger asf.step_to_thread(step)} :: step in steps ==> asf.step_to_thread(step) == tid)
    && (forall step {:trigger asf.is_step_tau(step)} :: step in steps ==> asf.is_step_tau(step) == tau)
    && if tau then |steps| <= 1 else |steps| > 0 ==> (
        && Armada_ThreadYielding(asf, s, tid)
        && (forall i :: 0 < i < |steps| ==> !Armada_ThreadYielding(asf, Armada_GetStateSequence(asf, s, steps)[i], tid))
      )
  }

  predicate MultistepPreservesInv<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool
    )
  {
    forall s, s', multistep :: ActionTuple(s, s', multistep) in SpecFunctionsToSpec(asf).next && inv(s) ==> inv(s')
  }

  predicate MultistepPreservesDependentInv<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    established_inv:State->bool,
    dependent_inv:State->bool
    )
  {
    forall s, s', multistep :: ActionTuple(s, s', multistep) in SpecFunctionsToSpec(asf).next && established_inv(s) && dependent_inv(s)
                         ==> dependent_inv(s')
  }

  function Armada_ApplyMultistep<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    multistep:Armada_Multistep<OneStep>
    ) : State
  {
    last(Armada_GetStateSequence(asf, s, multistep.steps))
  }

  predicate Armada_ValidMultistep<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    multistep:Armada_Multistep<OneStep>
    )
  {
    var steps := multistep.steps;
    var states := Armada_GetStateSequence(asf, s, steps);
    var s' := last(states);
    Armada_NextMultistep(asf, s, s', steps, multistep.tid, multistep.tau)
  }

  predicate HMultistepContinuesRefinement<LState(!new), HState(!new), HOneStep(!new), HPC>(
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    refinement_relation:(LState, HState)->bool,
    ls':LState,
    hs:HState,
    hmultistep:Armada_Multistep<HOneStep>
    )
  {
    var hs' := Armada_ApplyMultistep(hasf, hs, hmultistep);
    Armada_NextMultistep(hasf, hs, hs', hmultistep.steps, hmultistep.tid, hmultistep.tau) && refinement_relation(ls', hs')
  }

  predicate PreconditionsForGenericArmadaRefinement<LState(!new), LOneStep(!new), LPC, HState(!new), HOneStep(!new), HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool
    )
  {
    && (forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && refinement_relation(ls, hs))
    && (forall ls, hs :: refinement_relation(ls, hs) ==> RefinementPair(ls, hs) in relation)
    && (forall ls, ls', lmultistep, hs
         {:trigger ActionTuple(ls, ls', lmultistep) in SpecFunctionsToSpec(lasf).next, refinement_relation(ls, hs)} ::
         && var lspec := SpecFunctionsToSpec(lasf);
         && ls in AnnotatedReachables(lspec)
         && ActionTuple(ls, ls', lmultistep) in lspec.next
         && refinement_relation(ls, hs) ==>
         exists hmultistep:Armada_Multistep<HOneStep> ::
           HMultistepContinuesRefinement(hasf, refinement_relation, ls', hs, hmultistep))
  }

  predicate HStepContinuesRefinement<LState(!new), HState(!new), HOneStep(!new), HPC>(
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    refinement_relation:(LState, HState)->bool,
    ls':LState,
    hs:HState,
    tid:Armada_ThreadHandle,
    tau:bool,
    hstep:HOneStep
    )
  {
    var hs' := hasf.step_next(hs, hstep);
    && hasf.step_to_thread(hstep) == tid
    && hasf.is_step_tau(hstep) == tau
    && hasf.step_valid(hs, hstep)
    && refinement_relation(ls', hs')
  }

  predicate PreconditionsForGenericStepwiseRefinementConditions<LState(!new), LOneStep(!new), LPC, HState(!new), HOneStep(!new), HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    refinement_relation:(LState, HState)->bool,
    ls:LState,
    ls':LState,
    ls'':LState,
    lsteps:seq<LOneStep>,
    lstep:LOneStep,
    hs:HState,
    hs':HState,
    hsteps:seq<HOneStep>,
    tid:Armada_ThreadHandle,
    tau:bool
    )
  {
    && ls in AnnotatedReachables(SpecFunctionsToSpec(lasf))
    && Armada_NextPrefix(lasf, ls, ls', lsteps, tid, tau)
    && Armada_NextPrefix(hasf, hs, hs', hsteps, tid, tau)
    && lasf.step_valid(ls', lstep)
    && ls'' == lasf.step_next(ls', lstep)
    && refinement_relation(ls, hs)
    && refinement_relation(ls', hs')
  }

  predicate PreconditionsForGenericStepwiseRefinement<LState(!new), LOneStep(!new), LPC, HState(!new), HOneStep(!new), HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool
    )
  {
    && (forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && refinement_relation(ls, hs))
    && (forall ls, hs :: refinement_relation(ls, hs) ==> RefinementPair(ls, hs) in relation)
    && (forall ls, hs :: refinement_relation(ls, hs) ==> lasf.state_ok(ls) == hasf.state_ok(hs))
    && (forall ls, hs, tid :: refinement_relation(ls, hs) ==> Armada_ThreadYielding(lasf, ls, tid) == Armada_ThreadYielding(hasf, hs, tid))
    && (forall ls, ls', ls'', lsteps, lstep, hs, hs', hsteps, tid, tau
         {:trigger PreconditionsForGenericStepwiseRefinementConditions(lasf, hasf, refinement_relation,
                                                                       ls, ls', ls'', lsteps, lstep, hs, hs', hsteps, tid, tau)} ::
         PreconditionsForGenericStepwiseRefinementConditions(lasf, hasf, refinement_relation,
                                                             ls, ls', ls'', lsteps, lstep, hs, hs', hsteps, tid, tau)
         ==> exists hstep:HOneStep :: HStepContinuesRefinement(hasf, refinement_relation, ls'', hs', tid, tau, hstep))
  }

  predicate AnnotatedBehaviorSpecRefinesAnnotatedBehaviorSpec<LState(!new), LStep(!new), HState(!new), HStep(!new)>(
    lspec:AnnotatedBehaviorSpec<LState, LStep>,
    hspec:AnnotatedBehaviorSpec<HState, HStep>,
    relation:RefinementRelation<LState, HState>
    )
  {
    forall lb :: AnnotatedBehaviorSatisfiesSpec(lb, lspec) ==>
           exists hb :: AnnotatedBehaviorSatisfiesSpec(hb, hspec) && BehaviorRefinesBehavior(lb.states, hb.states, relation)
  }

  lemma lemma_EquivalenceOfArmadaNextMultipleSteps<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>
    )
    requires states == Armada_GetStateSequence(asf, s, steps)
    ensures  Armada_NextMultipleSteps(asf, s, s', steps) <==>
               (s' == last(states) &&
                forall i :: 0 <= i < |steps| ==> asf.step_valid(states[i], steps[i]) && states[i+1] == asf.step_next(states[i], steps[i]))
  {
    if |steps| > 0 {
      var s_next := asf.step_next(s, steps[0]);
      lemma_EquivalenceOfArmadaNextMultipleSteps(asf, s_next, s', steps[1..], states[1..]);
    }
  }

  lemma lemma_EquivalenceOfArmadaGetStateSequence<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    steps:seq<OneStep>,
    states:seq<State>
    )
    ensures states == Armada_GetStateSequence(asf, s, steps) <==>
            |states| == |steps| + 1 && states[0] == s && forall i :: 0 <= i < |steps| ==> states[i+1] == asf.step_next(states[i], steps[i])
  {
    if |states| == |steps| + 1 && states[0] == s && forall i :: 0 <= i < |steps| ==> states[i+1] == asf.step_next(states[i], steps[i]) {
      if |steps| > 0 {
        var s_next := asf.step_next(states[0], steps[0]);
        lemma_EquivalenceOfArmadaGetStateSequence(asf, s_next, steps[1..], states[1..]);
      }
    }
    if states == Armada_GetStateSequence(asf, s, steps) {
      forall i | 0 <= i < |steps|
        ensures states[i+1] == asf.step_next(states[i], steps[i])
      {
        lemma_ArmadaGetStateSequenceOnePos(asf, s, steps, i);
      }
    }
  }

  lemma lemma_EquivalenceOfArmadaStateSequenceProperties<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
    ensures  forall s, steps, states {:trigger states == Armada_GetStateSequence(asf, s, steps)} ::
               states == Armada_GetStateSequence(asf, s, steps) <==>
               (|states| == |steps| + 1 && states[0] == s && forall i :: 0 <= i < |steps| ==> states[i+1] == asf.step_next(states[i], steps[i]))
    ensures  forall s, s', steps {:trigger Armada_NextMultipleSteps(asf, s, s', steps)} ::
               var states := Armada_GetStateSequence(asf, s, steps);
               (Armada_NextMultipleSteps(asf, s, s', steps) <==>
                 (s' == last(states) &&
                  forall i :: 0 <= i < |steps| ==> asf.step_valid(states[i], steps[i]) && states[i+1] == asf.step_next(states[i], steps[i])))
  {
    forall s, steps, states {:trigger states == Armada_GetStateSequence(asf, s, steps)}
      ensures states == Armada_GetStateSequence(asf, s, steps) <==>
              (|states| == |steps| + 1 && states[0] == s && forall i :: 0 <= i < |steps| ==> states[i+1] == asf.step_next(states[i], steps[i]))
    {
      lemma_EquivalenceOfArmadaGetStateSequence(asf, s, steps, states);
    }
    forall s, s', steps {:trigger Armada_NextMultipleSteps(asf, s, s', steps)}
      ensures var states := Armada_GetStateSequence(asf, s, steps);
              Armada_NextMultipleSteps(asf, s, s', steps) <==>
                (s' == last(states) &&
                 forall i :: 0 <= i < |steps| ==> asf.step_valid(states[i], steps[i]) && states[i+1] == asf.step_next(states[i], steps[i]))
    {
      var states := Armada_GetStateSequence(asf, s, steps);
      lemma_EquivalenceOfArmadaNextMultipleSteps(asf, s, s', steps, states);
    }
  }

  lemma lemma_DropNextMultipleSteps
    <State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    s:State,
    s':State,
    steps:seq<OneStep>,
    states:seq<State>
    )
    requires |steps| > 0
    requires Armada_NextMultipleSteps(asf, s, s', steps)
    requires states == Armada_GetStateSequence(asf, s, steps)
    ensures  all_but_last(states) == Armada_GetStateSequence(asf, s, all_but_last(steps))
    ensures  Armada_NextMultipleSteps(asf, s, states[|states|-2], all_but_last(steps))
  {
    lemma_EquivalenceOfArmadaStateSequenceProperties(asf);
  }

  lemma lemma_InvariantHoldsAtBehaviorPos<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    b:AnnotatedBehavior<State, Armada_Multistep<OneStep>>,
    inv:State->bool,
    pos:int
    )
    requires InitImpliesInv(asf, inv)
    requires MultistepPreservesInv(asf, inv)
    requires AnnotatedBehaviorSatisfiesSpec(b, SpecFunctionsToSpec(asf))
    requires 0 <= pos < |b.states|
    ensures  inv(b.states[pos])
  {
    if pos > 0 {
      var prev := pos-1;
      assert ActionTuple(b.states[prev], b.states[prev+1], b.trace[prev]) in SpecFunctionsToSpec(asf).next;
      lemma_InvariantHoldsAtBehaviorPos(asf, b, inv, prev);
    }
  }

  lemma lemma_EstablishArmadaInvariantPredicatePure<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool
    )
    requires InitImpliesInv(asf, inv)
    requires MultistepPreservesInv(asf, inv)
    ensures  IsInvariantPredicateOfSpec(inv, SpecFunctionsToSpec(asf))
  {
    lemma_EstablishInvariantPredicatePure(inv, SpecFunctionsToSpec(asf));
  }

  lemma lemma_EstablishArmadaInvariantPredicateUsingPredicate<State, OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    established_inv:State->bool,
    dependent_inv:State->bool
    )
    requires IsInvariantPredicateOfSpec(established_inv, SpecFunctionsToSpec(asf))
    requires InitImpliesInv(asf, dependent_inv)
    requires MultistepPreservesDependentInv(asf, established_inv, dependent_inv)
    ensures  IsInvariantPredicateOfSpec(dependent_inv, SpecFunctionsToSpec(asf))
  {
    lemma_EstablishInvariantPredicateUsingInvariantPredicate(dependent_inv, established_inv, SpecFunctionsToSpec(asf));
  }

  lemma lemma_GenericArmadaRefinementConstructive<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool,
    lb:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>
    ) returns (
    hb:AnnotatedBehavior<HState, Armada_Multistep<HOneStep>>
    )
    requires PreconditionsForGenericArmadaRefinement(lasf, hasf, relation, refinement_relation)
    requires AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(lasf))
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, relation)
    ensures  refinement_relation(last(lb.states), last(hb.states))
    decreases |lb.states|
  {
    var lspec := SpecFunctionsToSpec(lasf);
    var hspec := SpecFunctionsToSpec(hasf);

    if |lb.trace| == 0 {
      var ls := lb.states[0];
      assert lasf.init(ls);
      lemma_StateInAnnotatedBehaviorInAnnotatedReachables(lspec, lb, 0);
      var hs :| hasf.init(hs) && refinement_relation(ls, hs);
      hb := AnnotatedBehavior([hs], []);
      var lh_map := [RefinementRange(0, 0)];
      assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, relation, lh_map);
    }
    else {
      var pos := |lb.trace|-1;
      var lb_prev := AnnotatedBehavior(lb.states[..pos+1], lb.trace[..pos]);
      assert lb.states[pos+1] == last(lb.states);
      assert lb.states == lb_prev.states + [last(lb.states)];
      lemma_TakeStateNextSeq(lb.states, lb.trace, lspec.next, pos);
      var hb_prev := lemma_GenericArmadaRefinementConstructive(lasf, hasf, relation, refinement_relation, lb_prev);

      lemma_StateInAnnotatedBehaviorInAnnotatedReachables(lspec, lb, pos);
      var hs := last(hb_prev.states);
      assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in lspec.next;
      assert refinement_relation(lb.states[pos], hs);
      var hmultistep :| HMultistepContinuesRefinement(hasf, refinement_relation, lb.states[pos+1], hs, hmultistep);

      var hs' := Armada_ApplyMultistep(hasf, hs, hmultistep);
      assert refinement_relation(lb.states[pos+1], hs');
      hb := AnnotatedBehavior(hb_prev.states + [hs'], hb_prev.trace + [hmultistep]);
      assert last(hb.states) == hs';
      lemma_ExtendBehaviorRefinesBehaviorRightOne_LH(lb_prev.states, hb_prev.states, relation, last(lb.states), hs');
      lemma_ExtendStateNextSeqRight(hb_prev.states, hb_prev.trace, hspec.next, hs', hmultistep);
    }
  }

  lemma lemma_GetStepwiseMultistep<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool,
    ls:LState,
    ls':LState,
    lsteps:seq<LOneStep>,
    tid:Armada_ThreadHandle,
    tau:bool,
    hs:HState
    ) returns (
    hsteps:seq<HOneStep>,
    hs':HState
    )
    requires PreconditionsForGenericStepwiseRefinement(lasf, hasf, relation, refinement_relation)
    requires ls in AnnotatedReachables(SpecFunctionsToSpec(lasf))
    requires refinement_relation(ls, hs)
    requires Armada_NextPrefix(lasf, ls, ls', lsteps, tid, tau)
    ensures  Armada_NextPrefix(hasf, hs, hs', hsteps, tid, tau)
    ensures  hs' == Armada_ApplyMultistep(hasf, hs, Armada_Multistep(hsteps, tid, tau))
    ensures  refinement_relation(ls', hs')
  {
    if |lsteps| == 0 {
      hsteps := [];
      hs' := hs;
      return;
    }

    lemma_EquivalenceOfArmadaStateSequenceProperties(lasf);
    lemma_EquivalenceOfArmadaStateSequenceProperties(hasf);

    var lstates := Armada_GetStateSequence(lasf, ls, lsteps);
    var lstep := last(lsteps);

    if |lsteps| == 1 {
      assert PreconditionsForGenericStepwiseRefinementConditions(lasf, hasf, refinement_relation, ls, ls, ls', [],
                                                                 lsteps[0], hs, hs, [], tid, tau);
      var hstep :| HStepContinuesRefinement(hasf, refinement_relation, ls', hs, tid, tau, hstep);
      hsteps := [hstep];
      hs' := Armada_ApplyMultistep(hasf, hs, Armada_Multistep(hsteps, tid, tau));
      return;
    }

    var pos := |lstates|-2;
    var ls_mid := lstates[pos];
    lemma_DropNextMultipleSteps(lasf, ls, ls', lsteps, lstates);
    var hsteps_mid, hs_mid := lemma_GetStepwiseMultistep(lasf, hasf, relation, refinement_relation, ls, ls_mid,
                                                         all_but_last(lsteps), tid, tau, hs);
    var hstates_mid := Armada_GetStateSequence(hasf, hs, hsteps_mid);
    assert PreconditionsForGenericStepwiseRefinementConditions(lasf, hasf, refinement_relation, ls, ls_mid, ls',
                                                               all_but_last(lsteps), lstep, hs, hs_mid, hsteps_mid, tid, tau);
    var hstep :| HStepContinuesRefinement(hasf, refinement_relation, ls', hs_mid, tid, tau, hstep);
    hs' := hasf.step_next(hs_mid, hstep);
    hsteps := hsteps_mid + [hstep];
    var hstates := hstates_mid + [hs'];

    assert hstates == Armada_GetStateSequence(hasf, hs, hsteps);
  }

  lemma lemma_GenericStepwiseRefinementConstructive<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool,
    lb:AnnotatedBehavior<LState, Armada_Multistep<LOneStep>>
    ) returns (
    hb:AnnotatedBehavior<HState, Armada_Multistep<HOneStep>>
    )
    requires PreconditionsForGenericStepwiseRefinement(lasf, hasf, relation, refinement_relation)
    requires AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(lasf))
    ensures  AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
    ensures  BehaviorRefinesBehavior(lb.states, hb.states, relation)
    ensures  refinement_relation(last(lb.states), last(hb.states))
    decreases |lb.states|
  {
    var lspec := SpecFunctionsToSpec(lasf);

    if |lb.trace| == 0 {
      var ls := lb.states[0];
      assert lasf.init(ls);
      lemma_StateInAnnotatedBehaviorInAnnotatedReachables(lspec, lb, 0);
      var hs :| hasf.init(hs) && refinement_relation(ls, hs);
      hb := AnnotatedBehavior([hs], []);
      var lh_map := [RefinementRange(0, 0)];
      assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, relation, lh_map);
      lemma_InitStateInAnnotatedReachables(lb.states[0], lspec);
    }
    else {
      var pos := |lb.trace|-1;
      var lb_prev := AnnotatedBehavior(lb.states[..pos+1], lb.trace[..pos]);
      lemma_TakeStateNextSeq(lb.states, lb.trace, lspec.next, pos);
      var hb_prev := lemma_GenericStepwiseRefinementConstructive(lasf, hasf, relation, refinement_relation, lb_prev);

      lemma_StateInAnnotatedBehaviorInAnnotatedReachables(lspec, lb, pos);
      var ls := lb.states[pos];
      var ls' := lb.states[pos+1];
      var hs := last(hb_prev.states);
      assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in lspec.next;
      var lmultistep := lb.trace[pos];
      assert ls == last(lb_prev.states);
      var hsteps, hs' := lemma_GetStepwiseMultistep(lasf, hasf, relation, refinement_relation, ls, ls',
                                                    lmultistep.steps, lmultistep.tid, lmultistep.tau, hs);
      var hmultistep := Armada_Multistep(hsteps, lmultistep.tid, lmultistep.tau);
      hb := AnnotatedBehavior(hb_prev.states + [hs'], hb_prev.trace + [hmultistep]);
      lemma_ExtendBehaviorRefinesBehaviorRightOne_LH(lb_prev.states, hb_prev.states, relation, last(lb.states), hs');
      assert lb.states == lb_prev.states + [last(lb.states)];
    }
  }

  ////////////////////////////////////
  // EXPORTED LEMMAS
  ////////////////////////////////////
    
  lemma lemma_GenericArmadaRefinement<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool
    )
    requires PreconditionsForGenericArmadaRefinement(lasf, hasf, relation, refinement_relation)
    ensures  AnnotatedBehaviorSpecRefinesAnnotatedBehaviorSpec(SpecFunctionsToSpec(lasf), SpecFunctionsToSpec(hasf), relation)
  {
    forall lb | AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(lasf))
      ensures exists hb :: AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
                     && BehaviorRefinesBehavior(lb.states, hb.states, relation)
    {
      var hb := lemma_GenericArmadaRefinementConstructive(lasf, hasf, relation, refinement_relation, lb);
    }
  }
    
  lemma lemma_GenericArmadaStepwiseRefinement<LState, LOneStep, LPC, HState, HOneStep, HPC>(
    lasf:Armada_SpecFunctions<LState, LOneStep, LPC>,
    hasf:Armada_SpecFunctions<HState, HOneStep, HPC>,
    relation:RefinementRelation<LState, HState>,
    refinement_relation:(LState, HState)->bool
    )
    requires PreconditionsForGenericStepwiseRefinement(lasf, hasf, relation, refinement_relation)
    ensures  AnnotatedBehaviorSpecRefinesAnnotatedBehaviorSpec(SpecFunctionsToSpec(lasf), SpecFunctionsToSpec(hasf), relation)
  {
    forall lb | AnnotatedBehaviorSatisfiesSpec(lb, SpecFunctionsToSpec(lasf))
      ensures exists hb :: AnnotatedBehaviorSatisfiesSpec(hb, SpecFunctionsToSpec(hasf))
                     && BehaviorRefinesBehavior(lb.states, hb.states, relation)
    {
      var hb := lemma_GenericStepwiseRefinementConstructive(lasf, hasf, relation, refinement_relation, lb);
    }
  }

}
