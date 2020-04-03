include "../../util/option.s.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../../ArmadaCommonDefinitions.dfy"

module GenericArmadaSpecModule {

  import opened util_option_s
  import opened AnnotatedBehaviorModule
  import opened ArmadaCommonDefinitions

  /////////////////////////////////////////////
  // Constructing an AnnotatedBehaviorSpec
  /////////////////////////////////////////////

  function SpecFunctionsToSpec<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    ) : AnnotatedBehaviorSpec<State, Armada_Multistep<OneStep>>
  {
    AnnotatedBehaviorSpec(
      iset s | asf.init(s) :: s,
      iset s, s', entry:Armada_Multistep<OneStep>
        | Armada_NextMultistep(asf, s, s', entry.steps, entry.tid, entry.tau)
        :: ActionTuple(s, s', entry)
    )
  }

  /////////////////////////////////////////////
  // Predicates about an Armada spec
  /////////////////////////////////////////////

  predicate InitImpliesInv<State(!new), OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool
    )
  {
    forall s :: asf.init(s) ==> inv(s)
  }

  predicate InitImpliesYielding<State(!new), OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, tid :: asf.init(s) && asf.get_thread_pc(s, tid).Some? ==> !asf.is_pc_nonyielding(asf.get_thread_pc(s, tid).v)
  }

  predicate InitImpliesOK<State(!new), OneStep, PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s :: asf.init(s) ==> asf.state_ok(s)
  }

  predicate OneStepPreservesInv<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>,
    inv:State->bool
    )
  {
    forall s, step :: inv(s) && asf.step_valid(s, step) ==> inv(asf.step_next(s, step))
  }

  predicate OneStepRequiresOK<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step :: asf.step_valid(s, step) ==> asf.state_ok(s)
  }

  predicate SteppingThreadHasPC<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step :: asf.step_valid(s, step) ==> asf.get_thread_pc(s, asf.step_to_thread(step)).Some?
  }

  predicate TauLeavesPCUnchanged<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step :: asf.step_valid(s, step) && asf.is_step_tau(step) ==>
      var tid := asf.step_to_thread(step);
      var s' := asf.step_next(s, step);
      asf.get_thread_pc(s', tid) == asf.get_thread_pc(s, tid)
  }

  predicate ThreadCantAffectOtherThreadPCExceptViaFork<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step, tid :: asf.step_valid(s, step) && asf.step_to_thread(step) != tid
       ==> var s' := asf.step_next(s, step);
           var pc := asf.get_thread_pc(s, tid);
           var pc' := asf.get_thread_pc(s', tid);
           (pc' != pc ==> pc.None? && !asf.is_pc_nonyielding(pc'.v))
  }

}
