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

  datatype Armada_Multistep<OneStep> = Armada_Multistep(steps:seq<OneStep>, tid:Armada_ThreadHandle, tau:bool)

  function SpecFunctionsToAnnotatedSpec<State(!new), OneStep(!new), PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>
    ) : AnnotatedBehaviorSpec<State, Armada_Multistep<OneStep>>
  {
    AnnotatedBehaviorSpec(
      iset s | asf.init(s) :: s,
      iset s, s', entry:Armada_Multistep<OneStep>
        | Armada_NextMultistep(asf, s, s', entry.steps, entry.tid, entry.tau)
        :: ActionTuple(s, s', entry)
    )
  }

  predicate Armada_Next<State(!new), OneStep(!new), PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    s': State,
    multistep: Armada_Multistep<OneStep>
    )
  {
    Armada_NextMultistep(asf, s, s', multistep.steps, multistep.tid, multistep.tau)
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
    forall s, step, tid :: inv(s) && asf.step_valid(s, step, tid) ==> inv(asf.step_next(s, step, tid))
  }

  predicate OneStepRequiresOK<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step, tid :: asf.step_valid(s, step, tid) ==> asf.state_ok(s)
  }

  predicate SteppingThreadHasPC<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step, tid :: asf.step_valid(s, step, tid) ==> asf.get_thread_pc(s, tid).Some?
  }

  predicate TauLeavesPCUnchanged<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step, tid :: asf.step_valid(s, step, tid) && asf.is_step_tau(step) ==>
      var s' := asf.step_next(s, step, tid);
      asf.get_thread_pc(s', tid) == asf.get_thread_pc(s, tid)
  }

  predicate ThreadCantAffectOtherThreadPCExceptViaFork<State(!new), OneStep(!new), PC>(
    asf:Armada_SpecFunctions<State, OneStep, PC>
    )
  {
    forall s, step, tid, other_tid :: asf.step_valid(s, step, tid) && tid != other_tid
       ==> var s' := asf.step_next(s, step, tid);
           var pc := asf.get_thread_pc(s, other_tid);
           var pc' := asf.get_thread_pc(s', other_tid);
           (pc' != pc ==> pc.None? && !asf.is_pc_nonyielding(pc'.v))
  }

  ////////////////////////////////////////////////////////////////////////
  // Extracting a sequence of states from a sequence of steps
  ////////////////////////////////////////////////////////////////////////

  function Armada_GetStateSequence<State, OneStep, PC>(
    asf: Armada_SpecFunctions<State, OneStep, PC>,
    s: State,
    steps: seq<OneStep>,
    tid: Armada_ThreadHandle
    ) : (states: seq<State>)
    ensures |states| == |steps| + 1
    ensures states[0] == s
    decreases |steps|
  {
    if |steps| == 0 then
      [s]
    else
      [s] + Armada_GetStateSequence(asf, asf.step_next(s, steps[0], tid), steps[1..], tid)
  }

}
