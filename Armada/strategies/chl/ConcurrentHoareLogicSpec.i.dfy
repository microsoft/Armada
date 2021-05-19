include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../../util/collections/maps.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../../util/option.s.dfy"

module ConcurrentHoareLogicSpecModule {

  // Yields are dealt with as follows.
  // * On a call, the callee has to deal with a yield happening after the requires clause is satisfied.
  // * On reaching a loop head for the first time, the loop modifies clause must hold before the yield.
  // * On reaching a loop a subsequent time, the loop modifies clause must hold between s1 and s2, where s1 is the
  //   state on reaching the loop head before a yield, and s2 is the state on returning to the loop head before yielding.
  // * After executing a loop-modifies clause, a yield can happen.
  // * On a return, the callee/returner must deal with a yield happening after reaching the return site.  That is,
  //   it must ensure the postcondition even after a yield.
  // * After executing an ensures clause, one does not have to worry about a yield happening.

  // The result of calling cr.step_to_proc on a step indicates which procedure that step is part of.
  // * A step that calls from method X into method Y is considered part of method X.
  // * A step that returns from method Y to method X is considered part of method X.  That's not a typo:  it's considered
  //   part of the caller, not the callee.
  // * A step that returns from method Y to method X and then calls method Z is likewise considered part of method X.

  import opened util_collections_maps_s
  import opened util_collections_seqs_s
  import opened util_option_s
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule

  /////////////////////////////////////////////////////
  // Type definitions
  /////////////////////////////////////////////////////

  datatype StraightlineStep<Step, PC, Proc> = StraightlineStepNormal(step:Step)
                                            | StraightlineStepLoopModifies(pc:PC)
                                            | StraightlineStepYield
                                            | StraightlineStepCall(step:Step)
                                            | StraightlineStepEnsures(callee:Proc)
                                            | StraightlineStepReturn(step:Step)
                                            | StraightlineStepReturnThenCall(step:Step)

  datatype StraightlinePhase = StraightlinePhaseNormal
                             | StraightlinePhaseLooped
                             | StraightlinePhaseYielded
                             | StraightlinePhaseCalled
                             | StraightlinePhaseEnsured

  datatype StraightlineAux<State, PC> = StraightlineAux(phase:StraightlinePhase, visited_loops:map<PC, State>)

  datatype StraightlineState<State, PC> = StraightlineState(state:State, aux:StraightlineAux<State, PC>)

  datatype PCStack<PC, Proc> = PCStack(pc:PC, stack:seq<Proc>)

  datatype CHLStepEffect<Proc> = CHLStepEffectNormal
                               | CHLStepEffectCall(callee:Proc)
                               | CHLStepEffectReturn
                               | CHLStepEffectExit
                               | CHLStepEffectReturnThenCall(callee:Proc)
                               | CHLStepEffectActorless
                               | CHLStepEffectStop

  datatype ConcurrentHoareLogicRequest<!State(==), !Actor(==), !Step(==), !PC(==), !Proc(==)> = ConcurrentHoareLogicRequest(
    spec:AnnotatedBehaviorSpec<State, Step>,
    step_to_actor:Step->Option<Actor>,
    step_to_proc:Step->Proc,
    get_actor_pc_stack:(State, Actor)->Option<PCStack<PC, Proc>>,
    state_ok:State->bool,
    pc_to_proc:PC->Proc,
    is_entry_point:PC->bool,
    is_loop_head:PC->bool,
    is_return_site:PC->bool,
    step_to_effect:Step->CHLStepEffect<Proc>,
    established_inv:State->bool,
    global_inv:State->bool,
    local_inv:(State, Actor)->bool,
    yield_pred:(State, State, Actor)->bool,
    requires_clauses:(Proc, State, Actor)->bool,
    ensures_clauses:(Proc, State, State, Actor)->bool,
    loop_modifies_clauses:(PC, State, State, Actor)->bool
    )

  /////////////////////////////////////////////////////
  // Straightline behavior specification
  /////////////////////////////////////////////////////

  function StraightlineInitAux<State, PC>() : StraightlineAux<State, PC>
  {
    StraightlineAux(StraightlinePhaseNormal, map [])
  }

  predicate StraightlineSpecInit<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    actor:Actor,
    proc:Proc
    )
  {
    // A straightline behavior begins with the actor at the beginning of a procedure
    var s := ss.state;
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    && cr.pc_to_proc(pc) == proc
    && cr.is_entry_point(pc)
    && cr.established_inv(s)
    && cr.global_inv(s)
    && cr.state_ok(s)
    && cr.requires_clauses(proc, s, actor)
    && ss.aux == StraightlineInitAux()
  }

  function StraightlineUpdateAux<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    actor:Actor,
    sstep:StraightlineStep<Step, PC, Proc>,
    s':State
    ) : StraightlineAux<State, PC>
  {
    var phase' :=
      match sstep
        case StraightlineStepNormal(_) =>          StraightlinePhaseNormal
        case StraightlineStepLoopModifies(_) =>    StraightlinePhaseLooped
        case StraightlineStepYield() =>            StraightlinePhaseYielded
        case StraightlineStepCall(_) =>            StraightlinePhaseCalled
        case StraightlineStepEnsures(_) =>         StraightlinePhaseEnsured
        case StraightlineStepReturn(_) =>          StraightlinePhaseNormal
        case StraightlineStepReturnThenCall(_) =>  StraightlinePhaseCalled
      ;
    var StraightlineState(s, aux) := ss;
    var visited_loops' := if sstep.StraightlineStepLoopModifies? && cr.get_actor_pc_stack(s, actor).Some? then
                            aux.visited_loops[cr.get_actor_pc_stack(s, actor).v.pc := s]
                          else
                            aux.visited_loops;
    StraightlineAux(phase', visited_loops')
  }

  predicate StraightlineSpecNextCommon<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor
    )
  {
    var StraightlineState(s, aux) := ss;
    var StraightlineState(s', aux') := ss';

    // The actor must be present both before and after the step.

    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).Some?

    // The type of step the state machine can take is dictated by the current phase.  (The phase depends on the previous
    // step, so this restriction restricts consecutive pairs of steps.)

    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    && (match aux.phase
         case StraightlinePhaseNormal => sstep.StraightlineStepYield?
         case StraightlinePhaseLooped => sstep.StraightlineStepNormal? || sstep.StraightlineStepCall?
         case StraightlinePhaseYielded => if cr.is_loop_head(pc) then sstep.StraightlineStepLoopModifies?
                                          else sstep.StraightlineStepNormal? || sstep.StraightlineStepCall?
         case StraightlinePhaseCalled => sstep.StraightlineStepEnsures?
         case StraightlinePhaseEnsured => sstep.StraightlineStepReturn? || sstep.StraightlineStepReturnThenCall?)

    // The established and global invariants are always preserved, and the state is always OK.

    && cr.established_inv(s')
    && cr.global_inv(s')
    && cr.state_ok(s')

    // The auxiliary information is a deterministic function of the current state and the straightline step taken.
    
    && aux' == StraightlineUpdateAux(cr, ss, actor, sstep, s')

    // If the state machine has reached an already-visited loop head and yielded, it can't execute further.

    && !(pc in aux.visited_loops && aux.phase.StraightlinePhaseYielded?)

    // The state machine can never return, except to return from a call that it made to another method.

    && (sstep.StraightlineStepReturn? || sstep.StraightlineStepReturnThenCall? ==> ss.aux.phase.StraightlinePhaseEnsured?)
  }

  predicate StraightlineSpecNextStep<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    step:Step
    )
  {
    && StraightlineSpecNextCommon(cr, ss, ss', sstep, actor)
    && cr.step_to_actor(step).Some?
    && cr.step_to_actor(step).v == actor
    && cr.step_to_proc(step) == proc
    && ActionTuple(ss.state, ss'.state, step) in cr.spec.next
    && cr.local_inv(ss.state, actor)
  }

  predicate StraightlineSpecNextNormal<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    step:Step
    )
    requires sstep.StraightlineStepNormal?
  {
    && StraightlineSpecNextStep(cr, ss, ss', sstep, actor, proc, step)
    && cr.step_to_effect(step).CHLStepEffectNormal?
  }

  predicate StraightlineSpecNextCall<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    step:Step
    )
    requires sstep.StraightlineStepCall?
  {
    && StraightlineSpecNextStep(cr, ss, ss', sstep, actor, proc, step)
    && cr.step_to_effect(step).CHLStepEffectCall?
    && var s' := ss'.state;
      var callee := cr.step_to_effect(step).callee;
    && callee == cr.pc_to_proc(cr.get_actor_pc_stack(s', actor).v.pc)
    && cr.requires_clauses(callee, s', actor)
  }

  predicate StraightlineSpecNextReturn<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    step:Step
    )
    requires sstep.StraightlineStepReturn?
  {
    && StraightlineSpecNextStep(cr, ss, ss', sstep, actor, proc, step)
    && cr.step_to_effect(step).CHLStepEffectReturn?
  }

  predicate StraightlineSpecNextReturnThenCall<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    step:Step
    )
    requires sstep.StraightlineStepReturnThenCall?
  {
    && StraightlineSpecNextStep(cr, ss, ss', sstep, actor, proc, step)
    && cr.step_to_effect(step).CHLStepEffectReturnThenCall?
    && var s' := ss'.state;
      var callee := cr.step_to_effect(step).callee;
    && callee == cr.pc_to_proc(cr.get_actor_pc_stack(s', actor).v.pc)
    && cr.requires_clauses(callee, s', actor)
  }

  predicate StraightlineSpecNextYield<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc
    )
    requires sstep.StraightlineStepYield?
  {
    && StraightlineSpecNextCommon(cr, ss, ss', sstep, actor)
    && var s := ss.state;
       var s' := ss'.state;
    && cr.get_actor_pc_stack(s', actor) == cr.get_actor_pc_stack(s, actor)
    && cr.yield_pred(s, s', actor)
  }

  predicate StraightlineSpecNextLoopModifies<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    pc:PC
    )
    requires sstep.StraightlineStepLoopModifies?
  {
    && StraightlineSpecNextCommon(cr, ss, ss', sstep, actor)
    && var s := ss.state;
      var s' := ss'.state;
    && pc == cr.get_actor_pc_stack(s, actor).v.pc
    && cr.is_loop_head(pc)
    && cr.get_actor_pc_stack(s', actor) == cr.get_actor_pc_stack(s, actor)
    && cr.loop_modifies_clauses(pc, s, s', actor)
  }

  predicate StraightlineSpecNextEnsures<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc,
    callee:Proc
    )
    requires sstep.StraightlineStepEnsures?
  {
    && StraightlineSpecNextCommon(cr, ss, ss', sstep, actor)
    && var s := ss.state;
       var s' := ss'.state;
       var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
       var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
    && callee == cr.pc_to_proc(pc)
    && callee == cr.pc_to_proc(pc')
    && cr.is_return_site(pc')
    && stack' == stack
    && cr.ensures_clauses(callee, s, s', actor)
  }

  predicate StraightlineSpecNext<State, Actor, Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    ss:StraightlineState<State, PC>,
    ss':StraightlineState<State, PC>,
    sstep:StraightlineStep<Step, PC, Proc>,
    actor:Actor,
    proc:Proc
    )
  {
    match sstep
      case StraightlineStepNormal(step) =>
        StraightlineSpecNextNormal(cr, ss, ss', sstep, actor, proc, step)

      case StraightlineStepLoopModifies(pc) =>
        StraightlineSpecNextLoopModifies(cr, ss, ss', sstep, actor, proc, pc)

      case StraightlineStepYield() =>
        StraightlineSpecNextYield(cr, ss, ss', sstep, actor, proc)

      case StraightlineStepCall(step) =>
        StraightlineSpecNextCall(cr, ss, ss', sstep, actor, proc, step)

      case StraightlineStepEnsures(callee) =>
        StraightlineSpecNextEnsures(cr, ss, ss', sstep, actor, proc, callee)

      case StraightlineStepReturn(step) =>
        StraightlineSpecNextReturn(cr, ss, ss', sstep, actor, proc, step)

      case StraightlineStepReturnThenCall(step) =>
        StraightlineSpecNextReturnThenCall(cr, ss, ss', sstep, actor, proc, step)
  }

  function GetStraightlineSpec<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    actor:Actor,
    proc:Proc
    ) :
    AnnotatedBehaviorSpec<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>
  {
    AnnotatedBehaviorSpec(iset s | StraightlineSpecInit(cr, s, actor, proc),
                          iset s, s', step | StraightlineSpecNext(cr, s, s', step, actor, proc) :: ActionTuple(s, s', step))
  }

  /////////////////////////////////////////////////////
  // Simple parameter validity
  /////////////////////////////////////////////////////

  predicate LoopHeadsArentReturnSites<PC(!new)>(
    is_loop_head:PC->bool,
    is_return_site:PC->bool
    )
  {
    forall pc :: !(is_loop_head(pc) && is_return_site(pc))
  }

  predicate YieldPredicateReflexive<State(!new), Actor(!new), Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s, actor {:trigger cr.yield_pred(s, s, actor)} ::
      cr.state_ok(s) && cr.get_actor_pc_stack(s, actor).Some? ==> cr.yield_pred(s, s, actor)
  }

  predicate YieldPredicateTransitive<State(!new), Actor(!new), Step, PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s1, s2, s3, actor {:trigger cr.yield_pred(s1, s2, actor), cr.yield_pred(s2, s3, actor)} ::
       && cr.established_inv(s1)
       && cr.global_inv(s1)
       && cr.established_inv(s2)
       && cr.global_inv(s2)
       && cr.yield_pred(s1, s2, actor)
       && cr.yield_pred(s2, s3, actor)
       ==> cr.yield_pred(s1, s3, actor)
  }

  /////////////////////////////////////////////////////
  // State initialization
  /////////////////////////////////////////////////////

  predicate ActorsBeginAtEntryPointsWithEmptyStacksConditions<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    actor:Actor
    )
  {
    && s in cr.spec.init
    && cr.get_actor_pc_stack(s, actor).Some?
  }

  predicate ActorsBeginAtEntryPointsWithEmptyStacks<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    // At initialization, each thread is at a procedure entry point with an empty stack
    forall s, actor {:trigger ActorsBeginAtEntryPointsWithEmptyStacksConditions(cr, s, actor)} ::
      ActorsBeginAtEntryPointsWithEmptyStacksConditions(cr, s, actor)
      ==> var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
          && cr.is_entry_point(pc)
          && |stack| == 0
  }

  predicate GlobalInvariantSatisfiedInitially<State(!new), Actor(!new), Step, PC, Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s :: s in cr.spec.init ==> cr.global_inv(s) && cr.state_ok(s)
  }

  predicate RequiresClausesSatisfiedInitiallyConditions<State(!new), Actor(!new), Step, PC, Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    actor:Actor
    )
  {
    && s in cr.spec.init
    && cr.get_actor_pc_stack(s, actor).Some?
  }

  predicate RequiresClausesSatisfiedInitially<State(!new), Actor(!new), Step, PC, Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s, actor {:trigger RequiresClausesSatisfiedInitiallyConditions(cr, s, actor)} ::
      RequiresClausesSatisfiedInitiallyConditions(cr, s, actor)
      ==> var pc := cr.get_actor_pc_stack(s, actor).v.pc;
          var proc := cr.pc_to_proc(pc);
          cr.requires_clauses(proc, s, actor)
  }

  /////////////////////////////////////////////////////
  // Actorless steps
  /////////////////////////////////////////////////////

  predicate ActorlessStepsDontChangeActorsConditions<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    actor:Actor
    )
  {
    && cr.established_inv(s)
    && ActionTuple(s, s', step) in cr.spec.next
    && cr.step_to_actor(step).None?
  }

  predicate ActorlessStepsDontChangeActors<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s, s', step, actor {:trigger ActorlessStepsDontChangeActorsConditions(cr, s, s', step, actor)} ::
      ActorlessStepsDontChangeActorsConditions(cr, s, s', step, actor)
      ==> cr.get_actor_pc_stack(s', actor) == cr.get_actor_pc_stack(s, actor)
  }

  predicate ActorlessStepsMaintainYieldPredicateAndGlobalInvariantConditions<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    actor:Actor
    )
  {
    && cr.established_inv(s)
    && cr.global_inv(s)
    && cr.established_inv(s')
    && ActionTuple(s, s', step) in cr.spec.next
    && cr.step_to_actor(step).None?
    && cr.get_actor_pc_stack(s, actor).Some?
  }

  predicate ActorlessStepsMaintainYieldPredicateAndGlobalInvariant<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s, s', step, actor {:trigger ActorlessStepsMaintainYieldPredicateAndGlobalInvariantConditions(cr, s, s', step, actor)} ::
      ActorlessStepsMaintainYieldPredicateAndGlobalInvariantConditions(cr, s, s', step, actor)
      ==> cr.yield_pred(s, s', actor) && cr.global_inv(s') && cr.state_ok(s')
  }

  /////////////////////////////////////////////////////
  // Step effects
  /////////////////////////////////////////////////////

  predicate CorrectCHLStepEffectNormal<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).Some?
    && var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
      var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
    && !cr.is_return_site(pc)
    && cr.pc_to_proc(pc') == cr.pc_to_proc(pc) == cr.step_to_proc(step)
    && stack' == stack
  }

  predicate CorrectCHLStepEffectCall<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    callee:Proc
    )
  {
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).Some?
    && var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
      var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
    && !cr.is_return_site(pc)
    && cr.is_entry_point(pc')
    && cr.pc_to_proc(pc') == callee
    && |stack'| > 0
    && stack'[0] == cr.pc_to_proc(pc) == cr.step_to_proc(step)
    && stack'[1..] == stack
  }

  predicate CorrectCHLStepEffectReturn<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).Some?
    && var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
      var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
    && cr.is_return_site(pc)
    && |stack| > 0
    && cr.pc_to_proc(pc') == stack[0] == cr.step_to_proc(step)
    && stack' == stack[1..]
  }

  predicate CorrectCHLStepEffectExit<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).None?
    && var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
    && cr.is_return_site(pc)
    && cr.pc_to_proc(pc) == cr.step_to_proc(step)
    && |stack| == 0
  }

  predicate CorrectCHLStepEffectReturnThenCall<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    callee:Proc
    )
  {
    // Step that returns to a caller, then does another call
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && cr.get_actor_pc_stack(s', actor).Some?
    && var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
      var PCStack(pc', stack') := cr.get_actor_pc_stack(s', actor).v;
    && cr.is_return_site(pc)
    && |stack| > 0
    && stack[0] == cr.step_to_proc(step)
    && cr.pc_to_proc(pc') == callee
    && cr.is_entry_point(pc')
    && stack' == stack
  }

  predicate CorrectCHLStepEffectActorless<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    && cr.state_ok(s)
    && cr.state_ok(s')
    && cr.step_to_actor(step).None?
  }

  predicate CorrectCHLStepEffectStop<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    && cr.state_ok(s)
    && !cr.state_ok(s')
    && (cr.step_to_actor(step).Some? ==> cr.get_actor_pc_stack(s, cr.step_to_actor(step).v).Some?)
  }

  predicate CorrectCHLStepEffect<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step
    )
  {
    match cr.step_to_effect(step)
      case CHLStepEffectNormal => CorrectCHLStepEffectNormal(cr, s, s', step)
      case CHLStepEffectCall(callee) => CorrectCHLStepEffectCall(cr, s, s', step, callee)
      case CHLStepEffectReturn => CorrectCHLStepEffectReturn(cr, s, s', step)
      case CHLStepEffectExit => CorrectCHLStepEffectExit(cr, s, s', step)
      case CHLStepEffectReturnThenCall(callee) => CorrectCHLStepEffectReturnThenCall(cr, s, s', step, callee)
      case CHLStepEffectActorless => CorrectCHLStepEffectActorless(cr, s, s', step)
      case CHLStepEffectStop => CorrectCHLStepEffectStop(cr, s, s', step)
  }

  predicate CHLStepEffectsCorrect<State(!new), Actor, Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall s, s', step :: ActionTuple(s, s', step) in cr.spec.next ==> CorrectCHLStepEffect(cr, s, s', step)
  }

  /////////////////////////////////////////////////////
  // Other control flow
  /////////////////////////////////////////////////////

  predicate ForkedActorsStartAtEntryPointsWithEmptyStacksConditions<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    forked_actor:Actor
    )
  {
    && ActionTuple(s, s', step) in cr.spec.next
    && cr.get_actor_pc_stack(s, forked_actor).None?
    && cr.get_actor_pc_stack(s', forked_actor).Some?
  }

  predicate ForkedActorsStartAtEntryPointsWithEmptyStacks<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    // When a thread starts (i.e., is forked), the forking step isn't actorless or an exit and the forked thread
    // is at a procedure entry point with an empty stack
    forall s, s', step, forked_actor {:trigger ForkedActorsStartAtEntryPointsWithEmptyStacksConditions(cr, s, s', step, forked_actor)} ::
      ForkedActorsStartAtEntryPointsWithEmptyStacksConditions(cr, s, s', step, forked_actor)
      ==> && cr.step_to_actor(step).Some?
          && !cr.step_to_effect(step).CHLStepEffectExit?
          && var PCStack(pc', stack') := cr.get_actor_pc_stack(s', forked_actor).v;
          && cr.is_entry_point(pc')
          && |stack'| == 0
  }

  predicate StepsDontChangeOtherActorsExceptViaForkConditions<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    s:State,
    s':State,
    step:Step,
    other_actor:Actor
    )
  {
    && ActionTuple(s, s', step) in cr.spec.next
    && cr.step_to_actor(step) != Some(other_actor)
    && cr.get_actor_pc_stack(s, other_actor).Some?
  }

  predicate StepsDontChangeOtherActorsExceptViaFork<State(!new), Actor(!new), Step(!new), PC, Proc>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    // One actor taking a step leaves each other actor's PC and stack unchanged
    // (unless that other actor didn't have a PC before, i.e., this actor was forking that actor)
    forall s, s', step, other_actor {:trigger StepsDontChangeOtherActorsExceptViaForkConditions(cr, s, s', step, other_actor)} ::
      StepsDontChangeOtherActorsExceptViaForkConditions(cr, s, s', step, other_actor)
      ==> cr.get_actor_pc_stack(s', other_actor) == cr.get_actor_pc_stack(s, other_actor)
  }

  /////////////////////////////////////////////////////
  // Requirements for straightline behaviors
  /////////////////////////////////////////////////////

  predicate StraightlineBehaviorsSatisfyGlobalInvariantConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    step:Step,
    s':State
    )
  {
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
      var proc := cr.step_to_proc(step);
      var effect := cr.step_to_effect(step);
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.local_inv(s, actor)
    && ActionTuple(s, s', step) in cr.spec.next
    && !effect.CHLStepEffectStop?
    && (if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
         phase.StraightlinePhaseEnsured?
       else
         phase.StraightlinePhaseYielded?)
  }

  predicate StraightlineBehaviorsSatisfyGlobalInvariant<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')} ::
      StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')
      ==> cr.global_inv(s')
  }

  predicate StraightlineBehaviorsSatisfyLocalInvariantConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    step:Step,
    s':State
    )
  {
    && cr.step_to_actor(step).Some?
    && |sb.states| > 0
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
      var actor := cr.step_to_actor(step).v;
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
      var proc := cr.pc_to_proc(pc);
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && ActionTuple(s, s', step) in cr.spec.next
    && phase.StraightlinePhaseYielded?
  }

  predicate StraightlineBehaviorsSatisfyLocalInvariant<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, sb, step, s')} ::
      StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, sb, step, s')
      ==> cr.local_inv(last(sb.states).state, cr.step_to_actor(step).v)
  }

  predicate StraightlineBehaviorsSatisfyPreconditionsForCallsConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    step:Step,
    s':State
    )
  {
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
      var proc := cr.step_to_proc(step);
      var effect := cr.step_to_effect(step);
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.local_inv(s, actor)
    && ActionTuple(s, s', step) in cr.spec.next
    && (|| (effect.CHLStepEffectCall? && phase.StraightlinePhaseYielded?)
       || (effect.CHLStepEffectReturnThenCall? && phase.StraightlinePhaseEnsured?))
    && cr.get_actor_pc_stack(s', actor).Some?
  }

  predicate StraightlineBehaviorsSatisfyPreconditionsForCalls<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyPreconditionsForCallsConditions(cr, sb, step, s')} ::
      StraightlineBehaviorsSatisfyPreconditionsForCallsConditions(cr, sb, step, s')
      ==> var actor := cr.step_to_actor(step).v;
          var callee := cr.step_to_effect(step).callee;
          cr.requires_clauses(callee, s', actor)
  }

  predicate StraightlineBehaviorsSatisfyPreconditionsForForksConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    step:Step,
    s':State,
    forked_actor:Actor
    )
  {
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
      var proc := cr.step_to_proc(step);
      var effect := cr.step_to_effect(step);
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.local_inv(s, actor)
    && ActionTuple(s, s', step) in cr.spec.next
    && !effect.CHLStepEffectStop?
    && (if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
         phase.StraightlinePhaseEnsured?
       else 
         phase.StraightlinePhaseYielded?)
    && actor != forked_actor
    && cr.get_actor_pc_stack(s, forked_actor).None?
    && cr.get_actor_pc_stack(s', forked_actor).Some?
  }

  predicate StraightlineBehaviorsSatisfyPreconditionsForForks<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, step, s', forked_actor {:trigger StraightlineBehaviorsSatisfyPreconditionsForForksConditions(cr, sb, step, s', forked_actor)} ::
      StraightlineBehaviorsSatisfyPreconditionsForForksConditions(cr, sb, step, s', forked_actor)
      ==> var forked_pc := cr.get_actor_pc_stack(s', forked_actor).v.pc;
          var forked_proc := cr.pc_to_proc(forked_pc);
          cr.requires_clauses(forked_proc, s', forked_actor)
  }

  predicate StraightlineBehaviorsSatisfyPostconditionsConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc
    )
  {
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    && cr.is_return_site(pc)
    && phase.StraightlinePhaseYielded?
  }

  predicate StraightlineBehaviorsSatisfyPostconditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyPostconditionsConditions(cr, sb, actor, proc)} ::
      StraightlineBehaviorsSatisfyPostconditionsConditions(cr, sb, actor, proc)
      ==> cr.ensures_clauses(proc, sb.states[0].state, last(sb.states).state, actor)
  }

  predicate StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc
    )
  {
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var StraightlineState(s, aux) := ss;
      var phase := aux.phase;
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    && cr.is_loop_head(pc)
    && pc !in aux.visited_loops
    && phase.StraightlinePhaseYielded?
  }

  predicate StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntry<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions(cr, sb, actor, proc)} ::
      StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions(cr, sb, actor, proc)
      ==> var s := last(sb.states).state;
          var pc := cr.get_actor_pc_stack(s, actor).v.pc;
          cr.loop_modifies_clauses(pc, s, s, actor)
  }

  predicate StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    actor:Actor,
    proc:Proc
    )
  {
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.get_actor_pc_stack(s, actor).Some?
    && var pc := cr.get_actor_pc_stack(s, actor).v.pc;
    && cr.is_loop_head(pc)
    && pc in ss.aux.visited_loops
    && phase.StraightlinePhaseYielded?
  }

  predicate StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBack<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions(cr, sb, actor, proc)} ::
      StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions(cr, sb, actor, proc)
      ==> var StraightlineState(s, aux) := last(sb.states);
          var pc := cr.get_actor_pc_stack(s, actor).v.pc;
          cr.loop_modifies_clauses(pc, aux.visited_loops[pc], s, actor)
  }

  predicate StraightlineBehaviorsSatisfyYieldPredicateConditions<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    sb:AnnotatedBehavior<StraightlineState<State, PC>, StraightlineStep<Step, PC, Proc>>,
    step:Step,
    s':State,
    other_actor:Actor
    )
  {
    && cr.step_to_actor(step).Some?
    && var actor := cr.step_to_actor(step).v;
      var proc := cr.step_to_proc(step);
      var effect := cr.step_to_effect(step);
    && AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, actor, proc))
    && var ss := last(sb.states);
      var s := ss.state;
      var phase := ss.aux.phase;
    && cr.local_inv(s, actor)
    && ActionTuple(s, s', step) in cr.spec.next
    && !effect.CHLStepEffectStop?
    && (if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
         phase.StraightlinePhaseEnsured?
       else 
         phase.StraightlinePhaseYielded?)
    && actor != other_actor
    && cr.get_actor_pc_stack(s, other_actor).Some?
  }

  predicate StraightlineBehaviorsSatisfyYieldPredicate<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    forall sb, step, s', other_actor {:trigger StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)} ::
      StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)
      ==> cr.yield_pred(last(sb.states).state, s', other_actor)
  }

  /////////////////////////////////////////////////////
  // Request validity
  /////////////////////////////////////////////////////

  predicate IsValidConcurrentHoareLogicRequest<State(!new), Actor(!new), Step(!new), PC(!new), Proc(!new)>(
    cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>
    )
  {
    // Simple parameter validity
    && IsInvariantPredicateOfSpec(cr.established_inv, cr.spec)
    && LoopHeadsArentReturnSites(cr.is_loop_head, cr.is_return_site)
    && YieldPredicateReflexive(cr)
    && YieldPredicateTransitive(cr)

    // Initialization
    && ActorsBeginAtEntryPointsWithEmptyStacks(cr)
    && GlobalInvariantSatisfiedInitially(cr)
    && RequiresClausesSatisfiedInitially(cr)

    // Actorless steps
    && ActorlessStepsDontChangeActors(cr)
    && ActorlessStepsMaintainYieldPredicateAndGlobalInvariant(cr)

    // Control flow
    && CHLStepEffectsCorrect(cr)
    && ForkedActorsStartAtEntryPointsWithEmptyStacks(cr)
    && StepsDontChangeOtherActorsExceptViaFork(cr)

    // Straightline behaviors
    && StraightlineBehaviorsSatisfyGlobalInvariant(cr)
    && StraightlineBehaviorsSatisfyLocalInvariant(cr)
    && StraightlineBehaviorsSatisfyPreconditionsForCalls(cr)
    && StraightlineBehaviorsSatisfyPreconditionsForForks(cr)
    && StraightlineBehaviorsSatisfyPostconditions(cr)
    && StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntry(cr)
    && StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBack(cr)
    && StraightlineBehaviorsSatisfyYieldPredicate(cr)
  }

}
