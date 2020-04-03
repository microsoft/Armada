include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../../util/collections/maps.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../../util/option.s.dfy"

module ConcurrentHoareLogicSpecModule {

    import opened util_collections_maps_s
    import opened util_collections_seqs_s
    import opened util_option_s
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule

    datatype PCType<!PC(==)> = ReturnSite | CallSite | ForkSite | LoopHead | NormalPC

    datatype StraightlineState<State, PC> = StraightlineState(state:State, visited_loops:map<PC, State>, started:bool)
    datatype StraightlineStep<State, Step>
        = StraightlineStepStart()
                // start execution of the procedure by yielding
        | StraightlineStepNormal(post_stmt_state:State, step:Step)
                // perform the associated real step, then yield
        | StraightlineStepCall(post_call_state:State, pre_return_state:State, post_return_state:State, call_step:Step, return_step:Step)
                // call, then havoc subject to the invariant and postcondition, then return, then yield
        | StraightlineStepLoop(post_loops_state:State, post_guard_state:State, guard_step:Step)
                // havoc the state subject to the invariant and loop modifies clause, then execute guard step, then yield
    datatype PCStack<PC> = PCStack(pc:PC, stack:seq<PC>)

    datatype StraightlineConfig<State> = StraightlineConfig(state:State)

    datatype ConcurrentHoareLogicRequest<!State(==), !Actor(==), !Step(==), !PC(==), !ProcName(==)> = ConcurrentHoareLogicRequest(
        spec:AnnotatedBehaviorSpec<State, Step>,
        idmap:Step->Option<Actor>,
        actor_info:State->imap<Actor, PCStack<PC>>,
        pc_to_proc:PC->ProcName,
        is_entry_point:PC->bool,
        pc_type:PC->PCType<PC>,
        established_inv:State->bool,
        global_inv:State->bool,
        local_inv:(State, Actor)->bool,
        enablement_condition:(State, Actor)->bool,
        yield_pred:(State, State, Actor)->bool,
        requires_clauses:(ProcName, State, Actor)->bool,
        ensures_clauses:(ProcName, State, State, Actor)->bool,
        loop_modifies_clauses:map<PC, (State, State, Actor)->bool>
        )

    predicate SpecSatisfiesProgramControlFlow<State(!new), Actor, Step(!new), PC, ProcName>(
        spec:AnnotatedBehaviorSpec<State, Step>,
        idmap:Step->Option<Actor>,
        actor_info:State->imap<Actor, PCStack<PC>>,
        pc_to_proc:PC->ProcName,
        is_entry_point:PC->bool,
        pc_type:PC->PCType<PC>
        )
    {
        // At initialization, each thread is at a procedure entry point with an empty stack
        && (forall s, actor ::
               && s in spec.init
               && actor in actor_info(s)
               ==> var PCStack(pc, stack) := actor_info(s)[actor];
                   && is_entry_point(pc)
                   && |stack| == 0)

        // When a thread starts (i.e., is forked), the forker is at a fork site and the forked thread
        // is at a procedure entry point with an empty stack
        && (forall s, s', step, forked_actor ::
              && ActionTuple(s, s', step) in spec.next
              && forked_actor !in actor_info(s)
              && forked_actor in actor_info(s')
              ==> && idmap(step).Some?
                  && idmap(step).v in actor_info(s)
                  && pc_type(actor_info(s)[idmap(step).v].pc).ForkSite?
                  && var PCStack(pc', stack') := actor_info(s')[forked_actor];
                  && is_entry_point(pc')
                  && |stack'| == 0)

        // One actor taking a step leaves each other actor's PC and stack unchanged
        // (unless that other actor didn't have a PC before, i.e., this actor was forking that actor)
        && (forall s, s', step, other_actor ::
              && ActionTuple(s, s', step) in spec.next
              && idmap(step) != Some(other_actor)
              && other_actor in actor_info(s)
              ==> && other_actor in actor_info(s')
                  && actor_info(s')[other_actor] == actor_info(s)[other_actor])

        // Executing a call instruction sets the PC to the target procedure's entry point and pushes the return-to value on the stack
        // Executing a return instruction sets the PC to what gets popped off the top of the stack
        // Executing anything other than a call or return leaves the stack unchanged and has the PC stay in the same procedure
        && (forall s, s', step ::
               && idmap(step).Some?
               && ActionTuple(s, s', step) in spec.next
               ==> var actor := idmap(step).v;
                   && actor in actor_info(s)
                   && var PCStack(pc, stack) := actor_info(s)[actor];
                   && (|| (&& pc_type(pc).CallSite?
                         && actor in actor_info(s')
                         && var PCStack(pc', stack') := actor_info(s')[actor];
                         && is_entry_point(pc')
                         && |stack'| > 0
                         && stack == stack'[1..]
                         && pc_to_proc(stack'[0]) == pc_to_proc(pc)
                         )
                      || (&& pc_type(pc).ReturnSite?
                         && |stack| > 0
                         && actor in actor_info(s')
                         && var PCStack(pc', stack') := actor_info(s')[actor];
                         && pc' == stack[0]
                         && stack' == stack[1..]
                         )
                      || (&& pc_type(pc).ReturnSite?
                         && |stack| == 0
                         // If the stack is empty when we return, the thread exits, which we model as no longer being in actor_info
                         && actor !in actor_info(s')
                         )
                      || (&& actor in actor_info(s')
                         && var PCStack(pc', stack') := actor_info(s')[actor];
                         && pc_to_proc(pc') == pc_to_proc(pc)
                         && stack' == stack
                         )
                      )
           )
    }

    predicate StraightlineSpecInit<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName
        )
    {
        // A straightline behavior begins with the actor at the beginning of a procedure, in the not-started state
        && actor in cr.actor_info(s.state)
        && var pc := cr.actor_info(s.state)[actor].pc;
        && cr.pc_to_proc(pc) == proc
        && cr.is_entry_point(pc)
        && cr.established_inv(s.state)
        && cr.global_inv(s.state)
        && cr.requires_clauses(proc, s.state, actor)
        && |s.visited_loops| == 0
        && !s.started
    }

    predicate StraightlineSpecNextCommon<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName
        )
    {
        && cr.established_inv(s.state)
        && cr.global_inv(s.state)
        && actor in cr.actor_info(s.state)
        && actor in cr.actor_info(s'.state)
        && cr.established_inv(s'.state)
        && cr.global_inv(s'.state)
        && var PCStack(pc, stack) := cr.actor_info(s.state)[actor];
        && cr.pc_to_proc(pc) == proc
        && s'.started
        && pc !in s.visited_loops      // The program can't proceed once the PC jumps back to a loop head
    }

    predicate StraightlineSpecNextStart<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName
        )
    {
        && StraightlineSpecNextCommon(cr, s, s', actor, proc)
        && !s.started
        && cr.yield_pred(s.state, s'.state, actor)
        && s'.visited_loops == s.visited_loops
    }

    predicate StraightlineSpecNextNormal<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName,
        post_stmt_state:State,
        lstep:Step
        )
    {
        && StraightlineSpecNextCommon(cr, s, s', actor, proc)
        && cr.local_inv(s.state, actor)
        && var pc := cr.actor_info(s.state)[actor].pc;
        && s.started
        && !cr.pc_type(pc).LoopHead?   // The PC can't be at a loop head, because from there we take loop steps
        && actor in cr.actor_info(post_stmt_state)
        && cr.actor_info(post_stmt_state)[actor].stack == cr.actor_info(s.state)[actor].stack

        // First, we take a normal step to go from s.state to post_stmt_state

        && cr.idmap(lstep).Some?
        && cr.idmap(lstep).v == actor
        && cr.enablement_condition(s.state, actor)
        && ActionTuple(s.state, post_stmt_state, lstep) in cr.spec.next
        && cr.established_inv(post_stmt_state)
        && cr.global_inv(post_stmt_state)

        // Then, we yield to other threads to go from post_stmt_state to s'.state

        && cr.yield_pred(post_stmt_state, s'.state, actor)
        && s'.visited_loops == s.visited_loops
        && cr.established_inv(s'.state)
        && cr.global_inv(s'.state)
    }

    predicate StraightlineSpecNextCall<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName,
        post_call_state:State,
        pre_return_state:State,
        post_return_state:State,
        call_step:Step,
        return_step:Step
        )
    {
        && StraightlineSpecNextCommon(cr, s, s', actor, proc)
        && cr.local_inv(s.state, actor)
        && var PCStack(pc, stack) := cr.actor_info(s.state)[actor];
        && s.started
        && cr.pc_type(pc).CallSite?
        && actor in cr.actor_info(post_call_state)
        && actor in cr.actor_info(pre_return_state)
        && actor in cr.actor_info(post_return_state)
        && var PCStack(pc_post_call, stack_post_call) := cr.actor_info(post_call_state)[actor];
        && var PCStack(pc_pre_return, stack_pre_return) := cr.actor_info(pre_return_state)[actor];
        && var PCStack(pc_post_return, stack_post_return) := cr.actor_info(post_return_state)[actor];

        // First, we call into the callee (pushing a stack frame, e.g.)

        && var callee := cr.pc_to_proc(pc_post_call);
        && cr.is_entry_point(pc_post_call)
        && |stack_post_call| > 0
        && cr.enablement_condition(s.state, actor)
        && ActionTuple(s.state, post_call_state, call_step) in cr.spec.next
        && cr.idmap(call_step).Some?
        && cr.idmap(call_step).v == actor
        && cr.established_inv(post_call_state)
        && cr.global_inv(post_call_state)
        && cr.requires_clauses(callee, post_call_state, actor)

        // Second, we simulate execution of the callee

        && cr.pc_to_proc(pc_pre_return) == callee
        && cr.pc_type(pc_pre_return).ReturnSite?
        && stack_pre_return == stack_post_call
        && cr.ensures_clauses(callee, post_call_state, pre_return_state, actor)
        && cr.established_inv(pre_return_state)
        && cr.global_inv(pre_return_state)
        && cr.local_inv(pre_return_state, actor)

        // Third, we return to the caller, with the PC becoming the return-to site of the call

        && cr.enablement_condition(pre_return_state, actor)
        && ActionTuple(pre_return_state, post_return_state, return_step) in cr.spec.next
        && cr.idmap(return_step).Some?
        && cr.idmap(return_step).v == actor
        && pc_post_return == stack_post_call[0]
        && stack_post_return == stack
        && cr.established_inv(post_return_state)
        && cr.global_inv(post_return_state)

        // Finally, we havoc the state subject to the yield predicate

        && cr.yield_pred(post_return_state, s'.state, actor)
        && s'.visited_loops == s.visited_loops
        && cr.established_inv(s'.state)
        && cr.global_inv(s'.state)
    }

    predicate StraightlineSpecNextLoop<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        actor:Actor,
        proc:ProcName,
        post_loops_state:State,
        post_guard_state:State,
        guard_step:Step
        )
    {
        && StraightlineSpecNextCommon(cr, s, s', actor, proc)
        && cr.local_inv(s.state, actor)
        && var PCStack(pc, stack) := cr.actor_info(s.state)[actor];
        && s.started
        && cr.pc_type(pc).LoopHead?
        && actor in cr.actor_info(post_loops_state)
        && actor in cr.actor_info(post_guard_state)
        && var PCStack(pc_post_loops, stack_post_loops) := cr.actor_info(post_loops_state)[actor];
        && var PCStack(pc_post_guard, stack_post_guard) := cr.actor_info(post_guard_state)[actor];

        // First, we emulate zero or more loop body executions, by havocing the state subject to the
        // local and global predicates, and the loop modifies clause. We keep the PC and stack of
        // this actor unchanged, though.

        && cr.enablement_condition(s.state, actor)
        && (pc in cr.loop_modifies_clauses ==> cr.loop_modifies_clauses[pc](s.state, post_loops_state, actor))
        && cr.established_inv(post_loops_state)
        && cr.global_inv(post_loops_state)
        && cr.local_inv(post_loops_state, actor)
        && pc_post_loops == pc
        && stack_post_loops == stack

        // Next, we execute the real step (the guard step).
        && cr.enablement_condition(post_loops_state, actor)
        && ActionTuple(post_loops_state, post_guard_state, guard_step) in cr.spec.next
        && cr.idmap(guard_step).Some?
        && cr.idmap(guard_step).v == actor
        && cr.established_inv(post_guard_state)
        && cr.global_inv(post_guard_state)

        // Finally, we havoc the state subject to the yield predicate
        && cr.yield_pred(post_guard_state, s'.state, actor)
        && s'.visited_loops == s.visited_loops[pc := s.state]
        && cr.established_inv(s'.state)
        && cr.global_inv(s'.state)
    }

    predicate StraightlineSpecNext<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        s:StraightlineState<State, PC>,
        s':StraightlineState<State, PC>,
        step:StraightlineStep<State, Step>,
        actor:Actor,
        proc:ProcName
        )
    {
        match step
           case StraightlineStepStart()
               => StraightlineSpecNextStart(cr, s, s', actor, proc)
           case StraightlineStepNormal(post_stmt_state, lstep)
               => StraightlineSpecNextNormal(cr, s, s', actor, proc, post_stmt_state, lstep)
           case StraightlineStepCall(post_call_state, pre_return_state, post_return_state, call_step, return_step)
               => StraightlineSpecNextCall(cr, s, s', actor, proc, post_call_state, pre_return_state, post_return_state,
                                           call_step, return_step)
           case StraightlineStepLoop(post_loops_state, post_guard_state, guard_step)
               => StraightlineSpecNextLoop(cr, s, s', actor, proc, post_loops_state, post_guard_state, guard_step)
    }

    function GetStraightlineSpec<State(!new), Actor(!new), Step(!new), PC(!new), ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>,
        actor:Actor,
        proc:ProcName
        ) :
        AnnotatedBehaviorSpec<StraightlineState<State, PC>, StraightlineStep<State, Step>>
    {
        AnnotatedBehaviorSpec(iset s | StraightlineSpecInit(cr, s, actor, proc),
                              iset s, s', step | StraightlineSpecNext(cr, s, s', step, actor, proc) :: ActionTuple(s, s', step))
    }

    predicate YieldPredicateReflexive<State(!new), Actor(!new)>(yp:(State, State, Actor)->bool)
    {
        forall s, actor :: yp(s, s, actor)
    }

    predicate YieldPredicateTransitive<State(!new), Actor(!new)>(yp:(State, State, Actor)->bool)
    {
        forall s1, s2, s3, actor :: yp(s1, s2, actor) && yp(s2, s3, actor) ==> yp(s1, s3, actor)
    }

    predicate YieldPredicateDoesntAffectActorInfo<State(!new), Actor, PC>(
        actor_info:State->imap<Actor, PCStack<PC>>,
        yield_pred:(State, State, Actor)->bool
        )
    {
        forall s, s', actor ::
            (actor in actor_info(s) && yield_pred(s, s', actor))
            ==> actor in actor_info(s') && actor_info(s')[actor] == actor_info(s)[actor]
    }

    predicate DesiredInvariantsSatisfiedInitially<State(!new), Actor(!new), Step, PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        && (forall s :: s in cr.spec.init ==> cr.global_inv(s))
        && (forall s, actor :: s in cr.spec.init ==> cr.local_inv(s, actor))
        && (forall s, actor :: s in cr.spec.init && actor in cr.actor_info(s) ==>
               var pc := cr.actor_info(s)[actor].pc;
               var proc := cr.pc_to_proc(pc);
               cr.requires_clauses(proc, s, actor))
    }

    predicate StraightlineSpecSatisfiesGlobalInvariants<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc, s', step ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && var s := last(b.states).state;
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).Some?
             && cr.idmap(step).v == actor
            )
            ==> cr.global_inv(s')
    }

    predicate StraightlineSpecSatisfiesLocalInvariants<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc ::
            AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
            ==> cr.local_inv(last(b.states).state, actor)
    }

    predicate StraightlineSpecSatisfiesEnablementConditions<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc, s', step ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && last(b.states).started
             && var s := last(b.states).state;
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).Some?
             && cr.idmap(step).v == actor
            )
            ==> cr.enablement_condition(last(b.states).state, actor)
    }

    predicate StraightlineSpecSatisfiesPreconditionsForCalls<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc, s', step ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && last(b.states).started
             && var s := last(b.states).state;
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).Some?
             && cr.idmap(step).v == actor
             && actor in cr.actor_info(s)
             && actor in cr.actor_info(s')
             && var pc := cr.actor_info(s)[actor].pc;
             && cr.pc_type(pc).CallSite?
            )
            ==> cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[actor].pc), s', actor)
    }

    predicate StraightlineSpecSatisfiesPreconditionsForForks<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, other_actor, proc, s', step ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && last(b.states).started
             && var s := last(b.states).state;
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).Some?
             && cr.idmap(step).v == actor
             && actor in cr.actor_info(s)
             && actor in cr.actor_info(s')
             && other_actor !in cr.actor_info(s)
             && other_actor in cr.actor_info(s')
             && var pc := cr.actor_info(s)[actor].pc;
             && cr.pc_type(pc).ForkSite?
            )
            ==> cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[other_actor].pc), s', other_actor)
    }

    predicate StraightlineSpecSatisfiesPostconditions<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && last(b.states).started
             && var s := last(b.states).state;
             && actor in cr.actor_info(s)
             && var pc := cr.actor_info(s)[actor].pc;
             && cr.pc_type(pc).ReturnSite?
            )
            ==> cr.ensures_clauses(proc, b.states[0].state, last(b.states).state, actor)
    }

    predicate StraightlineSpecSatisfiesLoopModifiesClausesOnEntry<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && var s := last(b.states).state;
             && actor in cr.actor_info(s)
             && var pc := cr.actor_info(s)[actor].pc;
             && cr.pc_type(pc).LoopHead?
             && pc in cr.loop_modifies_clauses
             && pc !in last(b.states).visited_loops
            )
            ==> var s := last(b.states).state;
                var pc := cr.actor_info(s)[actor].pc;
                cr.loop_modifies_clauses[pc](s, s, actor)
    }

    predicate StraightlineSpecSatisfiesLoopModifiesClausesOnJumpBack<State(!new), Actor(!new), Step(!new), PC, ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && var s := last(b.states).state;
             && actor in cr.actor_info(s)
             && var pc := cr.actor_info(s)[actor].pc;
             && cr.pc_type(pc).LoopHead?
             && pc in cr.loop_modifies_clauses
             && pc in last(b.states).visited_loops
            )
            ==> var s := last(b.states).state;
                var pc := cr.actor_info(s)[actor].pc;
                cr.loop_modifies_clauses[pc](last(b.states).visited_loops[pc], s, actor)
    }

    predicate StraightlineSpecSatisfiesYieldPredicateForOtherActor<State(!new), Actor(!new), Step(!new), PC(!new), ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall b, actor, proc, other_actor, s', step ::
            (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
             && last(b.states).started
             && var s := last(b.states).state;
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).Some?
             && cr.idmap(step).v == actor
             && actor != other_actor)
            ==> cr.yield_pred(last(b.states).state, s', other_actor)
    }

    predicate StraightlineSpecPreservesGlobalInvariantOnTermination<State(!new), Actor(!new), Step(!new), PC(!new), ProcName(!new)>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall s, s', step ::
            (&& cr.established_inv(s)
             && cr.global_inv(s)
             && ActionTuple(s, s', step) in cr.spec.next
             && (forall any_actor :: any_actor !in cr.actor_info(s'))
            )
            ==> cr.global_inv(s')
    }

    predicate StraightlineSpecRequirements<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        && StraightlineSpecSatisfiesGlobalInvariants(cr)
        && StraightlineSpecSatisfiesLocalInvariants(cr)
        && StraightlineSpecSatisfiesEnablementConditions(cr)
        && StraightlineSpecSatisfiesPreconditionsForCalls(cr)
        && StraightlineSpecSatisfiesPreconditionsForForks(cr)
        && StraightlineSpecSatisfiesPostconditions(cr)
        && StraightlineSpecSatisfiesLoopModifiesClausesOnEntry(cr)
        && StraightlineSpecSatisfiesLoopModifiesClausesOnJumpBack(cr)
        && StraightlineSpecSatisfiesYieldPredicateForOtherActor(cr)
        && StraightlineSpecPreservesGlobalInvariantOnTermination(cr)
    }

    predicate ActorlessActionsMaintainYieldPredicateAndGlobalInvariant<State(!new), Actor(!new), Step(!new), PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        forall s, s', step, actor ::
            (&& cr.established_inv(s)
             && cr.global_inv(s)
             && ActionTuple(s, s', step) in cr.spec.next
             && cr.idmap(step).None?)
            ==> && cr.yield_pred(s, s', actor)
                && cr.global_inv(s')
    }

    predicate IsValidConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>(
        cr:ConcurrentHoareLogicRequest<State, Actor, Step, PC, ProcName>
        )
    {
        && IsInvariantPredicateOfSpec(cr.established_inv, cr.spec)
        && SpecSatisfiesProgramControlFlow(cr.spec, cr.idmap, cr.actor_info, cr.pc_to_proc, cr.is_entry_point, cr.pc_type)
        && YieldPredicateReflexive(cr.yield_pred)
        && YieldPredicateTransitive(cr.yield_pred)
        && YieldPredicateDoesntAffectActorInfo(cr.actor_info, cr.yield_pred)
        && ActorlessActionsMaintainYieldPredicateAndGlobalInvariant(cr)
        && DesiredInvariantsSatisfiedInitially(cr)
        && StraightlineSpecRequirements(cr)
    }

}
