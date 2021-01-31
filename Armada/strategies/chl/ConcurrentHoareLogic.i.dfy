include "ConcurrentHoareLogicLemmas.i.dfy"

module ConcurrentHoareLogicModule {

  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened util_collections_seqs_s
  import opened util_option_s
  import opened ConcurrentHoareLogicSpecModule
  import opened ConcurrentHoareLogicLemmasModule

  lemma lemma_CHLGlobalInvariantHoldsWhenActorPresent<State, Actor, Step, PC, Proc>(
    cr: ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b: AnnotatedBehavior<State, Step>,
    pos: int,
    actor: Actor
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 <= pos < |b.states|
    requires cr.get_actor_pc_stack(b.states[pos], actor).Some?
    requires cr.state_ok(b.states[pos])
    ensures  cr.global_inv(b.states[pos])
  {
    var pc := cr.get_actor_pc_stack(b.states[pos], actor).v.pc;
    var proc := cr.pc_to_proc(pc);
    var overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos, actor, proc);
    lemma_StraightlineBehaviorSatisfiesGlobalInvariant(cr, overlay.sb, actor, proc, |overlay.sb.states| - 1);
  }

  lemma lemma_CHLLocalInvariantHoldsWhenActorAboutToStep<State, Actor, Step, PC, Proc>(
    cr: ConcurrentHoareLogicRequest<State, Actor, Step, PC, Proc>,
    b: AnnotatedBehavior<State, Step>,
    pos: int,
    actor: Actor
    )
    requires IsValidConcurrentHoareLogicRequest(cr)
    requires AnnotatedBehaviorSatisfiesSpec(b, cr.spec)
    requires 0 <= pos < |b.trace|
    requires cr.step_to_actor(b.trace[pos]).Some?
    ensures  cr.local_inv(b.states[pos], cr.step_to_actor(b.trace[pos]).v)
  {
    var s := b.states[pos];
    var s' := b.states[pos + 1];
    var step := b.trace[pos];
    assert ActionTuple(s, s', step) in cr.spec.next;

    var actor := cr.step_to_actor(step).v;
    var effect := cr.step_to_effect(step);
    var PCStack(pc, stack) := cr.get_actor_pc_stack(s, actor).v;
    var proc := cr.pc_to_proc(pc);
    var overlay := lemma_GetStraightlineBehaviorForCurrentProc(cr, b, pos, actor, proc);
    assert AnnotatedBehaviorSatisfiesSpec(overlay.sb, GetStraightlineSpec(cr, actor, proc));
    assert StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, overlay.sb, step, s');
  }

}
