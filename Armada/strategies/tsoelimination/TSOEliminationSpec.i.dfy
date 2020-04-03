include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../../util/option.s.dfy"
include "../../spec/refinement.s.dfy"

module TSOEliminationSpecModule {

    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule
    import opened util_option_s

    datatype TSOEliminationRequest<!LState(==), !HState(==), !ThreadID(==), !LStep(==), !HStep(==)> =
        TSOEliminationRequest(
            lspec:AnnotatedBehaviorSpec<LState, LStep>,
            hspec:AnnotatedBehaviorSpec<HState, HStep>,
            relation:RefinementRelation<LState, HState>,
            inv:LState->bool,
            initial_state_refiner:LState->HState,
            step_refiner:(LState,HState,LStep)->HStep,
            next_state:(HState,HStep)->HState, // computes next state given current state and next step
            intermediate_relation:(LState, HState)->bool
            )

    predicate InitialConditionsHold<LState(!new), HState, ThreadID(!new), LStep, HStep>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>
        )
    {
        forall ls :: ls in ter.lspec.init ==> var hs := ter.initial_state_refiner(ls);
                                       && hs in ter.hspec.init
                                       && ter.intermediate_relation(ls, hs)
    }

    predicate IntermediateRelationImpliesRelation<LState(!new), HState(!new), ThreadID, LStep, HStep>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>
        )
    {
        forall ls, hs :: ter.intermediate_relation(ls, hs) ==> RefinementPair(ls, hs) in ter.relation
    }

    predicate StepMaintainsRelation<LState(!new), HState(!new), ThreadID(!new), LStep(!new), HStep(!new)>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>
        )
    {
        forall ls, ls', lstep, hs ::
            && ter.inv(ls)
            && ter.intermediate_relation(ls, hs)
            && ActionTuple(ls, ls', lstep) in ter.lspec.next
            ==> var hstep := ter.step_refiner(ls, hs, lstep);
                var hs' := ter.next_state(hs, hstep);
                && ActionTuple(hs, hs', hstep) in ter.hspec.next
                && ter.intermediate_relation(ls', hs')
    }
    
    predicate ValidTSOEliminationRequest<LState(!new), HState(!new), ThreadID(!new), LStep(!new), HStep(!new)>(
        ter:TSOEliminationRequest<LState, HState, ThreadID, LStep, HStep>
        )
    {
        && IsInvariantPredicateOfSpec(ter.inv, ter.lspec)
        && InitialConditionsHold(ter)
        && IntermediateRelationImpliesRelation(ter)
        && StepMaintainsRelation(ter)
    }
    
}
