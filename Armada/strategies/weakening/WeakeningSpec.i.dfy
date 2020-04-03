include "../refinement/AnnotatedBehavior.i.dfy"
include "../../spec/refinement.s.dfy"
include "../invariants.i.dfy"

module WeakeningSpecModule {

    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule


    datatype WeakeningRequest<!LState(==), HState(==), !LStep(==), HStep(==)> =
        WeakeningRequest(
            lspec:AnnotatedBehaviorSpec<LState, LStep>,
            hspec:AnnotatedBehaviorSpec<HState, HStep>,
            relation:RefinementRelation<LState, HState>,
            inv:iset<LState>,
            converter:(LState)->HState,
            step_refiner:(LStep)->HStep
            )


    predicate ConvertingSatisfiesRelation<LState(!new), HState, LStep, HStep>(wr:WeakeningRequest<LState, HState, LStep, HStep>)
    {
        forall ls :: ls in wr.inv ==> RefinementPair(ls, wr.converter(ls)) in wr.relation
    }

    predicate AllActionsLiftableWeakened<LState(!new), HState(!new), LStep(!new), HStep(!new)>(wr:WeakeningRequest<LState, HState, LStep, HStep>)
    {
        forall s, s', lstep ::
            && ActionTuple(s, s', lstep) in wr.lspec.next
            && s in wr.inv
            ==> ActionTuple(wr.converter(s), wr.converter(s'), wr.step_refiner(lstep)) in wr.hspec.next
    }

    predicate InitStatesEquivalent<LState(!new), HState(!new), LStep(!new), HStep(!new)>(wr:WeakeningRequest<LState, HState, LStep, HStep>)
    {
      forall initial_ls | initial_ls in wr.lspec.init ::
        wr.converter(initial_ls) in wr.hspec.init
    }

    predicate ValidWeakeningRequest<LState, HState, LStep, HStep>(wr:WeakeningRequest<LState, HState, LStep, HStep>)
    {
      && InitStatesEquivalent(wr)
      && IsInvariantOfSpec(wr.inv, wr.lspec)
      && AllActionsLiftableWeakened(wr)
      && ConvertingSatisfiesRelation(wr)
    }

}
