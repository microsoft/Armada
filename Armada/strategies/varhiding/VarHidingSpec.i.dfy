include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../../spec/refinement.s.dfy"
include "../../util/collections/maps.s.dfy"

module VarHidingSpecModule {

    import opened util_collections_maps_s
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule

    datatype VarHidingRequest<!LState(==), HState(==), !LStep(==), HStep(==)> =
        VarHidingRequest(
            lspec:AnnotatedBehaviorSpec<LState, LStep>,
            hspec:AnnotatedBehaviorSpec<HState, HStep>,
            relation:RefinementRelation<LState, HState>,
            inv:LState->bool,
            hider:LState->HState,
            step_refiner:(LState,LStep)->HStep
            )

    predicate AllActionsLiftableWithoutVariable<LState(!new), HState(!new), LStep(!new), HStep(!new)>(
        vr:VarHidingRequest<LState, HState, LStep, HStep>)
    {
        forall s, s', lstep ::
            && ActionTuple(s, s', lstep) in vr.lspec.next
            && vr.inv(s)
            && vr.hider(s) != vr.hider(s')
            ==> ActionTuple(vr.hider(s), vr.hider(s'), vr.step_refiner(s, lstep)) in vr.hspec.next
    }

    predicate HidingSatisfiesRelation<LState(!new), HState, LStep, HStep>(vr:VarHidingRequest<LState, HState, LStep, HStep>)
    {
        forall s :: vr.inv(s) ==> RefinementPair(s, vr.hider(s)) in vr.relation
    }

    predicate HidingPreservesInit<LState, HState, LStep, HStep>(vr:VarHidingRequest<LState, HState, LStep, HStep>)
    {
        forall s :: s in vr.lspec.init ==> vr.hider(s) in vr.hspec.init
    }

    predicate ValidVarHidingRequest<LState, HState, LStep, HStep>(vr:VarHidingRequest<LState, HState, LStep, HStep>)
    {
        && IsInvariantPredicateOfSpec(vr.inv, vr.lspec)
        && AllActionsLiftableWithoutVariable(vr)
        && HidingSatisfiesRelation(vr)
        && HidingPreservesInit(vr)
    }

}
