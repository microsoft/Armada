include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../../spec/refinement.s.dfy"
include "../../util/collections/maps.s.dfy"

module VarIntroSpecModule {

    import opened util_collections_maps_s
    import opened AnnotatedBehaviorModule
    import opened InvariantsModule
    import opened GeneralRefinementModule

    datatype VarIntroRequest<!LState(==), !HState(==), !LStep(==), !HStep(==)> =
        VarIntroRequest(
            lspec:AnnotatedBehaviorSpec<LState, LStep>,
            hspec:AnnotatedBehaviorSpec<HState, HStep>,
            relation:RefinementRelation<LState, HState>,
            inv:HState->bool,                  // invariant of the high-level state
            hider:HState->LState,              // hides values of introduced variables
            revealer:LState->HState,           // only matters for initial state, introduces values for introduced variables
            step_mapper:LStep->HStep,          // maps a low-level step to a high-level one
            next_state:(HState,HStep)->HState, // computes next state given current state and next step
            at_new_instruction:HState->bool,   // whether the PC is just before a new instruction (an assignment to an introduced variable)
            next_step:HState->HStep,           // only matters when at_new_instruction, returns the step for that new instruction
            progress_measure:HState->int       // only matters when at_new_instruction, must decrease by executing the new instruction
            )

    predicate WhenAtNewInstructionNextStepMakesProgress<LState(!new), HState(!new), LStep(!new), HStep(!new)>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>)
    {
        forall hs :: vr.inv(hs) && vr.at_new_instruction(hs)
                ==> var hstep := vr.next_step(hs);
                    var hs' := vr.next_state(hs, hstep);
                    && vr.inv(hs')
                    && vr.hider(hs) == vr.hider(hs')
                    && ActionTuple(hs, hs', hstep) in vr.hspec.next
                    && 0 <= vr.progress_measure(hs') < vr.progress_measure(hs)
    }

    predicate WhenNotAtNewInstructionActionIsLiftable<LState(!new), HState(!new), LStep(!new), HStep(!new)>(
        vr:VarIntroRequest<LState, HState, LStep, HStep>)
    {
        forall ls, ls', hs, lstep ::
            && ActionTuple(ls, ls', lstep) in vr.lspec.next
            && vr.inv(hs)
            && ls == vr.hider(hs)
            && !vr.at_new_instruction(hs)
            ==> var hstep := vr.step_mapper(lstep);
                var hs' := vr.next_state(hs, hstep);
                && vr.inv(hs')
                && ls' == vr.hider(hs')
                && ActionTuple(hs, hs', hstep) in vr.hspec.next
    }

    predicate IntroSatisfiesRelation<LState, HState(!new), LStep, HStep>(vr:VarIntroRequest<LState, HState, LStep, HStep>)
    {
        forall s :: vr.inv(s) ==> RefinementPair(vr.hider(s), s) in vr.relation
    }

    predicate IntroPreservesInit<LState, HState, LStep, HStep>(vr:VarIntroRequest<LState, HState, LStep, HStep>)
    {
        forall ls :: ls in vr.lspec.init ==> var hs := vr.revealer(ls); vr.hider(hs) == ls && vr.inv(hs) && hs in vr.hspec.init
    }

    predicate ValidVarIntroRequest<LState, HState, LStep, HStep>(vr:VarIntroRequest<LState, HState, LStep, HStep>)
    {
        && WhenAtNewInstructionNextStepMakesProgress(vr)
        && WhenNotAtNewInstructionActionIsLiftable(vr)
        && IntroSatisfiesRelation(vr)
        && IntroPreservesInit(vr)
    }

}
