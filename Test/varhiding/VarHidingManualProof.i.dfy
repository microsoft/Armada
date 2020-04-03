include "A.dfy"
include "B.dfy"
include "../../Armada/strategies/VarHiding/VarHiding.i.dfy"
include "../../Armada/strategies/refinement/AnnotatedBehavior.i.dfy"
include "../../Armada/util/option.s.dfy"
include "../../Armada/util/collections/seqs.s.dfy"
include "../../Armada/util/collections/seqs.i.dfy"
include "../../Armada/util/collections/sets.i.dfy"
include "../../Armada/util/collections/maps.i.dfy"

module AB {
    import A
    import B
    import opened ArmadaCommonDefinitions
    import opened InvariantsModule
    import opened VarHidingSpecModule
    import opened VarHidingModule
    import opened util_option_s
    import opened util_collections_seqs_s
    import opened util_collections_seqs_i
    import opened util_collections_sets_i
    import opened util_collections_maps_i
    import opened GeneralRefinementModule
    import opened AnnotatedBehaviorModule

    function ConvertPC_AB(pc:A.Armada_PC) : B.Armada_PC
    {
        match pc
            case Armada_PC_None => B.Armada_PC_None
            case Armada_PC_main'0 => B.Armada_PC_main'0
            case Armada_PC_main'1 => B.Armada_PC_main'1
            case Armada_PC_main'2 => B.Armada_PC_main'2
            case Armada_PC_main'3 => B.Armada_PC_main'2
    }

    function ConvertStackFrame_AB(frame:A.Armada_StackFrame) : B.Armada_StackFrame
    {
        match frame
            case Armada_StackFrame_main() => B.Armada_StackFrame_main()
    }

    function ConvertFieldType_AB(fieldType:A.Armada_FieldType) : (result:B.Armada_FieldType)
        ensures ConvertFieldType_BA(result) == fieldType
    {
        match fieldType
            case Armada_FieldTypeNone => B.Armada_FieldTypeNone
    }

    function ConvertFieldType_BA(fieldType:B.Armada_FieldType) : A.Armada_FieldType
    {
        match fieldType
            case Armada_FieldTypeNone => A.Armada_FieldTypeNone
    }

    lemma lemma_ConvertFieldTypeIsBijective()
        ensures Inverses(ConvertFieldType_AB, ConvertFieldType_BA)
    {
        forall a:A.Armada_FieldType
            ensures ConvertFieldType_BA(ConvertFieldType_AB(a)) == a
        {
            match a {
                case Armada_FieldTypeNone => assert ConvertFieldType_BA(ConvertFieldType_AB(a)) == a;
            }
        }

        forall b:B.Armada_FieldType
            ensures ConvertFieldType_AB(ConvertFieldType_BA(b)) == b
        {
            match b {
                case Armada_FieldTypeNone => assert ConvertFieldType_AB(ConvertFieldType_BA(b)) == b;
            }
        }
    }

    function ConvertStructType_AB(structType:A.Armada_StructType) : B.Armada_StructType
    {
        match structType
            case Armada_StructTypeNone => B.Armada_StructTypeNone
    }

    function ConvertObjectType_AB(objectType:A.Armada_ObjectType) : B.Armada_ObjectType
    {
        match objectType
            case Armada_ObjectType_primitive(pty) => Armada_ObjectType_primitive(pty)
            case Armada_ObjectType_struct(s) => Armada_ObjectType_struct(ConvertStructType_AB(s))
            case Armada_ObjectType_array(subtype, sz) => Armada_ObjectType_array(ConvertObjectType_AB(subtype), sz)
    }

    function ConvertField_AB(field:A.Armada_Field) : (result:B.Armada_Field)
    {
        match field
            case Armada_FieldNone => Armada_FieldNone
            case Armada_FieldArrayIndex(i) => Armada_FieldArrayIndex(i)
            case Armada_FieldStruct(f) => Armada_FieldStruct(ConvertFieldType_AB(f))
    }

    function ConvertField_BA(field:B.Armada_Field) : A.Armada_Field
    {
        match field
            case Armada_FieldNone => Armada_FieldNone
            case Armada_FieldArrayIndex(i) => Armada_FieldArrayIndex(i)
            case Armada_FieldStruct(f) => Armada_FieldStruct(ConvertFieldType_BA(f))
    }

    function ConvertFieldSeq_AB(fields:seq<A.Armada_Field>) : seq<B.Armada_Field>
    {
        MapSeqToSeq(fields, ConvertField_AB)
    }

    lemma lemma_ConvertFieldIsBijective()
        ensures Inverses(ConvertField_AB, ConvertField_BA)
    {
        lemma_ConvertFieldTypeIsBijective();
    }

    function ConvertChildren_AB(children:map<A.Armada_Field, Armada_Pointer>) : map<B.Armada_Field, Armada_Pointer>
    {
        lemma_ConvertFieldIsBijective();
        Map2MapToMap(children, ConvertField_AB, ConvertField_BA, p=>p)
    }

    function ConvertNode_AB(node:A.Armada_Node) : B.Armada_Node
    {
        Armada_Node(node.parent, ConvertField_AB(node.field_of_parent), ConvertChildren_AB(node.children),
                    ConvertObjectType_AB(node.ty), node.level)
    }

    function ConvertTree_AB(tree:map<Armada_Pointer, A.Armada_Node>) : map<Armada_Pointer, B.Armada_Node>
    {
        MapMapToMap(tree, ConvertNode_AB)
    }

    function ConvertHeap_AB(heap:A.Armada_Heap) : B.Armada_Heap
    {
        Armada_Heap(ConvertTree_AB(heap.tree), heap.valid, heap.freed, heap.values)
    }

    function ConvertRegions_AB(regions:A.Armada_Regions) : B.Armada_Regions
    {
        B.Armada_Regions(ConvertHeap_AB(regions.default))
    }

    function ConvertRegionID_AB(regionID:A.Armada_RegionID) : B.Armada_RegionID
    {
        match regionID
            case Armada_RegionID_default => B.Armada_RegionID_default
    }

    function ConvertGlobals_AB(globals:A.Armada_Globals) : B.Armada_Globals
    {
        B.Armada_Globals(globals.x, globals.y)
    }

    function ConvertSnapshot_AB(snap:A.Armada_Snapshot) : B.Armada_Snapshot
    {
        B.Armada_Snapshot(ConvertStackFrame_AB(snap.top), ConvertRegions_AB(snap.regions), ConvertGlobals_AB(snap.globals))
    }

    function ConvertExtendedFrame_AB(eframe:A.Armada_ExtendedFrame) : B.Armada_ExtendedFrame
    {
        B.Armada_ExtendedFrame(ConvertPC_AB(eframe.return_pc), ConvertStackFrame_AB(eframe.frame), ConvertSnapshot_AB(eframe.snap))
    }

    function ConvertStack_AB(stack:seq<A.Armada_ExtendedFrame>) : seq<B.Armada_ExtendedFrame>
    {
        MapSeqToSeq(stack, ConvertExtendedFrame_AB)
    }

    predicate CanConvertStoreBufferEntry_AB(entry:A.Armada_StoreBufferEntry)
    {
        entry.Armada_StoreBufferEntry_Unaddressable? ==> CanConvertGlobalStaticVar_AB(entry.v)
    }

    function ConvertStoreBufferEntry_AB(entry:A.Armada_StoreBufferEntry) : B.Armada_StoreBufferEntry
        requires CanConvertStoreBufferEntry_AB(entry)
    {
        match entry
            case Armada_StoreBufferEntry_Unaddressable(v, fields, value) =>
                B.Armada_StoreBufferEntry_Unaddressable(ConvertGlobalStaticVar_AB(v), ConvertFieldSeq_AB(fields), value)
            case Armada_StoreBufferEntry_Addressable(p, region, value) =>
                B.Armada_StoreBufferEntry_Addressable(p, ConvertRegionID_AB(region), value)
    }

    function ConvertStoreBuffer_AB(entries:seq<A.Armada_StoreBufferEntry>) : seq<B.Armada_StoreBufferEntry>
    {
        FilterMapSeqToSeq(entries, e => if CanConvertStoreBufferEntry_AB(e) then Some(ConvertStoreBufferEntry_AB(e)) else None)
    }

    function ConvertThread_AB(t:A.Armada_Thread) : B.Armada_Thread
    {
        B.Armada_Thread(ConvertPC_AB(t.pc), ConvertStackFrame_AB(t.top), ConvertSnapshot_AB(t.snap), ConvertStack_AB(t.stack),
                        ConvertStoreBuffer_AB(t.storeBuffer))
    }

    function ConvertThreads_AB(threads:map<Armada_ThreadHandle, A.Armada_Thread>) : map<Armada_ThreadHandle, B.Armada_Thread>
    {
        MapMapToMap(threads, ConvertThread_AB)
    }

    predicate CanConvertGlobalStaticVar_AB(v:A.Armada_GlobalStaticVar)
    {
        !v.Armada_GlobalStaticVar_z?
    }

    function ConvertGlobalStaticVar_AB(v:A.Armada_GlobalStaticVar) : B.Armada_GlobalStaticVar
        requires CanConvertGlobalStaticVar_AB(v)
    {
        match v
            case Armada_GlobalStaticVarNone => B.Armada_GlobalStaticVarNone
            case Armada_GlobalStaticVar_x => B.Armada_GlobalStaticVar_x
            case Armada_GlobalStaticVar_y => B.Armada_GlobalStaticVar_y
    }

    function ConvertTS_AB(s:A.Armada_TotalState) : B.Armada_TotalState
    {
        B.Armada_TotalState(s.ok, s.log, ConvertThreads_AB(s.threads), ConvertRegions_AB(s.regions), ConvertGlobals_AB(s.globals))
    }

    function ConvertConfig_AB(config:A.Armada_Config) : B.Armada_Config
    {
        B.Armada_Config(config.tid_init)
    }

    function ConvertTraceEntry_AB(entry:A.Armada_TraceEntry) : B.Armada_TraceEntry
    {
        match entry
            case Armada_TraceEntry_Armada_PC_main'0(tid) => B.Armada_TraceEntry_Armada_PC_main'0(tid)
            case Armada_TraceEntry_Armada_PC_main'1(tid) => B.Armada_TraceEntry_Armada_PC_main'1(tid)
            case Armada_TraceEntry_Armada_PC_main'2(tid) =>
               // The mapping of this step is arbitrary since it's going to be turned into a stutter step.
               // So we arbitrarily map it to the start step of the program.
               B.Armada_TraceEntry_Armada_PC_main'0(tid)
            case Armada_TraceEntry_Terminate'main(tid) => B.Armada_TraceEntry_Terminate'main(tid)
            case Armada_TraceEntry_Tau(tid) => B.Armada_TraceEntry_Tau(tid)
    }

    type LState = A.Armada_TotalState
    type HState = B.Armada_TotalState
    type LStep = A.Armada_TraceEntry
    type HStep = B.Armada_TraceEntry
    type LSpec = AnnotatedBehaviorSpec<LState, LStep>
    type HSpec = AnnotatedBehaviorSpec<HState, HStep>
    type LConfig = A.Armada_Config
    type HConfig = B.Armada_Config
    type VHRequest = VarHidingRequest<LState, HState, LStep, HStep>

    function GetVarHidingInvariant() : iset<LState>
    {
        iset s | true
    }

    function GetLSpec() : LSpec
    {
        AnnotatedBehaviorSpec(iset s, config | A.Armada_Init(s, config) :: s,
                              iset s, s', entry | A.Armada_Next(s, s', entry) :: ActionTuple(s, s', entry))
    }

    function GetHSpec() : HSpec
    {
        AnnotatedBehaviorSpec(iset s, config | B.Armada_Init(s, config) :: s,
                              iset s, s', entry | B.Armada_Next(s, s', entry) :: ActionTuple(s, s', entry))
    }

    predicate ABStateRefinement(ls:LState, hs:HState)
    {
        && (ls.ok ==> hs.ok)
        && ls.log <= hs.log
    }

    function GetABRefinementRelation() : RefinementRelation<LState, HState>
    {
        iset p:RefinementPair<LState, HState> | ABStateRefinement(p.low, p.high)
    }

    function GetVarHidingRequest() : VHRequest
    {
        VarHidingRequest(GetLSpec(), GetHSpec(), GetABRefinementRelation(), GetVarHidingInvariant(), ConvertTS_AB, ConvertTraceEntry_AB)
    }

    lemma lemma_IsInvariantOfSpec(vr:VHRequest)
        requires vr == GetVarHidingRequest()
        ensures  IsInvariantOfSpec(vr.inv, vr.lspec)
    {
    }

    lemma lemma_HidingSatisfiesRelation(vr:VHRequest)
        requires vr == GetVarHidingRequest()
        ensures  HidingSatisfiesRelation(vr)
    {
    }

    lemma lemma_HidingPreservesInit_HeapInvariant(vr:VHRequest, ls:LState, hs:HState, lconfig:LConfig, hconfig:HConfig)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Init(ls, lconfig)
        requires hs == vr.hider(ls)
        requires hconfig == ConvertConfig_AB(lconfig)
        ensures  B.Armada_HeapInvariant(hs.regions.default)
    {
        var ltree := ls.regions.default.tree;
        var htree := hs.regions.default.tree;

        forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} |
            Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in htree && f in htree[p].children
            ensures var q := htree[p].children[f]; q in htree && htree[q].parent == p && htree[q].field_of_parent == f
        {
            assert Armada_TriggerField(ConvertField_BA(f));
        }
        forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} |
            Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in htree && htree[p].ty.Armada_ObjectType_array? && f in htree[p].children
            ensures f.Armada_FieldArrayIndex? && 0 <= f.i < htree[p].ty.sz
        {
            assert Armada_TriggerField(ConvertField_BA(f));
        }
        forall p, f {:trigger Armada_TriggerPointer(p), Armada_TriggerField(f)} |
            Armada_TriggerPointer(p) && Armada_TriggerField(f) && p in htree && htree[p].ty.Armada_ObjectType_primitive?
            ensures f !in htree[p].children
        {
            assert Armada_TriggerField(ConvertField_BA(f));
        }
        forall q {:trigger Armada_TriggerPointer(q)} |
           Armada_TriggerPointer(q) && q in htree && !htree[q].field_of_parent.Armada_FieldNone?
           ensures var p, f := htree[q].parent, htree[q].field_of_parent; p in htree && f in htree[p].children && htree[p].children[f] == q
       {
           assert Armada_TriggerPointer(q) && q in ltree && !ltree[q].field_of_parent.Armada_FieldNone?;
           var p, f := ltree[q].parent, ltree[q].field_of_parent;
           assert p in ltree && f in ltree[p].children && ltree[p].children[f] == q;
       }
    }

    lemma lemma_HidingPreservesInit(vr:VHRequest)
        requires vr == GetVarHidingRequest()
        ensures  HidingPreservesInit(vr)
    {
        forall ls | ls in vr.lspec.init
            ensures vr.hider(ls) in vr.hspec.init
        {
            var lconfig :| A.Armada_Init(ls, lconfig);
            var hs := vr.hider(ls);
            var hconfig := ConvertConfig_AB(lconfig);

            lemma_HidingPreservesInit_HeapInvariant(vr, ls, hs, lconfig, hconfig);
            assert B.Armada_Init(hs, hconfig);
        }
    }

    lemma lemma_LiftNext_Armada_PC_main'0(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Next(ls, ls', lstep)
        requires lstep.Armada_TraceEntry_Armada_PC_main'0?
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        var hs := vr.hider(ls);
        var hs' := vr.hider(ls');
        var tid := lstep.tid;

        assert hs'.threads == hs.threads[tid := hs'.threads[tid]];
    }

    lemma lemma_LiftNext_Armada_PC_main'1(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Next(ls, ls', lstep)
        requires lstep.Armada_TraceEntry_Armada_PC_main'1?
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        var hs := vr.hider(ls);
        var hs' := vr.hider(ls');
        var tid := lstep.tid;

        assert hs'.threads == hs.threads[tid := hs'.threads[tid]];
    }

    lemma lemma_LiftNext_Armada_PC_main'2(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Next(ls, ls', lstep)
        requires lstep.Armada_TraceEntry_Armada_PC_main'2?
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        var hs := vr.hider(ls);
        var hs' := vr.hider(ls');
        var tid := lstep.tid;

        assert hs'.threads[tid] == hs.threads[tid];
        assert hs'.threads == hs.threads;
        assert hs' == hs;
        assert false;
    }

    lemma lemma_LiftNext_Tau(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Next(ls, ls', lstep)
        requires lstep.Armada_TraceEntry_Tau?
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        var hs := vr.hider(ls);
        var hs' := vr.hider(ls');
        var tid := lstep.tid;

        var entry := ls.threads[tid].storeBuffer[0];
        if entry.Armada_StoreBufferEntry_Unaddressable? && entry.v.Armada_GlobalStaticVar_z? {
            assert hs'.threads[tid].storeBuffer == hs.threads[tid].storeBuffer;
            assert hs'.threads[tid] == hs.threads[tid];
            assert hs'.threads == hs.threads;
            assert hs.ok;
            assert hs' == hs;
            assert false;
        }
        else {
            assert hs'.threads[tid].storeBuffer == hs.threads[tid].storeBuffer[1..];
            assert hs'.threads[tid] == hs.threads[tid].(storeBuffer := hs'.threads[tid].storeBuffer);
            assert hs'.threads == hs.threads[tid := hs'.threads[tid]];
            assert B.Armada_Next_Tau(hs, hs', tid);
        }
    }

    lemma lemma_LiftNext_Terminate'main(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires A.Armada_Next(ls, ls', lstep)
        requires lstep.Armada_TraceEntry_Terminate'main?
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        var hs := vr.hider(ls);
        var hs' := vr.hider(ls');
        var tid := lstep.tid;

        var hs'_alt := B.Armada_GetNextState_Terminate'main(hs, tid);
        assert hs'.threads == hs'_alt.threads;
        assert hs' == hs'_alt;
        assert B.Armada_Next_Terminate'main(hs, hs', tid);
    }

    lemma lemma_LiftActionWithoutVariable(vr:VHRequest, ls:LState, ls':LState, lstep:LStep)
        requires vr == GetVarHidingRequest()
        requires ls in vr.inv
        requires ActionTuple(ls, ls', lstep) in vr.lspec.next
        requires vr.hider(ls) != vr.hider(ls')
        ensures  ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(lstep)) in vr.hspec.next
    {
        match lstep {
            case Armada_TraceEntry_Armada_PC_main'0(_) =>
                lemma_LiftNext_Armada_PC_main'0(vr, ls, ls', lstep);
            case Armada_TraceEntry_Armada_PC_main'1(_) =>
                lemma_LiftNext_Armada_PC_main'1(vr, ls, ls', lstep);
            case Armada_TraceEntry_Armada_PC_main'2(_) =>
                lemma_LiftNext_Armada_PC_main'2(vr, ls, ls', lstep);
            case Armada_TraceEntry_Tau(_) =>
                lemma_LiftNext_Tau(vr, ls, ls', lstep);
            case Armada_TraceEntry_Terminate'main(_) =>
                lemma_LiftNext_Terminate'main(vr, ls, ls', lstep);
        }
    }

    lemma lemma_AllActionsLiftableWithoutVariable(vr:VHRequest)
        requires vr == GetVarHidingRequest()
        ensures  AllActionsLiftableWithoutVariable(vr)
    {
        forall s, s', lstep |
            && ActionTuple(s, s', lstep) in vr.lspec.next
            && s in vr.inv
            && vr.hider(s) != vr.hider(s')
            ensures ActionTuple(vr.hider(s), vr.hider(s'), vr.step_refiner(lstep)) in vr.hspec.next
        {
            lemma_LiftActionWithoutVariable(vr, s, s', lstep);
        }
    }

    lemma lemma_ValidVarHidingRequest(vr:VHRequest)
        requires vr == GetVarHidingRequest()
        ensures  ValidVarHidingRequest(vr)
    {
        lemma_IsInvariantOfSpec(vr);
        lemma_AllActionsLiftableWithoutVariable(vr);
        lemma_HidingSatisfiesRelation(vr);
        lemma_HidingPreservesInit(vr);
    }

    lemma lemma_GetLAnnotatedBehavior(lb:seq<A.Armada_TotalState>) returns (alb:AnnotatedBehavior<LState, LStep>)
        requires BehaviorSatisfiesSpec(lb, A.Armada_Spec())
        ensures  AnnotatedBehaviorSatisfiesSpec(alb, GetLSpec())
        ensures  alb.states == lb
    {
        if |lb| == 1 {
            return AnnotatedBehavior(lb, []);
        }

        var pos := |lb|-2;
        var alb_prev := lemma_GetLAnnotatedBehavior(all_but_last(lb));
        assert 0 <= pos < |lb|-1;
        assert StatePair(lb[pos], lb[pos+1]) in A.Armada_Spec().next;
        var entry :| A.Armada_Next(lb[pos], lb[pos+1], entry);
        alb := AnnotatedBehavior(lb, alb_prev.trace + [entry]);
    }

    lemma lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(hb:AnnotatedBehavior<HState, HStep>)
        requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
        ensures  BehaviorSatisfiesSpec(hb.states, B.Armada_Spec())
    {
        var b := hb.states;

        forall i | 0 <= i < |b|-1
            ensures StatePair(b[i], b[i+1]) in B.Armada_Spec().next
        {
            assert ActionTuple(hb.states[i], hb.states[i+1], hb.trace[i]) in GetHSpec().next;
        }
    }

    lemma lemma_ProveRefinementViaVarHiding()
        ensures SpecRefinesSpec(A.Armada_Spec(), B.Armada_Spec(), GetABRefinementRelation())
    {
        var lspec := A.Armada_Spec();
        var hspec := B.Armada_Spec();
        var vr := GetVarHidingRequest();

        forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, vr.relation)
        {
            var alb := lemma_GetLAnnotatedBehavior(lb);
            lemma_ValidVarHidingRequest(vr);
            var ahb := lemma_PerformVarHiding(vr, alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, vr.relation);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
        }
    }
}
