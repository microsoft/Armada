include "SharedStructs.dfy"
include "A.dfy"
include "B.dfy"
include "../../Armada/strategies/weakening/Weakening.i.dfy"
include "../../Armada/strategies/refinement/AnnotatedBehavior.i.dfy"
include "../../Armada/util/option.s.dfy"
include "../../Armada/util/collections/seqs.s.dfy"
include "../../Armada/util/collections/seqs.i.dfy"
include "../../Armada/util/collections/sets.i.dfy"
include "../../Armada/util/collections/maps.i.dfy"

module AB {
 import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

  import opened GeneralRefinementModule = GeneralRefinementModule

  import L = A

  import H = B

  import opened AnnotatedBehaviorModule = AnnotatedBehaviorModule

  import opened SharedStructs = SharedStructs

  import opened InvariantsModule = InvariantsModule

  import opened WeakeningSpecModule = WeakeningSpecModule

  import opened WeakeningModule = WeakeningModule

  import opened util_option_s = util_option_s

  import opened util_collections_seqs_s = util_collections_seqs_s

  import opened util_collections_seqs_i = util_collections_seqs_i

  import opened util_collections_sets_i = util_collections_sets_i

  import opened util_collections_maps_i = util_collections_maps_i
  datatype MyInt = MyInt(x: int)

  type LState = L.Armada_TotalState

  type HState = H.Armada_TotalState

  type LStep = L.Armada_StepSequence

  type HStep = H.Armada_StepSequence

  type LSpec = AnnotatedBehaviorSpec<LState, LStep>

  type HSpec = AnnotatedBehaviorSpec<HState, HStep>

  type LConfig = L.Armada_Config

  type WRequest = WeakeningRequest<LState, HState, LStep, HStep>

  predicate LHStateRefinement(ls: LState, hs: HState)
  {
    && (hs.ok ==>
      ls.ok)
    && ls.log <= hs.log
  }

  function GetLHRefinementRelation(): RefinementRelation<LState, HState>
  {
    iset p: RefinementPair<LState, HState> | LHStateRefinement(p.low, p.high)
  }

  function GetLSpec(): LSpec
  {
    AnnotatedBehaviorSpec(iset s, config | L.Armada_Init(s, config) :: s, iset s, s', entry | L.Armada_Next(s, s', entry) :: ActionTuple(s, s', entry))
  }

  function GetHSpec_State(): HSpec
  {
     AnnotatedBehaviorSpec(iset s, config | H.Armada_Init(s, config) :: s, iset s, s', entry | H.Armada_Next(s, s', entry) :: ActionTuple(s, s', entry))
  }

  function GetHSpec(): HSpec
  {
    AnnotatedBehaviorSpec(iset s, config | H.Armada_Init(s, config) :: s, iset s, s', entry | H.Armada_Next(s, s', entry) :: ActionTuple(s, s', entry))
  }

  lemma lemma_GetLAnnotatedBehavior(lb: seq<L.Armada_TotalState>) returns (alb: AnnotatedBehavior<LState, LStep>)
    requires BehaviorSatisfiesSpec(lb, L.Armada_Spec())
    ensures AnnotatedBehaviorSatisfiesSpec(alb, GetLSpec())
    ensures alb.states == lb
  {
    if |lb| == 1 {
      return AnnotatedBehavior(lb, []);
    }
    var pos := |lb| - 2;
    var alb_prev := lemma_GetLAnnotatedBehavior(all_but_last(lb));
    assert 0 <= pos < |lb| - 1;
    assert StatePair(lb[pos], lb[pos + 1]) in L.Armada_Spec().next;
    var entry :| L.Armada_Next(lb[pos], lb[pos + 1], entry);
    alb := AnnotatedBehavior(lb, alb_prev.trace + [entry]);
  }

  predicate InductiveInv(s: LState)
  {
    true
  }

  lemma lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(hb: AnnotatedBehavior<HState, HStep>)
    requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
    ensures BehaviorSatisfiesSpec(hb.states, H.Armada_Spec())
  {
    var b := hb.states;
    forall i | 0 <= i < |b| - 1
      ensures StatePair(b[i], b[i + 1]) in H.Armada_Spec().next
    {
      assert ActionTuple(hb.states[i], hb.states[i + 1], hb.trace[i]) in GetHSpec().next;
    }
  }

  function ConvertPC_LH(pc: L.Armada_PC): H.Armada_PC
  {
    match pc
    case Armada_PC_None =>
      H.Armada_PC_None
    case Armada_PC_0_main =>
      H.Armada_PC_0_main
    case Armada_PC_1_main =>
      H.Armada_PC_1_main
    case Armada_PC_2_main =>
      H.Armada_PC_2_main
  }

  function ConvertStackFrame_LH(frame: L.Armada_StackFrame): H.Armada_StackFrame
  {
    match frame
    case Armada_StackFrame_main =>
      H.Armada_StackFrame_main()
  }

  function ConvertRegions_LH(regions: L.Armada_Regions): H.Armada_Regions
  {
    H.Armada_Regions(regions.default)
  }

  function ConvertRegionID_LH(regionID: L.Armada_RegionID): H.Armada_RegionID
  {
    match regionID
    case Armada_RegionID_default =>
      H.Armada_RegionID_default
  }

  function ConvertGlobals_LH(globals: L.Armada_Globals): H.Armada_Globals
  {
    H.Armada_Globals(globals.x)
  }

  function ConvertGhosts_LH(ghosts: L.Armada_Ghosts): H.Armada_Ghosts
  {
    H.Armada_Ghosts()
  }

  function ConvertAddrs_LH(addrs: L.Armada_Addrs): H.Armada_Addrs
  {
    H.Armada_Addrs()
  }

  function ConvertGlobalStaticVar_LH(v: L.Armada_GlobalStaticVar): H.Armada_GlobalStaticVar
  {
    match v
    case Armada_GlobalStaticVarNone =>
      H.Armada_GlobalStaticVarNone
    case Armada_GlobalStaticVar_x =>
      H.Armada_GlobalStaticVar_x
  }

  function ConvertSharedMemory_LH(mem: L.Armada_SharedMemory): H.Armada_SharedMemory
  {
    H.Armada_SharedMemory(ConvertRegions_LH(mem.regions), ConvertGlobals_LH(mem.globals))
  }

  function ConvertStoreBufferLocation_LH(loc: L.Armada_StoreBufferLocation): H.Armada_StoreBufferLocation
  {
    match loc
    case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
      H.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_LH(v), fields)
    case Armada_StoreBufferLocation_Addressable(p, r) =>
      H.Armada_StoreBufferLocation_Addressable(p, ConvertRegionID_LH(r))
  }

  predicate CanConvertGlobalStaticVar_LH(v: L.Armada_GlobalStaticVar)
  {
    true
  }

  predicate CanConvertStoreBufferLocation_LH(loc: L.Armada_StoreBufferLocation)
  {
    loc.Armada_StoreBufferLocation_Unaddressable? ==>
      CanConvertGlobalStaticVar_LH(loc.v)
  }

  predicate CanConvertStoreBufferEntry_LH(entry: L.Armada_StoreBufferEntry)
  {
    CanConvertStoreBufferLocation_LH(entry.loc)
  }


  function ConvertStoreBufferEntry_LH(entry: L.Armada_StoreBufferEntry): H.Armada_StoreBufferEntry
  {
    H.Armada_StoreBufferEntry(ConvertStoreBufferLocation_LH(entry.loc), entry.value)
  }

  function ConvertStoreBuffer_LH(entries: seq<L.Armada_StoreBufferEntry>): seq<H.Armada_StoreBufferEntry>
  {
    MapSeqToSeq(entries, ConvertStoreBufferEntry_LH)
  }

  function ConvertSnapshot_LH(snap: L.Armada_Snapshot): H.Armada_Snapshot
  {
    H.Armada_Snapshot(ConvertStackFrame_LH(snap.top), ConvertSharedMemory_LH(snap.mem), ConvertGhosts_LH(snap.ghosts))
  }

  function ConvertExtendedFrame_LH(eframe: L.Armada_ExtendedFrame): H.Armada_ExtendedFrame
  {
    H.Armada_ExtendedFrame(ConvertPC_LH(eframe.return_pc), ConvertStackFrame_LH(eframe.frame), ConvertSnapshot_LH(eframe.snap), eframe.new_ptrs)
  }

  function ConvertStack_LH(stack: seq<L.Armada_ExtendedFrame>): seq<H.Armada_ExtendedFrame>
  {
    MapSeqToSeq(stack, ConvertExtendedFrame_LH)
  }

  function ConvertThread_LH(t: L.Armada_Thread): H.Armada_Thread
  {
    H.Armada_Thread(ConvertPC_LH(t.pc), ConvertStackFrame_LH(t.top), ConvertSnapshot_LH(t.snap), t.new_ptrs, ConvertStack_LH(t.stack), ConvertStoreBuffer_LH(t.storeBuffer))
  }

  function ConvertThreads_LH(threads: map<Armada_ThreadHandle, L.Armada_Thread>): map<Armada_ThreadHandle, H.Armada_Thread>
  {
    MapMapToMap(threads, ConvertThread_LH)
  }

  function ConvertTotalState_LH(s: L.Armada_TotalState): H.Armada_TotalState
  {
    H.Armada_TotalState(s.ok, s.log, ConvertThreads_LH(s.threads), ConvertSharedMemory_LH(s.mem), ConvertGhosts_LH(s.ghosts), ConvertAddrs_LH(s.addrs))
  }

  function ConvertConfig_LH(config: L.Armada_Config): H.Armada_Config
  {
    H.Armada_Config(config.tid_init, config.new_ptrs)
  }

  function ConvertTraceEntry_LH(entry: L.Armada_TraceEntry): H.Armada_TraceEntry
  {
    match entry
    case Armada_TraceEntry_Update_0_main(tid: Armada_ThreadHandle) =>
      H.Armada_TraceEntry_Update_0_main(tid)
    case Armada_TraceEntry_Update_1_main(tid: Armada_ThreadHandle) =>
      H.Armada_TraceEntry_Update_1_main(tid)
    case Armada_TraceEntry_Terminate_main(tid: Armada_ThreadHandle) =>
      H.Armada_TraceEntry_Terminate_main(tid)
    case Armada_TraceEntry_Tau(tid: Armada_ThreadHandle) =>
      H.Armada_TraceEntry_Tau(tid)
  }

  function ConvertStepSequence_LH(entry: LStep): HStep
  {
    H.Armada_StepSequence(entry.tau, entry.tid, MapSeqToSeq(entry.steps, ConvertTraceEntry_LH))
  }

  function GetWeakeningRequest(): WRequest
  {
    WeakeningRequest(GetLSpec(), GetHSpec(), GetLHRefinementRelation(), iset ls | InductiveInv(ls) :: ls, ConvertTotalState_LH, ConvertStepSequence_LH)
  }

  lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem: L.Armada_SharedMemory, lentry: L.Armada_StoreBufferEntry, hentry: H.Armada_StoreBufferEntry, hmem1: H.Armada_SharedMemory, hmem2: H.Armada_SharedMemory)
    requires hentry == ConvertStoreBufferEntry_LH(lentry)
    requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry))
    requires hmem2 == H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry)
    ensures hmem1 == hmem2
  {
  }

    lemma lemma_ApplyStoreBufferCommutesWithConvert(lmem: L.Armada_SharedMemory, lbuf: seq<L.Armada_StoreBufferEntry>, hbuf: seq<H.Armada_StoreBufferEntry>, hmem1: H.Armada_SharedMemory, hmem2: H.Armada_SharedMemory)
    requires hbuf == ConvertStoreBuffer_LH(lbuf)
    requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBuffer(lmem, lbuf))
    requires hmem2 == H.Armada_ApplyStoreBuffer(ConvertSharedMemory_LH(lmem), hbuf)
    ensures hmem1 == hmem2
    decreases |lbuf| + |hbuf|
  {
    if |lbuf| == 0 {
      return;
    }
    var lmem' := L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]);
    var hmem1' := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
    var hmem2' := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hbuf[0]);
    lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
    lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
  }

  lemma lemma_GetThreadLocalViewCommutesWithConvert(ls: LState, hs: HState, tid: Armada_ThreadHandle)
    requires hs == ConvertTotalState_LH(ls)
    requires tid in ls.threads
    ensures ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(hs, tid)
  {
    assert tid in hs.threads;
    lemma_ApplyStoreBufferCommutesWithConvert(ls.mem, ls.threads[tid].storeBuffer, hs.threads[tid].storeBuffer, ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)), H.Armada_GetThreadLocalView(hs, tid));
  }

  lemma lemma_GetThreadLocalViewAlwaysCommutesWithConvert()
    ensures forall ls: L.Armada_TotalState, tid: Armada_ThreadHandle :: tid in ls.threads ==> ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
  {
    forall ls: L.Armada_TotalState, tid: Armada_ThreadHandle | tid in ls.threads
      ensures ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
    {
      var hs := ConvertTotalState_LH(ls);
      lemma_GetThreadLocalViewCommutesWithConvert(ls, hs, tid);
    }
  }

  lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
    ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)} :: true ==> H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) == ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
  {
  }

  lemma lemma_LiftNext_Update_0_main(wr: WRequest, ls: LState, ls':LState, lstep: L.Armada_TraceEntry)
    requires wr == GetWeakeningRequest()
    requires L.Armada_NextOneStep(ls, ls', lstep)
    requires lstep.Armada_TraceEntry_Update_0_main?
    ensures H.Armada_NextOneStep(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), ConvertTraceEntry_LH(lstep))
  {
    var hs := wr.converter(ls);
    var hs' := wr.converter(ls');
    var tid := lstep.tid;
    var hstep := ConvertTraceEntry_LH(lstep);
    lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
    lemma_StoreBufferAppendAlwaysCommutesWithConvert();
    assert H.Armada_ValidStep_Update_0_main(hs, tid);
    if L.Armada_CrashAvoidance_Update_0_main(ls, tid) {
      assert H.Armada_CrashAvoidance_Update_0_main(hs, tid);
      var alt_hs' := H.Armada_GetNextState_Update_0_main(hs, tid);
      assert hs'.ok == alt_hs'.ok;
      assert hs'.log == alt_hs'.log;
      if tid in hs'.threads {
        assert hs'.threads[tid] == alt_hs'.threads[tid];
      }
      assert hs'.threads == alt_hs'.threads;
      assert hs'.mem == alt_hs'.mem;
      assert hs' == alt_hs';
      assert H.Armada_Next_Update_0_main(hs, hs', tid);
    } else {
      assert !H.Armada_CrashAvoidance_Update_0_main(hs, tid);
    }
  }

  lemma lemma_LiftNext_Update_1_main(wr: WRequest, ls: LState, ls':LState, lentry: L.Armada_TraceEntry)
    requires wr == GetWeakeningRequest()
    requires L.Armada_NextOneStep(ls, ls', lentry)
    requires lentry.Armada_TraceEntry_Update_1_main?
    ensures H.Armada_NextOneStep(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), ConvertTraceEntry_LH(lentry))
  {
    var hs := wr.converter(ls);
    var hs' := wr.converter(ls');
    var tid := lentry.tid;
    var hstep := ConvertTraceEntry_LH(lentry);
    lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
    lemma_StoreBufferAppendAlwaysCommutesWithConvert();
    assert H.Armada_ValidStep_Update_1_main(hs, tid);
    if L.Armada_CrashAvoidance_Update_1_main(ls, tid) {
      assert H.Armada_CrashAvoidance_Update_1_main(hs, tid);
      var alt_hs' := H.Armada_GetNextState_Update_1_main(hs, tid);
      assert hs'.ok == alt_hs'.ok;
      assert hs'.log == alt_hs'.log;
      if tid in hs'.threads {
        assert hs'.threads[tid] == alt_hs'.threads[tid];
      }
      assert hs'.threads == alt_hs'.threads;
      assert hs'.mem == alt_hs'.mem;
      assert hs' == alt_hs';
      assert H.Armada_Next_Update_1_main(hs, hs', tid);
    } else {
      assert !H.Armada_CrashAvoidance_Update_1_main(hs, tid);
    }
  }

  lemma lemma_LiftNext_Terminate_main(wr: WRequest, ls: LState, ls':LState, lstep: L.Armada_TraceEntry)
    requires wr == GetWeakeningRequest()
    requires L.Armada_NextOneStep(ls, ls', lstep)
    requires lstep.Armada_TraceEntry_Terminate_main?
    ensures H.Armada_NextOneStep(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), ConvertTraceEntry_LH(lstep))
  {
    var hs := wr.converter(ls);
    var hs' := wr.converter(ls');
    var tid := lstep.tid;
    var hstep := ConvertTraceEntry_LH(lstep);
    lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
    lemma_StoreBufferAppendAlwaysCommutesWithConvert();
    assert H.Armada_ValidStep_Terminate_main(hs, tid);
    if L.Armada_CrashAvoidance_Terminate_main(ls, tid) {
      assert H.Armada_CrashAvoidance_Terminate_main(hs, tid);
      var alt_hs' := H.Armada_GetNextState_Terminate_main(hs, tid);
      assert hs'.ok == alt_hs'.ok;
      assert hs'.log == alt_hs'.log;
      if tid in hs'.threads {
        assert hs'.threads[tid] == alt_hs'.threads[tid];
      }
      assert hs'.threads == alt_hs'.threads;
      assert hs'.mem == alt_hs'.mem;
      assert hs' == alt_hs';
      assert H.Armada_Next_Terminate_main(hs, hs', tid);
    } else {
      assert !H.Armada_CrashAvoidance_Terminate_main(hs, tid);
    }

  }

  lemma lemma_LiftNext_Tau(wr: WRequest, ls: LState, ls':LState, lstep: L.Armada_TraceEntry)
    requires wr == GetWeakeningRequest()
    requires L.Armada_NextOneStep(ls, ls', lstep)
    requires lstep.Armada_TraceEntry_Tau?
    ensures H.Armada_NextOneStep(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), ConvertTraceEntry_LH(lstep))
  {
    var hs := wr.converter(ls);
    var hs' := wr.converter(ls');
    var tid := lstep.tid;
    var hstep := ConvertTraceEntry_LH(lstep);
    var lentry := ls.threads[tid].storeBuffer[0];
    assert H.Armada_ValidStep_Tau(hs, tid);
    assert H.Armada_CrashAvoidance_Tau(hs, tid);
    var hentry := hs.threads[tid].storeBuffer[0];
    var lmem := ls.mem;
    var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
    var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
    lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);
    var alt_hs' := H.Armada_GetNextState_Tau(hs, tid);
    assert hmem1 == hmem2;
    assert hs'.threads[tid].storeBuffer == alt_hs'.threads[tid].storeBuffer;
    assert hs'.threads[tid] == alt_hs'.threads[tid];
    assert hs'.threads == alt_hs'.threads;
    assert hs' == alt_hs';
    assert H.Armada_Next_Tau(hs, hs', tid);
  }

  lemma lemma_LNextOneImpliesHNextOne(ls:LState, ls':LState, hs:HState, hs':HState,
    lentry:L.Armada_TraceEntry, hentry:H.Armada_TraceEntry)
    
    requires L.Armada_NextOneStep(ls, ls', lentry)
    requires hs == ConvertTotalState_LH(ls)
    requires hs' == ConvertTotalState_LH(ls')
    requires hentry == ConvertTraceEntry_LH(lentry)
    ensures H.Armada_NextOneStep(hs, hs', hentry)
  {
    var wr := GetWeakeningRequest();
    match lentry {
      case Armada_TraceEntry_Update_0_main(tid: Armada_ThreadHandle) =>
        lemma_LiftNext_Update_0_main(wr, ls, ls', lentry);
      case Armada_TraceEntry_Update_1_main(tid: Armada_ThreadHandle) =>
        lemma_LiftNext_Update_1_main(wr, ls, ls', lentry);
      case Armada_TraceEntry_Terminate_main(tid: Armada_ThreadHandle) =>
        lemma_LiftNext_Terminate_main(wr, ls, ls', lentry);
      case Armada_TraceEntry_Tau(tid: Armada_ThreadHandle) =>
        lemma_LiftNext_Tau(wr, ls, ls', lentry);
    }
  }

  lemma lemma_LNextMultipleImpliesHNextMultiple(wr: WRequest, ls: LState, ls': LState, steps: seq<L.Armada_TraceEntry>)
    requires wr == GetWeakeningRequest()
    requires ls in wr.inv
    requires L.Armada_NextMultipleSteps(ls, ls', steps)
    ensures H.Armada_NextMultipleSteps(ConvertTotalState_LH(ls),  ConvertTotalState_LH(ls'), MapSeqToSeq(steps, ConvertTraceEntry_LH))
    decreases |steps|
  {
    if |steps| == 0 {
      return;
    }

    var ls_next := L.Armada_GetNextStateAlways(ls, steps[0]);
    var hs, hs_next, hs' := ConvertTotalState_LH(ls), ConvertTotalState_LH(ls_next), ConvertTotalState_LH(ls');
    var hsteps := MapSeqToSeq(steps, ConvertTraceEntry_LH);
    
    lemma_LNextMultipleImpliesHNextMultiple(wr, ls_next, ls', steps[1..]);
    assert H.Armada_NextMultipleSteps(ConvertTotalState_LH(ls_next), ConvertTotalState_LH(ls'), MapSeqToSeq(steps[1..], ConvertTraceEntry_LH));
    assert MapSeqToSeq(steps[1..], ConvertTraceEntry_LH) == MapSeqToSeq(steps, ConvertTraceEntry_LH)[1..] == hsteps[1..];
    assert H.Armada_NextMultipleSteps(hs_next, hs', hsteps[1..]); 
    lemma_LNextOneImpliesHNextOne(ls, ls_next, hs, hs_next, steps[0], hsteps[0]); 
  }

  lemma lemma_IntermediateStatesNonyielding(wr: WRequest, ls: LState, ls': LState, hs: HState, hs': HState, lsteps: seq<L.Armada_TraceEntry>, hsteps: seq<H.Armada_TraceEntry>, tid: Armada_ThreadHandle, tau: bool, lstates: seq<L.Armada_TotalState>)
    requires wr == GetWeakeningRequest()
    requires ls in wr.inv
    requires L.Armada_NextMultipleSteps(ls, ls', lsteps)
    requires tid in ls.threads ==> !L.Armada_IsNonyieldingPC(ls.threads[tid].pc)
    requires tid in ls'.threads ==> !L.Armada_IsNonyieldingPC(ls'.threads[tid].pc)
    requires forall step :: step in lsteps ==> step.tid == tid
    requires forall step :: step in lsteps ==> step.Armada_TraceEntry_Tau? == tau
    requires lstates == L.Armada_GetStateSequence(ls, lsteps)
    requires forall i :: 0 < i < |lsteps| ==> tid in lstates[i].threads && L.Armada_IsNonyieldingPC(lstates[i].threads[tid].pc)
    requires hs == ConvertTotalState_LH(ls)
    requires hs' == ConvertTotalState_LH(ls')
    requires hsteps == MapSeqToSeq(lsteps, ConvertTraceEntry_LH)
    requires H.Armada_NextMultipleSteps(hs, hs', hsteps)
    requires forall step :: step in hsteps ==> step.tid == tid
    requires forall step :: step in hsteps ==> step.Armada_TraceEntry_Tau? == tau
    ensures var hstates := H.Armada_GetStateSequence(hs, hsteps); forall i :: 0 < i < |hsteps| ==> tid in hstates[i].threads && H.Armada_IsNonyieldingPC(hstates[i].threads[tid].pc)
    ensures tid in hs'.threads ==> !H.Armada_IsNonyieldingPC(hs'.threads[tid].pc)
  {
  }

  lemma lemma_LNextImpliesHNext(ls:LState, ls':LState, lstep:LStep)
    requires L.Armada_Next(ls, ls', lstep)
    ensures H.Armada_Next(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), GetWeakeningRequest().step_refiner(lstep))
  {
    var hs, hs' := ConvertTotalState_LH(ls), ConvertTotalState_LH(ls');
    var hstep := GetWeakeningRequest().step_refiner(lstep);

    lemma_LNextMultipleImpliesHNextMultiple(GetWeakeningRequest(), ls, ls', lstep.steps);
    assert H.Armada_NextMultipleSteps(ConvertTotalState_LH(ls), ConvertTotalState_LH(ls'), hstep.steps);

    assert (hstep.tid in hs.threads ==>
      !H.Armada_IsNonyieldingPC(hs.threads[hstep.tid].pc));

    assert (hstep.tid in hs'.threads ==>
      !H.Armada_IsNonyieldingPC(hs'.threads[hstep.tid].pc));

    assert (forall step :: 
      step in hstep.steps ==>
      step.tid == hstep.tid);

    var states := H.Armada_GetStateSequence(hs, hstep.steps);

    assert (forall step :: 
      step in lstep.steps ==>
      step.Armada_TraceEntry_Tau? == lstep.tau);

    forall i |
      0 <= i < |hstep.steps|
      ensures hstep.steps[i].Armada_TraceEntry_Tau? == hstep.tau
    {
      assert lstep.steps[i].Armada_TraceEntry_Tau? == lstep.tau;
      assert hstep.steps[i].Armada_TraceEntry_Tau? == lstep.steps[i].Armada_TraceEntry_Tau?;
    }

    var wr := GetWeakeningRequest();
    lemma_IntermediateStatesNonyielding(wr, ls, ls', hs, hs', lstep.steps, hstep.steps, lstep.tid, lstep.tau, L.Armada_GetStateSequence(ls, lstep.steps));
  }

  lemma lemma_AllActionsLiftableWeakened()
    ensures WeakeningSpecModule.AllActionsLiftableWeakened(GetWeakeningRequest())
  {
    var wr := GetWeakeningRequest();

    forall s, s', lstep |
      && ActionTuple(s, s', lstep) in wr.lspec.next
      && s in wr.inv
      ensures ActionTuple(wr.converter(s), wr.converter(s'), wr.step_refiner(lstep)) in wr.hspec.next;
    {
      lemma_LNextImpliesHNext(s, s', lstep);
    }
  }

  lemma lemma_LInitImpliesHInit(ls:LState, hs:HState, lconf:L.Armada_Config, hconf:H.Armada_Config)
    requires L.Armada_Init(ls, lconf)
    requires hs == ConvertTotalState_LH(ls)
    requires hconf == ConvertConfig_LH(lconf)
    ensures H.Armada_Init(hs, hconf)
  {
  }

  lemma lemma_InitStatesEquivalent(wr:WRequest)
    requires wr == GetWeakeningRequest()
    ensures InitStatesEquivalent(wr)
  {
    forall initial_ls | initial_ls in wr.lspec.init
      ensures wr.converter(initial_ls) in wr.hspec.init
    {
      assert exists config :: L.Armada_Init(initial_ls, config);
      var lconf :| L.Armada_Init(initial_ls, lconf);
      lemma_LInitImpliesHInit(initial_ls, ConvertTotalState_LH(initial_ls), lconf, ConvertConfig_LH(lconf));
    }
  }

  lemma lemma_ProveRefinementViaVarHiding()
    ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
  {
    var lspec := L.Armada_Spec();
    var hspec := H.Armada_Spec();
    var wr := GetWeakeningRequest();
    
    forall lb | BehaviorSatisfiesSpec(lb, lspec)
      ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
    {
      var alb := lemma_GetLAnnotatedBehavior(lb);

      lemma_InitStatesEquivalent(wr);
      lemma_AllActionsLiftableWeakened();
      
      assert ValidWeakeningRequest(wr);
      var ahb := lemma_PerformWeakening(wr, alb);
      lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
    }
  }
}
