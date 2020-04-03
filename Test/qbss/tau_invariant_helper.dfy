include "QueueBSS_WithAbstractQueue.dfy"
include "UseAbstractQueueForLog/specs.dfy"
include "SharedStructs.dfy"
include "auxiliary_helper.dfy"
include "queue_abstractloginvariant.dfy"
// include "../../Armada/util/math/mod_auto.i.dfy"
include "mod_auto_cheat.dfy"


  module tau_invariant_helper {
import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions
import opened QueueBSS_WithAbstractQueue = QueueBSS_WithAbstractQueue
import opened ArmadaModule_specs = ArmadaModule_specs
import opened queue_abstractloginvariant = queue_abstractloginvariant
import opened Math__mod_auto_i = Math__mod_auto_i
import opened SharedStructs = SharedStructs
import opened auxiliary_helper = auxiliary_helper

lemma {:verify false} ApplyStoreBufferMaintainsWeakHeapInvariant(mem: L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, mem':L.Armada_SharedMemory)
 requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
 requires WeakHeapInvariant(mem.heap)
 ensures WeakHeapInvariant(mem'.heap)
 decreases |buf|
{
  if |buf| > 0 {
    var mem_next := Armada_ApplyStoreBufferEntry(mem, buf[0]);
    assert WeakHeapInvariant(mem_next.heap);
    var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
    ApplyStoreBufferMaintainsWeakHeapInvariant(mem_next, buf[1..], mem_next');
  }
}

lemma {:verify false} ApplyStoreBufferMaintainsWeakHeapInvariantAlways()
 ensures forall mem : L.Armada_SharedMemory, buf : seq<L.Armada_StoreBufferEntry> :: 
 && WeakHeapInvariant(mem.heap)
 ==> WeakHeapInvariant(L.Armada_ApplyStoreBuffer(mem, buf).heap)
{
  forall mem : L.Armada_SharedMemory, buf : seq<L.Armada_StoreBufferEntry> | && WeakHeapInvariant(mem.heap)
    ensures WeakHeapInvariant(L.Armada_ApplyStoreBuffer(mem, buf).heap)
    {
      ApplyStoreBufferMaintainsWeakHeapInvariant(mem, buf, L.Armada_ApplyStoreBuffer(mem, buf));
    }
}

lemma {:verify false} lemma_HeapMetaDataUnchanged_PrimitiveProperties()
  ensures forall h, h', p :: Armada_TriggerPointer(p) && Armada_HeapMetadataUnchangedByTau(h, h') ==> (
  Armada_ValidPointerToPrimitive(h, p, Armada_PrimitiveType_uint64) ==> Armada_ValidPointerToPrimitive(h', p, Armada_PrimitiveType_uint64)
  )
{
  
}

lemma {:verify false} lemma_HeapmetaDataUnchangedProperties()
  ensures forall h, h', p :: Armada_TriggerPointer(p) && Armada_HeapMetadataUnchangedByTau(h, h') ==> (
  Armada_ValidPointerToStructArray_BSSQueueElement(h, p) <==> Armada_ValidPointerToStructArray_BSSQueueElement(h', p)
  )
{
  forall h, h', p : Armada_Pointer |
    && Armada_TriggerPointer(p)
    && Armada_HeapMetadataUnchangedByTau(h, h')
    ensures (Armada_ValidPointerToStructArray_BSSQueueElement(h, p) ==> Armada_ValidPointerToStructArray_BSSQueueElement(h', p))
  {
    if (Armada_ValidPointerToStructArray_BSSQueueElement(h, p))
    {
      forall i |
        0 <= i < h.tree[p].ty.sz

        ensures Armada_ValidPointerToStruct_BSSQueueElement(h', h'.tree[p].children[Armada_FieldArrayIndex(i)])
      {
        var idx := Armada_FieldArrayIndex(i);
        assert Armada_TriggerField(idx);
        assert idx in h'.tree[p].children;
        lemma_HeapMetaDataUnchanged_PrimitiveProperties();
        assert Armada_ValidPointerToStruct_BSSQueueElement(h', h'.tree[p].children[idx]);
      }
      // && var ty := h.tree[p].ty; ty.Armada_ObjectType_array? && ty.subtype.Armada_ObjectType_struct? && ty.subtype.s.Armada_StructType_BSSQueueElement? && ty.sz >= 0 && forall i :: 0 <= i < ty.sz ==> var idx := Armada_FieldArrayIndex(i); Armada_TriggerField(idx) && idx in h.tree[p].children && Armada_ValidPointerToStruct_BSSQueueElement(h, h.tree[p].children[idx])

      assert Armada_ValidPointerToStructArray_BSSQueueElement(h', p);
    }
  }
}

lemma {:verify false} lemma_ApplyStoreBufferMaintainsMemorySafety(mem:Armada_SharedMemory, buf:seq<Armada_StoreBufferEntry>, mem':Armada_SharedMemory)
  requires WeakHeapInvariant(mem.heap)
  requires WeakHeapInvariant(mem'.heap)
  requires MemorySafetyElementArray(mem)
  requires mem'.globals.queue.number_elements == mem.globals.queue.number_elements
  requires mem'.globals.queue.element_array == mem.globals.queue.element_array
  requires mem'.heap.tree == mem.heap.tree
  requires mem'.heap.valid == mem.heap.valid
  requires mem'.heap.freed == mem.heap.freed

  ensures MemorySafetyElementArray(mem')
{
  var e' := mem'.globals.queue.element_array;
  var a' := mem'.heap.tree[e'].parent;
  assert Armada_TriggerPointer(a');
  lemma_HeapmetaDataUnchangedProperties();

  // assert Armada_ValidPointerToStructSizedArray_BSSQueueElement(mem'.heap, a', mem.globals.queue.number_elements as int);
  /*
  assert forall i :: 0 <= i < s'.s.mem.globals.queue.number_elements as int ==> Armada_TriggerField<Armada_FieldType>(Armada_FieldArrayIndex(i));
  assert s'.s.mem.heap.tree == locv'.heap.tree;
  assert Armada_ValidPointerToStructArray_BSSQueueElement(locv'.heap, a');
  assert Armada_ValidPointerToStructSizedArray_BSSQueueElement(locv'.heap, a', s'.s.mem.globals.queue.number_elements as int);
   */
}

lemma lemma_ApplyStoreBufferPreservesValuesMetadata(mem:Armada_SharedMemory, buf:seq<Armada_StoreBufferEntry>, mem':Armada_SharedMemory)
  requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
  ensures forall p :: p in mem.heap.values ==> p in mem'.heap.values;
  ensures forall p :: p in mem.heap.values && mem.heap.values[p].Armada_PrimitiveValue_uint64?
    ==> p in mem'.heap.values && mem'.heap.values[p].Armada_PrimitiveValue_uint64?;
{
  if |buf| > 0 {
    var mem_next := Armada_ApplyStoreBufferEntry(mem, buf[0]);
    var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);

    assert forall p :: p in mem.heap.values ==> p in mem_next.heap.values;
    assert forall p :: p in mem.heap.values && mem.heap.values[p].Armada_PrimitiveValue_uint64?
      ==> p in mem_next.heap.values && mem_next.heap.values[p].Armada_PrimitiveValue_uint64?;

    ApplyStoreBufferMaintainsWeakHeapInvariant(mem_next, buf[1..], mem_next');
  }
}

lemma lemma_DequeueDoesNotConcernImpliesElementArrayLocalMatchesGlobal(s:LPlusState, s':LPlusState, step: L.Armada_TraceEntry)
  requires WeakeningInvariant_ext(s)
  requires step.Armada_TraceEntry_Tau?
  requires LPlus_NextOneStep(s, s', step)
  ensures DequeueDoesNotConcernQbssElement(s') && ElementArrayDeqLocalMatchesGlobal(s')
{
  lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame();
  lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways();
  ApplyStoreBufferMaintainsWeakHeapInvariantAlways();

  forall tid | tid in s'.s.threads && tid != step.tid
    && s'.s.threads[tid].top.Armada_StackFrame_dequeue?
    ensures ElementArrayLocalViewMatchesGlobal(s', tid)
    {
      forall j |
        0 <= j < s.s.mem.globals.queue.number_elements as int
        && Queue_TriggerIndex(j)
        ensures StoreBufferDoesNotConcernQbssElement(s'.s.threads[tid].storeBuffer, s'.s.mem, j)
      {
        assert StoreBufferDoesNotConcernQbssElement(s.s.threads[tid].storeBuffer, s.s.mem, j);
      }
      assert DequeueDoesNotConcernQbssElement(s');

      var locv' := L.Armada_GetThreadLocalView(s'.s, tid);

      var buf := s'.s.threads[tid].storeBuffer;
      assume |buf| > 0;

      assert WeakHeapInvariant(s'.s.mem.heap);
      lemma_ApplyStoreBufferPreservesValuesMetadata(s'.s.mem, buf, locv');
      assert forall p :: p in s'.s.mem.heap.values ==> p in locv'.heap.values;
      assert forall p :: p in s'.s.mem.heap.values && s'.s.mem.heap.values[p].Armada_PrimitiveValue_uint64?
        ==> p in locv'.heap.values && locv'.heap.values[p].Armada_PrimitiveValue_uint64?;

      assert Armada_HeapMetadataUnchangedByTau(s'.s.mem.heap, locv'.heap);
      assert WeakHeapInvariant(locv'.heap);
      assert MemorySafetyElementArray(s'.s.mem);
      assert locv'.globals.queue.number_elements as int == s'.s.mem.globals.queue.number_elements as int;
      assert locv'.globals.queue.element_array as int == s'.s.mem.globals.queue.element_array as int;

      assert MemorySafetyElementArray(locv');

      forall j |
        0 <= j < s'.s.mem.globals.queue.number_elements as int
        && Queue_TriggerIndex(j)
        ensures GetQbssElement(locv', j) == GetQbssElement(s'.s.mem, j)
      {
        assert StoreBufferDoesNotConcernQbssElement(buf, s'.s.mem, j);
        assert StoreBufferDoesNotConcernAddress(buf, GetPointerToQbssElementKey(s'.s.mem, j));
        assert StoreBufferDoesNotConcernAddress(buf, GetPointerToQbssElementValue(s'.s.mem, j));

        lemma_IfStoreBufferDoesNotConcernAddressThenViewMatchesAlways(GetPointerToQbssElementKey(s'.s.mem, j));
        lemma_IfStoreBufferDoesNotConcernAddressThenViewMatchesAlways(GetPointerToQbssElementValue(s'.s.mem, j));
      }
    }
}

    lemma {:verify false} lemma_InvariantPredicateMaintainedByNext_WeakeningInvariant_Tau_dequeue(s: LPlusState, s': LPlusState, step: L.Armada_TraceEntry)
      requires WeakeningInvariant_ext(s)
      requires step.Armada_TraceEntry_Tau?
      requires LPlus_NextOneStep(s, s', step)
      requires s.s.threads[step.tid].top.Armada_StackFrame_dequeue?
      ensures WeakeningInvariant_ext(s')
    {
      // assert s'.s.mem.globals.queue.read_index == s.s.mem.globals.queue.read_index;
      // assert s'.s.mem.globals.queue.element_array == s.s.mem.globals.queue.element_array;

      lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame();
      lemma_mod_auto(s.s.mem.globals.queue.number_elements as int);
      lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways();
      lemma_DequeueDoesNotConcernImpliesElementArrayLocalMatchesGlobal(s, s', step);

      assert forall entry :: entry in s'.s.threads[step.tid].storeBuffer ==> entry in s.s.threads[step.tid].storeBuffer;
      assert s'.s.mem.globals.queue.number_elements == s.s.mem.globals.queue.number_elements;
      assert WeakeningInvariant_ext(s');
    }

    lemma {:verify false} lemma_Tau_enqueue_maintains_AuxDescribesStoreBuffer(s: LPlusState, s': LPlusState, step: L.Armada_TraceEntry)
      requires AuxDescribesStoreBuffer(s)
      requires ThreadsInv(s)
      requires step.Armada_TraceEntry_Tau?
      requires LPlus_NextOneStep(s, s', step)
      requires s.s.threads[step.tid].top.Armada_StackFrame_enqueue?
      ensures AuxDescribesStoreBuffer(s');
    {
      var tid1 := step.tid;
      if s.w_i_seq != []
      {
        if s.w_i_seq[0].position > 0 {

          forall i | 0 <= i < |s'.s.threads[tid1].storeBuffer|
            && s'.s.threads[tid1].storeBuffer[i].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
            ensures
            && s'.s.threads[tid1].storeBuffer[i].value.Armada_PrimitiveValue_uint64?
            && WriteIndexSBEntry(i, s'.s.threads[tid1].storeBuffer[i].value.n_uint64) in s'.w_i_seq
          {
            var sb' := s'.s.threads[tid1].storeBuffer;
            var sb := s.s.threads[tid1].storeBuffer;
            // assert sb'[i] == sb[i + 1];
            // assert sb[i + 1].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)]);

            // assert sb[i + 1].value.Armada_PrimitiveValue_uint64?;
            // assert WriteIndexSBEntry(i + 1, sb'[i].value.n_uint64) in s.w_i_seq;
            assert DecrementPosition(WriteIndexSBEntry(i + 1, sb'[i].value.n_uint64)) in s'.w_i_seq;
            // assert WriteIndexSBEntry(i, sb'[i].value.n_uint64) in s'.w_i_seq;
          }

          assert AuxDescribesStoreBuffer(s');
        }
        else {
          forall i | 0 <= i < |s'.s.threads[tid1].storeBuffer|
            && s'.s.threads[tid1].storeBuffer[i].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
            ensures
            && s'.s.threads[tid1].storeBuffer[i].value.Armada_PrimitiveValue_uint64?
            && WriteIndexSBEntry(i, s'.s.threads[tid1].storeBuffer[i].value.n_uint64) in s'.w_i_seq
          {
            var sb' := s'.s.threads[tid1].storeBuffer;
            var sb := s.s.threads[tid1].storeBuffer;
            // assert sb'[i] == sb[i + 1];
            // assert sb[i + 1].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)]);

            // assert sb[i + 1].value.Armada_PrimitiveValue_uint64?;
            // assert WriteIndexSBEntry(i + 1, sb'[i].value.n_uint64) in s.w_i_seq;
            assert DecrementPosition(WriteIndexSBEntry(i + 1, sb'[i].value.n_uint64)) in s'.w_i_seq;
            // assert WriteIndexSBEntry(i, sb'[i].value.n_uint64) in s'.w_i_seq;
          }

          assert AuxDescribesStoreBuffer(s');
        }
      }
    }

    lemma {:verify false} lemma_InvariantPredicateMaintainedByNext_WeakeningInvariant_Tau_enqueue(s: LPlusState, s': LPlusState, step: L.Armada_TraceEntry)
      requires WeakeningInvariant_ext(s)
      requires step.Armada_TraceEntry_Tau?
      requires LPlus_NextOneStep(s, s', step)
      requires s.s.threads[step.tid].top.Armada_StackFrame_enqueue?
      ensures WeakeningInvariant_ext(s')
    {
      // assert s'.s.mem.globals.queue.read_index == s.s.mem.globals.queue.read_index;
      // assert s'.s.mem.globals.queue.element_array == s.s.mem.globals.queue.element_array;
      // assert s'.s.mem.globals.queue.number_elements == s.s.mem.globals.queue.number_elements;

      lemma_Tau_enqueue_maintains_AuxDescribesStoreBuffer(s, s', step);
      assert AuxDescribesStoreBuffer(s');
      lemma_DequeueDoesNotConcernImpliesElementArrayLocalMatchesGlobal(s, s', step);

      lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame();
      lemma_mod_auto(s.s.mem.globals.queue.number_elements as int);
      lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways();
      assert DequeueLocalSpaceImpliesGlobalSpace(s');
      assert WeakeningInvariant_ext(s');
    }

  lemma {:verify false} lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_read_index(mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>)
    requires mem1.globals.queue.read_index == mem2.globals.queue.read_index
    ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.read_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.read_index
    decreases |buf|
  {
    if |buf| > 0 {
      var mem1' := L.Armada_ApplyStoreBufferEntry(mem1, buf[0]);
      var mem2' := L.Armada_ApplyStoreBufferEntry(mem2, buf[0]);
      lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_read_index(mem1', mem2', buf[1..]);
    }
  }

  lemma {:verify false} lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_read_index()
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.read_index == mem2.globals.queue.read_index ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.read_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.read_index

    {
      forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}
       | && mem1.globals.queue.read_index == mem2.globals.queue.read_index
        ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.read_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.read_index
        {
          lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_read_index(mem1, mem2, buf);
        }
    }

  lemma {:verify false} lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_write_index(mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>)
    requires mem1.globals.queue.write_index == mem2.globals.queue.write_index
    ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.write_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.write_index
    decreases |buf|
  {
    if |buf| > 0 {
      var mem1' := L.Armada_ApplyStoreBufferEntry(mem1, buf[0]);
      var mem2' := L.Armada_ApplyStoreBufferEntry(mem2, buf[0]);
      lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_write_index(mem1', mem2', buf[1..]);
    }
  }

  lemma {:verify false} lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_write_index()
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.write_index == mem2.globals.queue.write_index ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.write_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.write_index

    {
      forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}
       | && mem1.globals.queue.write_index == mem2.globals.queue.write_index
        ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.write_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.write_index
        {
          lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_write_index(mem1, mem2, buf);
        }
    }

  lemma {:verify false} lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_number_elements(mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>)
    requires mem1.globals.queue.number_elements == mem2.globals.queue.number_elements
    ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.number_elements == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.number_elements
    decreases |buf|
  {
    if |buf| > 0 {
      var mem1' := L.Armada_ApplyStoreBufferEntry(mem1, buf[0]);
      var mem2' := L.Armada_ApplyStoreBufferEntry(mem2, buf[0]);
      lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_number_elements(mem1', mem2', buf[1..]);
    }
  }

  lemma {:verify false} lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_number_elements()
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.number_elements == mem2.globals.queue.number_elements ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.number_elements == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.number_elements

  {
    forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}
    | && mem1.globals.queue.number_elements == mem2.globals.queue.number_elements
      ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.number_elements == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.number_elements
        {
          lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_number_elements(mem1, mem2, buf);
        }
  }

  lemma {:verify false} lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_element_array(mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>)
    requires mem1.globals.queue.element_array == mem2.globals.queue.element_array
    ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.element_array == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.element_array
    decreases |buf|
  {
    if |buf| > 0 {
      var mem1' := L.Armada_ApplyStoreBufferEntry(mem1, buf[0]);
      var mem2' := L.Armada_ApplyStoreBufferEntry(mem2, buf[0]);
      lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_element_array(mem1', mem2', buf[1..]);
    }
  }

  lemma {:verify false} lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_element_array()
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.element_array == mem2.globals.queue.element_array ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.element_array == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.element_array

  {
    forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}
    | && mem1.globals.queue.element_array == mem2.globals.queue.element_array
      ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.element_array == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.element_array
        {
          lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L_element_array(mem1, mem2, buf);
        }
  }

  lemma {:verify false} lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame()
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.read_index == mem2.globals.queue.read_index ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.read_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.read_index
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.write_index == mem2.globals.queue.write_index ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.write_index == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.write_index
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.number_elements == mem2.globals.queue.number_elements ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.number_elements == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.number_elements
    ensures forall mem1: L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> {:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)} :: && mem1.globals.queue.element_array == mem2.globals.queue.element_array ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals.queue.element_array == L.Armada_ApplyStoreBuffer(mem2, buf).globals.queue.element_array
  {
    lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_read_index();
    lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_write_index();
    lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_number_elements();
    lemma_VariableUnchangedAndStoreBufferSameImpliesLocalViewIsSame_element_array();
  }

  predicate {:verify false} StoreBufferLocationConcernsVar_L_write_index(loc: L.Armada_StoreBufferLocation)
  {
    && loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
  }

  predicate {:verify false} StoreBufferLacksIndices_L_write_index(buf: seq<L.Armada_StoreBufferEntry>)
  {
    forall entry ::
      entry in buf ==>
        !StoreBufferLocationConcernsVar_L_write_index(entry.loc)
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatches_L_write_index(mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>, mem': L.Armada_SharedMemory)
    requires StoreBufferLacksIndices_L_write_index(buf)
    requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
    ensures mem'.globals.queue.write_index == mem.globals.queue.write_index
    decreases |buf|
  {
    if |buf| > 0 {
      var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
      assert mem_next.globals.queue.write_index == mem.globals.queue.write_index;
      var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_write_index(mem_next, buf[1..], mem_next');
    }
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_write_index()
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_write_index(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.write_index == mem.globals.queue.write_index
  {
    forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> | StoreBufferLacksIndices_L_write_index(buf)
      ensures L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.write_index == mem.globals.queue.write_index
    {
      var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_write_index(mem, buf, mem');
    }
  }


  predicate {:verify false} StoreBufferLocationConcernsVar_L_read_index(loc: L.Armada_StoreBufferLocation)
  {
    && loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'read_index)])
  }

  predicate {:verify false} StoreBufferLacksIndices_L_read_index(buf: seq<L.Armada_StoreBufferEntry>)
  {
    forall entry ::
      entry in buf ==>
        !StoreBufferLocationConcernsVar_L_read_index(entry.loc)
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatches_L_read_index(mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>, mem': L.Armada_SharedMemory)
    requires StoreBufferLacksIndices_L_read_index(buf)
    requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
    ensures mem'.globals.queue.read_index == mem.globals.queue.read_index
    decreases |buf|
  {
    if |buf| > 0 {
      var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
      assert mem_next.globals.queue.read_index == mem.globals.queue.read_index;
      var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_read_index(mem_next, buf[1..], mem_next');
    }
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_read_index()
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_read_index(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.read_index == mem.globals.queue.read_index
  {
    forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> | StoreBufferLacksIndices_L_read_index(buf)
      ensures L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.read_index == mem.globals.queue.read_index
    {
      var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_read_index(mem, buf, mem');
    }
  }


  predicate {:verify false} StoreBufferLocationConcernsVar_L_number_elements(loc: L.Armada_StoreBufferLocation)
  {
    && loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'number_elements)])
  }

  predicate {:verify false} StoreBufferLacksIndices_L_number_elements(buf: seq<L.Armada_StoreBufferEntry>)
  {
    forall entry ::
      entry in buf ==>
        !StoreBufferLocationConcernsVar_L_number_elements(entry.loc)
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatches_L_number_elements(mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>, mem': L.Armada_SharedMemory)
    requires StoreBufferLacksIndices_L_number_elements(buf)
    requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
    ensures mem'.globals.queue.number_elements == mem.globals.queue.number_elements
    decreases |buf|
  {
    if |buf| > 0 {
      var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
      assert mem_next.globals.queue.number_elements == mem.globals.queue.number_elements;
      var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_number_elements(mem_next, buf[1..], mem_next');
    }
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_number_elements()
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_number_elements(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.number_elements == mem.globals.queue.number_elements
  {
    forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> | StoreBufferLacksIndices_L_number_elements(buf)
      ensures L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.number_elements == mem.globals.queue.number_elements
    {
      var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_number_elements(mem, buf, mem');
    }
  }


  predicate {:verify false} StoreBufferLocationConcernsVar_L_element_array(loc: L.Armada_StoreBufferLocation)
  {
    && loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'element_array)])
  }

  predicate {:verify false} StoreBufferLacksIndices_L_element_array(buf: seq<L.Armada_StoreBufferEntry>)
  {
    forall entry ::
      entry in buf ==>
        !StoreBufferLocationConcernsVar_L_element_array(entry.loc)
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatches_L_element_array(mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>, mem': L.Armada_SharedMemory)
    requires StoreBufferLacksIndices_L_element_array(buf)
    requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
    ensures mem'.globals.queue.element_array == mem.globals.queue.element_array
    decreases |buf|
  {
    if |buf| > 0 {
      var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
      assert mem_next.globals.queue.element_array == mem.globals.queue.element_array;
      var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_element_array(mem_next, buf[1..], mem_next');
    }
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_element_array()
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_element_array(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.element_array == mem.globals.queue.element_array
  {
    forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> | StoreBufferLacksIndices_L_element_array(buf)
      ensures L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.element_array == mem.globals.queue.element_array
    {
      var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
      lemma_IfStoreBufferLacksIndicesThenViewMatches_L_element_array(mem, buf, mem');
    }
  }

  lemma {:verify false} lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways()
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_element_array(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.element_array == mem.globals.queue.element_array
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_number_elements(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.number_elements == mem.globals.queue.number_elements
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_write_index(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.write_index == mem.globals.queue.write_index
    ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferLacksIndices_L_read_index(buf) ==> L.Armada_ApplyStoreBuffer(mem, buf).globals.queue.read_index == mem.globals.queue.read_index
  {
    lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_element_array();
    lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_number_elements();
    lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_write_index();
    lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L_read_index();
  }
  }
