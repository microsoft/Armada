include "QueueBSS_WithAbstractQueue.dfy"
include "UseAbstractQueueForLog/specs.dfy"
include "SharedStructs.dfy"
include "auxiliary_helper.dfy"

module queue_abstractloginvariant {
import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions
import opened QueueBSS_WithAbstractQueue = QueueBSS_WithAbstractQueue
import opened ArmadaModule_specs = ArmadaModule_specs
import opened SharedStructs = SharedStructs
import opened auxiliary_helper = auxiliary_helper

// This is the target invariant.
// (a) element_array[d!r .. w] == abstract_queue[..(w - d!r) % array_size ]

predicate {:verify false} WeakHeapInvariant(h: Armada_Heap)
{
    && h.valid * h.freed == {}
    && 0 in h.freed
    && !(0 in h.valid)
    && Armada_TreeProperties(h.tree)
    && (forall p {:trigger Armada_TriggerPointer(p)} :: 
        Armada_TriggerPointer(p) &&
        p in h.tree &&
        h.tree[p].ty.Armada_ObjectType_primitive? ==>
          p in h.values &&
          Armada_PrimitiveValueMatchesType(h.values[p], h.tree[p].ty.pty))
}

// This ensures that queue.element_array is an array with the appropriate number
// of elements and should allow GetQbssElement to be well-defined
predicate {:verify false} MemorySafetyElementArray(locv:Armada_SharedMemory)
  requires WeakHeapInvariant(locv.heap)
{
  var e := locv.globals.queue.element_array;
    && e in locv.heap.tree
    && locv.heap.tree[e].field_of_parent == Armada_FieldArrayIndex(0)
    && locv.globals.queue.number_elements as int > 0
    && var a := locv.heap.tree[e].parent; Armada_ValidPointerToStructSizedArray_BSSQueueElement(locv.heap, a, locv.globals.queue.number_elements as int)
}

function {:verify false} GetQbssElement(locv:Armada_SharedMemory, j:int) : QbssElement
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  var qbsse := Armada_DereferencePointerToStruct_BSSQueueElement(locv.heap,
    GetPointerToQbssElement(locv, j)
    );
    QbssElement(qbsse.key, qbsse.value)
}

function {:verify false} GetPointerToQbssElement(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
    locv.heap.tree[locv.heap.tree[locv.globals.queue.element_array].parent].children[Armada_FieldArrayIndex(locv.heap.tree[locv.globals.queue.element_array].field_of_parent.i + j)]
}

function {:verify false} GetPointerToQbssElementKey(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  locv.heap.tree[GetPointerToQbssElement(locv, j)].children[Armada_FieldStruct(Armada_FieldType_BSSQueueElement'key)]
}

function {:verify false} GetPointerToQbssElementValue(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  locv.heap.tree[GetPointerToQbssElement(locv, j)].children[Armada_FieldStruct(Armada_FieldType_BSSQueueElement'value)]
}

predicate StoreBufferDoesNotConcernQbssElementKey(buf: seq<Armada_StoreBufferEntry>, locv:Armada_SharedMemory, j:int)
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  && StoreBufferDoesNotConcernAddress(buf, GetPointerToQbssElementKey(locv, j))
}

predicate StoreBufferDoesNotConcernQbssElementValue(buf: seq<Armada_StoreBufferEntry>, locv:Armada_SharedMemory, j:int)
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  && StoreBufferDoesNotConcernAddress(buf, GetPointerToQbssElementValue(locv, j))
}

predicate StoreBufferDoesNotConcernAddress(buf: seq<Armada_StoreBufferEntry>, p:Armada_Pointer)
{
  forall entry ::
    entry in buf ==>
    entry.loc != Armada_StoreBufferLocation_Addressable(p)
}

predicate StoreBufferDoesNotConcernQbssElement(buf: seq<Armada_StoreBufferEntry>, locv:Armada_SharedMemory, j:int)
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  && StoreBufferDoesNotConcernQbssElementKey(buf, locv, j)
    && StoreBufferDoesNotConcernQbssElementValue(buf, locv, j)
}

lemma lemma_IfStoreBufferDoesNotConcernAddressThenViewMatches(mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, mem':L.Armada_SharedMemory, p:Armada_Pointer)
  requires StoreBufferDoesNotConcernAddress(buf, p)
  requires p in mem.heap.values
  requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
  ensures p in mem'.heap.values
  ensures (mem.heap.values[p] == mem'.heap.values[p])
  decreases |buf|
{
    if |buf| > 0 {
      var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
      assert mem.heap.values[p] == mem_next.heap.values[p];
      var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
      lemma_IfStoreBufferDoesNotConcernAddressThenViewMatches(mem_next, buf[1..], mem_next', p);
    }
}

lemma lemma_IfStoreBufferDoesNotConcernAddressThenViewMatchesAlways(p:Armada_Pointer)
  ensures forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> :: StoreBufferDoesNotConcernAddress(buf, p) && p in mem.heap.values ==> p in L.Armada_ApplyStoreBuffer(mem, buf).heap.values && L.Armada_ApplyStoreBuffer(mem, buf).heap.values[p] == mem.heap.values[p]
{
  forall mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry> |
    StoreBufferDoesNotConcernAddress(buf, p) && p in mem.heap.values
    ensures p in L.Armada_ApplyStoreBuffer(mem, buf).heap.values && L.Armada_ApplyStoreBuffer(mem, buf).heap.values[p] == mem.heap.values[p]
    {
      lemma_IfStoreBufferDoesNotConcernAddressThenViewMatches(mem, buf, L.Armada_ApplyStoreBuffer(mem,buf), p);
    }
}

predicate Queue_TriggerIndex(i:int)
{
  true
}

predicate DequeueDoesNotConcernQbssElement(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==>
    && WeakHeapInvariant(s.s.mem.heap)
    && MemorySafetyElementArray(s.s.mem)
    && (forall j {:trigger Queue_TriggerIndex(j)} :: 0 <= j < s.s.mem.globals.queue.number_elements as int && Queue_TriggerIndex(j) ==> StoreBufferDoesNotConcernQbssElement(s.s.threads[tid2].storeBuffer, s.s.mem, j))
}

// We will need to verify that this holds across any instruction that performs a
// store-buffer update and across a tau; the tau situation seems more difficult
predicate {:verify false} ElementArrayLocalViewMatchesGlobal(s:LPlusState, tid:Armada_ThreadHandle)
  requires tid in s.s.threads
{
  var locv := Armada_GetThreadLocalView(s.s, tid);
  && WeakHeapInvariant(s.s.mem.heap)
    && WeakHeapInvariant(locv.heap)
    && locv.globals.queue.number_elements == s.s.mem.globals.queue.number_elements
    && MemorySafetyElementArray(s.s.mem)
    && MemorySafetyElementArray(locv)
    && s.s.mem.globals.queue.element_array == locv.globals.queue.element_array
    && (forall i:int {:trigger Queue_TriggerIndex(i)}:: 0 <= i < s.s.mem.globals.queue.number_elements as int
        && Queue_TriggerIndex(i)
        ==>
        && GetPointerToQbssElement(locv, i) == GetPointerToQbssElement(s.s.mem, i)
        && GetQbssElement(locv, i) == GetQbssElement(s.s.mem, i)
       )
}

// This is the invariant we actually want; in order to support it, I need to 
predicate {:verify false} ElementArrayDeqLocalMatchesGlobal(s:LPlusState) {
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==> ElementArrayLocalViewMatchesGlobal(s, tid2)
}

predicate {:verify false} LocalViewOfNumberElementsAlwaysMatchsGlobalInEnqOrDeq(s:LPlusState)
{
  && (forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==> 
    var locv := Armada_GetThreadLocalView(s.s, tid2);
    locv.globals.queue.number_elements == s.s.mem.globals.queue.number_elements)


  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==> 
    var locv := Armada_GetThreadLocalView(s.s, tid1);
    locv.globals.queue.number_elements == s.s.mem.globals.queue.number_elements)
}

// In order to demonstrate this, we will simply require k and v to be roots in
// the tree
predicate {:verify false} DequeueInputPointersDoNotAliasElementArray(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==>
    var k := s.s.threads[tid2].top.dequeue'k;
    var v := s.s.threads[tid2].top.dequeue'v;
    && k in s.s.mem.heap.tree && s.s.mem.heap.tree[k].field_of_parent.Armada_FieldNone?
    && v in s.s.mem.heap.tree && s.s.mem.heap.tree[v].field_of_parent.Armada_FieldNone?

}

predicate {:verify false} TmpIntProperties(s:LPlusState)
  requires ElementArrayDeqLocalMatchesGlobal(s)
  requires LocalIndicesOfDequeueAlwaysWithinBounds(s)
{
    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_tmp_int_update_key)
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_k_update)
           ==>
            var f := s.s.threads[tid2].top;
            var locv := Armada_GetThreadLocalView(s.s, tid2);
            &&  f.dequeue'tmp_int == GetQbssElement(locv, f.dequeue'read_index as int % s.s.mem.globals.queue.number_elements as int).key
       )

    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_tmp_int_update_value)
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_v_update)
           ==>
            var f := s.s.threads[tid2].top;
            var locv := Armada_GetThreadLocalView(s.s, tid2);
            &&  f.dequeue'tmp_int == GetQbssElement(locv, f.dequeue'read_index as int % s.s.mem.globals.queue.number_elements as int).value
       )
}

predicate {:verify false} LocalViewOfEltArrayAddressAlwaysMatchesGlobal(s:LPlusState)
{
  forall tid :: tid in s.s.threads
    ==>
    var locv := Armada_GetThreadLocalView(s.s, tid);
    s.s.mem.globals.queue.element_array == locv.globals.queue.element_array
}

// Relies on:
// LocalViewOfEltArrayAddressAlwaysMatchesGlobal
predicate {:verify false} EnqueueEIsEltArrayPlusWriteIndex(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
  requires MemorySafetyElementArrayIfInEnqueue(s)
  requires IndicesAlwaysWithinBounds(s)
{
    && (forall tid1 :: tid1 in s.s.threads
        && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
        && PCToInstructionCount_L(Armada_PC_enqueue_e_init)
           < PCToInstructionCount_L(s.s.threads[tid1].pc) <=
           PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
        ==> 
        var f := s.s.threads[tid1].top;
        && f.enqueue'e == GetPointerToQbssElement(s.s.mem, f.enqueue'write_index as int)
        )
}

// Relies on:
// LocalViewOfEltArrayAddressAlwaysMatchesGlobal
predicate {:verify false} DequeueEisEltArrayPlusReadIndex(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
  requires MemorySafetyElementArrayIfInDequeue(s)
  requires IndicesAlwaysWithinBounds(s)
{
    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_e_init)
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
        ==> 
        var f := s.s.threads[tid2].top;

        && f.dequeue'e == GetPointerToQbssElement(s.s.mem, f.dequeue'read_index as int % s.s.mem.globals.queue.number_elements as int)
        )
}

predicate {:verify false} LocalNumberElementsAlwaysMatchesGlobal(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads ==>
        var locv := Armada_GetThreadLocalView(s.s, tid);
        locv.globals.queue.number_elements == s.s.mem.globals.queue.number_elements
    )
}

////////////////////////////////////////////////////////////////////////////////
// Memory safety invariant and invariants necessary to support lifting
// create_thread steps
////////////////////////////////////////////////////////////////////////////////

predicate {:verify false} MemorySafetyElementArrayIfInEnqueue(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
{
  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    // var locv := Armada_GetThreadLocalView(s.s, tid1);
    && MemorySafetyElementArray(s.s.mem)
    // && MemorySafetyElementArray(locv)
    )
}

predicate {:verify false} MemorySafetyElementArrayIfInDequeue(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
{
  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_dequeue?
    ==>
    var locv := Armada_GetThreadLocalView(s.s, tid1);
    && MemorySafetyElementArray(s.s.mem)
      // && MemorySafetyElementArray(locv)
    )
}

predicate {:verify false} MainSbEmpty(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    ==>
    s.s.threads[tid].storeBuffer == []
    )
}

predicate {:verify false} MainIfGuard(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && (s.s.threads[tid].pc == Armada_PC_main_BeforeEnqueueCreate
     || s.s.threads[tid].pc == Armada_PC_main_BeforeDequeueCreate)
     ==>
     s.s.mem.globals.queue.element_array != 0
     && s.s.threads[tid].top.main'k != 0
     && s.s.threads[tid].top.main'v != 0
    )
}

predicate {:verify false} ConditionalMemorySafetyElementInMainAfterCalloc(s:LPlusState)
{
  && MainSbEmpty(s)
  && WeakHeapInvariant(s.s.mem.heap)

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_number_elements_init)
    ==>
    && s.s.mem.globals.queue.number_elements > 0
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_element_array_alloc)
    ==>
    && (s.s.mem.globals.queue.element_array != 0) ==> MemorySafetyElementArray(s.s.mem)
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_k_alloc)
    ==>
    &&  var k := s.s.threads[tid].top.main'k;
    (k != 0 ==> k in s.s.mem.heap.tree && s.s.mem.heap.tree[k].field_of_parent.Armada_FieldNone?)
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_v_alloc)
    ==>
    &&  var v := s.s.threads[tid].top.main'v;
    (v != 0 ==> v in s.s.mem.heap.tree && s.s.mem.heap.tree[v].field_of_parent.Armada_FieldNone?)
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_read_index_init)
    ==>
    && 0 <= s.s.mem.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_write_index_init)
    ==>
    && 0 <= s.s.mem.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
    )
}

predicate {:verify false} MemorySafetyInvariant(s:LPlusState)
{
  && MainIfGuard(s)
  && ConditionalMemorySafetyElementInMainAfterCalloc(s)
  && WeakHeapInvariant(s.s.mem.heap)
  && MemorySafetyElementArrayIfInDequeue(s)
  && MemorySafetyElementArrayIfInEnqueue(s)
}

////////////////////////////////////////////////////////////////////////////////
// Invariant regarding bounds on read_index and write_index (within array
// bounds, never overflows uint64)
////////////////////////////////////////////////////////////////////////////////

predicate {:verify false} DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==>
    var f := s.s.threads[tid2].top;
    var locv := Armada_GetThreadLocalView(s.s, tid2);
    && 0 <= locv.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
}

predicate {:verify false} EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    var f := s.s.threads[tid1].top;
    var locv := Armada_GetThreadLocalView(s.s, tid1);
    0 <= locv.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
}

// Relies on DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds
predicate {:verify false} LocalIndicesOfDequeueAlwaysWithinBounds(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(s.s.threads[tid2].pc) > PCToInstructionCount_L(Armada_PC_dequeue_read_index_init)
    ==>
    var f := s.s.threads[tid2].top;
    0 <= f.dequeue'read_index as int < s.s.mem.globals.queue.number_elements as int
}
// Relies on EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds
predicate {:verify false} LocalIndicesOfEnqueueAlwaysWithinBounds(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(s.s.threads[tid1].pc) > PCToInstructionCount_L(Armada_PC_enqueue_write_index_init)
    ==>
    var f := s.s.threads[tid1].top;
    0 <= f.enqueue'write_index as int < s.s.mem.globals.queue.number_elements as int
}

predicate {:verify false} IndicesAlwaysWithinBounds(s:LPlusState)
{
  && EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s)
  && DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s)
  && LocalIndicesOfEnqueueAlwaysWithinBounds(s)
    && LocalIndicesOfDequeueAlwaysWithinBounds(s)
}

predicate {:verify false} DeqLocalReadIndexMatchesLocalViewAfterInit(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_read_index_init)
    < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
    PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
  var locv := Armada_GetThreadLocalView(s.s, tid2);
  && s.s.threads[tid2].top.dequeue'read_index == locv.globals.queue.read_index
}

predicate {:verify false} EnqLocalWriteIndexMatchesLocalViewAfterInit(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    &&
    PCToInstructionCount_L(Armada_PC_enqueue_write_index_init)
    < PCToInstructionCount_L(s.s.threads[tid1].pc) <=
    PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
  var locv := Armada_GetThreadLocalView(s.s, tid1);
  && s.s.threads[tid1].top.enqueue'write_index == locv.globals.queue.write_index
}

/*
predicate {:verify false} GhostReadIndexMatchesDeqLocalView(s:LPlusState) {
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && !s.s.threads[tid2].pc.Armada_PC_dequeue_inside_read_update_block?
    ==>
  var locv := Armada_GetThreadLocalView(s.s, tid2);
  && locv.globals.queue.read_index == s.s.ghosts.d_r
}

predicate {:verify false} GhostWriteIndexMatchesEnqLocalView(s:LPlusState) {
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && !s.s.threads[tid1].pc.Armada_PC_enqueue_inside_write_update_block?
    ==>
  var locv := Armada_GetThreadLocalView(s.s, tid1);
  && locv.globals.queue.read_index == s.s.ghosts.d_r
}
*/

predicate {:verify false} IndicesProperties(s:LPlusState) {
  // && GhostReadIndexMatchesDeqLocalView(s)
    // && GhostWriteIndexMatchesEnqLocalView(s)
    && DeqLocalReadIndexMatchesLocalViewAfterInit(s)
    && EnqLocalWriteIndexMatchesLocalViewAfterInit(s)
}

////////////////////////////////////////////////////////////////////////////////
// If inside dequeue if, then deq_size > 0 is non-empty
// Local space ==> global space, local
////////////////////////////////////////////////////////////////////////////////

predicate {:verify false} EnqueueLocalViewOfReadIndexIsGlobal(s:LPlusState)
{
  && (forall tid1 ::
      && tid1 in s.s.threads 
      && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
      ==>
      var locv := Armada_GetThreadLocalView(s.s, tid1);
      locv.globals.queue.read_index == s.s.mem.globals.queue.read_index
      )
}

predicate {:verify false} DequeueLocalViewOfWriteIndexIsGlobal(s:LPlusState)
{
  && (forall tid2 ::
      && tid2 in s.s.threads 
      && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
      ==>
      var locv := Armada_GetThreadLocalView(s.s, tid2);
      locv.globals.queue.write_index == s.s.mem.globals.queue.write_index
      )
}

predicate {:verify false} DequeueLocalSpaceImpliesGlobalSpace(s:LPlusState)
{
  && DequeueLocalViewOfWriteIndexIsGlobal(s)
    
  && (forall tid2 ::
      && tid2 in s.s.threads 
      && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
      && (PCToInstructionCount_L(L.Armada_PC_dequeue_write_index_init) <
          PCToInstructionCount_L(s.s.threads[tid2].pc) <=
          PCToInstructionCount_L(L.Armada_PC_dequeue_read_index_update))
          ==>
          var locv := Armada_GetThreadLocalView(s.s, tid2);
      (s.s.threads[tid2].top.dequeue'read_index != s.s.threads[tid2].top.dequeue'write_index ==> locv.globals.queue.read_index != locv.globals.queue.write_index)
  )
}

predicate {:verify false} DequeueIfProperties(s:LPlusState)
{
  (forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid2].pc)
    <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    s.s.threads[tid2].top.dequeue'read_index != s.s.threads[tid2].top.dequeue'write_index
    )

  && (forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid2].pc)
    <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    && Armada_GetThreadLocalView(s.s, tid2).globals.queue.number_elements as int > 0
    && (
        var locv := Armada_GetThreadLocalView(s.s, tid2);
        var deq_size := (locv.globals.queue.write_index as int - locv.globals.queue.read_index as int) % locv.globals.queue.number_elements as int;
        && locv.globals.queue.write_index as int != locv.globals.queue.read_index as int
        && 0 <= locv.globals.queue.write_index as int < locv.globals.queue.number_elements as int
        && 0 <= locv.globals.queue.read_index as int < locv.globals.queue.number_elements as int
        && deq_size > 0
    )
  )
}

predicate WeakHeapInvariantAlways(s:LPlusState)
{
  && WeakHeapInvariant(s.s.mem.heap)
  && forall tid :: tid in s.s.threads
    ==>
    var locv := Armada_GetThreadLocalView(s.s, tid);
    WeakHeapInvariant(locv.heap)
}

predicate {:verify false} AbstractQueueMatchesImpl(s:LPlusState)
{
  && (
    forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && ! (PCToInstructionCount_L(Armada_PC_dequeue_abs_queue_update) < PCToInstructionCount_L(s.s.threads[tid2].pc) <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update))
        ==>
        && Armada_GetThreadLocalView(s.s, tid2).globals.queue.number_elements as int > 0
        && (
            var locv := Armada_GetThreadLocalView(s.s, tid2);
            var deq_size := (s.s.mem.globals.queue.write_index as int - locv.globals.queue.read_index as int) % locv.globals.queue.number_elements as int;
            && WeakHeapInvariant(locv.heap)
            && MemorySafetyElementArray(locv)
            && 0 <= deq_size < |s.s.ghosts.q|
            && (forall i :: 0 <= i < deq_size ==>
            s.s.ghosts.q[i] == GetQbssElement(locv, (i + locv.globals.queue.read_index as int) % locv.globals.queue.number_elements as int))
        )
  )

  && (
    forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && (PCToInstructionCount_L(Armada_PC_dequeue_abs_queue_update) < PCToInstructionCount_L(s.s.threads[tid2].pc) <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update))
        ==>
        && Armada_GetThreadLocalView(s.s, tid2).globals.queue.number_elements as int > 0
        && (
            var locv := Armada_GetThreadLocalView(s.s, tid2);
            var deq_size := (s.s.mem.globals.queue.write_index as int - (locv.globals.queue.read_index as int + 1)) % locv.globals.queue.number_elements as int;
            && WeakHeapInvariant(locv.heap)
            && MemorySafetyElementArray(locv)
            && 0 <= deq_size < |s.s.ghosts.q|
            && locv.globals.queue.number_elements > 0
            && (forall i :: 0 <= i < deq_size ==>
            s.s.ghosts.q[i] == GetQbssElement(locv, (i + locv.globals.queue.read_index as int + 1) % locv.globals.queue.number_elements as int)
            )
        )
  )
}

predicate {:verify false} EnqueueInitInvariant(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
    var pc := s.s.threads[tid1].pc;
    var f := s.s.threads[tid1].top;
    var locv := Armada_GetThreadLocalView(s.s, tid1);
    (
      && (
      PCToInstructionCount_L(Armada_PC_enqueue_tmp_write_index_init) < PCToInstructionCount_L(pc)
      ==> f.enqueue'tmp_write_index == Armada_CastTo_uint64(f.enqueue'write_index as int + 1)
      )

      && (
      PCToInstructionCount_L(Armada_PC_enqueue_modulo_init) < PCToInstructionCount_L(pc)
      ==> locv.globals.queue.number_elements as int > 0 && f.enqueue'modulo == Armada_CastTo_uint64((f.enqueue'tmp_write_index as int % locv.globals.queue.number_elements as int) as int)
      )
    )
}

////////////////////////////////////////////////////////////////////////////////
// Invariant for queue.read_index := queue.read_indeax + 1;
////////////////////////////////////////////////////////////////////////////////

predicate {:verify false} DequeueReadIndexUpdateInvariant(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(s.s.threads[tid2].pc) <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    var pc := s.s.threads[tid2].pc;
    var f := s.s.threads[tid2].top;
    var locv := Armada_GetThreadLocalView(s.s, tid2);
    (
      && (
      PCToInstructionCount_L(Armada_PC_dequeue_tmp_read_index_init) < PCToInstructionCount_L(pc)
      ==> f.dequeue'tmp_read_index == Armada_CastTo_uint64(f.dequeue'read_index as int + 1)
      )

      && (
      PCToInstructionCount_L(Armada_PC_dequeue_modulo_init) < PCToInstructionCount_L(pc)
      ==> locv.globals.queue.number_elements as int > 0 && f.dequeue'modulo == Armada_CastTo_uint64((f.dequeue'tmp_read_index as int % locv.globals.queue.number_elements as int) as int)
      )
    )
}

predicate {:verify false} ThreadsInv(s:LPlusState)
{
        && (forall tid :: tid in s.s.threads ==> (s.s.threads[tid].top.Armada_StackFrame_main? <==> tid == s.config.tid_init))
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_enqueue? && s.s.threads[tid2].top.Armada_StackFrame_enqueue? ==> tid1 == tid2)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_dequeue? && s.s.threads[tid2].top.Armada_StackFrame_dequeue? ==> tid1 == tid2)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_main? && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(L.Armada_PC_main_BeforeEnqueueCreate) ==> !s.s.threads[tid2].top.Armada_StackFrame_enqueue?)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_main? && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(L.Armada_PC_main_BeforeDequeueCreate) ==> !s.s.threads[tid2].top.Armada_StackFrame_dequeue?)
        && (forall tid :: tid in s.s.threads ==> s.s.threads[tid].stack == [])
        && (forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_main? ==> s.s.threads[tid].storeBuffer == [])
}

predicate {:verify false} AbstractReadsMatchImplQueueValuesInDequeue(s:LPlusState)
{
    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_abs_queue_update) 
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
        ==>
        var f := s.s.threads[tid2].top;
        var locv := Armada_GetThreadLocalView(s.s, tid2);
        && WeakHeapInvariant(locv.heap)
        && MemorySafetyElementArray(locv)
        && s.s.mem.globals.queue.number_elements as int > 0
        && QbssElement(f.dequeue'i_k, f.dequeue'i_v) == GetQbssElement(locv, f.dequeue'read_index as int % locv.globals.queue.number_elements as int))
}


////////////////////////////////////////////////////////////////////////////////
// Store buffer invariants
////////////////////////////////////////////////////////////////////////////////

// Idea: make an auxiliary holding the positions of the store buffer entries
// updated queue.write. Can have an invariant asserting that the only writes to
// queue.write are those described by the aux.
// 
// The aux can even track the value being written to write_index.
// Can this somehow help with preserving the local space implies global space invariant?
//
// I think it can. Can assert that the store buffer entry "write_index := j" has
// the property that applying it to a state where write_index == j - 1 and where
// write_index != read_index will ensure that write_index != read_index is still true.
// This can be guaranteed by way of 

predicate {:verify false} AuxDescribesStoreBuffer(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) <= PCToInstructionCount_L(Armada_PC_main_BeforeEnqueueCreate)
    ==>
    s.w_i_seq == []
    )

    && (forall i, j :: 0 <= i < j < |s.w_i_seq|
        ==> s.w_i_seq[i].position < s.w_i_seq[j].position
    )

  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    (forall i :: 0 <= i < |s.s.threads[tid1].storeBuffer|
    && s.s.threads[tid1].storeBuffer[i].loc ==
    L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
    ==>
    && s.s.threads[tid1].storeBuffer[i].value.Armada_PrimitiveValue_uint64?
    && WriteIndexSBEntry(i, s.s.threads[tid1].storeBuffer[i].value.n_uint64) in s.w_i_seq
    )
  )

  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    && (forall w :: w in s.w_i_seq
    ==>
    0 <= w.position < |s.s.threads[tid1].storeBuffer|
    && s.s.threads[tid1].storeBuffer[w.position].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
    && s.s.threads[tid1].storeBuffer[w.position].value == Armada_PrimitiveValue_uint64(w.value)
    )
  )
}

// All the things that should never be in the store buffers of different threads
predicate {:verify false} StoreBufferDoesNotContainInvariant(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads
    ==>
    (forall e :: e in s.s.threads[tid].storeBuffer ==>
    && e.loc != L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'number_elements)])
    && e.loc != L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'element_array)])
    )
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_dequeue?
    ==>
    && (forall e :: e in s.s.threads[tid].storeBuffer ==>
        && e.loc != L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
      )

    && (forall e :: e in s.s.threads[tid].storeBuffer
        && e.loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'read_index)])
        ==> e.value.Armada_PrimitiveValue_uint64? && 0 <= e.value.n_uint64 < s.s.mem.globals.queue.number_elements
      )
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_enqueue?
    ==>
    && (forall e :: e in s.s.threads[tid].storeBuffer ==>
        && e.loc != L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'read_index)])
      )

    && (forall e :: e in s.s.threads[tid].storeBuffer
        && e.loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
        ==> e.value.Armada_PrimitiveValue_uint64? && 0 <= e.value.n_uint64 < s.s.mem.globals.queue.number_elements
      )
    )

    // && DequeueStoreBufferDoesNotWriteToWriteIndex(s)
    // && EnqueueStoreBufferDoesNotWriteToReadIndex(s)
}

predicate {:verify false} EnqueueStoreBufferDoesNotWriteToReadIndex(s:LPlusState)
{
  (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    && (forall mem :: var mem' := Armada_ApplyStoreBuffer(mem, s.s.threads[tid1].storeBuffer); mem.globals.queue.read_index == mem'.globals.queue.read_index)
    && (forall mem :: var mem' := Armada_ApplyStoreBuffer(mem, s.s.threads[tid1].storeBuffer); mem.globals.queue.number_elements == mem'.globals.queue.number_elements)
  )
}

predicate {:verify false} DequeueStoreBufferDoesNotWriteToWriteIndex(s:LPlusState)
{
  (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_dequeue?
    ==>
    && (forall mem :: var mem' := Armada_ApplyStoreBuffer(mem, s.s.threads[tid1].storeBuffer); mem.globals.queue.write_index == mem'.globals.queue.write_index)
    && (forall mem :: var mem' := Armada_ApplyStoreBuffer(mem, s.s.threads[tid1].storeBuffer); mem.globals.queue.number_elements == mem'.globals.queue.number_elements)
  )
}

predicate {:verify false} StoreBufferInvariant(s:LPlusState)
{
  StoreBufferDoesNotContainInvariant(s)
}

predicate {:verify false} WeakeningInvariant_ext(s:LPlusState)
{
  && ThreadsInv(s)
  && WeakHeapInvariant(s.s.mem.heap)

  && MemorySafetyInvariant(s)

    && ElementArrayDeqLocalMatchesGlobal(s)

    && EnqueueLocalViewOfReadIndexIsGlobal(s)
    && LocalViewOfNumberElementsAlwaysMatchsGlobalInEnqOrDeq(s)
    && EnqueueInitInvariant(s)
    && DequeueReadIndexUpdateInvariant(s)
    && IndicesProperties(s)
    && IndicesAlwaysWithinBounds(s)

    && DequeueInputPointersDoNotAliasElementArray(s)
    && TmpIntProperties(s)

    && LocalViewOfEltArrayAddressAlwaysMatchesGlobal(s)
    && EnqueueEIsEltArrayPlusWriteIndex(s)
    && DequeueEisEltArrayPlusReadIndex(s)

    && DequeueLocalSpaceImpliesGlobalSpace(s)
    && DequeueIfProperties(s)
    && WeakHeapInvariantAlways(s)

    && AuxDescribesStoreBuffer(s)
    && StoreBufferInvariant(s)
    && DequeueDoesNotConcernQbssElement(s)

    && AbstractQueueMatchesImpl(s)

    && AbstractReadsMatchImplQueueValuesInDequeue(s)
}

}
