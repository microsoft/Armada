include "QueueBSSNoTSO_WithAbstractQueue.dfy"
include "NoTSOUseAbstractQueueForLog/specs.dfy"
include "SharedStructs.dfy"

module queue_tsobypassing_abstractloginvariant {
import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions
import opened QueueBSSNoTSO_WithAbstractQueue = QueueBSSNoTSO_WithAbstractQueue
import opened ArmadaModule_specs = ArmadaModule_specs
import opened SharedStructs = SharedStructs


lemma lemma_NoSetIntersectionImpliesNoCommonElements<T>(a:set<T>, b:set<T>)
  requires (a * b) == {}
  ensures forall i :: i in a ==> i !in b
{
    forall i | i in a
      ensures i !in b
    {
      assert i in (a * b) ==> a * b != {};
    }
}

// This is the target invariant.
// (a) element_array[d!r .. w] == abstract_queue[..(w - d!r) % array_size ]

predicate WeakHeapInvariant(h: Armada_Heap)
{
    && (forall p :: p in h.valid ==> p !in h.freed)
    && 0 in h.freed
    && !(0 in h.valid)
    && Armada_TreeProperties(h.tree)
    && (forall p {:trigger Armada_TriggerPointer(p)} :: 
        Armada_TriggerPointer(p) in h.tree &&
        h.tree[p].ty.Armada_ObjectTypePrimitive? ==>
          p in h.values &&
          Armada_PrimitiveValueMatchesType(h.values[p], h.tree[p].ty.pty))
}

// This ensures that queue.element_array is an array with the appropriate number
// of elements and should allow GetQbssElement to be well-defined
predicate MemorySafetyElementArray(locv:Armada_SharedMemory)
  requires WeakHeapInvariant(locv.heap)
{
  MemorySafetyElementArrayCustomPointer(locv.globals.queue.element_array, locv)
}

predicate MemorySafetyElementArrayCustomPointer(pointer:Armada_Pointer, locv:Armada_SharedMemory)
  requires WeakHeapInvariant(locv.heap)
{
  var e := pointer;
    && e in locv.heap.tree
    && e in locv.heap.valid
    && locv.heap.tree[e].child_type == Armada_ChildTypeIndex(0)
    && locv.globals.queue.number_elements as int > 0
    && Armada_ComparablePointer(e, locv.heap)
    && var a := locv.heap.tree[e].parent;
    && Armada_ValidPointerToObjectType(locv.heap, a, Armada_ObjectTypeArray(Armada_StructType_BSSQueueElement(), locv.globals.queue.number_elements as int))
    && (forall i {:trigger locv.heap.tree[a].children[i]} :: 0 <= i < locv.globals.queue.number_elements as int ==> Armada_ValidPointerToObjectType(locv.heap, locv.heap.tree[a].children[i], Armada_StructType_BSSQueueElement()))
}


function GetQbssElement(locv:Armada_SharedMemory, j:int) : QbssElement
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  var qbsse := Armada_DereferenceStructPointer_BSSQueueElement(locv.heap, GetPointerToQbssElement(locv, j));
  QbssElement(qbsse.key, qbsse.value)
}

function GetPointerToQbssElement(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  locv.heap.tree[locv.heap.tree[locv.globals.queue.element_array].parent].children[locv.heap.tree[locv.globals.queue.element_array].child_type.i + j]
}

function GetPointerToQbssElementKey(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  locv.heap.tree[GetPointerToQbssElement(locv, j)].children[0 /* key is field 0 of BSSQueueElement */]
}

function GetPointerToQbssElementValue(locv:Armada_SharedMemory, j:int) : Armada_Pointer
  requires WeakHeapInvariant(locv.heap)
  requires MemorySafetyElementArray(locv)
  requires 0 <= j < locv.globals.queue.number_elements as int
{
  locv.heap.tree[GetPointerToQbssElement(locv, j)].children[1 /* value is field 1 of BSSQueueElement */]
}

// In order to demonstrate this, we will simply require k and v to be roots in
// the tree
predicate DequeueInputPointersDoNotAliasElementArray(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==>
    var k := s.s.threads[tid2].top.dequeue.k;
    var v := s.s.threads[tid2].top.dequeue.v;
    && k in s.s.mem.heap.tree && s.s.mem.heap.tree[k].child_type.Armada_ChildTypeRoot?
    && v in s.s.mem.heap.tree && s.s.mem.heap.tree[v].child_type.Armada_ChildTypeRoot?

}

predicate TmpIntProperties(s:LPlusState)
  requires LocalIndicesOfDequeueAlwaysWithinBounds(s)
  requires WeakHeapInvariant(s.s.mem.heap)
  requires MemorySafetyElementArrayIfInDequeue(s)
{
    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_tmp_int_update_key)
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_k_update)
           ==>
            var f := s.s.threads[tid2].top;
            && s.s.mem.globals.queue.number_elements > 0
            &&  f.dequeue.tmp_int == GetQbssElement(s.s.mem, f.dequeue.read_index as int % s.s.mem.globals.queue.number_elements as int).key
       )

    && (forall tid2 :: tid2 in s.s.threads
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        && PCToInstructionCount_L(Armada_PC_dequeue_tmp_int_update_value)
           < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
           PCToInstructionCount_L(Armada_PC_dequeue_v_update)
           ==>
            var f := s.s.threads[tid2].top;
            && s.s.mem.globals.queue.number_elements > 0
            &&  f.dequeue.tmp_int == GetQbssElement(s.s.mem, f.dequeue.read_index as int % s.s.mem.globals.queue.number_elements as int).value
       )
}

predicate EnqueueEIsEltArrayPlusWriteIndex(s:LPlusState)
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
        && f.enqueue.e == GetPointerToQbssElement(s.s.mem, f.enqueue.write_index as int)
        )
}

predicate DequeueEisEltArrayPlusReadIndex(s:LPlusState)
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

        && f.dequeue.e == GetPointerToQbssElement(s.s.mem, f.dequeue.read_index as int % s.s.mem.globals.queue.number_elements as int)
        )
}

////////////////////////////////////////////////////////////////////////////////
// Memory safety invariant and invariants necessary to support lifting
// create_thread steps
////////////////////////////////////////////////////////////////////////////////

predicate MemorySafetyElementArrayIfInEnqueue(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
{
  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    && MemorySafetyElementArray(s.s.mem)
    )
}

predicate MemorySafetyElementArrayIfInDequeue(s:LPlusState)
  requires WeakHeapInvariant(s.s.mem.heap)
{
  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_dequeue?
    ==>
    && MemorySafetyElementArray(s.s.mem)
    )
}

predicate MainIfGuard(s:LPlusState)
{
  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && (s.s.threads[tid].pc == Armada_PC_main_BeforeEnqueueCreate
     || s.s.threads[tid].pc == Armada_PC_main_BeforeDequeueCreate)
     ==>
     s.s.mem.globals.queue.element_array != 0
     && s.s.threads[tid].top.main.k != 0
     && s.s.threads[tid].top.main.v != 0
    )
}

predicate ConditionalMemorySafetyElementInMainAfterCalloc(s:LPlusState)
{
  && WeakHeapInvariant(s.s.mem.heap)

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_number_elements_init)
    ==>
    && s.s.mem.globals.queue.number_elements == 512
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_array_calloc)
    ==>
    && (s.s.threads[tid].top.main.a != 0 ==> MemorySafetyElementArrayCustomPointer(s.s.threads[tid].top.main.a, s.s.mem)
    )
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
    &&  var k := s.s.threads[tid].top.main.k;
    (k != 0 ==> k in s.s.mem.heap.tree && s.s.mem.heap.tree[k].child_type.Armada_ChildTypeRoot?
    && Armada_ComparablePointer(k, s.s.mem.heap)
      )
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_v_alloc)
    ==>
    &&  var v := s.s.threads[tid].top.main.v;
    (v != 0 ==> v in s.s.mem.heap.tree && s.s.mem.heap.tree[v].child_type.Armada_ChildTypeRoot?
    && Armada_ComparablePointer(v, s.s.mem.heap)
      )
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


  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(Armada_PC_main_BeforeEnqueueCreate) >= PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_write_index_init)
    ==>
    && 0 == s.s.mem.globals.queue.write_index as int
    )

  && (forall tid :: tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(Armada_PC_main_BeforeEnqueueCreate) >= PCToInstructionCount_L(s.s.threads[tid].pc) > PCToInstructionCount_L(Armada_PC_main_read_index_init)
    ==>
    && 0 == s.s.mem.globals.queue.read_index as int
    )
}

predicate MemorySafetyInvariant(s:LPlusState)
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

predicate DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    ==>
    var f := s.s.threads[tid2].top;
    && 0 <= s.s.mem.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
}

predicate EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    ==>
    var f := s.s.threads[tid1].top;
    && 0 <= s.s.mem.globals.queue.write_index as int < s.s.mem.globals.queue.number_elements as int
    && 0 <= s.s.mem.globals.queue.read_index as int < s.s.mem.globals.queue.number_elements as int
}

// Relies on DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds
predicate LocalIndicesOfDequeueAlwaysWithinBounds(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(s.s.threads[tid2].pc) > PCToInstructionCount_L(Armada_PC_dequeue_read_index_init)
    ==>
    var f := s.s.threads[tid2].top;
    0 <= f.dequeue.read_index as int < s.s.mem.globals.queue.number_elements as int
}
// Relies on EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds
predicate LocalIndicesOfEnqueueAlwaysWithinBounds(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(s.s.threads[tid1].pc) > PCToInstructionCount_L(Armada_PC_enqueue_write_index_init)
    ==>
    var f := s.s.threads[tid1].top;
    0 <= f.enqueue.write_index as int < s.s.mem.globals.queue.number_elements as int
}

predicate IndicesAlwaysWithinBounds(s:LPlusState)
{
  && EnqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s)
  && DeqGlobalAndLocalViewOfIndicesAlwaysWithinBounds(s)
  && LocalIndicesOfEnqueueAlwaysWithinBounds(s)
    && LocalIndicesOfDequeueAlwaysWithinBounds(s)
}

predicate DeqLocalReadIndexMatchesLocalViewAfterInit(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_read_index_init)
    < PCToInstructionCount_L(s.s.threads[tid2].pc) <=
    PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
  && s.s.threads[tid2].top.dequeue.read_index == s.s.mem.globals.queue.read_index
}

predicate EnqLocalWriteIndexMatchesLocalViewAfterInit(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    &&
    PCToInstructionCount_L(Armada_PC_enqueue_write_index_init)
    < PCToInstructionCount_L(s.s.threads[tid1].pc) <=
    PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
  && s.s.threads[tid1].top.enqueue.write_index == s.s.mem.globals.queue.write_index
}

predicate IndicesProperties(s:LPlusState) {
    && DeqLocalReadIndexMatchesLocalViewAfterInit(s)
    && EnqLocalWriteIndexMatchesLocalViewAfterInit(s)
}

////////////////////////////////////////////////////////////////////////////////
// If inside dequeue if, then deq_size > 0 is non-empty
// Local space ==> global space, local
////////////////////////////////////////////////////////////////////////////////

predicate DequeueLocalNonEmptyImpliesGlobalNonEmpty(s:LPlusState)
{
  && (forall tid2 ::
      && tid2 in s.s.threads 
      && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
      && (PCToInstructionCount_L(L.Armada_PC_dequeue_write_index_init) <
          PCToInstructionCount_L(s.s.threads[tid2].pc) <=
          PCToInstructionCount_L(L.Armada_PC_dequeue_read_index_update))
          ==>
      (s.s.threads[tid2].top.dequeue.read_index != s.s.threads[tid2].top.dequeue.write_index ==> s.s.mem.globals.queue.read_index != s.s.mem.globals.queue.write_index)
  )
}

predicate EnqueueLocalSpaceImpliesGlobalSpace(s:LPlusState)
{
    (forall tid1 ::
     && tid1 in s.s.threads 
     && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
     && (PCToInstructionCount_L(L.Armada_PC_enqueue_read_index_init) <
         PCToInstructionCount_L(s.s.threads[tid1].pc) <=
         PCToInstructionCount_L(L.Armada_PC_enqueue_write_index_update))
         ==>
         && s.s.mem.globals.queue.number_elements as int > 0
         && (s.s.threads[tid1].top.enqueue.read_index != s.s.threads[tid1].top.enqueue.modulo
          ==> s.s.mem.globals.queue.read_index != Armada_CastTo_uint64((Armada_CastTo_uint64((s.s.mem.globals.queue.write_index as int + 1 as int) as int) as int % s.s.mem.globals.queue.number_elements as int) as int))
    )
}

predicate DequeueIfProperties(s:LPlusState)
{
  (forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid2].pc)
    <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    && (s.s.threads[tid2].top.dequeue.read_index != s.s.threads[tid2].top.dequeue.write_index)
    && (s.s.mem.globals.queue.read_index != s.s.mem.globals.queue.write_index)
    )

  && (forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid2].pc)
    <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    && s.s.mem.globals.queue.number_elements as int > 0
    && (
        var queue := s.s.mem.globals.queue;
        var deq_size := (queue.write_index as int - queue.read_index as int) % queue.number_elements as int;
        && queue.write_index as int != queue.read_index as int
        && 0 <= queue.write_index as int < queue.number_elements as int
        && 0 <= queue.read_index as int < queue.number_elements as int
        && deq_size > 0
    )
  )
}


predicate EnqueueIfProperties(s:LPlusState)
{
  (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(Armada_PC_enqueue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid1].pc)
    <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
    s.s.threads[tid1].top.enqueue.modulo != s.s.threads[tid1].top.enqueue.read_index
    )
}

predicate BothIfProperties(s:LPlusState)
{
  (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(Armada_PC_enqueue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid1].pc)
    <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)

    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(Armada_PC_dequeue_inside_if_start) <= PCToInstructionCount_L(s.s.threads[tid2].pc)
    <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    s.s.threads[tid1].top.enqueue.write_index != s.s.threads[tid2].top.dequeue.read_index
    )
}

predicate AbstractQueueMatchesImplBetweenIndices(s:LPlusState, start:uint64, end:uint64)
  requires 0 <= start < s.s.mem.globals.queue.number_elements
  requires 0 <= end < s.s.mem.globals.queue.number_elements
{
  var q_size := (end as int - start as int) % s.s.mem.globals.queue.number_elements as int;
  && WeakHeapInvariant(s.s.mem.heap)
    && MemorySafetyElementArray(s.s.mem)
    && 0 <= q_size == |s.s.ghosts.q|
    && (forall i :: 0 <= i < q_size ==>
    s.s.ghosts.q[i] == GetQbssElement(s.s.mem, (i + start as int) % s.s.mem.globals.queue.number_elements as int))
}

predicate EnqueueAfterAssignmentQueueMatchesKV(s:LPlusState)
{
  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(Armada_PC_enqueue_k_update)
    < PCToInstructionCount_L(s.s.threads[tid1].pc)
    <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
    && s.s.mem.globals.queue.number_elements > 0
  && WeakHeapInvariant(s.s.mem.heap)
    && MemorySafetyElementArray(s.s.mem)
    && s.s.threads[tid1].top.enqueue.k == GetQbssElement(s.s.mem, s.s.mem.globals.queue.write_index as int % s.s.mem.globals.queue.number_elements as int).key
    )

  && (forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(Armada_PC_enqueue_v_update)
    < PCToInstructionCount_L(s.s.threads[tid1].pc)
    <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
    && s.s.mem.globals.queue.number_elements > 0
    && s.s.threads[tid1].top.enqueue.v == GetQbssElement(s.s.mem, s.s.mem.globals.queue.write_index as int % s.s.mem.globals.queue.number_elements as int).value
    )
}

predicate AbstractQueueMatchesImpl(s:LPlusState)
{
  && (
    forall tid :: tid in s.s.threads
     && s.s.threads[tid].top.Armada_StackFrame_main?
     && PCToInstructionCount_L(s.s.threads[tid].pc) <= PCToInstructionCount_L(Armada_PC_main_BeforeEnqueueCreate)
     ==>
     && s.s.ghosts.q == []
    )

  && (
    forall tid2 :: tid2 in s.s.threads
    && (s.s.threads[tid2].top.Armada_StackFrame_enqueue?
    || s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    || (s.s.threads[tid2].top.Armada_StackFrame_main?
        && (PCToInstructionCount_L(s.s.threads[tid2].pc) == PCToInstructionCount_L(Armada_PC_main_BeforeEnqueueCreate)
           || PCToInstructionCount_L(s.s.threads[tid2].pc) == PCToInstructionCount_L(Armada_PC_main_BeforeDequeueCreate))
       )
    )
    ==>
    && s.s.mem.globals.queue.number_elements as int > 0
    && 0 <= s.s.mem.globals.queue.read_index < s.s.mem.globals.queue.number_elements
    && 0 <= s.s.mem.globals.queue.write_index < s.s.mem.globals.queue.number_elements
    && (
    AbstractQueueMatchesImplBetweenIndices(s, s.s.mem.globals.queue.read_index, s.s.mem.globals.queue.write_index)
    )
    )
}

predicate EnqueueInitInvariant(s:LPlusState)
{
  forall tid1 :: tid1 in s.s.threads
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(Armada_PC_enqueue_write_index_update)
    ==>
    var pc := s.s.threads[tid1].pc;
    var f := s.s.threads[tid1].top;
    (
      && (
      PCToInstructionCount_L(Armada_PC_enqueue_tmp_write_index_init) < PCToInstructionCount_L(pc)
      ==> f.enqueue.tmp_write_index == Armada_CastTo_uint64(f.enqueue.write_index as int + 1)
      )

      && (
      PCToInstructionCount_L(Armada_PC_enqueue_modulo_init) < PCToInstructionCount_L(pc)
      ==> s.s.mem.globals.queue.number_elements as int > 0 && f.enqueue.modulo == Armada_CastTo_uint64((f.enqueue.tmp_write_index as int % s.s.mem.globals.queue.number_elements as int) as int)
      )
    )
}

////////////////////////////////////////////////////////////////////////////////
// Invariant for queue.read_index := queue.read_indeax + 1;
////////////////////////////////////////////////////////////////////////////////

predicate DequeueReadIndexUpdateInvariant(s:LPlusState)
{
  forall tid2 :: tid2 in s.s.threads
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && PCToInstructionCount_L(s.s.threads[tid2].pc) <= PCToInstructionCount_L(Armada_PC_dequeue_read_index_update)
    ==>
    var pc := s.s.threads[tid2].pc;
    var f := s.s.threads[tid2].top;
    (
      && (
      PCToInstructionCount_L(Armada_PC_dequeue_tmp_read_index_init) < PCToInstructionCount_L(pc)
      ==> f.dequeue.tmp_read_index == Armada_CastTo_uint64(f.dequeue.read_index as int + 1)
      )

      && (
      PCToInstructionCount_L(Armada_PC_dequeue_modulo_init) < PCToInstructionCount_L(pc)
      ==> s.s.mem.globals.queue.number_elements as int > 0 && f.dequeue.modulo == Armada_CastTo_uint64((f.dequeue.tmp_read_index as int % s.s.mem.globals.queue.number_elements as int) as int)
      )
    )
}

predicate ThreadsInv(s:LPlusState)
{
        && (forall tid :: tid in s.s.threads ==> (s.s.threads[tid].top.Armada_StackFrame_main? <==> tid == s.config.tid_init))
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_enqueue? && s.s.threads[tid2].top.Armada_StackFrame_enqueue? ==> tid1 == tid2)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_dequeue? && s.s.threads[tid2].top.Armada_StackFrame_dequeue? ==> tid1 == tid2)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_main? && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(L.Armada_PC_main_BeforeEnqueueCreate) ==> !s.s.threads[tid2].top.Armada_StackFrame_enqueue?)
        && (forall tid1, tid2 :: tid1 in s.s.threads && tid2 in s.s.threads && s.s.threads[tid1].top.Armada_StackFrame_main? && PCToInstructionCount_L(s.s.threads[tid1].pc) <= PCToInstructionCount_L(L.Armada_PC_main_BeforeDequeueCreate) ==> !s.s.threads[tid2].top.Armada_StackFrame_dequeue?)
        && (forall tid :: tid in s.s.threads ==> s.s.threads[tid].stack == [])
        && (forall tid :: tid in s.s.threads ==> s.s.threads[tid].storeBuffer == [])
        && (forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_main? ==> s.s.threads[tid].storeBuffer == [])
}

predicate WeakeningInvariant_ext(s:LPlusState)
{
  && ThreadsInv(s)
  && WeakHeapInvariant(s.s.mem.heap)

  && MemorySafetyInvariant(s)

    && EnqueueInitInvariant(s)
    && DequeueReadIndexUpdateInvariant(s)
    && IndicesProperties(s)
    && IndicesAlwaysWithinBounds(s)

    && DequeueInputPointersDoNotAliasElementArray(s)
    && TmpIntProperties(s)

    && EnqueueEIsEltArrayPlusWriteIndex(s)
    && DequeueEisEltArrayPlusReadIndex(s)

    && DequeueLocalNonEmptyImpliesGlobalNonEmpty(s)
    && EnqueueLocalSpaceImpliesGlobalSpace(s)
    && DequeueIfProperties(s)
    && EnqueueIfProperties(s)
    && BothIfProperties(s)

    && EnqueueAfterAssignmentQueueMatchesKV(s)
    && AbstractQueueMatchesImpl(s)

    // && AbstractReadsMatchImplQueueValuesInDequeue(s)
}

}
