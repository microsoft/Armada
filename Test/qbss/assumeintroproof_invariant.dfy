include "../../Armada/ArmadaCommonDefinitions.dfy"
include "QueueBSS_TSObypass.dfy"
include "QueueBSS_Assume.dfy"
include "AssumeIntroProof/specs.dfy"

module assumeintroproof_invariant {
import opened ArmadaModule_specs
import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

/*
   EnqueueRegion = set{enqueue.e, AddrOf((*e).key), AddrOf((*e).value) }

   All store buffer entries in enqueue write to EnqueueRegion.

   e == queue.element_array + write_index

   storeBuffer != [] ==> write_index 

   This will alow us to commute tau steps from different threads.

   Need to commute tau of enqueue with dequeue steps.
   EnqTau with read of e.key and e.value should work if we add to the invariant
   the following:

   enqueue.storeBuffer only contains writes to e.key, e.value, queue.write
   enqueue.storeBuffer != [] ==> e == queue.element_array + write_index

   enqueue.storeBuffer != [] && deq.pc in range 
    ==> enqueue.write_index != dequeue.read_index
  
   applying any entry of enqueue.storeBuffer preserves DequeueLocalToGlobalInv

*/

predicate MainInitInvariant(s:LPlusState) {
  && (forall tid ::
    && tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(L.Armada_PC_main_mn_array_size_init) < PCToInstructionCount_L(s.s.threads[tid].pc)
    ==> s.s.mem.globals.queue.array_size as int != 0)

    && (forall tid ::
    && tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(L.Armada_PC_main_mn_write_index_init) < PCToInstructionCount_L(s.s.threads[tid].pc)
    ==> 0 <= s.s.mem.globals.queue.write_index < s.s.mem.globals.queue.array_size)

    && (forall tid ::
    && tid in s.s.threads
    && s.s.threads[tid].top.Armada_StackFrame_main?
    && PCToInstructionCount_L(L.Armada_PC_main_mn_read_index_init) < PCToInstructionCount_L(s.s.threads[tid].pc)
    ==> 0 <= s.s.mem.globals.queue.read_index < s.s.mem.globals.queue.array_size)

    && (forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_enqueue?
    ==> 
    && s.s.mem.globals.queue.array_size as int > 0
    && 0 <= s.s.mem.globals.queue.write_index < s.s.mem.globals.queue.array_size
    && 0 <= s.s.mem.globals.queue.read_index < s.s.mem.globals.queue.array_size
    )

    && (forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_dequeue?
    ==> 
    && s.s.mem.globals.queue.array_size as int > 0
    && 0 <= s.s.mem.globals.queue.write_index < s.s.mem.globals.queue.array_size
    && 0 <= s.s.mem.globals.queue.read_index < s.s.mem.globals.queue.array_size
    )
}

predicate EnqueueInitInvariant(s:LPlusState)
  requires MainInitInvariant(s)
{
    // Self contained invariant. However, the subclauses depend upon one another.
    && (forall tid1 ::
        && tid1 in s.s.threads 
        && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
        ==> (
        var pc := s.s.threads[tid1].pc; var queue := s.s.mem.globals.queue;
        var frame := s.s.threads[tid1].top;

        // EnqInitWriteIndexIsGlobalWriteIndex
        && (
            && (PCToInstructionCount_L(L.Armada_PC_enqueue_write_index_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
            ==> frame.enqueue'write_index == queue.write_index
        )

        // EnqInitTmpWriteIndexIsGlobalWriteIndexPlusOne
        && (
            && (PCToInstructionCount_L(L.Armada_PC_enqueue_tmp_write_index_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
            ==> frame.enqueue'tmp_write_index == Armada_CastTo_uint64(queue.write_index as int + 1 as int)
        )

        // EnqInitArraySizeIsGlobalArraySize
        && (
            && (PCToInstructionCount_L(L.Armada_PC_enqueue_array_size_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
            ==> frame.enqueue'array_size == queue.array_size
        )

        // EnqInitModuloIsGlobalWriteIndexPlusOneModGlobalArraySize
        && (
            && (PCToInstructionCount_L(L.Armada_PC_enqueue_modulo_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
            ==> frame.enqueue'modulo ==
        Armada_CastTo_uint64((Armada_CastTo_uint64((queue.write_index as int + 1 as int) as int) as int % queue.array_size as int) as int)
        )

        )
    )
}

predicate DequeueInitInvariant(s:LPlusState) 
  requires MainInitInvariant(s)
{
    && (forall tid2 ::
        && tid2 in s.s.threads 
        && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
        ==> (
        var pc := s.s.threads[tid2].pc; var queue := s.s.mem.globals.queue;
        var frame := s.s.threads[tid2].top;
        && (
        // DeqInitReadIndexIsGlobalReadIndex
            && (PCToInstructionCount_L(L.Armada_PC_dequeue_read_index_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
            ==> frame.dequeue'read_index == queue.read_index
        )

        && (
        // DeqInitTmpReadIndexIsGlobalReadIndexPlusOne
            && (PCToInstructionCount_L(L.Armada_PC_dequeue_tmp_read_index_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
            ==> frame.dequeue'tmp_read_index == Armada_CastTo_uint64(queue.read_index as int + 1 as int)
        )

        && (
        // DeqInitArraySizeIsGlobalArraySize
            && (PCToInstructionCount_L(L.Armada_PC_dequeue_array_size_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
            ==> frame.dequeue'array_size == queue.array_size
        )

        && (
        // DeqInitModuloIsGlobalReadIndexPlusOneModGlobalArraySize
            && (PCToInstructionCount_L(L.Armada_PC_dequeue_modulo_init) <
                PCToInstructionCount_L(pc) <=
                PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
            ==> frame.dequeue'modulo ==
        Armada_CastTo_uint64((Armada_CastTo_uint64((queue.read_index as int + 1 as int) as int) as int % queue.array_size as int) as int)
        )

        )
        )
}

predicate EnqueueIfGuard(s:LPlusState) {
  (forall tid1 ::
    && tid1 in s.s.threads 
    && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
    && (PCToInstructionCount_L(L.Armada_PC_enqueue_if_start) <=
        PCToInstructionCount_L(s.s.threads[tid1].pc) <=
        PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
    ==> s.s.threads[tid1].top.enqueue'read_index != s.s.threads[tid1].top.enqueue'modulo
    )
}
predicate DequeueIfGuard(s:LPlusState) {
  (forall tid2 ::
    && tid2 in s.s.threads 
    && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
    && (PCToInstructionCount_L(L.Armada_PC_dequeue_if_start) <=
        PCToInstructionCount_L(s.s.threads[tid2].pc) <=
        PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
    ==> s.s.threads[tid2].top.dequeue'read_index != s.s.threads[tid2].top.dequeue'write_index
    )
}

predicate EnqLocalSpaceImpliesGlobal(s:LPlusState)
  requires MainInitInvariant(s)
{
    // EnqueueAssumeInvariant
    // Depends on: DequeueAssumeInvariant,
    // EnqInitModuloIsGlobalWriteIndexPlusOneModGlobalArraySize,
    // DequeueIfGuard
    (forall tid1 ::
     && tid1 in s.s.threads 
     && s.s.threads[tid1].top.Armada_StackFrame_enqueue?
     && (PCToInstructionCount_L(L.Armada_PC_enqueue_assume_start) <=
         PCToInstructionCount_L(s.s.threads[tid1].pc) <=
         PCToInstructionCount_L(L.Armada_PC_enqueue_assume_end))
     ==> (s.s.threads[tid1].top.enqueue'read_index != s.s.threads[tid1].top.enqueue'modulo
          ==> s.s.mem.globals.queue.read_index != Armada_CastTo_uint64((Armada_CastTo_uint64((s.s.mem.globals.queue.write_index as int + 1 as int) as int) as int % s.s.mem.globals.queue.array_size as int) as int))
    )
}

predicate DeqLocalNonemptyImpliesGlobal(s:LPlusState) {
    // DequeueAssumeInvariant
    // Depends on: EnqueueAssumeInvariant, DeqInitReadIndexIsGlobalReadIndex,
    // EnqueueIfGuard
    (forall tid2 ::
      && tid2 in s.s.threads 
      && s.s.threads[tid2].top.Armada_StackFrame_dequeue?
      && (PCToInstructionCount_L(L.Armada_PC_dequeue_assume_start) <=
          PCToInstructionCount_L(s.s.threads[tid2].pc) <=
          PCToInstructionCount_L(L.Armada_PC_dequeue_assume_end))
      ==> (s.s.threads[tid2].top.dequeue'read_index != s.s.threads[tid2].top.dequeue'write_index ==> s.s.mem.globals.queue.read_index != s.s.mem.globals.queue.write_index)
        )
}

predicate AssumeInvariant_mem(s:LPlusState) {
  && MainInitInvariant(s)
  && EnqueueInitInvariant(s)
  && EnqueueIfGuard(s)
  && DequeueInitInvariant(s)
  && DequeueIfGuard(s)
  && DeqLocalNonemptyImpliesGlobal(s)
  && EnqLocalSpaceImpliesGlobal(s)
}

predicate AssumeInvariant_ext(s:LPlusState) {
  AssumeInvariant_mem(s)

    && (forall tid, storeBufferEntry,
        stop_reason, threads, mem, ghosts, addrs, config ::
        storeBufferEntry in s.s.threads[tid].storeBuffer &&
        AssumeInvariant_mem(LPlusState(L.Armada_TotalState(stop_reason, threads, mem, ghosts, addrs), config))
        ==> AssumeInvariant_mem(LPlusState(L.Armada_TotalState(stop_reason, threads, L.Armada_ApplyStoreBufferEntry(mem, storeBufferEntry), ghosts, addrs), config))
        )
}

  lemma {:verify false} lemma_HoldsForAllStoreBuffersImpliesInLocalView(s:LPlusState, f:LPlusState->bool, tid:Armada_ThreadHandle)
    requires tid in s.s.threads
    ensures var mem' := L.Armada_GetThreadLocalView(s.s, tid); var s' := LPlusState(L.Armada_TotalState(s.s.stop_reason, s.s.threads, mem', s.s.ghosts, s.s.addrs), s.config);
        f(s')
  {
    
  }

  lemma {:verify false} lemma_GenericHoldsAcrossTauImpliesHoldsInLocalView(f:LPlusState->bool)
    ensures (forall s:LPlusState, tid {:trigger L.Armada_GetThreadLocalView(s.s, tid)}:: tid in s.s.threads ==> 
    var mem' := L.Armada_GetThreadLocalView(s.s, tid);
    var s' := LPlusState(L.Armada_TotalState(s.s.stop_reason, s.s.threads, mem', s.s.ghosts, s.s.addrs), s.config);
    f(s'))
  {
    
  }

}
