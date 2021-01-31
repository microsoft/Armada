include "L1.dfy"

module L1RefinesL2Helpers {

  import opened L = L1

  lemma lemma_FindStoreBuffer1WhenLocalViewSeesIt(
    which_thread:int,
    mem:L.Armada_SharedMemory,
    storeBuffer:seq<L.Armada_StoreBufferEntry>
    ) returns (
    entry:L.Armada_StoreBufferEntry
    )
    requires forall entry' :: && entry' in storeBuffer
                        && entry'.loc.Armada_StoreBufferLocation_Unaddressable?
                        && entry'.loc.v.Armada_GlobalStaticVar_barrier?
                        && |entry'.loc.fields| == 1
                        && entry'.value.Armada_PrimitiveValue_uint32?
                        ==> entry'.value.n_uint32 == 0 || entry'.value.n_uint32 == 1
    requires |mem.globals.barrier| == 10
    requires 0 <= which_thread < 10
    requires var locv := L.Armada_ApplyStoreBuffer(mem, storeBuffer);
             which_thread < |locv.globals.barrier| && locv.globals.barrier[which_thread] != 0
    requires mem.globals.barrier[which_thread] == 0
    ensures  entry in storeBuffer
    ensures  entry.loc.Armada_StoreBufferLocation_Unaddressable?
    ensures  entry.loc.v.Armada_GlobalStaticVar_barrier?
    ensures  |entry.loc.fields| == 1
    ensures  entry.loc.fields[0] == which_thread
    ensures  entry.value.Armada_PrimitiveValue_uint32?
    ensures  entry.value.n_uint32 == 1
    decreases |storeBuffer|
  {
    if |storeBuffer| == 0 {
      assert false;
    }

    var entry0 := storeBuffer[0];
    if && entry0.loc.Armada_StoreBufferLocation_Unaddressable?
       && entry0.loc.v.Armada_GlobalStaticVar_barrier?
       && |entry0.loc.fields| == 1
       && entry0.loc.fields[0] == which_thread
       && entry0.value.Armada_PrimitiveValue_uint32?
    {
      if entry0.value.n_uint32 == 1 {
        entry := entry0;
      }
      else {
        assert entry0.value.n_uint32 == 0;
        entry := lemma_FindStoreBuffer1WhenLocalViewSeesIt(which_thread, L.Armada_ApplyStoreBufferEntry(mem, entry0), storeBuffer[1..]);
      }
    }
    else {
      entry := lemma_FindStoreBuffer1WhenLocalViewSeesIt(which_thread, L.Armada_ApplyStoreBufferEntry(mem, entry0), storeBuffer[1..]);
    }
  }

  lemma lemma_BarrierNonzeroInLocalViewImpliesStoreBuffer1OrBarrier1(s:L.Armada_TotalState)
    requires forall tid, entry :: 
      tid in s.threads &&
      entry in s.threads[tid].storeBuffer &&
      entry.loc.Armada_StoreBufferLocation_Unaddressable? &&
      entry.loc.v.Armada_GlobalStaticVar_barrier? &&
      |entry.loc.fields| == 1 &&
      entry.value.Armada_PrimitiveValue_uint32? ==>
      entry.value.n_uint32 == 0 || entry.value.n_uint32 == 1

    requires forall tid, entry :: 
      s.ghosts.all_initialized &&
      |s.ghosts.threads_past_barrier| == 10 &&
      tid in s.threads &&
      entry in s.threads[tid].storeBuffer &&
      entry.loc.Armada_StoreBufferLocation_Unaddressable? &&
      entry.loc.v.Armada_GlobalStaticVar_barrier? &&
      |entry.loc.fields| == 1 &&
      entry.value.Armada_PrimitiveValue_uint32? &&
      entry.value.n_uint32 == 1 ==>
        var which_thread := entry.loc.fields[0]; 0 <= which_thread < 10 && s.ghosts.threads_past_barrier[which_thread]

    requires forall which_thread :: 
      s.ghosts.all_initialized &&
      |s.mem.globals.barrier| == 10 &&
      |s.ghosts.threads_past_barrier| == 10 &&
      0 <= which_thread < 10 &&
      s.mem.globals.barrier[which_thread] != 0 ==>
      s.ghosts.threads_past_barrier[which_thread]

    ensures forall which_thread, viewing_thread :: 
      s.ghosts.all_initialized &&
      |s.mem.globals.barrier| == 10 &&
      |s.ghosts.threads_past_barrier| == 10 &&
      0 <= which_thread < 10 &&
      viewing_thread in s.threads &&
      (var locv := L.Armada_GetThreadLocalView(s, viewing_thread);
       which_thread < |locv.globals.barrier| && locv.globals.barrier[which_thread] != 0) ==>
        s.ghosts.threads_past_barrier[which_thread]
  {
    forall which_thread, viewing_thread |
      && s.ghosts.all_initialized
      && |s.mem.globals.barrier| == 10
      && |s.ghosts.threads_past_barrier| == 10
      && 0 <= which_thread < 10
      && viewing_thread in s.threads
      && (var locv := L.Armada_GetThreadLocalView(s, viewing_thread);
         which_thread < |locv.globals.barrier| && locv.globals.barrier[which_thread] != 0)
      ensures s.ghosts.threads_past_barrier[which_thread]
    {
      if s.mem.globals.barrier[which_thread] != 0 {
        assert s.ghosts.threads_past_barrier[which_thread];
      }
      else {
        var entry := lemma_FindStoreBuffer1WhenLocalViewSeesIt(which_thread, s.mem, s.threads[viewing_thread].storeBuffer);
        assert s.ghosts.threads_past_barrier[which_thread];
      }
    }
  }

}
