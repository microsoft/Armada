include "../../Armada/ArmadaCommonDefinitions.dfy"
include "L5.dfy"
include "MCSLock.dfy"

module Helper
{
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

  import opened L = L5
  import opened MCSLock

  function {:opaque} Armada_ApplyStoreBufferEntryLength(mem: Armada_SharedMemory, entry: Armada_StoreBufferEntry): (mem': Armada_SharedMemory)
    ensures |mem.globals.locks| == |mem'.globals.locks|
  {
    L.Armada_ApplyStoreBufferEntry(mem, entry)
  }

  function {:opaque} Armada_ApplyStoreBufferLength(mem: Armada_SharedMemory, storeBuffer: seq<L.Armada_StoreBufferEntry>): (mem': Armada_SharedMemory)
    ensures |mem.globals.locks| == |mem'.globals.locks|
    ensures L.Armada_ApplyStoreBuffer(mem, storeBuffer) == mem'
    decreases |storeBuffer|
  {
    reveal Armada_ApplyStoreBufferEntryLength();
    if |storeBuffer| == 0 then
      mem
    else
      Armada_ApplyStoreBufferLength(Armada_ApplyStoreBufferEntryLength(mem, storeBuffer[0]), storeBuffer[1..])
  }

  function {:opaque} Armada_GetThreadLocalViewLength(s: Armada_TotalState, tid: Armada_ThreadHandle): (mem': Armada_SharedMemory)
    requires tid in s.threads
    ensures |s.mem.globals.locks| == |mem'.globals.locks|
    ensures L.Armada_GetThreadLocalView(s, tid) == mem'
  {
    Armada_ApplyStoreBufferLength(s.mem, s.threads[tid].storeBuffer)
  }
}
