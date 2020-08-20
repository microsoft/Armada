include "../../Armada/ArmadaCommonDefinitions.dfy"
include "L5.dfy"
include "MCSLock.dfy"

module L5_L6_Helper {
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

  import L = L5
  import MCSLock

  function Armada_ApplyStoreBufferEntryLength(mem: L.Armada_SharedMemory, entry: L.Armada_StoreBufferEntry): (mem': L.Armada_SharedMemory)
    ensures |mem.globals.locks| == |mem'.globals.locks|
  {
    L.Armada_ApplyStoreBufferEntry(mem, entry)
  }
  
  function Armada_ApplyStoreBufferLength(mem: L.Armada_SharedMemory, storeBuffer: seq<L.Armada_StoreBufferEntry>): (mem': L.Armada_SharedMemory)
    ensures |mem.globals.locks| == |mem'.globals.locks|
    ensures L.Armada_ApplyStoreBuffer(mem, storeBuffer) == mem'
    decreases |storeBuffer|
  {
    if |storeBuffer| == 0 then
      mem
    else
      Armada_ApplyStoreBufferLength(Armada_ApplyStoreBufferEntryLength(mem, storeBuffer[0]), storeBuffer[1..])
  }

  function Armada_GetThreadLocalViewLength(s: L.Armada_TotalState, tid: Armada_ThreadHandle): (mem': L.Armada_SharedMemory)
    requires tid in s.threads
    ensures |s.mem.globals.locks| == |mem'.globals.locks|
    ensures L.Armada_GetThreadLocalView(s, tid) == mem'
  {
    Armada_ApplyStoreBufferLength(s.mem, s.threads[tid].storeBuffer)
  }
}
