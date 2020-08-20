include "../../Armada/ArmadaCommonDefinitions.dfy"
include "L4.dfy"
include "MCSLock.dfy"

module L4_L5_Helper
{
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

  import L = L4
  import MCSLock

  predicate is_owner(tid: uint64, tidQueue: seq<uint64>)
  {
    |tidQueue| != 0 && tidQueue[0] == tid
  }

  function prev(tid: uint64, tidQueue: seq<uint64>): uint64
    requires tid in tidQueue
    requires ! is_owner(tid, tidQueue)
    ensures prev(tid, tidQueue) in tidQueue
  {
    tidQueue[queue_idx(tid, tidQueue) - 1]
  }

  lemma prev_injective(tid1: uint64, tid2: uint64, tidQueue: seq<uint64>)
    requires tid1 in tidQueue && tid2 in tidQueue
    requires ! is_owner(tid1, tidQueue) && ! is_owner(tid2, tidQueue)
    requires forall i, j :: 0 <= i < j < |tidQueue| ==> tidQueue[i] != tidQueue[j]
    ensures prev(tid1, tidQueue) == prev(tid2, tidQueue) ==> tid1 == tid2
  {

  }

  function queue_idx(tid: uint64, tidQueue: seq<uint64>): int
    requires tid in tidQueue
    ensures !is_owner(tid, tidQueue) ==> queue_idx(tid, tidQueue) > 0
    ensures tid != tidQueue[|tidQueue|-1] ==> queue_idx(tid, tidQueue) < |tidQueue|-1
  {
    var idx :| 0 <= idx < |tidQueue| && tidQueue[idx] == tid;
    idx
  }

  function wait_entry(idx: uint64, val: uint32): L.Armada_StoreBufferEntry
  {
    L.Armada_StoreBufferEntry(L.Armada_StoreBufferLocation_Unaddressable(
      L.Armada_GlobalStaticVar_locks,
      [Armada_FieldArrayIndex(idx as int),
       Armada_FieldStruct(MCSLock.Armada_FieldType_lock'wait)]),
      Armada_PrimitiveValue_uint32(val))
  }

  function next_entry(idx: uint64, val: uint64): L.Armada_StoreBufferEntry
  {
    L.Armada_StoreBufferEntry(L.Armada_StoreBufferLocation_Unaddressable(
      L.Armada_GlobalStaticVar_locks,
      [Armada_FieldArrayIndex(idx as int),
       Armada_FieldStruct(MCSLock.Armada_FieldType_lock'next)]),
      Armada_PrimitiveValue_uint64(val))
  }

  predicate waiting_facts(tid: uint64, s: L.Armada_TotalState)
    requires tid in s.threads
    requires 0 < tid as int < |s.mem.globals.locks|
    requires s.threads[tid].pc.Armada_PC_acquire_wait?
  {
    var queue, locks := s.ghosts.tidQueue, s.mem.globals.locks;
    var sb := s.threads[tid].storeBuffer;
    tid in queue &&
    if is_owner(tid, queue) then
      |sb| == 0
    else (
      var prev := prev(tid, queue);
      0 < prev as int < |locks| &&
      if |sb| == 0 then
        locks[tid].wait == 1 && locks[prev].next == tid
      else if sb == [next_entry(prev, tid)] then
        locks[tid].wait == 1 && locks[prev].next == 0
      else sb == [wait_entry(tid, 1), next_entry(prev, tid)] &&
        locks[tid].wait == 0 && locks[prev].next == 0
    )
  }

  predicate sb_entry_fact(tid: uint64, entry: L.Armada_StoreBufferEntry, s: L.Armada_TotalState)
    requires tid in s.threads
    requires entry in s.threads[tid].storeBuffer
  {
    entry.loc.Armada_StoreBufferLocation_Unaddressable? &&
    if entry.loc.fields == [Armada_FieldArrayIndex(tid as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'next)] then
      entry.value == Armada_PrimitiveValue_uint64(0) && s.threads[tid].top.Armada_StackFrame_acquire? && tid !in s.ghosts.tidQueue
    else if entry.loc.fields == [Armada_FieldArrayIndex(tid as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'wait)] then
      entry.value == Armada_PrimitiveValue_uint32(1)
    else |s.ghosts.tidQueue| > 0 && var owner := s.ghosts.tidQueue[0];
      if entry.loc.fields == [Armada_FieldArrayIndex(owner as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'wait)] then
      owner in s.threads && entry.value == Armada_PrimitiveValue_uint32(0) && s.threads[owner].pc.Armada_PC_acquire_wait?
    else
      tid in s.ghosts.tidQueue && !is_owner(tid, s.ghosts.tidQueue) &&
      entry.loc.fields == [Armada_FieldArrayIndex(prev(tid, s.ghosts.tidQueue) as int),
                           Armada_FieldStruct(MCSLock.Armada_FieldType_lock'next)] &&
      entry.value == Armada_PrimitiveValue_uint64(tid) &&
      0 < prev(tid, s.ghosts.tidQueue) as int < |s.mem.globals.locks| &&
      s.mem.globals.locks[prev(tid, s.ghosts.tidQueue)].next == 0 &&
      s.threads[tid].pc.Armada_PC_acquire_wait?
  }

  lemma sb_entry_fact_unfold(s: L.Armada_TotalState)
    ensures forall tid, entry :: tid in s.threads && entry in s.threads[tid].storeBuffer && sb_entry_fact(tid, entry, s) ==>
    entry.loc.Armada_StoreBufferLocation_Unaddressable? &&
    if entry.loc.fields == [Armada_FieldArrayIndex(tid as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'next)] then
      entry.value == Armada_PrimitiveValue_uint64(0) && s.threads[tid].top.Armada_StackFrame_acquire? && tid !in s.ghosts.tidQueue
    else if entry.loc.fields == [Armada_FieldArrayIndex(tid as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'wait)] then
      entry.value == Armada_PrimitiveValue_uint32(1)
    else |s.ghosts.tidQueue| > 0 && var owner := s.ghosts.tidQueue[0];
      if entry.loc.fields == [Armada_FieldArrayIndex(owner as int), Armada_FieldStruct(MCSLock.Armada_FieldType_lock'wait)] then
      owner in s.threads && entry.value == Armada_PrimitiveValue_uint32(0) && s.threads[owner].pc.Armada_PC_acquire_wait?
    else
      tid in s.ghosts.tidQueue && !is_owner(tid, s.ghosts.tidQueue) &&
      entry.loc.fields == [Armada_FieldArrayIndex(prev(tid, s.ghosts.tidQueue) as int),
                           Armada_FieldStruct(MCSLock.Armada_FieldType_lock'next)] &&
      entry.value == Armada_PrimitiveValue_uint64(tid) &&
      0 < prev(tid, s.ghosts.tidQueue) as int < |s.mem.globals.locks| &&
      s.mem.globals.locks[prev(tid, s.ghosts.tidQueue)].next == 0 &&
      s.threads[tid].pc.Armada_PC_acquire_wait?
  {
  }
}
