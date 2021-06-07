include "../../Armada/ArmadaCommonDefinitions.dfy"
include "L4.dfy"
include "MCSLock.dfy"

module Helper
{
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions

  import opened L = L4
  import opened MCSLock

  function wait_entry(tid: uint64, val: uint32, pc: L.Armada_PC): Armada_StoreBufferEntry
  {
    Armada_StoreBufferEntry(Armada_StoreBufferLocation_Unaddressable(
      Armada_GlobalStaticVar_locks,
      [tid as int, 0]),
      Armada_PrimitiveValue_uint32(val),
      pc
      )
  }

  function next_entry(tid: uint64, val: uint64, pc: L.Armada_PC): Armada_StoreBufferEntry
  {
    Armada_StoreBufferEntry(Armada_StoreBufferLocation_Unaddressable(
      Armada_GlobalStaticVar_locks,
      [tid as int, 1]),
      Armada_PrimitiveValue_uint64(val),
      pc
      )
  }

  predicate waiting_pc(pc: Armada_PC)
  {
    && !pc.Armada_PC_acquire_Start? && !pc.Armada_PC_acquire_1? && !pc.Armada_PC_acquire_2?
    && !pc.Armada_PC_acquire_3? && !pc.Armada_PC_acquire_4? && !pc.Armada_PC_acquire_5?
    && !pc.Armada_PC_acquire_End? && !pc.Armada_PC_release_Start? && !pc.Armada_PC_release_1?
    && !pc.Armada_PC_release_2? && !pc.Armada_PC_release_3? && !pc.Armada_PC_release_JumpBack_4?
    && !pc.Armada_PC_release_5? && !pc.Armada_PC_release_6? && !pc.Armada_PC_release_7?
    && !pc.Armada_PC_release_End? && !pc.Armada_PC_client_Start? && !pc.Armada_PC_client_1?
    && !pc.Armada_PC_client_2? && !pc.Armada_PC_client_first? && !pc.Armada_PC_client_second?
    && !pc.Armada_PC_client_third? && !pc.Armada_PC_client_JumpBack_6? && !pc.Armada_PC_client_End?
    && !pc.Armada_PC_main_Start? && !pc.Armada_PC_main_1? && !pc.Armada_PC_main_JumpBack_2?
    && !pc.Armada_PC_main_End?
  }

  predicate yp_nolocks(s: Armada_TotalState, s': Armada_TotalState, tid: Armada_ThreadHandle)
  {
    var Q, Q', locks, locks' := s.ghosts.Q, s'.ghosts.Q, s.mem.globals.locks, s'.mem.globals.locks;
    tid in s.threads && tid in s'.threads ==>
    var sb, sb' := s.threads[tid].storeBuffer, s'.threads[tid].storeBuffer;
    && (unique_Q(Q) ==> unique_Q(Q'))
    && (owner_of(tid, Q) ==> owner_of(tid, Q'))
    && (tid in Q <==> tid in Q')
    && (tid in Q && !owner_of(tid, Q) ==> owner_of(tid, Q') || (tid in Q' && pred(tid, Q) == pred(tid, Q')))
    && (owner_of(tid, Q) ==> yp_hard(Q, Q'))
    && (!owner_of(tid, Q) && owner_of(tid, Q') ==> |s'.threads[tid].storeBuffer| == 0 && waiting_pc(s'.threads[tid].pc))

    // a simpler store buffer fact
    && (|sb'| <= |sb|)
    && yp_storebuffer(sb, sb')
  }

  predicate yp_locks(s: Armada_TotalState, s': Armada_TotalState, tid: Armada_ThreadHandle)
  {
    var Q, Q', locks, locks' := s.ghosts.Q, s'.ghosts.Q, s.mem.globals.locks, s'.mem.globals.locks;
    tid in s.threads && tid in s'.threads && 0 < tid as int < |locks| ==>
    var sb, sb' := s.threads[tid].storeBuffer, s'.threads[tid].storeBuffer;
    && (|locks| == |locks'|)

    && (tid !in Q ==> locks[tid].next == 0 ==> locks'[tid].next == 0)
    && (locks[tid].next != 0 && tid in Q ==> locks[tid].next == locks'[tid].next)
    && (|sb| == 0 && locks[tid].wait == 0 ==> locks'[tid].wait == 0)
    && ((next_entry(tid, 0, L.Armada_PC_acquire_Start) in sb && tid !in Q && |sb'| == 0) ==> locks'[tid].next == 0)
    && ((sb == [wait_entry(tid, 1, L.Armada_PC_acquire_4)] && |sb'| == 0) ==> locks'[tid].wait != 0)

    // local view
    && (!owner_of(tid, Q) && tid in Q && 0 < pred(tid, Q) as int < |locks| &&
        Armada_ApplyStoreBufferLength(s.mem, sb).globals.locks[tid].wait != 0 &&
        Armada_ApplyStoreBufferLength(s'.mem, sb').globals.locks[tid].wait == 0 ==>
        waiting_pc(s.threads[tid].pc))
  }

  predicate yp_hard(Q: seq<uint64>, Q': seq<uint64>)
  {
    Q <= Q'
  }

  predicate {:opaque} yp_storebuffer(sb: seq<Armada_StoreBufferEntry>, sb': seq<Armada_StoreBufferEntry>)
    ensures sb == sb' ==> yp_storebuffer(sb, sb')
  {
    && |sb'| <= |sb|
    && sb' == sb[|sb|-|sb'|..]
  }

  lemma yp_storebuffer_trans()
    ensures forall sb1, sb2, sb3 :: yp_storebuffer(sb1, sb2) && yp_storebuffer(sb2, sb3) ==> yp_storebuffer(sb1, sb3)
  {
    reveal yp_storebuffer();
  }

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

  predicate inv_trivial(s: Armada_TotalState)
  {
    && (forall tid {:trigger s.threads[tid].pc == L.Armada_PC_main_End} :: tid in s.threads ==> s.threads[tid].pc != L.Armada_PC_main_End)
      && (forall tid {:trigger s.threads[tid].pc.Armada_PC_client_End?} {:trigger s.threads[tid].pc == L.Armada_PC_client_End} :: tid in s.threads ==> s.threads[tid].pc != L.Armada_PC_client_End)
    && (forall tid {:trigger L.Armada_GetThreadLocalView(s, tid).globals.locks}:: tid in s.threads ==> |s.mem.globals.locks| == |Armada_GetThreadLocalViewLength(s, tid).globals.locks|)
    && (forall tid {:trigger s.threads[tid].top.Armada_StackFrame_main?} :: tid in s.threads && s.threads[tid].top.Armada_StackFrame_main? ==>
      |s.threads[tid].storeBuffer| == 0 && tid !in s.ghosts.Q)
  }

  predicate new_tid_trigger(tid: uint64)
  {
    true
  }

  predicate inv_wf(s: Armada_TotalState)
  {
    && (forall tid {:trigger new_tid_trigger(tid)} :: new_tid_trigger(tid) ==> 0 <= tid as int < |s.mem.globals.locks|)
    && (forall tid {:trigger s.mem.globals.locks[tid]} {:trigger tid in s.threads} {:trigger lock_size_trigger(tid)} :: tid in s.threads && lock_size_trigger(tid) ==> 0 < tid as int < |s.mem.globals.locks|)
    && (forall tid :: tid in s.ghosts.Q ==> tid in s.threads)
    && (forall idx {:trigger s.ghosts.Q[idx]} :: 0 <= idx < |s.ghosts.Q| ==> s.ghosts.Q[idx] in s.ghosts.Q)
  }

  predicate inv_sb(s: Armada_TotalState)
  {
    inv_wf(s) ==>
      var threads := s.threads;
      forall tid {:trigger threads[tid].storeBuffer} :: tid in threads ==> inv_sb_thread(tid, threads[tid].storeBuffer, s)
  }

  predicate inv_sb_thread(tid: Armada_ThreadHandle, sb: seq<Armada_StoreBufferEntry>, s: Armada_TotalState)
    requires inv_wf(s)
    requires tid in s.threads
  {
    && (if |sb| == 0 then true
        else if |sb| == 2 then
          || (sb[0].pc.Armada_PC_release_7? && sb[1].pc.Armada_PC_acquire_Start?)
          || (sb[0].pc.Armada_PC_acquire_4? && sb[1].pc.Armada_PC_acquire_5?)
        else if |sb| == 1 then
          || sb[0].pc.Armada_PC_release_7? || sb[0].pc.Armada_PC_acquire_Start?
          || sb[0].pc.Armada_PC_acquire_4? || sb[0].pc.Armada_PC_acquire_5?
        else false)
    && (forall entry {:trigger entry.pc.Armada_PC_release_7?} :: entry in sb && entry.pc.Armada_PC_release_7? ==>
      inv_entry_release_7(tid, entry, s))
    && (forall entry {:trigger entry.pc.Armada_PC_acquire_Start?} :: entry in sb && entry.pc.Armada_PC_acquire_Start? ==>
      inv_entry_acquire_Start(tid, entry, s))
    && (forall entry {:trigger entry.pc.Armada_PC_acquire_4?} :: entry in sb && entry.pc.Armada_PC_acquire_4? ==>
      inv_entry_acquire_4(tid, entry, s))
    && (forall entry {:trigger entry.pc.Armada_PC_acquire_5?} :: entry in sb && entry.pc.Armada_PC_acquire_5? ==>
      inv_entry_acquire_5(tid, entry, s))
    && (|sb| == 1 && inv_entry_acquire_5(tid, sb[0], s) ==> s.mem.globals.locks[tid].wait != 0)
    && (|sb| == 1 && inv_entry_acquire_4(tid, sb[0], s) ==> s.threads[tid].pc.Armada_PC_acquire_5?)
  }

  predicate inv_entry_release_7(tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry, s: Armada_TotalState)
    requires inv_wf(s)
  {
    var Q, threads, locks := s.ghosts.Q, s.threads, s.mem.globals.locks;
    && |Q| != 0
    && s.ghosts.old_owner == tid
    && tid !in Q && waiting_pc(threads[Q[0]].pc)
    && s.mem.globals.locks[Q[0]].wait != 0
    && entry == wait_entry(Q[0], 0, L.Armada_PC_release_7)
  }

  predicate inv_entry_acquire_Start(tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry, s: Armada_TotalState)
    requires inv_wf(s)
    requires tid in s.threads
  {
    var Q, threads := s.ghosts.Q, s.threads;
    && tid !in Q
    && threads[tid].pc.Armada_PC_acquire_1?
    && entry == next_entry(tid, 0, L.Armada_PC_acquire_Start)
  }

  predicate inv_entry_acquire_4(tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry, s: Armada_TotalState)
    requires inv_wf(s)
    requires tid in s.threads
  {
    var Q, threads := s.ghosts.Q, s.threads;
    && tid in Q
    && !owner_of(tid, Q)
    && (threads[tid].pc.Armada_PC_acquire_5? || waiting_pc(threads[tid].pc))
    && entry == wait_entry(tid, 1, L.Armada_PC_acquire_4)
  }

  predicate inv_entry_acquire_5(tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry, s: Armada_TotalState)
    requires inv_wf(s)
  {
    var Q, threads := s.ghosts.Q, s.threads;
    && tid in Q
    && waiting_pc(threads[tid].pc)
    && !owner_of(tid, Q)
    && entry == next_entry(pred(tid, Q), tid, L.Armada_PC_acquire_5)
  }

  predicate inv_next_deliver(s: Armada_TotalState)
  {
    inv_wf(s) ==>
    && var threads, Q := s.threads, s.ghosts.Q;
    && (forall tid {:trigger waiting_pc(threads[tid].pc)} :: tid in Q && !owner_of(tid, Q) && waiting_pc(threads[tid].pc) && |threads[tid].storeBuffer| == 0 ==> s.mem.globals.locks[pred(tid, Q)].next != 0)
    && (forall tid {:trigger pred(tid, Q)} :: tid in Q && !owner_of(tid, Q) && s.mem.globals.locks[pred(tid, Q)].next != 0 ==>
       s.mem.globals.locks[tid].wait != 0 &&
       waiting_pc(threads[tid].pc) &&
       |s.threads[tid].storeBuffer| == 0 &&
       forall tid' {:trigger threads[tid'].storeBuffer} :: tid' in threads ==> next_entry(pred(tid, Q), tid', L.Armada_PC_acquire_5) !in threads[tid'].storeBuffer)
  }

  predicate inv_wait_clear(s: Armada_TotalState)
  {
    inv_wf(s) ==>
    //except in acquire, no wait clear
    && var threads, Q := s.threads, s.ghosts.Q;
    && (forall tid {:trigger s.mem.globals.locks[tid]} :: tid in threads ==>
      Armada_GetThreadLocalViewLength(s, tid).globals.locks[tid].wait == 0 ==> s.mem.globals.locks[tid].wait == 0)
    && (forall tid :: tid in threads && waiting_pc(threads[tid].pc) && Armada_GetThreadLocalViewLength(s, tid).globals.locks[tid].wait == 0 ==>
       owner_of(tid, Q))
  }

  predicate inv_Q(s: Armada_TotalState)
  {
    inv_wf(s) ==>
    && var Q, locks, threads, tail := s.ghosts.Q, s.mem.globals.locks, s.threads, s.ghosts.ghost_tail;
      // linked-list correctness
      && (forall tid {:trigger pred(tid, Q)} :: tid in Q && !owner_of(tid, Q) ==>
          locks[pred(tid, Q)].next == 0 || (locks[pred(tid, Q)].next == tid && waiting_pc(threads[tid].pc)))

      && (|Q| != 0 ==> locks[Q[|Q|-1]].next == 0)
      && (|Q| == 0 <==> tail == 0)
      && (|Q| != 0 ==> tail == Q[|Q|-1])
      && unique_Q(Q)
  }

  predicate {:opaque} unique_Q(Q: seq<uint64>)
  {
    forall i, j :: 0 <= i < j < |Q| ==> Q[i] != Q[j]
  }

  lemma unique_Q_singleton(Q: seq<uint64>)
    requires unique_Q(Q)
    requires |Q| != 0
    ensures Q[0] == Q[|Q|-1] ==> Q == [Q[0]]
  {
    reveal unique_Q();
  }

  lemma simple_unique_Q_facts(Q: seq<uint64>)
    requires unique_Q(Q)
    ensures |Q| > 1 ==> !owner_of(Q[1], Q) && Q[0] == pred(Q[1], Q)
    ensures forall tid {:trigger pred(tid, Q)} :: tid in Q && !owner_of(tid, Q) ==> pred(tid, Q) != Q[|Q|-1]
  {
    reveal unique_Q();
  }

  lemma unique_Q_facts(Q: seq<uint64>)
    requires unique_Q(Q)
    ensures |Q| > 1 ==> !owner_of(Q[1], Q) && Q[0] == pred(Q[1], Q)
    ensures forall tid1, tid2 {:trigger pred(tid1, Q), pred(tid2, Q)} :: tid1 in Q && tid2 in Q && tid1 != tid2 && !owner_of(tid1, Q) && !owner_of(tid2, Q) ==> pred(tid1, Q) != pred(tid2, Q)
    ensures forall tid {:trigger pred(tid, Q)} :: tid in Q && !owner_of(tid, Q) ==> pred(tid, Q) != Q[|Q|-1]
  {
    reveal unique_Q();
  }

  predicate owner_of(tid: uint64, Q: seq<uint64>)
  {
    |Q| != 0 && Q[0] == tid
  }

  function pred(tid: uint64, Q: seq<uint64>): (predecessor: uint64)
    requires tid in Q
    requires ! owner_of(tid, Q)
    ensures predecessor in Q
  {
    var idx :| 0 < idx < |Q| && Q[idx] == tid;
    Q[idx - 1]
  }

  lemma empty_Q_unique()
    ensures unique_Q([])
  {
    reveal unique_Q();
  }

  lemma Q_pop_facts(Q: seq<uint64>)
    requires unique_Q(Q)
    ensures |Q| > 0 ==> Q[0] !in Q[1..]
    ensures |Q| > 0 ==> unique_Q(Q[1..])
    ensures forall tid :: tid in Q && !owner_of(tid, Q) && !owner_of(tid, Q[1..]) ==> pred(tid, Q) == pred(tid, Q[1..])
    ensures |Q| > 1 ==> Q[|Q|-1] == Q[1..][|Q[1..]|-1]
  {
    reveal unique_Q();
    if |Q| > 0 {
      unique_Q_singleton(Q);
    }
  }

  lemma Q_push_facts(Q: seq<uint64>, elem: uint64)
    requires unique_Q(Q)
    requires elem !in Q
    ensures unique_Q(Q + [elem])
    ensures forall tid :: tid in Q && !owner_of(tid, Q) ==> pred(tid, Q) == pred(tid, Q + [elem])
  {
    reveal unique_Q();
  }

  lemma storebuffer_same_after_apply_same(mem1: Armada_SharedMemory, mem2: Armada_SharedMemory, storeBuffer: seq<L.Armada_StoreBufferEntry>)
    requires mem1.globals.locks == mem2.globals.locks
    ensures Armada_ApplyStoreBufferLength(mem1, storeBuffer).globals.locks == Armada_ApplyStoreBufferLength(mem2, storeBuffer).globals.locks
    decreases storeBuffer
  {
    reveal Armada_ApplyStoreBufferLength();
    if |storeBuffer| == 0 {

    } else {
      storebuffer_same_after_apply_same(Armada_ApplyStoreBufferEntryLength(mem1, storeBuffer[0]), Armada_ApplyStoreBufferEntryLength(mem1, storeBuffer[0]), storeBuffer[1..]);
    }
  }

  lemma storebuffer_same_localview_same(s: Armada_TotalState, s': Armada_TotalState, tid: Armada_ThreadHandle)
    requires tid in s.threads && tid in s'.threads
    requires s.threads[tid].storeBuffer == s'.threads[tid].storeBuffer
    requires s.mem.globals.locks == s'.mem.globals.locks
    ensures Armada_GetThreadLocalViewLength(s, tid).globals.locks == Armada_GetThreadLocalViewLength(s', tid).globals.locks
  {
    reveal Armada_GetThreadLocalViewLength();
    storebuffer_same_after_apply_same(s.mem, s'.mem, s.threads[tid].storeBuffer);
  }

  lemma storebuffer_same_localview_general(s: Armada_TotalState, s': Armada_TotalState)
    requires s.mem.globals.locks == s'.mem.globals.locks
    ensures forall tid :: tid in s.threads && tid in s'.threads && s.threads[tid].storeBuffer == s'.threads[tid].storeBuffer ==> Armada_GetThreadLocalViewLength(s, tid).globals.locks == Armada_GetThreadLocalViewLength(s', tid).globals.locks
  {
    forall tid | tid in s.threads && tid in s'.threads && s.threads[tid].storeBuffer == s'.threads[tid].storeBuffer
      ensures Armada_GetThreadLocalViewLength(s, tid).globals.locks == Armada_GetThreadLocalViewLength(s', tid).globals.locks
    {
      storebuffer_same_after_apply_same(s.mem, s'.mem, s.threads[tid].storeBuffer);
    }
  }

  lemma apply_storebuffer_snoc(mem: Armada_SharedMemory, storeBuffer: seq<Armada_StoreBufferEntry>, entry: Armada_StoreBufferEntry) returns (new_mem: Armada_SharedMemory)
    ensures Armada_ApplyStoreBufferLength(mem, storeBuffer + [entry]) == Armada_ApplyStoreBufferEntryLength(Armada_ApplyStoreBufferLength(mem, storeBuffer), entry)
    ensures |mem.globals.locks| == |new_mem.globals.locks|
    decreases |storeBuffer|
  {
    reveal Armada_ApplyStoreBufferEntryLength();
    reveal Armada_ApplyStoreBufferLength();

    if |storeBuffer| == 0 {

    } else {
      var storeBuffer', entry' := storeBuffer[1..], storeBuffer[0];
      assert (storeBuffer + [entry])[1..] == storeBuffer' + [entry];
      var mem' := Armada_ApplyStoreBufferEntryLength(mem, entry');
      assert Armada_ApplyStoreBufferLength(mem, storeBuffer + [entry]) == Armada_ApplyStoreBufferLength(mem', storeBuffer' + [entry]);
      assert Armada_ApplyStoreBufferEntryLength(Armada_ApplyStoreBufferLength(mem', storeBuffer'), entry) == Armada_ApplyStoreBufferEntryLength(Armada_ApplyStoreBufferLength(mem', storeBuffer'), entry);
      var _ := apply_storebuffer_snoc(mem', storeBuffer', entry);
    }

    return Armada_ApplyStoreBufferLength(mem, storeBuffer);
  }

  lemma next_wait_non_interference(s: Armada_TotalState, tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry)
    requires inv_wf(s)
    requires tid in s.threads
    requires entry.loc.Armada_StoreBufferLocation_Unaddressable?
    requires |entry.loc.fields| == 2
    requires entry.loc.fields[1] == 1
    ensures Armada_GetThreadLocalViewLength(s, tid).globals.locks[tid].wait == Armada_GetThreadLocalViewLength(Armada_AppendToThreadStoreBuffer(s, tid, entry), tid).globals.locks[tid].wait
  {
    reveal Armada_GetThreadLocalViewLength();
    reveal Armada_ApplyStoreBufferLength();
    reveal Armada_ApplyStoreBufferEntryLength();
    var mem' := Armada_GetThreadLocalViewLength(s, tid);
    var s' := Armada_AppendToThreadStoreBuffer(s, tid, entry);
    assert s'.mem == s.mem;
    assert s'.threads[tid].storeBuffer == s.threads[tid].storeBuffer + [entry];

    var _ := apply_storebuffer_snoc(s.mem, s.threads[tid].storeBuffer, entry);
    assert Armada_GetThreadLocalViewLength(Armada_AppendToThreadStoreBuffer(s, tid, entry), tid) == Armada_ApplyStoreBufferEntryLength(mem', entry);
  }

  lemma wait_wait_non_interference(s: Armada_TotalState, tid: Armada_ThreadHandle, entry: Armada_StoreBufferEntry)
    requires inv_wf(s)
    requires tid in s.threads
    requires entry.loc.Armada_StoreBufferLocation_Unaddressable?
    requires |entry.loc.fields| == 2
    requires entry.loc.fields[0] != tid as int
    ensures Armada_GetThreadLocalViewLength(s, tid).globals.locks[tid].wait == Armada_GetThreadLocalViewLength(Armada_AppendToThreadStoreBuffer(s, tid, entry), tid).globals.locks[tid].wait
  {
    reveal Armada_GetThreadLocalViewLength();
    reveal Armada_ApplyStoreBufferLength();
    reveal Armada_ApplyStoreBufferEntryLength();
    var mem' := Armada_GetThreadLocalViewLength(s, tid);
    var s' := Armada_AppendToThreadStoreBuffer(s, tid, entry);
    assert s'.mem == s.mem;
    assert s'.threads[tid].storeBuffer == s.threads[tid].storeBuffer + [entry];

    var _ := apply_storebuffer_snoc(s.mem, s.threads[tid].storeBuffer, entry);
    assert Armada_GetThreadLocalViewLength(Armada_AppendToThreadStoreBuffer(s, tid, entry), tid) == Armada_ApplyStoreBufferEntryLength(mem', entry);
  }

  lemma locks_independence(mem1: Armada_SharedMemory, mem2: Armada_SharedMemory, sb: seq<Armada_StoreBufferEntry>)
    requires mem1.globals.locks == mem2.globals.locks
    ensures Armada_ApplyStoreBufferLength(mem1, sb).globals.locks == Armada_ApplyStoreBufferLength(mem2, sb).globals.locks
    decreases |sb|
  {
    reveal Armada_ApplyStoreBufferLength();
    reveal Armada_ApplyStoreBufferEntryLength();
    if |sb| == 0 {

    } else {
      var mem1', mem2' := Armada_ApplyStoreBufferEntryLength(mem1, sb[0]), Armada_ApplyStoreBufferEntryLength(mem2, sb[0]);
      locks_independence(mem1', mem2', sb[1..]);
    }
  }

  lemma locks_independence_generalized(mem1: Armada_SharedMemory, mem2: Armada_SharedMemory)
    requires mem1.globals.locks == mem2.globals.locks
    ensures forall sb :: Armada_ApplyStoreBufferLength(mem1, sb).globals.locks == Armada_ApplyStoreBufferLength(mem2, sb).globals.locks
  {
    reveal Armada_ApplyStoreBufferLength();
    forall sb: seq<Armada_StoreBufferEntry>
      ensures Armada_ApplyStoreBufferLength(mem1, sb).globals.locks == Armada_ApplyStoreBufferLength(mem2, sb).globals.locks
    {
      locks_independence(mem1, mem2, sb);
    }
  }

  lemma wait_cleared_shared_memory_changed(mem1: Armada_SharedMemory, mem2: Armada_SharedMemory, sb: seq<Armada_StoreBufferEntry>, tid: Armada_ThreadHandle)
    requires 0 < tid as int < |mem2.globals.locks|
    requires 0 < tid as int < |mem1.globals.locks|
    requires Armada_ApplyStoreBufferLength(mem1, sb).globals.locks[tid].wait != Armada_ApplyStoreBufferLength(mem2, sb).globals.locks[tid].wait
    ensures Armada_ApplyStoreBufferLength(mem1, sb).globals.locks[tid].wait == mem1.globals.locks[tid].wait
    ensures Armada_ApplyStoreBufferLength(mem2, sb).globals.locks[tid].wait == mem2.globals.locks[tid].wait
    decreases |sb|
  {

    reveal Armada_ApplyStoreBufferLength();
    reveal Armada_ApplyStoreBufferEntryLength();
    if |sb| == 0 {

    } else {
      var mem1', mem2' := Armada_ApplyStoreBufferEntryLength(mem1, sb[0]), Armada_ApplyStoreBufferEntryLength(mem2, sb[0]);
      wait_cleared_shared_memory_changed(mem1', mem2', sb[1..], tid);
    }
  }

  lemma wait_cleared_entry_release_7(s: Armada_TotalState, tid: Armada_ThreadHandle, owner: Armada_ThreadHandle)
    requires inv_wf(s)
    requires tid in s.threads
    requires owner in s.threads
    requires inv_sb_thread(tid, s.threads[tid].storeBuffer, s)
    requires |s.threads[tid].storeBuffer| != 0
    requires s.mem.globals.locks[owner].wait != 0
    requires Armada_ApplyStoreBufferEntryLength(s.mem, s.threads[tid].storeBuffer[0]).globals.locks[owner].wait == 0
    ensures s.threads[tid].storeBuffer[0].loc.fields == [owner as int, 0]
    ensures owner_of(owner, s.ghosts.Q)
    ensures inv_entry_release_7(tid, s.threads[tid].storeBuffer[0], s)
  {
    reveal Armada_ApplyStoreBufferEntryLength();
  }

  predicate lock_size_trigger(tid: Armada_ThreadHandle)
  {
    true
  }
}
