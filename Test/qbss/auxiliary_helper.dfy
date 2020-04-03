include "QueueBSS_WithAbstractQueue.dfy"
  include "../../Armada/util/collections/seqs.i.dfy"
include "SharedStructs.dfy"

module auxiliary_helper {
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions
  import opened util_collections_seqs_i = util_collections_seqs_i
  import opened SharedStructs = SharedStructs

  import L = QueueBSS_WithAbstractQueue
  datatype WriteIndexSBEntry = WriteIndexSBEntry(position:int, value:uint64)

  function DecrementPosition(w:WriteIndexSBEntry): WriteIndexSBEntry
  {
    w.(position := w.position - 1)
  }

  function TauUpdateWriteSequence(ws:seq<WriteIndexSBEntry>) : seq<WriteIndexSBEntry>
  {
    if ws == [] then
      []
    else
      if ws[0].position == 0 then
      MapSeqToSeq(ws[1..], DecrementPosition)
      else
        MapSeqToSeq(ws, DecrementPosition)
  }

  function StoreBufferUpdateWriteSequence(sb:seq<L.Armada_StoreBufferEntry>, sb':seq<L.Armada_StoreBufferEntry>, ws:seq<WriteIndexSBEntry>) :
    seq<WriteIndexSBEntry>
  {
    if sb == sb' || sb' == [] then
      ws
    else if sb'[|sb'| - 1].loc == L.Armada_StoreBufferLocation_Unaddressable(L.Armada_GlobalStaticVar_queue, [Armada_FieldStruct(Armada_FieldType_QbssState'write_index)])
      && sb'[|sb'| - 1].value.Armada_PrimitiveValue_uint64? then
      ws + [WriteIndexSBEntry(|sb'| - 1, sb'[|sb'| - 1].value.n_uint64)]
    else
      ws
  }

}
