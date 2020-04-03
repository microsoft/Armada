include "A.dfy"
include "../../Armada/ArmadaCommonDefinitions.dfy"

module ABHelpers
{
  import opened ArmadaCommonDefinitions = ArmadaCommonDefinitions
  import L = A

  predicate MyGlobalInvariant(s:L.Armada_TotalState)
  {
    && (forall tid :: tid in s.threads ==> tid == s.tid_init)
    && (forall tid :: tid in s.threads ==> s.threads[tid].storeBuffer == [])
  }

  predicate MyYieldPredicate(s:L.Armada_TotalState, s':L.Armada_TotalState, tid:Armada_ThreadHandle)
  {
    && s'.mem.globals.x == s.mem.globals.x
    && s'.mem.globals.y == s.mem.globals.y
    && s'.mem.globals.z == s.mem.globals.z
  }
}
