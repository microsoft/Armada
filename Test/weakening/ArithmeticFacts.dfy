// Use /arith:2 to verify this file

include "../../Armada/ArmadaCommonDefinitions.dfy"
include "EF/specs.dfy"

module ArithmeticFactsModule
{
  import opened ArmadaCommonDefinitions
  import opened ArmadaModule_specs

  function ThreadToInstructionCount_LPlus(s:LPlusState, tid:Armada_ThreadHandle) : (v:int)
  {
    if tid in s.s.threads then PCToInstructionCount_L(s.s.threads[tid].pc) else -1
  }

  lemma lemma_Equivalence(x:int)
    ensures (x + 1) * (x + 1) == x * x + 2 * x + 1
  {
  }
}

