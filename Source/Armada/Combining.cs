using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Armada
{
  public class CombiningProofGenerator : AbstractProofGenerator
  {
    private CombiningStrategyDecl strategy;
    private HashSet<ArmadaPC> innerPCs;
    private ArmadaPC startPC;
    private ArmadaPC endPC;
    private ArmadaPC singlePC;
    private Dictionary<ArmadaPC, List<NextRoutine>> pcToNextRoutines;
    private NextRoutine singleNextRoutine;

    public CombiningProofGenerator(ProofGenerationParams i_pgp, CombiningStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, $"Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the combining strategy");
        return;
      }

      if (!MakePCMap()) {
        return;
      }

      AddIncludesAndImports();
      GenerateProofGivenMap();
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC map
    ////////////////////////////////////////////////////////////////////////

    bool MakePCMap()
    {
      startPC = pgp.symbolsLow.GetPCForMethodAndLabel(strategy.StartLabel.val);
      if (startPC == null) {
        AH.PrintError(pgp.prog, $"You specified a start label for combining of {strategy.StartLabel.val}, but that label doesn't exist in level {pgp.mLow.Name}.  Remember to prefix label names with the method name and an underscore, e.g., use main_lb1 if you have label lb1: in method main.");
        return false;
      }

      endPC = pgp.symbolsLow.GetPCForMethodAndLabel(strategy.EndLabel.val);
      if (endPC == null) {
        AH.PrintError(pgp.prog, $"You specified an end label for combining of {strategy.EndLabel.val}, but that label doesn't exist in level {pgp.mLow.Name}.  Remember to prefix label names with the method name and an underscore, e.g., use main_lb1 if you have label lb1: in method main.");
        return false;
      }

      if (endPC.methodName != startPC.methodName) {
        AH.PrintError(pgp.prog, $"The start and end labels you provided for combining aren't from the same method in {pgp.mLow.Name}.  The start label {strategy.StartLabel.val} is in method {startPC.methodName} and the end label {strategy.EndLabel.val} is in method {endPC.methodName}.");
        return false;
      }

      if (endPC.instructionCount <= startPC.instructionCount) {
        AH.PrintError(pgp.prog, $"The end label you provided for combining ({strategy.EndLabel.val}) isn't after the start label you provided for combining ({strategy.StartLabel.val}).");
        return false;
      }

      singlePC = pgp.symbolsHigh.GetPCForMethodAndLabel(strategy.SingleLabel.val);
      if (singlePC == null) {
        AH.PrintError(pgp.prog, $"You specified a single label for combining of {strategy.SingleLabel.val}, but that label doesn't exist in level {pgp.mHigh.Name}.  Remember to prefix label names with the method name and an underscore, e.g., use main_lb1 if you have label lb1: in method main.");
        return false;
      }

      if (singlePC.methodName != startPC.methodName) {
        AH.PrintError(pgp.prog, $"The start and end labels you provided for combining aren't from the same method as the single label you provided.  That is, {strategy.StartLabel.val} and {strategy.EndLabel.val} are both from method {startPC.methodName}, but the single label {strategy.SingleLabel.val} is from method {singlePC.methodName}.");
        return false;
      }

      if (singlePC.instructionCount != startPC.instructionCount) {
        AH.PrintError(pgp.prog, $"The start label you provided isn't at the same position in its method as the single label you provided.  That is, {strategy.StartLabel.val} is preceded by {startPC.instructionCount} instructions in {pgp.mLow.Name}, but {strategy.SingleLabel.val} is preceded by {singlePC.instructionCount} instructions in {pgp.mHigh.Name}.");
        return false;
      }

      innerPCs = new HashSet<ArmadaPC>();
      pcMap = new Dictionary<ArmadaPC, ArmadaPC>();
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        if (pc.methodName != startPC.methodName) {
          pcMap[pc] = pc.CloneWithNewSymbolTable(pgp.symbolsHigh);
        }
        else if (pc.instructionCount < startPC.instructionCount) {
          pcMap[pc] = pc.CloneWithNewSymbolTable(pgp.symbolsHigh);
        }
        else if (pc.instructionCount == startPC.instructionCount) {
          pcMap[pc] = singlePC;
        }
        else if (pc.instructionCount <= endPC.instructionCount) {
          innerPCs.Add(pc);
          pcMap[pc] = new ArmadaPC(pgp.symbolsHigh, pc.methodName, singlePC.instructionCount + 1);
        }
        else {
          pcMap[pc] = new ArmadaPC(pgp.symbolsHigh, pc.methodName, pc.instructionCount + startPC.instructionCount - endPC.instructionCount);
        }
      }

      ExtendPCMapWithExternalAndStructsMethods();
      GenerateNextRoutineMap(false);

      var innerOrStartPCs = new HashSet<ArmadaPC>(innerPCs);
      innerOrStartPCs.Add(startPC);
      pcToNextRoutines = new Dictionary<ArmadaPC, List<NextRoutine>>();
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var pc = nextRoutine.pc;
        if (innerOrStartPCs.Contains(pc)) {
          if (!pcToNextRoutines.ContainsKey(pc)) {
            pcToNextRoutines[pc] = new List<NextRoutine>();
          }
          pcToNextRoutines[pc].Add(nextRoutine);
        }
      }

      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        if (nextRoutine.pc == singlePC) {
          singleNextRoutine = nextRoutine;
          break;
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/combining/ArmadaCombining.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("GenericArmadaSpecModule");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");
      pgp.MainProof.AddImport("ArmadaCombiningSpecModule");
      pgp.MainProof.AddImport("ArmadaCombiningModule");
      pgp.MainProof.AddImport("GeneralRefinementLemmasModule");
      pgp.MainProof.AddImport("RefinementConvolutionModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy", "invariants");
      pgp.AddImport("GenericArmadaSpecModule", null, "invariants");
      pgp.AddImport("GenericArmadaLemmasModule", null, "invariants");
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateInnerPCPredicate();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateNextState_H();
      GenerateLocalViewCommutativityLemmas();
      GenerateGenericStoreBufferLemmas_L();

      GeneratePCFunctions_L();
      AddStackMatchesMethodInvariant();
      GenerateInvariantProof(pgp);

      GenerateCombiningRequestComponents();
      GenerateCombiningRequest();
      GenerateLInitImpliesHInitLemma();
      GenerateLemmasSupportingValidRequest();
      GenerateIsValidRequest();
      GenerateFinalProof();
    }

    private void GenerateInnerPCPredicate()
    {
      string str;

      str = @"
        predicate IsInnerPC(pc:L.Armada_PC)
        {
      ";
      foreach (var pc in innerPCs)
      {
        str += $"  || pc.{pc}?\n";
      }
      str += "}";
      pgp.AddPredicate(str);
    }

    private void GenerateCombiningRequestComponents()
    {
      CreateGenericArmadaSpec_L();
      CreateGenericArmadaSpec_H();
    }

    private void GenerateCombiningRequest()
    {
      var acrequest = AH.MakeGenericTypeSpecific("ArmadaCombiningRequest",
                                                 new List<Type> {
                                                   AH.ReferToType("LPlusState"),
                                                   AH.ReferToType("L.Armada_TraceEntry"),
                                                   AH.ReferToType("L.Armada_PC"),
                                                   AH.ReferToType("HState"),
                                                   AH.ReferToType("H.Armada_TraceEntry"),
                                                   AH.ReferToType("H.Armada_PC")
                                                 });
      pgp.MainProof.AddTypeSynonymDecl("ACRequest", acrequest);

      string str = @"
        function GetArmadaCombiningRequest() : ACRequest
        {
          ArmadaCombiningRequest(LPlus_GetSpecFunctions(), H.Armada_GetSpecFunctions(),
                                 GetLPlusHRefinementRelation(), InductiveInv,
                                 ConvertTotalState_LPlusH, ConvertTraceEntry_LH, ConvertPC_LH,  IsInnerPC)
        }
      ";
      pgp.AddFunction(str);
    }

    protected virtual void GenerateLiftStepLemmaForInnerNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var str = $@"
        lemma lemma_LiftStep_{nextRoutineName}(ls:LPlusState, lstep:L.Armada_TraceEntry)
          requires InductiveInv(ls)
          requires LPlus_ValidStep(ls, lstep)
          requires lstep.Armada_TraceEntry_{nextRoutineName}?
          requires var tid := lstep.tid; tid in ls.s.threads ==> !IsInnerPC(ls.s.threads[tid].pc)
          requires var tid := lstep.tid;
                   var ls' := LPlus_GetNextStateAlways(ls, lstep); 
                   tid in ls'.s.threads ==> !IsInnerPC(ls'.s.threads[tid].pc)
          ensures  var ls' := LPlus_GetNextStateAlways(ls, lstep);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hstep := ConvertTraceEntry_LH(lstep);
                   && hstep.tid == lstep.tid
                   && hstep.Armada_TraceEntry_Tau? == lstep.Armada_TraceEntry_Tau?
                   && H.Armada_ValidStep(hs, hstep)
                   && H.Armada_GetNextStateAlways(hs, hstep) == ConvertTotalState_LPlusH(ls')
        {{
          var tid := lstep.tid;
          var ls' := LPlus_GetNextStateAlways(ls, lstep); 
          assert tid in ls.s.threads;
          assert tid in ls'.s.threads;
          assert IsInnerPC(ls.s.threads[tid].pc) || IsInnerPC(ls'.s.threads[tid].pc);
          assert false;
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateNonInnerStepsLiftableLemmas()
    {
      var finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType == NextType.Tau) {
          GenerateLiftStepLemmaForTauNextRoutine(nextRoutine);
        }
        else {
          var pc = nextRoutine.pc;
          if (pc != null && pc.methodName == startPC.methodName && pc.instructionCount >= startPC.instructionCount &&
              pc.instructionCount <= endPC.instructionCount) {
            GenerateLiftStepLemmaForInnerNextRoutine(nextRoutine);
          }
          else {
            GenerateLiftStepLemmaForNormalNextRoutine(nextRoutine);
          }
        }
        var nextRoutineName = nextRoutine.NameSuffix;
        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LiftStep_{nextRoutineName}(ls, lstep);";
      }

      string str = $@"
        lemma lemma_LiftNonInnerStep(ls:LPlusState, lstep:L.Armada_TraceEntry)
          requires InductiveInv(ls)
          requires LPlus_ValidStep(ls, lstep)
          requires var tid := lstep.tid; tid in ls.s.threads ==> !IsInnerPC(ls.s.threads[tid].pc)
          requires var tid := lstep.tid;
                   var ls' := LPlus_GetNextStateAlways(ls, lstep); 
                   tid in ls'.s.threads ==> !IsInnerPC(ls'.s.threads[tid].pc)
          ensures  var ls' := LPlus_GetNextStateAlways(ls, lstep);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hstep := ConvertTraceEntry_LH(lstep);
                   && hstep.tid == lstep.tid
                   && hstep.Armada_TraceEntry_Tau? == lstep.Armada_TraceEntry_Tau?
                   && H.Armada_ValidStep(hs, hstep)
                   && H.Armada_GetNextStateAlways(hs, hstep) == ConvertTotalState_LPlusH(ls')
        {{
          match lstep {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_NonInnerStepsLiftable(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures  NonInnerStepsLiftable(acr)
        {
          forall ls, lstep {:trigger NonInnerStepsLiftableConditions(acr, ls, lstep)}
            | NonInnerStepsLiftableConditions(acr, ls, lstep)
            ensures var ls' := acr.l.step_next(ls, lstep);
                    var hs := acr.lstate_to_hstate(ls);
                    var hstep := acr.lonestep_to_honestep(lstep);
                    var hs' := acr.lstate_to_hstate(ls');
                    && acr.l.step_to_thread(lstep) == acr.h.step_to_thread(hstep)
                    && acr.l.is_step_tau(lstep) == acr.h.is_step_tau(hstep)
                    && acr.h.step_valid(hs, hstep)
                    && hs' == acr.h.step_next(hs, hstep)
          {
            lemma_LiftNonInnerStep(ls, lstep);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLInitImpliesHInitLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      string str;

      str = @"
        lemma lemma_LInitImpliesHInit(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures  LInitImpliesHInit(acr)
        {
          forall ls | acr.l.init(ls)
            ensures acr.h.init(acr.lstate_to_hstate(ls))
          {
            var hs := acr.lstate_to_hstate(ls);
            var hconfig := ConvertConfig_LH(ls.config);

            lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
            assert H.Armada_InitConfig(hs, hconfig);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLHYieldingCorrespondenceLemma()
    {
      string str;

      str = @"
        lemma lemma_LHYieldingCorrespondence(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures LHYieldingCorrespondence(acr)
        {
          forall lpc:L.Armada_PC
            ensures var hpc := acr.lpc_to_hpc(lpc);
                    acr.is_inner_pc(lpc) || (acr.h.is_pc_nonyielding(hpc) <==> acr.l.is_pc_nonyielding(lpc))
          {
            var hpc := acr.lpc_to_hpc(lpc);
            match lpc {
      ";

      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $@"        case {pc} => assert acr.is_inner_pc(lpc) || (acr.h.is_pc_nonyielding(hpc) <==> acr.l.is_pc_nonyielding(lpc));
";
      }

      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasSupportingValidRequest()
    {
      string str;

      GenerateNonInnerStepsLiftableLemmas();

      str = @"
        lemma lemma_LStateToHStateMapsPCsCorrectly(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures LStateToHStateMapsPCsCorrectly(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateLHYieldingCorrespondenceLemma();

      str = @"
        lemma lemma_StateConversionPreservesOK(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures StateConversionPreservesOK(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionSatisfiesRelation(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures StateConversionSatisfiesRelation(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ThreadCantAffectOtherThreadPCExceptViaFork(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures ThreadCantAffectOtherThreadPCExceptViaFork(acr.l)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_InnerPCsDontYield(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures InnerPCsDontYield(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_InnerPCPrecededByInnerOrYieldingPC(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures InnerPCPrecededByInnerOrYieldingPC(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_InnerPCSucceededByInnerOrYieldingPC(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures InnerPCSucceededByInnerOrYieldingPC(acr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateCanCombineInnerStepsLemmas();
    }

    ///////////////////////////////////////////////////////////////////////
    /// CanCombineInnerSteps lemmas
    ///////////////////////////////////////////////////////////////////////

    private void GenerateFullPathLemma(List<NextRoutine> nextRoutines, string pathLemmaSuffix)
    {
      string str = $@"
        lemma lemma_CombineInnerSteps_FullPath_{pathLemmaSuffix}(
          lstate0:LPlusState,
          ls':LPlusState,
          tid:Armada_ThreadHandle,
          hs:H.Armada_TotalState,
          hs':H.Armada_TotalState,
      ";
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        str += $@"
          lstep{i}:L.Armada_TraceEntry,
          lstate{i+1}:LPlusState,
        ";
      }
      str += $@"
          hstep:H.Armada_TraceEntry
          )
          requires InductiveInv(lstate0)
          requires hs == ConvertTotalState_LPlusH(lstate0)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires hstep == ConvertTraceEntry_LH(lstep0)
          requires H.Armada_ValidStep(hs, hstep)
          requires lstate{nextRoutines.Count()} == ls'
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
      ";
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        str += $@"
          requires LPlus_ValidStep(lstate{i}, lstep{i})
          requires lstate{i+1} == LPlus_GetNextStateAlways(lstate{i}, lstep{i})
        ";
      }
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        var nextRoutine = nextRoutines[i];
        str += $@"
          requires lstep{i}.tid == tid
          requires lstep{i}.Armada_TraceEntry_{nextRoutine.NameSuffix}?
        ";
      }
      str += @"
          ensures  hs' == H.Armada_GetNextStateAlways(hs, hstep)
        {
          lemma_StoreBufferAppendHasEffectOfAppendedEntryAlways_L();
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
        }
      ";
      pgp.AddLemma(str);
    }

    private string GeneratePathPrefixLemma(List<NextRoutine> nextRoutines, List<bool> branches, ArmadaPC lastPC)
    {
      string str;

      var pathLemmasForNextRoutines = new Dictionary<NextRoutine, string>();
      List<NextRoutine> lastNextRoutines;
      pcToNextRoutines.TryGetValue(lastPC, out lastNextRoutines);
  
      string pathLemmaSuffix = "";
      if (branches.Count > 0) {
        pathLemmaSuffix = String.Join("", branches.Select(b => b ? "T" : "F")) + "_";
      }
      pathLemmaSuffix += lastPC.Name;

      GenerateFullPathLemma(nextRoutines, pathLemmaSuffix);

      if (pgp.symbolsLow.AllMethods.LookupMethod(startPC.methodName).NonyieldingPCs.Contains(lastPC)) {
        foreach (var nextRoutine in lastNextRoutines) {
          var extendedNextRoutines = new List<NextRoutine>(nextRoutines);
          extendedNextRoutines.Add(nextRoutine);
          var extendedBranches = new List<bool>(branches);
          var nextType = nextRoutine.nextType;
          if (nextType == NextType.IfTrue || nextType == NextType.WhileTrue) {
            extendedBranches.Add(true);
          }
          else if (nextType == NextType.IfFalse || nextType == NextType.WhileFalse) {
            extendedBranches.Add(false);
          }
          pathLemmasForNextRoutines[nextRoutine] =
            GeneratePathPrefixLemma(extendedNextRoutines, extendedBranches, nextRoutine.endPC);
        }
      }

      str = $@"
        lemma lemma_CombineInnerSteps_PathPrefix_{pathLemmaSuffix}(
          lstate0:LPlusState,
          ls':LPlusState,
          tid:Armada_ThreadHandle,
          hs:H.Armada_TotalState,
          hs':H.Armada_TotalState,
      ";
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        str += $@"
          lstep{i}:L.Armada_TraceEntry,
          lstate{i+1}:LPlusState,
        ";
      }
      str += $@"
          lsteps:seq<L.Armada_TraceEntry>,
          lstates:seq<LPlusState>,
          hstep:H.Armada_TraceEntry
          )
          requires InductiveInv(lstate0)
          requires hs == ConvertTotalState_LPlusH(lstate0)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires hstep == ConvertTraceEntry_LH(lstep0)
          requires H.Armada_ValidStep(hs, hstep)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> !step.Armada_TraceEntry_Tau?
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
      ";
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        str += $@"
          requires LPlus_ValidStep(lstate{i}, lstep{i})
          requires lstate{i+1} == LPlus_GetNextStateAlways(lstate{i}, lstep{i})
        ";
      }
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        var nextRoutine = nextRoutines[i];
        str += $@"
          requires lstep{i}.tid == tid
          requires lstep{i}.Armada_TraceEntry_{nextRoutine.NameSuffix}?
        ";
      }
      str += $@"
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lstate{nextRoutines.Count()}, lsteps)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lstate{nextRoutines.Count()}, ls', lsteps)
          requires forall i :: 0 <= i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[i], tid)
          ensures  hs' == H.Armada_GetNextStateAlways(hs, hstep)
        {{
          if |lsteps| == 0 {{
            lemma_CombineInnerSteps_FullPath_{pathLemmaSuffix}(lstate0, ls', tid, hs, hs'
      ";
      for (int i = 0; i < nextRoutines.Count(); ++i) {
        str += $", lstep{i}, lstate{i+1}";
      }
      str += $@", hstep);
            return;
          }}

          var zero := 0;
          assert lstates[zero] == lstate{nextRoutines.Count()};
          assert LPlus_ValidStep(lstates[zero], lsteps[zero]);
          assert lstates[zero+1] == LPlus_GetNextStateAlways(lstates[zero], lsteps[zero]);
          assert !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[zero], tid);
        ";

      foreach (var nextRoutineInfo in pathLemmasForNextRoutines) {
        str += $@"
          if lsteps[zero].Armada_TraceEntry_{nextRoutineInfo.Key.NameSuffix}? {{
            lemma_CombineInnerSteps_PathPrefix_{nextRoutineInfo.Value}(lstate0, ls', tid, hs, hs'";
        for (int i = 0; i < nextRoutines.Count(); ++i) {
          str += $", lstep{i}, lstate{i+1}";
        }
        str += @", lsteps[0], lstates[1], lsteps[1..], lstates[1..], hstep);
            return;
          }
        ";
      }
      
      str += @"
          assert false;
        }
      ";
      pgp.AddLemma(str);

      return pathLemmaSuffix;
    }

    private void GenerateCanCombineInnerStepsLemmas()
    {
      string str;

      var pathLemmasForNextRoutines = new Dictionary<NextRoutine, string>();
      List<NextRoutine> startNextRoutines = pcToNextRoutines[startPC];

      foreach (var nextRoutine in startNextRoutines) {
        var branches = new List<bool>();
        var nextType = nextRoutine.nextType;
        if (nextType == NextType.IfTrue || nextType == NextType.WhileTrue) {
          branches.Add(true);
        }
        else if (nextType == NextType.IfFalse || nextType == NextType.WhileFalse) {
          branches.Add(false);
        }
        pathLemmasForNextRoutines[nextRoutine] = GeneratePathPrefixLemma(new List<NextRoutine> { nextRoutine }, branches, nextRoutine.endPC);
      }

      str = $@"
        lemma lemma_CombineInnerSteps(
          ls:LPlusState,
          ls':LPlusState,
          lsteps:seq<L.Armada_TraceEntry>,
          tid:Armada_ThreadHandle,
          lstates:seq<LPlusState>,
          hs:H.Armada_TotalState,
          hs':H.Armada_TotalState
          ) returns (
          hstep:H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires hs == ConvertTotalState_LPlusH(ls)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires |lsteps| > 0
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> !step.Armada_TraceEntry_Tau?
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid)
          requires forall i :: 0 < i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[i], tid)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
          requires tid in lstates[1].s.threads
          requires IsInnerPC(lstates[1].s.threads[tid].pc)
          ensures  !hstep.Armada_TraceEntry_Tau?
          ensures  H.Armada_ValidStep(hs, hstep)
          ensures  hs' == H.Armada_GetNextStateAlways(hs, hstep)
        {{
          assert LPlus_NextOneStep(lstates[0], lstates[1], lsteps[0]);
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          hstep := ConvertTraceEntry_LH(lsteps[0]);

          var zero := 0;
          assert lstates[zero] == ls;
          assert LPlus_ValidStep(lstates[zero], lsteps[zero]);
          assert lstates[zero+1] == LPlus_GetNextStateAlways(lstates[zero], lsteps[zero]);
      ";

      foreach (var nextRoutineInfo in pathLemmasForNextRoutines) {
        str += $@"
          if lsteps[zero].Armada_TraceEntry_{nextRoutineInfo.Key.NameSuffix}? {{
            lemma_CombineInnerSteps_PathPrefix_{nextRoutineInfo.Value}(ls, ls', tid, hs, hs', lsteps[0], lstates[1],
                                                                       lsteps[1..], lstates[1..], hstep);
            return;
          }}
        ";
      }
      
      str += @"
          assert false;
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_CanCombineInnerSteps(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures  CanCombineInnerSteps(acr)
        {
          forall ls, ls', lsteps, tid {:trigger CanCombineInnerStepsConditions(acr, ls, ls', lsteps, tid)}
            | CanCombineInnerStepsConditions(acr, ls, ls', lsteps, tid)
            ensures exists hstep :: InnerStepsCombined(acr, ls, ls', hstep)
          {
            var lstates := Armada_GetStateSequence(acr.l, ls, lsteps);
            var hs := acr.lstate_to_hstate(ls);
            var hs' := acr.lstate_to_hstate(ls');
            lemma_PropertiesOfGetStateSequence_LPlus(ls, lsteps, lstates);
            assert acr.l.step_valid(ls, lsteps[0]);
            var hstep := lemma_CombineInnerSteps(ls, ls', lsteps, tid, lstates, hs, hs');
            assert InnerStepsCombined(acr, ls, ls', hstep);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    ///////////////////////////////////////////////////////////////////////
    /// Final proof
    ///////////////////////////////////////////////////////////////////////

    private void GenerateIsValidRequest()
    {
      string str;

      str = @"
        lemma lemma_IsValidArmadaCombiningRequest(acr:ACRequest)
          requires acr == GetArmadaCombiningRequest()
          ensures  ValidArmadaCombiningRequest(acr)
        {
          lemma_InductiveInvInvariantInLPlusSpec(acr.l);
          lemma_OneStepRequiresOK_L(acr.l);
          lemma_InitImpliesYielding_L(acr.l);
          lemma_InitImpliesOK_L(acr.l);
          lemma_SteppingThreadHasPC_L(acr.l);
          lemma_TauLeavesPCUnchanged_L(acr.l);
          lemma_ThreadCantAffectOtherThreadPCExceptViaFork(acr);
          lemma_LInitImpliesHInit(acr);
          lemma_LStateToHStateMapsPCsCorrectly(acr);
          lemma_LHYieldingCorrespondence(acr);
          lemma_StateConversionPreservesOK(acr);
          lemma_StateConversionSatisfiesRelation(acr);
          lemma_InnerPCsDontYield(acr);
          lemma_InnerPCPrecededByInnerOrYieldingPC(acr);
          lemma_InnerPCSucceededByInnerOrYieldingPC(acr);
          lemma_NonInnerStepsLiftable(acr);
          lemma_CanCombineInnerSteps(acr);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str = @"
        lemma lemma_PerformArmadaSpecCombining()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var lspec := L.Armada_Spec();
          var hspec := H.Armada_Spec();
          var acr := GetArmadaCombiningRequest();
    
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);
            lemma_IsValidArmadaCombiningRequest(acr);
            var ahb := lemma_PerformArmadaCombining(acr, alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, acr.relation);
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
