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
  public class ReductionProofGenerator : AbstractProofGenerator
  {
    private ReductionStrategyDecl strategy;
    private HashSet<ArmadaPC> phase1PCs;
    private HashSet<ArmadaPC> phase2PCs;
    private Dictionary<ArmadaPC, NextRoutine> phase2PCToNextRoutine;

    public ReductionProofGenerator(ProofGenerationParams i_pgp, ReductionStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;

      phase1PCs = GetPCsForLabelRanges(strategy.Phase1LabelRanges);
      phase2PCs = GetPCsForLabelRanges(strategy.Phase2LabelRanges);

      phase2PCToNextRoutine = new Dictionary<ArmadaPC, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (phase2PCs.Contains(nextRoutine.pc)) {
          var pc = nextRoutine.pc;
          if (phase2PCToNextRoutine.ContainsKey(pc)) {
            AH.PrintError(pgp.prog, $"Multiple instructions occur at phase-2 PC {pc}.  I can't tell which of them to use for the proof that left movers are always enabled.");
          }
          else {
            phase2PCToNextRoutine[pc] = nextRoutine;
          }
        }
      }
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, $"Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the reduction strategy");
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofGivenMap();
    }

    private ArmadaPC GetPCForLabel(string labelName)
    {
      var pc = pgp.symbolsLow.GetPCForMethodAndLabel(labelName);
      if (pc == null) {
        AH.PrintError(pgp.prog, $"Specified non-existent label {labelName} in reduction description.  Remember to prefix label names with the method name and an underscore, e.g., use main_lb1 if you have label lb1: in method main.");
      }
      return pc;
    }

    private HashSet<ArmadaPC> GetPCsForLabelRanges(List<Tuple<string, string>> labelRanges)
    {
      HashSet<ArmadaPC> pcs = new HashSet<ArmadaPC>();

      foreach (var labelRange in labelRanges)
      {
        var label1Name = labelRange.Item1;
        var label2Name = labelRange.Item2;

        var pc1 = GetPCForLabel(label1Name);
        var pc2 = GetPCForLabel(label2Name);
        if (pc1 == null || pc2 == null) {
          continue;
        }

        if (pc1.methodName != pc2.methodName) {
          AH.PrintError(pgp.prog, $"You can't specify a range of labels where the start label is in a different method from the end label.  Label {label1Name} is in method {pc1.methodName} but label {label2Name} is in method {pc2.methodName}.");
          continue;
        }

        for (var i = pc1.instructionCount; i <= pc2.instructionCount; ++i) {
          var pc = new ArmadaPC(pgp.symbolsLow, pc1.methodName, i);
          pcs.Add(pc);
        }
      }

      return pcs;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/reduction/ArmadaReduction.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("GenericArmadaSpecModule");
      pgp.MainProof.AddImport("ArmadaReductionSpecModule");
      pgp.MainProof.AddImport("ArmadaReductionModule");
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

    private void InitializeAuxiliaryProofFiles()
    {
      var defsFile = pgp.proofFiles.CreateAuxiliaryProofFile("defs");
      defsFile.IncludeAndImportGeneratedFile("specs");
      defsFile.IncludeAndImportGeneratedFile("convert");
      defsFile.IncludeAndImportGeneratedFile("invariants");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/reduction/ArmadaReductionSpec.i.dfy",
                                "ArmadaReductionSpecModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("defs");

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var nextFileName = "next_" + nextRoutine.NameSuffix;
        var nextFile = pgp.proofFiles.CreateAuxiliaryProofFile(nextFileName);
        nextFile.IncludeAndImportGeneratedFile("specs");
        nextFile.IncludeAndImportGeneratedFile("invariants");
        nextFile.IncludeAndImportGeneratedFile("defs");
        nextFile.IncludeAndImportGeneratedFile("utility");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
        nextFile.AddImport("util_collections_seqs_s");
        pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile(nextFileName);
      }
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      InitializeAuxiliaryProofFiles();
      GeneratePhasePredicates();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateNextState_H();
      GenerateLocalViewCommutativityLemmas();

      GeneratePCFunctions_L();
      AddStackMatchesMethodInvariant();
      GenerateInvariantProof(pgp);

      GenerateReductionRequestComponents();
      GenerateReductionRequest();
      GenerateLInitImpliesHInitLemma();
      GenerateLeftMoverCommutativityLemmas();
      GenerateRightMoverCommutativityLemmas();
      GenerateLiftStepLemmas();
      GenerateLemmasSupportingValidRequest();
      GenerateIsValidRequest();
      GenerateFinalProof();
    }

    private void GeneratePhasePredicates()
    {
      string str;

      str = @"
        predicate IsPhase1PC(pc:L.Armada_PC)
        {
      ";
      if (phase1PCs.Any())
      {
        foreach (var pc in phase1PCs)
        {
          str += $"  || pc.{pc}?\n";
        }
      }
      else
      {
        str += "false\n";
      }
      str += "}";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate IsPhase2PC(pc:L.Armada_PC)
        {
      ";
      if (phase2PCs.Any())
      {
        foreach (var pc in phase2PCs)
        {
          str += $"  || pc.{pc}?\n";
        }
      }
      else
      {
        str += "false\n";
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateReductionRequestComponents()
    {
      string str;

      CreateGenericArmadaSpec_L();
      CreateGenericArmadaSpec_H();

      str = $@"
        predicate LLStateRefinement(ls:LState, hs:LState)
        {{
          {pgp.symbolsLow.RefinementConstraint}
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate LLPlusStateRefinement(ls:LPlusState, hs:LPlusState)
        {
          LLStateRefinement(ls.s, hs.s)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        function GetLLRefinementRelation() : RefinementRelation<LPlusState, LPlusState>
        {
          iset p:RefinementPair<LPlusState, LPlusState> | LLPlusStateRefinement(p.low, p.high)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function GenerateLeftMover(s:LPlusState, tid:Armada_ThreadHandle) : L.Armada_TraceEntry
        {
           if tid in s.s.threads then
             var pc := s.s.threads[tid].pc;
      ";
      foreach (KeyValuePair<ArmadaPC, NextRoutine> entry in phase2PCToNextRoutine) {
        str += $"    if pc.{entry.Key}? then L.Armada_TraceEntry_{entry.Value.NameSuffix}(tid) else\n";
      }
      str += @"
             L.Armada_TraceEntry_Tau(tid)
           else
             L.Armada_TraceEntry_Tau(tid)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function LeftMoverGenerationProgress(s:LPlusState, tid:Armada_ThreadHandle) : (progress:int)
          ensures progress >= 0
        {
          if tid in s.s.threads then
            var pc := s.s.threads[tid].pc;
            lemma_PCInstructionCountLessThanMethodInstructionCount_L(pc);
            MethodToInstructionCount_L(PCToMethod_L(pc)) - PCToInstructionCount_L(pc)
          else
            0
        }
      ";
      pgp.AddFunction(str, "defs");
    }

    private void GenerateReductionRequest()
    {
      var arrequest = AH.MakeGenericTypeSpecific("ArmadaReductionRequest",
                                                 new List<Type> {
                                                   AH.ReferToType("LPlusState"),
                                                   AH.ReferToType("L.Armada_TraceEntry"),
                                                   AH.ReferToType("L.Armada_PC"),
                                                   AH.ReferToType("HState"),
                                                   AH.ReferToType("H.Armada_TraceEntry"),
                                                   AH.ReferToType("H.Armada_PC")
                                                 });
      pgp.AddTypeSynonymDecl("ARRequest", arrequest, "defs");

      string str = @"
        function GetArmadaReductionRequest() : ARRequest
        {
          ArmadaReductionRequest(LPlus_GetSpecFunctions(), H.Armada_GetSpecFunctions(),
                                 GetLPlusHRefinementRelation(), InductiveInv, GetLLRefinementRelation(),
                                 ConvertTotalState_LPlusH, ConvertTraceEntry_LH, ConvertPC_LH, 
                                 IsPhase1PC, IsPhase2PC, GenerateLeftMover, LeftMoverGenerationProgress)
        }
      ";
      pgp.AddFunction(str, "defs");
    }

    private void GenerateLInitImpliesHInitLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      string str;

      str = @"
        lemma lemma_LInitImpliesHInit(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures  LInitImpliesHInit(arr)
        {
          forall ls | arr.l.init(ls)
            ensures arr.h.init(arr.lstate_to_hstate(ls))
          {
            var hs := arr.lstate_to_hstate(ls);
            var hconfig := ConvertConfig_LH(ls.config);

            lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
            assert H.Armada_InitConfig(hs, hconfig);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRightMoverCommutativityLemmaWithSpecificOther(NextRoutine nextRoutine1, NextRoutine nextRoutine2)
    {
      string str;

      string nameSuffix1 = nextRoutine1.NameSuffix;
      string nameSuffix2 = nextRoutine2.NameSuffix;
      str = $@"
        lemma lemma_RightMoverCommutativityWithSpecificOther_{nameSuffix1}_{nameSuffix2}(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          s2':LPlusState
          )
          requires InductiveInv(s1)
          requires step1.Armada_TraceEntry_{nameSuffix1}?
          requires step2.Armada_TraceEntry_{nameSuffix2}?
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step1.tid
          requires tid in s2.s.threads
          requires IsPhase1PC(s2.s.threads[tid].pc)
          requires step2.Armada_TraceEntry_Tau? || step2.tid != tid
          requires s2' == LPlus_GetNextStateAlways(s1, step2)
          requires s3.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(s2', step1)
          ensures  s3 == LPlus_GetNextStateAlways(s2', step1)
        {{
        }}
      ";
      pgp.AddLemma(str, "next_" + nameSuffix2);

      str = $@"
        lemma lemma_RightMoverPreservesCrashWithSpecificOther_{nameSuffix1}_{nameSuffix2}(
          initial_state:LPlusState,
          state_after_right_mover:LPlusState,
          state_after_both_steps:LPlusState,
          right_mover:L.Armada_TraceEntry,
          other_step:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_other_step':LPlusState
          )
          requires InductiveInv(initial_state)
          requires right_mover.Armada_TraceEntry_{nameSuffix1}?
          requires other_step.Armada_TraceEntry_{nameSuffix2}?
          requires !right_mover.Armada_TraceEntry_Tau?
          requires LPlus_ValidStep(initial_state, right_mover)
          requires state_after_right_mover == LPlus_GetNextStateAlways(initial_state, right_mover)
          requires LPlus_ValidStep(state_after_right_mover, other_step)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_right_mover, other_step)
          requires tid == right_mover.tid
          requires tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires state_after_other_step' == LPlus_GetNextStateAlways(initial_state, other_step)
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(initial_state, other_step)
          ensures  !state_after_other_step'.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_other_step')
        {{
        }}
      ";
      pgp.AddLemma(str, "next_" + nameSuffix2);
    }

    private void GenerateSpecificRightMoverCommutativityLemmaCasePhase1(NextRoutine nextRoutine1)
    {
      var nextRoutine1Name = nextRoutine1.NameSuffix;

      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";

      foreach (var nextRoutine2 in pgp.symbolsLow.NextRoutines) {
        GenerateRightMoverCommutativityLemmaWithSpecificOther(nextRoutine1, nextRoutine2);
        var nextRoutine2Name = nextRoutine2.NameSuffix;
        var step_params = String.Join("", nextRoutine2.Formals.Select(f => $", _"));
        finalCasesCommutativity += $"case Armada_TraceEntry_{nextRoutine2Name}(_{step_params}) => lemma_RightMoverCommutativityWithSpecificOther_{nextRoutine1Name}_{nextRoutine2Name}(s1, s2, s3, step1, step2, tid, s2');";
        finalCasesCrashPreservation += $"case Armada_TraceEntry_{nextRoutine2Name}(_{step_params}) => lemma_RightMoverPreservesCrashWithSpecificOther_{nextRoutine1Name}_{nextRoutine2Name}(initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step, tid, state_after_other_step');";
      }

      string str;

      str = $@"
        lemma lemma_RightMoverCommutativity_{nextRoutine1Name}(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          s2':LPlusState
          )
          requires InductiveInv(s1)
          requires step1.Armada_TraceEntry_{nextRoutine1Name}?
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step1.tid
          requires tid in s2.s.threads
          requires IsPhase1PC(s2.s.threads[tid].pc)
          requires step2.Armada_TraceEntry_Tau? || step2.tid != tid
          requires s2' == LPlus_GetNextStateAlways(s1, step2)
          requires s3.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(s2', step1)
          ensures  s3 == LPlus_GetNextStateAlways(s2', step1)
        {{
          match step2 {{
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_RightMoverPreservesCrash_{nextRoutine1Name}(
          initial_state:LPlusState,
          state_after_right_mover:LPlusState,
          state_after_both_steps:LPlusState,
          right_mover:L.Armada_TraceEntry,
          other_step:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_other_step':LPlusState
          )
          requires InductiveInv(initial_state)
          requires right_mover.Armada_TraceEntry_{nextRoutine1Name}?
          requires LPlus_ValidStep(initial_state, right_mover)
          requires state_after_right_mover == LPlus_GetNextStateAlways(initial_state, right_mover)
          requires LPlus_ValidStep(state_after_right_mover, other_step)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_right_mover, other_step)
          requires tid == right_mover.tid
          requires tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires state_after_other_step' == LPlus_GetNextStateAlways(initial_state, other_step)
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(initial_state, other_step)
          ensures  !state_after_other_step'.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_other_step')
        {{
          match other_step {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateSpecificRightMoverCommutativityLemmaCaseNotPhase1(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      string str;

      str = $@"
        lemma lemma_RightMoverCommutativity_{nextRoutineName}(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          s2':LPlusState
          )
          requires InductiveInv(s1)
          requires step1.Armada_TraceEntry_{nextRoutineName}?
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step1.tid
          requires tid in s2.s.threads
          requires IsPhase1PC(s2.s.threads[tid].pc)
          requires step2.Armada_TraceEntry_Tau? || step2.tid != tid
          requires s2' == LPlus_GetNextStateAlways(s1, step2)
          requires s3.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(s2', step1)
          ensures  s3 == LPlus_GetNextStateAlways(s2', step1)
        {{
          assert !IsPhase1PC(s2.s.threads[tid].pc);
          assert false;
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_RightMoverPreservesCrash_{nextRoutineName}(
          initial_state:LPlusState,
          state_after_right_mover:LPlusState,
          state_after_both_steps:LPlusState,
          right_mover:L.Armada_TraceEntry,
          other_step:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_other_step':LPlusState
          )
          requires InductiveInv(initial_state)
          requires right_mover.Armada_TraceEntry_{nextRoutineName}?
          requires LPlus_ValidStep(initial_state, right_mover)
          requires state_after_right_mover == LPlus_GetNextStateAlways(initial_state, right_mover)
          requires LPlus_ValidStep(state_after_right_mover, other_step)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_right_mover, other_step)
          requires tid == right_mover.tid
          requires tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires state_after_other_step' == LPlus_GetNextStateAlways(initial_state, other_step)
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(initial_state, other_step)
          ensures  !state_after_other_step'.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_other_step')
        {{
          assert !IsPhase1PC(state_after_right_mover.s.threads[tid].pc);
          assert false;
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateSpecificRightMoverCommutativityLemma(NextRoutine nextRoutine)
    {
      var pc = nextRoutine.endPC;
      if (pc != null && phase1PCs.Contains(pc)) {
        GenerateSpecificRightMoverCommutativityLemmaCasePhase1(nextRoutine);
        return;
      }

      GenerateSpecificRightMoverCommutativityLemmaCaseNotPhase1(nextRoutine);
    }

    private void GenerateRightMoverCommutativityLemmas()
    {
      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType != NextType.Tau) {
          GenerateSpecificRightMoverCommutativityLemma(nextRoutine);
          var nextRoutineName = nextRoutine.NameSuffix;
          var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
          finalCasesCommutativity += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RightMoverCommutativity_{nextRoutineName}(s1, s2, s3, step1, step2, tid, s2');";
          finalCasesCrashPreservation += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RightMoverPreservesCrash_{nextRoutineName}(initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step, tid, state_after_other_step');";
        }
      }

      string str;

      str = $@"
        lemma lemma_RightMoverCommutativity(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          s2':LPlusState
          )
          requires InductiveInv(s1)
          requires !step1.Armada_TraceEntry_Tau?
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step1.tid
          requires tid in s2.s.threads
          requires IsPhase1PC(s2.s.threads[tid].pc)
          requires step2.Armada_TraceEntry_Tau? || step2.tid != tid
          requires s2' == LPlus_GetNextStateAlways(s1, step2)
          requires s3.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(s2', step1)
          ensures  s3 == LPlus_GetNextStateAlways(s2', step1)
        {{
          match step1 {{
            case Armada_TraceEntry_Tau(_) => assert false;
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_RightMoverPreservesCrash(
          initial_state:LPlusState,
          state_after_right_mover:LPlusState,
          state_after_both_steps:LPlusState,
          right_mover:L.Armada_TraceEntry,
          other_step:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_other_step':LPlusState
          )
          requires InductiveInv(initial_state)
          requires !right_mover.Armada_TraceEntry_Tau?
          requires LPlus_ValidStep(initial_state, right_mover)
          requires state_after_right_mover == LPlus_GetNextStateAlways(initial_state, right_mover)
          requires LPlus_ValidStep(state_after_right_mover, other_step)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_right_mover, other_step)
          requires tid == right_mover.tid
          requires tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires state_after_other_step' == LPlus_GetNextStateAlways(initial_state, other_step)
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LPlus_ValidStep(initial_state, other_step)
          ensures  !state_after_other_step'.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_other_step')
        {{
          match right_mover {{
            case Armada_TraceEntry_Tau(_) => assert false;
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLeftMoverCommutativityLemmaWithSpecificOther(NextRoutine nextRoutine1, NextRoutine nextRoutine2)
    {
      string str;

      string nameSuffix1 = nextRoutine1.NameSuffix;
      string nameSuffix2 = nextRoutine2.NameSuffix;
      str = $@"
        lemma lemma_LeftMoverCommutativityWithSpecificOther_{nameSuffix1}_{nameSuffix2}(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle
          )
          requires InductiveInv(s1)
          requires step1.Armada_TraceEntry_{nameSuffix1}?
          requires step2.Armada_TraceEntry_{nameSuffix2}?
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step2.tid
          requires tid in s2.s.threads
          requires IsPhase2PC(s2.s.threads[tid].pc)
          requires step1.Armada_TraceEntry_Tau? || step1.tid != tid
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(LPlus_GetNextStateAlways(s1, step2), step1)
          ensures  s3 == LPlus_GetNextStateAlways(LPlus_GetNextStateAlways(s1, step2), step1)
        {{
        }}
      ";
      pgp.AddLemma(str, "next_" + nameSuffix1);

      str = $@"
        lemma lemma_LeftMoverPreservesCrashWithSpecificOther_{nameSuffix1}_{nameSuffix2}(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_left_mover:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_both_steps:LPlusState
          )
          requires InductiveInv(initial_state)
          requires other_step.Armada_TraceEntry_{nameSuffix1}?
          requires left_mover.Armada_TraceEntry_{nameSuffix2}?
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(initial_state, left_mover)
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          requires tid == left_mover.tid
          requires tid in initial_state.s.threads
          requires IsPhase2PC(initial_state.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires !state_after_other_step.s.stop_reason.Armada_NotStopped?
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_left_mover, other_step)
          ensures  LPlus_ValidStep(state_after_left_mover, other_step)
          ensures  !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_other_step, state_after_both_steps)
        {{
        }}
      ";
      pgp.AddLemma(str, "next_" + nameSuffix1);

      str = $@"
        lemma lemma_LeftMoverPreservesSelfCrashWithSpecificOther_{nameSuffix1}_{nameSuffix2}(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_both_steps:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_left_mover:LPlusState
          )
          requires InductiveInv(initial_state)
          requires other_step.Armada_TraceEntry_{nameSuffix1}?
          requires left_mover.Armada_TraceEntry_{nameSuffix2}?
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(state_after_other_step, left_mover)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_other_step, left_mover)
          requires tid == left_mover.tid
          requires tid in state_after_other_step.s.threads
          requires IsPhase2PC(state_after_other_step.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires initial_state.s.stop_reason.Armada_NotStopped?
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          ensures  LPlus_ValidStep(initial_state, left_mover)
          ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_left_mover)
        {{
        }}
      ";
      pgp.AddLemma(str, "next_" + nameSuffix1);
    }

    private void GenerateSpecificLeftMoverCommutativityLemma(NextRoutine nextRoutine2)
    {
      var nextRoutine2Name = nextRoutine2.NameSuffix;

      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";
      var finalCasesSelfCrashPreservation = "";

      foreach (var nextRoutine1 in pgp.symbolsLow.NextRoutines) {
        GenerateLeftMoverCommutativityLemmaWithSpecificOther(nextRoutine1, nextRoutine2);
        var nextRoutine1Name = nextRoutine1.NameSuffix;
        var step_params = String.Join("", nextRoutine1.Formals.Select(f => $", _"));
        finalCasesCommutativity += $"case Armada_TraceEntry_{nextRoutine1Name}(_{step_params}) => lemma_LeftMoverCommutativityWithSpecificOther_{nextRoutine1Name}_{nextRoutine2Name}(s1, s2, s3, step1, step2, tid);";
        finalCasesCrashPreservation += $"case Armada_TraceEntry_{nextRoutine1Name}(_{step_params}) => lemma_LeftMoverPreservesCrashWithSpecificOther_{nextRoutine1Name}_{nextRoutine2Name}(initial_state, state_after_other_step, state_after_left_mover, other_step, left_mover, tid, state_after_both_steps);";
        finalCasesSelfCrashPreservation += $"case Armada_TraceEntry_{nextRoutine1Name}(_{step_params}) => lemma_LeftMoverPreservesSelfCrashWithSpecificOther_{nextRoutine1Name}_{nextRoutine2Name}(initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover, tid, state_after_left_mover);";
      }

      string str;

      str = $@"
        lemma lemma_LeftMoverCommutativity_{nextRoutine2Name}(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle
          )
          requires InductiveInv(s1)
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires step2.Armada_TraceEntry_{nextRoutine2Name}?
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step2.tid
          requires tid in s2.s.threads
          requires IsPhase2PC(s2.s.threads[tid].pc)
          requires step1.Armada_TraceEntry_Tau? || step1.tid != tid
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(LPlus_GetNextStateAlways(s1, step2), step1)
          ensures  s3 == LPlus_GetNextStateAlways(LPlus_GetNextStateAlways(s1, step2), step1)
        {{
          match step1 {{
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesCrash_{nextRoutine2Name}(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_left_mover:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_both_steps:LPlusState
          )
          requires InductiveInv(initial_state)
          requires left_mover.Armada_TraceEntry_{nextRoutine2Name}?
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(initial_state, left_mover)
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          requires tid == left_mover.tid
          requires tid in initial_state.s.threads
          requires IsPhase2PC(initial_state.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires !state_after_other_step.s.stop_reason.Armada_NotStopped?
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_left_mover, other_step)
          ensures  LPlus_ValidStep(state_after_left_mover, other_step)
          ensures  !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_other_step, state_after_both_steps)
        {{
          match other_step {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesSelfCrash_{nextRoutine2Name}(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_both_steps:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_left_mover:LPlusState
          )
          requires InductiveInv(initial_state)
          requires left_mover.Armada_TraceEntry_{nextRoutine2Name}?
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(state_after_other_step, left_mover)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_other_step, left_mover)
          requires tid == left_mover.tid
          requires tid in state_after_other_step.s.threads
          requires IsPhase2PC(state_after_other_step.s.threads[tid].pc)
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires initial_state.s.stop_reason.Armada_NotStopped?
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          ensures  LPlus_ValidStep(initial_state, left_mover)
          ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_left_mover)
        {{
          match other_step {{
            {finalCasesSelfCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLeftMoverCommutativityLemmas()
    {
      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";
      var finalCasesSelfCrashPreservation = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType != NextType.Tau) {
          var nextRoutineName = nextRoutine.NameSuffix;
          var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
          if (phase2PCs.Contains(nextRoutine.pc)) {
            GenerateSpecificLeftMoverCommutativityLemma(nextRoutine);
            finalCasesCommutativity += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_LeftMoverCommutativity_{nextRoutineName}(s1, s2, s3, step1, step2, tid);";
            finalCasesCrashPreservation += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_LeftMoverPreservesCrash_{nextRoutineName}(initial_state, state_after_other_step, state_after_left_mover, other_step, left_mover, tid, state_after_both_steps);";
            finalCasesSelfCrashPreservation += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_LeftMoverPreservesSelfCrash_{nextRoutineName}(initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover, tid, state_after_left_mover);";
          }
          else {
            finalCasesCommutativity += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => assert false;";
            finalCasesCrashPreservation += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => assert false;";
            finalCasesSelfCrashPreservation += $"case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => assert false;";
          }
        }
      }

      string str;

      str = $@"
        lemma lemma_LeftMoverCommutativity(
          s1:LPlusState,
          s2:LPlusState,
          s3:LPlusState,
          step1:L.Armada_TraceEntry,
          step2:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle
          )
          requires InductiveInv(s1)
          requires LPlus_ValidStep(s1, step1)
          requires s2 == LPlus_GetNextStateAlways(s1, step1)
          requires !step2.Armada_TraceEntry_Tau?
          requires LPlus_ValidStep(s2, step2)
          requires s3 == LPlus_GetNextStateAlways(s2, step2)
          requires tid == step2.tid
          requires tid in s2.s.threads
          requires IsPhase2PC(s2.s.threads[tid].pc)
          requires step1.Armada_TraceEntry_Tau? || step1.tid != tid
          ensures  LPlus_ValidStep(s1, step2)
          ensures  LPlus_ValidStep(LPlus_GetNextStateAlways(s1, step2), step1)
          ensures  s3 == LPlus_GetNextStateAlways(LPlus_GetNextStateAlways(s1, step2), step1)
        {{
          match step2 {{
            case Armada_TraceEntry_Tau(_) => assert false;
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesCrash(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_left_mover:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_both_steps:LPlusState
          )
          requires InductiveInv(initial_state)
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(initial_state, left_mover)
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          requires tid == left_mover.tid
          requires tid in initial_state.s.threads
          requires IsPhase2PC(initial_state.s.threads[tid].pc)
          requires !left_mover.Armada_TraceEntry_Tau?
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires !state_after_other_step.s.stop_reason.Armada_NotStopped?
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_left_mover, other_step)
          ensures  LPlus_ValidStep(state_after_left_mover, other_step)
          ensures  !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_other_step, state_after_both_steps)
        {{
          match left_mover {{
            case Armada_TraceEntry_Tau(_) => assert false;
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesSelfCrash(
          initial_state:LPlusState,
          state_after_other_step:LPlusState,
          state_after_both_steps:LPlusState,
          other_step:L.Armada_TraceEntry,
          left_mover:L.Armada_TraceEntry,
          tid:Armada_ThreadHandle,
          state_after_left_mover:LPlusState
          )
          requires InductiveInv(initial_state)
          requires LPlus_ValidStep(initial_state, other_step)
          requires state_after_other_step == LPlus_GetNextStateAlways(initial_state, other_step)
          requires LPlus_ValidStep(state_after_other_step, left_mover)
          requires state_after_both_steps == LPlus_GetNextStateAlways(state_after_other_step, left_mover)
          requires tid == left_mover.tid
          requires tid in state_after_other_step.s.threads
          requires IsPhase2PC(state_after_other_step.s.threads[tid].pc)
          requires !left_mover.Armada_TraceEntry_Tau?
          requires other_step.Armada_TraceEntry_Tau? || other_step.tid != tid
          requires initial_state.s.stop_reason.Armada_NotStopped?
          requires !state_after_both_steps.s.stop_reason.Armada_NotStopped?
          requires state_after_left_mover == LPlus_GetNextStateAlways(initial_state, left_mover)
          ensures  LPlus_ValidStep(initial_state, left_mover)
          ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_steps, state_after_left_mover)
        {{
          match left_mover {{
            case Armada_TraceEntry_Tau(_) => assert false;
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLHYieldingCorrespondenceLemma()
    {
      string str;

      str = @"
        lemma lemma_LHYieldingCorrespondence(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LHYieldingCorrespondence(arr)
        {
          forall lpc:L.Armada_PC
            ensures var hpc := arr.lpc_to_hpc(lpc);
                    arr.h.is_pc_nonyielding(hpc) <==> (arr.l.is_pc_nonyielding(lpc) || arr.is_phase1(lpc) || arr.is_phase2(lpc))
          {
            var hpc := arr.lpc_to_hpc(lpc);
            match lpc {
      ";

      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $@"        case {pc} => assert arr.h.is_pc_nonyielding(hpc) <==> (arr.l.is_pc_nonyielding(lpc) || arr.is_phase1(lpc) || arr.is_phase2(lpc));
";
      }

      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRightMoversPreserveStateRefinementLemma()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var nameSuffix = nextRoutine.NameSuffix;
        str = $@"
          lemma lemma_RightMoversPreserveStateRefinement_{nameSuffix}(arr:ARRequest, s:LPlusState, step:L.Armada_TraceEntry)
            requires arr == GetArmadaReductionRequest()
            requires LPlus_ValidStep(s, step)
            requires !step.Armada_TraceEntry_Tau?
            requires step.Armada_TraceEntry_{nameSuffix}?
            ensures  var tid := step.tid;
                     var s' := LPlus_GetNextStateAlways(s, step);
                     var pc' := arr.l.get_thread_pc(s', tid);
                     (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
          {{
          }}
        ";
        pgp.AddLemma(str);

        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"case Armada_TraceEntry_{nameSuffix}(_{step_params}) => lemma_RightMoversPreserveStateRefinement_{nameSuffix}(arr, s, step);\n";
      }

      str = $@"
        lemma lemma_RightMoversPreserveStateRefinement(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures RightMoversPreserveStateRefinement(arr)
        {{
           forall s, step | arr.l.step_valid(s, step) && !arr.l.is_step_tau(step)
             ensures var tid := arr.l.step_to_thread(step);
                     var s' := arr.l.step_next(s, step);
                     var pc' := arr.l.get_thread_pc(s', tid);
                     (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
           {{
             match step {{
               {finalCases}
             }}
           }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasSupportingValidRequest()
    {
      string str;

      str = @"
        lemma lemma_RefinementRelationsSatisfyRequirements(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures RefinementRelationReflexive(arr.self_relation)
          ensures RefinementRelationTransitive(arr.self_relation)
          ensures RefinementRelationsConvolve(arr.self_relation, arr.relation, arr.relation)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LStateToHStateMapsPCsCorrectly(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LStateToHStateMapsPCsCorrectly(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateLHYieldingCorrespondenceLemma();

      str = @"
        lemma lemma_LHOneStepPropertiesMatch(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LHOneStepPropertiesMatch(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LOneStepImpliesHOneStep(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LOneStepImpliesHOneStep(arr)
        {
          forall ls, lstep | arr.inv(ls) && arr.l.step_valid(ls, lstep)
            ensures var ls' := arr.l.step_next(ls, lstep);
                    var hs := arr.lstate_to_hstate(ls);
                    var hstep := arr.lonestep_to_honestep(lstep);
                    var hs' := arr.lstate_to_hstate(ls');
                    && arr.h.step_valid(hs, hstep)
                    && hs' == arr.h.step_next(hs, hstep)
          {
            lemma_LiftStep(ls, lstep);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionPreservesOK(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures StateConversionPreservesOK(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionSatisfiesRelation(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures StateConversionSatisfiesRelation(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ThreadsDontStartInAnyPhase(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures ThreadsDontStartInAnyPhase(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PhasesDontOverlap(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures PhasesDontOverlap(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ThreadCantAffectOtherThreadPhaseExceptViaFork(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures ThreadCantAffectOtherThreadPhaseExceptViaFork(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PhasesPrecededByYielding(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures PhasesPrecededByYielding(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PhasesSucceededByYielding(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures PhasesSucceededByYielding(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_Phase2NotFollowedByPhase1(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures Phase2NotFollowedByPhase1(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateRightMoversPreserveStateRefinementLemma();

      str = @"
        lemma lemma_LeftMoversPreserveStateRefinement(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LeftMoversPreserveStateRefinement(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RightMoversCommute(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures RightMoversCommute(arr)
        {
          forall s1, step1, step2 |
            var tid := arr.l.step_to_thread(step1);
            var other_tid := arr.l.step_to_thread(step2);
            var other_tau := arr.l.is_step_tau(step2);
            var s2 := LPlus_GetNextStateAlways(s1, step1);
            var s3 := LPlus_GetNextStateAlways(s2, step2);
            var pc := arr.l.get_thread_pc(s2, tid);
            var s2' := LPlus_GetNextStateAlways(s1, step2);
            && arr.inv(s1)
            && !arr.l.is_step_tau(step1)
            && LPlus_ValidStep(s1, step1)
            && pc.Some?
            && arr.is_phase1(pc.v)
            && LPlus_ValidStep(s2, step2)
            && s3.s.stop_reason.Armada_NotStopped?
            && (other_tau || other_tid != tid)
            ensures var s2 := LPlus_GetNextStateAlways(s1, step1);
                    var s3 := LPlus_GetNextStateAlways(s2, step2);
                    var s2' := LPlus_GetNextStateAlways(s1, step2);
                    && LPlus_ValidStep(s1, step2)
                    && LPlus_ValidStep(s2', step1)
                    && s3 == LPlus_GetNextStateAlways(s2', step1)
          {
            var tid := arr.l.step_to_thread(step1);
            var s2 := LPlus_GetNextStateAlways(s1, step1);
            var s3 := LPlus_GetNextStateAlways(s2, step2);
            var s2' := LPlus_GetNextStateAlways(s1, step2);
            lemma_RightMoverCommutativity(s1, s2, s3, step1, step2, tid, s2');
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RightMoverCrashPreservation(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures RightMoverCrashPreservation(arr)
        {
          forall initial_state, right_mover, other_step |
            var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
            var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
            var tid := arr.l.step_to_thread(right_mover);
            var pc := arr.l.get_thread_pc(state_after_right_mover, tid);
            var other_tau := arr.l.is_step_tau(other_step);
            var other_tid := arr.l.step_to_thread(other_step);
            && arr.inv(initial_state)
            && arr.l.step_valid(initial_state, right_mover)
            && arr.l.step_valid(state_after_right_mover, other_step)
            && !arr.l.state_ok(state_after_both_steps)
            && !arr.l.is_step_tau(right_mover)
            && pc.Some?
            && arr.is_phase1(pc.v)
            && (other_tau || other_tid != tid)
            ensures var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
                    var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
                    var state_after_other_step' := arr.l.step_next(initial_state, other_step);
                    && arr.l.step_valid(initial_state, other_step)
                    && !arr.l.state_ok(state_after_other_step')
                    && RefinementPair(state_after_both_steps, state_after_other_step') in arr.self_relation
          {
            var tid := arr.l.step_to_thread(right_mover);
            var state_after_right_mover := arr.l.step_next(initial_state, right_mover);
            var state_after_both_steps := arr.l.step_next(state_after_right_mover, other_step);
            var state_after_other_step' := arr.l.step_next(initial_state, other_step);
            lemma_RightMoverPreservesCrash(initial_state, state_after_right_mover, state_after_both_steps, right_mover, other_step,
                                           tid, state_after_other_step');
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoversCommute(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LeftMoversCommute(arr)
        {
          forall initial_state, other_step, left_mover | LeftMoversCommuteConditions(arr, initial_state, other_step, left_mover)
            ensures var state_after_other_step := arr.l.step_next(initial_state, other_step);
                    var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
                    var new_middle_state := arr.l.step_next(initial_state, left_mover);
                    && arr.l.step_valid(initial_state, left_mover)
                    && arr.l.step_valid(new_middle_state, other_step)
                    && state_after_both_steps == arr.l.step_next(new_middle_state, other_step)
          {
            var tid := arr.l.step_to_thread(left_mover);
            var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
            lemma_LeftMoverCommutativity(initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoverCrashPreservation(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LeftMoverCrashPreservation(arr)
        {
          forall initial_state, left_mover, other_step |
            var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
            var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var tid := arr.l.step_to_thread(left_mover);
            var pc := arr.l.get_thread_pc(initial_state, tid);
            var other_tau := arr.l.is_step_tau(other_step);
            var other_tid := arr.l.step_to_thread(other_step);
            && arr.inv(initial_state)
            && !arr.l.is_step_tau(left_mover)
            && arr.l.step_valid(initial_state, left_mover)
            && arr.l.step_valid(initial_state, other_step)
            && arr.l.state_ok(initial_state)
            && !arr.l.state_ok(state_after_other_step)
            && pc.Some?
            && arr.is_phase2(pc.v)
            && (other_tau || other_tid != tid)
            ensures var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
                    var state_after_other_step := arr.l.step_next(initial_state, other_step);
                    var state_after_both_steps := arr.l.step_next(state_after_left_mover, other_step);
                    && arr.l.step_valid(state_after_left_mover, other_step)
                    && !arr.l.state_ok(state_after_both_steps)
                    && RefinementPair(state_after_other_step, state_after_both_steps) in arr.self_relation
          {
            var tid := arr.l.step_to_thread(left_mover);
            var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
            var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var state_after_both_steps := arr.l.step_next(state_after_left_mover, other_step);
            lemma_LeftMoverPreservesCrash(initial_state, state_after_other_step, state_after_left_mover, other_step, left_mover,
                                          tid, state_after_both_steps);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoverSelfCrashPreservation(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures LeftMoverSelfCrashPreservation(arr)
        {
          forall initial_state, left_mover, other_step |
            var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
            var tid := arr.l.step_to_thread(left_mover);
            var pc := arr.l.get_thread_pc(state_after_other_step, tid);
            var other_tau := arr.l.is_step_tau(other_step);
            var other_tid := arr.l.step_to_thread(other_step);
            && arr.inv(initial_state)
            && !arr.l.is_step_tau(left_mover)
            && arr.l.step_valid(initial_state, left_mover)
            && arr.l.step_valid(state_after_other_step, other_step)
            && arr.l.state_ok(initial_state)
            && !arr.l.state_ok(state_after_both_steps)
            && pc.Some?
            && arr.is_phase2(pc.v)
            && (other_tau || other_tid != tid)
            ensures var state_after_other_step := arr.l.step_next(initial_state, other_step);
                    var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
                    var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
                    && arr.l.step_valid(initial_state, left_mover)
                    && !arr.l.state_ok(state_after_left_mover)
                    && RefinementPair(state_after_both_steps, state_after_left_mover) in arr.self_relation
          {
            var tid := arr.l.step_to_thread(left_mover);
            var state_after_other_step := arr.l.step_next(initial_state, other_step);
            var state_after_both_steps := arr.l.step_next(state_after_other_step, left_mover);
            var state_after_left_mover := arr.l.step_next(initial_state, left_mover);
            lemma_LeftMoverPreservesSelfCrash(initial_state, state_after_other_step, state_after_both_steps, other_step, left_mover,
                                              tid, state_after_left_mover);
          }
        }
      ";
      pgp.AddLemma(str);

      GenerateLeftMoverEnablementLemmas();
    }

    private void GenerateLeftMoverEnablementLemmas()
    {
      string str;
      string body = "";

      foreach (KeyValuePair<ArmadaPC, NextRoutine> entry in phase2PCToNextRoutine)
      {
        var pc = entry.Key;
        var nextRoutine = entry.Value;
        var nameSuffix = nextRoutine.NameSuffix;
        str = $@"
          lemma lemma_LeftMoverEnabled_{nameSuffix}(s:LPlusState, tid:Armada_ThreadHandle, step:L.Armada_TraceEntry)
            requires InductiveInv(s)
            requires s.s.stop_reason.Armada_NotStopped?
            requires tid in s.s.threads
            requires s.s.threads[tid].pc.{pc}?
            requires step == GenerateLeftMover(s, tid)
            ensures  LPlus_ValidStep(s, step)
            ensures  step.tid == tid
            ensures  !step.Armada_TraceEntry_Tau?
            ensures  0 <= LeftMoverGenerationProgress(LPlus_GetNextStateAlways(s, step), tid) < LeftMoverGenerationProgress(s, tid)
          {{
            assert s.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?;
          }}
        ";
        pgp.AddLemma(str);
        body += $@"
          if pc.{pc}? {{
            lemma_LeftMoverEnabled_{nameSuffix}(s, tid, step);
          }}
        ";
      }

      str = $@"
        lemma lemma_LeftMoverEnabled(s:LPlusState, tid:Armada_ThreadHandle, step:L.Armada_TraceEntry)
          requires InductiveInv(s)
          requires s.s.stop_reason.Armada_NotStopped?
          requires tid in s.s.threads
          requires IsPhase2PC(s.s.threads[tid].pc)
          requires step == GenerateLeftMover(s, tid)
          ensures  LPlus_ValidStep(s, step)
          ensures  step.tid == tid
          ensures  !step.Armada_TraceEntry_Tau?
          ensures  0 <= LeftMoverGenerationProgress(LPlus_GetNextStateAlways(s, step), tid) < LeftMoverGenerationProgress(s, tid)
        {{
          var pc := s.s.threads[tid].pc;
          { body }
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoversAlwaysEnabled(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures  LeftMoversAlwaysEnabled(arr)
        {
          forall s, tid |
            && arr.inv(s)
            && s.s.stop_reason.Armada_NotStopped?
            && arr.l.get_thread_pc(s, tid).Some?
            && arr.is_phase2(arr.l.get_thread_pc(s, tid).v)
            ensures var step := arr.generate_left_mover(s, tid);
                    && LPlus_ValidStep(s, step)
                    && arr.l.step_to_thread(step) == tid
                    && !arr.l.is_step_tau(step)
                    && var s' := LPlus_GetNextStateAlways(s, step);
                      0 <= arr.left_mover_generation_progress(s', tid) < arr.left_mover_generation_progress(s, tid)
          {
            var step := arr.generate_left_mover(s, tid);
            lemma_LeftMoverEnabled(s, tid, step);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateIsValidRequest()
    {
      string str = @"
        lemma lemma_IsValidArmadaReductionRequest(arr:ARRequest)
          requires arr == GetArmadaReductionRequest()
          ensures  ValidArmadaReductionRequest(arr)
        {
          lemma_RefinementRelationsSatisfyRequirements(arr);
          lemma_LInitImpliesHInit(arr);
          lemma_InductiveInvInvariantInLPlusSpec(arr.l);
          lemma_InitImpliesYielding_L(arr.l);
          lemma_InitImpliesOK_L(arr.l);
          lemma_OneStepRequiresOK_L(arr.l);
          lemma_LStateToHStateMapsPCsCorrectly(arr);
          lemma_LHYieldingCorrespondence(arr);
          lemma_LHOneStepPropertiesMatch(arr);
          lemma_LOneStepImpliesHOneStep(arr);
          lemma_StateConversionPreservesOK(arr);
          lemma_StateConversionSatisfiesRelation(arr);
          lemma_ThreadsDontStartInAnyPhase(arr);
          lemma_PhasesDontOverlap(arr);
          lemma_ThreadCantAffectOtherThreadPhaseExceptViaFork(arr);
          lemma_PhasesPrecededByYielding(arr);
          lemma_PhasesSucceededByYielding(arr);
          lemma_Phase2NotFollowedByPhase1(arr);
          lemma_SteppingThreadHasPC_L(arr.l);
          lemma_TauLeavesPCUnchanged_L(arr.l);
          lemma_RightMoversPreserveStateRefinement(arr);
          lemma_LeftMoversPreserveStateRefinement(arr);
          lemma_RightMoversCommute(arr);
          lemma_LeftMoversCommute(arr);
          lemma_RightMoverCrashPreservation(arr);
          lemma_LeftMoverCrashPreservation(arr);
          lemma_LeftMoverSelfCrashPreservation(arr);
          lemma_LeftMoversAlwaysEnabled(arr);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str = @"
        lemma lemma_ProveRefinementViaReduction()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var lspec := L.Armada_Spec();
          var hspec := H.Armada_Spec();
          var arr := GetArmadaReductionRequest();
    
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);
            lemma_IsValidArmadaReductionRequest(arr);
            var ahb := lemma_PerformArmadaReduction(arr, alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, arr.relation);
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
