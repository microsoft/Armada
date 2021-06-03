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
    private HashSet<ArmadaPC> extraRecurrentPCs;
    private Dictionary<ArmadaPC, AtomicPath> phase2PCToPath;

    public ReductionProofGenerator(ProofGenerationParams i_pgp, ReductionStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;

      phase1PCs = GetYieldingPCsForLabelRanges(strategy.Phase1LabelRanges);
      phase2PCs = GetYieldingPCsForLabelRanges(strategy.Phase2LabelRanges);
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, $"Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the reduction strategy");
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateExtraRecurrentPCs();
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

    private HashSet<ArmadaPC> GetYieldingPCsForLabelRanges(List<Tuple<string, string>> labelRanges)
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
          if (!pgp.symbolsLow.IsNonyieldingPC(pc)) {
            pcs.Add(pc);
          }
        }
      }

      return pcs;
    }

    private void GenerateExtraRecurrentPCs()
    {
      extraRecurrentPCs = new HashSet<ArmadaPC>(phase1PCs.Concat(phase2PCs).Select(pc => pcMap[pc]));
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/reduction/AtomicReduction.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("GenericArmadaSpecModule");
      pgp.MainProof.AddImport("AtomicReductionSpecModule");
      pgp.MainProof.AddImport("AtomicReductionModule");
      pgp.MainProof.AddImport("GeneralRefinementLemmasModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy", "invariants");
      pgp.AddImport("GenericArmadaLemmasModule", null, "invariants");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/reduction/AtomicReductionSpec.i.dfy", "defs");
      pgp.AddImport("AtomicReductionSpecModule", null, "defs");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/reduction/AtomicReductionSpec.i.dfy", "lift");
      pgp.AddImport("AtomicReductionSpecModule", null, "lift");
    }

    private void InitializeAuxiliaryProofFiles()
    {
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var pathFileName = "path_" + atomicPath.Name;
        var pathFile = pgp.proofFiles.CreateAuxiliaryProofFile(pathFileName);
        pathFile.IncludeAndImportGeneratedFile("specs");
        pathFile.IncludeAndImportGeneratedFile("revelations");
        pathFile.IncludeAndImportGeneratedFile("invariants");
        pathFile.IncludeAndImportGeneratedFile("defs");
        pathFile.IncludeAndImportGeneratedFile("utility");
        pathFile.IncludeAndImportGeneratedFile("latomic");
        pathFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
        pathFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
        pathFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
        pathFile.AddImport("util_collections_seqs_s");
        pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile(pathFileName);
      }
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateAtomicSpecs(true, null, extraRecurrentPCs);
      InitializeAuxiliaryProofFiles();
      GeneratePhasePredicates();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
      GenerateLocalViewCommutativityLemmas();

      GeneratePCFunctions_L();
      AddStackMatchesMethodInvariant();
      GenerateInvariantProof(pgp);

      GenerateReductionRequestComponents();
      GenerateReductionRequest();
      GenerateLInitImpliesHInitLemma();
      GenerateLeftMoverCommutativityLemmas();
      GenerateRightMoverCommutativityLemmas();
      GenerateLiftAtomicPathLemmas("LHPathTypesMatchYR(ty, HAtomic_GetPathType(hpath))");
      GenerateLemmasSupportingValidRequest();
      GenerateIsValidRequest();
      GenerateLiftLAtomicToHAtomicLemma();
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

      phase2PCToPath = new Dictionary<ArmadaPC, AtomicPath>();
      foreach (var atomicPath in lAtomic.AtomicPaths.Where(ap => !ap.Tau && !ap.Stopping && phase2PCs.Contains(ap.StartPC))) {
        var pc = atomicPath.StartPC;
        if (phase2PCToPath.ContainsKey(pc)) {
          AH.PrintError(pgp.prog, $"Multiple instructions occur at phase-2 PC {pc}.  I can't tell which of them to use for the proof that left movers are always enabled.");
        }
        else {
          phase2PCToPath[pc] = atomicPath;
        }
      }

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
        function GenerateLeftMover(s:LPlusState, tid:Armada_ThreadHandle) : LAtomic_Path
        {
           if tid in s.s.threads then
             var pc := s.s.threads[tid].pc;
      ";
      foreach (KeyValuePair<ArmadaPC, AtomicPath> entry in phase2PCToPath) {
        str += $"    if pc.{entry.Key}? then { lAtomic.GetConstructorString(entry.Value) } else\n";
      }
      str += $@"
             { lAtomic.GetConstructorString(lAtomic.TauPath) }
           else
             { lAtomic.GetConstructorString(lAtomic.TauPath) }
        }}
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
      pgp.AddTypeSynonym("type ARRequest = AtomicReductionRequest<LPlusState, LAtomic_Path, L.Armada_PC, HState, HAtomic_Path, H.Armada_PC>", "defs");

      string str = @"
        function GetAtomicReductionRequest() : ARRequest
        {
          AtomicReductionRequest(LAtomic_GetSpecFunctions(), HAtomic_GetSpecFunctions(),
                                 GetLPlusHRefinementRelation(), InductiveInv, GetLLRefinementRelation(),
                                 ConvertTotalState_LPlusH, ConvertAtomicPath_LH, ConvertPC_LH, 
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
          requires arr == GetAtomicReductionRequest()
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

    private void GenerateRightMoverCommutativityLemmaWithSpecificOther(AtomicPath rightMoverPath, AtomicPath otherPath)
    {
      string str;

      var prRightMover = new ReductionPathPrinter(lAtomic, "right_mover", "initial_state", "state_after_right_mover",
                                                  "right_mover", "mover_tid");
      var prOther = new ReductionPathPrinter(lAtomic, "other_path", "state_after_right_mover", "state_after_both_paths",
                                             "other_path", "other_tid");
      var prOtherAlt = new ReductionPathPrinter(lAtomic, "right_mover_alt", "initial_state", "state_after_other_path",
                                                "other_path", "other_tid");
      var prRightMoverAlt = new ReductionPathPrinter(lAtomic, "other_path_alt", "state_after_other_path", "state_after_both_paths'",
                                                     "right_mover", "mover_tid");

      if (otherPath.Stopping) {
        str = $@"
          lemma lemma_RightMoverPreservesCrashWithSpecificOther_{rightMoverPath.Name}_{otherPath.Name}(
            initial_state: LPlusState,
            state_after_right_mover: LPlusState,
            state_after_both_paths: LPlusState,
            right_mover: LAtomic_Path,
            other_path: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_other_path: LPlusState
            )
            requires InductiveInv(initial_state)
            requires right_mover.LAtomic_Path_{rightMoverPath.Name}?
            requires other_path.LAtomic_Path_{otherPath.Name}?
            requires !right_mover.LAtomic_Path_Tau?
            requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
            requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
            requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
            requires mover_tid in state_after_right_mover.s.threads
            requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
            ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
            ensures  !state_after_other_path.s.stop_reason.Armada_NotStopped?
            ensures  LLPlusStateRefinement(state_after_both_paths, state_after_other_path)
          {{
            { prRightMover.GetOpenValidPathInvocation(rightMoverPath) }
            { prOther.GetOpenValidPathInvocation(otherPath) }

            { prOtherAlt.GetOpenPathInvocation(otherPath) }

            /* { prOtherAlt.GetAssertValidPathInvocation(otherPath) } */

            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "path_" + otherPath.Name);
      }
      else {
        str = $@"
          lemma lemma_RightMoverCommutativityWithSpecificOther_{rightMoverPath.Name}_{otherPath.Name}(
            initial_state:LPlusState,
            state_after_right_mover:LPlusState,
            state_after_both_paths:LPlusState,
            right_mover:LAtomic_Path,
            other_path:LAtomic_Path,
            mover_tid:Armada_ThreadHandle,
            other_tid:Armada_ThreadHandle,
            state_after_other_path:LPlusState
            )
            requires InductiveInv(initial_state)
            requires right_mover.LAtomic_Path_{rightMoverPath.Name}?
            requires other_path.LAtomic_Path_{otherPath.Name}?
            requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
            requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
            requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
            requires mover_tid in state_after_right_mover.s.threads
            requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
            ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
            ensures  LAtomic_ValidPath(state_after_other_path, right_mover, mover_tid)
            ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, right_mover, mover_tid)
          {{
            var state_after_both_paths' := LAtomic_GetStateAfterPath(state_after_other_path, right_mover, mover_tid);

            { prRightMover.GetOpenValidPathInvocation(rightMoverPath) }
            { prOther.GetOpenValidPathInvocation(otherPath) }

            { prOtherAlt.GetOpenPathInvocation(otherPath) }
            { prRightMoverAlt.GetOpenPathInvocation(rightMoverPath) }

            /* { prOtherAlt.GetAssertValidPathInvocation(otherPath) } */
            /* { prRightMoverAlt.GetAssertValidPathInvocation(rightMoverPath) } */

            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "path_" + otherPath.Name);
      }
    }

    private void GenerateSpecificRightMoverCommutativityLemma(AtomicPath rightMoverPath)
    {
      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";

      foreach (var otherPath in lAtomic.AtomicPaths) {
        GenerateRightMoverCommutativityLemmaWithSpecificOther(rightMoverPath, otherPath);

        var caseIntro = $"case LAtomic_Path_{otherPath.Name}(_) =>\n";
        finalCasesCommutativity += caseIntro;
        finalCasesCrashPreservation += caseIntro;
        
        if (otherPath.Stopping) {
          finalCasesCommutativity += $@"
            lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(state_after_right_mover, other_path, other_tid);
            assert !asf.state_ok(state_after_both_paths);
            assert false;";
          finalCasesCrashPreservation += $@"
            lemma_RightMoverPreservesCrashWithSpecificOther_{rightMoverPath.Name}_{otherPath.Name}(
              initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
              mover_tid, other_tid, state_after_other_path);";
        }
        else {
          finalCasesCommutativity += $@"
            lemma_RightMoverCommutativityWithSpecificOther_{rightMoverPath.Name}_{otherPath.Name}(
              initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
              mover_tid, other_tid, state_after_other_path);";
          finalCasesCrashPreservation += $@"
            lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(state_after_right_mover, other_path, other_tid);
            lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(state_after_right_mover, other_path, other_tid);
            assert asf.state_ok(state_after_both_paths);
            assert false;";
        }
      }

      string str;

      str = $@"
        lemma lemma_RightMoverCommutativity_{rightMoverPath.Name}(
          initial_state: LPlusState,
          state_after_right_mover: LPlusState,
          state_after_both_paths: LPlusState,
          right_mover: LAtomic_Path,
          other_path: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_other_path: LPlusState
          )
          requires InductiveInv(initial_state)
          requires right_mover.LAtomic_Path_{rightMoverPath.Name}?
          requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
          requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
          requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
          requires mover_tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
          ensures  LAtomic_ValidPath(state_after_other_path, right_mover, mover_tid)
          ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, right_mover, mover_tid)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match other_path {{
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_RightMoverPreservesCrash_{rightMoverPath.Name}(
          initial_state: LPlusState,
          state_after_right_mover: LPlusState,
          state_after_both_paths: LPlusState,
          right_mover: LAtomic_Path,
          other_path: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_other_path: LPlusState
          )
          requires InductiveInv(initial_state)
          requires right_mover.LAtomic_Path_{rightMoverPath.Name}?
          requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
          requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
          requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
          requires mover_tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
          ensures  !state_after_other_path.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_paths, state_after_other_path)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match other_path {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRightMoverCommutativityLemmas()
    {
      string finalCasesCommutativity = "";
      string finalCasesCrashPreservation = "";

      foreach (var atomicPath in lAtomic.AtomicPaths) {

        var caseIntro = $"case LAtomic_Path_{atomicPath.Name}(_) =>\n";
        finalCasesCommutativity += caseIntro;
        finalCasesCrashPreservation += caseIntro;
        
        if (atomicPath.Tau) {
          finalCasesCommutativity += $@"
            assert right_mover.LAtomic_Path_Tau?;
            assert false;";
          finalCasesCrashPreservation += $@"
            assert right_mover.LAtomic_Path_Tau?;
            assert false;";
        }
        else if (atomicPath.Stopping) {
          finalCasesCommutativity += $@"
              lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(initial_state, right_mover, mover_tid);
              assert !asf.state_ok(state_after_right_mover);
              assert false;";
          finalCasesCrashPreservation += $@"
              lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(initial_state, right_mover, mover_tid);
              assert !asf.state_ok(state_after_right_mover);
              assert false;";
        }
        else if (phase1PCs.Contains(atomicPath.EndPC)) {
          GenerateSpecificRightMoverCommutativityLemma(atomicPath);
          finalCasesCommutativity += $@"
            lemma_RightMoverCommutativity_{atomicPath.Name}(
              initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
              mover_tid, other_tid, state_after_other_path);";
          finalCasesCrashPreservation += $@"
            lemma_RightMoverPreservesCrash_{atomicPath.Name}(
              initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
              mover_tid, other_tid, state_after_other_path);";
        }
        else {
          finalCasesCommutativity += $@"
            lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(initial_state, right_mover, mover_tid);
            assert !IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc);
            assert false;";
          finalCasesCrashPreservation += $@"
            lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(initial_state, right_mover, mover_tid);
            assert !IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc);
            assert false;";
        }
      }

      string str;

      str = $@"
        lemma lemma_RightMoverCommutativity(
          initial_state: LPlusState,
          state_after_right_mover: LPlusState,
          state_after_both_paths: LPlusState,
          right_mover: LAtomic_Path,
          other_path: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_other_path: LPlusState
          )
          requires InductiveInv(initial_state)
          requires !right_mover.LAtomic_Path_Tau?
          requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
          requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
          requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
          requires mover_tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
          ensures  LAtomic_ValidPath(state_after_other_path, right_mover, mover_tid)
          ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, right_mover, mover_tid)
        {{
          var asf := LAtomic_GetSpecFunctions();
          lemma_LAtomic_PathImpliesThreadRunning(state_after_right_mover, other_path, other_tid);
          assert asf.state_ok(state_after_right_mover);
          match right_mover {{
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_RightMoverPreservesCrash(
          initial_state: LPlusState,
          state_after_right_mover: LPlusState,
          state_after_both_paths: LPlusState,
          right_mover: LAtomic_Path,
          other_path: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_other_path: LPlusState
          )
          requires InductiveInv(initial_state)
          requires !right_mover.LAtomic_Path_Tau?
          requires LAtomic_ValidPath(initial_state, right_mover, mover_tid)
          requires state_after_right_mover == LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid)
          requires LAtomic_ValidPath(state_after_right_mover, other_path, other_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid)
          requires mover_tid in state_after_right_mover.s.threads
          requires IsPhase1PC(state_after_right_mover.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LAtomic_ValidPath(initial_state, other_path, other_tid)
          ensures  !state_after_other_path.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_paths, state_after_other_path)
        {{
          var asf := LAtomic_GetSpecFunctions();
          lemma_LAtomic_PathImpliesThreadRunning(state_after_right_mover, other_path, other_tid);
          match right_mover {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLeftMoverCommutativityLemmaWithSpecificOther(AtomicPath otherPath, AtomicPath leftMoverPath)
    {
      string str;

      if (!otherPath.Stopping && !leftMoverPath.Stopping) {
        var prOther = new ReductionPathPrinter(lAtomic, "other_path", "initial_state", "state_after_othe_path", "other_path", "other_tid");
        var prLeftMover = new ReductionPathPrinter(lAtomic, "left_mover", "state_after_other_path", "state_after_both_paths",
                                                   "left_mover", "mover_tid");
        var prLeftMoverAlt = new ReductionPathPrinter(lAtomic, "left_mover_alt", "initial_state", "state_after_left_mover",
                                                      "left_mover", "mover_tid");
        var prOtherAlt = new ReductionPathPrinter(lAtomic, "other_path_alt", "state_after_left_mover", "state_after_both_paths'",
                                                  "other_path", "other_tid");

        str = $@"
          lemma lemma_LeftMoverCommutativityWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
            initial_state: LPlusState,
            state_after_other_path: LPlusState,
            state_after_both_paths: LPlusState,
            other_path: LAtomic_Path,
            left_mover: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_left_mover: LPlusState
            )
            requires InductiveInv(initial_state)
            requires other_path.LAtomic_Path_{otherPath.Name}?
            requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
            requires LAtomic_ValidPath(initial_state, other_path, other_tid)
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
            requires mover_tid in state_after_other_path.s.threads
            requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
            requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(state_after_left_mover, other_path, other_tid)
            ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
          {{
            var state_after_both_paths' := LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid);

            { prOther.GetOpenValidPathInvocation(otherPath) }
            { prLeftMover.GetOpenValidPathInvocation(leftMoverPath) }

            { prLeftMoverAlt.GetOpenPathInvocation(leftMoverPath) }
            { prOtherAlt.GetOpenPathInvocation(otherPath) }

            /* { prLeftMoverAlt.GetAssertValidPathInvocation(leftMoverPath) } */
            /* { prOtherAlt.GetAssertValidPathInvocation(otherPath) } */

            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "path_" + otherPath.Name);
      }

      if (otherPath.Stopping) {
        var prOther = new ReductionPathPrinter(lAtomic, "other_path", "initial_state", "state_after_other_path", "other_path", "other_tid");
        var prLeftMover = new ReductionPathPrinter(lAtomic, "left_mover", "initial_state", "state_after_left_mover",
                                                   "left_mover", "mover_tid");
        var prOtherAlt = new ReductionPathPrinter(lAtomic, "other_path_alt", "state_after_left_mover", "state_after_both_paths",
                                                  "other_path", "other_tid");

        str = $@"
          lemma lemma_LeftMoverPreservesCrashWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
            initial_state: LPlusState,
            state_after_other_path: LPlusState,
            state_after_left_mover: LPlusState,
            other_path: LAtomic_Path,
            left_mover: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_both_paths: LPlusState
            )
            requires InductiveInv(initial_state)
            requires other_path.LAtomic_Path_{otherPath.Name}?
            requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
            requires LAtomic_ValidPath(initial_state, other_path, other_tid)
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires LAtomic_ValidPath(initial_state, left_mover, mover_tid)
            requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
            requires mover_tid in initial_state.s.threads
            requires IsPhase2PC(initial_state.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires !state_after_other_path.s.stop_reason.Armada_NotStopped?
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
            ensures  LAtomic_ValidPath(state_after_left_mover, other_path, other_tid)
            ensures  !state_after_both_paths.s.stop_reason.Armada_NotStopped?
            ensures  LLPlusStateRefinement(state_after_other_path, state_after_both_paths)
          {{
            { prOther.GetOpenValidPathInvocation(otherPath) }
            { prLeftMover.GetOpenValidPathInvocation(leftMoverPath) }

            { prOtherAlt.GetOpenPathInvocation(otherPath) }

            /* { prOtherAlt.GetAssertValidPathInvocation(otherPath) } */

            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "path_" + otherPath.Name);
      }

      if (!otherPath.Stopping && leftMoverPath.Stopping) {
        var prOther = new ReductionPathPrinter(lAtomic, "other_path", "initial_state", "state_after_other_path", "other_path", "other_tid");
        var prLeftMover = new ReductionPathPrinter(lAtomic, "left_mover", "state_after_other_path", "state_after_both_paths",
                                                   "left_mover", "mover_tid");
        var prLeftMoverAlt = new ReductionPathPrinter(lAtomic, "left_mover_alt", "initial_state", "state_after_left_mover",
                                                      "left_mover", "mover_tid");

        str = $@"
          lemma lemma_LeftMoverPreservesSelfCrashWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
            initial_state: LPlusState,
            state_after_other_path: LPlusState,
            state_after_both_paths: LPlusState,
            other_path: LAtomic_Path,
            left_mover: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_left_mover: LPlusState
            )
            requires InductiveInv(initial_state)
            requires other_path.LAtomic_Path_{otherPath.Name}?
            requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
            requires LAtomic_ValidPath(initial_state, other_path, other_tid)
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
            requires mover_tid in state_after_other_path.s.threads
            requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires initial_state.s.stop_reason.Armada_NotStopped?
            requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
            requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
            ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
            ensures  LLPlusStateRefinement(state_after_both_paths, state_after_left_mover)
          {{
            { prOther.GetOpenValidPathInvocation(otherPath) }
            { prLeftMover.GetOpenValidPathInvocation(leftMoverPath) }

            { prLeftMoverAlt.GetOpenPathInvocation(leftMoverPath) }

            /* { prLeftMoverAlt.GetAssertValidPathInvocation(leftMoverPath) } */

            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "path_" + otherPath.Name);
      }
    }

    private void GenerateSpecificLeftMoverCommutativityLemma(AtomicPath leftMoverPath)
    {
      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";
      var finalCasesSelfCrashPreservation = "";

      foreach (var otherPath in lAtomic.AtomicPaths) {
        GenerateLeftMoverCommutativityLemmaWithSpecificOther(otherPath, leftMoverPath);

        var caseIntro = $"case LAtomic_Path_{otherPath.Name}(_) =>\n";

        if (!leftMoverPath.Stopping) {
          finalCasesCommutativity += caseIntro;
          if (otherPath.Stopping) {
            finalCasesCommutativity += $@"
              lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(initial_state, other_path, other_tid);
              assert !asf.state_ok(state_after_other_path);
              assert false;";
          }
          else {
            finalCasesCommutativity += $@"
              lemma_LeftMoverCommutativityWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
                initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                mover_tid, other_tid, state_after_left_mover);";
          }
        }

        finalCasesCrashPreservation += caseIntro;
        if (otherPath.Stopping) {
          finalCasesCrashPreservation += $@"
            lemma_LeftMoverPreservesCrashWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
              initial_state, state_after_other_path, state_after_left_mover, other_path, left_mover,
              mover_tid, other_tid, state_after_both_paths);";
        }
        else {
          finalCasesCrashPreservation += $@"
            lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(initial_state, other_path, other_tid);
            lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(initial_state, other_path, other_tid);
            assert asf.state_ok(state_after_other_path);
            assert false;";
        }

        if (leftMoverPath.Stopping) {
          finalCasesSelfCrashPreservation += caseIntro;
          if (otherPath.Stopping) {
            finalCasesSelfCrashPreservation += $@"
              lemma_LAtomic_PathHasPCEffect_{otherPath.Name}(initial_state, other_path, other_tid);
              assert !asf.state_ok(state_after_other_path);
              assert false;";
          }
          else {
            finalCasesSelfCrashPreservation += $@"
              lemma_LeftMoverPreservesSelfCrashWithSpecificOther_{otherPath.Name}_{leftMoverPath.Name}(
                initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                mover_tid, other_tid, state_after_left_mover);";
          }
        }
      }

      string str;

      if (!leftMoverPath.Stopping) {
        str = $@"
          lemma lemma_LeftMoverCommutativity_{leftMoverPath.Name}(
            initial_state: LPlusState,
            state_after_other_path: LPlusState,
            state_after_both_paths: LPlusState,
            other_path: LAtomic_Path,
            left_mover: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_left_mover: LPlusState
            )
            requires InductiveInv(initial_state)
            requires LAtomic_ValidPath(initial_state, other_path, other_tid)
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
            requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
            requires mover_tid in state_after_other_path.s.threads
            requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
            requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(state_after_left_mover, other_path, other_tid)
            ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
          {{
            var asf := LAtomic_GetSpecFunctions();
            lemma_LAtomic_PathImpliesThreadRunning(state_after_other_path, left_mover, mover_tid);
            match other_path {{
              {finalCasesCommutativity}
            }}
          }}
        ";
        pgp.AddLemma(str);
      }

      str = $@"
        lemma lemma_LeftMoverPreservesCrash_{leftMoverPath.Name}(
          initial_state: LPlusState,
          state_after_other_path: LPlusState,
          state_after_left_mover: LPlusState,
          other_path: LAtomic_Path,
          left_mover: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_both_paths: LPlusState
          )
          requires InductiveInv(initial_state)
          requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
          requires LAtomic_ValidPath(initial_state, other_path, other_tid)
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires LAtomic_ValidPath(initial_state, left_mover, mover_tid)
          requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
          requires mover_tid in initial_state.s.threads
          requires IsPhase2PC(initial_state.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires !state_after_other_path.s.stop_reason.Armada_NotStopped?
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
          ensures  LAtomic_ValidPath(state_after_left_mover, other_path, other_tid)
          ensures  !state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_other_path, state_after_both_paths)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match other_path {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);

      if (leftMoverPath.Stopping) {
        str = $@"
          lemma lemma_LeftMoverPreservesSelfCrash_{leftMoverPath.Name}(
            initial_state: LPlusState,
            state_after_other_path: LPlusState,
            state_after_both_paths: LPlusState,
            other_path: LAtomic_Path,
            left_mover: LAtomic_Path,
            mover_tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle,
            state_after_left_mover: LPlusState
            )
            requires InductiveInv(initial_state)
            requires left_mover.LAtomic_Path_{leftMoverPath.Name}?
            requires LAtomic_ValidPath(initial_state, other_path, other_tid)
            requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
            requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
            requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
            requires mover_tid in state_after_other_path.s.threads
            requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
            requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
            requires initial_state.s.stop_reason.Armada_NotStopped?
            requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
            requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
            ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
            ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
            ensures  LLPlusStateRefinement(state_after_both_paths, state_after_left_mover)
          {{
            var asf := LAtomic_GetSpecFunctions();
            lemma_LAtomic_PathImpliesThreadRunning(state_after_other_path, left_mover, mover_tid);
            match other_path {{
              {finalCasesSelfCrashPreservation}
            }}
          }}
        ";
        pgp.AddLemma(str);
      }
    }

    private void GenerateLeftMoverCommutativityLemmas()
    {
      var finalCasesCommutativity = "";
      var finalCasesCrashPreservation = "";
      var finalCasesSelfCrashPreservation = "";

      foreach (var atomicPath in lAtomic.AtomicPaths)
      {
        string caseIntro = $"case LAtomic_Path_{atomicPath.Name}(_) =>\n";
        finalCasesCommutativity += caseIntro;
        finalCasesCrashPreservation += caseIntro;
        finalCasesSelfCrashPreservation += caseIntro;

        if (atomicPath.Tau)
        {
          finalCasesCommutativity += $@"
            assert left_mover.LAtomic_Path_Tau?;
            assert false;";
          finalCasesCrashPreservation += $@"
            assert left_mover.LAtomic_Path_Tau?;
            assert false;";
          finalCasesSelfCrashPreservation += $@"
            assert left_mover.LAtomic_Path_Tau?;
            assert false;";
        }
        else if (!phase2PCs.Contains(atomicPath.StartPC))
        {
          finalCasesCommutativity += $@"
            lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(state_after_other_path, left_mover, mover_tid);
            assert !IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc);
            assert false;";
          finalCasesCrashPreservation += $@"
            lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(initial_state, left_mover, mover_tid);
            assert !IsPhase2PC(initial_state.s.threads[mover_tid].pc);
            assert false;";
          finalCasesSelfCrashPreservation += $@"
            lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(state_after_other_path, left_mover, mover_tid);
            assert !IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc);
            assert false;";
        }
        else {
          GenerateSpecificLeftMoverCommutativityLemma(atomicPath);

          if (atomicPath.Stopping) {
            finalCasesCommutativity += $@"
              lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(state_after_other_path, left_mover, mover_tid);
              assert !asf.state_ok(state_after_both_paths);
              assert false;";
          }
          else {
            finalCasesCommutativity += $@"
              lemma_LeftMoverCommutativity_{atomicPath.Name}(
                initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                mover_tid, other_tid, state_after_left_mover);";
          }

          finalCasesCrashPreservation += $@"
            lemma_LeftMoverPreservesCrash_{atomicPath.Name}(
              initial_state, state_after_other_path, state_after_left_mover, other_path, left_mover,
              mover_tid, other_tid, state_after_both_paths);";

          if (atomicPath.Stopping) {
            finalCasesSelfCrashPreservation += $@"
              lemma_LeftMoverPreservesSelfCrash_{atomicPath.Name}(
                initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                mover_tid, other_tid, state_after_left_mover);";
          }
          else {
            finalCasesSelfCrashPreservation += $@"
              lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(state_after_other_path, left_mover, mover_tid);
              assert asf.state_ok(state_after_both_paths);
              assert false;";
          }
        }
      }

      string str;

      str = $@"
        lemma lemma_LeftMoverCommutativity(
          initial_state: LPlusState,
          state_after_other_path: LPlusState,
          state_after_both_paths: LPlusState,
          other_path: LAtomic_Path,
          left_mover: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_left_mover: LPlusState
          )
          requires InductiveInv(initial_state)
          requires LAtomic_ValidPath(initial_state, other_path, other_tid)
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires !left_mover.LAtomic_Path_Tau?
          requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
          requires mover_tid in state_after_other_path.s.threads
          requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires state_after_both_paths.s.stop_reason.Armada_NotStopped?
          requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid);
          ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
          ensures  LAtomic_ValidPath(LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid), other_path, other_tid)
          ensures  state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match left_mover {{
            {finalCasesCommutativity}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesCrash(
          initial_state: LPlusState,
          state_after_other_path: LPlusState,
          state_after_left_mover: LPlusState,
          other_path: LAtomic_Path,
          left_mover: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_both_paths: LPlusState
          )
          requires InductiveInv(initial_state)
          requires LAtomic_ValidPath(initial_state, other_path, other_tid)
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires LAtomic_ValidPath(initial_state, left_mover, mover_tid)
          requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
          requires mover_tid in initial_state.s.threads
          requires IsPhase2PC(initial_state.s.threads[mover_tid].pc)
          requires !left_mover.LAtomic_Path_Tau?
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires !state_after_other_path.s.stop_reason.Armada_NotStopped?
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_left_mover, other_path, other_tid)
          ensures  LAtomic_ValidPath(state_after_left_mover, other_path, other_tid)
          ensures  !state_after_both_paths.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_other_path, state_after_both_paths)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match left_mover {{
            {finalCasesCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LeftMoverPreservesSelfCrash(
          initial_state: LPlusState,
          state_after_other_path: LPlusState,
          state_after_both_paths: LPlusState,
          other_path: LAtomic_Path,
          left_mover: LAtomic_Path,
          mover_tid: Armada_ThreadHandle,
          other_tid: Armada_ThreadHandle,
          state_after_left_mover: LPlusState
          )
          requires InductiveInv(initial_state)
          requires LAtomic_ValidPath(initial_state, other_path, other_tid)
          requires state_after_other_path == LAtomic_GetStateAfterPath(initial_state, other_path, other_tid)
          requires LAtomic_ValidPath(state_after_other_path, left_mover, mover_tid)
          requires state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, left_mover, mover_tid)
          requires mover_tid in state_after_other_path.s.threads
          requires IsPhase2PC(state_after_other_path.s.threads[mover_tid].pc)
          requires !left_mover.LAtomic_Path_Tau?
          requires other_path.LAtomic_Path_Tau? || other_tid != mover_tid
          requires initial_state.s.stop_reason.Armada_NotStopped?
          requires !state_after_both_paths.s.stop_reason.Armada_NotStopped?
          requires state_after_left_mover == LAtomic_GetStateAfterPath(initial_state, left_mover, mover_tid)
          ensures  LAtomic_ValidPath(initial_state, left_mover, mover_tid)
          ensures  !state_after_left_mover.s.stop_reason.Armada_NotStopped?
          ensures  LLPlusStateRefinement(state_after_both_paths, state_after_left_mover)
        {{
          var asf := LAtomic_GetSpecFunctions();
          match left_mover {{
            {finalCasesSelfCrashPreservation}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLHYieldingCorrespondenceLemma()
    {
      string str;

      str = @"
        lemma lemma_LHYieldingCorrespondence(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
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
        str += $@"
          case {pc} => assert arr.h.is_pc_nonyielding(hpc) <==> (arr.l.is_pc_nonyielding(lpc) || arr.is_phase1(lpc) || arr.is_phase2(lpc));
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

      var pr = new PathPrinter(lAtomic);
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var nameSuffix = atomicPath.Name;
        str = $@"
          lemma lemma_RightMoversPreserveStateRefinement_{nameSuffix}(
            arr: ARRequest,
            s: LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle
            )
            requires arr == GetAtomicReductionRequest()
            requires LAtomic_ValidPath(s, path, tid)
            requires !path.LAtomic_Path_Tau?
            requires path.LAtomic_Path_{nameSuffix}?
            ensures  var s' := LAtomic_GetStateAfterPath(s, path, tid);
                     var pc' := arr.l.get_thread_pc(s', tid);
                     (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
          {{
            { pr.GetOpenValidPathInvocation(atomicPath) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);

        finalCases += $"case LAtomic_Path_{nameSuffix}(_) => lemma_RightMoversPreserveStateRefinement_{nameSuffix}(arr, s, path, tid);\n";
      }

      str = $@"
        lemma lemma_RightMoversPreserveStateRefinement(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures RightMoversPreserveStateRefinement(arr)
        {{
           forall s, path, tid | arr.l.path_valid(s, path, tid) && !arr.l.path_type(path).AtomicPathType_Tau?
             ensures var s' := arr.l.path_next(s, path, tid);
                     var pc' := arr.l.get_thread_pc(s', tid);
                     (pc'.Some? && arr.is_phase1(pc'.v) && arr.l.state_ok(s') ==> RefinementPair(s', s) in arr.self_relation)
           {{
             match path {{
               {finalCases}
             }}
           }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateAtomicPathCantAffectOtherThreadPhaseExceptViaForkLemma()
    {

      string postcondition = @"forall other_tid :: tid != other_tid ==>
                               var s' := asf.path_next(s, path, tid);
                               var pc := asf.get_thread_pc(s, other_tid);
                               var pc' := asf.get_thread_pc(s', other_tid);
                               (pc' != pc ==> pc.None? && !IsPhase1PC(pc'.v) && !IsPhase2PC(pc'.v) && !asf.is_pc_nonyielding(pc'.v))";
      lAtomic.GeneratePerAtomicPathLemma(null,
                                         "AtomicPathCantAffectOtherThreadPhaseExceptViaFork",
                                         atomicPath => true,
                                         atomicPath => postcondition,
                                         atomicPath => "",
                                         false);
      lAtomic.GenerateOverallAtomicPathLemma(null,
                                             "AtomicPathCantAffectOtherThreadPhaseExceptViaFork",
                                             "AtomicPathCantAffectOtherThreadPhaseExceptViaFork",
                                             postcondition,
                                             ap => true);

      string str = @"
        lemma lemma_ThreadCantAffectOtherThreadPhaseExceptViaFork(arr:ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures  ThreadCantAffectOtherThreadPhaseExceptViaFork(arr)
        {
          forall s, path, tid, other_tid | arr.l.path_valid(s, path, tid) && tid != other_tid
            ensures var s' := arr.l.path_next(s, path, tid);
                    var pc := arr.l.get_thread_pc(s, other_tid);
                    var pc' := arr.l.get_thread_pc(s', other_tid);
                    pc' != pc ==> pc.None? && !arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v) && !arr.l.is_pc_nonyielding(pc'.v)
          {
            lemma_LAtomic_AtomicPathCantAffectOtherThreadPhaseExceptViaFork(arr.l, s, path, tid);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasSupportingValidRequest()
    {
      string str;

      lAtomic.GeneratePCEffectLemmas();
      lAtomic.GenerateAtomicPathRequiresOKLemma();
      lAtomic.GenerateAtomicSteppingThreadHasPCLemma();
      lAtomic.GenerateAtomicTauLeavesPCUnchangedLemma();
      lAtomic.GenerateAtomicPathTypeAlwaysMatchesPCTypesLemma();
      hAtomic.GeneratePCEffectLemmas();
      hAtomic.GenerateAtomicPathTypeAlwaysMatchesPCTypesLemma();

      str = @"
        lemma lemma_RefinementRelationsSatisfyRequirements(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures RefinementRelationReflexive(arr.self_relation)
          ensures RefinementRelationTransitive(arr.self_relation)
          ensures RefinementRelationsConvolve(arr.self_relation, arr.relation, arr.relation)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateGenericAtomicPropertyLemmas();

      str = $@"
        lemma lemma_LAtomic_AtomicInitImpliesYielding()
          ensures AtomicInitImpliesYielding(LAtomic_GetSpecFunctions())
        {{
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LStateToHStateMapsPCsCorrectly(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LStateToHStateMapsPCsCorrectly(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateLHYieldingCorrespondenceLemma();

      str = @"
        lemma lemma_LHPathPropertiesMatch(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LHPathPropertiesMatch(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LPathImpliesHPath(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LPathImpliesHPath(arr)
        {
          forall ls, lpath, tid | arr.inv(ls) && arr.l.path_valid(ls, lpath, tid)
            ensures var ls' := arr.l.path_next(ls, lpath, tid);
                    var hs := arr.lstate_to_hstate(ls);
                    var hpath := arr.lpath_to_hpath(lpath);
                    var hs' := arr.lstate_to_hstate(ls');
                    && arr.h.path_valid(hs, hpath, tid)
                    && hs' == arr.h.path_next(hs, hpath, tid)
          {
            lemma_LiftAtomicPath(ls, lpath, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionPreservesOK(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures StateConversionPreservesOK(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionSatisfiesRelation(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures StateConversionSatisfiesRelation(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ThreadsDontStartInAnyPhase(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures ThreadsDontStartInAnyPhase(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PhasesDontOverlap(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures PhasesDontOverlap(arr)
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateAtomicPathCantAffectOtherThreadPhaseExceptViaForkLemma();

      str = @"
        lemma lemma_PhasesPrecededByYielding(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures PhasesPrecededByYielding(arr)
        {
          forall s, path, tid |
            var s' := arr.l.path_next(s, path, tid);
            var pc := arr.l.get_thread_pc(s, tid);
            var pc' := arr.l.get_thread_pc(s', tid);
            && arr.l.path_valid(s, path, tid)
            && pc'.Some?
            && (arr.is_phase1(pc'.v) || arr.is_phase2(pc'.v))
            && pc.Some?
            && (!arr.is_phase1(pc.v) && !arr.is_phase2(pc.v))
            ensures var pc := arr.l.get_thread_pc(s, tid);
                    !arr.l.is_pc_nonyielding(pc.v)
          {
            match path {
      ";
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        str += $@"
              case LAtomic_Path_{atomicPath.Name}(_) =>
                lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
        ";
      }
      str += "} } }\n";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PhasesSucceededByYielding(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures PhasesSucceededByYielding(arr)
        {
          forall s, path, tid |
            var s' := arr.l.path_next(s, path, tid);
            var pc := arr.l.get_thread_pc(s, tid);
            var pc' := arr.l.get_thread_pc(s', tid);
            && arr.l.path_valid(s, path, tid)
            && pc.Some?
            && (arr.is_phase1(pc.v) || arr.is_phase2(pc.v))
            && pc'.Some?
            && (!arr.is_phase1(pc'.v) && !arr.is_phase2(pc'.v))
            ensures var s' := arr.l.path_next(s, path, tid);
                    var pc' := arr.l.get_thread_pc(s', tid);
                    !arr.l.is_pc_nonyielding(pc'.v)
          {
            match path {
      ";
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        str += $@"
              case LAtomic_Path_{atomicPath.Name}(_) =>
                lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
        ";
      }
      str += "} } }\n";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_Phase2NotFollowedByPhase1(arr:ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures Phase2NotFollowedByPhase1(arr)
        {
          forall s, path, tid |
            var s' := arr.l.path_next(s, path, tid);
            var pc := arr.l.get_thread_pc(s, tid);
            var pc' := arr.l.get_thread_pc(s', tid);
            && arr.l.path_valid(s, path, tid)
            && pc.Some?
            && arr.is_phase2(pc.v)
            && pc'.Some?
            && !arr.is_phase2(pc'.v)
            ensures var s' := arr.l.path_next(s, path, tid);
                    var pc' := arr.l.get_thread_pc(s', tid);
                    !arr.is_phase1(pc'.v)
          {
            match path {
      ";
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        str += $@"
              case LAtomic_Path_{atomicPath.Name}(_) =>
                lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
        ";
      }
      str += "} } }\n";
      pgp.AddLemma(str);

      GenerateRightMoversPreserveStateRefinementLemma();

      var pr = new PathPrinter(lAtomic);
      str = @"
        lemma lemma_LeftMoversPreserveStateRefinement(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LeftMoversPreserveStateRefinement(arr)
        {
          forall s, path, tid | arr.l.path_valid(s, path, tid) && !arr.l.path_type(path).AtomicPathType_Tau?
            ensures var s' := arr.l.path_next(s, path, tid);
                    var pc := arr.l.get_thread_pc(s, tid);
                    (pc.Some? && arr.is_phase2(pc.v) ==> RefinementPair(s, s') in arr.self_relation)
          {
            var pc := arr.l.get_thread_pc(s, tid);
            var s' := arr.l.path_next(s, path, tid);
            match path {
      ";
      str += String.Join("\n", lAtomic.AtomicPaths.Select(atomicPath => $@"
        case LAtomic_Path_{atomicPath.Name}(_) => " +
          (phase2PCs.Contains(atomicPath.StartPC)
             ? $@"{ pr.GetOpenValidPathInvocation(atomicPath) }
                  assert RefinementPair(s, s') in arr.self_relation;"
             : $@"lemma_LAtomic_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
                  assert !arr.is_phase2(pc.v);")
      ));
      str += "}\n}\n}";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RightMoversCommute(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures RightMoversCommute(arr)
        {
          forall initial_state, right_mover, other_path, mover_tid, other_tid
            {:trigger RightMoversCommuteConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)}
            | RightMoversCommuteConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)
            ensures var state_after_right_mover := LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid);
                    var state_after_both_paths := LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid);
                    var state_after_other_path := LAtomic_GetStateAfterPath(initial_state, other_path, other_tid);
                    && LAtomic_ValidPath(initial_state, other_path, other_tid)
                    && LAtomic_ValidPath(state_after_other_path, right_mover, mover_tid)
                    && state_after_both_paths == LAtomic_GetStateAfterPath(state_after_other_path, right_mover, mover_tid)
          {
            var state_after_right_mover := LAtomic_GetStateAfterPath(initial_state, right_mover, mover_tid);
            var state_after_both_paths := LAtomic_GetStateAfterPath(state_after_right_mover, other_path, other_tid);
            var state_after_other_path := LAtomic_GetStateAfterPath(initial_state, other_path, other_tid);
            lemma_RightMoverCommutativity(initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
                                          mover_tid, other_tid, state_after_other_path);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RightMoverCrashPreservation(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures RightMoverCrashPreservation(arr)
        {
          forall initial_state, right_mover, other_path, mover_tid, other_tid
            {:trigger RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)}
            | RightMoverCrashPreservationConditions(arr, initial_state, right_mover, other_path, mover_tid, other_tid)
            ensures var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
                    var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
                    var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
                    && arr.l.path_valid(initial_state, other_path, other_tid)
                    && !arr.l.state_ok(state_after_other_path)
                    && RefinementPair(state_after_both_paths, state_after_other_path) in arr.self_relation
          {
            var state_after_right_mover := arr.l.path_next(initial_state, right_mover, mover_tid);
            var state_after_both_paths := arr.l.path_next(state_after_right_mover, other_path, other_tid);
            var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
            lemma_RightMoverPreservesCrash(initial_state, state_after_right_mover, state_after_both_paths, right_mover, other_path,
                                           mover_tid, other_tid, state_after_other_path);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoversCommute(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LeftMoversCommute(arr)
        {
          forall initial_state, other_path, left_mover, mover_tid, other_tid
            {:trigger LeftMoversCommuteConditions(arr, initial_state, other_path, left_mover, mover_tid, other_tid)}
            | LeftMoversCommuteConditions(arr, initial_state, other_path, left_mover, mover_tid, other_tid)
            ensures var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
                    var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
                    var new_middle_state := arr.l.path_next(initial_state, left_mover, mover_tid);
                    && arr.l.path_valid(initial_state, left_mover, mover_tid)
                    && arr.l.path_valid(new_middle_state, other_path, other_tid)
                    && state_after_both_paths == arr.l.path_next(new_middle_state, other_path, other_tid)
          {
            var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
            var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
            var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
            lemma_LeftMoverCommutativity(initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                                         mover_tid, other_tid, state_after_left_mover);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoverCrashPreservation(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LeftMoverCrashPreservation(arr)
        {
          forall initial_state, left_mover, other_path, mover_tid, other_tid
            {:trigger LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)}
            | LeftMoverCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)
            ensures var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
                    var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
                    var state_after_both_paths := arr.l.path_next(state_after_left_mover, other_path, other_tid);
                    && arr.l.path_valid(state_after_left_mover, other_path, other_tid)
                    && !arr.l.state_ok(state_after_both_paths)
                    && RefinementPair(state_after_other_path, state_after_both_paths) in arr.self_relation
          {
            var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
            var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
            var state_after_both_paths := arr.l.path_next(state_after_left_mover, other_path, other_tid);
            lemma_LeftMoverPreservesCrash(initial_state, state_after_other_path, state_after_left_mover, other_path, left_mover,
                                          mover_tid, other_tid, state_after_both_paths);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoverSelfCrashPreservation(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures LeftMoverSelfCrashPreservation(arr)
        {
          forall initial_state, left_mover, other_path, mover_tid, other_tid
            {:trigger LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)}
            | LeftMoverSelfCrashPreservationConditions(arr, initial_state, left_mover, other_path, mover_tid, other_tid)
            ensures var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
                    var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
                    var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
                    && arr.l.path_valid(initial_state, left_mover, mover_tid)
                    && !arr.l.state_ok(state_after_left_mover)
                    && RefinementPair(state_after_both_paths, state_after_left_mover) in arr.self_relation
          {
            var state_after_other_path := arr.l.path_next(initial_state, other_path, other_tid);
            var state_after_both_paths := arr.l.path_next(state_after_other_path, left_mover, mover_tid);
            var state_after_left_mover := arr.l.path_next(initial_state, left_mover, mover_tid);
            lemma_LeftMoverPreservesSelfCrash(initial_state, state_after_other_path, state_after_both_paths, other_path, left_mover,
                                              mover_tid, other_tid, state_after_left_mover);
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

      var pr = new PathPrinter(lAtomic);
      foreach (KeyValuePair<ArmadaPC, AtomicPath> entry in phase2PCToPath)
      {
        var pc = entry.Key;
        var atomicPath = entry.Value;
        var nameSuffix = atomicPath.Name;
        str = $@"
          lemma lemma_LeftMoverEnabled_{nameSuffix}(s: LPlusState, tid: Armada_ThreadHandle, path: LAtomic_Path)
            requires InductiveInv(s)
            requires s.s.stop_reason.Armada_NotStopped?
            requires tid in s.s.threads
            requires s.s.threads[tid].pc.{pc}?
            requires path == GenerateLeftMover(s, tid)
            ensures  LAtomic_ValidPath(s, path, tid)
            ensures  !path.LAtomic_Path_Tau?
            ensures  0 <= LeftMoverGenerationProgress(LAtomic_GetStateAfterPath(s, path, tid), tid) < LeftMoverGenerationProgress(s, tid)
          {{
            assert s.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?;
            { pr.GetOpenPathInvocation(atomicPath) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);
        body += $@"
          if pc.{pc}? {{
            lemma_LeftMoverEnabled_{nameSuffix}(s, tid, path);
          }}
        ";
      }

      str = $@"
        lemma lemma_LeftMoverEnabled(s: LPlusState, tid: Armada_ThreadHandle, path: LAtomic_Path)
          requires InductiveInv(s)
          requires s.s.stop_reason.Armada_NotStopped?
          requires tid in s.s.threads
          requires IsPhase2PC(s.s.threads[tid].pc)
          requires path == GenerateLeftMover(s, tid)
          ensures  LAtomic_ValidPath(s, path, tid)
          ensures  !path.LAtomic_Path_Tau?
          ensures  0 <= LeftMoverGenerationProgress(LAtomic_GetStateAfterPath(s, path, tid), tid) < LeftMoverGenerationProgress(s, tid)
        {{
          var pc := s.s.threads[tid].pc;
          { body }
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LeftMoversAlwaysEnabled(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures  LeftMoversAlwaysEnabled(arr)
        {
          forall s, tid {:trigger LeftMoversAlwaysEnabledConditions(arr, s, tid)}
            | LeftMoversAlwaysEnabledConditions(arr, s, tid)
            ensures var path := arr.generate_left_mover(s, tid);
                    && LAtomic_ValidPath(s, path, tid)
                    && !arr.l.path_type(path).AtomicPathType_Tau?
                    && var s' := LAtomic_GetStateAfterPath(s, path, tid);
                       0 <= arr.left_mover_generation_progress(s', tid) < arr.left_mover_generation_progress(s, tid)
          {
            var path := arr.generate_left_mover(s, tid);
            lemma_LeftMoverEnabled(s, tid, path);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateIsValidRequest()
    {
      string str = @"
        lemma lemma_IsValidAtomicReductionRequest(arr: ARRequest)
          requires arr == GetAtomicReductionRequest()
          ensures  ValidAtomicReductionRequest(arr)
        {
          lemma_RefinementRelationsSatisfyRequirements(arr);
          lemma_LInitImpliesHInit(arr);
          lemma_LAtomic_AtomicInitImpliesInv();
          lemma_LAtomic_AtomicPathPreservesInv();
          lemma_LAtomic_AtomicPathRequiresOK();
          lemma_LAtomic_AtomicInitImpliesYielding();
          lemma_LAtomic_AtomicInitImpliesOK();
          lemma_LAtomic_AtomicPathTypeAlwaysMatchesPCTypes();
          lemma_HAtomic_AtomicPathTypeAlwaysMatchesPCTypes();
          lemma_LStateToHStateMapsPCsCorrectly(arr);
          lemma_LHYieldingCorrespondence(arr);
          lemma_LHPathPropertiesMatch(arr);
          lemma_LPathImpliesHPath(arr);
          lemma_StateConversionPreservesOK(arr);
          lemma_StateConversionSatisfiesRelation(arr);
          lemma_ThreadsDontStartInAnyPhase(arr);
          lemma_PhasesDontOverlap(arr);
          lemma_ThreadCantAffectOtherThreadPhaseExceptViaFork(arr);
          lemma_PhasesPrecededByYielding(arr);
          lemma_PhasesSucceededByYielding(arr);
          lemma_Phase2NotFollowedByPhase1(arr);
          lemma_LAtomic_AtomicSteppingThreadHasPC();
          lemma_LAtomic_AtomicTauLeavesPCUnchanged();
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

    private void GenerateLiftLAtomicToHAtomicLemma()
    {
      var str = @"
        lemma lemma_LiftLAtomicToHAtomic() returns (refinement_relation: RefinementRelation<LPlusState, H.Armada_TotalState>)
          ensures SpecRefinesSpec(AtomicSpec(LAtomic_GetSpecFunctions()), AtomicSpec(HAtomic_GetSpecFunctions()), refinement_relation)
          ensures refinement_relation == GetLPlusHRefinementRelation()
        {
          var arr := GetAtomicReductionRequest();
          lemma_IsValidAtomicReductionRequest(arr);
          lemma_PerformAtomicReduction(arr);
          refinement_relation := GetLPlusHRefinementRelation();
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
