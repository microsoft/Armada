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
    private ArmadaPC startPC;
    private ArmadaPC endPC;
    private ArmadaPC singlePC;

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
          pcMap[pc] = new ArmadaPC(pgp.symbolsHigh, pc.methodName, singlePC.instructionCount + 1);
        }
        else {
          pcMap[pc] = new ArmadaPC(pgp.symbolsHigh, pc.methodName, pc.instructionCount + startPC.instructionCount - endPC.instructionCount);
        }
      }

      ExtendPCMapWithExternalAndStructsMethods();
      GenerateNextRoutineMap(false);

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
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("GenericArmadaSpecModule");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");
      pgp.MainProof.AddImport("GeneralRefinementLemmasModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy", "invariants");
      pgp.AddImport("GenericArmadaLemmasModule", null, "invariants");
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateAtomicSpecs(false);
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
      GenerateGenericStoreBufferLemmas_L();

      GeneratePCFunctions_L();
      AddStackMatchesMethodInvariant();
      GenerateInvariantProof(pgp);

      GenerateLocalViewCommutativityLemmas();
      GenerateLiftingRelation();
      GenerateLiftAtomicPathLemmas();
      GenerateEstablishInitRequirementsLemma();
      GenerateEstablishStateOKRequirementLemma();
      GenerateEstablishRelationRequirementLemma();
      GenerateEstablishAtomicPathLiftableLemma();
      GenerateEstablishAtomicPathsLiftableLemma(false, false);
      GenerateLiftLAtomicToHAtomicLemma(false, false);
      GenerateFinalProof();
    }
  }
}
