using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class WeakeningProofGenerator : AbstractProofGenerator
  {
    private WeakeningStrategyDecl strategy;

    public WeakeningProofGenerator(ProofGenerationParams i_pgp, WeakeningStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
    }

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();
      
      pgp.MainProof.AddImport("InvariantsModule");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddImport("util_option_s");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddImport("util_collections_seqs_s");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddImport("util_collections_seqs_i");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddImport("util_collections_sets_i");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }
      AddIncludesAndImports();

      GeneratePCFunctions_L();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofHeader();
      GenerateAtomicSpecs();
      GenerateInvariantProof(pgp);
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
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
