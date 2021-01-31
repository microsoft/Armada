using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class RefinementProofGenerator
  {
    private Program prog;
    private ModuleDefinition mProof;
    private Resolver.ModuleBindings bindings;
    private LiteralModuleDecl mLow, mHigh;
    private ArmadaSymbolTable symbolsLow, symbolsHigh;
    private StrategyDecl strategy;

    public RefinementProofGenerator(Program i_prog, ModuleDefinition i_mProof, Resolver.ModuleBindings i_bindings)
    {
      prog = i_prog;
      mProof = i_mProof;
      bindings = i_bindings;
      mLow = null;
      mHigh = null;
      strategy = null;
    }

    private bool LookupLevel(IToken levelDescriptor, string kind, out LiteralModuleDecl m)
    {
      ModuleDecl md = null;
      m = null;

      if (!bindings.TryLookup(levelDescriptor, out md)) {
        AH.PrintError(prog, $"Could not find {kind} level {levelDescriptor} referred to in proof module {mProof.Name}");
        return false;
      }
      if (!(md is LiteralModuleDecl)) {
        AH.PrintError(prog, $"Low-level {levelDescriptor} referred to in proof module {mProof.Name} isn't a code level");
        return false;
      }
      m = (LiteralModuleDecl)md;
      return true;
    }

    private bool GetLevelsAndStrategy()
    {
      foreach (var d in mProof.TopLevelDecls) {
        if (d is RefinementParametersDecl) {
          var refinement = (RefinementParametersDecl)d;
          if (mLow != null || mHigh != null) {
            AH.PrintError(prog, $"More than one 'refinement' declaration found in proof module {mProof.Name}");
            return false;
          }
          if (!LookupLevel(refinement.LowLevel, "low-level", out mLow)) {
            return false;
          }
          if (!LookupLevel(refinement.HighLevel, "high-level", out mHigh)) {
            return false;
          }
        }
        else if (d is StrategyDecl) {
          if (strategy != null) {
            AH.PrintError(prog, $"More than one strategy found in proof module {mProof.Name}");
            return false;
          }
          strategy = (StrategyDecl)d;
        }
      }

      if (mLow == null || mHigh == null) {
        AH.PrintError(prog, $"No 'refinement' declaration found in proof module {mProof.Name}");
        return false;
      }
      if (strategy == null) {
        AH.PrintError(prog, $"No strategy given in proof module {mProof.Name}");
        return false;
      }

      symbolsLow = mLow.ModuleDef.ArmadaSymbols;
      symbolsHigh = mHigh.ModuleDef.ArmadaSymbols;

      return true;
    }

    public void GenerateProof()
    {
      if (!GetLevelsAndStrategy()) {
        return;
      }

      ProofGenerationParams pgp = new ProofGenerationParams(prog, mProof, mLow, mHigh);
      AbstractProofGenerator pg = null;
      if (strategy is GlobalVariableHidingStrategyDecl gvhsd) {
        pg = new GlobalVarHidingProofGenerator(pgp, gvhsd);
      }
      else if (strategy is StackVariableHidingStrategyDecl svhsd) {
        pg = new StackVarHidingProofGenerator(pgp, svhsd);
      }
      else if (strategy is GlobalVariableIntroStrategyDecl gvisd) {
        pg = new GlobalVarIntroProofGenerator(pgp, gvisd);
      }
      else if (strategy is StackVariableIntroStrategyDecl svisd) {
        pg = new StackVarIntroProofGenerator(pgp, svisd);
      }
      else if (strategy is AssumeIntroStrategyDecl aisd) {
        pg = new AssumeIntroProofGenerator(pgp, aisd);
      }
      else if (strategy is TSOEliminationStrategyDecl tesd) {
        pg = new TSOEliminationProofGenerator(pgp, tesd);
      }
      else if (strategy is ReductionStrategyDecl rsd) {
        pg = new ReductionProofGenerator(pgp, rsd);
      }
      else if (strategy is WeakeningStrategyDecl wsd) {
        pg = new WeakeningProofGenerator(pgp, wsd);
      }
      else if (strategy is StarWeakeningStrategyDecl swsd) {
        pg = new StarWeakeningProofGenerator(pgp, swsd);
      }
      else if (strategy is CombiningStrategyDecl csd) {
        pg = new CombiningProofGenerator(pgp, csd);
      }

      if (pg != null) {
        pg.GenerateProof();
        pgp.proofFiles.Print();
      }
    }
  }

}
