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
      if (strategy is StackVariableHidingStrategyDecl) {
        pg = new StackVarHidingProofGenerator(pgp, (StackVariableHidingStrategyDecl)strategy);
      }
      else if (strategy is VariableHidingStrategyDecl) {
        pg = new VarHidingProofGenerator(pgp, (VariableHidingStrategyDecl)strategy);
      }
      else if (strategy is StackVariableIntroStrategyDecl) {
        pg = new StackVarIntroProofGenerator(pgp, (StackVariableIntroStrategyDecl)strategy);
      }
      else if (strategy is VariableIntroStrategyDecl) {
        pg = new VarIntroProofGenerator(pgp, (VariableIntroStrategyDecl)strategy);
      }
      else if (strategy is AssumeIntroStrategyDecl) {
        pg = new AssumeIntroProofGenerator(pgp, (AssumeIntroStrategyDecl)strategy);
      }
      else if (strategy is TSOEliminationStrategyDecl) {
        pg = new TSOEliminationProofGenerator(pgp, (TSOEliminationStrategyDecl)strategy);
      }
      else if (strategy is ReductionStrategyDecl) {
        pg = new ReductionProofGenerator(pgp, (ReductionStrategyDecl)strategy);
      }
      else if (strategy is WeakeningStrategyDecl) {
        pg = new WeakeningProofGenerator(pgp, (WeakeningStrategyDecl)strategy);
      }
      else if (strategy is StarWeakeningStrategyDecl) {
        pg = new StarWeakeningProofGenerator(pgp, (StarWeakeningStrategyDecl)strategy);
      }
      else if (strategy is CombiningStrategyDecl) {
        pg = new CombiningProofGenerator(pgp, (CombiningStrategyDecl)strategy);
      }

      if (pg != null) {
        pg.GenerateProof();
        pgp.proofFiles.Print();
      }
    }
  }

}
