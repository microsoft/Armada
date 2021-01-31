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

  public abstract class VarHidingProofGenerator : AbstractProofGenerator
  {
    protected bool canHideTau;

    public VarHidingProofGenerator(ProofGenerationParams i_pgp, bool i_canHideTau)
      : base(i_pgp, true)
    {
      canHideTau = i_canHideTau;
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }

      AddIncludesAndImports();

      GenerateVarHidingPCMap();
      ExtendPCMapWithExternalAndStructsMethods();
      GenerateNextRoutineMap(false); // Don't warn on missing next routines, since some low-level routines don't map to high-level ones
      GenerateProofGivenMap();
    }

    protected void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateAtomicSpecs(false);
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateInvariantProof(pgp);
      GenerateLocalViewCommutativityLemmas();
      GenerateConvertAtomicPath_LH();
      GenerateEstablishInitRequirementsLemma();
      GenerateEstablishStateOKRequirementLemma();
      GenerateEstablishRelationRequirementLemma();
      GenerateLiftingRelation();
      GenerateLiftAtomicPathLemmas(
        "HAtomic_GetPathType(hpath) == ty",
        "requires !IsSkippedPath(ls, lpath, tid)",
        canHideTau ? "lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid);" : ""
      );
      GenerateSkippablePathsLiftableLemma();
      GenerateEstablishAtomicPathLiftableLemma();
      GenerateEstablishAtomicPathsLiftableLemma(true, false);
      GenerateLiftLAtomicToHAtomicLemma(true, false);
      GenerateFinalProof();
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
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "convert");
      pgp.AddImport("util_option_s", null, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    // PC mapping
    ////////////////////////////////////////////////////////////////////////

    protected abstract bool IsVariableHidden(string methodName, string varName);

    private bool IsHiddenStatement(string methodName, ArmadaStatement stmt)
    {
      if (stmt is ArmadaUpdateStatement aus) {
        var us = (UpdateStmt)aus.Stmt;
        return us.Lhss.All(lhs => IsVariableHidden(methodName, AH.GetLValueRootVariable(lhs)));
      }
      else if (stmt is ArmadaSomehowStatement ashs) {
        var shs = (SomehowStmt)ashs.Stmt;
        return shs.Mod.Expressions.Any() &&
               shs.Mod.Expressions.All(lhs => IsVariableHidden(methodName, AH.GetLValueRootVariable(lhs)));
      }
      else if (stmt is ArmadaVarDeclStatement avds) {
        var vds = (VarDeclStmt)avds.Stmt;
        return vds.Locals.All(v => IsVariableHidden(methodName, v.Name));
      }

      return false;
    }

    private void GenerateVarHidingPCMapForBlocks(string methodName, ArmadaStatement blockLow, ArmadaStatement blockHigh)
    {
      if (blockLow == null) {
        return;
      }

      if (blockHigh == null) {
        AH.PrintError(pgp.prog, $"No block in high level corresponding to block at {AH.TokenToString(blockLow.Stmt.Tok)} in low level.");
        return;
      }

      var pcLow = blockLow.StartPC;
      var pcHigh = blockHigh.StartPC;
      pcMap[pcLow] = pcHigh;

      var stmtsHigh = blockHigh.GetStatementsInBody().ToArray();

      int whichStmtHigh = 0;
      foreach (var stmtLow in blockLow.GetStatementsInBody()) {

        if (IsHiddenStatement(methodName, stmtLow)) {
          pcMap[stmtLow.EndPC] = pcHigh;
          continue;
        }

        if (whichStmtHigh >= stmtsHigh.Length) {
          AH.PrintError(pgp.prog, $"Could not figure out how the low-level statement at {AH.TokenToString(stmtLow.Stmt.Tok)} is a hidden-variable assignment, but it doesn't seem to correspond to any high-level statement.");
          pcMap[stmtLow.EndPC] = pcHigh;
          continue;
        }

        var stmtHigh = stmtsHigh[whichStmtHigh];
        if (stmtLow.RoughlyMatches(stmtHigh)) {
          if (stmtLow is ArmadaIfStatement ifLow) {
            var ifHigh = (ArmadaIfStatement)stmtHigh;
            GenerateVarHidingPCMapForBlocks(methodName, ifLow.ThenClause, ifHigh.ThenClause);
            GenerateVarHidingPCMapForBlocks(methodName, ifLow.ElseClause, ifHigh.ElseClause);
          }
          else if (stmtLow is ArmadaWhileStatement whileLow) {
            var whileHigh = (ArmadaWhileStatement)stmtHigh;
            GenerateVarHidingPCMapForBlocks(methodName, whileLow.Body, whileHigh.Body);
          }
        }
        else {
          AH.PrintError(pgp.prog, $"Could not figure out how the low-level statement at {AH.TokenToString(stmtLow.Stmt.Tok)} correponds to the high-level statement at {AH.TokenToString(stmtHigh.Stmt.Tok)}.");
        }

        pcHigh = stmtHigh.EndPC;
        pcMap[stmtLow.EndPC] = pcHigh;
        ++whichStmtHigh;
      }
    }

    private void GenerateVarHidingPCMapForMethod(string methodName)
    {
      if (!pgp.symbolsHigh.DoesMethodNameExist(methodName)) {
        AH.PrintError(pgp.prog, $"There's a method named {methodName} in the low level but not the high level.");
        return;
      }

      var bodyLow = pgp.symbolsLow.AllMethods.LookupMethod(methodName).ParsedBody;
      var bodyHigh = pgp.symbolsHigh.AllMethods.LookupMethod(methodName).ParsedBody;

      GenerateVarHidingPCMapForBlocks(methodName, bodyLow, bodyHigh);
    }

    private void GenerateVarHidingPCMap()
    {
      pcMap = new Dictionary<ArmadaPC, ArmadaPC>();

      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var st = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        if (!st.IsExternal && !st.IsFromStructsModule) {
          GenerateVarHidingPCMapForMethod(methodName);
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lifting lemmas
    ////////////////////////////////////////////////////////////////////////

    private bool IsSuppressedNextRoutine(NextRoutine nextRoutine)
    {
      return nextRoutine.nextType is NextType.Update && pcMap[nextRoutine.stmt.Parsed.StartPC] == pcMap[nextRoutine.stmt.Parsed.EndPC];
    }

    protected override string GetStepCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      if (IsSuppressedNextRoutine(nextRoutine)) {
        // This is the case of an update statement that gets suppressed because it only updates hidden variables.
        return GetStepCaseForSuppressedNextRoutine_LH(nextRoutine);
      }
      else {
        return GetStepCaseForNormalNextRoutine_LH(nextRoutine);
      }
    }

    private void GenerateSkippablePathsLiftableLemma()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);

      if (canHideTau) {
        str = $@"
          lemma lemma_SkippablePathLiftable_Tau(ls: LPlusState, ls': LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
            requires InductiveInv(ls)
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_Tau?
            requires IsSkippedTauPath(ls, lpath, tid)
            ensures  ConvertTotalState_LPlusH(ls) == ConvertTotalState_LPlusH(ls')
            ensures  ls'.s.stop_reason.Armada_NotStopped?
          {{
            { lpr.GetOpenValidPathInvocation(lAtomic.TauPath) }
  
            var hs := ConvertTotalState_LPlusH(ls);
            var hs' := ConvertTotalState_LPlusH(ls');
            var lentry := ls.s.threads[tid].storeBuffer[0];
            ProofCustomizationGoesHere();
            assert !CanConvertStoreBufferEntry_LH(lentry);
            assert hs'.threads[tid].storeBuffer == hs.threads[tid].storeBuffer;
            assert hs'.threads[tid] == hs.threads[tid];
            assert hs'.threads == hs.threads;
            assert hs'.stop_reason == hs.stop_reason;
            assert hs' == hs;
          }}
        ";
        pgp.AddLemma(str, "lift");
        finalCases += "    case LAtomic_Path_Tau(_) => lemma_SkippablePathLiftable_Tau(ls, ls', lpath, tid);\n";
      }
      else {
        finalCases += "    case LAtomic_Path_Tau(_) => assert false;\n";
      }

      var extraProof = canHideTau ? "lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid);" : "";

      foreach (var atomicPath in lAtomic.AtomicPaths.Where(ap => !pathMap.ContainsKey(ap))) {
        var name = atomicPath.Name;

        str = $@"
          lemma lemma_SkippablePathLiftable_{name}(ls: LPlusState, ls': LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
            requires InductiveInv(ls)
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            ensures  ConvertTotalState_LPlusH(ls) == ConvertTotalState_LPlusH(ls')
            ensures  ls'.s.stop_reason.Armada_NotStopped?
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }

            var hs := ConvertTotalState_LPlusH(ls);
            var hs' := ConvertTotalState_LPlusH(ls');
            { extraProof }
            ProofCustomizationGoesHere();
            assert hs'.stop_reason == hs.stop_reason;
            if tid in hs'.threads {{
              assert hs'.threads[tid] == hs.threads[tid];
            }}
            assert hs'.threads == hs.threads;
            assert hs'.mem == hs.mem;
            assert hs' == hs;
          }}
        ";
        pgp.AddLemma(str, "lift");
        finalCases += $"    case LAtomic_Path_{name}(_) => lemma_SkippablePathLiftable_{name}(ls, ls', lpath, tid);\n";
      }

      str = $@"
        lemma lemma_SkippablePathLiftable(ls: LPlusState, ls': LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires IsSkippedPath(ls, lpath, tid)
          ensures  ConvertTotalState_LPlusH(ls) == ConvertTotalState_LPlusH(ls')
          ensures  ls'.s.stop_reason.Armada_NotStopped?
        {{
          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    protected override void GenerateLiftAtomicPathLemmaForTauPath(AtomicPath atomicPath, string typeComparison,
                                                                  string extraSignatureLines)
    {
      if (!canHideTau) {
        base.GenerateLiftAtomicPathLemmaForTauPath(atomicPath, typeComparison, extraSignatureLines);
        return;
      }

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      string str = $@"
        lemma lemma_LiftAtomicPath_Tau(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_Tau?
          requires !IsSkippedTauPath(ls, lpath, tid)
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hpath := ConvertAtomicPath_LH(ls, lpath, tid);
                   var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
                   var ty := LAtomic_GetPathType(lpath);
                   && HAtomic_GetPathType(hpath) == ty
                   && HAtomic_ValidPath(hs, hpath, tid)
                   && hs' == ConvertTotalState_LPlusH(ls')
                   && ls'.s.stop_reason.Armada_NotStopped? == hs'.stop_reason.Armada_NotStopped?
        {{
          { lpr.GetOpenValidPathInvocation(lAtomic.TauPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          var hs := ConvertTotalState_LPlusH(ls);
          var hpath := ConvertAtomicPath_LH(ls, lpath, tid);
          var hs' := ConvertTotalState_LPlusH(ls');

          { hpr.GetOpenPathInvocation(hAtomic.TauPath) }

          var lentry := ls.s.threads[tid].storeBuffer[0];
          assert CanConvertStoreBufferEntry_LH(lentry);
          var hentry := hs.threads[tid].storeBuffer[0];
          var lmem := ls.s.mem;
          var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
          var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

          var alt_hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
          ProofCustomizationGoesHere();

          assert hs'.threads[tid] == alt_hs'.threads[tid];
          assert hs'.threads == alt_hs'.threads;
          assert hs' == alt_hs';

          /* { hpr.GetAssertValidPathInvocation(hAtomic.TauPath) } */
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    protected override void GenerateEstablishAtomicPathLiftableLemma()
    {
      string str = @"
        lemma lemma_EstablishAtomicPathLiftable(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          ) returns (
          hpath: HAtomic_Path
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires !AtomicPathSkippable(lasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs)
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
        {
          var inv := InductiveInv;
          var relation := LiftingRelation;
          var ls' := lasf.path_next(ls, lpath, tid);
          if IsSkippedPath(ls, lpath, tid) {
            lemma_SkippablePathLiftable(ls, ls', lpath, tid);
            lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);
            assert AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs);
            assert false;
          }
          else {
            var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
            lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);
            assert inv(ls');
            hpath := ConvertAtomicPath_LH(ls, lpath, tid);
            lemma_LiftAtomicPath(ls, lpath, tid);
            assert LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }

}
