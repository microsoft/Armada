using System.Collections.Generic;
using System.Linq;
using System;

namespace Microsoft.Armada
{
  public abstract class VarIntroProofGenerator : AbstractProofGenerator
  {
    protected bool canIntroduceTau;
    protected Dictionary<ArmadaPC, ArmadaPC> reversePCMap;
    protected Dictionary<NextRoutine, NextRoutine> reverseNextRoutineMap;
    protected Dictionary<AtomicPath, AtomicPath> reverseAtomicPathMap;
    protected Dictionary<ArmadaPC, List<AtomicPath>> pcToIntroducedPaths;

    public VarIntroProofGenerator(ProofGenerationParams i_pgp, bool i_canIntroduceTau) : base(i_pgp)
    {
      canIntroduceTau = i_canIntroduceTau;
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-introduction strategy");
        return;
      }

      GenerateVarIntroReversePCMap();
      GeneratePCMapFromReversePCMap();

      if (!CheckAllIntroducedAreUpdates()) {
        AH.PrintError(pgp.prog, "Higher level introduced non-update instructions, which is not supported");
        return;
      }

      AddIncludesAndImports();
      GenerateNextRoutineMap();
      GenerateReverseNextRoutineMap();

      GenerateProofGivenMap();
    }

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/MapSum.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");
      pgp.MainProof.AddImport("util_collections_MapSum_i");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "convert");
      pgp.AddImport("util_option_s", null, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    // PC mapping
    ////////////////////////////////////////////////////////////////////////

    protected abstract bool IsIntroducedVariable(string methodName, string varName);

    private bool IsIntroducedStatement(string methodName, ArmadaStatement stmt)
    {
      if (stmt is ArmadaUpdateStatement aus) {
        var us = (UpdateStmt)aus.Stmt;
        return us.Lhss.All(lhs => IsIntroducedVariable(methodName, AH.GetLValueRootVariable(lhs)));
      }
      else if (stmt is ArmadaSomehowStatement ashs) {
        var shs = (SomehowStmt)ashs.Stmt;
        return shs.Mod.Expressions.Any() && shs.Mod.Expressions.All(lhs => IsIntroducedVariable(methodName, AH.GetLValueRootVariable(lhs)));
      }
      else if (stmt is ArmadaVarDeclStatement avds) {
        var vds = (VarDeclStmt)avds.Stmt;
        return vds.Locals.All(v => IsIntroducedVariable(methodName, v.Name));
      }

      return false;
    }

    private void GenerateVarIntroReversePCMapForBlocks(string methodName, ArmadaStatement blockLow, ArmadaStatement blockHigh)
    {
      if (blockHigh == null) {
        return;
      }

      if (blockLow == null) {
        AH.PrintError(pgp.prog, $"No block in low level corresponding to block at {AH.TokenToString(blockHigh.Stmt.Tok)} in high level.");
        return;
      }

      var pcLow = blockLow.StartPC;
      var pcHigh = blockHigh.StartPC;
      reversePCMap[pcHigh] = pcLow;

      var stmtsLow = blockLow.GetStatementsInBody().ToArray();

      int whichStmtLow = 0;
      foreach (var stmtHigh in blockHigh.GetStatementsInBody()) {

        if (IsIntroducedStatement(methodName, stmtHigh)) {
          reversePCMap[stmtHigh.EndPC] = pcLow;
          continue;
        }

        if (whichStmtLow >= stmtsLow.Length) {
          AH.PrintError(pgp.prog, $"Could not figure out how the high-level statement at {AH.TokenToString(stmtHigh.Stmt.Tok)} is an introduced-variable assignment, but it doesn't seem to correspond to any low-level statement.");
          reversePCMap[stmtHigh.EndPC] = pcLow;
          continue;
        }

        var stmtLow = stmtsLow[whichStmtLow];
        if (stmtLow.RoughlyMatches(stmtHigh)) {
          if (stmtLow is ArmadaIfStatement ifLow) {
            var ifHigh = (ArmadaIfStatement)stmtHigh;
            GenerateVarIntroReversePCMapForBlocks(methodName, ifLow.ThenClause, ifHigh.ThenClause);
            GenerateVarIntroReversePCMapForBlocks(methodName, ifLow.ElseClause, ifHigh.ElseClause);
          }
          else if (stmtLow is ArmadaWhileStatement whileLow) {
            var whileHigh = (ArmadaWhileStatement)stmtHigh;
            GenerateVarIntroReversePCMapForBlocks(methodName, whileLow.Body, whileHigh.Body);
          }
        }
        else {
          AH.PrintError(pgp.prog, $"Could not figure out how the low-level statement at {AH.TokenToString(stmtLow.Stmt.Tok)} correponds to the high-level statement at {AH.TokenToString(stmtHigh.Stmt.Tok)}.");
        }

        pcLow = stmtLow.EndPC;
        reversePCMap[stmtHigh.EndPC] = pcLow;
        ++whichStmtLow;
      }
    }

    private void GenerateVarIntroReversePCMapForMethod(string methodName)
    {
      if (!pgp.symbolsLow.DoesMethodNameExist(methodName)) {
        AH.PrintError(pgp.prog, $"There's a method named {methodName} in the high level but not the low level.");
        return;
      }

      var bodyLow = pgp.symbolsLow.AllMethods.LookupMethod(methodName).ParsedBody;
      var bodyHigh = pgp.symbolsHigh.AllMethods.LookupMethod(methodName).ParsedBody;

      GenerateVarIntroReversePCMapForBlocks(methodName, bodyLow, bodyHigh);
    }

    private void GenerateVarIntroReversePCMap()
    {
      reversePCMap = new Dictionary<ArmadaPC, ArmadaPC>();

      foreach (var methodName in pgp.symbolsHigh.MethodNames) {
        var st = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
        if (st.IsExternal || st.IsFromStructsModule) {
          List<ArmadaPC> allPCs = new List<ArmadaPC>();
          pgp.symbolsHigh.AllMethods.LookupMethod(methodName).AppendAllPCs(allPCs);
          foreach (var pc in allPCs) {
            reversePCMap[pc] = pc.CloneWithNewSymbolTable(pgp.symbolsLow);
          }
        }
        else {
          GenerateVarIntroReversePCMapForMethod(methodName);
        }
      }
    }

    private void GeneratePCMapFromReversePCMap()
    {
      pcMap = new Dictionary<ArmadaPC, ArmadaPC>();

      foreach (var entry in reversePCMap) {
        if (!pcMap.ContainsKey(entry.Value)) {
          pcMap[entry.Value] = entry.Key;
        }
      }
    }

    private ArmadaPC LowerPC(ArmadaPC pc)
    {
      if (pc == null) {
        return null;
      }
      return reversePCMap[pc];
    }

    protected override void GenerateNextRoutineMap(bool warnOnMissingRoutines = true)
    {
      nextRoutineMap = new Dictionary<NextRoutine, NextRoutine>();
      var hmap = new Dictionary<Tuple<ArmadaPC, ArmadaPC, bool, bool>, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        var startPC = LowerPC(nextRoutine.startPC);
        var endPC = LowerPC(nextRoutine.endPC);
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(startPC, endPC, nextRoutine.UndefinedBehavior,
                                                          nextRoutine.BranchOutcome);

        // If more than one high-level next routine maps to the same low-level startPC/endPC combination,
        // use the one earlier in its method.
        
        if (!hmap.ContainsKey(t) || nextRoutine.startPC.instructionCount < hmap[t].startPC.instructionCount) {
          hmap[t] = nextRoutine;
        }
      }

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(nextRoutine.startPC, nextRoutine.endPC, nextRoutine.UndefinedBehavior,
                                                          nextRoutine.BranchOutcome);
        if (hmap.ContainsKey(t)) {
          nextRoutineMap[nextRoutine] = hmap[t];
        }
        else if (warnOnMissingRoutines) {
          AH.PrintWarning(pgp.prog, $"No next routine found in high level from {nextRoutine.startPC} to {nextRoutine.endPC}");
        }
      }
    }

    protected void GenerateReverseNextRoutineMap()
    {
      reverseNextRoutineMap = new Dictionary<NextRoutine, NextRoutine>();
      var hmap = new Dictionary<Tuple<ArmadaPC, ArmadaPC, bool, bool>, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(nextRoutine.startPC, nextRoutine.endPC, nextRoutine.UndefinedBehavior,
                                                          nextRoutine.BranchOutcome);
        if (hmap.ContainsKey(t)) {
          AH.PrintError(pgp.prog,
                        $"More than one next routine from PC {nextRoutine.startPC} to {nextRoutine.endPC} in level {pgp.mLow.Name}");
          hmap.Remove(t);
        }
        else {
          hmap[t] = nextRoutine;
        }
      }

      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        var startPC = LowerPC(nextRoutine.startPC);
        var endPC = LowerPC(nextRoutine.endPC);
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(startPC, endPC, nextRoutine.UndefinedBehavior, nextRoutine.BranchOutcome);
        if (hmap.ContainsKey(t)) {
          reverseNextRoutineMap[nextRoutine] = hmap[t];
        }
      }
    }

    protected void GenerateReverseAtomicPathMap()
    {
      reverseAtomicPathMap = hAtomic.CreatePathMap(lAtomic, reverseNextRoutineMap);
    }

    protected void RegenerateAtomicPathMap()
    {
      pathMap = new Dictionary<AtomicPath, AtomicPath>();
      foreach (var entry in reverseAtomicPathMap)
      {
        pathMap[entry.Value] = entry.Key;
      }
    }

    protected void GeneratePCToIntroducedPathsMap()
    {
      pcToIntroducedPaths = new Dictionary<ArmadaPC, List<AtomicPath>>();

      foreach (var hAtomicPath in hAtomic.AtomicPaths.Where(ap => !ap.Tau && !reverseAtomicPathMap.ContainsKey(ap) &&
                                                                  ap.StartType == ap.EndType && !ap.Stopping))
      {
        var startPC = LowerPC(hAtomicPath.StartPC);
        if (pcToIntroducedPaths.ContainsKey(startPC)) {
          pcToIntroducedPaths[startPC].Add(hAtomicPath);
        }
        else {
          pcToIntroducedPaths[startPC] = new List<AtomicPath>{ hAtomicPath };
        }
      }
    }

    protected bool CheckAllIntroducedAreUpdates() {
      foreach (var routine in pgp.symbolsHigh.NextRoutines) {
        if (routine.nextType != NextType.Update && routine.startPC != routine.endPC && routine.endPC != null && LowerPC(routine.startPC) == LowerPC(routine.endPC)) {
          AH.PrintError(pgp.prog, routine.armadaStatement.Stmt.Tok, $"Can't introduce non-assignment statement");
          return false;
        }
      }
      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    // Proof
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateProofGivenMap() {
      GenerateProofHeader();
      GenerateAtomicSpecs();
      GenerateReverseAtomicPathMap();
      RegenerateAtomicPathMap();
      GeneratePCToIntroducedPathsMap();

      // the state conversion functions are required from H to L
      GenerateStateAbstractionFunctions_HL(reversePCMap);
      // the step conversion functions are required from L to H

      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
      GeneratePCFunctions_H();
      GenerateIsReturnSite_H();
      GenerateLiftingRelation();
      if (canIntroduceTau) {
        GenerateCanIntroduceTau();
      }
      GenerateProgressMeasure();

      // lemma generation

      lAtomic.GeneratePCEffectLemmas();
      GenerateInvariantProof(pgp);
      GenerateLocalViewCommutativityLemmas();
      GenerateEstablishInitRequirementsLemma();
      GenerateEstablishStateOKRequirementLemma();
      GenerateEstablishRelationRequirementLemma();
      GenerateIntroduceOrLiftAtomicPathLemmas();
      GenerateEstablishAtomicPathsLiftableLemma(false, true);
      GenerateLiftLAtomicToHAtomicLemma(false, true);
      GenerateFinalProof();
    }

    ////////////////////////////////////////////////////////////////////////
    // Abstraction
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateConvertAtomicPath_LH()
    {
      string str = @"
        function ConvertAtomicPath_LH(lpath: LAtomic_Path) : HAtomic_Path
        {
          match lpath
      ";
      foreach (var entry in pathMap)
      {
        var lPath = entry.Key;
        var hPath = entry.Value;

        var steps = new List<string>();
        var numLNextRoutinesUsed = 0;
        for (int i = 0; i < hPath.NumNextRoutines; ++i) {
          var hNextRoutine = hPath.NextRoutines[i];
          if (reverseNextRoutineMap.ContainsKey(hNextRoutine)) {
            steps.Add($"ConvertStep_LH(steps.step{numLNextRoutinesUsed})");
            ++numLNextRoutinesUsed;
          }
          else {
            if (hNextRoutine.HasFormals) {
              // TODO: this does not work with introduced statements with *
              AH.PrintError(pgp.prog, "The variable-introduction proof generator doesn't support introducing a non-deterministic statement.");
            }
            steps.Add($"H.Armada_Step_{hNextRoutine.NameSuffix}()");
          }
        }

        str += $"case LAtomic_Path_{lPath.Name}(steps) => HAtomic_Path_{hPath.Name}(HAtomic_PathSteps_{hPath.Name}(";
        str += String.Join(", ", steps);
        str += "))\n";
      }
      str += "}\n";
      pgp.AddFunction(str, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    // Commutativity lemmas
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateLocalViewCommutativityLemmas()
    {
      string str;

      string cases = "";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(varName);
        if (globalVar is AddressableArmadaVariable || globalVar.NoTSO()) {
          continue;
        }
        cases += $"case Armada_GlobalStaticVar_{varName} => {{ }}\n";
      }

      var extraRequires = canIntroduceTau ? "requires CanConvertGlobalStaticVar_HL(lv)" : "";
      str = $@"
        lemma lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(
          lglobals:H.Armada_Globals, lv:H.Armada_GlobalStaticVar, fields:seq<int>, value:Armada_PrimitiveValue,
          hv:L.Armada_GlobalStaticVar, hglobals1:L.Armada_Globals, hglobals2:L.Armada_Globals)
          { extraRequires }
          requires hv == ConvertGlobalStaticVar_HL(lv)
          requires hglobals1 == ConvertGlobals_HL(H.Armada_ApplyTauUnaddressable(lglobals, lv, fields, value))
          requires hglobals2 == L.Armada_ApplyTauUnaddressable(ConvertGlobals_HL(lglobals), hv, fields, value)
          ensures  hglobals1 == hglobals2
        {{
          match lv
            case Armada_GlobalStaticVarNone =>
            {{
              var hglobals := ConvertGlobals_HL(lglobals);
              assert hglobals1 == hglobals == hglobals2;
            }}
            { cases }
        }}
      ";
      pgp.AddLemma(str, "utility");

      if (canIntroduceTau) {
        str = @"
          lemma lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(
            lmem:H.Armada_SharedMemory,
            lentry:H.Armada_StoreBufferEntry
            )
            requires !CanConvertStoreBufferEntry_HL(lentry)
            ensures  ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lentry)) == ConvertSharedMemory_HL(lmem)
          {
          }
        ";
        pgp.AddLemma(str, "utility");
      }

      extraRequires = canIntroduceTau ? "requires CanConvertStoreBufferEntry_HL(lentry)" : "";
      str = $@"
        lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem:H.Armada_SharedMemory, lentry:H.Armada_StoreBufferEntry,
                                                             hentry:L.Armada_StoreBufferEntry, hmem1:L.Armada_SharedMemory,
                                                             hmem2:L.Armada_SharedMemory)
          { extraRequires }
          requires hentry == ConvertStoreBufferEntry_HL(lentry)
          requires hmem1 == ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lentry))
          requires hmem2 == L.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_HL(lmem), hentry)
          ensures  hmem1 == hmem2
        {{
          match lentry.loc
            case Armada_StoreBufferLocation_Unaddressable(lv, lfields) =>
            {{
              var hv := ConvertGlobalStaticVar_HL(lv);
              lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(lmem.globals, lv, lfields, lentry.value, hv, hmem1.globals,
                                                                          hmem2.globals);
            }}
            case Armada_StoreBufferLocation_Addressable(p) =>
            {{
            }}
        }}
      ";
      pgp.AddLemma(str, "utility");

      var mainProof = @"
        var hmem1' := ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
        var hmem2' := L.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_HL(lmem), hbuf[0]);
        lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
        lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
      ";
      if (canIntroduceTau) {
        mainProof = $@"
          if CanConvertStoreBufferEntry_HL(lbuf[0]) {{
            { mainProof }
          }}
          else {{
            lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem, lbuf[0]);
            assert ConvertSharedMemory_HL(lmem') == ConvertSharedMemory_HL(lmem);
            assert hbuf == ConvertStoreBuffer_HL(lbuf[1..]);
            lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf, hmem1, hmem2);
          }}
        ";
      }

      str = $@"
        lemma lemma_ApplyStoreBufferCommutesWithConvert(lmem:H.Armada_SharedMemory, lbuf:seq<H.Armada_StoreBufferEntry>,
                                                        hbuf:seq<L.Armada_StoreBufferEntry>, hmem1:L.Armada_SharedMemory,
                                                        hmem2:L.Armada_SharedMemory)
          requires hbuf == ConvertStoreBuffer_HL(lbuf)
          requires hmem1 == ConvertSharedMemory_HL(H.Armada_ApplyStoreBuffer(lmem, lbuf))
          requires hmem2 == L.Armada_ApplyStoreBuffer(ConvertSharedMemory_HL(lmem), hbuf)
          ensures  hmem1 == hmem2
          decreases |lbuf| + |hbuf|
        {{
          if |lbuf| == 0 {{
            return;
          }}

          var lmem' := H.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]);

          { mainProof }
        }}
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_GetThreadLocalViewCommutesWithConvert(ls:HState, hs:LState, tid:Armada_ThreadHandle)
          requires hs == ConvertTotalState_HL(ls)
          requires tid in ls.threads;
          ensures  ConvertSharedMemory_HL(H.Armada_GetThreadLocalView(ls, tid)) == L.Armada_GetThreadLocalView(hs, tid)
        {
          assert tid in hs.threads;
          lemma_ApplyStoreBufferCommutesWithConvert(ls.mem, ls.threads[tid].storeBuffer,
                                                    hs.threads[tid].storeBuffer,
                                                    ConvertSharedMemory_HL(H.Armada_GetThreadLocalView(ls, tid)),
                                                    L.Armada_GetThreadLocalView(hs, tid));
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_GetThreadLocalViewAlwaysCommutesWithConvert()
          ensures forall ls:H.Armada_TotalState, tid:Armada_ThreadHandle :: tid in ls.threads ==>
                    ConvertSharedMemory_HL(H.Armada_GetThreadLocalView(ls, tid)) ==
                    L.Armada_GetThreadLocalView(ConvertTotalState_HL(ls), tid)
        {
          forall ls:H.Armada_TotalState, tid:Armada_ThreadHandle | tid in ls.threads
            ensures ConvertSharedMemory_HL(H.Armada_GetThreadLocalView(ls, tid)) ==
                    L.Armada_GetThreadLocalView(ConvertTotalState_HL(ls), tid)
          {
            var hs := ConvertTotalState_HL(ls);
            lemma_GetThreadLocalViewCommutesWithConvert(ls, hs, tid);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      if (canIntroduceTau) {
        str = @"
          lemma lemma_StoreBufferAppendConversion(buf: seq<H.Armada_StoreBufferEntry>, entry: H.Armada_StoreBufferEntry)
            ensures  ConvertStoreBuffer_HL(buf + [entry]) ==
                       if CanConvertStoreBufferEntry_HL(entry) then
                         ConvertStoreBuffer_HL(buf) + [ConvertStoreBufferEntry_HL(entry)]
                       else
                         ConvertStoreBuffer_HL(buf)
          {
            assert [entry][1..] == [];
  
            if |buf| == 0 {
              assert buf + [entry] == [entry];
              assert ConvertStoreBuffer_HL(buf + [entry]) == ConvertStoreBuffer_HL([entry]);
              assert ConvertStoreBuffer_HL(buf) == [];
  
              if CanConvertStoreBufferEntry_HL(entry) {
                calc {
                    ConvertStoreBuffer_HL([entry]);
                    [ConvertStoreBufferEntry_HL(entry)] + ConvertStoreBuffer_HL([entry][1..]);
                    [ConvertStoreBufferEntry_HL(entry)] + ConvertStoreBuffer_HL([]);
                    [ConvertStoreBufferEntry_HL(entry)] + [];
                    [ConvertStoreBufferEntry_HL(entry)];
                }
              }
              else {
                calc {
                    ConvertStoreBuffer_HL([entry]);
                    ConvertStoreBuffer_HL([entry][1..]);
                    ConvertStoreBuffer_HL([]);
                    [];
                }
              }
            }
            else {
              calc {
                ConvertStoreBuffer_HL(buf + [entry]);
                {
                  assert buf == [buf[0]] + buf[1..];
                }
                ConvertStoreBuffer_HL([buf[0]] + buf[1..] + [entry]);
                {
                  assert [buf[0]] + buf[1..] + [entry] == [buf[0]] + (buf[1..] + [entry]);
                }
                ConvertStoreBuffer_HL([buf[0]] + (buf[1..] + [entry]));
              }
              if CanConvertStoreBufferEntry_HL(buf[0]) {
                calc {
                  ConvertStoreBuffer_HL(buf + [entry]);
                  ConvertStoreBuffer_HL([buf[0]] + (buf[1..] + [entry]));
                  [ConvertStoreBufferEntry_HL(buf[0])] + ConvertStoreBuffer_HL(buf[1..] + [entry]);
                }
                lemma_StoreBufferAppendConversion(buf[1..], entry);
                if CanConvertStoreBufferEntry_HL(entry) {
                  calc {
                    ConvertStoreBuffer_HL(buf + [entry]);
                    [ConvertStoreBufferEntry_HL(buf[0])] + (ConvertStoreBuffer_HL(buf[1..]) + [ConvertStoreBufferEntry_HL(entry)]);
                    [ConvertStoreBufferEntry_HL(buf[0])] + ConvertStoreBuffer_HL(buf[1..]) + [ConvertStoreBufferEntry_HL(entry)];
                    ConvertStoreBuffer_HL(buf) + [ConvertStoreBufferEntry_HL(entry)];
                  }
                }
                else {
                  calc {
                    ConvertStoreBuffer_HL(buf + [entry]);
                    [ConvertStoreBufferEntry_HL(buf[0])] + ConvertStoreBuffer_HL(buf[1..]);
                    ConvertStoreBuffer_HL(buf);
                  }
                }
              }
              else {
                assert ConvertStoreBuffer_HL(buf) == ConvertStoreBuffer_HL(buf[1..]);
                calc {
                  ConvertStoreBuffer_HL(buf + [entry]);
                  ConvertStoreBuffer_HL([buf[0]] + (buf[1..] + [entry]));
                  ConvertStoreBuffer_HL((buf[1..] + [entry]));
                }
                lemma_StoreBufferAppendConversion(buf[1..], entry);
                if CanConvertStoreBufferEntry_HL(entry) {
                  calc {
                    ConvertStoreBuffer_HL(buf + [entry]);
                    ConvertStoreBuffer_HL(buf[1..]) + [ConvertStoreBufferEntry_HL(entry)];
                    ConvertStoreBuffer_HL(buf) + [ConvertStoreBufferEntry_HL(entry)];
                  }
                }
                else {
                  calc {
                    ConvertStoreBuffer_HL(buf + [entry]);
                    ConvertStoreBuffer_HL(buf[1..]);
                    ConvertStoreBuffer_HL(buf);
                  }
                }
              }
            }
          }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry
            {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)} ::
            CanConvertStoreBufferEntry_HL(lentry) ==>
            L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) ==
            ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry
            {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)}
            | CanConvertStoreBufferEntry_HL(lentry)
            ensures L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) ==
                    ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_ConvertStoreBufferCommutesOverBeheadment(buf:seq<H.Armada_StoreBufferEntry>)
            requires |buf| > 0
            requires CanConvertStoreBufferEntry_HL(buf[0])
            ensures  ConvertStoreBuffer_HL(buf[1..]) == ConvertStoreBuffer_HL(buf)[1..]
          {
            var hbuf1 := ConvertStoreBuffer_HL(buf[1..]);
            var hbuf2 := ConvertStoreBuffer_HL(buf)[1..];
            assert |hbuf1| == |hbuf2|;

            forall i | 0 <= i < |buf| - 1
              ensures hbuf1[i] == hbuf2[i]
            {
            }

            assert hbuf1 == hbuf2;
          }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectLowLevel(tid:Armada_ThreadHandle)
            ensures forall s:H.Armada_TotalState, entry:H.Armada_StoreBufferEntry
                      {:trigger H.Armada_AppendToThreadStoreBuffer(s, tid, entry)} ::
                      tid in s.threads && !CanConvertStoreBufferEntry_HL(entry) ==>
                      ConvertTotalState_HL(H.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_HL(s)
          {
            forall s:H.Armada_TotalState, entry:H.Armada_StoreBufferEntry {:trigger H.Armada_AppendToThreadStoreBuffer(s, tid, entry)} |
              tid in s.threads && !CanConvertStoreBufferEntry_HL(entry)
              ensures ConvertTotalState_HL(H.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_HL(s)
            {
              var hs := ConvertTotalState_HL(s);
              var hs' := ConvertTotalState_HL(H.Armada_AppendToThreadStoreBuffer(s, tid, entry));
              lemma_StoreBufferAppendConversion(s.threads[tid].storeBuffer, entry);
              assert hs.threads[tid].storeBuffer == hs'.threads[tid].storeBuffer;
              assert hs.threads == hs'.threads;
              assert hs == hs';
            }
          }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_IfLStoreBufferEmptyAndCantIntroduceTauThenHStoreBufferEmpty(
            ls: LState,
            hs: HState,
            tid: Armada_ThreadHandle
            )
            requires ls == ConvertTotalState_HL(hs)
            requires tid in ls.threads
            requires |ls.threads[tid].storeBuffer| == 0
            requires !CanIntroduceTau(hs, tid)
            ensures  tid in hs.threads
            ensures  |hs.threads[tid].storeBuffer| == 0
          {
            assert tid in hs.threads;
            var lsb := ls.threads[tid].storeBuffer;
            var hsb := hs.threads[tid].storeBuffer;
            if |hsb| == 0 {
              return;
            }
            assert CanConvertStoreBufferEntry_HL(hsb[0]);
            assert lsb == ConvertStoreBuffer_HL(hsb);
            calc {
              lsb;
              FilterMapSeqToSeq(hsb, ConvertStoreBufferEntryTotal_HL);
              [ ConvertStoreBufferEntry_HL(hsb[0]) ] + FilterMapSeqToSeq(hsb[1..], ConvertStoreBufferEntryTotal_HL);
            }
            assert |lsb| > 0;
            assert false;
          }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_AlwaysIfLStoreBufferEmptyAndCantIntroduceTauThenHStoreBufferEmpty()
            ensures forall ls: LPlusState, hs: HState, tid: Armada_ThreadHandle
                      {:trigger LiftingRelation(ls, hs), CanIntroduceTau(hs, tid)} ::
                      && LiftingRelation(ls, hs)
                      && tid in ls.s.threads
                      && |ls.s.threads[tid].storeBuffer| == 0
                      && !CanIntroduceTau(hs, tid)
                      ==> tid in hs.threads &&  |hs.threads[tid].storeBuffer| == 0
          {
            forall ls: LPlusState, hs: HState, tid: Armada_ThreadHandle
              {:trigger LiftingRelation(ls, hs), CanIntroduceTau(hs, tid)} |
              && LiftingRelation(ls, hs)
              && tid in ls.s.threads
              && |ls.s.threads[tid].storeBuffer| == 0
              && !CanIntroduceTau(hs, tid)
              ensures tid in hs.threads
              ensures |hs.threads[tid].storeBuffer| == 0
            {
              lemma_IfLStoreBufferEmptyAndCantIntroduceTauThenHStoreBufferEmpty(ls.s, hs, tid);
            }
          }
        ";
        pgp.AddLemma(str, "utility");
      }
      else {
        str = @"
          lemma lemma_StoreBufferAppendConversion(buf: seq<H.Armada_StoreBufferEntry>, entry: H.Armada_StoreBufferEntry)
            ensures  ConvertStoreBuffer_HL(buf + [entry]) == ConvertStoreBuffer_HL(buf) + [ConvertStoreBufferEntry_HL(entry)]
          {
            assert [entry][1..] == [];
  
            if |buf| == 0 {
              assert buf + [entry] == [entry];
              assert ConvertStoreBuffer_HL(buf + [entry]) == ConvertStoreBuffer_HL([entry]);
              assert ConvertStoreBuffer_HL(buf) == [];
  
              calc {
                ConvertStoreBuffer_HL([entry]);
                [ConvertStoreBufferEntry_HL(entry)] + ConvertStoreBuffer_HL([entry][1..]);
                [ConvertStoreBufferEntry_HL(entry)] + ConvertStoreBuffer_HL([]);
                [ConvertStoreBufferEntry_HL(entry)] + [];
                [ConvertStoreBufferEntry_HL(entry)];
              }
            }
            else {
              calc {
                ConvertStoreBuffer_HL(buf + [entry]);
                {
                  assert buf == [buf[0]] + buf[1..];
                }
                ConvertStoreBuffer_HL([buf[0]] + buf[1..] + [entry]);
                {
                  assert [buf[0]] + buf[1..] + [entry] == [buf[0]] + (buf[1..] + [entry]);
                }
                ConvertStoreBuffer_HL([buf[0]] + (buf[1..] + [entry]));
              }
              calc {
                ConvertStoreBuffer_HL(buf + [entry]);
                ConvertStoreBuffer_HL([buf[0]] + (buf[1..] + [entry]));
                [ConvertStoreBufferEntry_HL(buf[0])] + ConvertStoreBuffer_HL(buf[1..] + [entry]);
              }
              lemma_StoreBufferAppendConversion(buf[1..], entry);
              calc {
                ConvertStoreBuffer_HL(buf + [entry]);
                [ConvertStoreBufferEntry_HL(buf[0])] + (ConvertStoreBuffer_HL(buf[1..]) + [ConvertStoreBufferEntry_HL(entry)]);
                [ConvertStoreBufferEntry_HL(buf[0])] + ConvertStoreBuffer_HL(buf[1..]) + [ConvertStoreBufferEntry_HL(entry)];
                ConvertStoreBuffer_HL(buf) + [ConvertStoreBufferEntry_HL(entry)];
              }
            }
          }
        ";
        pgp.AddLemma(str, "utility");

        str = @"
          lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry
            {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)} ::
            L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) ==
            ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry
            {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)}
            ensures L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) ==
                    ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
        ";
        pgp.AddLemma(str, "utility");
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // VarIntro-specific functions
    ////////////////////////////////////////////////////////////////////////

    private void GenerateCanIntroduceTau()
    {
      string str = @"
        predicate CanIntroduceTau(hs: HState, tid: Armada_ThreadHandle)
        {
          && tid in hs.threads
          && |hs.threads[tid].storeBuffer| > 0
          && !CanConvertStoreBufferEntry_HL(hs.threads[tid].storeBuffer[0])
        }
      ";

      pgp.AddPredicate(str, "utility");
    }

    private void GenerateProgressMeasure()
    {
      string secondProgressElement = canIntroduceTau ? "|t.storeBuffer|" : "0";

      string str = $@"
        function ProgressMeasure(hs: HState, lpath: LAtomic_Path, tid: Armada_ThreadHandle) : (v:(int, int))
          ensures v.0 >= 0
          ensures v.1 >= 0
        {{
          if tid in hs.threads then
            var t := hs.threads[tid];
            (MaxPCInstructionCount_H() - PCToInstructionCount_H(t.pc), {secondProgressElement})
          else
            (0, 0)
        }}
      ";
      pgp.AddFunction(str, "utility");
    }

    private void GenerateIsReturnSite_H()
    {
      string body = String.Join(" || ",
                                pgp.symbolsHigh.NextRoutines
                                .Where(r => r.nextType == NextType.Return)
                                .Select(r => r.endPC)
                                .Distinct()
                                .Select(pc => $"pc.{pc}?"));
      if (body.Length == 0) { body = "false"; }

      string str = "predicate IsReturnSite_H(pc:H.Armada_PC) { " + body + "}";
      pgp.AddPredicate(str, "defs");
    }

    protected override void GenerateLiftingRelation()
    {
      string str;

      str = @"
        predicate VarIntroThreadInvariant(hs: HState, tid: Armada_ThreadHandle)
          requires tid in hs.threads
        {
          var t := hs.threads[tid];
          var pc := t.pc;
          && StackMatchesMethod_H(t.top, PCToMethod_H(pc))
          && (forall eframe :: eframe in t.stack ==> IsReturnSite_H(eframe.return_pc))
          && (!hs.stop_reason.Armada_NotStopped? || !H.Armada_IsNonyieldingPC(pc) || HAtomic_IsRecurrentPC(pc))
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate LiftingRelation(ls: LPlusState, hs: HState)
        {
          && ls.s == ConvertTotalState_HL(hs)
          && (forall tid :: tid in hs.threads ==> VarIntroThreadInvariant(hs, tid))
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    protected override void GenerateEstablishInitRequirementsLemma()
    {
      string str = @"
        lemma lemma_EstablishInitRequirements(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          inv:LPlusState->bool,
          relation:(LPlusState, HState)->bool
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires inv == InductiveInv
          requires relation == LiftingRelation
          ensures  AtomicInitImpliesInv(lasf, inv)
          ensures  forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
        {
          forall ls | lasf.init(ls)
            ensures inv(ls)
            ensures exists hs :: hasf.init(hs) && relation(ls, hs)
          {
            lemma_InitImpliesInductiveInv(ls);
            var hs := ConvertTotalState_LPlusH(ls);
            var hconfig := ConvertConfig_LH(ls.config);
            assert H.Armada_InitConfig(hs, hconfig);
            var tid_init := ls.config.tid_init;
            var ls_alt := ConvertTotalState_HL(hs);
            assert ls.s.threads[tid_init] == ls_alt.threads[tid_init];
            assert hasf.init(hs) && relation(ls, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateIntroduceAtomicPathLemmaForNormalPath(AtomicPath atomicPath)
    {
      var name = atomicPath.Name;

      var lpc = LowerPC(atomicPath.StartPC);

      string tyConstraint =
        atomicPath.StartType == PCAtomicType.Yielding
          ? "ty.AtomicPathType_YY? || ty.AtomicPathType_YS? || ty.AtomicPathType_YR?"
          : "ty.AtomicPathType_RY? || ty.AtomicPathType_RS? || ty.AtomicPathType_RR?";
      string yieldingDependentRequires =
        (pgp.symbolsLow.IsNonyieldingPC(lpc) || !canIntroduceTau) ? "" : "requires !CanIntroduceTau(hs, tid)";
      string pathConstructor = hAtomic.GetConstructorString(atomicPath);
      string extraProof = canIntroduceTau ? "lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectLowLevel(tid);" : "";

      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      string str = $@"
        lemma lemma_IntroduceAtomicPath_{name}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          requires ls.s.stop_reason.Armada_NotStopped?
          requires tid in ls.s.threads
          requires tid in hs.threads
          requires ls.s.threads[tid].pc.{lpc}?
          { yieldingDependentRequires }
          requires var ty := lasf.path_type(lpath); {tyConstraint}
          requires hs.threads[tid].pc.{atomicPath.StartPC}?
          ensures  AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath)
        {{
          hpath := { pathConstructor };
          var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);

          { hpr.GetOpenPathInvocation(atomicPath) }

          assert hs'.stop_reason.Armada_NotStopped?;
          assert PCToInstructionCount_H(hs'.threads[tid].pc) > PCToInstructionCount_H(hs.threads[tid].pc);

          { extraProof }
          ProofCustomizationGoesHere();
          assert VarIntroThreadInvariant(hs', tid);

          /* { hpr.GetAssertValidPathInvocation(atomicPath) } */
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateIntroduceNormalPathLemmas()
    {
      foreach (var atomicPaths in pcToIntroducedPaths.Values) {
        foreach (var atomicPath in atomicPaths) {
          GenerateIntroduceAtomicPathLemmaForNormalPath(atomicPath);
        }
      }
    }

    private void GenerateIntroduceAtomicPathLemmaForTauPath()
    {
      var pr = new PrefixedVarsPathPrinter(hAtomic);

      string str = $@"
        lemma lemma_IntroduceAtomicPath_Tau(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          requires ls.s.stop_reason.Armada_NotStopped?
          requires tid in ls.s.threads
          requires !L.Armada_IsNonyieldingPC(ls.s.threads[tid].pc) || lpath.LAtomic_Path_Tau?
          requires CanIntroduceTau(hs, tid)
          ensures  AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath)
        {{
          var lty := lasf.path_type(lpath);
          if lty.AtomicPathType_RY? || lty.AtomicPathType_RS? || lty.AtomicPathType_RR? {{
            assert !L.Armada_IsNonyieldingPC(ls.s.threads[tid].pc);
            assert false;
          }}

          hpath := HAtomic_Path_Tau(HAtomic_PathSteps_Tau(H.Armada_Step_Tau()));
          var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);

          { pr.GetOpenPathInvocation(hAtomic.TauPath) }
          ProofCustomizationGoesHere();

          assert ProgressMeasure(hs', lpath, tid).1 == |hs'.threads[tid].storeBuffer|;
          assert ProgressMeasure(hs, lpath, tid).1 == |hs.threads[tid].storeBuffer|;
          assert 0 <= ProgressMeasure(hs', lpath, tid).0 == ProgressMeasure(hs, lpath, tid).0;
          assert 0 <= ProgressMeasure(hs', lpath, tid).1 < ProgressMeasure(hs, lpath, tid).1;
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateLiftAtomicPathLemmaForTauPath()
    {
      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);
      var extraRequires = canIntroduceTau ? "requires !CanIntroduceTau(hs, tid)" : "";

      string str = $@"
        lemma lemma_LiftAtomicPath_Tau(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          requires lpath.LAtomic_Path_Tau?
          { extraRequires }
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
        {{
          { lpr.GetOpenValidPathInvocation(lAtomic.TauPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          hpath := ConvertAtomicPath_LH(lpath);

          lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);

          { hpr.GetOpenPathInvocation(hAtomic.TauPath) }
          ProofCustomizationGoesHere();
          assert ls'.s.threads[tid] == ConvertTotalState_HL(hasf.path_next(hs, hpath, tid)).threads[tid];
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateLiftAtomicPathLemmaForNormalPath(AtomicPath lAtomicPath, AtomicPath hAtomicPath)
    {
      var lname = lAtomicPath.Name;
      var hname = hAtomicPath.Name;

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      string extraProof = "";
      if (lAtomicPath.StartType == PCAtomicType.Yielding)
      {
        extraProof = @"
          var lpc := ls.s.threads[tid].pc;
          assert !L.Armada_IsNonyieldingPC(lpc);
        ";
        if (canIntroduceTau)
        {
          extraProof += @"
          assert !CanIntroduceTau(hs, tid);
          lemma_AlwaysIfLStoreBufferEmptyAndCantIntroduceTauThenHStoreBufferEmpty();
          lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectLowLevel(tid);
          ";
        }
      }
      string yieldingDependentRequires =
        (lAtomicPath.StartType == PCAtomicType.Yielding && canIntroduceTau) ? "requires !CanIntroduceTau(hs, tid)" : "";

      string str = $@"
        lemma lemma_VarIntroThreadInvariantMaintainedByAtomicPath_{lname}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hpath: HAtomic_Path,
          hs': HState
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{lname}?
          requires tid in ls.s.threads
          requires tid in hs.threads
          { yieldingDependentRequires }
          requires hs.threads[tid].pc.{hAtomicPath.StartPC}?
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_ValidPath(hs, hpath, tid)
          requires hs' == HAtomic_GetStateAfterPath(hs, hpath, tid)
          ensures  forall other_tid :: other_tid in hs'.threads ==> VarIntroThreadInvariant(hs', other_tid)
        {{
          { lpr.GetOpenValidPathInvocation(lAtomicPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);

          { hpr.GetOpenPathInvocation(hAtomicPath) }
          ProofCustomizationGoesHere();

          forall other_tid | other_tid in hs'.threads
            ensures VarIntroThreadInvariant(hs', other_tid)
          {{
            assert other_tid in hs.threads ==> VarIntroThreadInvariant(hs, other_tid);
            if other_tid == tid {{
              assert VarIntroThreadInvariant(hs', other_tid);
            }}
            else {{
              assert VarIntroThreadInvariant(hs', other_tid);
            }}
          }}
        }}
      ";
      pgp.AddLemma(str, "lift");

      if (!lAtomicPath.Stopping)
      {
        string postcondition;
        if (lAtomicPath.LastNextRoutine.nextType == NextType.TerminateThread)
        {
          postcondition = "tid !in ls'.s.threads && tid !in alt_ls'.threads";
        }
        else
        {
          postcondition = "tid in ls'.s.threads && tid in alt_ls'.threads && ls'.s.threads[tid] == alt_ls'.threads[tid]";
        }
        str = $@"
        lemma lemma_ActingThreadMatchesLHMaintainedByAtomicPath_{lname}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hpath: HAtomic_Path,
          hs': HState
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{lname}?
          requires tid in ls.s.threads
          requires tid in hs.threads
          { yieldingDependentRequires }
          requires hs.threads[tid].pc.{hAtomicPath.StartPC}?
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_ValidPath(hs, hpath, tid)
          requires hs' == HAtomic_GetStateAfterPath(hs, hpath, tid)
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var alt_ls' := ConvertTotalState_HL(hs');
                   { postcondition }
        {{
          { lpr.GetOpenValidPathInvocation(lAtomicPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);

          { hpr.GetOpenPathInvocation(hAtomicPath) }
          ProofCustomizationGoesHere();
          { extraProof }

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
        }}
        ";
        pgp.AddLemma(str, "lift");

        foreach (var tup in lAtomicPath.NextRoutinesWithIndices)
        {
          var nextRoutine = tup.Item1;
          if (nextRoutine.nextType == NextType.CreateThread)
          {
            var whichStep = tup.Item2;
            str = $@"
        lemma lemma_ThreadCreatedInStep{whichStep}MatchesLHMaintainedByAtomicPath_{lname}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hpath: HAtomic_Path,
          hs': HState
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{lname}?
          requires tid in ls.s.threads
          requires tid in hs.threads
          { yieldingDependentRequires }
          requires hs.threads[tid].pc.{hAtomicPath.StartPC}?
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_ValidPath(hs, hpath, tid)
          requires hs' == HAtomic_GetStateAfterPath(hs, hpath, tid)
          requires lpath.steps_{lAtomicPath.Name}.step{whichStep}.Armada_Step_{nextRoutine.NameSuffix}?
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var alt_ls' := ConvertTotalState_HL(hs');
                   var newtid := lpath.steps_{lAtomicPath.Name}.step{whichStep}.params_{nextRoutine.NameSuffix}.newtid;
                   newtid in ls'.s.threads && newtid in alt_ls'.threads && ls'.s.threads[newtid] == alt_ls'.threads[newtid]
        {{
          { lpr.GetOpenValidPathInvocation(lAtomicPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);

          { hpr.GetOpenPathInvocation(hAtomicPath) }
          ProofCustomizationGoesHere();
          { extraProof }

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
        }}
          ";
            pgp.AddLemma(str, "lift");
          }
        }

        var threadNotCreatedRequires = String.Concat(lAtomicPath.NextRoutinesWithIndices
          .Where(tup => tup.Item1.nextType == NextType.CreateThread)
          .Select(tup => $@"
             requires lpath.steps_{lAtomicPath.Name}.step{tup.Item2}.Armada_Step_{tup.Item1.NameSuffix}?
             requires any_tid != lpath.steps_{lAtomicPath.Name}.step{tup.Item2}.params_{tup.Item1.NameSuffix}.newtid
          ")
        );
        str = $@"
        lemma lemma_NonactingThreadMatchesLHMaintainedByAtomicPath_{lname}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hpath: HAtomic_Path,
          hs': HState,
          any_tid: Armada_ThreadHandle
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{lname}?
          requires tid in ls.s.threads
          requires tid in hs.threads
          { yieldingDependentRequires }
          requires hs.threads[tid].pc.{hAtomicPath.StartPC}?
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_ValidPath(hs, hpath, tid)
          requires hs' == HAtomic_GetStateAfterPath(hs, hpath, tid)
          requires any_tid != tid
          { threadNotCreatedRequires }
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var alt_ls' := ConvertTotalState_HL(hs');
                   if any_tid !in ls'.s.threads then
                     any_tid !in alt_ls'.threads
                   else
                     && any_tid in alt_ls'.threads
                     && ls'.s.threads[any_tid] == alt_ls'.threads[any_tid]
        {{
          { lpr.GetOpenValidPathInvocation(lAtomicPath) }

          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);

          { hpr.GetOpenPathInvocation(hAtomicPath) }
          ProofCustomizationGoesHere();
          { extraProof }

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
        }}
        ";
        pgp.AddLemma(str, "lift");
      }

      str = $@"
        lemma lemma_LiftAtomicPath_{lname}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          requires lpath.LAtomic_Path_{lname}?
          requires tid in ls.s.threads
          requires tid in hs.threads
          { yieldingDependentRequires }
          requires hs.threads[tid].pc.{hAtomicPath.StartPC}?
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
        {{
          { lpr.GetOpenValidPathInvocation(lAtomicPath) }

          var locv: H.Armada_SharedMemory := H.Armada_GetThreadLocalView(ConvertTotalState_LPlusH(ls), tid);
          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          hpath := ConvertAtomicPath_LH(lpath);
          var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);

          { hpr.GetOpenPathInvocation(hAtomicPath) }
          ProofCustomizationGoesHere();
          { extraProof }

          lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);
          assert InductiveInv(ls');
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();

          assert HAtomic_ValidPath(hs, hpath, tid);
      ";
      if (lAtomicPath.Stopping)
      {
        str += @"
          assert !ls'.s.stop_reason.Armada_NotStopped?;
        ";
      }
      else
      {
        str += $@"
          assert ls'.s.stop_reason.Armada_NotStopped?;
          var alt_ls' := ConvertTotalState_HL(hs');
          assert ls'.s.stop_reason == alt_ls'.stop_reason;
          forall any_tid
            ensures any_tid !in ls'.s.threads ==> any_tid !in alt_ls'.threads
            ensures any_tid in ls'.s.threads ==> any_tid in alt_ls'.threads && ls'.s.threads[any_tid] == alt_ls'.threads[any_tid]
          {{
            if any_tid == tid {{
              lemma_ActingThreadMatchesLHMaintainedByAtomicPath_{lname}(lasf, hasf, ls, lpath, tid, hs, hpath, hs');
            }}
        ";
        foreach (var tup in lAtomicPath.NextRoutinesWithIndices)
        {
          var nextRoutine = tup.Item1;
          if (nextRoutine.nextType == NextType.CreateThread)
          {
            var whichStep = tup.Item2;
            str += $@"
            else if any_tid == lsteps.step{whichStep}.params_{nextRoutine.NameSuffix}.newtid {{
              lemma_ThreadCreatedInStep{whichStep}MatchesLHMaintainedByAtomicPath_{lname}(lasf, hasf, ls, lpath, tid, hs, hpath, hs');
            }}
            ";
          }
        }
        str += $@"
            else {{
              lemma_NonactingThreadMatchesLHMaintainedByAtomicPath_{lname}(lasf, hasf, ls, lpath, tid, hs, hpath, hs', any_tid);
            }}
          }}
          assert ls'.s.threads == alt_ls'.threads;
          assert ls'.s.mem == alt_ls'.mem;
          assert ls'.s == alt_ls';
        ";
      }
      str += $@"
          lemma_VarIntroThreadInvariantMaintainedByAtomicPath_{lname}(lasf, hasf, ls, lpath, tid, hs, hpath, hs');
          assert LiftingRelation(ls', hs');
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateIntroduceOrLiftAtomicPathLemmaForNormalPath(AtomicPath lAtomicPath)
    {
      var name = lAtomicPath.Name;

      string finalCases = "";

      var hAtomicPath = pathMap[lAtomicPath];
      GenerateLiftAtomicPathLemmaForNormalPath(lAtomicPath, hAtomicPath);

      finalCases += $@"
        if hpc.{hAtomicPath.StartPC}? {{
          hpath := lemma_LiftAtomicPath_{name}(lasf, hasf, ls, lpath, tid, hs);
          assert LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath);
          return;
        }}
      ";

      List<AtomicPath> introducedPaths;
      if (pcToIntroducedPaths.TryGetValue(lAtomicPath.StartPC, out introducedPaths)) {
        foreach (var introducedPath in introducedPaths) {
          finalCases += $@"
            if hpc.{introducedPath.StartPC}? {{
              hpath := lemma_IntroduceAtomicPath_{introducedPath.Name}(lasf, hasf, ls, lpath, tid, hs);
              assert AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath);
              return;
            }}
          ";
        }
      }

      string extraProof = "";
      if (lAtomicPath.StartType == PCAtomicType.Yielding) {
        extraProof = "assert !L.Armada_IsNonyieldingPC(lpc);\n";
        if (canIntroduceTau) {
          extraProof += "assert !CanIntroduceTau(hs, tid);\n";
        }
      }

      string yieldingRequires =
        canIntroduceTau ? "requires !Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid) || !CanIntroduceTau(hs, tid)" : "";

      string str = $@"
        lemma lemma_IntroduceOrLiftAtomicPath_{name}(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          requires lpath.LAtomic_Path_{name}?
          { yieldingRequires }
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
                   || AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath)
        {{
          lemma_LAtomic_PathHasPCEffect_{lAtomicPath.Name}(ls, lpath, tid);
          assert tid in ls.s.threads;
          assert tid in hs.threads;
          var lpc := ls.s.threads[tid].pc;
          var hpc := hs.threads[tid].pc;
          assert lpc.{lAtomicPath.StartPC}?;
          assert VarIntroThreadInvariant(hs, tid);
          { extraProof }
          { finalCases }
          assert false;
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateIntroduceOrLiftAtomicPathLemmas()
    {
      GenerateIntroduceNormalPathLemmas();
      if (canIntroduceTau) {
        GenerateIntroduceAtomicPathLemmaForTauPath();
      }
      GenerateLiftAtomicPathLemmaForTauPath();

      var finalCases = @"
        case LAtomic_Path_Tau(_) =>
          hpath := lemma_LiftAtomicPath_Tau(lasf, hasf, ls, lpath, tid, hs);
          assert LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath);
      ";

      foreach (var atomicPath in lAtomic.AtomicPaths.Where(ap => !ap.Tau)) {
        GenerateIntroduceOrLiftAtomicPathLemmaForNormalPath(atomicPath);
        finalCases += $@"
          case LAtomic_Path_{atomicPath.Name}(_) =>
            hpath := lemma_IntroduceOrLiftAtomicPath_{atomicPath.Name}(lasf, hasf, ls, lpath, tid, hs);
        ";
      }

      string tauIntroduction = "";
      if (canIntroduceTau) {
        tauIntroduction = $@"
          if (lpath.LAtomic_Path_Tau? || Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid)) && CanIntroduceTau(hs, tid) {{
            hpath := lemma_IntroduceAtomicPath_Tau(lasf, hasf, ls, lpath, tid, hs);
            assert AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath);
            return;
          }}
        ";
      }

      string str = $@"
        lemma lemma_EstablishAtomicPathLiftable(
          lasf: AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf: AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
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
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
                   || AtomicPathIntroduced(lasf, hasf, LiftingRelation, ProgressMeasure, ls, lpath, tid, hs, hpath)
        {{
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          { tauIntroduction }

          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }
  };
};
