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

  public class GlobalVarHidingProofGenerator : VarHidingProofGenerator
  {
    private GlobalVariableHidingStrategyDecl strategy;
    private HashSet<string> hiddenVariables;

    public GlobalVarHidingProofGenerator(ProofGenerationParams i_pgp, GlobalVariableHidingStrategyDecl i_strategy) : base(i_pgp, true)
    {
      strategy = i_strategy;
      hiddenVariables = new HashSet<string>(strategy.Variables);
      if (hiddenVariables.All(varName => pgp.symbolsLow.Globals.Lookup(varName).varType == ArmadaVarType.Ghost)) {
        canHideTau = false;
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Checking that the layers are similar enough to generate a proof
    ////////////////////////////////////////////////////////////////////////

    // We have to override the default implementation of CheckGlobalsEquivalence because we need to
    // skip hidden variables.

    protected override bool CheckGlobalsEquivalence()
    {
      var globalVarsLow = pgp.symbolsLow.Globals.VariableNames.Where(s => !hiddenVariables.Contains(s)).ToArray();
      var globalVarsHigh = pgp.symbolsHigh.Globals.VariableNames.ToArray();

      if (globalVarsLow.Length != globalVarsHigh.Length) {
        AH.PrintError(pgp.prog, $"There are {globalVarsLow.Length} global variables in level {pgp.mLow.Name} (not counting hidden ones) but {globalVarsHigh.Length} in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < globalVarsLow.Length; ++i) {
        if (globalVarsLow[i] != globalVarsHigh[i]) {
          AH.PrintError(pgp.prog, $"Global variable number {i+1} (not counting hidden ones) in level {pgp.mLow.Name} is {globalVarsLow[i]}, which doesn't match global variable number {i+1} in level {pgp.mHigh.Name} which is {globalVarsHigh[i]}");
          return false;
        }
        var name = globalVarsLow[i];
        if (!CheckGlobalVariableEquivalence(name, pgp.symbolsLow.Globals.Lookup(name), pgp.symbolsHigh.Globals.Lookup(name))) {
          return false;
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    // PC mapping
    ////////////////////////////////////////////////////////////////////////

    protected override bool IsVariableHidden(string methodName, string varName)
    {
      if (varName == null) {
        return false;
      }
      if (!hiddenVariables.Contains(varName)) {
        return false;
      }

      // If it has the same name as an introduced global varible, make sure
      // it isn't shadowed by a local variable in this method.

      var st = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      return st.LookupVariable(varName) == null;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateConvertGlobals_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          ps.Add($"globals.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertGlobals_LH(globals: L.Armada_Globals) : H.Armada_Globals
        {{
          H.Armada_Globals({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertGlobalStaticVar_LH()
    {
      if (!canHideTau) {
        base.GenerateConvertGlobalStaticVar_LH();
        return;
      }
      
      var es = new List<string>();
      foreach (var varName in hiddenVariables) {
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          es.Add($"!v.Armada_GlobalStaticVar_{varName}?");
        }
      }

      var fn = $@"
        predicate CanConvertGlobalStaticVar_LH(v: L.Armada_GlobalStaticVar)
        {{
          {AH.CombineStringsWithAnd(es)}
        }}
      ";
      pgp.AddPredicate(fn, "convert");

      var caseBodies = "case Armada_GlobalStaticVarNone => H.Armada_GlobalStaticVarNone\n";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          caseBodies += $"case Armada_GlobalStaticVar_{varName} => H.Armada_GlobalStaticVar_{varName}\n";
        }
      }
      fn = $@"
        function ConvertGlobalStaticVar_LH(v: L.Armada_GlobalStaticVar) : H.Armada_GlobalStaticVar
          requires CanConvertGlobalStaticVar_LH(v)
        {{
          match v
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertGhosts_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalGhostArmadaVariable) {
          ps.Add($"ghosts.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertGhosts_LH(ghosts: L.Armada_Ghosts) : H.Armada_Ghosts
        {{
          H.Armada_Ghosts({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertStoreBufferLocation_LH()
    {
      if (!canHideTau) {
        base.GenerateConvertStoreBufferLocation_LH();
        return;
      }

      string str;

      str = @"
        predicate CanConvertStoreBufferLocation_LH(loc:L.Armada_StoreBufferLocation)
        {
          loc.Armada_StoreBufferLocation_Unaddressable? ==> CanConvertGlobalStaticVar_LH(loc.v)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferLocation_LH(loc:L.Armada_StoreBufferLocation) : H.Armada_StoreBufferLocation
          requires CanConvertStoreBufferLocation_LH(loc)
        {
          match loc
            case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
              H.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_LH(v), fields)
            case Armada_StoreBufferLocation_Addressable(p) =>
              H.Armada_StoreBufferLocation_Addressable(p)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBufferEntry_LH()
    {
      if (!canHideTau) {
        base.GenerateConvertStoreBufferEntry_LH();
        return;
      }
      
      string str;

      str = @"
        predicate CanConvertStoreBufferEntry_LH(entry:L.Armada_StoreBufferEntry)
        {
          CanConvertStoreBufferLocation_LH(entry.loc)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferEntry_LH(entry:L.Armada_StoreBufferEntry) : H.Armada_StoreBufferEntry
          requires CanConvertStoreBufferEntry_LH(entry)
        {
          H.Armada_StoreBufferEntry(ConvertStoreBufferLocation_LH(entry.loc), entry.value, ConvertPC_LH(entry.pc))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBuffer_LH()
    {
      if (!canHideTau) {
        base.GenerateConvertStoreBuffer_LH();
        return;
      }

      string str = @"
        function ConvertStoreBuffer_LH(entries:seq<L.Armada_StoreBufferEntry>) : seq<H.Armada_StoreBufferEntry>
        {
          FilterMapSeqToSeq(entries, e => if CanConvertStoreBufferEntry_LH(e) then Some(ConvertStoreBufferEntry_LH(e)) else None)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertAtomicPath_LH()
    {
      string str;

      var skipped_strs = new List<string>();

      if (canHideTau) {
        str = @"
          predicate IsSkippedTauPath(s: LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
          {
            && path.LAtomic_Path_Tau?
            && tid in s.s.threads
            && |s.s.threads[tid].storeBuffer| > 0
            && !CanConvertStoreBufferEntry_LH(s.s.threads[tid].storeBuffer[0])
          }
        ";
        pgp.AddPredicate(str, "convert");

        skipped_strs.Add("IsSkippedTauPath(s, path, tid)");
      }

      string convert_str = @"
        function ConvertAtomicPath_LH(s: LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle) : HAtomic_Path
          requires LAtomic_ValidPath(s, path, tid)
          requires !IsSkippedPath(s, path, tid)
        {
          match path
      ";

      foreach (var lpath in lAtomic.AtomicPaths) {
        if (pathMap.ContainsKey(lpath)) {
          var hpath = pathMap[lpath];
          var n = lpath.NextRoutines.Count;
          convert_str += $"case LAtomic_Path_{lpath.Name}(steps) => HAtomic_Path_{hpath.Name}(HAtomic_PathSteps_{hpath.Name}(";
          convert_str += String.Join(", ", Enumerable.Range(0, n)
                                                     .Where(i => nextRoutineMap.ContainsKey(lpath.NextRoutines[i]))
                                                     .Select(i => $"ConvertStep_LH(steps.step{i})"));
          convert_str += "))\n";
        }
        else {
          skipped_strs.Add($"path.LAtomic_Path_{lpath.Name}?");
        }
      }

      convert_str += "}\n";

      pgp.AddPredicate($@"
        predicate IsSkippedPath(s: LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
        {{
          { AH.CombineStringsWithOr(skipped_strs) }
        }}
      ", "convert");

      pgp.AddFunction(convert_str, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Store-buffer lemmas
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateLocalViewCommutativityLemmas()
    {
      if (!canHideTau) {
        base.GenerateLocalViewCommutativityLemmas();
        return;
      }

      string str;

      string cases = "";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var globalVar = pgp.symbolsLow.Globals.Lookup(varName);
        if (globalVar is AddressableArmadaVariable || globalVar.NoTSO()) {
          continue;
        }
        cases += $"case Armada_GlobalStaticVar_{varName} => {{ }}";
      }
      str = $@"
        lemma lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(
          lglobals:L.Armada_Globals, lv:L.Armada_GlobalStaticVar, fields:seq<int>, value:Armada_PrimitiveValue,
          hv:H.Armada_GlobalStaticVar, hglobals1:H.Armada_Globals, hglobals2:H.Armada_Globals)
          requires CanConvertGlobalStaticVar_LH(lv)
          requires hv == ConvertGlobalStaticVar_LH(lv)
          requires hglobals1 == ConvertGlobals_LH(L.Armada_ApplyTauUnaddressable(lglobals, lv, fields, value))
          requires hglobals2 == H.Armada_ApplyTauUnaddressable(ConvertGlobals_LH(lglobals), hv, fields, value)
          ensures  hglobals1 == hglobals2
        {{
          match lv
            case Armada_GlobalStaticVarNone =>
            {{
              var hglobals := ConvertGlobals_LH(lglobals);
              assert hglobals1 == hglobals == hglobals2;
            }}
            { cases }
        }}
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem:L.Armada_SharedMemory, lentry:L.Armada_StoreBufferEntry)
          requires !CanConvertStoreBufferEntry_LH(lentry)
          ensures  ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry)) == ConvertSharedMemory_LH(lmem)
        {
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem:L.Armada_SharedMemory, lentry:L.Armada_StoreBufferEntry,
                                                             hentry:H.Armada_StoreBufferEntry, hmem1:H.Armada_SharedMemory,
                                                             hmem2:H.Armada_SharedMemory)
          requires CanConvertStoreBufferEntry_LH(lentry)
          requires hentry == ConvertStoreBufferEntry_LH(lentry)
          requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry))
          requires hmem2 == H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry)
          ensures  hmem1 == hmem2
        {
          match lentry.loc
            case Armada_StoreBufferLocation_Unaddressable(lv, lfields) =>
            {
              var hv := ConvertGlobalStaticVar_LH(lv);
              lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(lmem.globals, lv, lfields, lentry.value, hv, hmem1.globals,
                                                                          hmem2.globals);
            }
            case Armada_StoreBufferLocation_Addressable(p) =>
            {
            }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferCommutesWithConvert(lmem:L.Armada_SharedMemory, lbuf:seq<L.Armada_StoreBufferEntry>,
                                                        hbuf:seq<H.Armada_StoreBufferEntry>, hmem1:H.Armada_SharedMemory,
                                                        hmem2:H.Armada_SharedMemory)
          requires hbuf == ConvertStoreBuffer_LH(lbuf)
          requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBuffer(lmem, lbuf))
          requires hmem2 == H.Armada_ApplyStoreBuffer(ConvertSharedMemory_LH(lmem), hbuf)
          ensures  hmem1 == hmem2
          decreases |lbuf| + |hbuf|
        {
          if |lbuf| == 0 {
              return;
          }

          var lmem' := L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]);

          if CanConvertStoreBufferEntry_LH(lbuf[0]) {
              var hmem1' := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
              var hmem2' := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hbuf[0]);
              lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
          }
          else {
              lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem, lbuf[0]);
              assert ConvertSharedMemory_LH(lmem') == ConvertSharedMemory_LH(lmem);
              assert hbuf == ConvertStoreBuffer_LH(lbuf[1..]);
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf, hmem1, hmem2);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_GetThreadLocalViewCommutesWithConvert(ls:LState, hs:HState, tid:Armada_ThreadHandle)
          requires hs == ConvertTotalState_LH(ls)
          requires tid in ls.threads;
          ensures  ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(hs, tid)
        {
          assert tid in hs.threads;
          lemma_ApplyStoreBufferCommutesWithConvert(ls.mem, ls.threads[tid].storeBuffer,
                                                    hs.threads[tid].storeBuffer,
                                                    ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)),
                                                    H.Armada_GetThreadLocalView(hs, tid));
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_GetThreadLocalViewAlwaysCommutesWithConvert()
          ensures forall ls:L.Armada_TotalState, tid:Armada_ThreadHandle
                    {:trigger L.Armada_GetThreadLocalView(ls, tid)}
                    :: tid in ls.threads ==>
                    ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) ==
                    H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
        {
          forall ls:L.Armada_TotalState, tid:Armada_ThreadHandle {:trigger L.Armada_GetThreadLocalView(ls, tid)}
            | tid in ls.threads
            ensures ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) ==
                    H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
          {
              var hs := ConvertTotalState_LH(ls);
              lemma_GetThreadLocalViewCommutesWithConvert(ls, hs, tid);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_StoreBufferAppendConversion(buf: seq<L.Armada_StoreBufferEntry>, entry: L.Armada_StoreBufferEntry)
          ensures  ConvertStoreBuffer_LH(buf + [entry]) ==
                     if CanConvertStoreBufferEntry_LH(entry) then
                       ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)]
                     else
                       ConvertStoreBuffer_LH(buf)
        {
          assert [entry][1..] == [];

          if |buf| == 0 {
            assert buf + [entry] == [entry];
            assert ConvertStoreBuffer_LH(buf + [entry]) == ConvertStoreBuffer_LH([entry]);
            assert ConvertStoreBuffer_LH(buf) == [];

            if CanConvertStoreBufferEntry_LH(entry) {
              calc {
                ConvertStoreBuffer_LH([entry]);
                [ConvertStoreBufferEntry_LH(entry)] + ConvertStoreBuffer_LH([entry][1..]);
                [ConvertStoreBufferEntry_LH(entry)] + ConvertStoreBuffer_LH([]);
                [ConvertStoreBufferEntry_LH(entry)] + [];
                [ConvertStoreBufferEntry_LH(entry)];
              }
            }
            else {
              calc {
                ConvertStoreBuffer_LH([entry]);
                ConvertStoreBuffer_LH([entry][1..]);
                ConvertStoreBuffer_LH([]);
                [];
              }
            }
          }
          else {
            calc {
              ConvertStoreBuffer_LH(buf + [entry]);
              {
                assert buf == [buf[0]] + buf[1..];
              }
              ConvertStoreBuffer_LH([buf[0]] + buf[1..] + [entry]);
              {
                assert [buf[0]] + buf[1..] + [entry] == [buf[0]] + (buf[1..] + [entry]);
              }
              ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
            }
            if CanConvertStoreBufferEntry_LH(buf[0]) {
              calc {
                ConvertStoreBuffer_LH(buf + [entry]);
                ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
                [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..] + [entry]);
              }
              lemma_StoreBufferAppendConversion(buf[1..], entry);
              if CanConvertStoreBufferEntry_LH(entry) {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + (ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)];
                  ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)];
                }
              }
              else {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..]);
                  ConvertStoreBuffer_LH(buf);
                }
              }
            }
            else {
              assert ConvertStoreBuffer_LH(buf) == ConvertStoreBuffer_LH(buf[1..]);
              calc {
                ConvertStoreBuffer_LH(buf + [entry]);
                ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
                ConvertStoreBuffer_LH((buf[1..] + [entry]));
              }
              lemma_StoreBufferAppendConversion(buf[1..], entry);
              if CanConvertStoreBufferEntry_LH(entry) {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)];
                  ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)];
                }
              }
              else {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  ConvertStoreBuffer_LH(buf[1..]);
                  ConvertStoreBuffer_LH(buf);
                }
              }
            }
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry
                    {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)} ::
                    CanConvertStoreBufferEntry_LH(lentry) ==>
                    H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) ==
                    ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry
            {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)}
            | CanConvertStoreBufferEntry_LH(lentry)
            ensures H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) ==
                    ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ConvertStoreBufferCommutesOverBeheadment(buf:seq<L.Armada_StoreBufferEntry>)
          requires |buf| > 0
          requires CanConvertStoreBufferEntry_LH(buf[0])
          ensures  ConvertStoreBuffer_LH(buf[1..]) == ConvertStoreBuffer_LH(buf)[1..]
        {
          var hbuf1 := ConvertStoreBuffer_LH(buf[1..]);
          var hbuf2 := ConvertStoreBuffer_LH(buf)[1..];
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
        lemma lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid:Armada_ThreadHandle)
          ensures forall s:L.Armada_TotalState, entry:L.Armada_StoreBufferEntry
            {:trigger L.Armada_AppendToThreadStoreBuffer(s, tid, entry)} ::
            tid in s.threads && !CanConvertStoreBufferEntry_LH(entry) ==>
            ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_LH(s)
        {
          forall s:L.Armada_TotalState, entry:L.Armada_StoreBufferEntry {:trigger L.Armada_AppendToThreadStoreBuffer(s, tid, entry)} |
            tid in s.threads && !CanConvertStoreBufferEntry_LH(entry)
            ensures ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_LH(s)
          {
            var hs := ConvertTotalState_LH(s);
            var hs' := ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry));
            lemma_StoreBufferAppendConversion(s.threads[tid].storeBuffer, entry);
            assert hs.threads[tid].storeBuffer == hs'.threads[tid].storeBuffer;
            assert hs.threads == hs'.threads;
            assert hs == hs';
          }
        }
      ";
      pgp.AddLemma(str, "utility");
    }
  }
}
