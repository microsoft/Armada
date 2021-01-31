using System.Collections.Generic;
using System.Linq;
using System;

namespace Microsoft.Armada
{
  public class GlobalVarIntroProofGenerator : VarIntroProofGenerator
  {
    private GlobalVariableIntroStrategyDecl strategy;
    private HashSet<string> introducedVariables;

    public GlobalVarIntroProofGenerator(ProofGenerationParams i_pgp, GlobalVariableIntroStrategyDecl i_strategy)
      : base(i_pgp, true /* can introduce tau */)
    {
      strategy = i_strategy;
      introducedVariables = new HashSet<string>();
      foreach (var tok in strategy.Variables) {
        introducedVariables.Add(tok.val);
      }
      if (introducedVariables.All(varName => pgp.symbolsHigh.Globals.Lookup(varName).varType == ArmadaVarType.Ghost)) {
        canIntroduceTau = false;
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // Equivalence checking
    ////////////////////////////////////////////////////////////////////////

    // We have to override the default implementation of CheckGlobalsEquivalence because we need to
    // skip introduced variables.

    protected override bool CheckGlobalsEquivalence()
    {
      var globalVarsLow = pgp.symbolsLow.Globals.VariableNames.ToArray();
      var globalVarsHigh = pgp.symbolsHigh.Globals.VariableNames.Where(s => !introducedVariables.Contains(s)).ToArray();

      if (globalVarsLow.Length != globalVarsHigh.Length) {
        AH.PrintError(pgp.prog, $"There are {globalVarsLow.Length} global variables in level {pgp.mLow.Name} (not counting hidden ones) but {globalVarsHigh.Length} in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < globalVarsLow.Length; ++i) {
        if (globalVarsLow[i] != globalVarsHigh[i]) {
          AH.PrintError(pgp.prog, $"Global variable number {i+1} (not counting hidden ones) in level {pgp.mLow.Name} is {globalVarsLow[i]}, which do<esn't match global variable number {i+1} in level {pgp.mHigh.Name} which is {globalVarsHigh[i]}");
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

    protected override bool IsIntroducedVariable(string methodName, string varName)
    {
      if (varName == null) {
        return false;
      }
      if (!introducedVariables.Contains(varName)) {
        return false;
      }

      // If it has the same name as an introduced global varible, make sure
      // it isn't shadowed by a local variable in this method.

      var st = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
      return st.LookupVariable(varName) == null;
    }

    ////////////////////////////////////////////////////////////////////////
    // Abstraction
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateConvertGlobals_HL()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          ps.Add($"globals.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertGlobals_HL(globals: H.Armada_Globals) : L.Armada_Globals
        {{
          L.Armada_Globals({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertGlobalStaticVar_HL()
    {
      if (!canIntroduceTau) {
        base.GenerateConvertGlobalStaticVar_HL();
        return;
      }

      var es = new List<string>();
      foreach (var varName in introducedVariables) {
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          es.Add($"!v.Armada_GlobalStaticVar_{varName}?");
        }
      }
      var fn = $@"
        predicate CanConvertGlobalStaticVar_HL(v: H.Armada_GlobalStaticVar)
        {{
          {AH.CombineStringsWithAnd(es)}
        }}
      ";
      pgp.AddPredicate(fn, "convert");

      var caseBodies = "case Armada_GlobalStaticVarNone => L.Armada_GlobalStaticVarNone\n";
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          caseBodies += $"case Armada_GlobalStaticVar_{varName} => L.Armada_GlobalStaticVar_{varName}\n";
        }
      }
      fn = $@"
        function ConvertGlobalStaticVar_HL(v: H.Armada_GlobalStaticVar) : L.Armada_GlobalStaticVar
          requires CanConvertGlobalStaticVar_HL(v)
        {{
          match v
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertGhosts_HL()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalGhostArmadaVariable) {
          ps.Add($"ghosts.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertGhosts_HL(ghosts: H.Armada_Ghosts) : L.Armada_Ghosts
        {{
          L.Armada_Ghosts({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertStoreBufferEntry_HL()
    {
      if (!canIntroduceTau) {
        base.GenerateConvertStoreBufferEntry_HL();
        return;
      }
      
      string str;

      str = @"
        predicate CanConvertStoreBufferEntry_HL(entry:H.Armada_StoreBufferEntry)
        {
          CanConvertStoreBufferLocation_HL(entry.loc)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferEntry_HL(entry:H.Armada_StoreBufferEntry) : L.Armada_StoreBufferEntry
          requires CanConvertStoreBufferEntry_HL(entry)
        {
          L.Armada_StoreBufferEntry(ConvertStoreBufferLocation_HL(entry.loc), entry.value, ConvertPC_HL(entry.pc))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBuffer_HL()
    {
      if (!canIntroduceTau) {
        base.GenerateConvertStoreBuffer_HL();
        return;
      }

      string str = @"
        function ConvertStoreBufferEntryTotal_HL(entry: H.Armada_StoreBufferEntry): Option<L.Armada_StoreBufferEntry> {
          if CanConvertStoreBufferEntry_HL(entry) then
            Some(ConvertStoreBufferEntry_HL(entry))
          else
            None
        }
      ";

      pgp.AddFunction(str, "convert");

      str = @"
        function ConvertStoreBuffer_HL(entries:seq<H.Armada_StoreBufferEntry>) : seq<L.Armada_StoreBufferEntry>
        {
          FilterMapSeqToSeq(entries, ConvertStoreBufferEntryTotal_HL)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBufferLocation_HL()
    {
      if (!canIntroduceTau) {
        base.GenerateConvertStoreBufferLocation_HL();
        return;
      }

      string str;

      str = @"
        predicate CanConvertStoreBufferLocation_HL(loc:H.Armada_StoreBufferLocation)
        {
          loc.Armada_StoreBufferLocation_Unaddressable? ==> CanConvertGlobalStaticVar_HL(loc.v)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferLocation_HL(loc:H.Armada_StoreBufferLocation) : L.Armada_StoreBufferLocation
          requires CanConvertStoreBufferLocation_HL(loc)
        {
          match loc
            case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
              L.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_HL(v), fields)
            case Armada_StoreBufferLocation_Addressable(p) =>
              L.Armada_StoreBufferLocation_Addressable(p)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    // TODO (Luke): more cases
    protected string ResolveInit(Expression expr)
    {
      return Printer.ExprToString(expr);
    }

    protected override void GenerateConvertGlobals_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v == null) {
          v = pgp.symbolsHigh.Globals.Lookup(varName);
          if (v is GlobalUnaddressableArmadaVariable global) {
            var p = ResolveInit(global.initialValue);
            if (p == null) {
              AH.PrintError(pgp.prog, $"Introduced global variable {varName} must be initialized");
            }
            ps.Add(p);
          }
        }
        else if (v is GlobalUnaddressableArmadaVariable) {
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

    protected override void GenerateConvertGhosts_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v == null) {
          v = pgp.symbolsHigh.Globals.Lookup(varName);
          if (v is GlobalGhostArmadaVariable ghost) {
            var p = ResolveInit(ghost.initialValue);
            if (p == null) {
              AH.PrintError(pgp.prog, $"Introduced ghost variable {varName} must be initialized");
            }
            ps.Add(p);
          }
        }
        else if (v is GlobalGhostArmadaVariable) {
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

  }
};
