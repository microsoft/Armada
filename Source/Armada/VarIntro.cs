using System.Collections.Generic;
using System.Linq;
using System;

namespace Microsoft.Armada
{
  public class VarIntroProofGenerator : AbstractProofGenerator
  {
    protected VariableIntroStrategyDecl strategy;
    protected HashSet<string> introducedVariables;
    protected Dictionary<ArmadaPC, ArmadaPC> reversePcMap;
    protected HashSet<ArmadaPC> newInstructionPCs;
    protected int pcCountHigh;
    protected Dictionary<ArmadaPC, ArmadaPC> endPcMap;

    public VarIntroProofGenerator(ProofGenerationParams i_pgp, VariableIntroStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      introducedVariables = new HashSet<string>();
      foreach (var tok in strategy.Variables) {
        introducedVariables.Add(tok.val);
      }
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-introduction strategy");
        return;
      }

      var differ = new ASTDiff(pgp.originalsHigh, pgp.originalsLow, true); // the mapping is exactly the opposite of hiding
      reversePcMap = differ.VariableHiding();
      ExtendReversePCMapWithExternalAndStructsMethods();
      GenerateAuxiliaryDataStructure();

      if (!CheckAllIntroducedAreUpdates()) {
        AH.PrintError(pgp.prog, "Higher level introduced non-update instructions, which is not supported");
        return;
      }

      AddIncludesAndImports();

      ExtendPCMapWithExternalAndStructsMethods();
      GenerateNextRoutineMap();

      GenerateProofGivenMap();
    }

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

    protected override bool CheckVariableNameListEquivalence(IEnumerable<string> varNames_l, IEnumerable<string> varNames_h,
                                                    ArmadaSingleMethodSymbolTable s_l, ArmadaSingleMethodSymbolTable s_h,
                                                    string methodName, string descriptor)
    {
      var vars_l = varNames_l.ToArray();
      var vars_h = varNames_h.ToArray();
      if (vars_l.Length > vars_h.Length) {
        AH.PrintError(pgp.prog, $"Method {methodName} has {vars_l.Length} {descriptor} variables in level {pgp.mLow.Name} but {vars_h.Length} of them in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < vars_l.Length; ++i) {
        var name_l = vars_l[i];
        var name_h = vars_h[i];
        if (name_l != name_h) {
          AH.PrintError(pgp.prog, $"In method {methodName}, {descriptor} variable number {i+1} is named {name_l} in level {pgp.mLow.Name} but named {name_h} in level {pgp.mHigh.Name}");
          return false;
        }
        var v_l = s_l.LookupVariable(name_l);
        var v_h = s_h.LookupVariable(name_h);
        if (!AH.TypesMatch(v_l.ty, v_h.ty)) {
          AH.PrintError(pgp.prog, $"In method {methodName}, the {descriptor} variable named {name_l} has type {v_l.ty} in level {pgp.mLow.Name} but type {v_h.ty} in level {pgp.mHigh.Name}");
          return false;
        }
      }

      return true;
    }

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/varintro/VarIntro.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/MapSum.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("VarIntroSpecModule");
      pgp.MainProof.AddImport("VarIntroModule");
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

    private void ExtendReversePCMapWithExternalAndStructsMethods()
    {
      foreach (var methodName in pgp.symbolsHigh.MethodNames) {
        var st = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
        if (st.IsExternal || st.IsFromStructsModule) {
          List<ArmadaPC> allPCs = new List<ArmadaPC>();
          pgp.symbolsHigh.AllMethods.LookupMethod(methodName).AppendAllPCs(allPCs);
          foreach (var pc in allPCs) {
            reversePcMap[pc] = pc;
          }
        }
      }
    }

    protected void GenerateAuxiliaryDataStructure() {
      pcMap = new Dictionary<ArmadaPC, ArmadaPC>();
      endPcMap = new Dictionary<ArmadaPC, ArmadaPC>();
      newInstructionPCs = new HashSet<ArmadaPC>();

      foreach (var entry in reversePcMap) {
        ++ pcCountHigh;
        if (pcMap.ContainsKey(entry.Value)) {
          // there is a previously-mapped PC to the same PC
          /*
           * L.Main_4 --- H.Main_6
           *  (stmt)       (stmt)
           *            / H.Main_7    -- newInstructionPC/endPC
           *             (new_stmt)
           * L.Main_5 --- H.Main_8
           *             (new_stmt)   -- newInstructionPC
           *            \ H.Main_9
           *  (stmt)       (stmt)
           * L.Main_6 --- H.Main_10
           */
          if (entry.Key.instructionCount > pcMap[entry.Value].instructionCount) {
            // new PC occurs after the previously-mapped one
            newInstructionPCs.Add(pcMap[entry.Value]);
            pcMap[entry.Value] = entry.Key;
          }
          else {
            // new PC occurs before the previously-mapped one
            newInstructionPCs.Add(entry.Key);
          }
          if (entry.Key.instructionCount < endPcMap[entry.Value].instructionCount) {
            endPcMap[entry.Value] = entry.Key;
          }
        }
        else {
          pcMap[entry.Value] = entry.Key;
          endPcMap[entry.Value] = entry.Key;
        }
      }
    }

    private ArmadaPC LowerPC(ArmadaPC pc)
    {
      if (pc == null) {
        return null;
      }
      return reversePcMap[pc];
    }

    protected override void GenerateNextRoutineMap(bool warnOnMissingRoutines = true)
    {
      var hmap = new Dictionary<Tuple<ArmadaPC, ArmadaPC>, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        var startPC = LowerPC(nextRoutine.pc);
        var endPC = LowerPC(nextRoutine.endPC);
        var t = new Tuple<ArmadaPC, ArmadaPC>(startPC, endPC);

        // If more than one high-level next routine maps to the same low-level startPC/endPC combination,
        // use the one earlier in its method.
        
        if (!hmap.ContainsKey(t) || nextRoutine.pc.instructionCount < hmap[t].pc.instructionCount) {
          hmap[t] = nextRoutine;
        }
      }

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var t = new Tuple<ArmadaPC, ArmadaPC>(nextRoutine.pc, nextRoutine.endPC);
        if (hmap.ContainsKey(t)) {
          nextRoutineMap[nextRoutine] = hmap[t];
        }
        else if (warnOnMissingRoutines) {
          AH.PrintWarning(pgp.prog, $"No next routine found in high level from {nextRoutine.pc} to {nextRoutine.endPC}");
        }
      }
    }

    protected bool CheckAllIntroducedAreUpdates() {
      foreach (var routine in pgp.symbolsHigh.NextRoutines) {
        if (routine.nextType == NextType.Return && newInstructionPCs.Contains(routine.armadaStatement.StartPC)) {
          return false;
        }
      }
      return true;
    }

    protected void GenerateProofGivenMap() {
      GenerateProofHeader();
      GenerateLOneStepSpec(false);
      GenerateHOneStepSpec();
      // the state conversion functions are required from H to L
      GenerateStateAbstractionFunctions_HL(reversePcMap);
      // the step conversion functions are required from L to H
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateValidStepLemmas();

      GenerateVarIntroRequest();
      GenerateOnlyIntroducedAssignmentsBeforeYielding();
      GenerateLemmasAboutPCs();
      GenerateLemmasAboutMultisteps();
      GenerateFinalProof();
    }

    protected override void GenerateConvertGlobals_HL()
    {
      var g = AH.MakeNameSegment("globals", "H.Armada_Globals");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("L.Armada_Globals", ps, "L.Armada_Globals");
      var formals = new List<Formal> { AH.MakeFormal("globals", "H.Armada_Globals") };
      var fn = AH.MakeFunction("ConvertGlobals_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertGhosts_HL()
    {
      var g = AH.MakeNameSegment("ghosts", "H.Armada_Ghosts");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalGhostArmadaVariable) {
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("L.Armada_Ghosts", ps, "L.Armada_Ghosts");
      var formals = new List<Formal> { AH.MakeFormal("ghosts", "H.Armada_Ghosts") };
      var fn = AH.MakeFunction("ConvertGhosts_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }


    protected override void GenerateConvertGlobalStaticVar_HL()
    {
      var v = AH.MakeNameSegment("v", "H.Armada_GlobalStaticVar");
      var es = new List<Expression>();
      foreach (var varName in introducedVariables) {
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          var e = AH.MakeNotExpr(AH.MakeExprDotName(v, $"Armada_GlobalStaticVar_{varName}?", new BoolType()));
          es.Add(e);
        }
      }
      var body = AH.CombineExpressionsWithAnd(es);
      var formals = new List<Formal> { AH.MakeFormal("v", "H.Armada_GlobalStaticVar") };
      var pred = AH.MakePredicate("CanConvertGlobalStaticVar_HL", formals, body);
      pgp.AddDefaultClassDecl(pred, "convert");

      var cases = new List<MatchCaseExpr>();
      var case_body = AH.MakeNameSegment("L.Armada_GlobalStaticVarNone", "L.Armada_GlobalStaticVar");
      cases.Add(AH.MakeMatchCaseExpr("Armada_GlobalStaticVarNone", case_body));
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
          continue;
        }
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          case_body = AH.MakeNameSegment($"L.Armada_GlobalStaticVar_{varName}", "L.Armada_GlobalStaticVar");
          cases.Add(AH.MakeMatchCaseExpr($"Armada_GlobalStaticVar_{varName}", case_body));
        }
      }
      body = AH.MakeMatchExpr(v, cases, "L.Armada_GlobalStaticVar");
      var req = AH.MakeApply1("CanConvertGlobalStaticVar_HL", v, new BoolType());
      var fn = AH.MakeFunctionWithReq("ConvertGlobalStaticVar_HL", formals, req, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertStackFrame_LH()
    {
      var cases = new List<MatchCaseExpr>();
      var methodNames = pgp.symbolsLow.MethodNames;
      foreach (var methodName in methodNames) {
        var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        var ps = new List<Expression>();
        var bvs = new List<BoundVar>();
        foreach (var v in smst.AllVariablesInOrder) {
          var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
          var e = AH.MakeNameSegment(v.FieldName, ty);
          ps.Add(e);
          var bv = AH.MakeBoundVar(v.FieldName, v.GetFlattenedType(pgp.symbolsLow));
          bvs.Add(bv);
        }
        var case_body = AH.MakeApplyN($"H.Armada_StackFrame_{methodName}", ps, "H.Armada_StackFrame");
        cases.Add(AH.MakeMatchCaseExpr($"Armada_StackFrame_{methodName}", bvs, case_body));
      }

      var source = AH.MakeNameSegment("frame", "L.Armada_StackFrame");
      var body = AH.MakeMatchExpr(source, cases, "H.Armada_StackFrame");
      var formals = new List<Formal> { AH.MakeFormal("frame", "L.Armada_StackFrame") };
      var fn = AH.MakeFunction("ConvertStackFrame_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }


    // TODO: proof-read this part, it looks extremely fragile
    protected void GenerateReturnToPC_HL()
    {
      var cases = new List<MatchCaseExpr>();
      Expression case_body;

      HashSet<ArmadaPC> remainingHighPCs = new HashSet<ArmadaPC>(reversePcMap.Select(p => p.Key));

      foreach (var mapping in endPcMap) {
        case_body = AH.MakeNameSegment($"L.{mapping.Key}", "L.Armada_PC");
        cases.Add(AH.MakeMatchCaseExpr(mapping.Value.ToString(), case_body));
        remainingHighPCs.Remove(mapping.Value);
      }

      foreach (var pc in remainingHighPCs) {
        case_body = AH.MakeNameSegment("L." + new ArmadaPC(pgp.symbolsLow, "main", 0).ToString(), "L.Armada_PC");
        cases.Add(AH.MakeMatchCaseExpr(pc.ToString(), case_body));
      }

      var source = AH.MakeNameSegment("pc", "H.Armada_PC");
      var body = AH.MakeMatchExpr(source, cases, "L.Armada_PC");
      var formals = new List<Formal> { AH.MakeFormal("pc", "H.Armada_PC") };
      var fn = AH.MakeFunction("ConvertReturnToPC_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertExtendedFrame_HL()
    {
      string str = @"
        function ConvertExtendedFrame_HL(eframe:H.Armada_ExtendedFrame) : L.Armada_ExtendedFrame
        {
          L.Armada_ExtendedFrame(ConvertReturnToPC_HL(eframe.return_pc), ConvertStackFrame_HL(eframe.frame), eframe.new_ptrs)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBufferLocation_HL()
    {
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

    protected override void GenerateConvertStoreBufferEntry_HL()
    {
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
          L.Armada_StoreBufferEntry(ConvertStoreBufferLocation_HL(entry.loc), entry.value)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBuffer_HL()
    {
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

    // TODO (Luke): more cases
    protected Expression ResolveInit(Expression expr) {
      if (expr is LiteralExpr lit) {
        if (lit.Value == null) {
          return new LiteralExpr(Boogie.Token.NoToken, 0);
        }
      }

      return expr;
    }

    protected override void GenerateConvertGlobals_LH()
    {
      var g = AH.MakeNameSegment("globals", "L.Armada_Globals");
      var ps = new List<Expression>();
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
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Globals", ps, "H.Armada_Globals");
      var formals = new List<Formal> { AH.MakeFormal("globals", "L.Armada_Globals") };
      var fn = AH.MakeFunction("ConvertGlobals_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertGhosts_LH()
    {
      var ghosts = AH.MakeNameSegment("ghosts", "L.Armada_Ghosts");
      var ps = new List<Expression>();
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
          var p = AH.MakeExprDotName(ghosts, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Ghosts", ps, "H.Armada_Ghosts");
      var formals = new List<Formal> { AH.MakeFormal("ghosts", "L.Armada_Ghosts") };
      var fn = AH.MakeFunction("ConvertGhosts_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    // VarIntro specific functions

    protected virtual void GenerateNewInstructionPC_H() {
      var hs = AH.MakeNameSegment("hs", "HState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var threads = AH.MakeExprDotName(hs, "threads", "map<Armada_ThreadHandle, H.Armada_Thread");
      var thread = AH.MakeSeqSelectExpr(threads, tid, "H.Armada_Thread");
      var pc = AH.MakeExprDotName(thread, "pc", "H.Armada_PC");
      var cases = new List<MatchCaseExpr>();
      Expression case_body;

      foreach (var mapping in reversePcMap) {
        if (newInstructionPCs.Contains(mapping.Key)) {
          case_body = AH.MakeNameSegment("true", "bool");
        }
        else {
          case_body = AH.MakeNameSegment("false", "bool");
        };
        cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
      }

      var body = AH.MakeMatchExpr(pc, cases, "bool");
      var formals = new List<Formal> { AH.MakeFormal("hs", "HState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
      var req = AH.MakeInExpr(tid, threads);
      var fn = AH.MakePredicateWithReq("NewInstructionPC_H", formals, req, body);
      pgp.MainProof.AddDefaultClassDecl(fn);
    }

    protected void GenerateNewTSOInstruction_H() {
      var cases = new List<MatchCaseExpr>();
      Expression case_body;
      foreach (var routine in pgp.symbolsHigh.NextRoutines) {
        var routine_params = String.Join("", routine.Formals.Select(f => $", _"));
        if (routine.nextType is NextType.Update) {
          if (((ArmadaUpdateStatement)(routine.armadaStatement)).GenuineTSO &&
              newInstructionPCs.Contains(routine.pc)) {
            case_body = AH.MakeNameSegment("true", "bool");
          }
          else {
            case_body = AH.MakeNameSegment("false", "bool");
          }
        }
        else {
          case_body = AH.MakeNameSegment("false", "bool");
        }
        cases.Add(AH.MakeMatchCaseExpr($"Armada_TraceEntry_{routine.NameSuffix}(_{routine_params})", case_body));
      }

      var source = AH.MakeNameSegment("hstep", "H.Armada_TraceEntry");
      var body = AH.MakeMatchExpr(source, cases, "bool");
      var formals = new List<Formal> { AH.MakeFormal("hstep", "H.Armada_TraceEntry") };
      var fn = AH.MakePredicate("NewTSOInstruction_H", formals, body);
      pgp.MainProof.AddDefaultClassDecl(fn);
    }

    protected void GenerateNewInstructionThread_H() {
      string str = @"
        predicate NewInstructionThread_H(s:H.Armada_TotalState, tid:Armada_ThreadHandle)
        {
          && s.stop_reason.Armada_NotStopped?
          && tid in s.threads
          && NewInstructionPC_H(s, tid)
        }
      ";

      pgp.AddPredicate(str);
    }

    protected void GenerateNewInstructionStoreBufferEntries_H() {
      string str = @"
        predicate NewInstructionStoreBufferEntries_H(entries: seq<H.Armada_StoreBufferEntry>)
        {
          |entries| > 0 && !CanConvertStoreBufferEntry_HL(entries[0])
        }
      ";

      pgp.AddPredicate(str);
    }

    protected void GenerateNextStepThread_H() {
      var cases = new List<MatchCaseExpr>();
      var s = AH.MakeNameSegment("s", "Armada_TotalState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      foreach (var routine in pgp.symbolsHigh.NextRoutines) {
        if (routine.nextType == NextType.Update && newInstructionPCs.Contains(routine.pc)) {
          // TODO: this does not work with introduced statements with *
          var case_body = AH.MakeApply1($"H.Armada_TraceEntry_{routine.NameSuffix}", tid, "H.Armada_TraceEntry");
          cases.Add(AH.MakeMatchCaseExpr(routine.pc.ToString(), case_body));
        }
      }

      var pc = AH.MakeExprDotName(thread, "pc", "H.Armada_PC");
      var body = AH.MakeMatchExpr(pc, cases, "H.Armada_TraceEntry");

      var formals = new List<Formal> { AH.MakeFormal("s", "H.Armada_TotalState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
      var req = AH.MakeApply2("NewInstructionThread_H", s, tid, new BoolType());
      var fn = AH.MakeFunctionWithReq("NextStepThread_H", formals, req, body);
      pgp.MainProof.AddDefaultClassDecl(fn);
    }

    protected void GenerateProgressMeasureThread_H() {
      var cases = new List<MatchCaseExpr>();
      Expression case_body;

      foreach (var mapping in reversePcMap) {
        if (newInstructionPCs.Contains(mapping.Key)) {
          case_body = AH.MakeNameSegment(((pcCountHigh - mapping.Key.instructionCount) * 2).ToString(), "int");
          cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
        }
        else {
          case_body = AH.MakeNameSegment("0", "int");
          cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
        }
      }

      var source = AH.MakeNameSegment("thread.pc", "H.Armada_PC");
      var body = AH.MakeMatchExpr(source, cases, new IntType());
      var formals = new List<Formal> { AH.MakeFormal("thread", "H.Armada_Thread") };
      var fn = AH.MakeFunction("ProgressMeasureThread_H", formals, body);
      pgp.MainProof.AddDefaultClassDecl(fn);
    }

    protected void GenerateProgressMeasureState_H()
    {
      string str = @"
        function ProgressMeasureState_H(s: HState, tid: Armada_ThreadHandle) : int
        {
          if tid in s.threads then ProgressMeasureThread_H(s.threads[tid]) else 0
        }
      ";
      pgp.AddFunction(str);
    }

    protected virtual void GenerateLemmasWhenAtNewInstructionNextStepMakesProgress() {
      string str;

      str = @"
        lemma lemma_AppendNewEntriesSame(buffer: seq<H.Armada_StoreBufferEntry>)
          ensures forall entries :: ConvertStoreBuffer_HL(entries) == [] ==> ConvertStoreBuffer_HL(buffer + entries) == ConvertStoreBuffer_HL(buffer)
        {
          forall entries | ConvertStoreBuffer_HL(entries) == []
            ensures ConvertStoreBuffer_HL(buffer + entries) == ConvertStoreBuffer_HL(buffer)
          {
            lemma_FilterMapSeqsToSeq(buffer, entries, ConvertStoreBufferEntryTotal_HL);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_WhenAtNewInstructionNextStepMakesProgress(
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry,
          tid: Armada_ThreadHandle
          )
          requires VarIntroInvariant(hs)
          requires hs.stop_reason.Armada_NotStopped?
          requires tid in hs.threads
          requires NewInstructionThread_H(hs, tid)
          requires hstep == NextStepThread_H(hs, tid)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          ensures  ConvertTotalState_HL(hs') == ConvertTotalState_HL(hs)
          ensures  H.Armada_NextOneStep(hs, hs', hstep)
          ensures  0 <= ProgressMeasureState_H(hs', tid) < ProgressMeasureState_H(hs, tid)
        {
          var threads := hs.threads;
          var new_threads := hs'.threads;
          assert forall tid' :: tid' in threads && tid' != tid ==> threads[tid'] == new_threads[tid'];
          assert ConvertThread_HL(new_threads[tid]) == ConvertThread_HL(threads[tid]) ==> ConvertThreads_HL(new_threads) == ConvertThreads_HL(threads);
          if NewTSOInstruction_H(hstep) {
            var entries := hs'.threads[tid].storeBuffer[|hs.threads[tid].storeBuffer|..];
            assert forall entry :: entry in entries ==> ConvertStoreBufferEntryTotal_HL(entry).None?;
            FilterMapSeqToSeq_FilterEmpty(entries, ConvertStoreBufferEntryTotal_HL);
            assert ConvertStoreBuffer_HL(entries) == [];
            assert new_threads[tid].storeBuffer == threads[tid].storeBuffer + entries;
            lemma_AppendNewEntriesSame(threads[tid].storeBuffer);
            assert ConvertStoreBuffer_HL(new_threads[tid].storeBuffer) == ConvertStoreBuffer_HL(threads[tid].storeBuffer);
          }
          assert ConvertTotalState_HL(hs) == ConvertTotalState_HL(hs');
          assert H.Armada_NextOneStep(hs, hs', hstep);
          assert 0 <= ProgressMeasureState_H(hs', tid) < ProgressMeasureState_H(hs, tid);
        }
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateLocalViewCommutativityLemmas()
    {
      string str;

      string cases = "";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (introducedVariables.Contains(varName)) {
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
          lglobals:H.Armada_Globals, lv:H.Armada_GlobalStaticVar, fields:seq<Armada_Field>, value:Armada_PrimitiveValue,
          hv:L.Armada_GlobalStaticVar, hglobals1:L.Armada_Globals, hglobals2:L.Armada_Globals)
          requires CanConvertGlobalStaticVar_HL(lv)
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
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem:H.Armada_SharedMemory, lentry:H.Armada_StoreBufferEntry)
          requires !CanConvertStoreBufferEntry_HL(lentry)
          ensures  ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lentry)) == ConvertSharedMemory_HL(lmem)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem:H.Armada_SharedMemory, lentry:H.Armada_StoreBufferEntry,
                                                             hentry:L.Armada_StoreBufferEntry, hmem1:L.Armada_SharedMemory,
                                                             hmem2:L.Armada_SharedMemory)
          requires CanConvertStoreBufferEntry_HL(lentry)
          requires hentry == ConvertStoreBufferEntry_HL(lentry)
          requires hmem1 == ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lentry))
          requires hmem2 == L.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_HL(lmem), hentry)
          ensures  hmem1 == hmem2
        {
          match lentry.loc
            case Armada_StoreBufferLocation_Unaddressable(lv, lfields) =>
            {
              var hv := ConvertGlobalStaticVar_HL(lv);
              lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(lmem.globals, lv, lfields, lentry.value, hv, hmem1.globals,
                                                                          hmem2.globals);
            }
            case Armada_StoreBufferLocation_Addressable(p) =>
            {
            }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyStoreBufferCommutesWithConvert(lmem:H.Armada_SharedMemory, lbuf:seq<H.Armada_StoreBufferEntry>,
                                                        hbuf:seq<L.Armada_StoreBufferEntry>, hmem1:L.Armada_SharedMemory,
                                                        hmem2:L.Armada_SharedMemory)
          requires hbuf == ConvertStoreBuffer_HL(lbuf)
          requires hmem1 == ConvertSharedMemory_HL(H.Armada_ApplyStoreBuffer(lmem, lbuf))
          requires hmem2 == L.Armada_ApplyStoreBuffer(ConvertSharedMemory_HL(lmem), hbuf)
          ensures  hmem1 == hmem2
          decreases |lbuf| + |hbuf|
        {
          if |lbuf| == 0 {
              return;
          }

          var lmem' := H.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]);

          if CanConvertStoreBufferEntry_HL(lbuf[0]) {
              var hmem1' := ConvertSharedMemory_HL(H.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
              var hmem2' := L.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_HL(lmem), hbuf[0]);
              lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
          }
          else {
              lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem, lbuf[0]);
              assert ConvertSharedMemory_HL(lmem') == ConvertSharedMemory_HL(lmem);
              assert hbuf == ConvertStoreBuffer_HL(lbuf[1..]);
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf, hmem1, hmem2);
          }
        }
      ";
      pgp.AddLemma(str);

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
      pgp.AddLemma(str);

      str = @"
        lemma lemma_GetThreadLocalViewAlwaysCommutesWithConvert()
          ensures forall ls:H.Armada_TotalState, tid:Armada_ThreadHandle :: tid in ls.threads ==>
                    ConvertSharedMemory_HL(H.Armada_GetThreadLocalView(ls, tid)) == L.Armada_GetThreadLocalView(ConvertTotalState_HL(ls), tid)
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
      pgp.AddLemma(str);

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
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)} :: CanConvertStoreBufferEntry_HL(lentry) ==> L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) == ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<H.Armada_StoreBufferEntry>, lentry: H.Armada_StoreBufferEntry {:trigger H.Armada_StoreBufferAppend(lbuf, lentry)}
            | CanConvertStoreBufferEntry_HL(lentry)
            ensures L.Armada_StoreBufferAppend(ConvertStoreBuffer_HL(lbuf), ConvertStoreBufferEntry_HL(lentry)) == ConvertStoreBuffer_HL(H.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
      ";
      pgp.AddLemma(str);

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
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid:Armada_ThreadHandle)
          ensures forall s:H.Armada_TotalState, entry:H.Armada_StoreBufferEntry {:trigger H.Armada_AppendToThreadStoreBuffer(s, tid, entry)} ::
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
      pgp.AddLemma(str);
    }

    protected override void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{TranslateFormalNameUsingPcMap(f, nextRoutine.pc, pcMap)}"));

      var hNextRoutineName = LiftNextRoutine(nextRoutine).NameSuffix;

      string optionalRequires = "";
      string optionalProof = "";

      if (nextRoutine.nextType == NextType.Call || nextRoutine.nextType == NextType.Return ||
          nextRoutine.nextType == NextType.Update) {
        optionalProof = "assert ls'.threads[tid] == ConvertTotalState_HL(hs').threads[tid];";
      }
      else if (nextRoutine.nextType == NextType.Terminate) {
        optionalRequires = "requires !(hs.stop_reason.Armada_NotStopped? && lstep.tid in hs.threads && NewInstructionStoreBufferEntries_H(hs.threads[lstep.tid].storeBuffer))";
      }

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(
            ls:LState,
            ls':LState,
            lstep:L.Armada_TraceEntry,
            hs:HState,
            hs':HState,
            hstep:H.Armada_TraceEntry
            )
            {optionalRequires}
            requires !NewInstructionThread_H(hs, lstep.tid)
            requires L.Armada_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires ls == ConvertTotalState_HL(hs)
            ensures  H.Armada_NextOneStep(hs, hs', hstep)
            ensures  ls' == ConvertTotalState_HL(hs')
        {{
            var tid := lstep.tid;

            lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
            lemma_StoreBufferAppendAlwaysCommutesWithConvert();
            assert H.Armada_ValidStep_{hNextRoutineName}(hs, tid{hstep_params});
            if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(ls, tid{lstep_params}) {{
              {optionalProof}
              assert H.Armada_UndefinedBehaviorAvoidance_{hNextRoutineName}(hs, tid{hstep_params});
              var alt_hs' := H.Armada_GetNextState_{hNextRoutineName}(hs, tid{hstep_params});
              assert hs'.stop_reason == alt_hs'.stop_reason;
              if tid in hs'.threads {{
                assert hs'.threads[tid] == alt_hs'.threads[tid];
              }}
              assert hs'.threads == alt_hs'.threads;
              assert hs'.mem == alt_hs'.mem;
              assert hs' == alt_hs';
              assert H.Armada_Next_{hNextRoutineName}(hs, hs', tid{hstep_params});
            }}
            else {{
              assert !H.Armada_UndefinedBehaviorAvoidance_{hNextRoutineName}(hs, tid{hstep_params});
            }}
        }}
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateLiftStepLemmaForTauNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftNext_Tau(
            ls:LState,
            ls':LState,
            lstep:L.Armada_TraceEntry,
            hs:HState,
            hs':HState,
            hstep:H.Armada_TraceEntry
            )
            requires !(hs.stop_reason.Armada_NotStopped? && lstep.tid in hs.threads && NewInstructionStoreBufferEntries_H(hs.threads[lstep.tid].storeBuffer))
            requires L.Armada_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires ls == ConvertTotalState_HL(hs)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            ensures  H.Armada_NextOneStep(hs, hs', hstep)
            ensures  ls' == ConvertTotalState_HL(hs')
        {{
            var tid := lstep.tid;

            var lentry := ls.threads[tid].storeBuffer[0];
            assert H.Armada_ValidStep_{nextRoutineName}(hs, tid{hstep_params});
            assert H.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(hs, tid{hstep_params});
            var hentry := hs.threads[tid].storeBuffer[0];

            var alt_hs' := H.Armada_GetNextState_{nextRoutineName}(hs, tid{hstep_params});
            assert hs' == alt_hs';
            assert H.Armada_Next_{nextRoutineName}(hs, hs', tid{hstep_params});
        }}
      ";

      pgp.AddLemma(str);
    }

    protected override void GenerateLiftStepLemmas()
    {
      var finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType == NextType.Tau) {
          GenerateLiftStepLemmaForTauNextRoutine(nextRoutine);
        }
        else {
          GenerateLiftStepLemmaForNormalNextRoutine(nextRoutine);
        }
        var nextRoutineName = nextRoutine.NameSuffix;
        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LiftNext_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep);";
      }

      string str = $@"
        lemma lemma_LiftActionWithoutVariable(
            ls:LState,
            ls':LState,
            lstep:L.Armada_TraceEntry,
            hs:HState,
            hs':HState,
            hstep:H.Armada_TraceEntry
            )
            requires lstep.Armada_TraceEntry_Tau? || IsTerminatingStep_L(lstep) ==>
                       !(hs.stop_reason.Armada_NotStopped? && lstep.tid in hs.threads && NewInstructionStoreBufferEntries_H(hs.threads[lstep.tid].storeBuffer))
            requires !lstep.Armada_TraceEntry_Tau? ==> !NewInstructionThread_H(hs, lstep.tid)
            requires L.Armada_NextOneStep(ls, ls', lstep)
            requires ls == ConvertTotalState_HL(hs)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            ensures  H.Armada_NextOneStep(hs, hs', hstep)
            ensures  ls' == ConvertTotalState_HL(hs')
        {{
          match lstep {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    protected void GenerateIntroSatisfiesRelation()
    {
      string str = @"
        lemma lemma_IntroSatisfiesRelation(hs: HState)
          ensures  RefinementPair(ConvertTotalState_HL(hs), hs) in GetLHRefinementRelation()
        {
        }
      ";
      pgp.AddLemma(str);
    }

    protected void GenerateIntroPreservesInit()
    {
      string str = @"
        lemma lemma_IntroPreservesInit(ls:LPlusState, hs:HState)
          requires ls in GetLPlusSpec().init
          requires hs == ConvertTotalState_LPlusH(ls)
          ensures  hs in GetHSpec().init
          ensures  ConvertTotalState_HL(hs) == ls.s
          ensures  VarIntroInvariant(hs)
        {
          var hconfig := ConvertConfig_LH(ls.config);
          assert H.Armada_InitConfig(hs, hconfig);
          var ls_alt := ConvertTotalState_HL(hs);
          assert forall tid :: tid in ls.s.threads ==> ls.s.threads[tid] == ls_alt.threads[tid];
          lemma_VarIntroInvariantHoldsAtInit(hs, hconfig);
        }
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateVarIntroRequest()
    {
      // function generation

      GenerateReturnToPC_HL();

      GenerateVarIntroInvariant();
      GenerateVarIntroInvariantProof();

      GenerateNextState_H();
      GenerateNewInstructionPC_H();
      GenerateNewTSOInstruction_H();
      GenerateNewInstructionThread_H();
      GenerateNewInstructionStoreBufferEntries_H();

      GenerateNextStepThread_H();

      GenerateProgressMeasureThread_H();
      GenerateProgressMeasureState_H();

      // lemma generation

      GenerateLemmasWhenAtNewInstructionNextStepMakesProgress();

      GenerateLocalViewCommutativityLemmas();
      GenerateLiftStepLemmas();
      GenerateIntroSatisfiesRelation();
      GenerateIntroPreservesInit();
    }

    protected virtual void GenerateVarIntroInvariant()
    {
      string str;

      GeneratePCStackFrameRel_H();

      str = $@"
        predicate VarIntroInvariant(s:HState)
        {{
          forall tid :: tid in s.threads ==> PCStackFrameRel_H(s, tid)
        }}
      ";
      pgp.AddPredicate(str);
    }

    protected virtual void GeneratePCStackFrameRel_H() {
      var hs = AH.MakeNameSegment("hs", "HState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var threads = AH.MakeExprDotName(hs, "threads", "map<Armada_ThreadHandle, H.Armada_Thread");
      var thread = AH.MakeSeqSelectExpr(threads, tid, "H.Armada_Thread");
      var pc = AH.MakeExprDotName(thread, "pc", "H.Armada_PC");
      var cases = new List<MatchCaseExpr>();
      Expression case_body;

      foreach (var mapping in reversePcMap) {
        case_body = AH.MakeExprDotName(thread, $"top.Armada_StackFrame_{mapping.Key.methodName}?", "bool");
        cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
      }

      var body = AH.MakeMatchExpr(pc, cases, "bool");
      var formals = new List<Formal> { AH.MakeFormal("hs", "HState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
      var req = AH.MakeInExpr(tid, threads);
      var fn = AH.MakePredicateWithReq("PCStackFrameRel_H", formals, req, body);
      pgp.MainProof.AddDefaultClassDecl(fn);
    }

    protected void GenerateVarIntroInvariantProof()
    {
      string str;

      str = @"
        lemma lemma_VarIntroInvariantHoldsAtInit(s: HState, config:H.Armada_Config)
          requires H.Armada_InitConfig(s, config)
          ensures  VarIntroInvariant(s)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_VarIntroInvariantPreservedByNext(s:HState, s':HState, step:H.Armada_TraceEntry)
          requires VarIntroInvariant(s)
          requires H.Armada_NextOneStep(s, s', step)
          ensures  VarIntroInvariant(s')
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private HashSet<ArmadaPC> ComputePCsWithOnlyIntroducedAssignmentsBeforeYielding()
    {
      var allPCsList = new List<ArmadaPC>();
      pgp.symbolsHigh.AllMethods.AppendAllPCs(allPCsList);

      var nonyieldingPCsList = new List<ArmadaPC>();
      pgp.symbolsHigh.AllMethods.AppendAllNonyieldingPCs(nonyieldingPCsList);
      var nonyieldingPCs = new HashSet<ArmadaPC>(nonyieldingPCsList);

      var onlyIntroducedAssignmentsBeforeYieldingPCs = new HashSet<ArmadaPC>();

      // Start out by enumerating all the PCs that yield, i.e., the
      // ones that are among all PCs but not among the nonyielding
      // ones.  Obviously, these PCs don't have any introduced assignments
      // before yielding.

      foreach (var pc in allPCsList) {
        if (!nonyieldingPCs.Contains(pc)) {
          onlyIntroducedAssignmentsBeforeYieldingPCs.Add(pc);
        }
      }

      // Compute a list of all introduced assignments' next routines.
      // This will be useful for the next step.

      var introducedNextRoutines = new List<NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        if (nextRoutine.nextType is NextType.Update && newInstructionPCs.Contains(nextRoutine.stmt.Parsed.StartPC)) {
          introducedNextRoutines.Add(nextRoutine);
        }
      }

      // For each introduced next routine, if its end PC is among the
      // PCs we've computed so far, put its start PC into the list.
      // Keep doing this until we have an iteration through all
      // introduced next routines that doesn't add any new PC to our
      // to-be-returned set.

      bool done = false;
      while (!done) {
        done = true;
        foreach (var nextRoutine in introducedNextRoutines) {
          if (onlyIntroducedAssignmentsBeforeYieldingPCs.Contains(nextRoutine.stmt.Parsed.EndPC) &&
              !onlyIntroducedAssignmentsBeforeYieldingPCs.Contains(nextRoutine.stmt.Parsed.StartPC)) {
            onlyIntroducedAssignmentsBeforeYieldingPCs.Add(nextRoutine.stmt.Parsed.StartPC);
            done = false;
          }
        }
      }

      return onlyIntroducedAssignmentsBeforeYieldingPCs;
    }

    private void GenerateOnlyIntroducedAssignmentsBeforeYielding()
    {
      HashSet<ArmadaPC> onlyIntroducedAssignmentsBeforeYieldingPCs = ComputePCsWithOnlyIntroducedAssignmentsBeforeYielding();

      string str;

      str = @"
        predicate OnlyIntroducedAssignmentsBeforeYielding(pc:H.Armada_PC)
        {
      ";
      foreach (var pc in onlyIntroducedAssignmentsBeforeYieldingPCs) {
        str += $"    || pc.{pc}?\n";
      }
      str += "  }\n";
      pgp.AddPredicate(str);

      str = @"
        lemma lemma_RegularStepMakingLowYieldingMakesHighOnlyIntroducedAssignmentsBeforeYielding(
          ls: LState,
          ls': LState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires L.Armada_NextOneStep(ls, ls', lstep)
          requires hs == ConvertTotalState_LH(ls)
          requires hs' == ConvertTotalState_LH(ls')
          requires !lstep.Armada_TraceEntry_Tau?
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires Armada_ThreadYielding(L.Armada_GetSpecFunctions(), ls', lstep.tid)
          ensures  Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs', hstep.tid) || OnlyIntroducedAssignmentsBeforeYielding(hs'.threads[hstep.tid].pc)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_OnlyIntroducedAssignmentsBeforeYielding(s: HState, tid:Armada_ThreadHandle)
          requires tid in s.threads
          requires OnlyIntroducedAssignmentsBeforeYielding(s.threads[tid].pc)
          requires H.Armada_IsNonyieldingPC(s.threads[tid].pc)
          ensures  NewInstructionPC_H(s, tid)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_YieldPointMapsToYieldPoint(pc:H.Armada_PC)
          ensures  !H.Armada_IsNonyieldingPC(pc) ==> !L.Armada_IsNonyieldingPC(ConvertPC_HL(pc))
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_TerminatingPCCorrespondsToOnlyIntroducedAssignmentsBeforeYielding(
          ls: LState,
          ls': LState,
          lstep: L.Armada_TraceEntry,
          hs:HState
          )
          requires L.Armada_NextOneStep(ls, ls', lstep)
          requires IsTerminatingStep_L(lstep)
          requires ls == ConvertTotalState_HL(hs)
          ensures  lstep.tid in hs.threads
          ensures  OnlyIntroducedAssignmentsBeforeYielding(hs.threads[lstep.tid].pc)
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasAboutPCs()
    {
      string str;

      str = @"
        predicate IsTerminatingStep_L(step:L.Armada_TraceEntry)
        {
      ";
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType == NextType.Terminate) {
          str += $"    || step.Armada_TraceEntry_{nextRoutine.NameSuffix}?\n";
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str);

      str = @"
        lemma lemma_TerminatingStepStartsAtYieldingPoint(s:LState, s':LState, step:L.Armada_TraceEntry)
          requires L.Armada_NextOneStep(s, s', step)
          requires IsTerminatingStep_L(step)
          ensures  step.tid in s.threads
          ensures  !L.Armada_IsNonyieldingPC(s.threads[step.tid].pc)
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasAboutMultisteps()
    {
      string str;

      str = @"
        lemma lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(s:HState, s':HState, step:H.Armada_TraceEntry, tid:Armada_ThreadHandle)
          requires s' == H.Armada_GetNextStateAlways(s, step)
          requires tid != step.tid
          requires Armada_ThreadYielding(H.Armada_GetSpecFunctions(), s, tid)
          ensures  Armada_ThreadYielding(H.Armada_GetSpecFunctions(), s', tid)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ExecutingTauDoesntChangeThreadYielding_H(s:HState, s':HState, step:H.Armada_TraceEntry, tid:Armada_ThreadHandle)
          requires s' == H.Armada_GetNextStateAlways(s, step)
          requires step.Armada_TraceEntry_Tau?
          requires Armada_ThreadYielding(H.Armada_GetSpecFunctions(), s, tid)
          ensures  Armada_ThreadYielding(H.Armada_GetSpecFunctions(), s', tid)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_OnlyFirstStepOfMultistepCanBeTau(
          ls: LState,
          ls': LState,
          lmultistep: LStep,
          pos:int
          )
          requires L.Armada_Next(ls, ls', lmultistep)
          requires 0 <= pos < |lmultistep.steps|
          requires lmultistep.steps[pos].Armada_TraceEntry_Tau?
          ensures  pos == 0
        {
          assert forall step :: step in lmultistep.steps ==> step.Armada_TraceEntry_Tau? == lmultistep.tau;
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_NextMultipleStepsImpliesValidStep(s: LState, s': LState, steps:seq<L.Armada_TraceEntry>, states:seq<LState>, pos:int)
          requires Armada_NextMultipleSteps(L.Armada_GetSpecFunctions(), s, s', steps)
          requires states == Armada_GetStateSequence(L.Armada_GetSpecFunctions(), s, steps)
          requires 0 <= pos < |steps|
          ensures  L.Armada_ValidStep(states[pos], steps[pos])
          decreases pos
        {
          if pos > 0 {
            lemma_NextMultipleStepsImpliesValidStep(states[1], s', steps[1..], states[1..], pos-1);
          }
        }
      ";

      pgp.AddLemma(str);

      str = @"
        lemma lemma_OnlyFirstStepOfMultistepCanBeTerminate(
          ls: LState,
          ls': LState,
          lmultistep: LStep,
          pos:int
          )
          requires L.Armada_Next(ls, ls', lmultistep)
          requires 0 <= pos < |lmultistep.steps|
          requires IsTerminatingStep_L(lmultistep.steps[pos])
          ensures  pos == 0
        {
          if pos == 0 {
            return;
          }

          var ls_next := L.Armada_GetNextStateAlways(ls, lmultistep.steps[pos-1]);
          var tid := lmultistep.tid;
          var states := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), ls, lmultistep.steps);
          assert !Armada_ThreadYielding(L.Armada_GetSpecFunctions(), states[pos], tid);
          lemma_NextMultipleStepsImpliesValidStep(ls, ls', lmultistep.steps, states, pos);
          lemma_TerminatingStepStartsAtYieldingPoint(states[pos], states[pos+1], lmultistep.steps[pos]);
          assert false;
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str;

      str = @"
        lemma lemma_PerformVarIntroCaseRealTerminatingStep(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps != |lmultistep.steps|
          requires !(num_steps == 0 && |hsteps| == 0 && hs_current.stop_reason.Armada_NotStopped? && tid in hs_current.threads && NewInstructionStoreBufferEntries_H(hs_current.threads[tid].storeBuffer))
          requires !NewInstructionThread_H(hs_current, tid)
          requires IsTerminatingStep_L(lmultistep.steps[num_steps])
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var prev := pos - 1;
          var ls := lb.states[prev];
          var hs := last(hb.states);
          var lmultistep := lb.trace[prev];
          var ls' := lb.states[pos];
          var tid := lmultistep.tid;
          var lstates := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), lb.states[pos-1].s, lmultistep.steps);

          assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
          lemma_LPlusNextMultipleStepsImpliesLNextMultipleSteps(ls, ls', lmultistep.steps);
          assert L.Armada_Next(ls.s, ls'.s, lmultistep);
          lemma_OnlyFirstStepOfMultistepCanBeTerminate(ls.s, ls'.s, lmultistep, num_steps);
          assert num_steps == 0;

          if |hsteps| > 0 {
            var ls_next := L.Armada_GetNextStateAlways(ls.s, lmultistep.steps[0]);
            lemma_TerminatingPCCorrespondsToOnlyIntroducedAssignmentsBeforeYielding(ls.s, ls_next, lmultistep.steps[0], hs_current);
            var j := |hstates|-1;
            assert !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[j], tid);
            assert !NewInstructionThread_H(hs_current, tid);
            lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);
            assert hs_current == hstates[j];
            assert false;
          }

          var lstep := lmultistep.steps[num_steps];
          var ls_next := LPlus_GetNextStateAlways(ls_current, lstep);
          assert LPlus_NextOneStep(ls_current, ls_next, lstep);
          var hstep := ConvertTraceEntry_LH(lstep);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);
          lemma_LiftActionWithoutVariable(ls_current.s, ls_next.s, lstep, hs_current, hs_next, hstep);

          assert H.Armada_NextOneStep(hs_current, hs_next, hstep);
          lemma_ExtendArmadaNextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_current, hs_next, hsteps, hstep);
          assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_next, hsteps + [hstep]);
          lemma_ExtendArmadaGetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps, hstates, hs_next, hstep);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);

          forall any_tid | any_tid != tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }

          if !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, tid) {
            hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb, lh_map, pos, tid, num_steps+1, ls_next, lmultistep, hstates + [hs_next], hsteps + [hstep], hs_next);
          }
          else {
            forall ensures |lmultistep.steps| == 1
            {
              if tid in hs_next.threads {
                lemma_YieldPointMapsToYieldPoint(hs_next.threads[tid].pc);
                assert !L.Armada_IsNonyieldingPC(ls_next.s.threads[tid].pc);
              }
              else {
                assert tid !in ls_next.s.threads;
              }

              var prev := pos - 1;
              assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
              assert ls_next == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps+1];
              assert ls_next.s == lstates[num_steps+1];
            }

            var hmultistep := Armada_Multistep(hsteps + [hstep], tid, false);
            assert H.Armada_Next(hs, hs_next, hmultistep);
            hb' := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
            lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];
            assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map');
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroCaseRealTauStep(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps != |lmultistep.steps|
          requires !(num_steps == 0 && |hsteps| == 0 && hs_current.stop_reason.Armada_NotStopped? && tid in hs_current.threads && NewInstructionStoreBufferEntries_H(hs_current.threads[tid].storeBuffer))
          requires lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var prev := pos - 1;
          var ls := lb.states[prev];
          var hs := last(hb.states);
          var lmultistep := lb.trace[prev];
          var ls' := lb.states[pos];
          var tid := lmultistep.tid;
          var lstates := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), lb.states[pos-1].s, lmultistep.steps);

          assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
          lemma_LPlusNextMultipleStepsImpliesLNextMultipleSteps(ls, ls', lmultistep.steps);
          assert L.Armada_Next(ls.s, ls'.s, lmultistep);
          lemma_OnlyFirstStepOfMultistepCanBeTau(ls.s, ls'.s, lmultistep, num_steps);
          assert num_steps == 0;

          var lstep := lmultistep.steps[num_steps];
          var ls_next := LPlus_GetNextStateAlways(ls_current, lstep);
          assert LPlus_NextOneStep(ls_current, ls_next, lstep);
          var hstep := ConvertTraceEntry_LH(lstep);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);
          lemma_LiftActionWithoutVariable(ls_current.s, ls_next.s, lstep, hs_current, hs_next, hstep);

          assert H.Armada_NextOneStep(hs_current, hs_next, hstep);
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);
          lemma_ExtendArmadaNextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_current, hs_next, hsteps, hstep);
          assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_next, hsteps + [hstep]);
          lemma_ExtendArmadaGetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps, hstates, hs_next, hstep);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);

          forall ensures |lmultistep.steps| == 1
          {
            if tid in hs_next.threads {
              lemma_YieldPointMapsToYieldPoint(hs_next.threads[tid].pc);
              assert !L.Armada_IsNonyieldingPC(ls_next.s.threads[tid].pc);
            }
            else {
              assert tid !in ls_next.s.threads;
            }

            var prev := pos - 1;
            assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
            assert ls_next == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps+1];
            assert ls_next.s == lstates[num_steps+1];
          }

          var hmultistep := Armada_Multistep(hsteps + [hstep], tid, true);
          assert H.Armada_Next(hs, hs_next, hmultistep);
          hb' := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
          lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];

          forall any_tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingTauDoesntChangeThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma {:timeLimitMultiplier 3} lemma_PerformVarIntroCaseRealRegularStep(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| && tid in hs_current.threads ==>
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps != |lmultistep.steps|
          requires !(num_steps == 0 && |hsteps| == 0 && hs_current.stop_reason.Armada_NotStopped? && tid in hs_current.threads && NewInstructionStoreBufferEntries_H(hs_current.threads[tid].storeBuffer))
          requires !NewInstructionThread_H(hs_current, tid)
          requires !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires !IsTerminatingStep_L(lmultistep.steps[num_steps])
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var prev := pos - 1;
          var ls := lb.states[prev];
          var hs := last(hb.states);
          var lmultistep := lb.trace[prev];
          var ls' := lb.states[pos];
          var tid := lmultistep.tid;

          assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;

          var lstep := lmultistep.steps[num_steps];
          var ls_next := LPlus_GetNextStateAlways(ls_current, lstep);
          assert LPlus_NextOneStep(ls_current, ls_next, lstep);
          var hstep := ConvertTraceEntry_LH(lstep);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);
          lemma_LiftActionWithoutVariable(ls_current.s, ls_next.s, lstep, hs_current, hs_next, hstep);

          assert H.Armada_NextOneStep(hs_current, hs_next, hstep);
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);
          lemma_ExtendArmadaNextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_current, hs_next, hsteps, hstep);
          assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_next, hsteps + [hstep]);
          lemma_ExtendArmadaGetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps, hstates, hs_next, hstep);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);

          forall any_tid | any_tid != tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }

          if !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, tid) {
            hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb, lh_map, pos, tid, num_steps+1, ls_next, lmultistep, hstates + [hs_next], hsteps + [hstep], hs_next);
          }
          else {
            forall ensures |lmultistep.steps| == 1
            {
              if tid in hs_next.threads {
                lemma_YieldPointMapsToYieldPoint(hs_next.threads[tid].pc);
                assert !L.Armada_IsNonyieldingPC(ls_next.s.threads[tid].pc);
              }
              else {
                assert tid !in ls_next.s.threads;
              }

              var prev := pos - 1;
              assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
              assert ls_next == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps+1];
              var lstates := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), lb.states[pos-1].s, lmultistep.steps);
              assert ls_next.s == lstates[num_steps+1];
            }

            var hmultistep := Armada_Multistep(hsteps + [hstep], tid, false);
            assert H.Armada_Next(hs, hs_next, hmultistep);
            hb' := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
            lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];
            lemma_ArmadaNextMultipleStepsLastElement(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..],
                                                     Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls_current, lmultistep.steps[num_steps..]));
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroCaseIntroducedInstruction(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps != |lmultistep.steps|
          requires NewInstructionThread_H(hs_current, tid);
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var hs := last(hb.states);
          var hstep := NextStepThread_H(hs_current, tid);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);

          lemma_WhenAtNewInstructionNextStepMakesProgress(hs_current, hs_next, hstep, tid);
          assert H.Armada_NextOneStep(hs_current, hs_next, hstep);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);

          forall any_tid | any_tid != tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }

          if !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, tid) {
            var hsteps_mid := hsteps + [hstep];
            var hstates_mid := hstates + [hs_next];
            hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates_mid, hsteps_mid, hs_next);
          }
          else {
            forall ensures num_steps == 0
            {
              if tid in hs_next.threads {
                lemma_YieldPointMapsToYieldPoint(hs_next.threads[tid].pc);
                assert !L.Armada_IsNonyieldingPC(ls_current.s.threads[tid].pc);
              }
              else {
                assert tid !in ls_current.s.threads;
              }

              var prev := pos - 1;
              assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;
              assert ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps];
              var lstates := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), lb.states[pos-1].s, lmultistep.steps);
              assert ls_current.s == lstates[num_steps];
              assert 0 < num_steps < |lmultistep.steps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls_current, tid);
            }

            var hmultistep := Armada_Multistep(hsteps + [hstep], tid, false);
            lemma_ExtendArmadaNextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_current, hs_next, hsteps, hstep);
            assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs_next, hmultistep.steps);
            lemma_ExtendArmadaGetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps, hstates, hs_next, hstep);
            assert H.Armada_Next(hs, hs_next, hmultistep);
            var hb_mid := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
            var lh_map_mid := lh_map[pos-1 := lh_map[pos-1].(last := |hb_mid.states|-1)];
            hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb_mid, lh_map_mid, pos, tid, 0, ls_current, lmultistep, [hs_next], [], hs_next);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroCaseIntroducedTau(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps == 0
          requires |hsteps| == 0
          requires hs_current.stop_reason.Armada_NotStopped?
          requires tid in hs_current.threads
          requires NewInstructionStoreBufferEntries_H(hs_current.threads[tid].storeBuffer)
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var hstep := H.Armada_TraceEntry_Tau(tid);
          var hmultistep := Armada_Multistep([hstep], tid, true);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);
          assert H.Armada_NextOneStep(hs_current, hs_next, hstep);
          assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs_current, hs_next, hmultistep.steps);
          assert H.Armada_Next(hs_current, hs_next, hmultistep);
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);
          var hb_mid := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
          var lh_map_mid := lh_map[pos-1 := lh_map[pos-1].(last := |hb.states|)];

          forall any_tid | any_tid != tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }

          hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb_mid, lh_map_mid, pos, tid, 0, ls_current, lmultistep, [hs_next], [], hs_next);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroCaseFinished(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps == |lmultistep.steps|
          requires Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid)
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);
          if |hsteps| > 0 {
            var hmultistep := Armada_Multistep(hsteps, tid, false);
            hb' := AnnotatedBehavior(hb.states + [hs_current], hb.trace + [hmultistep]);
            lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];
          }
          else {
            hb' := hb;
            lh_map' := lh_map + [RefinementRange(|hb.states|-1, |hb.states|-1)];
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroCaseIntroducedStepAtEnd(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          requires num_steps == |lmultistep.steps|
          requires tid in hs_current.threads
          requires H.Armada_IsNonyieldingPC(hs_current.threads[tid].pc)
          requires hs_current.stop_reason.Armada_NotStopped?
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    0
        {
          var hs := last(hb.states);
          lemma_OnlyIntroducedAssignmentsBeforeYielding(hs_current, tid);
          assert NewInstructionPC_H(hs_current, tid);

          var hstep := NextStepThread_H(hs_current, tid);
          var hs_next := H.Armada_GetNextStateAlways(hs_current, hstep);
          lemma_VarIntroInvariantPreservedByNext(hs_current, hs_next, hstep);
          lemma_ArmadaNextMultipleStepsLastElement(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps, hstates);

          forall any_tid | any_tid != tid
            ensures Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, any_tid)
          {
            lemma_ExecutingStepDoesntChangeOtherThreadYielding_H(hs_current, hs_next, hstep, any_tid);
          }

          if !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_next, tid) {
            lemma_WhenAtNewInstructionNextStepMakesProgress(hs_current, hs_next, hstep, tid);
            var hsteps_mid := hsteps + [hstep];
            var hstates_mid := hstates + [hs_next];
            hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates_mid, hsteps_mid, hs_next);
          }
          else {
            var hmultistep := Armada_Multistep(hsteps + [hstep], tid, false);
            hb' := AnnotatedBehavior(hb.states + [hs_next], hb.trace + [hmultistep]);
            lemma_ExtendArmadaNextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hs_next, hsteps, hstep);
            lemma_ExtendArmadaGetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps, hstates, hs_next, hstep);
            assert H.Armada_Next(last(hb.states), hs_next, hmultistep);
            lh_map' := lh_map + [RefinementRange(|hb.states|, |hb.states|)];
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroGeneral(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle,
          num_steps: int,
          ls_current: LPlusState,
          lmultistep: LStep,
          hstates: seq<HState>,
          hsteps: seq<H.Armada_TraceEntry>,
          hs_current: HState
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires VarIntroInvariant(hs_current)
          requires lmultistep == lb.trace[pos-1]
          requires 0 <= num_steps <= |lmultistep.steps|
          requires ls_current == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lb.states[pos-1], lmultistep.steps)[num_steps]
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls_current, lb.states[pos], lmultistep.steps[num_steps..])
          requires forall step :: step in lmultistep.steps ==> step.tid == tid && step.Armada_TraceEntry_Tau? == lmultistep.tau
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          requires forall any_tid :: any_tid != tid ==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, any_tid)
          requires lmultistep.tid == tid
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), last(hb.states), hs_current, hsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), last(hb.states), hsteps)
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall i :: 0 < i < |hstates| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          requires ConvertTotalState_HL(hs_current) == ls_current.s
          requires 0 < num_steps == |lmultistep.steps| ==>
                     Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) ||
                     OnlyIntroducedAssignmentsBeforeYielding(hs_current.threads[tid].pc)
          requires |hsteps| > 0 && num_steps < |lmultistep.steps| ==> !lmultistep.steps[num_steps].Armada_TraceEntry_Tau?
          ensures  |hb'.states| > 0
          ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures  AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures  VarIntroInvariant(last(hb'.states))
          ensures  lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
          decreases |lmultistep.steps| - num_steps,
                    var hs := hs_current; if tid in hs.threads then ProgressMeasureThread_H(hs.threads[tid]) else 0,
                    var hs := hs_current; if tid in hs.threads then |hs.threads[tid].storeBuffer| else 0,
                    1
        {
          if num_steps == |lmultistep.steps| {
            if !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs_current, tid) {
              hb', lh_map' := lemma_PerformVarIntroCaseIntroducedStepAtEnd(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
            }
            else {
              hb', lh_map' := lemma_PerformVarIntroCaseFinished(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
            }
          }
          else if !lmultistep.steps[num_steps].Armada_TraceEntry_Tau? && NewInstructionThread_H(hs_current, tid) {
            hb', lh_map' := lemma_PerformVarIntroCaseIntroducedInstruction(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
          }
          else if && num_steps == 0
                  && |hsteps| == 0
                  && hs_current.stop_reason.Armada_NotStopped?
                  && tid in hs_current.threads
                  && NewInstructionStoreBufferEntries_H(hs_current.threads[tid].storeBuffer) {
            hb', lh_map' := lemma_PerformVarIntroCaseIntroducedTau(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
          }
          else if lmultistep.steps[num_steps].Armada_TraceEntry_Tau? {
            hb', lh_map' := lemma_PerformVarIntroCaseRealTauStep(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
          }
          else if IsTerminatingStep_L(lmultistep.steps[num_steps]) {
            hb', lh_map' := lemma_PerformVarIntroCaseRealTerminatingStep(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
          }
          else {
            hb', lh_map' := lemma_PerformVarIntroCaseRealRegularStep(lb, hb, lh_map, pos, tid, num_steps, ls_current, lmultistep, hstates, hsteps, hs_current);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntroOneMultistep(
          lb: AnnotatedBehavior<LPlusState, LStep>,
          hb: AnnotatedBehavior<HState, HStep>,
          lh_map: RefinementMap,
          pos: int,
          tid: Armada_ThreadHandle
          ) returns (
          hb': AnnotatedBehavior<HState, HStep>,
          lh_map': RefinementMap
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 1 <= pos < |lb.states|
          requires |hb.states| > 0
          requires BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
          requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
          requires VarIntroInvariant(last(hb.states))
          requires lb.states[pos - 1].s == ConvertTotalState_HL(last(hb.states))
          requires tid == lb.trace[pos-1].tid
          requires forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos - 1], any_tid)
          requires forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          ensures |hb'.states| > 0
          ensures BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos + 1], hb'.states, GetLPlusHRefinementRelation(), lh_map')
          ensures AnnotatedBehaviorSatisfiesSpec(hb', GetHSpec())
          ensures VarIntroInvariant(last(hb'.states))
          ensures lb.states[pos].s == ConvertTotalState_HL(last(hb'.states))
          ensures  forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos], any_tid)
          ensures  forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb'.states), any_tid)
        {
          var prev := pos - 1;
          var ls := lb.states[prev];
          var hs := last(hb.states);
          var lmultistep := lb.trace[prev];
          var tid := lmultistep.tid;

          assert ls.s == ConvertTotalState_HL(hs);
          assert ActionTuple(lb.states[prev], lb.states[prev + 1], lb.trace[prev]) in GetLPlusSpec().next;

          hb', lh_map' := lemma_PerformVarIntroGeneral(lb, hb, lh_map, pos, tid, 0, lb.states[pos-1], lb.trace[pos-1],
                                                       [last(hb.states)], [], last(hb.states));
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformVarIntro(lb:AnnotatedBehavior<LPlusState, LStep>) returns (hb:AnnotatedBehavior<HState, HStep>)
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          ensures  BehaviorRefinesBehavior(lb.states, hb.states, GetLPlusHRefinementRelation())
          ensures  AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
        {
          var ls := lb.states[0];
          var hs := ConvertTotalState_LPlusH(ls);
          lemma_IntroPreservesInit(ls, hs);

          var hstates := [hs];
          var htrace := [];
          hb := AnnotatedBehavior(hstates, htrace);
          var pos := 1;
          var lh_map := [RefinementRange(0, 0)];

          while pos < |lb.states|
            invariant 1 <= pos <= |lb.states|
            invariant |hb.states| > 0
            invariant VarIntroInvariant(last(hb.states))
            invariant BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos], hb.states, GetLPlusHRefinementRelation(), lh_map)
            invariant AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
            invariant lb.states[pos-1].s == ConvertTotalState_HL(last(hb.states))
            invariant forall any_tid :: Armada_ThreadYielding(LPlus_GetSpecFunctions(), lb.states[pos-1], any_tid)
            invariant forall any_tid :: Armada_ThreadYielding(H.Armada_GetSpecFunctions(), last(hb.states), any_tid)
          {
            hb, lh_map := lemma_PerformVarIntroOneMultistep(lb, hb, lh_map, pos, lb.trace[pos-1].tid);
            pos := pos + 1;
          }

          assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, GetLPlusHRefinementRelation(), lh_map);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ProveRefinementViaVarIntro()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          forall lb | BehaviorSatisfiesSpec(lb, L.Armada_Spec())
            ensures BehaviorRefinesSpec(lb, H.Armada_Spec(), GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);
            var ahb := lemma_PerformVarIntro(alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, GetLPlusHRefinementRelation());
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  };
};
