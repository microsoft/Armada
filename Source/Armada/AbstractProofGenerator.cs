using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada
{
  public class AuxiliaryInfo
  {
    public readonly string FieldName;
    public readonly string TypeName;
    public readonly string InitName;
    public readonly string NextName;

    public AuxiliaryInfo(string i_FieldName, string i_TypeName, string i_InitName, string i_NextName)
    {
      FieldName = i_FieldName;
      TypeName = i_TypeName;
      InitName = i_InitName;
      NextName = i_NextName;
    }
  }

  public abstract class InvariantInfo
  {
    protected string key;
    protected string name;
    protected List<string> dependencies;
    protected string initLemmaName;
    protected string nextLemmaName;
    protected string nextStepBody;

    public InvariantInfo(string i_key, string i_name, List<string> i_dependencies, string i_nextStepBody="")
    {
      key = i_key;
      name = i_name;
      dependencies = i_dependencies;
      initLemmaName = null;
      nextLemmaName = null;
      nextStepBody = i_nextStepBody;
    }

    public virtual string Key { get { return key; } }
    public virtual string Name { get { return name; } }
    public virtual List<string> Dependencies { get { return dependencies; } }
    public virtual string InitLemmaName { get { return initLemmaName; } }
    public virtual string NextLemmaName { get { return nextLemmaName; } }

    private string FindMatchingDependency(string dependency, IEnumerable<InvariantInfo> allInvariants)
    {
      foreach (var inv in allInvariants) {
        if (inv.Key == dependency || inv.Key == $"UserInv_{dependency}") {
          return inv.Name;
        }
      }
      return dependency;
    }

    public virtual void GenerateInitLemma(ProofGenerationParams pgp)
    {
      initLemmaName = $"lemma_InvariantPredicateImpliedByInit_{Key}";
      string str = $@"
        lemma {initLemmaName}(s:LPlusState)
          requires LPlus_Init(s)
          ensures  {Name}(s)
        {{
        }}
      ";
      pgp.AddLemma(str, "invariants");
    }

    public virtual string GenerateSpecificNextLemma(ProofGenerationParams pgp, NextRoutine nextRoutine,
                                                    IEnumerable<InvariantInfo> allInvariants)
    {
      string nameSuffix = nextRoutine.NameSuffix;
      string nextLemmaName = $"lemma_InvariantPredicateMaintainedByNext_{Key}_{nameSuffix}";
      string str = $@"
        lemma {nextLemmaName}(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
          requires {Name}(s)
      ";
      foreach (var dependency in Dependencies)
      {
        str += $"  requires {FindMatchingDependency(dependency, allInvariants)}(s);\n";
      }
      str += $@"
          requires step.Armada_TraceEntry_{nameSuffix}?
          requires LPlus_NextOneStep(s, s', step)
          ensures  {Name}(s')
        {{
          {nextStepBody}
        }}
      ";
      pgp.AddLemma(str, "invariants");

      return nextLemmaName;
    }

    public virtual void GenerateNextLemma(ProofGenerationParams pgp, IEnumerable<InvariantInfo> allInvariants)
    {
      string finalCases = "";
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        string specificNext = GenerateSpecificNextLemma(pgp, nextRoutine, allInvariants);
        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"    case Armada_TraceEntry_{nextRoutine.NameSuffix}(_{step_params}) => {specificNext}(s, s', step);\n";
      }

      nextLemmaName = $"lemma_InvariantPredicateMaintainedByNext_{Key}";
      string str = $@"
        lemma {nextLemmaName}(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
          requires {Name}(s)
      ";
      foreach (var dependency in Dependencies)
      {
        str += $"  requires {FindMatchingDependency(dependency, allInvariants)}(s);\n";
      }
      str += $@"
          requires LPlus_NextOneStep(s, s', step)
          ensures  {Name}(s')
        {{
          match step {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str, "invariants");
    }

    public virtual void GenerateProofs(ProofGenerationParams pgp, IEnumerable<InvariantInfo> allInvariants)
    {
      GenerateInitLemma(pgp);
      GenerateNextLemma(pgp, allInvariants);
    }
  }

  public class UserInvariantInfo : InvariantInfo
  {
    public UserInvariantInfo(string i_key, string i_name, List<string> i_dependencies) : base(i_key, i_name, i_dependencies)
    {
    }
  }

  public class InternalInvariantInfo : InvariantInfo
  {
    public InternalInvariantInfo(string i_key, string i_name, List<string> i_dependencies, string nextStepBody="") : base(i_key, i_name, i_dependencies, nextStepBody)
    {
    }
  }

  public abstract class AbstractProofGenerator
  {
    protected ProofGenerationParams pgp;
    protected Dictionary<ArmadaPC, ArmadaPC> pcMap;
    protected Dictionary<NextRoutine, NextRoutine> nextRoutineMap;
    protected List<ImportFileArmadaProofDecl> importedFiles;
    protected List<ImportModuleArmadaProofDecl> importedModules;
    protected List<InvariantInfo> invariants;
    protected List<AuxiliaryInfo> auxiliaries;

    // To prevent duplicate lemmas when there are duplicate calls
    private bool calledGenerateAppendStoreBufferOtherWay = false;

    public AbstractProofGenerator(ProofGenerationParams i_pgp)
    {
      pgp = i_pgp;
      nextRoutineMap = new Dictionary<NextRoutine, NextRoutine>();
      importedFiles = new List<ImportFileArmadaProofDecl>();
      importedModules = new List<ImportModuleArmadaProofDecl>();
      invariants = new List<InvariantInfo>();
      auxiliaries = new List<AuxiliaryInfo>();

      var specFile = pgp.proofFiles.CreateAuxiliaryProofFile("specs");
      specFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      specFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      specFile.AddImport("GenericArmadaSpecModule");
      specFile.AddImport("GenericArmadaLemmasModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("specs");

      var convertFile = pgp.proofFiles.CreateAuxiliaryProofFile("convert");
      convertFile.IncludeAndImportGeneratedFile("specs");
      convertFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      convertFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("convert");

      var invFile = pgp.proofFiles.CreateAuxiliaryProofFile("invariants");
      invFile.IncludeAndImportGeneratedFile("specs");
      invFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/invariants.i.dfy", "InvariantsModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("invariants");
      invFile.IncludeAndImportGeneratedFile("utility");

      var utilityFile = pgp.proofFiles.CreateAuxiliaryProofFile("utility");
      utilityFile.IncludeAndImportGeneratedFile("specs");
      utilityFile.IncludeAndImportGeneratedFile("convert");
      utilityFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy", "util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("utility");
    }

    public abstract void GenerateProof();

    ////////////////////////////////////////////////////////////////////////
    /// Checking that the layers are similar enough to generate a proof
    ////////////////////////////////////////////////////////////////////////

    protected virtual bool CheckEquivalence()
    {
      return CheckStructsEquivalence() && CheckGlobalsEquivalence() && CheckMethodsEquivalence();
    }

    protected virtual bool CheckStructsEquivalence()
    {
      if (pgp.symbolsLow.StructsModuleName != pgp.symbolsHigh.StructsModuleName) {
        AH.PrintError(pgp.prog, $"Levels {pgp.mLow.Name} and {pgp.mHigh.Name} don't use the same structs module");
        return false;
      }

      return true;
    }

    protected bool CheckGlobalVariableEquivalence(string name, ArmadaVariable v_l, ArmadaVariable v_h)
    {
        if (v_l is AddressableArmadaVariable && !(v_h is AddressableArmadaVariable)) {
          AH.PrintError(pgp.prog, $"Global variable {name} is addressable in level {pgp.mLow.Name} but not in level {pgp.mHigh.Name}");
          return false;
        }
        if (!(v_l is AddressableArmadaVariable) && (v_h is AddressableArmadaVariable)) {
          AH.PrintError(pgp.prog, $"Global variable {name} is addressable in level {pgp.mHigh.Name} but not in level {pgp.mLow.Name}");
          return false;
        }
        if (v_l.NoTSO() && !v_h.NoTSO()) {
          AH.PrintError(pgp.prog, $"Global variable {name} is ghost in level {pgp.mLow.Name} but not in level {pgp.mHigh.Name}");
          return false;
        }
        if (!v_l.NoTSO() && v_h.NoTSO()) {
          AH.PrintError(pgp.prog, $"Global variable {name} is ghost in level {pgp.mHigh.Name} but not in level {pgp.mLow.Name}");
          return false;
        }

        if (!AH.TypesMatch(v_l.ty, v_h.ty)) {
          AH.PrintError(pgp.prog, $"Global variable {name} has type {v_l.ty} in level {pgp.mLow.Name} but type {v_h.ty} in level {pgp.mHigh.Name}");
          return false;
        }

        if (v_l is GlobalUnaddressableArmadaVariable && v_h is GlobalUnaddressableArmadaVariable &&
            ((GlobalUnaddressableArmadaVariable)v_l).initialValue == null && ((GlobalUnaddressableArmadaVariable)v_h).initialValue != null) {
          AH.PrintError(pgp.prog, $"Global variable {name} has an initial value in level {pgp.mHigh.Name} but no initial value in level {pgp.mLow.Name}");
          return false;
        }

        return true;
    }

    protected virtual bool CheckGlobalsEquivalence()
    {
      return CheckGlobalsEquivalenceAbstract();
    }

    protected bool CheckGlobalsEquivalenceAbstract()
    {
      var globalVarsLow = pgp.symbolsLow.Globals.VariableNames.ToArray();
      var globalVarsHigh = pgp.symbolsHigh.Globals.VariableNames.ToArray();

      if (globalVarsLow.Length != globalVarsHigh.Length) {
        AH.PrintError(pgp.prog, $"There are {globalVarsLow.Length} global variables in level {pgp.mLow.Name} but {globalVarsHigh.Length} in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < globalVarsLow.Length; ++i) {
        if (globalVarsLow[i] != globalVarsHigh[i]) {
          AH.PrintError(pgp.prog, $"Global variable number {i+1} in level {pgp.mLow.Name} is {globalVarsLow[i]}, which doesn't match global variable number {i+1} in level {pgp.mHigh.Name} which is {globalVarsHigh[i]}");
          return false;
        }
        var name = globalVarsLow[i];
        if (!CheckGlobalVariableEquivalence(name, pgp.symbolsLow.Globals.Lookup(name), pgp.symbolsHigh.Globals.Lookup(name))) {
          return false;
        }
      }

      return true;
    }

    protected virtual bool CheckVariableNameListEquivalence(IEnumerable<string> varNames_l, IEnumerable<string> varNames_h,
                                                            ArmadaSingleMethodSymbolTable s_l, ArmadaSingleMethodSymbolTable s_h,
                                                            string methodName, string descriptor)
    {
      var vars_l = varNames_l.ToArray();
      var vars_h = varNames_h.ToArray();
      if (vars_l.Length != vars_h.Length) {
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

    protected virtual bool CheckMethodsEquivalence()
    {
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        if (!pgp.symbolsHigh.DoesMethodNameExist(methodName)) {
          AH.PrintError(pgp.prog, $"Method {methodName} is in level {pgp.mLow.Name} but not in level {pgp.mHigh.Name}");
          return false;
        }
      }

      foreach (var methodName in pgp.symbolsHigh.MethodNames) {
        if (!pgp.symbolsLow.DoesMethodNameExist(methodName)) {
          AH.PrintError(pgp.prog, $"Method {methodName} is in level {pgp.mHigh.Name} but not in level {pgp.mLow.Name}");
          return false;
        }
      }

      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var s_l = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        var s_h = pgp.symbolsHigh.GetMethodSymbolTable(methodName);

        if (s_l.IsExternal && !s_h.IsExternal) {
            AH.PrintError(pgp.prog, $"Method {methodName} is external in level {pgp.mLow.Name} but not external in level {pgp.mHigh.Name}");
            return false;
        }
        if (!s_l.IsExternal && s_h.IsExternal) {
            AH.PrintError(pgp.prog, $"Method {methodName} is external in level {pgp.mHigh.Name} but not external in level {pgp.mLow.Name}");
            return false;
        }

        if (!CheckVariableNameListEquivalence(s_l.InputVariableNames, s_h.InputVariableNames, s_l, s_h, methodName, "input")) {
          return false;
        }
        if (!CheckVariableNameListEquivalence(s_l.OutputVariableNames, s_h.OutputVariableNames, s_l, s_h, methodName, "output")) {
          return false;
        }
        if (!CheckVariableNameListEquivalence(s_l.AllVariableNamesInOrder, s_h.AllVariableNamesInOrder, s_l, s_h, methodName, "any")) {
          return false;
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC map
    ////////////////////////////////////////////////////////////////////////

    protected void MakeTrivialPCMap()
    {
      pcMap = new Dictionary<ArmadaPC, ArmadaPC>();
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        pcMap[pc] = pc.CloneWithNewSymbolTable(pgp.symbolsHigh);
      }
    }

    protected virtual void ExtendPCMapWithExternalAndStructsMethods()
    {
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var st = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        if (st.IsExternal || st.IsFromStructsModule) {
          List<ArmadaPC> allPCs = new List<ArmadaPC>();
          pgp.symbolsLow.AllMethods.LookupMethod(methodName).AppendAllPCs(allPCs);
          foreach (var pc in allPCs) {
            pcMap[pc] = pc.CloneWithNewSymbolTable(pgp.symbolsHigh);
          }
        }
      }
    }

    protected ArmadaPC LiftPC(ArmadaPC pc)
    {
      if (pc == null) {
        return null;
      }
      return pcMap[pc];
    }

    protected virtual String TranslateFormalNameUsingPcMap(NextFormal formal, ArmadaPC lpc, Dictionary<ArmadaPC, ArmadaPC> pcMap)
    {
      var lpcName = lpc.ToString();
      if (formal.GloballyUniqueVarName.Contains(lpcName)) {
        return formal.GloballyUniqueVarName.Replace(lpcName, pcMap[lpc].ToString());
      }
      else {
        return formal.GloballyUniqueVarName;
      }
    }

    protected virtual void GenerateNextRoutineMap(bool warnOnMissingRoutines = true)
    {
      var hmap = new Dictionary<Tuple<ArmadaPC, ArmadaPC>, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        var t = new Tuple<ArmadaPC, ArmadaPC>(nextRoutine.pc, nextRoutine.endPC);
        if (hmap.ContainsKey(t)) {
          AH.PrintError(pgp.prog,
                        $"More than one next routine from PC {nextRoutine.pc} to {nextRoutine.endPC} in level {pgp.mLow.Name}");
          hmap.Remove(t);
        }
        else {
          hmap[t] = nextRoutine;
        }
      }

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var startPC = LiftPC(nextRoutine.pc);
        var endPC = LiftPC(nextRoutine.endPC);
        var t = new Tuple<ArmadaPC, ArmadaPC>(startPC, endPC);
        if (hmap.ContainsKey(t)) {
          nextRoutineMap[nextRoutine] = hmap[t];
        }
        else if (warnOnMissingRoutines) {
          AH.PrintWarning(pgp.prog, $"No next routine found in high level from {startPC} to {endPC}");
        }
      }
    }

    protected virtual NextRoutine LiftNextRoutine(NextRoutine nextRoutine)
    {
      if (nextRoutineMap.ContainsKey(nextRoutine)) {
        return nextRoutineMap[nextRoutine];
      }
      else {
        return null;
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    private void AddInductiveInvariant(InductiveInvariantArmadaProofDecl d)
    {
      string invKey = d.InvariantName;
      string invName, str;
      var userInvariants = pgp.symbolsLow.GlobalInvariants;
      if (d.Code != null) {
        invName = $"UserInv_{invKey}";
        str = $@"
          predicate {invName}(s:LPlusState)
          {{
            { d.Code }
          }}
        ";
        pgp.AddPredicate(str, "invariants");
      }
      else if (userInvariants.ContainsKey(invKey)) {
        var inv = userInvariants[invKey];
        invName = $"UserInv_{invKey}";
        str = $@"
          predicate {invName}(splus:LPlusState)
          {{
            L.{inv.TranslatedName}(splus.s)
          }}
        ";
        pgp.AddPredicate(str, "invariants");
      }
      else {
        AH.PrintError(pgp.prog, d.tok, $"No invariant named {invKey} found among the invariants");
        return;
      }
      var dependencies = new List<string>(d.Dependencies);
      invariants.Add(new UserInvariantInfo(invKey, invName, dependencies));
    }

    private void ParseImports()
    {
      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is ImportFileArmadaProofDecl) {
          var ifd = (ImportFileArmadaProofDecl)topDecl;
          importedFiles.Add(ifd);
        }
        else if (topDecl is ImportModuleArmadaProofDecl) {
          var imd = (ImportModuleArmadaProofDecl)topDecl;
          importedModules.Add(imd);
        }
        else if (topDecl is InductiveInvariantArmadaProofDecl) {
          var iid = (InductiveInvariantArmadaProofDecl)topDecl;
          AddInductiveInvariant(iid);
        }
        else if (topDecl is ExtraMaterialArmadaProofDecl) {
          var emapd = (ExtraMaterialArmadaProofDecl)topDecl;
          pgp.AddExtraMaterial(emapd.Loc, emapd.Contents);
        }
        else if (topDecl is UseRegionsArmadaProofDecl) {
          GenerateRegionInvariant();
        }
        else if (topDecl is UseAddressInvariantArmadaProofDecl) {
          GenerateAddressableInvariant();
        }
        else if (topDecl is AuxiliaryArmadaProofDecl) {
          var iad = (AuxiliaryArmadaProofDecl)topDecl;
          if (iad.TypeDefinitionCode.Length > 0) {
            var d = AH.ParseTopLevelDecl(pgp.prog, iad.TypeName, iad.TypeDefinitionCode);
            if (d is DatatypeDecl) {
              pgp.AddTopLevelDecl((DatatypeDecl)d, "specs");
            }
            else if (d is TypeSynonymDecl) {
              pgp.AddTopLevelDecl((TypeSynonymDecl)d, "specs");
            }
            else {
              AH.PrintError(pgp.prog, d.tok, "Type definition code is neither a datatype declaration nor a type declaration");
              continue;
            }
          }
          string str;
          string auxInitName = $"AuxInit_{iad.FieldName}";
          str = $@"
            function {auxInitName}(s:LState, config:LConfig) : {iad.TypeName}
            {{
              {iad.InitCode}
            }}
          ";
          pgp.AddFunction(str, "specs");

          string auxNextName = $"AuxNext_{iad.FieldName}";
          str = $@"
            function {auxNextName}(s:LPlusState, s':LState, step:L.Armada_TraceEntry) : {iad.TypeName}
            {{
              {iad.NextCode}
            }}
          ";
          pgp.AddFunction(str, "specs");

          var auxiliaryInfo = new AuxiliaryInfo(iad.FieldName, iad.TypeName, auxInitName, auxNextName);
          auxiliaries.Add(auxiliaryInfo);
        }
      }
    }

    protected virtual void AddIncludesAndImports()
    {
      ParseImports();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Utility functions
    ////////////////////////////////////////////////////////////////////////

    protected string GetConversionFunctionForTypeName_LH(string s)
    {
      var m = Regex.Match(s, @"^Armada_(PC|Globals|StoreBufferLocation|StoreBufferEntry|Stack|StoreBuffer|Thread|Threads|TotalState|Config)$");
      if (m.Success) {
        return $"Abstract{m.Groups[1]}_LH";
      }

      return null;
    }

    protected string GetConversionFunctionForTypeName_HL(string s)
    {
      var m = Regex.Match(s, @"^Armada_(PC|Globals|StoreBufferLocation|StoreBufferEntry|Stack|StoreBuffer|Thread|Threads|TotalState|Config)$");
      if (m.Success) {
        return $"Abstract{m.Groups[1]}_HL";
      }

      return null;
    }

    protected Type AddModuleNameToArmadaType(Type ty, string moduleName)
    {
      if (ty is UserDefinedType) {
        var udt = (UserDefinedType)ty;
        string conversionFn = GetConversionFunctionForTypeName_LH(udt.Name);
        if (conversionFn != null) {
          return new UserDefinedType(udt.tok, $"{moduleName}.{udt.Name}", udt.TypeArgs);
        }
      }
      else if (ty is SeqType) {
        var sty = (SeqType)ty;
        return new SeqType(AddModuleNameToArmadaType(sty.Arg, moduleName));
      }
      else if (ty is SetType) {
        var sty = (SetType)ty;
        return new SetType(sty.Finite, AddModuleNameToArmadaType(sty.Arg, moduleName));
      }

      return ty;
    }

    protected string GetCalleeNameForCallStmt(Statement stmt)
    {
      var us = (UpdateStmt)stmt;
      var rhs = us.Rhss[0];
      var ex = (ExprRhs)rhs;
      var suffix = (ApplySuffix)ex.Expr;
      var suffixName = (NameSegment)suffix.Lhs;
      return suffixName.Name;
    }

    ////////////////////////////////////////////////////////////////////////
    /// State abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateConvertPC_LH()
    {
      var cases = new List<MatchCaseExpr>();

      foreach (var mapping in pcMap) {
        var case_body = AH.MakeNameSegment($"H.{mapping.Value}", "H.Armada_PC");
        cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
      }

      var source = AH.MakeNameSegment("pc", "L.Armada_PC");
      var body = AH.MakeMatchExpr(source, cases, "H.Armada_PC");
      var formals = new List<Formal> { AH.MakeFormal("pc", "L.Armada_PC") };
      var fn = AH.MakeFunction("ConvertPC_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertStackFrame_LH()
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

    protected virtual void GenerateConvertGlobals_LH()
    {
      var g = AH.MakeNameSegment("globals", "L.Armada_Globals");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Globals", ps, "H.Armada_Globals");
      var formals = new List<Formal> { AH.MakeFormal("globals", "L.Armada_Globals") };
      var fn = AH.MakeFunction("ConvertGlobals_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertGhosts_LH()
    {
      var ghosts = AH.MakeNameSegment("ghosts", "L.Armada_Ghosts");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalGhostArmadaVariable) {
          var p = AH.MakeExprDotName(ghosts, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Ghosts", ps, "H.Armada_Ghosts");
      var formals = new List<Formal> { AH.MakeFormal("ghosts", "L.Armada_Ghosts") };
      var fn = AH.MakeFunction("ConvertGhosts_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertAddrs_LH()
    {
      var addrs = AH.MakeNameSegment("addrs", "L.Armada_Addrs");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalAddressableArmadaVariable) {
          var p = AH.MakeExprDotName(addrs, v.FieldName, "Armada_Pointer");
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Addrs", ps, "H.Armada_Addrs");
      var formals = new List<Formal> { AH.MakeFormal("addrs", "L.Armada_Addrs") };
      var fn = AH.MakeFunction("ConvertAddrs_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertGlobalStaticVar_LH()
    {
      var cases = new List<MatchCaseExpr>();
      var case_body = AH.MakeNameSegment("H.Armada_GlobalStaticVarNone", "H.Armada_GlobalStaticVar");
      cases.Add(AH.MakeMatchCaseExpr("Armada_GlobalStaticVarNone", case_body));
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          case_body = AH.MakeNameSegment($"H.Armada_GlobalStaticVar_{varName}", "H.Armada_GlobalStaticVar");
          cases.Add(AH.MakeMatchCaseExpr($"Armada_GlobalStaticVar_{varName}", case_body));
        }
      }

      var v = AH.MakeNameSegment("v", "L.Armada_GlobalStaticVar");
      var body = AH.MakeMatchExpr(v, cases, "H.Armada_GlobalStaticVar");
      var formals = new List<Formal> { AH.MakeFormal("v", "L.Armada_GlobalStaticVar") };
      var fn = AH.MakeFunction("ConvertGlobalStaticVar_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertSharedMemory_LH()
    {
      string str = @"
        function ConvertSharedMemory_LH(mem: L.Armada_SharedMemory) : H.Armada_SharedMemory
        {
          H.Armada_SharedMemory(mem.heap, ConvertGlobals_LH(mem.globals))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBufferLocation_LH()
    {
      string str = @"
        function ConvertStoreBufferLocation_LH(loc:L.Armada_StoreBufferLocation) : H.Armada_StoreBufferLocation
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

    protected virtual void GenerateConvertStoreBufferEntry_LH()
    {
      string str = @"
        function ConvertStoreBufferEntry_LH(entry:L.Armada_StoreBufferEntry) : H.Armada_StoreBufferEntry
        {
          H.Armada_StoreBufferEntry(ConvertStoreBufferLocation_LH(entry.loc), entry.value)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBuffer_LH()
    {
      string str = @"
        function ConvertStoreBuffer_LH(entries:seq<L.Armada_StoreBufferEntry>) : seq<H.Armada_StoreBufferEntry>
        {
          MapSeqToSeq(entries, ConvertStoreBufferEntry_LH)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertExtendedFrame_LH()
    {
      string str = @"
        function ConvertExtendedFrame_LH(eframe:L.Armada_ExtendedFrame) : H.Armada_ExtendedFrame
        {
          H.Armada_ExtendedFrame(ConvertPC_LH(eframe.return_pc), ConvertStackFrame_LH(eframe.frame), eframe.new_ptrs)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStack_LH()
    {
      string str = @"
        function ConvertStack_LH(stack:seq<L.Armada_ExtendedFrame>) : seq<H.Armada_ExtendedFrame>
        {
          MapSeqToSeq(stack, ConvertExtendedFrame_LH)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertThread_LH()
    {
      string str = @"
        function ConvertThread_LH(t:L.Armada_Thread) : H.Armada_Thread
        {
          H.Armada_Thread(ConvertPC_LH(t.pc), ConvertStackFrame_LH(t.top), t.new_ptrs, ConvertStack_LH(t.stack),
                          ConvertStoreBuffer_LH(t.storeBuffer))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertThreads_LH()
    {
      string str = @"
        function ConvertThreads_LH(threads:map<Armada_ThreadHandle, L.Armada_Thread>) : map<Armada_ThreadHandle, H.Armada_Thread>
        {
          MapMapToMap(threads, ConvertThread_LH)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertTotalState_LH()
    {
      string str = @"
        function ConvertTotalState_LH(s:L.Armada_TotalState) : H.Armada_TotalState
        {
          H.Armada_TotalState(s.stop_reason, ConvertThreads_LH(s.threads), ConvertSharedMemory_LH(s.mem), ConvertGhosts_LH(s.ghosts),
                              ConvertAddrs_LH(s.addrs))
        }
      ";
      pgp.AddFunction(str, "convert");

      str = @"
        function ConvertTotalState_LPlusH(s:LPlusState) : HState
        {
          ConvertTotalState_LH(s.s)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertConfig_LH()
    {
      string str = @"
        function ConvertConfig_LH(config:L.Armada_Config) : H.Armada_Config
        {
          H.Armada_Config(config.tid_init, config.new_ptrs)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateStateAbstractionFunctions_LH()
    {
      GenerateConvertPC_LH();
      GenerateConvertStackFrame_LH();
      GenerateConvertGlobals_LH();
      GenerateConvertGhosts_LH();
      GenerateConvertAddrs_LH();
      GenerateConvertGlobalStaticVar_LH();
      GenerateConvertSharedMemory_LH();
      GenerateConvertStoreBufferLocation_LH();
      GenerateConvertStoreBufferEntry_LH();
      GenerateConvertStoreBuffer_LH();
      GenerateConvertExtendedFrame_LH();
      GenerateConvertStack_LH();
      GenerateConvertThread_LH();
      GenerateConvertThreads_LH();
      GenerateConvertTotalState_LH();
      GenerateConvertConfig_LH();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Next-state functions
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateNextState_H() {
      string str;

      str = @"
        function ApplySteps_H(s: HState, steps: seq<H.Armada_TraceEntry>) : HState
          decreases |steps|
        {
          if |steps| == 0 then
            s
          else
            var s_next := H.Armada_GetNextStateAlways(s, steps[0]);
            ApplySteps_H(s_next, steps[1..])
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function NextState_H(s: HState, entry: HStep): HState
        {
          ApplySteps_H(s, entry.steps)
        }
      ";
      pgp.AddFunction(str, "specs");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Step abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual MatchCaseExpr GetTraceEntryCaseForSuppressedNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      // This is the case where the next routine doesn't have a corresponding next routine in the high layer,
      // e.g., because it's an assignment to a hidden variable.  In this case, just arbitrarily map it to
      // something we know to exist, namely H.Armada_TraceEntry_Tau.

      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var case_body = AH.MakeApply1("H.Armada_TraceEntry_Tau", tid, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected virtual MatchCaseExpr GetTraceEntryCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      string hname;

      var hNextRoutine = LiftNextRoutine(nextRoutine);
      if (hNextRoutine != null) {
        bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));
        ps.AddRange(nextRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType)));
        hname = hNextRoutine.NameSuffix;
      }
      else {
        hname = "Tau";
      }

      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutine.NameSuffix}", bvs, case_body);
      return case0;
    }

    protected virtual MatchCaseExpr GetTraceEntryCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      return GetTraceEntryCaseForNormalNextRoutine_LH(nextRoutine);
    }

    protected virtual void GenerateConvertTraceEntry_LH()
    {
      var cases = new List<MatchCaseExpr>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        cases.Add(GetTraceEntryCaseForNextRoutine_LH(nextRoutine));
      }

      var source = AH.MakeNameSegment("entry", "L.Armada_TraceEntry");
      var body = AH.MakeMatchExpr(source, cases, "H.Armada_TraceEntry");
      var formals = new List<Formal> { AH.MakeFormal("entry", "L.Armada_TraceEntry") };
      var fn = AH.MakeFunction("ConvertTraceEntry_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");

      string str = @"
        function ConvertMultistep_LH(entry: LStep) : HStep
        {
          Armada_Multistep(MapSeqToSeq(entry.steps, ConvertTraceEntry_LH), entry.tid, entry.tau)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    /// State refinement functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateConvertPC_HL(Dictionary<ArmadaPC, ArmadaPC> reversePCMap)
    {
      var cases = new List<MatchCaseExpr>();

      foreach (var mapping in reversePCMap) {
        var case_body = AH.MakeNameSegment($"L.{mapping.Value}", "L.Armada_PC");
        cases.Add(AH.MakeMatchCaseExpr(mapping.Key.ToString(), case_body));
      }

      var source = AH.MakeNameSegment("pc", "H.Armada_PC");
      var body = AH.MakeMatchExpr(source, cases, "L.Armada_PC");
      var formals = new List<Formal> { AH.MakeFormal("pc", "H.Armada_PC") };
      var fn = AH.MakeFunction("ConvertPC_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertStackFrame_HL()
    {
      var cases = new List<MatchCaseExpr>();
      var methodNames = pgp.symbolsHigh.MethodNames;
      foreach (var methodName in methodNames) {
        var smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
        var ps = new List<Expression>();
        var bvs = new List<BoundVar>();
        foreach (var v in smst.AllVariablesInOrder) {
          var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
          var e = AH.MakeNameSegment(v.FieldName, ty);
          ps.Add(e);
          var bv = AH.MakeBoundVar(v.FieldName, v.GetFlattenedType(pgp.symbolsHigh));
          bvs.Add(bv);
        }
        var case_body = AH.MakeApplyN($"L.Armada_StackFrame_{methodName}", ps, "L.Armada_StackFrame");
        cases.Add(AH.MakeMatchCaseExpr($"Armada_StackFrame_{methodName}", bvs, case_body));
      }

      var source = AH.MakeNameSegment("frame", "H.Armada_StackFrame");
      var body = AH.MakeMatchExpr(source, cases, "L.Armada_StackFrame");
      var formals = new List<Formal> { AH.MakeFormal("frame", "H.Armada_StackFrame") };
      var fn = AH.MakeFunction("ConvertStackFrame_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertGlobals_HL()
    {
      var g = AH.MakeNameSegment("globals", "H.Armada_Globals");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is AddressableArmadaVariable) {
          var p = AH.MakeExprDotName(g, v.FieldName, "Armada_Pointer");
          ps.Add(p);
        }
        else {
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("L.Armada_Globals", ps, "L.Armada_Globals");
      var formals = new List<Formal> { AH.MakeFormal("globals", "H.Armada_Globals") };
      var fn = AH.MakeFunction("ConvertGlobals_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertGhosts_HL()
    {
      var g = AH.MakeNameSegment("ghosts", "H.Armada_Ghosts");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
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

    protected virtual void GenerateConvertAddrs_HL()
    {
      var addrs = AH.MakeNameSegment("addrs", "H.Armada_Addrs");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalAddressableArmadaVariable) {
          var p = AH.MakeExprDotName(addrs, v.FieldName, "Armada_Pointer");
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("L.Armada_Addrs", ps, "L.Armada_Addrs");
      var formals = new List<Formal> { AH.MakeFormal("addrs", "H.Armada_Addrs") };
      var fn = AH.MakeFunction("ConvertAddrs_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertGlobalStaticVar_HL()
    {
      var cases = new List<MatchCaseExpr>();
      var case_body = AH.MakeNameSegment("L.Armada_GlobalStaticVarNone", "L.Armada_GlobalStaticVar");
      cases.Add(AH.MakeMatchCaseExpr("Armada_GlobalStaticVarNone", case_body));
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is UnaddressableArmadaVariable && !gv.NoTSO()) {
          case_body = AH.MakeNameSegment($"L.Armada_GlobalStaticVar_{varName}", "L.Armada_GlobalStaticVar");
          cases.Add(AH.MakeMatchCaseExpr($"Armada_GlobalStaticVar_{varName}", case_body));
        }
      }
      var v = AH.MakeNameSegment("v", "H.Armada_GlobalStaticVar");
      var body = AH.MakeMatchExpr(v, cases, "L.Armada_GlobalStaticVar");
      var formals = new List<Formal> { AH.MakeFormal("v", "H.Armada_GlobalStaticVar") };
      var fn = AH.MakeFunction("ConvertGlobalStaticVar_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected virtual void GenerateConvertSharedMemory_HL()
    {
      string str = @"
        function ConvertSharedMemory_HL(mem: H.Armada_SharedMemory) : L.Armada_SharedMemory
        {
          L.Armada_SharedMemory(mem.heap, ConvertGlobals_HL(mem.globals))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBufferLocation_HL()
    {
      string str = @"
        function ConvertStoreBufferLocation_HL(loc:H.Armada_StoreBufferLocation) : L.Armada_StoreBufferLocation
        {
          match loc
            case Armada_StoreBufferLocation_Unaddressable(v, fields, value) =>
              L.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_HL(v), fields, value)
            case Armada_StoreBufferLocation_Addressable(p, value) =>
              L.Armada_StoreBufferLocation_Addressable(p, value)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBufferEntry_HL()
    {
      string str = @"
        function ConvertStoreBufferEntry_HL(entry:H.Armada_StoreBufferEntry) : L.Armada_StoreBufferEntry
        {
          L.Armada_StoreBufferEntry(ConvertStoreBufferLocation_HL(entry.loc), entry.value)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBuffer_HL()
    {
      string str = @"
        function ConvertStoreBuffer_HL(entries:seq<H.Armada_StoreBufferEntry>) : seq<L.Armada_StoreBufferEntry>
        {
          MapSeqToSeq(entries, ConvertStoreBufferEntry_HL)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertExtendedFrame_HL()
    {
      string str = @"
        function ConvertExtendedFrame_HL(eframe:H.Armada_ExtendedFrame) : L.Armada_ExtendedFrame
        {
          L.Armada_ExtendedFrame(ConvertPC_HL(eframe.return_pc), ConvertStackFrame_HL(eframe.frame), eframe.new_ptrs)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStack_HL()
    {
      string str = @"
        function ConvertStack_HL(stack:seq<H.Armada_ExtendedFrame>) : seq<L.Armada_ExtendedFrame>
        {
          MapSeqToSeq(stack, ConvertExtendedFrame_HL)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertThread_HL()
    {
      string str = @"
        function ConvertThread_HL(t:H.Armada_Thread) : L.Armada_Thread
        {
          L.Armada_Thread(ConvertPC_HL(t.pc), ConvertStackFrame_HL(t.top), t.new_ptrs, ConvertStack_HL(t.stack),
                          ConvertStoreBuffer_HL(t.storeBuffer))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertThreads_HL()
    {
      string str = @"
        function ConvertThreads_HL(threads:map<Armada_ThreadHandle, H.Armada_Thread>) : map<Armada_ThreadHandle, L.Armada_Thread>
        {
          MapMapToMap(threads, ConvertThread_HL)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertTotalState_HL()
    {
      string str = @"
        function ConvertTotalState_HL(s:H.Armada_TotalState) : L.Armada_TotalState
        {
          L.Armada_TotalState(s.stop_reason, ConvertThreads_HL(s.threads), ConvertSharedMemory_HL(s.mem), ConvertGhosts_HL(s.ghosts),
                              ConvertAddrs_HL(s.addrs))
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertConfig_HL()
    {
      string str = @"
        function ConvertConfig_HL(config:H.Armada_Config) : L.Armada_Config
        {
          L.Armada_Config(config.tid_init, config.new_ptrs)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateStateAbstractionFunctions_HL(Dictionary<ArmadaPC, ArmadaPC> reversePCMap)
    {
      GenerateConvertPC_HL(reversePCMap);
      GenerateConvertStackFrame_HL();
      GenerateConvertGlobals_HL();
      GenerateConvertGhosts_HL();
      GenerateConvertAddrs_HL();
      GenerateConvertGlobalStaticVar_HL();
      GenerateConvertSharedMemory_HL();
      GenerateConvertStoreBufferLocation_HL();
      GenerateConvertStoreBufferEntry_HL();
      GenerateConvertStoreBuffer_HL();
      GenerateConvertExtendedFrame_HL();
      GenerateConvertStack_HL();
      GenerateConvertThread_HL();
      GenerateConvertThreads_HL();
      GenerateConvertTotalState_HL();
      GenerateConvertConfig_HL();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Proof header
    ////////////////////////////////////////////////////////////////////////

    public void AddCommonHeaderElements(ProofFile proof)
    {
      proof.AddInclude(pgp.mLow.Name + ".dfy");
      proof.AddInclude(pgp.mHigh.Name + ".dfy");
      proof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/refinement/AnnotatedBehavior.i.dfy");
      if (pgp.symbolsLow.StructsModuleName != null) {
        proof.AddInclude($"{pgp.symbolsLow.StructsModuleName}.dfy");
      }
      foreach (var importedFile in importedFiles) {
        proof.AddInclude(importedFile);
      }

      proof.AddImport(pgp.mLow.Name, "L");
      proof.AddImport(pgp.mHigh.Name, "H");
      proof.AddImport("AnnotatedBehaviorModule");
      if (pgp.symbolsLow.StructsModuleName != null) {
        proof.AddImport(pgp.symbolsLow.StructsModuleName);
      }
      foreach (var importedModule in importedModules) {
        proof.AddImport(importedModule);
      }
    }

    protected void GenerateProofHeader()
    {
      pgp.proofFiles.AssociateProofGenerator(this);
      GenerateSpecsFile();
    }

    protected void GenerateSpecsFile()
    {
      pgp.AddImport("util_collections_seqs_s", null, "specs");

      var lstate = AH.ReferToType("L.Armada_TotalState");
      pgp.AddTypeSynonymDecl("LState", lstate, "specs");
      lstate = AH.ReferToType("LState");
      var hstate = AH.ReferToType("H.Armada_TotalState");
      pgp.AddTypeSynonymDecl("HState", hstate, "specs");
      hstate = AH.ReferToType("HState");
      var lstep = AH.ReferToType("Armada_Multistep<L.Armada_TraceEntry>");
      pgp.AddTypeSynonymDecl("LStep", lstep, "specs");
      lstep = AH.ReferToType("LStep");
      var hstep = AH.ReferToType("Armada_Multistep<H.Armada_TraceEntry>");
      pgp.AddTypeSynonymDecl("HStep", hstep, "specs");
      hstep = AH.ReferToType("HStep");
      var lconfig = AH.ReferToType("L.Armada_Config");

      var lspec = AH.MakeGenericTypeSpecific("AnnotatedBehaviorSpec", new List<Type>{ lstate, lstep });
      pgp.AddTypeSynonymDecl("LSpec", lspec, "specs");
      var hspec = AH.MakeGenericTypeSpecific("AnnotatedBehaviorSpec", new List<Type>{ hstate, hstep });
      pgp.AddTypeSynonymDecl("HSpec", hspec, "specs");

      pgp.AddTypeSynonymDecl("LConfig", lconfig, "specs");

      var lplusstate = AH.ReferToType("LPlusState");
      var lplusspec = AH.MakeGenericTypeSpecific("AnnotatedBehaviorSpec", new List<Type>{ lplusstate, lstep });
      pgp.AddTypeSynonymDecl("LPlusSpec", lplusspec, "specs");

      string str;

      str = @"
        function GetLSpec() : LSpec
        {
          SpecFunctionsToSpec(L.Armada_GetSpecFunctions())
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function GetHSpec() : HSpec
        {
          SpecFunctionsToSpec(H.Armada_GetSpecFunctions())
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function GetLPlusSpec() : LPlusSpec
        {
          SpecFunctionsToSpec(LPlus_GetSpecFunctions())
        }
      ";
      pgp.AddFunction(str, "specs");

      str = $@"
        predicate LHStateRefinement(ls:LState, hs:HState)
        {{
          {pgp.symbolsLow.RefinementConstraint}
        }}
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        function GetLHRefinementRelation() : RefinementRelation<LState, HState>
        {
          iset p:RefinementPair<LState, HState> | LHStateRefinement(p.low, p.high)
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        predicate LPlusHStateRefinement(lplus:LPlusState, hs:HState)
        {
          LHStateRefinement(lplus.s, hs)
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        function GetLPlusHRefinementRelation() : RefinementRelation<LPlusState, HState>
        {
          iset p:RefinementPair<LPlusState, HState> | LPlusHStateRefinement(p.low, p.high)
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        predicate LPlus_Init(splus:LPlusState)
        {
          && L.Armada_InitConfig(splus.s, splus.config)
      ";
      foreach (var aux in auxiliaries) {
        str += $"  && splus.{aux.FieldName} == {aux.InitName}(splus.s, splus.config)\n";
      }
      str += "}\n";
      pgp.AddPredicate(str, "specs");

      str = @"
        predicate LPlus_ValidStep(s: LPlusState, step:L.Armada_TraceEntry)
        {
          L.Armada_ValidStep(s.s, step)
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        predicate LPlus_NextOneStep(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
        {
          && L.Armada_NextOneStep(s.s, s'.s, step)
          && s'.config == s.config
      ";
      foreach (var aux in auxiliaries) {
        str += $"  && s'.{aux.FieldName} == {aux.NextName}(s, s'.s, step)\n";
      }
      str += "}\n";
      pgp.AddPredicate(str, "specs");

      str = @"
        function MakeLPlusInitialState(s:LState) : (splus:LPlusState)
          requires s in L.Armada_Spec().init
          ensures  splus.s == s
          ensures  LPlus_Init(splus)
        {
          var config :| L.Armada_InitConfig(s, config);
      ";
      foreach (var aux in auxiliaries) {
        str += $"    var field_{aux.FieldName} := {aux.InitName}(s, config);\n";
      }
      str += "    LPlusState(s, config";
      foreach (var aux in auxiliaries) {
        str += $", field_{aux.FieldName}";
      }
      str += ")\n";
      str += "}\n";
      pgp.AddFunction(str, "specs");

      str = @"
        function LPlus_GetNextStateAlways(splus:LPlusState, step:L.Armada_TraceEntry) : (splus':LPlusState)
          ensures  L.Armada_ValidStep(splus.s, step) ==> LPlus_NextOneStep(splus, splus', step)
        {
          var s' := L.Armada_GetNextStateAlways(splus.s, step);
      ";
      foreach (var aux in auxiliaries) {
        str += $"  var field_{aux.FieldName} := {aux.NextName}(splus, s', step);\n";
      }
      str += "LPlusState(s', splus.config";
      foreach (var aux in auxiliaries) {
        str += $", field_{aux.FieldName}";
      }
      str += ")\n";
      str += "}\n";
      pgp.AddFunction(str, "specs");

      str = @"
        function LPlus_GetSpecFunctions() : Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
        {
          Armada_SpecFunctions(LPlus_Init, LPlus_ValidStep, LPlus_GetNextStateAlways,
                              (step: L.Armada_TraceEntry) => step.tid,
                              (step: L.Armada_TraceEntry) => step.Armada_TraceEntry_Tau?,
                              (s: LPlusState) => s.s.stop_reason.Armada_NotStopped?,
                              (s: LPlusState, tid: Armada_ThreadHandle) => if tid in s.s.threads then Some(s.s.threads[tid].pc) else None,
                              L.Armada_IsNonyieldingPC)
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        lemma lemma_PropertiesOfGetStateSequence_LPlus(s: LPlusState, steps: seq<L.Armada_TraceEntry>, states: seq<LPlusState>)
          requires states == Armada_GetStateSequence(LPlus_GetSpecFunctions(), s, steps)
          ensures forall i {:trigger states[i], steps[i]} :: 0 <= i < |steps| ==>
                                                             states[i + 1].s == L.Armada_GetNextStateAlways(states[i].s, steps[i])
          ensures forall i :: 0 <= i < |states| ==> states[i].s == Armada_GetStateSequence(L.Armada_GetSpecFunctions(), s.s, steps)[i]
        {
          var asf := L.Armada_GetSpecFunctions();
          forall i {:trigger states[i], steps[i]} | 0 <= i < |steps|
            ensures states[i + 1].s == L.Armada_GetNextStateAlways(states[i].s, steps[i])
          {
            lemma_ArmadaGetStateSequenceOnePos(LPlus_GetSpecFunctions(), s, steps, i);
          }
          var j := 1;
          while j < |states|
            invariant 1 <= j <= |states|
            invariant forall i :: 0 <= i < j ==> states[i].s == Armada_GetStateSequence(asf, s.s, steps)[i]
          {
            var prev := j-1;
            assert states[prev+1].s == L.Armada_GetNextStateAlways(states[prev].s, steps[prev]);
            assert states[prev].s == Armada_GetStateSequence(asf, s.s, steps)[prev];
            lemma_ArmadaGetStateSequenceOnePos(asf, s.s, steps, prev);
            assert states[prev+1].s == Armada_GetStateSequence(asf, s.s, steps)[prev+1];

            forall i | 0 <= i < j+1
              ensures states[i].s == Armada_GetStateSequence(asf, s.s, steps)[i]
            {
              if i < j {
                assert states[i].s == Armada_GetStateSequence(asf, s.s, steps)[i];
              }
              else {
                assert i == j == prev + 1;
                assert states[i].s == Armada_GetStateSequence(asf, s.s, steps)[i];
              }
            }

            j := j + 1;
          }
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        predicate LPlus_Next(s: LPlusState, s': LPlusState, entry: LStep)
        {
          Armada_NextMultistep(LPlus_GetSpecFunctions(), s, s', entry.steps, entry.tid, entry.tau)
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        function MakeLPlusNextMultipleSteps(splus: LPlusState, s': LState, steps: seq<L.Armada_TraceEntry>): (splus': LPlusState)
          requires Armada_NextMultipleSteps(L.Armada_GetSpecFunctions(), splus.s, s', steps)
          ensures  splus'.s == s'
          ensures  Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), splus, splus', steps)
          decreases |steps|
        {
          if |steps| == 0 then
            splus
          else
            var splus1 := LPlus_GetNextStateAlways(splus, steps[0]);
            MakeLPlusNextMultipleSteps(splus1, s', steps[1..])
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function MakeLPlusNextState(splus: LPlusState, s': LState, entry: LStep): (splus': LPlusState)
          requires L.Armada_Next(splus.s, s', entry)
          ensures  splus'.s == s'
          ensures  LPlus_Next(splus, splus', entry)
        {
          lemma_PropertiesOfGetStateSequence_LPlus(splus, entry.steps,
                                                       Armada_GetStateSequence(LPlus_GetSpecFunctions(), splus, entry.steps));
          MakeLPlusNextMultipleSteps(splus, s', entry.steps)
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        lemma lemma_LPlusNextMultipleStepsImpliesLNextMultipleSteps(
          ls: LPlusState,
          ls': LPlusState,
          lsteps: seq<L.Armada_TraceEntry>
          )
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          ensures  Armada_NextMultipleSteps(L.Armada_GetSpecFunctions(), ls.s, ls'.s, lsteps)
          decreases |lsteps|
        {
          if |lsteps| > 0 {
            var ls_next := LPlus_GetNextStateAlways(ls, lsteps[0]);
            lemma_LPlusNextMultipleStepsImpliesLNextMultipleSteps(ls_next, ls', lsteps[1..]);
          }
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_GetLAnnotatedBehavior(lb:seq<L.Armada_TotalState>) returns (alb:AnnotatedBehavior<LState, LStep>)
            requires BehaviorSatisfiesSpec(lb, L.Armada_Spec())
            ensures  AnnotatedBehaviorSatisfiesSpec(alb, GetLSpec())
            ensures  alb.states == lb
        {
            if |lb| == 1 {
                return AnnotatedBehavior(lb, []);
            }

            var pos := |lb|-2;
            var alb_prev := lemma_GetLAnnotatedBehavior(all_but_last(lb));
            assert 0 <= pos < |lb|-1;
            assert StatePair(lb[pos], lb[pos+1]) in L.Armada_Spec().next;
            var entry :| L.Armada_Next(lb[pos], lb[pos+1], entry);
            alb := AnnotatedBehavior(lb, alb_prev.trace + [entry]);
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(hb:AnnotatedBehavior<HState, HStep>)
            requires AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
            ensures  BehaviorSatisfiesSpec(hb.states, H.Armada_Spec())
        {
            var b := hb.states;

            forall i | 0 <= i < |b|-1
                ensures StatePair(b[i], b[i+1]) in H.Armada_Spec().next
            {
              var s := hb.states[i];
              var s' := hb.states[i+1];
              var entry := hb.trace[i];
              assert ActionTuple(s, s', entry) in GetHSpec().next;
              assert Armada_NextMultistep(H.Armada_GetSpecFunctions(), s, s', entry.steps, entry.tid, entry.tau);
              assert H.Armada_Next(s, s', entry);
              assert StatePair(s, s') in H.Armada_Spec().next;
            }
        }
      ";
      pgp.AddLemma(str, "specs");

      var formals = new List<Formal>();
      formals.Add(AH.MakeFormal("s", "LState"));
      formals.Add(AH.MakeFormal("config", "LConfig"));
      foreach (var aux in auxiliaries) {
        formals.Add(AH.MakeFormal(aux.FieldName, aux.TypeName));
      }
      pgp.AddDatatypeDecl("LPlusState", new List<DatatypeCtor> { AH.MakeDatatypeCtor("LPlusState", formals) }, "specs");

      str = @"
        lemma lemma_GetLPlusAnnotatedBehavior(lb:seq<LState>) returns (alb:AnnotatedBehavior<LPlusState, LStep>)
          requires BehaviorSatisfiesSpec(lb, L.Armada_Spec())
          ensures  AnnotatedBehaviorSatisfiesSpec(alb, GetLPlusSpec())
          ensures  |alb.states| == |lb|
          ensures  forall i :: 0 <= i < |lb| ==> alb.states[i].s == lb[i]
        {
          var spec := L.Armada_Spec();

          var splus0 := MakeLPlusInitialState(lb[0]);
          var states:seq<LPlusState> := [splus0];
          var trace:seq<LStep> := [];

          while |states| < |lb|
            invariant |states| == |trace| + 1
            invariant 1 <= |states| <= |lb|
            invariant LPlus_Init(states[0])
            invariant forall i :: 0 <= i < |states|-1 ==> LPlus_Next(states[i], states[i+1], trace[i])
            invariant forall i :: 0 <= i < |states| ==> states[i].s == lb[i]
          {
            var pos := |states|-1;
            var s := lb[pos];
            var s' := lb[pos+1];
            assert states[pos].s == s;
            assert 0 <= pos < |lb|-1;
            assert StatePair(lb[pos], lb[pos + 1]) in L.Armada_Spec().next;
            var step :| L.Armada_Next(lb[pos], lb[pos + 1], step);
            var splus := states[pos];
            var splus' := MakeLPlusNextState(splus, s', step);
            states := states + [splus'];
            trace := trace + [step];
          }

          alb := AnnotatedBehavior(states, trace);
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb:seq<LState>, lplusb:seq<LPlusState>, hb:seq<HState>)
          requires |lb| == |lplusb|
          requires forall i :: 0 <= i < |lb| ==> lplusb[i].s == lb[i]
          requires BehaviorRefinesBehavior(lplusb, hb, GetLPlusHRefinementRelation())
          ensures  BehaviorRefinesBehavior(lb, hb, GetLHRefinementRelation())
        {
          var lplush_relation := GetLPlusHRefinementRelation();
          var lh_relation := GetLHRefinementRelation();
          var lh_map:RefinementMap :| BehaviorRefinesBehaviorUsingRefinementMap(lplusb, hb, lplush_relation, lh_map);
          forall i, j {:trigger RefinementPair(lb[i], hb[j]) in lh_relation} | 0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in lh_relation;
          {
            assert RefinementPair(lplusb[i], hb[j]) in lplush_relation;
            assert RefinementPair(lplusb[i].s, hb[j]) in lh_relation;
            assert RefinementPair(lb[i], hb[j]) in lh_relation;
          }
          assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetLHRefinementRelation(), lh_map);
        }
      ";
      pgp.AddLemma(str, "specs");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about region invariant
    ////////////////////////////////////////////////////////////////////////

    protected virtual List<string> GenerateAddressableInvariant_Global()
    {
      pgp.AuxiliaryProof("specs").AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.AuxiliaryProof("specs").AddImport("util_collections_maps_i");

      string str = "";
      var predBuilder = new PredicateBuilder(pgp.prog);
      var abstractAddresses = new List<string>();
      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        if (globalVar is GlobalAddressableArmadaVariable) {
          string globalAddress = $"s.s.addrs.{globalVarName}";
          predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", $"Armada_TriggerPointer({globalAddress})"));
          predBuilder.AddConjunct(AH.GetInvocationOfValidPointer(AH.MakeNameSegment("s.s.mem.heap", "Armada_Heap"), AH.MakeNameSegment($"s.s.addrs.{globalVarName}", "Armada_Pointer"), globalVar.ty));
          var allocatedByExpr = AH.GetInvocationOfAllocatedBy(AH.MakeNameSegment("s.s.mem.heap", "Armada_Heap"), AH.MakeNameSegment($"s.s.addrs.{globalVarName}", "Armada_Pointer"), globalVar.ty);
          str  = $@"
            (forall p {{:trigger Armada_TriggerPointer(p)}}
              :: p in {Printer.ExprToString(allocatedByExpr)} && Armada_TriggerPointer(p) ==>
              p in s.addr_map && s.addr_map[p] == GlobalAbstractAddress_{globalVarName})
          ";
          abstractAddresses.Add($"GlobalAbstractAddress_{globalVarName}");
          predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
        }
      }

      str =  $@"
      predicate AddressableInvariant_Globals(s: LPlusState)
      {{
        {Printer.ExprToString(predBuilder.Extract())}
      }}";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, $"AddressableInvariant_Globals", str), "invariants");
      return abstractAddresses;
    }

    protected virtual List<string> GenerateAddressableInvariant_StackFrame(string methodName)
    {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var predBuilder = new PredicateBuilder(pgp.prog);
      string str;
      var abstractAddresses = new List<string>();
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", $"Armada_TriggerPointer(frame.{varStackFrameFieldName})"));
        predBuilder.AddConjunct(AH.GetInvocationOfValidPointer(AH.MakeNameSegment("heap", "Armada_Heap"), AH.MakeNameSegment($"frame.{varStackFrameFieldName}", "Armada_Pointer"), localVar.ty));
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(AH.MakeNameSegment("heap", "Armada_Heap"), AH.MakeNameSegment($"frame.{varStackFrameFieldName}", "Armada_Pointer"), localVar.ty);
        str  = $@"
          && (forall p {{:trigger Armada_TriggerPointer(p)}}
            :: p in {Printer.ExprToString(allocatedByExpr)} && Armada_TriggerPointer(p) ==>
            p in addr_map && addr_map[p] == LocalAbstractAddress_{methodName.Replace("_", "__")}_{varStackFrameFieldName.Replace("_", "__")}(tid, h))
        ";
        abstractAddresses.Add($"LocalAbstractAddress_{methodName.Replace("_", "__")}_{varStackFrameFieldName.Replace("_", "__")}(tid:Armada_ThreadHandle, h:int)");
        predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
      }
      str =  $@"
      predicate AddressableInvariant_StackFrame_{methodName}(addr_map:map<Armada_Pointer, AbstractAddress>,
        frame: L.Armada_StackFrame, tid: Armada_ThreadHandle, h: int, heap: Armada_Heap)
        requires frame.Armada_StackFrame_{methodName}?
      {{
        {Printer.ExprToString(predBuilder.Extract())}
      }}";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, $"AddressableInvariant_StackFrame_{methodName}", str), "invariants");
      return abstractAddresses;
    }

    protected virtual void GenerateAddressableMapInit()
    {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable("main");
      MapBuilder mapBuilder = new MapBuilder("m");

      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        var localAddress = $"s.threads[config.tid_init].top.{varStackFrameFieldName}";
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
          AH.MakeNameSegment("s.mem.heap", "Armada_Heap"),
          AH.MakeNameSegment(localAddress, "Armada_Pointer"),
          localVar.ty
        );
        mapBuilder.Add(Printer.ExprToString(allocatedByExpr),
          $"LocalAbstractAddress_main_{varStackFrameFieldName.Replace("_","__")}(config.tid_init, 0)");
      }
      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        if (globalVar is GlobalAddressableArmadaVariable) {
          string globalAddress = $"s.addrs.{globalVarName}";
          var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
            AH.MakeNameSegment("s.mem.heap", "Armada_Heap"),
            AH.MakeNameSegment(globalAddress, "Armada_Pointer"),
            globalVar.ty
          );
          mapBuilder.Add(Printer.ExprToString(allocatedByExpr), $"GlobalAbstractAddress_{globalVarName}");
        }
      }

      string str =$@"
        function AddrMapInit(s: LState, config: LConfig): map<Armada_Pointer, AbstractAddress>
          requires L.Armada_InitConfig(s, config)
        {{
          {mapBuilder.Extract()}
        }}
        ";
      pgp.AddDefaultClassDecl((Function)AH.ParseTopLevelDecl(pgp.prog, "AddrMapInit", str), "specs");
    }

    protected virtual string GenerateAddressableMapNextCase_Call(NextRoutine nextRoutine)
    {
      var armadaCallStmt = (ArmadaCallStatement)nextRoutine.armadaStatement;
      var methodName = armadaCallStmt.CalleeName;
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      MapBuilder mapBuilder = new MapBuilder("m", "splus.addr_map");
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        var localAddress = $"new_frame.{varStackFrameFieldName}";
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
          AH.MakeNameSegment("s'.mem.heap", "Armada_Heap"),
          AH.MakeNameSegment(localAddress, "Armada_Pointer"),
          localVar.ty
        );
        mapBuilder.Add(Printer.ExprToString(allocatedByExpr),
          $"LocalAbstractAddress_{methodName.Replace("_", "__")}_{varStackFrameFieldName.Replace("_", "__")}(step.tid, |s'.threads[step.tid].stack|)");
      }
      string str = $@"
        if s'.stop_reason.Armada_NotStopped? then
          var new_frame := s'.threads[step.tid].top; {mapBuilder.Extract()}
        else
          splus.addr_map
      ";
      return str;
    }
    protected virtual string GenerateAddressableMapNextCase_CreateThread(NextRoutine nextRoutine)
    {
      var armadaCreateThreadStmt = (ArmadaCreateThreadStatement)nextRoutine.armadaStatement;
      var stmt = (UpdateStmt)armadaCreateThreadStmt.Stmt;
      var rhs = (CreateThreadRhs)stmt.Rhss[0];
      var methodName = rhs.MethodName.val;
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      MapBuilder mapBuilder = new MapBuilder("m", "splus.addr_map");
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        var localAddress = $"new_frame.{varStackFrameFieldName}";
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
          AH.MakeNameSegment("s'.mem.heap", "Armada_Heap"),
          AH.MakeNameSegment(localAddress, "Armada_Pointer"),
          localVar.ty
        );
        mapBuilder.Add(Printer.ExprToString(allocatedByExpr),
          $"LocalAbstractAddress_{methodName.Replace("_", "__")}_{varStackFrameFieldName.Replace("_", "__")}(newtid, 0)");
      }
      string str = $@"
        if s'.stop_reason.Armada_NotStopped? then
          var newtid := step.newtid_{armadaCreateThreadStmt.StartPC}; var new_frame := s'.threads[newtid].top; {mapBuilder.Extract()}
        else
          splus.addr_map
      ";
      return str;
    }

    protected virtual string GenerateAddressableMapNextCase(NextRoutine nextRoutine)
    {
      string caseBody = "";
      if (nextRoutine.nextType == NextType.Call) {
        caseBody = GenerateAddressableMapNextCase_Call(nextRoutine);
      }
      else if (nextRoutine.nextType == NextType.CreateThread) {
        caseBody = GenerateAddressableMapNextCase_CreateThread(nextRoutine);
      }
      else {
        caseBody = "splus.addr_map";
      }

      string formalUnderscores = "_" + string.Join("", nextRoutine.Formals.Select(f => $", _"));
      return $"case Armada_TraceEntry_{nextRoutine.NameSuffix}({formalUnderscores}) => {caseBody}";
    }

    protected virtual void GenerateAddressableMapNext()
    {
      var caseStrings = new List<string>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        caseStrings.Add(GenerateAddressableMapNextCase(nextRoutine));
      }

      string str = $@"
        function AddrMapNext(splus: LPlusState, s': LState, step: L.Armada_TraceEntry): map<Armada_Pointer, AbstractAddress>
          requires s' == L.Armada_GetNextStateAlways(splus.s, step);
        {{
          if L.Armada_ValidStep(splus.s, step) then
            match step
            {{
              {string.Join("\n", caseStrings)}
            }}
          else
            splus.addr_map
        }}
      ";
      pgp.AddDefaultClassDecl((Function)AH.ParseTopLevelDecl(pgp.prog, "AddrMapNext", str), "specs");
    }

    protected virtual void GenerateAddressableMapAux(List<string> abstractAddresses)
    {
      string datatypeDecl = "datatype AbstractAddress = " + string.Join(" | ", abstractAddresses);
      if (abstractAddresses.Count == 0) {
        datatypeDecl = "datatype AbstractAddress = AbstractAddress_None";
      }
      pgp.AddDatatype(datatypeDecl, "specs");

      GenerateAddressableMapNext();
      GenerateAddressableMapInit();

      var auxiliaryInfo = new AuxiliaryInfo("addr_map", "map<Armada_Pointer, AbstractAddress>", "AddrMapInit", "AddrMapNext");
      auxiliaries.Add(auxiliaryInfo);
    }

    protected virtual void GenerateAddressableInvariant()
    {
      GenerateValidStackFramePredicate();
      string body = $@"";
      List<string> abstractAddresses = new List<string>();
      abstractAddresses = GenerateAddressableInvariant_Global();
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        abstractAddresses.AddRange(GenerateAddressableInvariant_StackFrame(methodName));
        body += $@"
          && (forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_{methodName}?
            ==>
            var frame := s.s.threads[tid].top; var heap := s.s.mem.heap;
            AddressableInvariant_StackFrame_{methodName}(s.addr_map, frame, tid, |s.s.threads[tid].stack|, heap)
          )

          && (forall tid, h:: tid in s.s.threads && 0 <= h < |s.s.threads[tid].stack| &&  s.s.threads[tid].stack[h].frame.Armada_StackFrame_{methodName}?
              ==>
              var frame := s.s.threads[tid].stack[h].frame; var heap := s.s.mem.heap;
              AddressableInvariant_StackFrame_{methodName}(s.addr_map, frame, tid, |s.s.threads[tid].stack| - 1 - h, heap)
          )
        ";
      }
      GenerateAddressableMapAux(abstractAddresses);

      string predicateDecl = $@"
        predicate AddressableInvariant(s: LPlusState)
        {{
          {body}
          && AllValidStackFrames(s)
          && AddressableInvariant_Globals(s)
          && (forall p :: p in s.addr_map ==> (p in s.s.mem.heap.valid || p in s.s.mem.heap.freed) )
        }}
      ";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "AddressableInvariant", predicateDecl), "invariants");

      AddInvariant(new InternalInvariantInfo("AddressableInvariant", "AddressableInvariant", new List<string>()));
    }

    protected virtual void GenerateValidStackMethod(string methodName) {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var predBuilder = new PredicateBuilder(pgp.prog);
      string p_in_new_ptrs = "";
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        predBuilder.AddConjunct(AH.GetInvocationOfValidPointer(AH.MakeNameSegment("heap", "Armada_Heap"), AH.MakeNameSegment($"frame.{varStackFrameFieldName}", localVar.ty), localVar.ty));
        string str = $@"
            heap.tree[frame.{varStackFrameFieldName}].field_of_parent.Armada_FieldNone?
            && heap.tree[frame.{varStackFrameFieldName}].field_of_parent.rt.Armada_RootTypeStack?";
        predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
        var allocatedByExpr = AH.GetInvocationOfAllocatedBy(
          AH.MakeNameSegment("heap", "Armada_Heap"),
          AH.MakeNameSegment($"frame.{varStackFrameFieldName}", "Armada_Pointer"),
          localVar.ty
        );
        p_in_new_ptrs += $"|| p in {Printer.ExprToString(allocatedByExpr)}";
      }

      string newPtrsIsAllocatedAddresses;
      if (p_in_new_ptrs.Length > 0) {
        newPtrsIsAllocatedAddresses = $"forall p {{:trigger Armada_TriggerPointer(p)}}:: (Armada_TriggerPointer(p) && p in new_ptrs) <==> (Armada_TriggerPointer(p) && ({p_in_new_ptrs}))";
      } else {
        newPtrsIsAllocatedAddresses = "new_ptrs == {}";
      }
       
      predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", newPtrsIsAllocatedAddresses));
      string predicateDecl = $@"
        predicate ValidStackFrame_{methodName}(frame: L.Armada_StackFrame, heap: Armada_Heap, new_ptrs: set<Armada_Pointer>) 
        requires frame.Armada_StackFrame_{methodName}?
        {{
          {Printer.ExprToString(predBuilder.Extract())}
        }}
      ";

      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "ValidStackFrame_{methodName}", predicateDecl), "invariants");
    }

    protected virtual void GenerateValidStackFramePredicate()
    {
      string caseBody = "";
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        GenerateValidStackMethod(methodName);

        caseBody += $@"
            && (forall tid :: tid in s.s.threads 
              && s.s.threads[tid].top.Armada_StackFrame_{methodName}? ==>
              var t := s.s.threads[tid]; ValidStackFrame_{methodName}(t.top, s.s.mem.heap, t.new_ptrs))
            && (forall tid, h :: tid in s.s.threads && 0 <= h < |s.s.threads[tid].stack| && s.s.threads[tid].stack[h].frame.Armada_StackFrame_{methodName}? ==>
                ValidStackFrame_{methodName}(s.s.threads[tid].stack[h].frame, s.s.mem.heap, s.s.threads[tid].stack[h].new_ptrs))
        ";
       }

       string str = $@"
        predicate AllValidStackFrames(s: LPlusState)
        {{
            {caseBody}
        }}
       ";

       pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "AllValidStackFrames", str), "invariants");
    }

    public class RegionInfo
    {
      public Dictionary<string, string> globalPtrVarRegionMap;
      public Dictionary<string, string> globalAddrVarRegionMap;
      public Dictionary<string, Dictionary<string, string>> methodToPtrVarRegionTable;
      public Dictionary<string, Dictionary<string, string>> methodToAddrVarRegionTable;
      public List<string> regionIds;

      public RegionInfo()
      {
        globalPtrVarRegionMap = new Dictionary<string, string>();
        globalAddrVarRegionMap = new Dictionary<string, string>();
        methodToPtrVarRegionTable = new Dictionary<string, Dictionary<string, string>>();
        methodToAddrVarRegionTable = new Dictionary<string, Dictionary<string, string>>();
        regionIds = new List<string>();
      }

      public string GetGlobalRegionId(string varName)
      {
        string regionId = null;
        if (varName.Length > 0 && varName[0] == '&') {
          globalAddrVarRegionMap.TryGetValue(varName.Substring(1), out regionId);
        }
        else {
          globalPtrVarRegionMap.TryGetValue(varName, out regionId);
        }
        return regionId;
      }

      public string GetLocalRegionId(string methodName, string varName)
      {
        string regionId = null;
        Dictionary<string, string> methodAddrVarRegionTable = null;
        if (methodToAddrVarRegionTable.TryGetValue(methodName, out methodAddrVarRegionTable)) {
          if (varName.Length > 0 && varName[0] == '&') {
            methodToAddrVarRegionTable[methodName].TryGetValue(varName.Substring(1), out regionId);
          }
          else {
            methodToPtrVarRegionTable[methodName].TryGetValue(varName, out regionId);
          }
        }
        return regionId;
      }

      public string GetRegionId(string methodName, string varName)
      {
        string regionId = GetLocalRegionId(methodName, varName);
        if (regionId == null) {
          regionId = GetGlobalRegionId(varName);
        }
        return regionId;
      }
    }

    // Initial region of &globalVariable is represented as `r_&globalVariableName`
    // Initial region of globalPointer is represented as `r_globalPointer`
    // Initial region of methodName's &localVariable is represented as `r_methodName.&localVariable`
    // Initial region of methodName's localPointer is represented as `r_methodName.localVariable`
    // Initial region of methodName's Malloc/Calloc statement at PC=p is represented `alloc_r_methodName[p]`

    private RegionInfo GenerateInitialRegionInfo()
    {
      RegionInfo r = new RegionInfo();

      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        // Global addressable variables
        if (globalVar is GlobalAddressableArmadaVariable) {
          r.globalAddrVarRegionMap[globalVarName] = $"rga_{globalVarName}";
          r.regionIds.Add($"rga_{globalVarName}");
        }
        if (globalVar.ty is PointerType) {
          r.globalPtrVarRegionMap[globalVarName] = $"rgp_{globalVarName}";
          r.regionIds.Add($"rgp_{globalVarName}");
        }
      }

      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        Dictionary<string, string> ptrRegionTable = new Dictionary<string, string>();
        Dictionary<string, string> addrRegionTable = new Dictionary<string, string>();
        foreach (var localVar in methodSymbols.AllVariables) {
          var localVarName = localVar.name;
          if (localVar is MethodStackFrameAddressableLocalArmadaVariable) {
            addrRegionTable[localVarName] = $"rap_{methodName.Replace("_", "__")}_{localVarName.Replace("_", "__")}";
            r.regionIds.Add($"rap_{methodName.Replace("_", "__")}_{localVarName.Replace("_", "__")}");
          }
          if (localVar.ty is PointerType) {
            ptrRegionTable[localVarName] = $"rlp_{methodName.Replace("_", "__")}_{localVarName.Replace("_", "__")}";
            r.regionIds.Add($"rlp_{methodName.Replace("_", "__")}_{localVarName.Replace("_", "__")}");
          }
          r.methodToAddrVarRegionTable[methodName] = addrRegionTable;
          r.methodToPtrVarRegionTable[methodName] = ptrRegionTable;
        }
      }
      // Console.WriteLine(string.Join(" ", r.regionIds));
      return r;
    }

    protected virtual List<string> GetPossibleResultantVariables(Expression expr)
    {
      var vars = new List<string>();
      if (expr is NameSegment) // return `variable`
      {
        var e = (NameSegment)expr;
        vars.Add(e.Name);
      }
      if (expr is UnaryOpExpr)
      {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.AddressOf)
        {
          vars.Add(Printer.ExprToString(e)); // Want to return `&variable`
        }
      }
      return vars;
    }

    protected virtual RegionInfo GenerateVariableRegionMap()
    {
      RegionInfo r = GenerateInitialRegionInfo();
      Dictionary<string, int> regionIdToIndex = new Dictionary<string, int>();
      List<string> indexToRegionId = new List<string>();
      int numRegions = 0;
      foreach (var regionId in r.regionIds)
      {
        regionIdToIndex[regionId] = numRegions;
        indexToRegionId.Add(regionId);
        numRegions += 1;
      }
      DisjointSet d = new DisjointSet(numRegions);

      // TODO: Merge for al initializations of pointer variables

      // Merge for all statements that force regions to be merged
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType == NextType.Update) {
          var updateStmt = (UpdateStmt)nextRoutine.stmt;
          var lhss = updateStmt.Lhss;
          var rhss = updateStmt.Rhss;
          var methodName = nextRoutine.method.Name;
          for (int i = 0; i < lhss.Count; ++i) {
            var lhs = lhss[i];
            var rhs_Rhs = rhss[i];
            
            var lhsVarName = Printer.ExprToString(lhs);

            var eRhs = (ExprRhs)rhs_Rhs;
            var rhs = eRhs.Expr;
            List<string> rhsVarNames = GetPossibleResultantVariables(rhs);
            var r1 = r.GetRegionId(methodName, lhsVarName);
            if (r1 != null) {
              foreach (var rhsVarName in rhsVarNames) {
                // Console.WriteLine($"Merging {lhsVarName} with {rhsVarName}");
                var r2 = r.GetRegionId(methodName, rhsVarName);
                // Console.WriteLine($"Merging region {r1} with {r2}");
                if (r2 != null) {
                  d.Join(regionIdToIndex[r1], regionIdToIndex[r2]);
                } else { // For whatever reason, we don't know the region of the RHS, so we can't reason about the LHS either.
                  //Console.WriteLine($"Region can't be specified for {lhsVarName} because of {Printer.ExprToString(rhs)}");
                }
              }
            } else {
              //Console.WriteLine(lhsVarName);
            }
          }
        }
        else if (nextRoutine.nextType == NextType.Call) {
          var methodName = nextRoutine.method.Name;
          var armadaCallStmt = (ArmadaCallStatement)nextRoutine.armadaStatement;
          var stmt = (UpdateStmt)armadaCallStmt.Stmt;
          var ex = (ExprRhs)stmt.Rhss[0];
          var suffix = (ApplySuffix)ex.Expr;
          var args = suffix.Args;
          var calledMethodName = armadaCallStmt.CalleeName;
          var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(calledMethodName);
          var methodInputVars = methodSymbols.InputVariableNames.ToList();
          for (int i = 0; i < methodInputVars.Count; i++) {
            var inputVar = methodSymbols.LookupVariable(methodInputVars[i]);
            if (inputVar.ty is PointerType) {
              var lhsVarName = methodInputVars[i];
              var arg = args[i];
              List<string> rhsVarNames = GetPossibleResultantVariables(arg);

              foreach (var rhsVarName in rhsVarNames) {
                // Console.WriteLine($"Merging {lhsVarName} with {rhsVarName}");
                var r1 = r.GetRegionId(calledMethodName, lhsVarName);
                var r2 = r.GetRegionId(methodName, rhsVarName);
                //Console.WriteLine($"Method varName: {methodName} {rhsVarName}");
                //Console.WriteLine($"Merging region {r1} with {r2}");
                if (r2 != null) {
                  d.Join(regionIdToIndex[r1], regionIdToIndex[r2]);
                } else { // For whatever reason, we don't know the region of the RHS, so we can't reason about the LHS either.
                  //Console.WriteLine($"Region can't be specified for {lhsVarName} because of {rhsVarName}");
                }
              }
            }
          }
        }
        else if (nextRoutine.nextType == NextType.CreateThread) {
          var methodName = nextRoutine.method.Name;
          var armadaCallStmt = (ArmadaCreateThreadStatement)nextRoutine.armadaStatement;
          var stmt = (UpdateStmt)armadaCallStmt.Stmt;
          var rhs = (CreateThreadRhs)stmt.Rhss[0];
          var calledMethodName = rhs.MethodName.val;
          var args = rhs.Args;
          var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(calledMethodName);
          var methodInputVars = methodSymbols.InputVariableNames.ToList();
          for (int i = 0; i < methodInputVars.Count; i++) {
            var inputVar = methodSymbols.LookupVariable(methodInputVars[i]);
            if (inputVar.ty is PointerType) {
              var lhsVarName = methodInputVars[i];
              var arg = args[i];
              List<string> rhsVarNames = GetPossibleResultantVariables(arg);

              foreach (var rhsVarName in rhsVarNames) {
                // Console.WriteLine($"Merging {lhsVarName} with {rhsVarName}");
                var r1 = r.GetRegionId(calledMethodName, lhsVarName);
                var r2 = r.GetRegionId(methodName, rhsVarName);
                // Console.WriteLine($"Merging region {r1} with {r2}");
                d.Join(regionIdToIndex[r1], regionIdToIndex[r2]);
              }
            }
          }
        }
      }

      foreach (var k in r.globalAddrVarRegionMap.Keys.ToList())
      {
        r.globalAddrVarRegionMap[k] = indexToRegionId[d.Find(regionIdToIndex[r.globalAddrVarRegionMap[k]])];
      }
      foreach (var k in r.globalPtrVarRegionMap.Keys.ToList())
      {
        r.globalPtrVarRegionMap[k] = indexToRegionId[d.Find(regionIdToIndex[r.globalPtrVarRegionMap[k]])];
      }
      foreach (var k1 in r.methodToAddrVarRegionTable.Keys.ToList())
      {
        foreach (var k2 in r.methodToAddrVarRegionTable[k1].Keys.ToList())
        {
          r.methodToAddrVarRegionTable[k1][k2] = indexToRegionId[d.Find(regionIdToIndex[r.methodToAddrVarRegionTable[k1][k2]])];
        }
      }
      foreach (var k1 in r.methodToPtrVarRegionTable.Keys.ToList())
      {
        foreach (var k2 in r.methodToPtrVarRegionTable[k1].Keys.ToList())
        {
          r.methodToPtrVarRegionTable[k1][k2] = indexToRegionId[d.Find(regionIdToIndex[r.methodToPtrVarRegionTable[k1][k2]])];
        }
      }

      HashSet<string> possibleRegionIds = new HashSet<string>();
      foreach(var pair in regionIdToIndex)
      {
         possibleRegionIds.Add(indexToRegionId[d.Find(pair.Value)]);
      }
      string str = "datatype RegionId = " + String.Join(" | ", possibleRegionIds);
      pgp.AddDatatype(str, "specs");
      return r;
    }

    protected virtual string GenerateRegionMapNextCase_CreateThread(NextRoutine nextRoutine, RegionInfo regionInfo)
    {
      var armadaCreateThreadStmt = (ArmadaCreateThreadStatement)nextRoutine.armadaStatement;
      var stmt = (UpdateStmt)armadaCreateThreadStmt.Stmt;
      var rhs = (CreateThreadRhs)stmt.Rhss[0];
      var methodName = rhs.MethodName.val;
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      List<string> mapUpdates = new List<string>();
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        string regionIdStr = regionInfo.GetRegionId(methodName, "&" + localVar.name);
        mapUpdates.Add($"[newframe_{localVar.name} := {regionIdStr}]");
      }
      string mapUpdateBody = string.Join("", mapUpdates);
      string str = $@"
        s.region_map{mapUpdateBody}
      ";
      return str;
    }

    protected virtual string GenerateRegionMapNextCase_Call(NextRoutine nextRoutine, RegionInfo regionInfo)
    {
      var armadaCallStmt = (ArmadaCallStatement)nextRoutine.armadaStatement;
      var methodName = armadaCallStmt.CalleeName;
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      List<string> mapUpdates = new List<string>();
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        string regionIdStr = regionInfo.GetRegionId(methodName, "&" + localVar.name);
        mapUpdates.Add($"[newframe_{localVar.name} := {regionIdStr}]");
      }
      string mapUpdateBody = string.Join("", mapUpdates);
      string str = $@"
        s.region_map{mapUpdateBody}
      ";
      return str;
    }
    
    protected virtual MatchCaseExpr GenerateRegionMapNextCase(NextRoutine nextRoutine, RegionInfo regionInfo)
    {
      string str = ""; // $"case Armada_TraceEntry_{nextRoutine.NameSuffix} => ";
      if (nextRoutine.nextType == NextType.Malloc)
      {
        var updateStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
        // Get the variable from the LHS and use that to determine the case 
        string methodName = nextRoutine.method.Name;
        string varName = Printer.ExprToString(updateStmt.Lhss[0]);
        var regionId = regionInfo.GetRegionId(methodName, varName);
        str = $"if new_ptr != 0 then s.region_map[new_ptr := {regionId}] else s.region_map";
      }
      else if (nextRoutine.nextType == NextType.Call) {
        str = GenerateRegionMapNextCase_Call(nextRoutine, regionInfo);
      }
      else if (nextRoutine.nextType == NextType.CreateThread) {
        str = GenerateRegionMapNextCase_CreateThread(nextRoutine, regionInfo);
      }
      else{
        str = "s.region_map";
      }

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      return AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutine.NameSuffix}", bvs, AH.ParseExpression(pgp.prog, "", str));
    }

    protected virtual void GenerateRegionMapNext(RegionInfo regionInfo)
    {
      var cases = new List<MatchCaseExpr>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        cases.Add(GenerateRegionMapNextCase(nextRoutine, regionInfo));
      }

      var source = AH.MakeNameSegment("step", "L.Armada_TraceEntry");
      var body = AH.MakeMatchExpr(source, cases, "map<Armada_Pointer, RegionId>");
      var formals = new List<Formal> { AH.MakeFormal("s", "LPlusState"), AH.MakeFormal("ls'", "LState"), AH.MakeFormal("step", "L.Armada_TraceEntry") };
      var fn = AH.MakeFunction("RegionMapNext", formals, body);
      pgp.AddDefaultClassDecl(fn, "specs");
    }

    protected virtual void GenerateRegionMap(IEnumerable<string> regionIds)
    {
      string auxNextName = $"RegionMapNext";
      var auxiliaryInfo = new AuxiliaryInfo("region_map", "map<Armada_Pointer, RegionId>", "RegionMapInit", "RegionMapNext");
      auxiliaries.Add(auxiliaryInfo);
    }

    protected virtual void GenerateRegionInvariant()
    {
      GenerateHeapInvariant();
      RegionInfo regionInfo = GenerateVariableRegionMap();
      GenerateAddressableInvariant();
      // OtherWay lemmas are needed for addressable pointer variables
      GenerateAppendStoreBufferOtherWay();
      var regionIds = new HashSet<string>();

      var predBuilder = new PredicateBuilder(pgp.prog);
      var plus_s = AH.MakeNameSegment("s", "LPlusState");
      var s = AH.MakeExprDotName(plus_s, "s", "L.Armada_TotalState");
      var addrs = AH.MakeExprDotName(s, "addrs", "L.Armada_Addrs");
      var regionIdType = AH.ReferToType("RegionId");
      var regionMap = AH.MakeExprDotName(plus_s, "region_map", AH.MakeMapType("Armada_Pointer", regionIdType));

      string str;

      List<string> regionMapInitUpdates = new List<string>();

      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        // Global addressable variables
        if (globalVar is GlobalAddressableArmadaVariable) {
          string regionNameStr = regionInfo.GetGlobalRegionId("&" + globalVarName);

          var globalVarAddr = AH.MakeExprDotName(addrs, globalVar.name, globalVar.ty);
          str = $"addrs.{globalVarName} in region_map";
          predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));

          str = $"region_map[addrs.{globalVarName}] == {regionNameStr}";
          predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));

          regionMapInitUpdates.Add($"s.addrs.{globalVarName} := {regionNameStr}");
        }

        // Deal with global pointer variables
        if (globalVar.ty is PointerType) {
          string regionNameStr = regionInfo.GetGlobalRegionId(globalVarName);

          // Global addressable pointer variable
          if (globalVar is GlobalAddressableArmadaVariable) {

            // Need to ensure that the address stored in this pointer variable is in the correct region
            var pointerValue = Printer.ExprToString(
              AH.GetInvocationOfDereferencePointer(
                            AH.MakeNameSegment("mem.heap", "Armada_Heap"),
                            AH.MakeNameSegment($"addrs.{globalVarName}", "Armada_Pointer"), globalVar.ty
            ));

            var validPointer = Printer.ExprToString(
              AH.GetInvocationOfValidPointer(
                AH.MakeNameSegment("mem.heap", "Armada_Heap"),
                AH.MakeNameSegment($"addrs.{globalVarName}", "Armada_Pointer"), globalVar.ty
            ));

            str = $"{validPointer} && ({pointerValue} == 0 || ({pointerValue} in region_map && region_map[{pointerValue}] == {regionNameStr}))";
            predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
          }
          // Global non-addressable pointer variable
          else 
          {
            str = $"mem.globals.{globalVarName} == 0 || (mem.globals.{globalVarName} in region_map && region_map[mem.globals.{globalVarName}] == {regionNameStr})";
            predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
          }
        }
      }
      // Deal with addresses of addressable stack variables
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        foreach (var localVar in methodSymbols.AllVariables) {
          var localVarName = localVar.name;
          if (localVar is MethodStackFrameAddressableLocalArmadaVariable) {
            string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
            string regionIdStr = regionInfo.GetLocalRegionId(methodName, "&" + localVarName);

            if (methodName == "main") {
              regionMapInitUpdates.Add($"s.threads[config.tid_init].top.{varStackFrameFieldName} := {regionIdStr}");
            }

            str = $@"
              forall tid, extended_frame ::
                tid in threads
                && extended_frame in threads[tid].stack
                && extended_frame.frame.Armada_StackFrame_{methodName}?
                  ==> var stack_frame := extended_frame.frame; 
                  (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
            ";
            predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "RegionInvariantStackVarExtendedFrameClause", str));

            str = $@"
              forall tid ::
                tid in threads
                && threads[tid].top.Armada_StackFrame_{methodName}?
                  ==> var stack_frame := threads[tid].top;
                  (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
            ";
            predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "RegionInvariantStackVarTopClause", str));
          }
          if (localVar.ty is PointerType) { // If the variable is a pointer type
            string regionIdStr = regionInfo.GetLocalRegionId(methodName, localVarName);
            string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);

            Expression validPointerExpr = AH.GetInvocationOfValidPointer(
              AH.MakeNameSegment("mem.heap", "Armada_Heap"),
              AH.MakeNameSegment($"frame.{varStackFrameFieldName}", localVar.ty), localVar.ty
            );
            string validPointerStr = Printer.ExprToString(validPointerExpr);

            Expression pointerValueExpr = AH.GetInvocationOfDereferencePointer(
              AH.MakeNameSegment("mem.heap", "Armada_Heap"),
              AH.MakeNameSegment($"frame.{varStackFrameFieldName}", localVar.ty), localVar.ty
            );
            string pointerValueStr = Printer.ExprToString(pointerValueExpr);

            // Local addressable pointer
            if (localVar is MethodStackFrameAddressableLocalArmadaVariable) {
              str = $@"
              forall tid :: tid in threads && threads[tid].top.Armada_StackFrame_{methodName}?
              ==> var frame := threads[tid].top;
                    {validPointerStr}
                    && ({pointerValueStr} == 0 ||
                        ({pointerValueStr} in region_map 
                         && region_map[{pointerValueStr}] == {regionIdStr}
                         )
                      )
              ";
              predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));

              str = $@"
              forall tid, extended_frame ::
                  tid in threads
                  && extended_frame in threads[tid].stack
                  && extended_frame.frame.Armada_StackFrame_{methodName}?
                    ==> var frame := extended_frame.frame;
                    {validPointerStr}
                    && ({pointerValueStr} == 0 ||
                        ({pointerValueStr} in region_map 
                         && region_map[{pointerValueStr}] == {regionIdStr}
                         )
                      )
              ";
              predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "", str));
            }
            // Local non-addressable pointer
            else {
              str = $@"
                forall tid, extended_frame ::
                  tid in threads
                  && extended_frame in threads[tid].stack
                  && extended_frame.frame.Armada_StackFrame_{methodName}?
                    ==> var stack_frame := extended_frame.frame; 
                    stack_frame.{varStackFrameFieldName} == 0 || (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
              ";
              predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "RegionInvariantStackVarExtendedFrameClause", str));

              str = $@"
                forall tid ::
                  tid in threads
                  && threads[tid].top.Armada_StackFrame_{methodName}?
                    ==> var stack_frame := threads[tid].top;
                    stack_frame.{varStackFrameFieldName} == 0 || (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
              ";
              predBuilder.AddConjunct(AH.ParseExpression(pgp.prog, "RegionInvariantStackVarTopClause", str));
            }
          }
        }
      }

      string mapUpdate = String.Join(", ", regionMapInitUpdates);
      str = $@"
        function RegionMapInit(s:LState, config:LConfig) : map<Armada_Pointer, RegionId>
           requires L.Armada_InitConfig(s, config)
        {{
          map[{mapUpdate}]
        }}
      ";
      pgp.AddDefaultClassDecl((Function)AH.ParseTopLevelDecl(pgp.prog, "RegionMapInit", str), "specs");

      GenerateRegionMapNext(regionInfo);

      var body = predBuilder.Extract();
      str = $@"
        predicate RegionInvariant_mem(threads: map<Armada_ThreadHandle, L.Armada_Thread>, addrs: L.Armada_Addrs,
        mem: L.Armada_SharedMemory, region_map: map<Armada_Pointer, RegionId>)
        {{
          {Printer.ExprToString(body)}
        }}
      ";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "RegionInvariant_mem", str), "invariants");

      str = @"
        predicate RegionMapOnlyContainsValidOrFreedPointers(s: LPlusState)
        {
          forall k :: k in s.region_map ==> k in s.s.mem.heap.valid || k in s.s.mem.heap.freed
        }
      ";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "RegionMapOnlyContainsValidOrFreedPointers", str), "invariants");

      str = $@"
        predicate RegionInvariant(s: LPlusState)
        {{
            RegionMapOnlyContainsValidOrFreedPointers(s)
            && RegionInvariant_mem(s.s.threads, s.s.addrs, s.s.mem, s.region_map)
            && (forall tid, storeBufferEntry, threads, addrs, mem, region_map :: tid in s.s.threads && storeBufferEntry in s.s.threads[tid].storeBuffer
                && (forall p :: p in s.region_map ==> p in region_map && region_map[p] == s.region_map[p]) 
                && RegionInvariant_mem(threads, addrs, mem, region_map) ==>
                RegionInvariant_mem(threads, addrs, L.Armada_ApplyStoreBufferEntry(mem, storeBufferEntry), region_map))
        }}
      ";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "RegionInvariant", str), "invariants");

      GenerateRegionMap(regionIds);
      AddInvariant(new InternalInvariantInfo("RegionInvariant", "RegionInvariant", new List<string>(){"AddressableInvariant"}, "lemma_RegionInvariantOnGlobalViewAlwaysImpliesRegionInvariantOnLocalView();"));
      GenerateRegionInvariantHoldsOnLocalViewLemmas();
    }

    protected virtual void GenerateRegionInvariantHoldsOnLocalViewLemmas()
    {
      string str = @"
        lemma lemma_RegionInvariantOnGlobalViewImpliesRegionInvariantOnLocalView(s_threads: map<Armada_ThreadHandle, L.Armada_Thread>, s_addrs: L.Armada_Addrs, s_mem: L.Armada_SharedMemory, s_region_map: map<Armada_Pointer, RegionId>, storeBuffer:seq<L.Armada_StoreBufferEntry>)
          requires RegionInvariant_mem(s_threads, s_addrs, s_mem, s_region_map)
          
          requires forall storeBufferEntry, threads, addrs, mem, region_map :: 
              storeBufferEntry in storeBuffer &&
              (forall p :: p in s_region_map ==> p in region_map && region_map[p] == s_region_map[p]) &&
              RegionInvariant_mem(threads, addrs, mem, region_map) ==>
              RegionInvariant_mem(threads, addrs, L.Armada_ApplyStoreBufferEntry(mem, storeBufferEntry), region_map)
              
          ensures RegionInvariant_mem(s_threads, s_addrs, L.Armada_ApplyStoreBuffer(s_mem, storeBuffer), s_region_map)
          decreases |storeBuffer|
        {
          if |storeBuffer| > 0 {
            var s_mem' := L.Armada_ApplyStoreBufferEntry(s_mem, storeBuffer[0]);
            lemma_RegionInvariantOnGlobalViewImpliesRegionInvariantOnLocalView(s_threads, s_addrs, s_mem', s_region_map, storeBuffer[1..]);
          }
        }
      ";
      pgp.AddDefaultClassDecl((Lemma)AH.ParseTopLevelDecl(pgp.prog, "lemma_RegionInvariantOnGlobalViewImpliesRegionInvariantOnLocalView", str), "invariants");

      str = @"
        lemma lemma_RegionInvariantOnGlobalViewAlwaysImpliesRegionInvariantOnLocalView()
          ensures forall s :: RegionInvariant(s) ==> (forall tid :: tid in s.s.threads ==>
          RegionInvariant_mem(s.s.threads, s.s.addrs, L.Armada_GetThreadLocalView(s.s, tid), s.region_map))
        {
          forall s | RegionInvariant(s)
            ensures (forall tid :: tid in s.s.threads ==> RegionInvariant_mem(s.s.threads, s.s.addrs, L.Armada_GetThreadLocalView(s.s, tid), s.region_map))
          {
            forall tid | tid in s.s.threads
              ensures RegionInvariant_mem(s.s.threads, s.s.addrs, L.Armada_GetThreadLocalView(s.s, tid), s.region_map)
            {
              lemma_RegionInvariantOnGlobalViewImpliesRegionInvariantOnLocalView(s.s.threads, s.s.addrs, s.s.mem, s.region_map, s.s.threads[tid].storeBuffer);
            }
          }
        }
      ";
      pgp.AddDefaultClassDecl((Lemma)AH.ParseTopLevelDecl(pgp.prog, "lemma_RegionInvariantOnGlobalViewAlwaysImpliesRegionInvariantOnLocalView", str), "invariants");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about heap invariant preservation
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateHeapInvariant() {
      string str = @"
        predicate HeapInvariant(s:LPlusState)
        {
          Armada_HeapInvariant(s.s.mem.heap)
        }
      ";
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "HeapInvariant", str), "specs");
      AddInvariant(new InternalInvariantInfo("HeapInvariant", "HeapInvariant", new List<string>() {"AddressableInvariant"} ));
    }

    protected virtual void GenerateLemmasHelpfulForProvingInitPreservation_LH()
    {
      string str;

      str = $@"
        lemma lemma_ConvertTotalStatePreservesAddressableStaticVariablesAreValid(ls:LState, hs:HState, new_ptrs:set<Armada_Pointer>)
          requires hs == ConvertTotalState_LH(ls)
          requires L.Armada_AddressableStaticVariablesAreValid(ls, new_ptrs)
          ensures  H.Armada_AddressableStaticVariablesAreValid(hs, new_ptrs)
        {{
          var lheap := ls.mem.heap.(valid := ls.mem.heap.valid - new_ptrs);
          var hheap := hs.mem.heap.(valid := hs.mem.heap.valid - new_ptrs);
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertTotalStatePreservesAddressableStaticVariablesAreRoots(ls:LState, hs:HState)
          requires hs == ConvertTotalState_LH(ls)
          requires L.Armada_AddressableStaticVariablesAreDistinctRoots(ls)
          ensures  H.Armada_AddressableStaticVariablesAreDistinctRoots(hs)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertTotalStatePreservesInit(ls:LState, hs:HState, lconfig:L.Armada_Config, hconfig:H.Armada_Config)
          requires L.Armada_InitConfig(ls, lconfig)
          requires hs == ConvertTotalState_LH(ls)
          requires hconfig == ConvertConfig_LH(lconfig)
          ensures  H.Armada_InitConfig(hs, hconfig)
        {
          lemma_ConvertTotalStatePreservesAddressableStaticVariablesAreValid(ls, hs, lconfig.new_ptrs);
          lemma_ConvertTotalStatePreservesAddressableStaticVariablesAreRoots(ls, hs);
        }
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about commutativity
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateLocalViewCommutativityLemmas()
    {
      string str;

      str = @"
        lemma lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(
          lglobals:L.Armada_Globals, lv:L.Armada_GlobalStaticVar, fields:seq<Armada_Field>, value:Armada_PrimitiveValue,
          hv:H.Armada_GlobalStaticVar, hglobals1:H.Armada_Globals, hglobals2:H.Armada_Globals)
          requires hv == ConvertGlobalStaticVar_LH(lv)
          requires hglobals1 == ConvertGlobals_LH(L.Armada_ApplyTauUnaddressable(lglobals, lv, fields, value))
          requires hglobals2 == H.Armada_ApplyTauUnaddressable(ConvertGlobals_LH(lglobals), hv, fields, value)
          ensures  hglobals1 == hglobals2
        {
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem:L.Armada_SharedMemory, lentry:L.Armada_StoreBufferEntry,
                                                             hentry:H.Armada_StoreBufferEntry, hmem1:H.Armada_SharedMemory,
                                                             hmem2:H.Armada_SharedMemory)
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

          var hmem1' := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
          var hmem2' := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hbuf[0]);
          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
          lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
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
                    {:trigger H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)}
                    {:trigger ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid))}
                    :: tid in ls.threads ==>
                    ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
        {
          forall ls:L.Armada_TotalState, tid:Armada_ThreadHandle | tid in ls.threads
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
          ensures  ConvertStoreBuffer_LH(buf + [entry]) == ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)]
        {
          assert [entry][1..] == [];

          if |buf| == 0 {
            assert buf + [entry] == [entry];
            assert ConvertStoreBuffer_LH(buf + [entry]) == ConvertStoreBuffer_LH([entry]);
            assert ConvertStoreBuffer_LH(buf) == [];

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
            calc {
              ConvertStoreBuffer_LH(buf + [entry]);
              ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
              [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..] + [entry]);
            }
            lemma_StoreBufferAppendConversion(buf[1..], entry);
            calc {
              ConvertStoreBuffer_LH(buf + [entry]);
              [ConvertStoreBufferEntry_LH(buf[0])] + (ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)]);
              [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)];
              ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)];
            }
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)} :: H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) == ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)}
            ensures H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) == ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ConvertStoreBufferCommutesOverBeheadment(buf:seq<L.Armada_StoreBufferEntry>)
          requires |buf| > 0
          ensures  ConvertStoreBuffer_LH(buf[1..]) == ConvertStoreBuffer_LH(buf)[1..]
        {
          var hbuf1 := ConvertStoreBuffer_LH(buf[1..]);
          var hbuf2 := ConvertStoreBuffer_LH(buf)[1..];
          assert |hbuf1| == |hbuf2| == |buf| - 1;

          forall i | 0 <= i < |buf| - 1
            ensures hbuf1[i] == hbuf2[i]
          {
          }

          assert hbuf1 == hbuf2;
        }
      ";
      pgp.AddLemma(str, "utility");
    }

    protected virtual void GenerateAppendStoreBufferOtherWay()
    {
      if (calledGenerateAppendStoreBufferOtherWay)
      {
        return;
      }
      calledGenerateAppendStoreBufferOtherWay= true;
      string str;

      str = @"
        function ApplyStoreBufferOtherWay_L(mem: L.Armada_SharedMemory, storeBuffer: seq<L.Armada_StoreBufferEntry>): (mem': L.Armada_SharedMemory)
          decreases |storeBuffer|
        {
          if |storeBuffer| == 0 then
            mem
          else
            L.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_L(mem, all_but_last(storeBuffer)), last(storeBuffer))
        }
      ";
      pgp.AddFunction(str, "utility");

      str = @"
        function ApplyStoreBufferOtherWay_H(mem: H.Armada_SharedMemory, storeBuffer: seq<H.Armada_StoreBufferEntry>): (mem': H.Armada_SharedMemory)
          decreases |storeBuffer|
        {
          if |storeBuffer| == 0 then
            mem
          else
            H.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_H(mem, all_but_last(storeBuffer)), last(storeBuffer))
        }
      ";
      pgp.AddFunction(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferOtherWayEquivalent_L(mem: L.Armada_SharedMemory, storeBuffer: seq<L.Armada_StoreBufferEntry>)
          ensures L.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_L(mem, storeBuffer)
          decreases |storeBuffer|
        {
          if |storeBuffer| == 0 || |storeBuffer| == 1 {
              return;
          }

          var mem' := L.Armada_ApplyStoreBufferEntry(mem, storeBuffer[0]);
          calc {
              L.Armada_ApplyStoreBuffer(mem, storeBuffer);
              L.Armada_ApplyStoreBuffer(mem', storeBuffer[1..]);
              { lemma_ApplyStoreBufferOtherWayEquivalent_L(mem', storeBuffer[1..]); }
              ApplyStoreBufferOtherWay_L(mem', storeBuffer[1..]);
              L.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_L(mem', all_but_last(storeBuffer[1..])), last(storeBuffer[1..]));
              { assert last(storeBuffer[1..]) == last(storeBuffer); }
              L.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_L(mem', all_but_last(storeBuffer[1..])), last(storeBuffer));
              { lemma_ApplyStoreBufferOtherWayEquivalent_L(mem', all_but_last(storeBuffer[1..])); }
              L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem', all_but_last(storeBuffer[1..])), last(storeBuffer));
              L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, [storeBuffer[0]] + all_but_last(storeBuffer[1..])), last(storeBuffer));
              { assert [storeBuffer[0]] + all_but_last(storeBuffer[1..]) == all_but_last(storeBuffer); }
              L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, all_but_last(storeBuffer)), last(storeBuffer));
              { lemma_ApplyStoreBufferOtherWayEquivalent_L(mem, all_but_last(storeBuffer)); }
              L.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_L(mem, all_but_last(storeBuffer)), last(storeBuffer));
              ApplyStoreBufferOtherWay_L(mem, storeBuffer);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferOtherWayEquivalent_H(mem: H.Armada_SharedMemory, storeBuffer: seq<H.Armada_StoreBufferEntry>)
          ensures H.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_H(mem, storeBuffer)
          decreases |storeBuffer|
        {
          if |storeBuffer| == 0 || |storeBuffer| == 1 {
              return;
          }

          var mem' := H.Armada_ApplyStoreBufferEntry(mem, storeBuffer[0]);
          calc {
              H.Armada_ApplyStoreBuffer(mem, storeBuffer);
              H.Armada_ApplyStoreBuffer(mem', storeBuffer[1..]);
              { lemma_ApplyStoreBufferOtherWayEquivalent_H(mem', storeBuffer[1..]); }
              ApplyStoreBufferOtherWay_H(mem', storeBuffer[1..]);
              H.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_H(mem', all_but_last(storeBuffer[1..])), last(storeBuffer[1..]));
              { assert last(storeBuffer[1..]) == last(storeBuffer); }
              H.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_H(mem', all_but_last(storeBuffer[1..])), last(storeBuffer));
              { lemma_ApplyStoreBufferOtherWayEquivalent_H(mem', all_but_last(storeBuffer[1..])); }
              H.Armada_ApplyStoreBufferEntry(H.Armada_ApplyStoreBuffer(mem', all_but_last(storeBuffer[1..])), last(storeBuffer));
              H.Armada_ApplyStoreBufferEntry(H.Armada_ApplyStoreBuffer(mem, [storeBuffer[0]] + all_but_last(storeBuffer[1..])), last(storeBuffer));
              { assert [storeBuffer[0]] + all_but_last(storeBuffer[1..]) == all_but_last(storeBuffer); }
              H.Armada_ApplyStoreBufferEntry(H.Armada_ApplyStoreBuffer(mem, all_but_last(storeBuffer)), last(storeBuffer));
              { lemma_ApplyStoreBufferOtherWayEquivalent_H(mem, all_but_last(storeBuffer)); }
              H.Armada_ApplyStoreBufferEntry(ApplyStoreBufferOtherWay_H(mem, all_but_last(storeBuffer)), last(storeBuffer));
              ApplyStoreBufferOtherWay_H(mem, storeBuffer);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferOtherWayAlwaysEquivalent()
          ensures forall mem, storeBuffer :: L.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_L(mem, storeBuffer)
          ensures forall mem, storeBuffer :: H.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_H(mem, storeBuffer)
        {
          forall mem, storeBuffer
            ensures L.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_L(mem, storeBuffer)
          {
            lemma_ApplyStoreBufferOtherWayEquivalent_L(mem, storeBuffer);
          }

          forall mem, storeBuffer
            ensures H.Armada_ApplyStoreBuffer(mem, storeBuffer) == ApplyStoreBufferOtherWay_H(mem, storeBuffer)
          {
            lemma_ApplyStoreBufferOtherWayEquivalent_H(mem, storeBuffer);
          }
        }
      ";
      pgp.AddLemma(str, "utility");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Store buffers
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateGenericStoreBufferLemmas_L()
    {
      string str;

      str = @"
        lemma lemma_ApplyStoreBufferCommutesWithAppend_L(
          mem: L.Armada_SharedMemory,
          buf:seq<L.Armada_StoreBufferEntry>,
          entry:L.Armada_StoreBufferEntry
          )
          ensures L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)) ==
                  L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, buf), entry)
          decreases |buf|
        {
          if |buf| > 0 {
            var mem' := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
            var buf' := L.Armada_StoreBufferAppend(buf, entry);
            assert buf'[0] == buf[0];
            assert buf'[1..] == buf[1..] + [entry];
            calc {
              L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry));
              L.Armada_ApplyStoreBuffer(mem, buf');
              L.Armada_ApplyStoreBuffer(L.Armada_ApplyStoreBufferEntry(mem, buf'[0]), buf'[1..]);
              L.Armada_ApplyStoreBuffer(mem', buf'[1..]);
              { lemma_ApplyStoreBufferCommutesWithAppend_L(mem', buf[1..], entry); }
              L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem', buf[1..]), entry);
              L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, buf), entry);
            }
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        lemma lemma_ApplyStoreBufferCommutesWithAppendAlways_L()
          ensures forall mem: L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, entry:L.Armada_StoreBufferEntry ::
                    L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)) ==
                    L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, buf), entry)
        {
          forall mem: L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, entry:L.Armada_StoreBufferEntry
            ensures L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)) ==
                    L.Armada_ApplyStoreBufferEntry(L.Armada_ApplyStoreBuffer(mem, buf), entry)
          {
            lemma_ApplyStoreBufferCommutesWithAppend_L(mem, buf, entry);
          }
        }
      ";
      pgp.AddLemma(str, "utility");

      str = @"
        predicate SharedMemoryHasPredecessor_L(mem':L.Armada_SharedMemory, entry:L.Armada_StoreBufferEntry)
        {
          exists mem :: mem' == L.Armada_ApplyStoreBufferEntry(mem, entry)
        }
      ";
      pgp.AddPredicate(str, "utility");

      str = @"
        lemma lemma_StoreBufferAppendHasEffectOfAppendedEntryAlways_L()
          ensures forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, entry:L.Armada_StoreBufferEntry
                    {:trigger L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry))} ::
                    SharedMemoryHasPredecessor_L(L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)), entry)
        {
          forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>, entry:L.Armada_StoreBufferEntry
                    {:trigger L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry))}
            ensures SharedMemoryHasPredecessor_L(L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)), entry)
          {
            lemma_ApplyStoreBufferCommutesWithAppend_L(mem, buf, entry);
            var mem_prev := L.Armada_ApplyStoreBuffer(mem, buf);
            assert L.Armada_ApplyStoreBuffer(mem, L.Armada_StoreBufferAppend(buf, entry)) ==
                   L.Armada_ApplyStoreBufferEntry(mem_prev, entry);
          }
        }
      ";
      pgp.AddLemma(str, "utility");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Invariants
    ////////////////////////////////////////////////////////////////////////

    protected void AddInvariant(InvariantInfo inv)
    {
      invariants.Add(inv);
    }

    private void GenerateInductiveInv(ProofGenerationParams pgp)
    {
      var invNames = invariants.Select(x => x.Name).ToList();

      string str = $@"
        predicate InductiveInv(s:LPlusState)
        {{
      ";
      foreach (var inv in invariants) {
        str += $"    && {inv.Name}(s)\n";
      }
      if (!invariants.Any()) {
        str += "    true\n";
      }
      str += "}\n";
      pgp.AddPredicate(str, "invariants");
    }

    private void GenerateInitImpliesInductiveInvLemma(ProofGenerationParams pgp)
    {
      string str = @"
        lemma lemma_InitImpliesInductiveInv(s:LPlusState)
          requires LPlus_Init(s)
          ensures  InductiveInv(s)
        {
      ";
      foreach (var inv in invariants) {
        str += $"    {inv.InitLemmaName}(s);\n";
      }
      str += "  }\n";
      pgp.AddLemma(str, "invariants");
    }

    private void GenerateNextMaintainsInductiveInvLemma(ProofGenerationParams pgp)
    {
      string str = @"
        lemma lemma_NextOneStepMaintainsInductiveInv(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
          requires InductiveInv(s)
          requires LPlus_NextOneStep(s, s', step)
          ensures  InductiveInv(s')
        {
      ";
      foreach (var inv in invariants) {
        str += $"    {inv.NextLemmaName}(s, s', step);\n";
      }
      str += "  }\n";
      pgp.AddLemma(str, "invariants");
    }

    private void GenerateInductiveInvInductiveLemma(ProofGenerationParams pgp)
    {
      string str;

      str = @"
        lemma lemma_NextMultipleStepsMaintainsInductiveInv(s: LPlusState, s': LPlusState, steps: seq<L.Armada_TraceEntry>)
          requires InductiveInv(s)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), s, s', steps)
          ensures InductiveInv(s')
          decreases |steps|
        {
          if |steps| == 0 {
            return;
          }

          var splus1 := LPlus_GetNextStateAlways(s, steps[0]);
          lemma_NextOneStepMaintainsInductiveInv(s, splus1, steps[0]);
          assert InductiveInv(splus1);
          lemma_NextMultipleStepsMaintainsInductiveInv(splus1, s', steps[1..]);
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        lemma lemma_InductiveInvIsInvariant()
          ensures  IsInvariantPredicateOfSpec(InductiveInv, GetLPlusSpec())
        {
          var spec := GetLPlusSpec();

          forall s | s in spec.init
            ensures InductiveInv(s);
          {
            lemma_InitImpliesInductiveInv(s);
          }

          forall s, s', step | InductiveInv(s) && ActionTuple(s, s', step) in spec.next
            ensures InductiveInv(s')
          {
            lemma_NextMultipleStepsMaintainsInductiveInv(s, s', step.steps);
          }

          lemma_EstablishInvariantPredicatePure(InductiveInv, spec);
        }
      ";
      pgp.AddLemma(str, "invariants");
    }

    public void GenerateInvariantProof(ProofGenerationParams pgp)
    {
      foreach (var inv in invariants) {
        inv.GenerateProofs(pgp, invariants);
      }

      GenerateInductiveInv(pgp);
      GenerateInitImpliesInductiveInvLemma(pgp);
      GenerateNextMaintainsInductiveInvLemma(pgp);
      GenerateInductiveInvInductiveLemma(pgp);
    }

    ////////////////////////////////////////////////////////////////////////
    /// One-step specs
    ////////////////////////////////////////////////////////////////////////

    public void GenerateLOneStepSpec(bool plus)
    {
      string str;

      var state = plus ? "LPlusState" : "LState";
      var nextOneStep = plus ? "LPlus_NextOneStep" : "L.Armada_NextOneStep";
      var getSpec = plus ? "GetLPlusSpec" : "GetLSpec";
      var getState = plus ? ".s" : "";
      var specFunctions = plus ? "LPlus_GetSpecFunctions()" : "L.Armada_GetSpecFunctions()";
      var makeNext = plus ? "LPlus_GetNextStateAlways" : "L.Armada_GetNextStateAlways";

      str = $@"
        type LOneStepSpec = AnnotatedBehaviorSpec<{state}, L.Armada_TraceEntry>
      ";
      pgp.AddTopLevelDecl((TypeSynonymDecl)AH.ParseTopLevelDecl(pgp.prog, "LOneStepSpec", str), "specs");

      str = $@"
        predicate LOneStep_Next(s: {state}, s': {state}, step: L.Armada_TraceEntry)
        {{
          && {nextOneStep}(s, s', step)
          && (forall tid :: tid in s{getState}.threads && L.Armada_IsNonyieldingPC(s{getState}.threads[tid].pc) ==> !step.Armada_TraceEntry_Tau? && step.tid == tid)
        }}
      ";
      pgp.AddPredicate(str, "specs");

      str = $@"
        function GetLOneStepSpec() : LOneStepSpec
        {{
          AnnotatedBehaviorSpec(iset s | s in {getSpec}().init,
                                (iset s, s', step | LOneStep_Next(s, s', step) :: ActionTuple(s, s', step)))
        }}
      ";
      pgp.AddFunction(str, "specs");

      str = $@"
        lemma lemma_EstablishLOneStepNext(
          tau: bool,
          tid: Armada_ThreadHandle,
          s: {state},
          s': {state},
          step: L.Armada_TraceEntry
          )
          requires forall any_tid :: any_tid in s{getState}.threads && (any_tid != tid || tau) ==> !L.Armada_IsNonyieldingPC(s{getState}.threads[any_tid].pc)
          requires {nextOneStep}(s, s', step)
          requires step.tid == tid
          requires step.Armada_TraceEntry_Tau? == tau
          ensures  LOneStep_Next(s, s', step)
          ensures  forall any_tid :: any_tid in s'{getState}.threads && (any_tid != tid || tau) ==> !L.Armada_IsNonyieldingPC(s'{getState}.threads[any_tid].pc)
        {{
        }}
      ";
      pgp.AddLemma(str, "specs");

      str = $@"
        lemma lemma_UnrollBehavior(
          lb:AnnotatedBehavior<{state}, LStep>,
          pos:int
          ) returns (
          ub:AnnotatedBehavior<{state}, L.Armada_TraceEntry>
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, {getSpec}())
          requires 0 <= pos < |lb.states|
          ensures  AnnotatedBehaviorSatisfiesSpec(ub, GetLOneStepSpec())
          ensures  last(ub.states) == lb.states[pos]
          ensures  var s := last(ub.states){getState}; s.stop_reason.Armada_NotStopped? ==>
                     (forall tid :: tid in s.threads ==> !L.Armada_IsNonyieldingPC(s.threads[tid].pc))
          decreases pos
        {{
          if pos == 0 {{
            ub := AnnotatedBehavior([lb.states[0]], []);
            return;
          }}

          var prev_pos := pos-1;
          ub := lemma_UnrollBehavior(lb, prev_pos);
          var num_steps := 0;
          var lstep := lb.trace[prev_pos];
          var ls' := lb.states[pos];
          assert ActionTuple(lb.states[prev_pos], lb.states[prev_pos+1], lb.trace[prev_pos]) in {getSpec}().next;

          while num_steps < |lstep.steps|
            invariant 0 <= num_steps <= |lstep.steps|
            invariant AnnotatedBehaviorSatisfiesSpec(ub, GetLOneStepSpec())
            invariant Armada_NextMultipleSteps({specFunctions}, last(ub.states), ls', lstep.steps[num_steps..])
            invariant var s := last(ub.states){getState};
                      s.stop_reason.Armada_NotStopped? ==>
                      (forall tid :: tid in s.threads && (tid != lstep.tid || lstep.tau) ==> !L.Armada_IsNonyieldingPC(s.threads[tid].pc))
          {{
            var us := last(ub.states);
            var ustep := lstep.steps[num_steps];
            var us' := {makeNext}(us, ustep);
            assert ustep in lstep.steps;
            lemma_EstablishLOneStepNext(lstep.tau, lstep.tid, us, us', ustep);
            ub := AnnotatedBehavior(ub.states + [us'], ub.trace + [ustep]);
            num_steps := num_steps + 1;
          }}
        }}
      ";
      pgp.AddLemma(str, "specs");
    }

    public void GenerateHOneStepSpec()
    {
      string str;

      str = @"
        type HOneStepSpec = AnnotatedBehaviorSpec<HState, H.Armada_TraceEntry>
      ";
      pgp.AddTopLevelDecl((TypeSynonymDecl)AH.ParseTopLevelDecl(pgp.prog, "HOneStepSpec", str), "specs");

      str = @"
        predicate HOneStep_Next(s: HState, s': HState, step: H.Armada_TraceEntry)
        {
          && H.Armada_NextOneStep(s, s', step)
          && (forall tid :: tid in s.threads && H.Armada_IsNonyieldingPC(s.threads[tid].pc) ==> !step.Armada_TraceEntry_Tau? && step.tid == tid)
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        function GetHOneStepSpec() : HOneStepSpec
        {
          AnnotatedBehaviorSpec(iset s | s in GetHSpec().init,
                                (iset s, s', step | HOneStep_Next(s, s', step) :: ActionTuple(s, s', step)))
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        lemma lemma_EstablishHOneStepNext(
          tau: bool,
          tid: Armada_ThreadHandle,
          s: HState,
          s': HState,
          step: H.Armada_TraceEntry
          )
          requires forall any_tid :: any_tid in s.threads && (any_tid != tid || tau) ==> !H.Armada_IsNonyieldingPC(s.threads[any_tid].pc)
          requires H.Armada_NextOneStep(s, s', step)
          requires step.tid == tid
          requires step.Armada_TraceEntry_Tau? == tau
          ensures  HOneStep_Next(s, s', step)
          ensures  forall any_tid :: any_tid in s'.threads && (any_tid != tid || tau) ==> !H.Armada_IsNonyieldingPC(s'.threads[any_tid].pc)
        {
        }
      ";
      pgp.AddLemma(str, "specs");
    }

    public void GenerateValidStepLemmas()
    {
      string str;

      str = @"
        lemma lemma_NextMultipleStepsImpliesValidStep_H(s: HState, s': HState, steps: seq<H.Armada_TraceEntry>, pos:int)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), s, s', steps)
          requires 0 <= pos < |steps|
          ensures  H.Armada_ValidStep(Armada_GetStateSequence(H.Armada_GetSpecFunctions(), s, steps)[pos], steps[pos]);
          decreases pos
        {
          if pos > 0 {
            var s_next := H.Armada_GetNextStateAlways(s, steps[0]);
            lemma_NextMultipleStepsImpliesValidStep_H(s_next, s', steps[1..], pos-1);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about step lifting
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{TranslateFormalNameUsingPcMap(f, nextRoutine.pc, pcMap)}"));

      var hNextRoutineName = LiftNextRoutine(nextRoutine).NameSuffix;

      var str = $@"
        lemma lemma_LiftStep_{nextRoutineName}(ls:LPlusState, lstep:L.Armada_TraceEntry)
          requires InductiveInv(ls)
          requires LPlus_ValidStep(ls, lstep)
          requires lstep.Armada_TraceEntry_{nextRoutineName}?
          ensures  var ls' := LPlus_GetNextStateAlways(ls, lstep);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hstep := ConvertTraceEntry_LH(lstep);
                   && hstep.tid == lstep.tid
                   && hstep.Armada_TraceEntry_Tau? == lstep.Armada_TraceEntry_Tau?
                   && H.Armada_ValidStep(hs, hstep)
                   && H.Armada_GetNextStateAlways(hs, hstep) == ConvertTotalState_LPlusH(ls')
        {{
          var locv: H.Armada_SharedMemory := H.Armada_GetThreadLocalView(ConvertTotalState_LPlusH(ls), lstep.tid);
          var tid := lstep.tid;
          var ls' := LPlus_GetNextStateAlways(ls, lstep);
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var hstep := ConvertTraceEntry_LH(lstep);

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          assert H.Armada_ValidStep_{hNextRoutineName}(hs, tid{hstep_params});
          if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(ls.s, tid{lstep_params}) {{
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

    protected virtual void GenerateLiftStepLemmaForTauNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftStep_{nextRoutineName}(ls:LPlusState, lstep:L.Armada_TraceEntry)
          requires InductiveInv(ls)
          requires LPlus_ValidStep(ls, lstep)
          requires lstep.Armada_TraceEntry_{nextRoutineName}?
          ensures  var ls' := LPlus_GetNextStateAlways(ls, lstep);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hstep := ConvertTraceEntry_LH(lstep);
                   && hstep.tid == lstep.tid
                   && hstep.Armada_TraceEntry_Tau? == lstep.Armada_TraceEntry_Tau?
                   && H.Armada_ValidStep(hs, hstep)
                   && H.Armada_GetNextStateAlways(hs, hstep) == ConvertTotalState_LPlusH(ls')
        {{
          var tid := lstep.tid;
          var ls' := LPlus_GetNextStateAlways(ls, lstep);
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var hstep := ConvertTraceEntry_LH(lstep);

          var lentry := ls.s.threads[tid].storeBuffer[0];
          assert H.Armada_ValidStep_{nextRoutineName}(hs, tid{hstep_params});
          assert H.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(hs, tid{hstep_params});
          var hentry := hs.threads[tid].storeBuffer[0];
          var lmem := ls.s.mem;
          var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
          var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

          var alt_hs' := H.Armada_GetNextState_{nextRoutineName}(hs, tid{hstep_params});
          assert hs'.threads[tid] == alt_hs'.threads[tid];
          assert hs'.threads == alt_hs'.threads;
          assert hs' == alt_hs';
          assert H.Armada_Next_{nextRoutineName}(hs, hs', tid{hstep_params});
        }}
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateLiftStepLemmas()
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
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LiftStep_{nextRoutineName}(ls, lstep);";
      }

      string str = $@"
        lemma lemma_LiftStep(ls:LPlusState, lstep:L.Armada_TraceEntry)
          requires InductiveInv(ls)
          requires LPlus_ValidStep(ls, lstep)
          ensures  var ls' := LPlus_GetNextStateAlways(ls, lstep);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hstep := ConvertTraceEntry_LH(lstep);
                   H.Armada_ValidStep(hs, hstep) && H.Armada_GetNextStateAlways(hs, hstep) == ConvertTotalState_LPlusH(ls')
        {{
          match lstep {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GeneratePCFunctions_L()
    {
      var methodNames = pgp.symbolsLow.AllMethods.AllMethodNames;

      string str;

      str = "datatype LMethodName = " + String.Join(" | ", methodNames.Select(x => $"LMethodName_{x}"));
      pgp.AddDatatype(str, "specs");

      str = @"
        function MethodToInstructionCount_L(m:LMethodName) : (v:int)
          ensures v >= 0
        {
          match m
      ";
      foreach (var methodName in methodNames)
      {
        var methodInfo = pgp.symbolsLow.AllMethods.LookupMethod(methodName);
        str += $"    case LMethodName_{methodName} => {methodInfo.NumPCs}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);

      str = @"
        function PCToMethod_L(pc:L.Armada_PC) : LMethodName
        {
          match pc
      ";
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => LMethodName_{pc.methodName}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      str = @"
        function PCToInstructionCount_L(pc:L.Armada_PC) : (v:int)
          ensures v >= 0
        {
          match pc
      ";
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => {pc.instructionCount}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      str = @"
        lemma lemma_PCInstructionCountLessThanMethodInstructionCount_L(pc:L.Armada_PC)
          ensures 0 <= PCToInstructionCount_L(pc) < MethodToInstructionCount_L(PCToMethod_L(pc))
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        predicate StackMatchesMethod_L(frame:L.Armada_StackFrame, m:LMethodName)
        {
          match m
      ";
      foreach (var methodName in methodNames) {
        str += $"    case LMethodName_{methodName} => frame.Armada_StackFrame_{methodName}?\n";
      }
      str += "  }\n";
      pgp.AddPredicate(str, "specs");
    }

    protected void AddStackMatchesMethodInvariant()
    {
      string str;

      str = @"
        predicate StackMatchesMethodInv(s:LPlusState)
        {
          forall tid :: tid in s.s.threads ==>
            var pc := s.s.threads[tid].pc;
            StackMatchesMethod_L(s.s.threads[tid].top, PCToMethod_L(pc))
        }
      ";
      pgp.AddPredicate(str, "invariants");

      var inv = new InternalInvariantInfo("StackMatchesMethodInv", "StackMatchesMethodInv", new List<string>());
      invariants.Add(inv);
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about NextStep
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateLemmasAboutGetNextState()
    {
      string str;

      str = @"
        lemma lemma_NextOneStepImpliesGetNextState_L(ls: LState, ls': LState, lstep: L.Armada_TraceEntry)
          requires L.Armada_NextOneStep(ls, ls', lstep)
          ensures  ls' == L.Armada_GetNextStateAlways(ls, lstep)
          ensures  L.Armada_ValidStep(ls, lstep)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_NextOneStepImpliesGetNextState_H(hs: HState, hs': HState, hstep: H.Armada_TraceEntry)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  hs' == H.Armada_GetNextStateAlways(hs, hstep)
          ensures  H.Armada_ValidStep(hs, hstep)
        {
        }
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// GenericArmadaSpec
    ////////////////////////////////////////////////////////////////////////

    protected void CreateGenericArmadaSpec_L()
    {
      string str;

      str = @"
        lemma lemma_InitImpliesYielding_L(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures InitImpliesYielding(asf)
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_InitImpliesOK_L(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures InitImpliesOK(asf)
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_OneStepRequiresOK_L(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures OneStepRequiresOK(asf)
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_SteppingThreadHasPC_L(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures SteppingThreadHasPC(asf)
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_TauLeavesPCUnchanged_L(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures TauLeavesPCUnchanged(asf)
        {
        }
      ";
      pgp.AddLemma(str, "specs");

      str = @"
        lemma lemma_InductiveInvInvariantInLPlusSpec(
          asf:Armada_SpecFunctions<LPlusState, L.Armada_TraceEntry, L.Armada_PC>
          )
          requires asf == LPlus_GetSpecFunctions()
          ensures InitImpliesInv(asf, InductiveInv)
          ensures OneStepPreservesInv(asf, InductiveInv)
        {
          forall s | asf.init(s)
            ensures InductiveInv(s)
          {
            lemma_InitImpliesInductiveInv(s);
          }

          forall s, step | InductiveInv(s) && LPlus_ValidStep(s, step)
            ensures InductiveInv(LPlus_GetNextStateAlways(s, step))
          {
            var s' := LPlus_GetNextStateAlways(s, step);
            lemma_NextOneStepMaintainsInductiveInv(s, s', step);
          }
        }
      ";
      pgp.AddLemma(str, "invariants");
    }

    protected void CreateGenericArmadaSpec_H()
    {
      string str;

      str = @"
        function StepToThread_H(step:H.Armada_TraceEntry) : Armada_ThreadHandle
        {
          step.tid
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        predicate IsStepTau_H(step:H.Armada_TraceEntry)
        {
          step.Armada_TraceEntry_Tau?
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        predicate IsStateOK_H(s:HState)
        {
          s.stop_reason.Armada_NotStopped?
        }
      ";
      pgp.AddPredicate(str, "specs");

      str = @"
        function GetThreadPC_H(s:HState, tid:Armada_ThreadHandle) : Option<H.Armada_PC>
        {
          if tid in s.threads then Some(s.threads[tid].pc) else None
        }
      ";
      pgp.AddFunction(str, "specs");
    }

  }
  
}
