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

    public virtual string GenerateSpecificNextLemma(ProofGenerationParams pgp, AtomicPath atomicPath,
                                                    IEnumerable<InvariantInfo> allInvariants, AtomicSpec atomicSpec,
                                                    bool onlyNonstoppingPaths)
    {
      string nameSuffix = atomicPath.Name;
      string specificPathLemmaName = $"lemma_InvariantPredicateMaintainedByPath_{Key}_{nameSuffix}";
      var pr = new PathPrinter(atomicSpec);
      string str = $@"
        lemma {specificPathLemmaName}(s: LPlusState, s': LPlusState, path: {atomicSpec.Prefix}_Path, tid: Armada_ThreadHandle)
          requires {Name}(s)
      ";
      str += String.Concat(Dependencies.Select(dependency => $"  requires {FindMatchingDependency(dependency, allInvariants)}(s);\n"));
      if (onlyNonstoppingPaths) {
        str += $@"
          requires s'.s.stop_reason.Armada_NotStopped?
        ";
      }
      str += $@"
          requires path.{atomicSpec.Prefix}_Path_{nameSuffix}?
          requires {atomicSpec.Prefix}_ValidPath(s, path, tid)
          requires s' == {atomicSpec.Prefix}_GetStateAfterPath(s, path, tid)
          ensures  {Name}(s')
        {{
          { pr.GetOpenValidPathInvocation(atomicPath) }
          ProofCustomizationGoesHere();
          { nextStepBody }
        }}
      ";
      pgp.AddLemma(str, "invariants");

      return specificPathLemmaName;
    }

    public virtual void GenerateAtomicNextLemma(ProofGenerationParams pgp, IEnumerable<InvariantInfo> allInvariants,
                                                AtomicSpec atomicSpec, bool onlyNonstoppingPaths)
    {
      string finalCases = "";
      foreach (var atomicPath in atomicSpec.AtomicPaths) {
        string specificPathLemma = GenerateSpecificNextLemma(pgp, atomicPath, allInvariants, atomicSpec, onlyNonstoppingPaths);
        finalCases += $"    case {atomicSpec.Prefix}_Path_{atomicPath.Name}(_) => {specificPathLemma}(s, s', path, tid);\n";
      }

      nextLemmaName = $"lemma_InvariantPredicateMaintainedByPath_{Key}";
      string str = $@"
        lemma {nextLemmaName}(s: LPlusState, s': LPlusState, path: {atomicSpec.Prefix}_Path, tid: Armada_ThreadHandle)
          requires {Name}(s)
      ";
      foreach (var dependency in Dependencies)
      {
        str += $"  requires {FindMatchingDependency(dependency, allInvariants)}(s);\n";
      }
      if (onlyNonstoppingPaths) {
        str += @"
          requires s'.s.stop_reason.Armada_NotStopped?
        ";
      }
      str += $@"
          requires {atomicSpec.Prefix}_ValidPath(s, path, tid)
          requires s' == {atomicSpec.Prefix}_GetStateAfterPath(s, path, tid)
          ensures  {Name}(s')
        {{
          match path {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str, "invariants");
    }

    public virtual void GenerateProofs(ProofGenerationParams pgp, IEnumerable<InvariantInfo> allInvariants, AtomicSpec atomicSpec,
                                       bool onlyNonstoppingPaths)
    {
      GenerateInitLemma(pgp);
      GenerateAtomicNextLemma(pgp, allInvariants, atomicSpec, onlyNonstoppingPaths);
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
    public InternalInvariantInfo(string i_key, string i_name, List<string> i_dependencies, string nextStepBody="")
      : base(i_key, i_name, i_dependencies, nextStepBody)
    {
    }
  }

  public abstract class AbstractProofGenerator
  {
    protected ProofGenerationParams pgp;
    protected bool stateDependentConvertStep;
    protected Dictionary<ArmadaPC, ArmadaPC> pcMap;
    protected Dictionary<NextRoutine, NextRoutine> nextRoutineMap;
    protected List<ImportFileArmadaProofDecl> importedFiles;
    protected List<ImportModuleArmadaProofDecl> importedModules;
    protected List<InvariantInfo> invariants;
    protected List<AuxiliaryInfo> auxiliaries;
    protected AtomicSpec lAtomic, hAtomic;
    protected Dictionary<AtomicPath, AtomicPath> pathMap;

    // To prevent duplicate lemmas when there are duplicate calls
    private bool calledGenerateAppendStoreBufferOtherWay = false;

    public AbstractProofGenerator(ProofGenerationParams i_pgp, bool i_stateDependentConvertStep = false)
    {
      pgp = i_pgp;
      stateDependentConvertStep = i_stateDependentConvertStep;
      nextRoutineMap = null;
      importedFiles = new List<ImportFileArmadaProofDecl>();
      importedModules = new List<ImportModuleArmadaProofDecl>();
      invariants = new List<InvariantInfo>();
      auxiliaries = new List<AuxiliaryInfo>();
      lAtomic = null;
      hAtomic = null;
      pathMap = null;

      var revelationsFile = pgp.proofFiles.CreateAuxiliaryProofFile("revelations", false);
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("revelations");

      var specFile = pgp.proofFiles.CreateAuxiliaryProofFile("specs", false);
      specFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      specFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      specFile.AddImport("GenericArmadaSpecModule");
      specFile.AddImport("GenericArmadaLemmasModule");
      specFile.IncludeAndImportGeneratedFile("revelations");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("specs");

      var plusFile = pgp.proofFiles.CreateAuxiliaryProofFile("PlusLemmas");
      plusFile.IncludeAndImportGeneratedFile("specs");
      plusFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaPlus.i.dfy");
      plusFile.AddImport("GenericArmadaPlusModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("PlusLemmas");

      var effectFile = pgp.proofFiles.CreateAuxiliaryProofFile("pceffect");
      effectFile.IncludeAndImportGeneratedFile("specs");
      effectFile.IncludeAndImportGeneratedFile("revelations");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("pceffect");

      var latomicFile = pgp.proofFiles.CreateAuxiliaryProofFile("latomic");
      latomicFile.IncludeAndImportGeneratedFile("specs");
      latomicFile.IncludeAndImportGeneratedFile("revelations");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("latomic");

      var hatomicFile = pgp.proofFiles.CreateAuxiliaryProofFile("hatomic");
      hatomicFile.IncludeAndImportGeneratedFile("specs");
      hatomicFile.IncludeAndImportGeneratedFile("revelations");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("hatomic");

      var convertFile = pgp.proofFiles.CreateAuxiliaryProofFile("convert");
      convertFile.IncludeAndImportGeneratedFile("specs");
      convertFile.IncludeAndImportGeneratedFile("pceffect");
      convertFile.IncludeAndImportGeneratedFile("latomic");
      convertFile.IncludeAndImportGeneratedFile("hatomic");
      convertFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      convertFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("convert");

      var defsFile = pgp.proofFiles.CreateAuxiliaryProofFile("defs");
      defsFile.IncludeAndImportGeneratedFile("specs");
      defsFile.IncludeAndImportGeneratedFile("convert");
      defsFile.IncludeAndImportGeneratedFile("latomic");
      defsFile.IncludeAndImportGeneratedFile("hatomic");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      defsFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("defs");

      var utilityFile = pgp.proofFiles.CreateAuxiliaryProofFile("utility");
      utilityFile.IncludeAndImportGeneratedFile("specs");
      utilityFile.IncludeAndImportGeneratedFile("convert");
      utilityFile.IncludeAndImportGeneratedFile("defs");
      utilityFile.IncludeAndImportGeneratedFile("latomic");
      utilityFile.IncludeAndImportGeneratedFile("hatomic");
      utilityFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy",
                                   "util_collections_seqs_s");
      utilityFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy",
                                   "util_collections_seqs_i");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("utility");

      var invFile = pgp.proofFiles.CreateAuxiliaryProofFile("invariants");
      invFile.IncludeAndImportGeneratedFile("specs");
      invFile.IncludeAndImportGeneratedFile("convert");
      invFile.IncludeAndImportGeneratedFile("revelations");
      invFile.IncludeAndImportGeneratedFile("utility");
      invFile.IncludeAndImportGeneratedFile("defs");
      invFile.IncludeAndImportGeneratedFile("latomic");
      invFile.IncludeAndImportGeneratedFile("hatomic");
      invFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/invariants.i.dfy", "InvariantsModule");
      invFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaSpec.i.dfy",
                               "GenericArmadaSpecModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("invariants");

      var liftFile = pgp.proofFiles.CreateAuxiliaryProofFile("lift");
      liftFile.IncludeAndImportGeneratedFile("specs");
      liftFile.IncludeAndImportGeneratedFile("convert");
      liftFile.IncludeAndImportGeneratedFile("defs");
      liftFile.IncludeAndImportGeneratedFile("invariants");
      liftFile.IncludeAndImportGeneratedFile("utility");
      liftFile.IncludeAndImportGeneratedFile("latomic");
      liftFile.IncludeAndImportGeneratedFile("hatomic");
      liftFile.IncludeAndImportGeneratedFile("revelations");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/LiftAtomicToAtomic.i.dfy",
                                "LiftAtomicToAtomicModule");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaAtomic.i.dfy",
                                "GenericArmadaAtomicModule");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy",
                                "util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("lift");

      var str = @"
        predicate InductiveInvBasic(s: LPlusState)
        {
          0 !in s.s.threads
        }
      ";
      pgp.AddPredicate(str, "defs");
      AddInvariant(new InternalInvariantInfo("InductiveInvBasic", "InductiveInvBasic", new List<string>()));

      var atomicModulePath = ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaAtomic.i.dfy";
      convertFile.AddIncludeImport(atomicModulePath, "GenericArmadaAtomicModule");
      invFile.AddIncludeImport(atomicModulePath, "GenericArmadaAtomicModule");
      pgp.proofFiles.MainProof.AddIncludeImport(atomicModulePath, "GenericArmadaAtomicModule");
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
        if (!CheckVariableNameListEquivalence(s_l.AllVariableNamesInOrder, s_h.AllVariableNamesInOrder, s_l, s_h, methodName, "")) {
          return false;
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Generate PC-effect elements
    ////////////////////////////////////////////////////////////////////////

    protected void GeneratePCEffectLemmas()
    {
      GeneratePCEffectLemmas("L", pgp.symbolsLow);
      GeneratePCEffectLemmas("H", pgp.symbolsHigh);
    }

    protected void GeneratePCEffectLemmas(string m, ArmadaSymbolTable symbols)
    {
      string str;

      var pr = new ModuleStepPrinter(m);
      foreach (var nextRoutine in symbols.NextRoutines)
      {
        str = $@"
          lemma lemma_PCEffectOfStep_{m}_{nextRoutine.NameSuffix}(
            s: {m}.Armada_TotalState,
            step: {m}.Armada_Step,
            tid: Armada_ThreadHandle
            )
            requires {m}.Armada_ValidStep(s, step, tid)
            requires step.Armada_Step_{nextRoutine.NameSuffix}?
        ";

        if (nextRoutine.Tau) {
          str += $@"
            ensures  var s' := {m}.Armada_GetNextState(s, step, tid);
                     s'.stop_reason.Armada_NotStopped? && tid in s'.threads && s'.threads[tid].pc == s.threads[tid].pc";
        }
        else {
          str += $"ensures  s.threads[tid].pc.{nextRoutine.startPC}?\n";
          if (nextRoutine.Stopping) {
            str += $"ensures var s' := {m}.Armada_GetNextState(s, step, tid); !s'.stop_reason.Armada_NotStopped?\n";
          }
          else if (nextRoutine.endPC == null) {
            str += $"ensures var s' := {m}.Armada_GetNextState(s, step, tid); s'.stop_reason.Armada_NotStopped? && tid !in s'.threads\n";
          }
          else {
            str += $@"
            ensures  var s' := {m}.Armada_GetNextState(s, step, tid);
                     s'.stop_reason.Armada_NotStopped? && tid in s'.threads && s'.threads[tid].pc.{nextRoutine.endPC}?
            ";
          }
        }

        str += $@"
          {{
            { pr.GetOpenValidStepInvocation(nextRoutine) }
          }}
        ";

        pgp.AddLemma(str, "pceffect");
      }

      var pcToNextRoutines = new Dictionary<ArmadaPC, List<NextRoutine>>();

      foreach (var nextRoutine in symbols.NextRoutines.Where(r => !r.Tau))
      {
        if (pcToNextRoutines.ContainsKey(nextRoutine.startPC)) {
          pcToNextRoutines[nextRoutine.startPC].Add(nextRoutine);
        }
        else {
          pcToNextRoutines[nextRoutine.startPC] = new List<NextRoutine>{ nextRoutine };
        }
      }

      var pcs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str = $@"
          lemma lemma_PossibleStepsFromPC_{m}_{pc}(s: {m}.Armada_TotalState, step: {m}.Armada_Step, tid: Armada_ThreadHandle)
            requires {m}.Armada_ValidStep(s, step, tid)
            requires tid in s.threads
            requires s.threads[tid].pc.{pc}?
            ensures  step.Armada_Step_Tau?";
        var nextRoutines = pcToNextRoutines.ContainsKey(pc) ? pcToNextRoutines[pc] : new List<NextRoutine>();
        str += String.Concat(nextRoutines.Select(r => $" || step.Armada_Step_{r.NameSuffix}?"));
        str += @"
          {
            match step {
        ";
        foreach (var nextRoutine in symbols.NextRoutines) {
          str += $"{pr.CaseEntry(nextRoutine)} =>\n";
          if (!nextRoutine.Tau && !nextRoutine.startPC.Equals(pc)) {
            str += $"lemma_PCEffectOfStep_{m}_{nextRoutine.NameSuffix}(s, step, tid);\n";
          }
        }
        str += "} }";
        pgp.AddLemma(str, "pceffect");
      }
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
      nextRoutineMap = new Dictionary<NextRoutine, NextRoutine>();
      var hmap = new Dictionary<Tuple<ArmadaPC, ArmadaPC, bool, bool>, NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsHigh.NextRoutines) {
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(nextRoutine.startPC, nextRoutine.endPC, nextRoutine.UndefinedBehavior,
                                                          nextRoutine.BranchOutcome);
        if (hmap.ContainsKey(t)) {
          AH.PrintError(pgp.prog,
                        $"More than one next routine from PC {nextRoutine.startPC} to {nextRoutine.endPC} in level {pgp.mHigh.Name}");
          hmap.Remove(t);
        }
        else {
          hmap[t] = nextRoutine;
        }
      }

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var startPC = LiftPC(nextRoutine.startPC);
        var endPC = LiftPC(nextRoutine.endPC);
        var t = new Tuple<ArmadaPC, ArmadaPC, bool, bool>(startPC, endPC, nextRoutine.UndefinedBehavior, nextRoutine.BranchOutcome);
        if (hmap.ContainsKey(t)) {
          nextRoutineMap[nextRoutine] = hmap[t];
        }
        else if (warnOnMissingRoutines) {
          AH.PrintWarning(pgp.prog, $"No next routine found in high level from {startPC} to {endPC}");
        }
      }
    }

    protected virtual NextRoutine LiftNextRoutine(NextRoutine lNextRoutine)
    {
      NextRoutine hNextRoutine;
      nextRoutineMap.TryGetValue(lNextRoutine, out hNextRoutine);
      return hNextRoutine;
    }

    protected virtual AtomicPath LiftAtomicPath(AtomicPath lPath)
    {
      AtomicPath hPath = null;
      pathMap.TryGetValue(lPath, out hPath);
      return hPath;
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
            var threads := s.s.threads;
            var globals := s.s.mem.globals;
            var ghosts := s.s.ghosts;
            var tid_init := s.config.tid_init;
            { d.Code }
          }}
        ";
        pgp.AddPredicate(str, "defs");
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
        pgp.AddPredicate(str, "defs");
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
            function {auxInitName}(s:LState, config:Armada_Config) : {iad.TypeName}
            {{
              {iad.InitCode}
            }}
          ";
          pgp.AddFunction(str, "specs");

          string auxNextName = $"AuxNext_{iad.FieldName}";
          str = $@"
            function {auxNextName}(s: LPlusState, s': LState, step: L.Armada_Step, tid: Armada_ThreadHandle) : {iad.TypeName}
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
    /// Revelations
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateRevelationLemmas()
    {
      GenerateRevelationLemmas("L", pgp.symbolsLow);
      GenerateRevelationLemmas("H", pgp.symbolsHigh);
    }

    protected void GenerateRevelationLemmas(string moduleName, ArmadaSymbolTable symbols)
    {
      string str;

      var pr = new ModuleStepPrinter(moduleName);

      foreach (var nextRoutine in symbols.NextRoutines)
      {
        str = $@"
          lemma lemma_OpenStep_{moduleName}_{nextRoutine.NameSuffix}(
            s: {moduleName}.Armada_TotalState,
            step: {moduleName}.Armada_Step,
            tid: Armada_ThreadHandle
            )
            requires step.Armada_Step_{nextRoutine.NameSuffix}?
            ensures  {moduleName}.Armada_ValidStep(s, step, tid) <==>
                       tid in s.threads && s.stop_reason.Armada_NotStopped? && {pr.ValidStepInvocation(nextRoutine)}
            ensures  {moduleName}.Armada_ValidStep(s, step, tid) ==>
                       {moduleName}.Armada_GetNextState(s, step, tid) == {pr.GetNextStateInvocation(nextRoutine)}
          {{
            reveal {moduleName}.Armada_ValidStepCases();
            reveal {moduleName}.Armada_GetNextState();
          }}
        ";
        pgp.AddLemma(str, "revelations");
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Atomic specs
    ////////////////////////////////////////////////////////////////////////

    protected void GenerateAtomicSpecs(bool avoidFinalUnmappedStoppingStep = true,
                                       HashSet<ArmadaPC> lExtraRecurrentPCs = null,
                                       HashSet<ArmadaPC> hExtraRecurrentPCs = null)
    {
      GeneratePCEffectLemmas();

      lAtomic = new AtomicSpec(pgp, pgp.symbolsLow, "latomic", "LAtomic", true, "L", "LPlusState",
                               "LPlus_GetSpecFunctions()", "GetLPlusSpec()",
                               "LPlus_ValidStep", "LPlus_GetNextState");
      lAtomic.MakeSpec(lExtraRecurrentPCs);

      GenerateLiftToAtomicLemma();

      hAtomic = new AtomicSpec(pgp, pgp.symbolsHigh, "hatomic", "HAtomic", false, "H", "HState",
                               "H.Armada_GetSpecFunctions()", "GetHSpec()", "H.Armada_ValidStep",
                               "H.Armada_GetNextState");
      hAtomic.MakeSpec(hExtraRecurrentPCs);

      GenerateLiftFromAtomicLemma();

      if (nextRoutineMap == null) {
        pathMap = lAtomic.CreatePathMap(hAtomic);
      }
      else {
        pathMap = lAtomic.CreatePathMap(hAtomic, nextRoutineMap, avoidFinalUnmappedStoppingStep);
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// LiftToAtomic
    ////////////////////////////////////////////////////////////////////////

    public void GenerateLiftToAtomicSimpleRequirementsLemma()
    {
      string str = @"
        lemma lemma_LiftToAtomicSimpleRequirements()
          ensures var lasf := LPlus_GetSpecFunctions();
                  var hasf := LAtomic_GetSpecFunctions();
                  && LInitImpliesHInit(lasf, hasf)
                  && StateOKsMatch(lasf, hasf)
                  && NonyieldingPCsMatch(lasf, hasf)
                  && ThreadPCsMatch(lasf, hasf)
        {
        }
      ";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    public void GenerateTausLiftableLemma()
    {
      var stepPr = new LPlusStepPrinter();
      stepPr.Step = "lstep";

      var pathPr = new PathPrinter(lAtomic);
      pathPr.State = "s";
      pathPr.States = "hstates";
      pathPr.Steps = "hsteps";
      pathPr.Path = "hpath";

      string str = $@"
        lemma lemma_TausLiftable()
          ensures var lasf := LPlus_GetSpecFunctions();
                  var hasf := LAtomic_GetSpecFunctions();
                  TausLiftable(lasf, hasf)
        {{
          reveal_LAtomic_ValidPath();
          reveal_LAtomic_GetStateAfterPath();
          var lasf := LPlus_GetSpecFunctions();
          var hasf := LAtomic_GetSpecFunctions();
          forall s, s', lstep, tid {{:trigger TausLiftableConditions(lasf, s, s', lstep, tid)}}
            | TausLiftableConditions(lasf, s, s', lstep, tid)
            ensures exists hpath :: && hasf.path_valid(s, hpath, tid)
                              && hasf.path_type(hpath).AtomicPathType_Tau? 
                              && s' == hasf.path_next(s, hpath, tid)
          {{
            { stepPr.GetOpenValidStepInvocation(pgp.symbolsLow.TauNextRoutine) }
            var hpath := LAtomic_Path_Tau(LAtomic_PathSteps_Tau(lstep));
            { pathPr.GetOpenPathInvocation(lAtomic.TauPath) }
            ProofCustomizationGoesHere();
            assert && hasf.path_valid(s, hpath, tid)
                   && hasf.path_type(hpath).AtomicPathType_Tau? 
                   && s' == hasf.path_next(s, hpath, tid);
          }}
        }}
      ";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    public string GenerateCompressStepSequenceBodyForPathPrefix(AtomicPathPrefix pathPrefix)
    {
      var pos = pathPrefix.NumNextRoutines - 1;
      var nextRoutine = pathPrefix.LastNextRoutine;
      string str = "";
      var stepsRemaining = (pos == 0) ? "steps" : $"steps[{pos}..]";
      str += $@"
          if steps[{pos}].Armada_Step_{nextRoutine.NameSuffix}? {{
            var s{pos + 1} := asf.step_next(s{pos}, steps[{pos}], tid);
            assert steps[{pos+1}..] == {stepsRemaining}[1..];
            assert StepsStartNonyieldingNonrecurrent(asf, LAtomic_IsRecurrentPC, s{pos + 1}, s', steps[{pos + 1}..], tid);
            assert |steps[{pos + 1}..]| == 0 <==> ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s{pos + 1}, tid);
            lemma_PCEffectOfStep_L_{nextRoutine.NameSuffix}(s{pos}.s, steps[{pos}], tid);
      ";
      if (pathPrefix.EndType is PCAtomicType.Nonyielding) {
        str += $@"
            assert !ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s{pos + 1}, tid);
            assert steps[{pos+1}] == steps[{pos + 1}..][0];
            lemma_PossibleStepsFromPC_L_{nextRoutine.endPC}(s{pos + 1}.s, steps[{pos + 1}], tid);
        ";
        foreach (var descendant in pathPrefix.Extensions)
        {
          str += GenerateCompressStepSequenceBodyForPathPrefix(descendant);
        }
        str += @"
             assert false;
           }
        ";
      }
      else {
        var path = pathPrefix.PathVal;
        var pr = new PathPrinter(lAtomic);
        str += $@"
            assert ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s{pos + 1}, tid);
            assert s' == s{pos + 1};
            path := LAtomic_Path_{path.Name}(LAtomic_PathSteps_{path.Name}(
        ";
        str += String.Join(", ", Enumerable.Range(0, pos + 1).Select(i => $"steps[{i}]"));
        str += $@"));
            { pr.GetOpenPathInvocation(path) }
            return;
          }}
        ";
      }
      return str;
    }

    public void GenerateCompressStepSequenceIntoPathStartingAt(ArmadaPC startPC)
    {
      string str;

      str = $@"
        lemma lemma_CompressStepSequenceIntoPathStartingAt_{startPC}(
          asf: Armada_SpecFunctions<LPlusState, L.Armada_Step, L.Armada_PC>,
          s: LPlusState,
          s': LPlusState,
          steps: seq<L.Armada_Step>,
          tid: Armada_ThreadHandle
          ) returns (
          path: LAtomic_Path
          )
          requires asf == LPlus_GetSpecFunctions()
          requires |steps| > 0
          requires !steps[0].Armada_Step_Tau?
          requires LPlus_ValidStep(s, steps[0], tid)
          requires ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s, tid)
          requires ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s', tid)
          requires StepsStartNonyieldingNonrecurrent(asf, LAtomic_IsRecurrentPC, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
          requires s.s.threads[tid].pc.{startPC}?
          ensures  LAtomic_ValidPath(s, path, tid)
          ensures  s' == LAtomic_GetStateAfterPath(s, path, tid)
          ensures  !LAtomic_GetPathType(path).AtomicPathType_Tau?
          ensures  AtomicPathTypeMatchesPCTypes(LAtomic_GetSpecFunctions(), s, path, tid)
        {{
          var s0 := s;
          lemma_PossibleStepsFromPC_L_{startPC}(s.s, steps[0], tid);
      ";
      foreach (var pathPrefix in lAtomic.RootPathPrefixesByPC(startPC))
      {
        str += GenerateCompressStepSequenceBodyForPathPrefix(pathPrefix);
      }
      str += @"
          assert false;
        }}
      ";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    public void GenerateCompressStepSequenceLemmas()
    {
      string str;

      str = @"
        lemma lemma_CompressStepSequenceIntoPath(
          asf: Armada_SpecFunctions<LPlusState, L.Armada_Step, L.Armada_PC>,
          s: LPlusState,
          s': LPlusState,
          steps: seq<L.Armada_Step>,
          tid: Armada_ThreadHandle
          ) returns (
          path: LAtomic_Path
          )
          requires asf == LPlus_GetSpecFunctions()
          requires |steps| > 0
          requires !steps[0].Armada_Step_Tau?
          requires LPlus_ValidStep(s, steps[0], tid)
          requires ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s, tid)
          requires ThreadYieldingOrRecurrent(asf, LAtomic_IsRecurrentPC, s', tid)
          requires StepsStartNonyieldingNonrecurrent(asf, LAtomic_IsRecurrentPC, asf.step_next(s, steps[0], tid), s', steps[1..], tid)
          ensures  LAtomic_ValidPath(s, path, tid)
          ensures  s' == LAtomic_GetStateAfterPath(s, path, tid)
          ensures  !LAtomic_GetPathType(path).AtomicPathType_Tau?
          ensures  AtomicPathTypeMatchesPCTypes(LAtomic_GetSpecFunctions(), s, path, tid)
        {
          var pc := s.s.threads[tid].pc;
          assert L.Armada_IsNonyieldingPC(pc) ==> LAtomic_IsRecurrentPC(pc);
          match pc {
      ";
      foreach (var pc in lAtomic.AllPCs)
      {
        str += $"    case {pc} =>\n";
        if (pgp.symbolsLow.IsNonyieldingPC(pc) && !lAtomic.RecurrentPCs.Contains(pc)) {
          str += "     assert false;\n";
        }
        else {
          GenerateCompressStepSequenceIntoPathStartingAt(pc);
          str += $"    path := lemma_CompressStepSequenceIntoPathStartingAt_{pc}(asf, s, s', steps, tid);\n";
        }
      }
      str += "}\n}\n";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    public void GenerateSequencesCompressibleLemma()
    {
      string str = @"
        lemma lemma_SequencesCompressible()
          ensures SequencesCompressible(LPlus_GetSpecFunctions(), LAtomic_GetSpecFunctions(), LAtomic_IsRecurrentPC)
        {
          var lasf := LPlus_GetSpecFunctions();
          var hasf := LAtomic_GetSpecFunctions();
          forall s, s', lsteps, tid {:trigger SequencesCompressibleConditions(lasf, LAtomic_IsRecurrentPC, s, s', lsteps, tid)}
            | SequencesCompressibleConditions(lasf, LAtomic_IsRecurrentPC, s, s', lsteps, tid)
            ensures exists hpath :: SequencesCompressibleConclusions(hasf, s, s', tid, hpath)
          {
            var hpath := lemma_CompressStepSequenceIntoPath(lasf, s, s', lsteps, tid);
            assert SequencesCompressibleConclusions(hasf, s, s', tid, hpath);
          }
        }
      ";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    public void GenerateLiftToAtomicLemma()
    {
      var liftFile = pgp.proofFiles.CreateAuxiliaryProofFile("LiftToAtomic");
      liftFile.IncludeAndImportGeneratedFile("specs");
      liftFile.IncludeAndImportGeneratedFile("pceffect");
      liftFile.IncludeAndImportGeneratedFile("revelations");
      liftFile.IncludeAndImportGeneratedFile("latomic");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy", "util_collections_seqs_s");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/LiftToAtomic.i.dfy",
                                "LiftToAtomicModule");
      liftFile.AddImport("GenericArmadaAtomicModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("LiftToAtomic");

      GenerateLiftToAtomicSimpleRequirementsLemma();
      GenerateTausLiftableLemma();
      GenerateCompressStepSequenceLemmas();
      GenerateSequencesCompressibleLemma();

      string str = $@"
        lemma lemma_LiftToAtomic() returns (refinement_relation:RefinementRelation<LPlusState, LPlusState>)
          ensures SpecRefinesSpec(Armada_SpecFunctionsToSpec(LPlus_GetSpecFunctions()), AtomicSpec(LAtomic_GetSpecFunctions()),
                                  refinement_relation)
          ensures refinement_relation == iset s: LPlusState | true :: RefinementPair(s, s)
        {{
          lemma_LiftToAtomicSimpleRequirements();
          lemma_TausLiftable();
          lemma_SequencesCompressible();
          refinement_relation := lemma_SpecRefinesAtomicSpec(LPlus_GetSpecFunctions(), LAtomic_GetSpecFunctions(), LAtomic_IsRecurrentPC);
        }}
      ";
      pgp.AddLemma(str, "LiftToAtomic");
    }

    ////////////////////////////////////////////////////////////////////////
    /// LiftFromAtomic
    ////////////////////////////////////////////////////////////////////////

    private void GenerateLiftTauPathFromAtomicLemma(AtomicPath atomicPath)
    {
      var pr = new PathPrinter(hAtomic);
      var str = $@"
        lemma lemma_HAtomic_LiftFromAtomic_Tau(
          lasf: AtomicSpecFunctions<H.Armada_TotalState, HAtomic_Path, H.Armada_PC>,
          hasf: Armada_SpecFunctions<H.Armada_TotalState, H.Armada_Step, H.Armada_PC>,
          s: H.Armada_TotalState,
          s': H.Armada_TotalState,
          path: HAtomic_Path,
          tid: Armada_ThreadHandle
          ) returns (
          hsteps: seq<H.Armada_Step>
          )
          requires lasf == HAtomic_GetSpecFunctions()
          requires hasf == H.Armada_GetSpecFunctions()
          requires lasf.path_type(path).AtomicPathType_Tau?
          requires AtomicLiftPathFromAtomicPossible(lasf, s, s', path, tid)
          ensures  AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, tid, hsteps)
        {{
          { pr.GetOpenPathInvocation(hAtomic.TauPath) }
          ProofCustomizationGoesHere();
          hsteps := [steps.step0];
          lemma_PCEffectOfStep_H_Tau(s, steps.step0, tid);
        }}
      ";
      pgp.AddLemma(str, "LiftFromAtomic");
    }

    private void GenerateSpecificLiftPathFromAtomicLemma(AtomicPath atomicPath)
    {
      if (atomicPath.Tau) {
        GenerateLiftTauPathFromAtomicLemma(atomicPath);
        return;
      }

      var n = atomicPath.NumNextRoutines;
      var pr = new PathPrinter(hAtomic);

      var str = $@"
        lemma lemma_HAtomic_LiftFromAtomic_{atomicPath.Name}(
          lasf: AtomicSpecFunctions<H.Armada_TotalState, HAtomic_Path, H.Armada_PC>,
          hasf: Armada_SpecFunctions<H.Armada_TotalState, H.Armada_Step, H.Armada_PC>,
          s: H.Armada_TotalState,
          s': H.Armada_TotalState,
          path: HAtomic_Path,
          tid: Armada_ThreadHandle
          ) returns (
          hsteps: seq<H.Armada_Step>
          )
          requires lasf == HAtomic_GetSpecFunctions()
          requires hasf == H.Armada_GetSpecFunctions()
          requires path.HAtomic_Path_{atomicPath.Name}?
          requires AtomicLiftPathFromAtomicPossible(lasf, s, s', path, tid)
          ensures  AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, tid, hsteps)
        {{
          { pr.GetOpenValidPathInvocation(atomicPath) }
      ";
      str += "hsteps := [";
      str += String.Join(", ", Enumerable.Range(0, n).Select(i => $"steps.step{i}"));
      str += "];\n";
      str += String.Concat(Enumerable.Range(0, n).Select(
        i => $@"
          lemma_PCEffectOfStep_H_{atomicPath.NextRoutines[i].NameSuffix}(states.s{i}, steps.step{i}, tid);
        "
      ));
      str += String.Concat(Enumerable.Range(0, n).Select(
        i => $@"                                                                                                            
          assert Armada_NextMultipleSteps(hasf, states.s{n - i}, s', hsteps[{n-i}..], tid);
          assert hsteps[{n-i-1}..][1..] == hsteps[{n-i}..];
        "
      ));
      str += String.Concat(Enumerable.Range(1, n - 1).Select(
        i => $@"                                                                                                            
          assert Armada_StepsStartNonyielding(hasf, states.s{n - i}, s', hsteps[{n-i}..], tid);
        "
      ));
      if (atomicPath.EndType == PCAtomicType.Yielding) {
        str += $@"
          assert Armada_ThreadYielding(hasf, s', tid);
        ";
      }
      str += $@"
          assert hsteps == hsteps[0..];
          assert {atomicPath.OptionalNotForOK}hasf.state_ok(states.s{n});
          assert Armada_NextMultipleSteps(hasf, s, s', hsteps, tid);
        }}
      ";
      pgp.AddLemma(str, "LiftFromAtomic");
    }

    private void GenerateLiftPathFromAtomicLemma()
    {
      foreach (var atomicPath in hAtomic.AtomicPaths)
      {
        GenerateSpecificLiftPathFromAtomicLemma(atomicPath);
      }

      var str = $@"
        lemma lemma_LiftPathFromAtomic(
          lasf: AtomicSpecFunctions<H.Armada_TotalState, HAtomic_Path, H.Armada_PC>,
          hasf: Armada_SpecFunctions<H.Armada_TotalState, H.Armada_Step, H.Armada_PC>,
          s: H.Armada_TotalState,
          s': H.Armada_TotalState,
          path: HAtomic_Path,
          tid: Armada_ThreadHandle
          ) returns (
          hsteps: seq<H.Armada_Step>
          )
          requires lasf == HAtomic_GetSpecFunctions()
          requires hasf == H.Armada_GetSpecFunctions()
          requires AtomicLiftPathFromAtomicPossible(lasf, s, s', path, tid)
          ensures  AtomicLiftPathFromAtomicSuccessful(lasf, hasf, s, s', path, tid, hsteps)
       {{
         match path {{
      ";
      str += String.Concat(hAtomic.AtomicPaths.Select(p => $@"
          case HAtomic_Path_{p.Name}(_) =>
            hsteps := lemma_HAtomic_LiftFromAtomic_{p.Name}(lasf, hasf, s, s', path, tid);
            return;
      "));
      str += "}\n }\n";
      pgp.AddLemma(str, "LiftFromAtomic");
    }

    public void GenerateLiftFromAtomicLemma()
    {
      var liftFile = pgp.proofFiles.CreateAuxiliaryProofFile("LiftFromAtomic");
      liftFile.IncludeAndImportGeneratedFile("specs");
      liftFile.IncludeAndImportGeneratedFile("pceffect");
      liftFile.IncludeAndImportGeneratedFile("revelations");
      liftFile.IncludeAndImportGeneratedFile("hatomic");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy", "util_collections_seqs_s");
      liftFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/LiftFromAtomic.i.dfy",
                                "LiftFromAtomicModule");
      liftFile.AddImport("GenericArmadaAtomicModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("LiftFromAtomic");

      GenerateLiftPathFromAtomicLemma();

      string str = $@"
        lemma lemma_LiftFromAtomic() returns (refinement_relation: RefinementRelation<H.Armada_TotalState, H.Armada_TotalState>)
          ensures SpecRefinesSpec(AtomicSpec(HAtomic_GetSpecFunctions()), Armada_SpecFunctionsToSpec(H.Armada_GetSpecFunctions()),
                                  refinement_relation)
          ensures refinement_relation == iset s: H.Armada_TotalState | true :: RefinementPair(s, s)
        {{
          var lasf := HAtomic_GetSpecFunctions();
          var hasf := H.Armada_GetSpecFunctions();
          forall ls, ls', path, tid | AtomicLiftPathFromAtomicPossible(lasf, ls, ls', path, tid)
            ensures exists hsteps :: AtomicLiftPathFromAtomicSuccessful(lasf, hasf, ls, ls', path, tid, hsteps)
          {{
            var hsteps := lemma_LiftPathFromAtomic(lasf, hasf, ls, ls', path, tid);
          }}
          refinement_relation := lemma_AtomicSpecRefinesSpec(lasf, hasf);
        }}
      ";
      pgp.AddLemma(str, "LiftFromAtomic");
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
      var caseBodies = String.Concat(pcMap.Select(mapping => $"case {mapping.Key.ToString()} => H.{mapping.Value}\n"));
      var fn = $@"
        function ConvertPC_LH(pc: L.Armada_PC) : H.Armada_PC
        {{
          match pc
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertStackVars_LH(string methodName)
    {
      var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var ps = smst.AllVariablesInOrder.Select(v => $"vs.{v.FieldName}");
      var fn = $@"
        function ConvertStackVars_LH_{methodName}(vs: L.Armada_StackVars_{methodName}) : H.Armada_StackVars_{methodName}
        {{
          H.Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertStackFrame_LH()
    {
      var methodNames = pgp.symbolsLow.MethodNames;
      foreach (var methodName in methodNames) {
        GenerateConvertStackVars_LH(methodName);
      }
      var caseBodies = String.Concat(methodNames.Select(methodName =>
        $@"case Armada_StackFrame_{methodName}(vs) => H.Armada_StackFrame_{methodName}(ConvertStackVars_LH_{methodName}(vs))"
      ));
      var fn = $@"
        function ConvertStackFrame_LH(frame: L.Armada_StackFrame) : H.Armada_StackFrame
        {{
          match frame
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertGlobals_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
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

    protected virtual void GenerateConvertGhosts_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
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

    protected virtual void GenerateConvertAddrs_LH()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalAddressableArmadaVariable) {
          ps.Add($"addrs.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertAddrs_LH(addrs: L.Armada_Addrs) : H.Armada_Addrs
        {{
          H.Armada_Addrs({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertGlobalStaticVar_LH()
    {
      var caseBodies = "case Armada_GlobalStaticVarNone => H.Armada_GlobalStaticVarNone\n";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          caseBodies += $"case Armada_GlobalStaticVar_{varName} => H.Armada_GlobalStaticVar_{varName}\n";
        }
      }
      var fn = $@"
        function ConvertGlobalStaticVar_LH(v: L.Armada_GlobalStaticVar) : H.Armada_GlobalStaticVar
        {{
          match v
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
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
          H.Armada_StoreBufferEntry(ConvertStoreBufferLocation_LH(entry.loc), entry.value, ConvertPC_LH(entry.pc))
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
                              ConvertAddrs_LH(s.addrs), s.joinable_tids)
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
        function ConvertConfig_LH(config:Armada_Config) : Armada_Config
        {
          config
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
    /// Step abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual string GetStepCaseForSuppressedNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;

      // This is the case where the next routine doesn't have a corresponding next routine in the high layer,
      // e.g., because it's an assignment to a hidden variable.  In this case, just arbitrarily map it to
      // something we know to exist, namely H.Armada_Step_Tau.

      var bvs = nextRoutine.HasFormals ? "_" : "";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => H.Armada_Step_Tau\n";
    }

    protected virtual string GetStepCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;
      var hNextRoutine = LiftNextRoutine(nextRoutine);
      string hname = (hNextRoutine != null) ? hNextRoutine.NameSuffix : "Tau";

      var bvs = nextRoutine.HasFormals ? "params" : "";

      string caseBody;
      if (hNextRoutine == null) {
        caseBody = "H.Armada_Step_Tau";
      }
      else if (hNextRoutine.HasFormals) {
        var ps = nextRoutine.Formals.Select(f => $"params.{f.LocalVarName}");
        caseBody = $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))";
      }
      else {
        caseBody = $"H.Armada_Step_{hname}";
      }

      return $"case Armada_Step_{nextRoutineName}({bvs}) => {caseBody}\n";
    }

    protected virtual string GetStepCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      return GetStepCaseForNormalNextRoutine_LH(nextRoutine);
    }

    protected virtual void GenerateConvertStep_LH()
    {
      var caseBodies = String.Concat(pgp.symbolsLow.NextRoutines.Select(nextRoutine => GetStepCaseForNextRoutine_LH(nextRoutine)));
      var fn = $@"
        function ConvertStep_LH(step: L.Armada_Step) : H.Armada_Step
        {{
          match step
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertAtomicPathStateDependent_LH()
    {
      string str = @"
        function ConvertAtomicPath_LH(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle) : HAtomic_Path
          requires LAtomic_ValidPath(ls, lpath, tid)
        {
          reveal LAtomic_ValidPath();
          reveal LAtomic_GetStateAfterPath();
          match lpath
      ";

      var pr = new PathPrinter(lAtomic);

      foreach (var lpath in lAtomic.AtomicPaths)
      {
        if (pathMap.ContainsKey(lpath)) {
          var hpath = pathMap[lpath];
          str += $@"
            case LAtomic_Path_{lpath.Name}(steps) =>
              var states := LAtomic_GetPathStates_{lpath.Name}(ls, tid, steps);
          ";
          str += $"HAtomic_Path_{hpath.Name}(HAtomic_PathSteps_{hpath.Name}(";
          str += String.Join(", ", Enumerable.Range(0, lpath.NextRoutines.Count)
                                             .Where(i => nextRoutineMap.ContainsKey(lpath.NextRoutines[i]))
                                             .Select(i => $"ConvertStep_LH(states.s{i}, steps.step{i}, tid)"));
          str += "))\n";
        }
        else {
          str += $"case LAtomic_Path_{lpath.Name}(_) => HAtomic_Path_Tau(HAtomic_PathSteps_Tau(H.Armada_Step_Tau()))\n";
        }
      }
      str += "}";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertAtomicPath_LH()
    {
      if (stateDependentConvertStep) {
        GenerateConvertAtomicPathStateDependent_LH();
        return;
      }

      string str = @"
        function ConvertAtomicPath_LH(lpath: LAtomic_Path) : HAtomic_Path
        {
          match lpath
      ";
      foreach (var lpath in lAtomic.AtomicPaths)
      {
        if (pathMap.ContainsKey(lpath) && pathMap[lpath] != null) {
          var hpath = pathMap[lpath];
          str += $"case LAtomic_Path_{lpath.Name}(steps) => HAtomic_Path_{hpath.Name}(HAtomic_PathSteps_{hpath.Name}(";
          str += String.Join(", ", Enumerable.Range(0, lpath.NextRoutines.Count)
                                             .Where(i => nextRoutineMap.ContainsKey(lpath.NextRoutines[i]))
                                             .Select(i => $"ConvertStep_LH(steps.step{i})"));
          str += "))\n";
        }
        else {
          str += $"case LAtomic_Path_{lpath.Name}(_) => HAtomic_Path_Tau(HAtomic_PathSteps_Tau(H.Armada_Step_Tau()))\n";
        }
      }
      str += "}";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertAtomicTraceEntry_LH()
    {
      string str;
      if (stateDependentConvertStep) {
        str = @"
          function ConvertAtomicTraceEntry_LH(ls: LPlusState, lentry: AtomicTraceEntry<LAtomic_Path>): AtomicTraceEntry<HAtomic_Path>
            requires AtomicValidStep(LAtomic_GetSpecFunctions(), ls, lentry)
          {
            GenericAtomicLiftTraceEntryStateDependent(LAtomic_GetSpecFunctions(), ls, lentry, ConvertAtomicPath_LH)
          }
        ";
        pgp.AddFunction(str, "convert");
      }
      else {
        str = @"
          function ConvertAtomicTraceEntry_LH(lentry:AtomicTraceEntry<LAtomic_Path>) : AtomicTraceEntry<HAtomic_Path>
          {
            GenericAtomicLiftTraceEntry(lentry, ConvertAtomicPath_LH)
          }
        ";
        pgp.AddFunction(str, "convert");
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// State refinement functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateConvertPC_HL(Dictionary<ArmadaPC, ArmadaPC> reversePCMap)
    {
      var caseBodies = String.Concat(reversePCMap.Select(mapping => $"case {mapping.Key} => L.{mapping.Value}\n"));
      var fn = $@"
        function ConvertPC_HL(pc: H.Armada_PC) : L.Armada_PC
        {{
          match pc
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertStackVars_HL(string methodName)
    {
      var smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
      var ps = smst.AllVariablesInOrder.Select(v => $"vs.{v.FieldName}");
      var fn = $@"
        function ConvertStackVars_HL_{methodName}(vs: H.Armada_StackVars_{methodName}) : L.Armada_StackVars_{methodName}
        {{
          L.Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertStackFrame_HL()
    {
      var caseBodies = "";
      foreach (var methodName in pgp.symbolsHigh.MethodNames) {
        GenerateConvertStackVars_HL(methodName);
        caseBodies += $"case Armada_StackFrame_{methodName}(vs) => L.Armada_StackFrame_{methodName}(ConvertStackVars_HL_{methodName}(vs))\n";
      }

      var fn = $@"
        function ConvertStackFrame_HL(frame: H.Armada_StackFrame) : L.Armada_StackFrame
        {{
          match frame
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertGlobals_HL()
    {
      var g = pgp.symbolsHigh.Globals;
      var ps = pgp.symbolsHigh.Globals.VariableNames.Select(varName => $"globals.{g.Lookup(varName).FieldName}");
      var fn = $@"
        function ConvertGlobals_HL(globals: H.Armada_Globals) : L.Armada_Globals
        {{
          L.Armada_Globals({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertGhosts_HL()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
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

    protected virtual void GenerateConvertAddrs_HL()
    {
      var ps = new List<string>();
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var v = pgp.symbolsHigh.Globals.Lookup(varName);
        if (v is GlobalAddressableArmadaVariable) {
          ps.Add($"addrs.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertAddrs_HL(addrs: H.Armada_Addrs) : L.Armada_Addrs
        {{
          L.Armada_Addrs({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected virtual void GenerateConvertGlobalStaticVar_HL()
    {
      var caseBodies = $"case Armada_GlobalStaticVarNone => L.Armada_GlobalStaticVarNone\n";
      foreach (var varName in pgp.symbolsHigh.Globals.VariableNames) {
        var gv = pgp.symbolsHigh.Globals.Lookup(varName);
        if (gv is UnaddressableArmadaVariable && !gv.NoTSO()) {
          caseBodies += $"case Armada_GlobalStaticVar_{varName} => L.Armada_GlobalStaticVar_{varName}\n";
        }
      }
      var fn = $@"
        function ConvertGlobalStaticVar_HL(v: H.Armada_GlobalStaticVar) : L.Armada_GlobalStaticVar
        {{
          match v
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "convert");
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
            case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
              L.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_HL(v), fields)
            case Armada_StoreBufferLocation_Addressable(p) =>
              L.Armada_StoreBufferLocation_Addressable(p)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertStoreBufferEntry_HL()
    {
      string str = @"
        function ConvertStoreBufferEntry_HL(entry:H.Armada_StoreBufferEntry) : L.Armada_StoreBufferEntry
        {
          L.Armada_StoreBufferEntry(ConvertStoreBufferLocation_HL(entry.loc), entry.value, ConvertPC_HL(entry.pc))
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
                              ConvertAddrs_HL(s.addrs), s.joinable_tids)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected virtual void GenerateConvertConfig_HL()
    {
      string str = @"
        function ConvertConfig_HL(config:Armada_Config) : Armada_Config
        {
          config
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

      if (proof.IncludeImportedFiles) {
        foreach (var importedFile in importedFiles) {
          proof.AddInclude(importedFile);
        }
      }

      proof.AddImport(pgp.mLow.Name, "L");
      proof.AddImport(pgp.mHigh.Name, "H");
      proof.AddImport("AnnotatedBehaviorModule");
      if (pgp.symbolsLow.StructsModuleName != null) {
        proof.AddImport(pgp.symbolsLow.StructsModuleName);
      }

      if (proof.IncludeImportedFiles) {
        foreach (var importedModule in importedModules) {
          proof.AddImport(importedModule);
        }
      }
    }

    protected void GenerateProofHeader()
    {
      GenerateSpecsFile();
      GenerateRevelationLemmas();
      pgp.proofFiles.AssociateProofGenerator(this);
    }

    protected void GenerateSpecsFile()
    {
      pgp.AddImport("util_collections_seqs_s", null, "specs");

      pgp.AddTypeSynonym("type LState = L.Armada_TotalState", "specs");
      pgp.AddTypeSynonym("type HState = H.Armada_TotalState", "specs");
      pgp.AddTypeSynonym("type LSpec = AnnotatedBehaviorSpec<LState, Armada_Multistep<L.Armada_Step>>", "specs");
      pgp.AddTypeSynonym("type HSpec = AnnotatedBehaviorSpec<HState, Armada_Multistep<H.Armada_Step>>", "specs");
      pgp.AddTypeSynonym("type LPlusSpec = AnnotatedBehaviorSpec<LPlusState, Armada_Multistep<L.Armada_Step>>", "specs");

      string str;

      str = @"
        function GetLSpec() : LSpec
        {
          SpecFunctionsToAnnotatedSpec(L.Armada_GetSpecFunctions())
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function GetHSpec() : HSpec
        {
          SpecFunctionsToAnnotatedSpec(H.Armada_GetSpecFunctions())
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function GetLPlusSpec() : LPlusSpec
        {
          SpecFunctionsToAnnotatedSpec(LPlus_GetSpecFunctions())
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

      var auxiliaryParams = String.Concat(auxiliaries.Select(aux => $", {aux.FieldName}: {aux.TypeName}"));
      pgp.AddDatatype($"datatype LPlusState = LPlusState(s: LState, config: Armada_Config{auxiliaryParams})", "specs");

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
        predicate LPlus_ValidStep(s: LPlusState, step:L.Armada_Step, tid: Armada_ThreadHandle)
        {
          L.Armada_ValidStep(s.s, step, tid)
        }
      ";
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
        function LPlus_GetNextState(splus: LPlusState, step: L.Armada_Step, tid: Armada_ThreadHandle) : (splus': LPlusState)
        {
          var s' := L.Armada_GetNextState(splus.s, step, tid);
      ";
      foreach (var aux in auxiliaries) {
        str += $"  var field_{aux.FieldName} := {aux.NextName}(splus, s', step, tid);\n";
      }
      str += "LPlusState(s', splus.config";
      foreach (var aux in auxiliaries) {
        str += $", field_{aux.FieldName}";
      }
      str += ")\n";
      str += "}\n";
      pgp.AddFunction(str, "specs");

      str = @"
        function LPlus_GetSpecFunctions() : Armada_SpecFunctions<LPlusState, L.Armada_Step, L.Armada_PC>
        {
          Armada_SpecFunctions(LPlus_Init, LPlus_ValidStep, LPlus_GetNextState,
                              (step: L.Armada_Step) => step.Armada_Step_Tau?,
                              (s: LPlusState) => s.s.stop_reason.Armada_NotStopped?,
                              (s: LPlusState, tid: Armada_ThreadHandle) =>
                                if tid in s.s.threads then Some(s.s.threads[tid].pc) else None,
                              L.Armada_IsNonyieldingPC)
        }
      ";
      pgp.AddFunction(str, "specs");

      str = @"
        function ConvertTotalState_LPlusL(lps: LPlusState) : LState
        {
          lps.s
        }
      ";
      pgp.AddFunction(str, "PlusLemmas");

      str = @"
        lemma lemma_EstablishRequirementsForLSpecRefinesLPlusSpec()
          ensures RequirementsForSpecRefinesPlusSpec(L.Armada_GetSpecFunctions(), LPlus_GetSpecFunctions(), ConvertTotalState_LPlusL)
        {
          var lasf := L.Armada_GetSpecFunctions();
          var hasf := LPlus_GetSpecFunctions();
          var convert := ConvertTotalState_LPlusL;
          forall ls | lasf.init(ls)
            ensures exists hs :: hasf.init(hs) && ls == convert(hs)
          {
            var hs := MakeLPlusInitialState(ls);
            assert hasf.init(hs) && ls == convert(hs);
          }
        }
      ";
      pgp.AddLemma(str, "PlusLemmas");

      str = @"
        lemma lemma_LSpecRefinesLPlusSpec() returns (refinement_relation:RefinementRelation<LState, LPlusState>)
          ensures SpecRefinesSpec(Armada_SpecFunctionsToSpec(L.Armada_GetSpecFunctions()),
                                  Armada_SpecFunctionsToSpec(LPlus_GetSpecFunctions()),
                                  refinement_relation)
          ensures  refinement_relation == iset ls: LState, lps: LPlusState | ls == lps.s :: RefinementPair(ls, lps)
        {
          lemma_EstablishRequirementsForLSpecRefinesLPlusSpec();
          refinement_relation :=
            lemma_SpecRefinesPlusSpec(L.Armada_GetSpecFunctions(), LPlus_GetSpecFunctions(), ConvertTotalState_LPlusL);
        }
      ";
      pgp.AddLemma(str, "PlusLemmas");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about region invariant
    ////////////////////////////////////////////////////////////////////////

    protected virtual List<string> GenerateAddressableInvariant_Global()
    {
      pgp.AuxiliaryProof("specs").AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.AuxiliaryProof("specs").AddImport("util_collections_maps_i");

      var abstractAddresses = new List<string>();
      var preds = new List<string>();
      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        if (globalVar is GlobalAddressableArmadaVariable) {
          string globalAddress = $"s.s.addrs.{globalVarName}";
          preds.Add(AH.GetInvocationOfValidPointer("s.s.mem.heap", $"s.s.addrs.{globalVarName}", globalVar.ty));
          var descendants = AH.GetInvocationOfDescendants("s.s.mem.heap", $"s.s.addrs.{globalVarName}", globalVar.ty);
          preds.Add($@"
            forall p {{:trigger Armada_TriggerPointer(p)}} :: Armada_TriggerPointer(p) in {descendants} ==>
              p in s.addr_map && s.addr_map[p] == GlobalAbstractAddress_{globalVarName}
          ");
          abstractAddresses.Add($"GlobalAbstractAddress_{globalVarName}");
        }
      }

      var str = $@"
        predicate AddressableInvariant_Globals(s: LPlusState)
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");
      return abstractAddresses;
    }

    protected virtual List<string> GenerateAddressableInvariant_StackFrame(string methodName)
    {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var abstractAddresses = new List<string>();
      var preds = new List<string>();
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        preds.Add(AH.GetInvocationOfValidPointer("heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty));
        var descendants = AH.GetInvocationOfDescendants("heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty);
        preds.Add($@"
          forall p {{:trigger Armada_TriggerPointer(p)}} :: Armada_TriggerPointer(p) in ({descendants}) ==>
            p in addr_map &&
            addr_map[p] == LocalAbstractAddress_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(varStackFrameFieldName)}(tid, h)
        ");
        abstractAddresses.Add($"LocalAbstractAddress_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(varStackFrameFieldName)}(tid:Armada_ThreadHandle, h:int)");
      }

      var str = $@"
        predicate AddressableInvariant_StackFrame_{methodName}(addr_map:map<Armada_Pointer, AbstractAddress>, frame: L.Armada_StackFrame,
                                                               tid: Armada_ThreadHandle, h: int, heap: Armada_Heap)
          requires frame.Armada_StackFrame_{methodName}?
        {{
          var frame_vars := frame.{methodName};
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");
      return abstractAddresses;
    }

    protected virtual void GenerateAddressableMapInit()
    {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable("main");
      MapBuilder mapBuilder = new MapBuilder("m");

      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        var localAddress = $"s.threads[config.tid_init].top.main.{varStackFrameFieldName}";
        var descendants = AH.GetInvocationOfDescendants("s.mem.heap", localAddress, localVar.ty);
        mapBuilder.Add(descendants, $"LocalAbstractAddress_main_{AH.ExpandUnderscores(varStackFrameFieldName)}(config.tid_init, 0)");
      }
      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        if (globalVar is GlobalAddressableArmadaVariable) {
          string globalAddress = $"s.addrs.{globalVarName}";
          var descendants = AH.GetInvocationOfDescendants("s.mem.heap", globalAddress, globalVar.ty);
          mapBuilder.Add(descendants, $"GlobalAbstractAddress_{globalVarName}");
        }
      }

      string str = $@"
        function AddrMapInit(s: LState, config: Armada_Config): map<Armada_Pointer, AbstractAddress>
          requires L.Armada_InitConfig(s, config)
        {{
          {mapBuilder.Extract()}
        }}
      ";
      pgp.AddFunction(str, "specs");
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
        var descendants = AH.GetInvocationOfDescendants("s'.mem.heap", localAddress, localVar.ty);
        mapBuilder.Add(descendants, $"LocalAbstractAddress_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(varStackFrameFieldName)}(tid, |s'.threads[tid].stack|)");
      }
      var pr = new ModuleStepPrinter("L");
      pr.State = "splus.s";
      string str = $@"
        { pr.GetOpenStepInvocation(nextRoutine) }
        if s'.stop_reason.Armada_NotStopped? then
          var new_frame := s'.threads[tid].top.{methodName}; {mapBuilder.Extract()}
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
        var descendants = AH.GetInvocationOfDescendants("s'.mem.heap", localAddress, localVar.ty);
        mapBuilder.Add(descendants,
          $"LocalAbstractAddress_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(varStackFrameFieldName)}(newtid, 0)");
      }
      var pr = new ModuleStepPrinter("L");
      pr.State = "splus.s";
      string str = $@"
        { pr.GetOpenStepInvocation(nextRoutine) }
        if s'.stop_reason.Armada_NotStopped? then
          var newtid := params.newtid; var new_frame := s'.threads[newtid].top.{methodName}; {mapBuilder.Extract()}
        else
          splus.addr_map
      ";
      return str;
    }

    protected virtual string GenerateAddressableMapNextCase(NextRoutine nextRoutine)
    {
      string caseBody = "";
      if (nextRoutine.Stopping) {
        caseBody = "splus.addr_map";
      }
      else if (nextRoutine.nextType == NextType.Call) {
        caseBody = GenerateAddressableMapNextCase_Call(nextRoutine);
      }
      else if (nextRoutine.nextType == NextType.CreateThread) {
        caseBody = GenerateAddressableMapNextCase_CreateThread(nextRoutine);
      }
      else {
        caseBody = "splus.addr_map";
      }

      var pr = new ModuleStepPrinter("L");
      return $"{pr.CaseEntry(nextRoutine)} => {caseBody}";
    }

    protected virtual void GenerateAddressableMapNext()
    {
      var caseStrings = new List<string>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        caseStrings.Add(GenerateAddressableMapNextCase(nextRoutine));
      }

      string str = $@"
        function AddrMapNext(splus: LPlusState, s': LState, step: L.Armada_Step, tid: Armada_ThreadHandle)
          : map<Armada_Pointer, AbstractAddress>
          requires s' == L.Armada_GetNextState(splus.s, step, tid)
        {{
          if L.Armada_ValidStep(splus.s, step, tid) then
            match step
            {{
              {string.Join("\n", caseStrings)}
            }}
          else
            splus.addr_map
        }}
      ";
      pgp.AddFunction(str, "specs");
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

          && (forall tid, h ::
              tid in s.s.threads && 0 <= h < |s.s.threads[tid].stack| && s.s.threads[tid].stack[h].frame.Armada_StackFrame_{methodName}?
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
      pgp.AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(pgp.prog, "AddressableInvariant", predicateDecl), "defs");

      AddInvariant(new InternalInvariantInfo("AddressableInvariant", "AddressableInvariant", new List<string>()));
    }

    protected virtual void GenerateValidStackMethod(string methodName) {
      var methodSymbols = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var preds = new List<string>();
      var p_in_new_ptrs = new List<string>();
      foreach (var localVar in methodSymbols.AllVariablesInOrder.Where(v => v is MethodStackFrameAddressableLocalArmadaVariable)) {
        string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);
        preds.Add(AH.GetInvocationOfValidPointer("heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty));
        preds.Add($@"
          heap.tree[frame_vars.{varStackFrameFieldName}].child_type.Armada_ChildTypeRoot?
          && heap.tree[frame_vars.{varStackFrameFieldName}].child_type.rt.Armada_RootTypeStack?");
        var descendants = AH.GetInvocationOfDescendants("heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty);
        p_in_new_ptrs.Add($"p in ({descendants})");
      }

      if (p_in_new_ptrs.Count > 0) {
        preds.Add($@"
          forall p {{:trigger Armada_TriggerPointer(p)}} ::
            (Armada_TriggerPointer(p) in new_ptrs) <==> ({AH.CombineStringsWithOr(p_in_new_ptrs)})
        ");
      } else {
        preds.Add("|new_ptrs| == 0");
      }
       
      string predicateDecl = $@"
        predicate ValidStackFrame_{methodName}(frame: L.Armada_StackFrame, heap: Armada_Heap, new_ptrs: set<Armada_Pointer>) 
        requires frame.Armada_StackFrame_{methodName}?
        {{
          var frame_vars := frame.{methodName};
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(predicateDecl, "defs");
    }

    protected virtual void GenerateValidStackFramePredicate()
    {
      List<string> caseBodies = new List<string>();
      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        GenerateValidStackMethod(methodName);

        caseBodies.Add($@"
          forall tid :: tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_{methodName}? ==>
            var t := s.s.threads[tid];
            ValidStackFrame_{methodName}(t.top, s.s.mem.heap, t.new_ptrs)
        ");
        caseBodies.Add($@"
          forall tid, h ::
            tid in s.s.threads && 0 <= h < |s.s.threads[tid].stack|
            && s.s.threads[tid].stack[h].frame.Armada_StackFrame_{methodName}? ==>
            ValidStackFrame_{methodName}(s.s.threads[tid].stack[h].frame, s.s.mem.heap, s.s.threads[tid].stack[h].new_ptrs)
        ");
      }

      string str = $@"
        predicate AllValidStackFrames(s: LPlusState)
        {{
          {AH.CombineStringsWithAnd(caseBodies)}
        }}
      ";
      pgp.AddPredicate(str, "defs");
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
            addrRegionTable[localVarName] = $"rap_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(localVarName)}";
            r.regionIds.Add($"rap_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(localVarName)}");
          }
          if (localVar.ty is PointerType) {
            ptrRegionTable[localVarName] = $"rlp_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(localVarName)}";
            r.regionIds.Add($"rlp_{AH.ExpandUnderscores(methodName)}_{AH.ExpandUnderscores(localVarName)}");
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
        if (nextRoutine.Stopping) {
          continue;
        }
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
        string regionIdStr = regionInfo.GetRegionId(methodName, "&" + localVar.name);
        mapUpdates.Add($"[params.newframe_{localVar.name} := {regionIdStr}]");
      }
      string mapUpdateBody = string.Join("", mapUpdates);
      var pr = new LPlusStepPrinter();
      string str = $@"
        { pr.GetOpenStepInvocation(nextRoutine) }
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
        string regionIdStr = regionInfo.GetRegionId(methodName, "&" + localVar.name);
        mapUpdates.Add($"[params.newframe_{localVar.name} := {regionIdStr}]");
      }
      string mapUpdateBody = string.Join("", mapUpdates);
      var pr = new LPlusStepPrinter();
      string str = $@"
        { pr.GetOpenStepInvocation(nextRoutine) }
        s.region_map{mapUpdateBody}
      ";
      return str;
    }
    
    protected virtual string GenerateRegionMapNextCase(NextRoutine nextRoutine, RegionInfo regionInfo)
    {
      string str = ""; // $"case Armada_Step_{nextRoutine.NameSuffix} => ";
      if (nextRoutine.Stopping) {
        str = "s.region_map";
      }
      else if (nextRoutine.nextType == NextType.MallocSuccess) {
        var updateStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
        // Get the variable from the LHS and use that to determine the case 
        string methodName = nextRoutine.method.Name;
        string varName = Printer.ExprToString(updateStmt.Lhss[0]);
        var regionId = regionInfo.GetRegionId(methodName, varName);
        var pr = new LPlusStepPrinter();
        str = $@"
          { pr.GetOpenStepInvocation(nextRoutine) }
          s.region_map[params.new_ptr := {regionId}]
        ";
      }
      else if (nextRoutine.nextType == NextType.Call) {
        str = GenerateRegionMapNextCase_Call(nextRoutine, regionInfo);
      }
      else if (nextRoutine.nextType == NextType.CreateThread) {
        str = GenerateRegionMapNextCase_CreateThread(nextRoutine, regionInfo);
      }
      else {
        str = "s.region_map";
      }

      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => {str}\n";
    }

    protected virtual void GenerateRegionMapNext(RegionInfo regionInfo)
    {
      var caseBodies =
        String.Concat(pgp.symbolsLow.NextRoutines.Select(nextRoutine => GenerateRegionMapNextCase(nextRoutine, regionInfo)));
      var fn = $@"
        function RegionMapNext(s: LPlusState, ls': LState, step: L.Armada_Step, tid: Armada_ThreadHandle)
          : map<Armada_Pointer, RegionId>
        {{
          match step
            {caseBodies}
        }}
      ";
      pgp.AddFunction(fn, "specs");
    }

    protected virtual void GenerateRegionMap(IEnumerable<string> regionIds)
    {
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

      var preds = new List<string>();
      List<string> regionMapInitUpdates = new List<string>();

      foreach (var globalVarName in pgp.symbolsLow.Globals.VariableNames) {
        var globalVar = pgp.symbolsLow.Globals.Lookup(globalVarName);
        // Global addressable variables
        if (globalVar is GlobalAddressableArmadaVariable) {
          string regionNameStr = regionInfo.GetGlobalRegionId("&" + globalVarName);

          preds.Add($"addrs.{globalVarName} in region_map");

          preds.Add($"region_map[addrs.{globalVarName}] == {regionNameStr}");

          regionMapInitUpdates.Add($"s.addrs.{globalVarName} := {regionNameStr}");
        }

        // Deal with global pointer variables
        if (globalVar.ty is PointerType) {
          string regionNameStr = regionInfo.GetGlobalRegionId(globalVarName);

          // Global addressable pointer variable
          if (globalVar is GlobalAddressableArmadaVariable) {

            // Need to ensure that the address stored in this pointer variable is in the correct region
            var pointerValue = AH.GetInvocationOfDereferencePointer("mem.heap", $"addrs.{globalVarName}", globalVar.ty);
            var validPointer = AH.GetInvocationOfValidPointer("mem.heap", $"addrs.{globalVarName}", globalVar.ty);
            preds.Add(validPointer);
            preds.Add($"({pointerValue}) == 0 || (({pointerValue}) in region_map && region_map[{pointerValue}] == {regionNameStr})");
          }
          // Global non-addressable pointer variable
          else 
          {
            preds.Add($"mem.globals.{globalVarName} == 0 || (mem.globals.{globalVarName} in region_map && region_map[mem.globals.{globalVarName}] == {regionNameStr})");
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
              regionMapInitUpdates.Add($"s.threads[config.tid_init].top.{methodName}.{varStackFrameFieldName} := {regionIdStr}");
            }

            preds.Add($@"
              forall tid, extended_frame ::
                tid in threads
                && extended_frame in threads[tid].stack
                && extended_frame.frame.Armada_StackFrame_{methodName}?
                  ==> var stack_frame := extended_frame.frame.{methodName};
                  (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
            ");

            preds.Add($@"
              forall tid ::
                tid in threads
                && threads[tid].top.Armada_StackFrame_{methodName}?
                  ==> var stack_frame := threads[tid].top.{methodName};
                  (stack_frame.{varStackFrameFieldName} in region_map && region_map[stack_frame.{varStackFrameFieldName}] == {regionIdStr})
            ");
          }
          if (localVar.ty is PointerType) { // If the variable is a pointer type
            string regionIdStr = regionInfo.GetLocalRegionId(methodName, localVarName);
            string varStackFrameFieldName = methodSymbols.GetVariableStackFrameFieldName(localVar.name);

            var validPointerStr = AH.GetInvocationOfValidPointer("mem.heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty);
            var pointerValueStr = AH.GetInvocationOfDereferencePointer("mem.heap", $"frame_vars.{varStackFrameFieldName}", localVar.ty);

            // Local addressable pointer
            if (localVar is MethodStackFrameAddressableLocalArmadaVariable) {
              preds.Add($@"
                forall tid :: tid in threads && threads[tid].top.Armada_StackFrame_{methodName}?
                ==> var frame_vars := threads[tid].top.{methodName};
                    {validPointerStr}
                    && ({pointerValueStr} == 0 ||
                        ({pointerValueStr} in region_map 
                         && region_map[{pointerValueStr}] == {regionIdStr}
                         )
                        )
              ");

              preds.Add($@"
                forall tid, extended_frame ::
                  tid in threads
                  && extended_frame in threads[tid].stack
                  && extended_frame.frame.Armada_StackFrame_{methodName}?
                    ==> var frame_vars := extended_frame.frame.{methodName};
                    {validPointerStr}
                    && ({pointerValueStr} == 0 ||
                        ({pointerValueStr} in region_map 
                         && region_map[{pointerValueStr}] == {regionIdStr}
                         )
                      )
              ");
            }
            // Local non-addressable pointer
            else {
              preds.Add($@"
                forall tid, extended_frame ::
                  tid in threads
                  && extended_frame in threads[tid].stack
                  && extended_frame.frame.Armada_StackFrame_{methodName}?
                    ==> var stack_frame_vars := extended_frame.frame.{methodName};
                    stack_frame_vars.{varStackFrameFieldName} == 0 || (stack_frame_vars.{varStackFrameFieldName} in region_map && region_map[stack_frame_vars.{varStackFrameFieldName}] == {regionIdStr})
              ");

              preds.Add($@"
                forall tid ::
                  tid in threads
                  && threads[tid].top.Armada_StackFrame_{methodName}?
                    ==> var stack_frame_vars := threads[tid].top.{methodName};
                    stack_frame_vars.{varStackFrameFieldName} == 0 || (stack_frame_vars.{varStackFrameFieldName} in region_map && region_map[stack_frame_vars.{varStackFrameFieldName}] == {regionIdStr})
              ");
            }
          }
        }
      }

      var str = $@"
        function RegionMapInit(s: LState, config: Armada_Config) : map<Armada_Pointer, RegionId>
           requires L.Armada_InitConfig(s, config)
        {{
          map[{AH.CombineStringsWithCommas(regionMapInitUpdates)}]
        }}
      ";
      pgp.AddFunction(str, "specs");

      GenerateRegionMapNext(regionInfo);

      str = $@"
        predicate RegionInvariant_mem(threads: map<Armada_ThreadHandle, L.Armada_Thread>, addrs: L.Armada_Addrs,
                                      mem: L.Armada_SharedMemory, region_map: map<Armada_Pointer, RegionId>)
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate RegionMapOnlyContainsValidOrFreedPointers(s: LPlusState)
        {
          forall k :: k in s.region_map ==> k in s.s.mem.heap.valid || k in s.s.mem.heap.freed
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = $@"
        predicate RegionInvariant(s: LPlusState)
        {{
            RegionMapOnlyContainsValidOrFreedPointers(s)
            && RegionInvariant_mem(s.s.threads, s.s.addrs, s.s.mem, s.region_map)
            && (forall tid, storeBufferEntry, threads, addrs, mem, region_map ::
                 tid in s.s.threads && storeBufferEntry in s.s.threads[tid].storeBuffer
                 && (forall p :: p in s.region_map ==> p in region_map && region_map[p] == s.region_map[p]) 
                 && RegionInvariant_mem(threads, addrs, mem, region_map) ==>
                 RegionInvariant_mem(threads, addrs, L.Armada_ApplyStoreBufferEntry(mem, storeBufferEntry), region_map))
        }}
      ";
      pgp.AddPredicate(str, "defs");

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
      pgp.AddLemma(str, "invariants");

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
      pgp.AddLemma(str, "invariants");
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
        lemma lemma_ConvertTotalStatePreservesInit(ls: LState, hs: HState, lconfig: Armada_Config, hconfig: Armada_Config)
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
          lglobals:L.Armada_Globals, lv:L.Armada_GlobalStaticVar, fields:seq<int>, value:Armada_PrimitiveValue,
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

    private void GenerateInductiveInv(ProofGenerationParams pgp, bool onlyNonstoppingPaths)
    {
      var invNames = invariants.Select(x => x.Name).ToList();

      var conjuncts = new List<string>();
      if (onlyNonstoppingPaths) {
        conjuncts.Add("s.s.stop_reason.Armada_NotStopped?");
      }
      conjuncts.AddRange(invariants.Select(inv => $"{inv.Name}(s)"));
      
      string str = $@"
        predicate InductiveInv(s:LPlusState)
        {{
          { AH.CombineStringsWithAnd(conjuncts) }
        }}
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateInitImpliesInductiveInvLemma(ProofGenerationParams pgp)
    {
      string str = @"
        lemma lemma_InitImpliesInductiveInv(s:LPlusState)
          requires LPlus_Init(s)
          ensures  InductiveInv(s)
        {
      ";
      str += String.Concat(invariants.Select(inv => $"{inv.InitLemmaName}(s);\n"));
      str += "  }\n";
      pgp.AddLemma(str, "invariants");
    }

    private void GenerateAtomicPathMaintainsInductiveInvLemma(ProofGenerationParams pgp)
    {
      string str = @"
        lemma lemma_AtomicPathMaintainsInductiveInv(s: LPlusState, s': LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(s)
          requires LAtomic_ValidPath(s, path, tid)
          requires s' == LAtomic_GetStateAfterPath(s, path, tid)
          ensures  InductiveInv(s')
        {
      ";
      str += String.Concat(invariants.Select(inv => $"{inv.NextLemmaName}(s, s', path, tid);\n"));
      str += "}\n";
      pgp.AddLemma(str, "invariants");
    }

    public void GenerateInvariantProof(ProofGenerationParams pgp, bool onlyNonstoppingPaths = false)
    {
      if (lAtomic == null) {
        AH.PrintError(pgp.prog, "Internal error:  Must call GenerateProofHeader before calling GenerateInvariantProof");
      }

      foreach (var inv in invariants) {
        inv.GenerateProofs(pgp, invariants, lAtomic, onlyNonstoppingPaths);
      }

      GenerateInductiveInv(pgp, onlyNonstoppingPaths);
      GenerateInitImpliesInductiveInvLemma(pgp);
      GenerateAtomicPathMaintainsInductiveInvLemma(pgp);
    }

    ////////////////////////////////////////////////////////////////////////
    /// Lemmas about path lifting
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GenerateLiftAtomicPathLemmaForNormalPath(AtomicPath atomicPath,
                                                                    string typeComparison = "HAtomic_GetPathType(hpath) == ty",
                                                                    string extraSignatureLines = "",
                                                                    string extraProof = "")
    {
      string convertParams = stateDependentConvertStep ? "ls, lpath, tid" : "lpath";
      var hAtomicPath = pathMap[atomicPath];
      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);
      var prioritizationAttrs = Prioritizer.GetPrioritizationAttributesForLiftAtomicPath(atomicPath, hAtomicPath);
      var str = $@"
        lemma {prioritizationAttrs} lemma_LiftAtomicPath_{atomicPath.Name}(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{atomicPath.Name}?
          { extraSignatureLines }
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hpath := ConvertAtomicPath_LH({convertParams});
                   var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
                   var ty := LAtomic_GetPathType(lpath);
                   && {typeComparison}
                   && HAtomic_ValidPath(hs, hpath, tid)
                   && hs' == ConvertTotalState_LPlusH(ls')
                   && {atomicPath.OptionalNotForOK}ls'.s.stop_reason.Armada_NotStopped?
                   && {atomicPath.OptionalNotForOK}hs'.stop_reason.Armada_NotStopped?
        {{
          { lpr.GetOpenValidPathInvocation(atomicPath) }
          var locv: H.Armada_SharedMemory := H.Armada_GetThreadLocalView(ConvertTotalState_LPlusH(ls), tid);
          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          var hs := ConvertTotalState_LPlusH(ls);
          var hpath := ConvertAtomicPath_LH({convertParams});
          var hs' := ConvertTotalState_LPlusH(ls');

          { hpr.GetOpenPathInvocation(hAtomicPath) }

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          { extraProof }
          ProofCustomizationGoesHere();
      ";
      if (atomicPath.Stopping) {
        str += "assert !hs'.stop_reason.Armada_NotStopped?;\n";
      }
      else {
        str += @"
          assert ls'.s.stop_reason.Armada_NotStopped?;
          var alt_hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
          assert hs'.stop_reason == alt_hs'.stop_reason;
        ";
        if (atomicPath.LastNextRoutine.nextType == NextType.TerminateThread) {
          str += @"
            assert tid !in hs'.threads;
            assert tid !in alt_hs'.threads;
          ";
        }
        else {
          str += "assert hs'.threads[tid] == alt_hs'.threads[tid];\n";
        }
        foreach (var tup in atomicPath.NextRoutinesWithIndices) {
          var nextRoutine = tup.Item1;
          if (nextRoutine.nextType == NextType.CreateThread) {
            var i = tup.Item2;
            str += $@"
              assert  hs'.threads[lsteps.step{i}.params_{nextRoutine.NameSuffix}.newtid] ==
                      alt_hs'.threads[lsteps.step{i}.params_{nextRoutine.NameSuffix}.newtid];
            ";
          }
        }
        str += @"
          forall other_tid
            ensures other_tid !in hs'.threads ==> other_tid !in alt_hs'.threads
            ensures other_tid in hs'.threads ==> other_tid in alt_hs'.threads && hs'.threads[other_tid] == alt_hs'.threads[other_tid]
          {
          }
          assert hs'.threads == alt_hs'.threads;
          assert hs'.mem == alt_hs'.mem;
          assert hs' == alt_hs';
        ";
      }
//      str += hpr.GetAssertValidPathInvocation(hAtomicPath);
      str += "}\n";
      pgp.AddLemma(str, "lift");
    }

    protected virtual void GenerateLiftAtomicPathLemmaForTauPath(AtomicPath atomicPath,
                                                                 string typeComparison = "HAtomic_GetPathType(hpath) == ty",
                                                                 string extraSignatureLines = "")
    {
      string convertParams = stateDependentConvertStep ? "ls, lpath, tid" : "lpath";
      var hAtomicPath = pathMap[atomicPath];
      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);
      var str = $@"
        lemma lemma_LiftAtomicPath_Tau(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{atomicPath.Name}?
          { extraSignatureLines }
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hpath := ConvertAtomicPath_LH({convertParams});
                   var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
                   var ty := LAtomic_GetPathType(lpath);
                   && {typeComparison}
                   && HAtomic_ValidPath(hs, hpath, tid)
                   && hs' == ConvertTotalState_LPlusH(ls')
                   && ls'.s.stop_reason.Armada_NotStopped? == hs'.stop_reason.Armada_NotStopped?
        {{
          { lpr.GetOpenValidPathInvocation(atomicPath) }
          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          var hs := ConvertTotalState_LPlusH(ls);
          var hpath := ConvertAtomicPath_LH({convertParams});
          var hs' := ConvertTotalState_LPlusH(ls');

          var lentry := ls.s.threads[tid].storeBuffer[0];
          var hentry := hs.threads[tid].storeBuffer[0];
          var lmem := ls.s.mem;
          var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
          var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);

          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

          { hpr.GetOpenPathInvocation(hAtomicPath) }

          var alt_hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
          ProofCustomizationGoesHere();

          assert hs'.threads[tid] == alt_hs'.threads[tid];
          assert hs'.threads == alt_hs'.threads;
          assert hs' == alt_hs';

          /* { hpr.GetAssertValidPathInvocation(hAtomicPath) } */
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    protected virtual void GenerateLiftAtomicPathLemmaForUnmappedPath(AtomicPath atomicPath, string extraSignatureLines)
    {
      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var str = $@"
        lemma lemma_LiftAtomicPath_{atomicPath.Name}(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires lpath.LAtomic_Path_{atomicPath.Name}?
          { extraSignatureLines }
          ensures  false
        {{
          { lpr.GetOpenValidPathInvocation(atomicPath) }
          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          ProofCustomizationGoesHere();
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    protected virtual void GenerateLiftAtomicPathLemmas(string typeComparison = "HAtomic_GetPathType(hpath) == ty",
                                                        string extraSignatureLines = "", string extraProof = "")
    {
      var finalCases = "";

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        if (atomicPath.Tau) {
          GenerateLiftAtomicPathLemmaForTauPath(atomicPath, typeComparison, extraSignatureLines);
        }
        else if (pathMap.ContainsKey(atomicPath) && pathMap[atomicPath] != null) {
          GenerateLiftAtomicPathLemmaForNormalPath(atomicPath, typeComparison, extraSignatureLines, extraProof);
        }
        else {
          GenerateLiftAtomicPathLemmaForUnmappedPath(atomicPath, extraSignatureLines);
        }
        finalCases += $"case LAtomic_Path_{atomicPath.Name}(_) => lemma_LiftAtomicPath_{atomicPath.Name}(ls, lpath, tid);\n";
      }

      string convertParams = stateDependentConvertStep ? "ls, lpath, tid" : "lpath";
      string str = $@"
        lemma lemma_LiftAtomicPath(ls: LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(ls)
          requires LAtomic_ValidPath(ls, lpath, tid)
          { extraSignatureLines }
          ensures  var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hpath := ConvertAtomicPath_LH({convertParams});
                   var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
                   var ty := LAtomic_GetPathType(lpath);
                   && {typeComparison}
                   && HAtomic_ValidPath(hs, hpath, tid)
                   && hs' == ConvertTotalState_LPlusH(ls')
                   && ls'.s.stop_reason.Armada_NotStopped? == hs'.stop_reason.Armada_NotStopped?
        {{
          match lpath {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    protected virtual void GenerateLiftingRelation()
    {
      string str = @"
        predicate LiftingRelation(ls:LPlusState, hs:HState)
        {
          hs == ConvertTotalState_LPlusH(ls)
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    protected virtual void GenerateEstablishAtomicPathLiftableLemma()
    {
      var convertParams = stateDependentConvertStep ? "ls, lpath, tid" : "lpath";
      string str = $@"
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
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
        {{
          var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
          lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);
          assert InductiveInv(ls');
          lemma_LiftAtomicPath(ls, lpath, tid);
          hpath := ConvertAtomicPath_LH({convertParams});
          assert LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath);
        }}
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateEstablishAtomicPathsLiftableLemma(bool skippable, bool introducible)
    {
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/LiftAtomicToAtomic.i.dfy");
      pgp.MainProof.AddImport("LiftAtomicToAtomicModule");

      string str = @"
        lemma lemma_EstablishAtomicPathsLiftable(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          inv:LPlusState->bool,
          relation:(LPlusState, HState)->bool
      ";
      if (introducible) {
        str += ", progress_measure:(HState, LAtomic_Path, Armada_ThreadHandle)->(int, int)";
      }
      str += @"
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires inv == InductiveInv
          requires relation == LiftingRelation
      ";
      if (introducible) {
        str += @"
          requires progress_measure == ProgressMeasure
        ";
      }
      str += @"
          ensures forall ls, lpath, hs, tid ::
                    inv(ls) && relation(ls, hs) && lasf.path_valid(ls, lpath, tid)
      ";
      if (skippable) {
        str += " && !AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs)";
      }
      str += @"
                    ==> exists hpath :: LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
      ";
      if (introducible) {
        str += @"
                                        || AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
        ";
      }
      str += @"
        {
          forall ls, lpath, hs, tid
            | inv(ls) && relation(ls, hs) && lasf.path_valid(ls, lpath, tid)
      ";
      if (skippable) {
        str += " && !AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs)";
      }
      str += @"
            ensures exists hpath :: LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath)
      ";
      if (introducible) {
        str += @"
                                    || AtomicPathIntroduced(lasf, hasf, relation, progress_measure, ls, lpath, tid, hs, hpath)
        ";
      }
      str += @"
          {
            var hpath := lemma_EstablishAtomicPathLiftable(lasf, hasf, ls, lpath, tid, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateEstablishInitRequirementsLemma()
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
            assert hasf.init(hs) && relation(ls, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateEstablishStateOKRequirementLemma()
    {
      string str = @"
        lemma lemma_EstablishStateOKRequirement(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          relation:(LPlusState, HState)->bool
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires relation == LiftingRelation
          ensures  forall ls, hs :: relation(ls, hs) ==> lasf.state_ok(ls) == hasf.state_ok(hs)
        {
        }
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateEstablishRelationRequirementLemma()
    {
      string str = @"
        lemma lemma_EstablishRelationRequirement(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          inv:LPlusState->bool,
          relation:(LPlusState, HState)->bool,
          refinement_relation:RefinementRelation<LPlusState, HState>
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires inv == InductiveInv
          requires relation == LiftingRelation
          requires refinement_relation == GetLPlusHRefinementRelation()
          ensures  forall ls, hs :: inv(ls) && relation(ls, hs) ==> RefinementPair(ls, hs) in refinement_relation
        {
          forall ls, hs | inv(ls) && relation(ls, hs)
            ensures RefinementPair(ls, hs) in refinement_relation
          {
          }
        }
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateLiftLAtomicToHAtomicLemma(bool skippable, bool introducible)
    {
      string str = @"
        lemma lemma_LiftLAtomicToHAtomic() returns (refinement_relation:RefinementRelation<LPlusState, H.Armada_TotalState>)
          ensures SpecRefinesSpec(AtomicSpec(LAtomic_GetSpecFunctions()), AtomicSpec(HAtomic_GetSpecFunctions()), refinement_relation)
          ensures refinement_relation == GetLPlusHRefinementRelation()
        {
          var lasf := LAtomic_GetSpecFunctions();
          var hasf := HAtomic_GetSpecFunctions();
          var inv := InductiveInv;
          var relation := LiftingRelation;
          refinement_relation := GetLPlusHRefinementRelation();
      ";
      if (introducible) {
        str += @"
          var progress_measure := ProgressMeasure;
          lemma_EstablishAtomicPathsLiftable(lasf, hasf, inv, relation, progress_measure);
        ";
      }
      else {
        str += @"
          lemma_EstablishAtomicPathsLiftable(lasf, hasf, inv, relation);
        ";
      }
      str += @"
          lemma_EstablishInitRequirements(lasf, hasf, inv, relation);
          lemma_EstablishStateOKRequirement(lasf, hasf, relation);
          lemma_EstablishRelationRequirement(lasf, hasf, inv, relation, refinement_relation);
      ";
      if (skippable) {
        if (introducible) {
          str += @"
          lemma_LiftAtomicToAtomicGivenAtomicPathsLiftableGeneral(lasf, hasf, inv, relation, progress_measure, refinement_relation);
          ";
        }
        else {
          str += @"
          lemma_LiftAtomicToAtomicGivenAtomicPathsSkippablyLiftable(lasf, hasf, inv, relation, refinement_relation);
          ";
        }
      }
      else if (introducible) {
        str += @"
          lemma_LiftAtomicToAtomicGivenAtomicPathsIntroduciblyLiftable(lasf, hasf, inv, relation, progress_measure, refinement_relation);
        ";
      }
      else {
        str += @"
          lemma_LiftAtomicToAtomicGivenAtomicPathsLiftable(lasf, hasf, inv, relation, refinement_relation);
        ";
      }
      str += "}\n";
      pgp.AddLemma(str);
    }

    protected void GenerateGenericAtomicPropertyLemmas()
    {
      string str;

      str = $@"
        lemma lemma_LAtomic_AtomicInitImpliesOK()
          ensures AtomicInitImpliesOK(LAtomic_GetSpecFunctions())
        {{
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LAtomic_AtomicInitImpliesInv()
          ensures AtomicInitImpliesInv(LAtomic_GetSpecFunctions(), InductiveInv)
        {{
          forall s | LAtomic_GetSpecFunctions().init(s)
            ensures InductiveInv(s)
          {{
            lemma_InitImpliesInductiveInv(s);
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_LAtomic_AtomicPathPreservesInv()
          ensures AtomicPathPreservesInv(LAtomic_GetSpecFunctions(), InductiveInv)
        {{
          var asf := LAtomic_GetSpecFunctions();
          forall s, path, tid | InductiveInv(s) && asf.path_valid(s, path, tid)
            ensures InductiveInv(asf.path_next(s, path, tid))
          {{
            var s' := asf.path_next(s, path, tid);
            lemma_AtomicPathMaintainsInductiveInv(s, s', path, tid);
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    protected virtual void GenerateFinalProof()
    {
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/refinement/RefinementConvolution.i.dfy");
      pgp.MainProof.AddImport("RefinementConvolutionModule");

      string str = @"
        lemma lemma_ProveRefinement()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var rr1 := lemma_LSpecRefinesLPlusSpec();
          var rr2 := lemma_LiftToAtomic();
          var rr3 := lemma_LiftLAtomicToHAtomic();
          var rr4 := lemma_LiftFromAtomic();
          lemma_SpecRefinesSpecQuadrupleConvolution(
            L.Armada_Spec(),
            Armada_SpecFunctionsToSpec(LPlus_GetSpecFunctions()),
            AtomicSpec(LAtomic_GetSpecFunctions()),
            AtomicSpec(HAtomic_GetSpecFunctions()),
            H.Armada_Spec(),
            rr1,
            rr2,
            rr3,
            rr4,
            GetLHRefinementRelation()
            );
        }
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC functions
    ////////////////////////////////////////////////////////////////////////

    protected virtual void GeneratePCFunctions(bool low)
    {
      var c = low ? "L" : "H";
      var symbols = low ? pgp.symbolsLow : pgp.symbolsHigh;

      var methodNames = symbols.AllMethods.AllMethodNames;

      string str;

      str = $"datatype {c}MethodName = " + String.Join(" | ", methodNames.Select(x => $"{c}MethodName_{x}"));
      pgp.AddDatatype(str, "specs");

      str = $@"
        function MethodToInstructionCount_{c}(m:{c}MethodName) : (v:int)
          ensures v >= 0
        {{
          match m
      ";
      foreach (var methodName in methodNames)
      {
        var methodInfo = symbols.AllMethods.LookupMethod(methodName);
        str += $"    case {c}MethodName_{methodName} => {methodInfo.NumPCs}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      var pcs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllPCs(pcs);
      var maxInstructionCount = pcs.Select(pc => pc.instructionCount).Max();

      str = $@"
        function PCToMethod_{c}(pc:{c}.Armada_PC) : {c}MethodName
        {{
          match pc
      ";
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => {c}MethodName_{pc.methodName}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      str = $@"
        function MaxPCInstructionCount_{c}() : int
        {{
          { maxInstructionCount }
        }}
      ";
      pgp.AddFunction(str, "specs");

      str = $@"
        function PCToInstructionCount_{c}(pc:{c}.Armada_PC) : (v:int)
          ensures 0 <= v <= MaxPCInstructionCount_{c}()
        {{
          match pc
      ";
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => {pc.instructionCount}\n";
      }
      str += "  }\n";
      pgp.AddFunction(str, "specs");

      str = $@"
        lemma lemma_PCInstructionCountLessThanMethodInstructionCount_{c}(pc:{c}.Armada_PC)
          ensures 0 <= PCToInstructionCount_{c}(pc) < MethodToInstructionCount_{c}(PCToMethod_{c}(pc))
        {{
        }}
      ";
      pgp.AddLemma(str, "specs");

      str = $@"
        predicate StackMatchesMethod_{c}(frame:{c}.Armada_StackFrame, m:{c}MethodName)
        {{
          match m
      ";
      foreach (var methodName in methodNames) {
        str += $"    case {c}MethodName_{methodName} => frame.Armada_StackFrame_{methodName}?\n";
      }
      str += "  }\n";
      pgp.AddPredicate(str, "specs");
    }

    protected virtual void GeneratePCFunctions_L()
    {
      GeneratePCFunctions(true);
    }

    protected virtual void GeneratePCFunctions_H()
    {
      GeneratePCFunctions(false);
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
      pgp.AddPredicate(str, "defs");

      var inv = new InternalInvariantInfo("StackMatchesMethodInv", "StackMatchesMethodInv", new List<string>());
      invariants.Add(inv);
    }
  }
  
}
