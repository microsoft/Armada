using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class StackVarHidingProofGenerator : VarHidingProofGenerator
  {
    private StackVariableHidingStrategyDecl strategy;
    private string hiddenVariablesMethodName;
    private HashSet<string> hiddenVariables;

    public StackVarHidingProofGenerator(ProofGenerationParams i_pgp, StackVariableHidingStrategyDecl i_strategy)
      : base(i_pgp, false)
    {
      strategy = i_strategy;
      hiddenVariablesMethodName = strategy.MethodName;
      hiddenVariables = new HashSet<string>(strategy.Variables);

      foreach (var varName in strategy.Variables) {
        var v = pgp.symbolsLow.Lookup(hiddenVariablesMethodName, varName);
        if (!(v is MethodStackFrameUnaddressableLocalArmadaVariable)) {
          AH.PrintError(pgp.prog, $"Variable {hiddenVariablesMethodName}.{varName} isn't a noaddr stack variable, but stack_var_hiding can only hide noaddr stack variables");
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Checking that the layers are similar enough to generate a proof
    ////////////////////////////////////////////////////////////////////////

    protected override bool CheckVariableNameListEquivalence(IEnumerable<string> varNames_l, IEnumerable<string> varNames_h,
                                                             ArmadaSingleMethodSymbolTable s_l, ArmadaSingleMethodSymbolTable s_h,
                                                             string methodName, string descriptor)
    {
      string[] vars_l;
      if (methodName == hiddenVariablesMethodName) {
        vars_l = varNames_l.Where(v => !hiddenVariables.Contains(v)).ToArray();
      }
      else {
        vars_l = varNames_l.ToArray();
      }
      var vars_h = varNames_h.ToArray();
      if (vars_l.Length != vars_h.Length) {
        AH.PrintError(pgp.prog, $"Method {methodName} has {vars_l.Length} {descriptor} non-hidden variables in level {pgp.mLow.Name} but {vars_h.Length} of them in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < vars_l.Length; ++i) {
        var name_l = vars_l[i];
        var name_h = vars_h[i];
        if (name_l != name_h) {
          AH.PrintError(pgp.prog, $"In method {methodName}, {descriptor} non-hidden variable number {i+1} is named {name_l} in level {pgp.mLow.Name} but named {name_h} in level {pgp.mHigh.Name}");
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

    ////////////////////////////////////////////////////////////////////////
    /// Abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected override bool IsVariableHidden(string methodName, string varName)
    {
      return methodName == hiddenVariablesMethodName && hiddenVariables.Contains(varName);
    }

    protected override void GenerateConvertStackVars_LH(string methodName)
    {
      var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var ps = smst.AllVariablesInOrder.Where(v => !IsVariableHidden(methodName, v.FieldName)).Select(v => $"vs.{v.FieldName}");
      var fn = $@"
        function ConvertStackVars_LH_{methodName}(vs: L.Armada_StackVars_{methodName}) : H.Armada_StackVars_{methodName}
        {{
          H.Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertAtomicPath_LH()
    {
      var skipped_strs = new List<string>();

      string convert_str = @"
        function ConvertAtomicPath_LH(s: LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle) : HAtomic_Path
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
        predicate IsSkippedPath(s: LPlusState, path:LAtomic_Path, tid: Armada_ThreadHandle)
        {{
          { AH.CombineStringsWithOr(skipped_strs) }
        }}
      ", "convert");
      pgp.AddFunction(convert_str, "convert");
    }

    protected override string GetStepCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;

      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      var hNextRoutine = LiftNextRoutine(nextRoutine);
      var ps = hNextRoutine.Formals.Select(f => $"params.{f.LocalVarName}");
      string hname = hNextRoutine.NameSuffix;
      var caseBody = hNextRoutine.HasFormals ? $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))"
                                             : $"H.Armada_Step_{hname}";
      return $"case Armada_Step_{nextRoutineName}({bvs}) => {caseBody}\n";
    }
  }

}
