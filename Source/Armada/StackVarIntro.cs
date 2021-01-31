using System.Collections.Generic;
using System.Linq;
using System;

namespace Microsoft.Armada
{
  public class StackVarIntroProofGenerator : VarIntroProofGenerator
  {
    protected StackVariableIntroStrategyDecl strategy;
    public StackVarIntroProofGenerator(ProofGenerationParams i_pgp, StackVariableIntroStrategyDecl i_strategy)
      : base(i_pgp, false)
    {
      strategy = i_strategy;
      var v = pgp.symbolsHigh.Lookup(strategy.MethodName, strategy.VariableName);
      if (!(v is MethodStackFrameUnaddressableLocalArmadaVariable)) {
        AH.PrintError(pgp.prog, $"Variable {strategy.MethodName}.{strategy.VariableName} isn't a noaddr stack variable, but stack_var_intro can only introduce noaddr stack variables");
      }
    }

    protected override bool CheckVariableNameListEquivalence(IEnumerable<string> varNames_l, IEnumerable<string> varNames_h,
                                                            ArmadaSingleMethodSymbolTable s_l, ArmadaSingleMethodSymbolTable s_h,
                                                            string methodName, string descriptor)
    {
      var vars_l = varNames_l.ToArray();
      string[] vars_h;
      if (methodName == strategy.MethodName) {
        vars_h = varNames_h.Where(v => v != strategy.VariableName).ToArray();
      }
      else {
        vars_h = varNames_h.ToArray();
      }

      if (vars_l.Length != vars_h.Length) {
        AH.PrintError(pgp.prog, $"Method {methodName} has {vars_l.Length} {descriptor} variables in level {pgp.mLow.Name} but {vars_h.Length} of them in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < vars_l.Length; ++i) {
        var name_l = vars_l[i];
        var name_h = vars_h[i];
        if (name_l != name_h) {
          AH.PrintError(pgp.prog, $"In method {methodName}, {descriptor} non-introduced variable number {i+1} is named {name_l} in level {pgp.mLow.Name} but named {name_h} in level {pgp.mHigh.Name}");
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

    protected override bool IsIntroducedVariable(string methodName, string varName)
    {
      return methodName == strategy.MethodName && varName == strategy.VariableName;
    }

    protected override void GenerateConvertStackVars_LH(string methodName)
    {
      var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
      var ps = new List<string>();

      var lowVarNames = new List<string>(smst.AllVariableNamesInOrder);
      foreach (var varName in lowVarNames)
      {
        var v = smst.LookupVariable(varName);
        ps.Add($"vs.{v.FieldName}");
      }

      smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
      var highVars = new List<ArmadaVariable>(smst.AllVariablesInOrder);

      if (highVars.Count() != lowVarNames.Count()) {
        for (var i = 0; i < highVars.Count(); ++i) {
          if (!lowVarNames.Contains(highVars[i].name)) {
            var v = highVars[i];
            ps.Insert(i, strategy.InitializationExpression);
          }
        }
      }

      var fn = $@"
        function ConvertStackVars_LH_{methodName}(vs: L.Armada_StackVars_{methodName}) : H.Armada_StackVars_{methodName}
        {{
          H.Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override void GenerateConvertStackVars_HL(string methodName)
    {
      var smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
      var ps = new List<string>();
      foreach (var v in smst.AllVariablesInOrder) {
        if (methodName != strategy.MethodName || v.name != strategy.VariableName) {
          ps.Add($"vs.{v.FieldName}");
        }
      }
      var fn = $@"
        function ConvertStackVars_HL_{methodName}(vs: H.Armada_StackVars_{methodName}) : L.Armada_StackVars_{methodName}
        {{
          L.Armada_StackVars_{methodName}({AH.CombineStringsWithCommas(ps)})
        }}
      ";
      pgp.AddFunction(fn, "convert");
    }

    protected override string GetStepCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      var ps = nextRoutine.Formals.Select(f => $"params.{f.LocalVarName}").ToList();

      if (nextRoutine.nextType == NextType.Call &&
          ((ArmadaCallStatement)nextRoutine.armadaStatement).CalleeName == strategy.MethodName ||
          nextRoutine.nextType == NextType.CreateThread &&
          ((nextRoutine.stmt as UpdateStmt).Rhss[0] as CreateThreadRhs).MethodName.val == strategy.MethodName) {
        var highRoutine = LiftNextRoutine(nextRoutine);
        var highFormals = new List<NextFormal>(highRoutine.Formals);
        for (var i = 0; i < highFormals.Count(); ++ i) {
          if (!nextRoutine.Formals.Any(f => f.LocalVarName == highFormals[i].LocalVarName)) {
            ps.Insert(i, strategy.InitializationExpression);
            break;
          }
        }
      }

      var hNextRoutine = LiftNextRoutine(nextRoutine);
      string hname = hNextRoutine.NameSuffix;
      var caseBody = hNextRoutine.HasFormals ? $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))"
                                             : $"H.Armada_Step_{hname}";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => {caseBody}\n";
    }
  };
};
