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

  public class NextFormal {
    public readonly string GloballyUniqueVarName;
    public readonly string LocalVarName;
    public readonly string VarType;

    public NextFormal(string globallyUniqueVarName, string localVarName, Type varType, ArmadaSymbolTable symbols)
    {
      GloballyUniqueVarName = globallyUniqueVarName;
      LocalVarName = localVarName;
      VarType = symbols.FlattenType(varType).ToString();
    }

    public NextFormal(string globallyUniqueVarName, string localVarName, string varTypeName)
    {
      GloballyUniqueVarName = globallyUniqueVarName;
      LocalVarName = localVarName;
      VarType = varTypeName;
    }
  }

  public enum NextType { Update, Call, Return, CreateThread, MallocSuccess, MallocFailure, CallocSuccess, CallocFailure, Dealloc,
                         IfTrue, IfFalse, JumpPastElse, WhileTrue, WhileFalse, WhileEnd, WhileBreak, WhileContinue,
                         AssertTrue, AssertFalse, Somehow, Fence, Goto, CompareAndSwap, AtomicExchange, Join,
                         ExternStart, ExternContinue, ExternEnd, TerminateThread, TerminateProcess, Tau }

  public class NextRoutineConstructor : IConstraintCollector {
    private Program prog;
    private ArmadaSymbolTable symbols;
    private PredicateBuilder validDefinedStepBuilder;
    private PredicateBuilder validUndefinedStepBuilder;
    private ExpressionBuilder getNextStateBuilder;
    private ArmadaPC startPC;
    private ArmadaPC endPC;
    private List<NextFormal> formals;
    private bool valid;
    private bool hasUndefinedBehaviorAvoidanceConstraint;
    private NextType nextType;
    private MethodInfo methodInfo;
    private ArmadaStatement armadaStatement;
    private Statement stmt;
    private NextRoutine definedBehaviorNextRoutine;
    private NextRoutine undefinedBehaviorNextRoutine;

    public string s;
    public string entry;
    public string tid;
    public string t;
    public string locv;
    public Method method;

    public NextRoutineConstructor(Program i_prog, ArmadaSymbolTable i_symbols, NextType i_nextType, MethodInfo i_methodInfo,
                                  ArmadaStatement i_armadaStatement, Statement i_stmt, ArmadaPC i_startPC, ArmadaPC i_endPC)
    {
      prog = i_prog;
      symbols = i_symbols;
      nextType = i_nextType;
      validDefinedStepBuilder = new PredicateBuilder(i_prog, true);
      validUndefinedStepBuilder = new PredicateBuilder(i_prog, false);
      getNextStateBuilder = new ExpressionBuilder(i_prog);
      methodInfo = i_methodInfo;
      method = methodInfo == null ? null : methodInfo.method;
      armadaStatement = i_armadaStatement;
      stmt = i_stmt;
      startPC = i_startPC;
      endPC = i_endPC;
      formals = new List<NextFormal>();
      valid = true;
      hasUndefinedBehaviorAvoidanceConstraint = false;
      definedBehaviorNextRoutine = null;
      undefinedBehaviorNextRoutine = null;

      s = ReserveVariableName("s");
      entry = ReserveVariableName("entry");
      tid = ReserveVariableName("tid");
      t = ReserveVariableName("t");
      locv = ReserveVariableName("locv");

      if (startPC != null) {
        AddConjunct($"{t}.pc.{startPC}?");
        AddConjunct($"{t}.top.Armada_StackFrame_{startPC.methodName}?");

        if (methodInfo != null) {
          var constraints = methodInfo.GetEnablingConstraintCollector(startPC);
          if (constraints != null && !constraints.Empty) {
            AddConjunct($"Armada_EnablingConditions_{startPC}(s, tid)");
          }
        }

        AddConjunct("Armada_UniversalStepConstraint(s, tid)");
      }
    }

    public string AddFormal(NextFormal formal)
    {
      formals.Add(formal);
      return formal.LocalVarName;
    }
    
    public IEnumerable<NextFormal> Formals { get { return formals; } }
    public NextRoutine DefinedBehaviorNextRoutine { get { return definedBehaviorNextRoutine; } }
    public NextRoutine UndefinedBehaviorNextRoutine { get { return undefinedBehaviorNextRoutine; } }

    private string MakeNameSuffix()
    {
      switch (nextType) {
        case NextType.Tau:
          return "Tau";
        case NextType.Return:
          return "ReturnFrom_" + startPC.methodName + "_" + startPC.Name + "_To_" + endPC.methodName + "_" + endPC.Name;
        default:
          return nextType.ToString("g") + "_" + startPC.methodName + "_" + startPC.Name;
      }
    }

    public bool Valid { get { return valid; } }

    public string ReserveVariableName(string varName)
    {
      validDefinedStepBuilder.ReserveVariableName(varName);
      validUndefinedStepBuilder.ReserveVariableName(varName);
      return getNextStateBuilder.ReserveVariableName(varName);
    }

    public string AddVariableDeclaration(string varName, string value)
    {
      validDefinedStepBuilder.AddVariableDeclaration(varName, value);
      validUndefinedStepBuilder.AddVariableDeclaration(varName, value);
      return getNextStateBuilder.AddVariableDeclaration(varName, value);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(string constraint)
    {
      hasUndefinedBehaviorAvoidanceConstraint = true;
      validDefinedStepBuilder.AddConjunct(constraint);
      validUndefinedStepBuilder.AddDisjunct($"!({constraint})");
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList)
      {
        AddUndefinedBehaviorAvoidanceConstraint(e);
      }
    }

    public void AddConjunct(string conjunct)
    {
      validDefinedStepBuilder.AddConjunct(conjunct);
      validUndefinedStepBuilder.AddConjunct(conjunct);
    }

    public void AddUBAvoidanceConstraintAsConjunct(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList) {
        validDefinedStepBuilder.AddConjunct(e);
        validUndefinedStepBuilder.AddConjunct(e);
      }
    }

    public void AddDefinedBehaviorConjunct(string conjunct)
    {
      validDefinedStepBuilder.AddConjunct(conjunct);
    }

    public void AddUBAvoidanceConstraintAsDefinedBehaviorConjunct(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList) {
        validDefinedStepBuilder.AddConjunct(e);
      }
    }

    public void SetNextState(string e)
    {
      getNextStateBuilder.SetBody(e);
    }

    public void Fail(IToken tok, string reason) {
      valid = false;
      if (reason != null) {
        AH.PrintError(prog, tok, reason);
      }
    }

    public void Fail(string reason) {
      Fail(Token.NoToken, reason);
    }

    private void ExtractInternal(ArmadaSymbolTable symbols, DeclCollector declCollector, List<string> stepCtors, bool ub)
    {
      var nameSuffix = MakeNameSuffix();
      if (ub) {
        nameSuffix = "UB_" + nameSuffix;
      }

      if (formals.Any()) {
        var paramsFormalsList = String.Join(", ", formals.Select(f => $"{f.LocalVarName}: {f.VarType}"));
        var paramsTypeDecl = $"datatype Armada_StepParams_{nameSuffix} = Armada_StepParams_{nameSuffix}({paramsFormalsList})";
        declCollector.AddItem(paramsTypeDecl);
      }

      stepCtors.Add($"Armada_Step_{nameSuffix}("
                    + (formals.Any() ? $"params_{nameSuffix}: Armada_StepParams_{nameSuffix}" : "")
                    + ")");
      
      var extraParameterDecls = formals.Any() ? $", params: Armada_StepParams_{nameSuffix}" : "";
      var extraParameterArgs = formals.Any() ? $", params" : "";
      var paramDecls = String.Concat(formals.Select(f => $"var {f.LocalVarName} := params.{f.LocalVarName};\n"));
      var validState = ub ? validUndefinedStepBuilder.Extract() : validDefinedStepBuilder.Extract();
      var nextState = ub ? $"s.(stop_reason := Armada_StopReasonUndefinedBehavior)" : $"{paramDecls}{getNextStateBuilder.Extract()}";

      declCollector.AddItem($@"
        predicate Armada_ValidStep_{nameSuffix}(s: Armada_TotalState, tid: Armada_ThreadHandle{extraParameterDecls})
          requires tid in s.threads
        {{
          var t := s.threads[tid];
          var locv := Armada_GetThreadLocalView(s, tid);
          {paramDecls}
          {validState}
        }}
      ");

      declCollector.AddItem($@"
        function Armada_GetNextState_{nameSuffix}(s: Armada_TotalState, tid: Armada_ThreadHandle{extraParameterDecls})
          : Armada_TotalState
          requires tid in s.threads
          requires Armada_ValidStep_{nameSuffix}(s, tid{extraParameterArgs})
        {{
          var t := s.threads[tid];
          var locv := Armada_GetThreadLocalView(s, tid);
          {nextState}
        }}
      ");

      var stopping = (nextType == NextType.TerminateProcess || nextType == NextType.AssertFalse || ub);
      var nextRoutine = new NextRoutine(prog, symbols, nextType, methodInfo, armadaStatement, stmt, startPC, endPC,
                                        formals, nameSuffix, ub, stopping);
      symbols.AddNextRoutine(nextRoutine);
      if (ub) {
        undefinedBehaviorNextRoutine = nextRoutine;
      }
      else {
        definedBehaviorNextRoutine = nextRoutine;
      }
    }

    public void Extract(ArmadaSymbolTable symbols, DeclCollector declCollector, List<string> stepCtors)
    {
      if (!valid) {
        return;
      }

      ExtractInternal(symbols, declCollector, stepCtors, false);
      if (hasUndefinedBehaviorAvoidanceConstraint) {
        ExtractInternal(symbols, declCollector, stepCtors, true);
      }
    }

    public bool Nonyielding { get { return symbols.IsNonyieldingPC(endPC); } }
  }

  public class NextRoutine {
    private Program prog;
    private ArmadaSymbolTable symbols;

    public NextType nextType;
    public MethodInfo methodInfo;
    public ArmadaStatement armadaStatement;
    public Statement stmt;
    public ArmadaPC startPC;
    public ArmadaPC endPC;
    private List<NextFormal> formals;
    public string nameSuffix;

    private bool undefinedBehavior;
    private bool stopping;

    public NextRoutine(Program i_prog, ArmadaSymbolTable i_symbols, NextType i_nextType, MethodInfo i_methodInfo,
                       ArmadaStatement i_armadaStatement, Statement i_stmt, ArmadaPC i_startPC, ArmadaPC i_endPC,
                       List<NextFormal> i_formals, string i_nameSuffix, bool i_undefinedBehavior, bool i_stopping)
    {
      prog = i_prog;
      symbols = i_symbols;
      nextType = i_nextType;
      methodInfo = i_methodInfo;
      armadaStatement = i_armadaStatement;
      stmt = i_stmt;
      startPC = i_startPC;
      endPC = i_endPC;
      formals = new List<NextFormal>(i_formals);
      nameSuffix = i_nameSuffix;
      undefinedBehavior = i_undefinedBehavior;
      stopping = i_stopping;
    }

    public IEnumerable<NextFormal> Formals { get { return formals; } }
    public bool HasFormals { get { return formals.Any(); } }
    public string NameSuffix { get { return nameSuffix; } }
    public bool Tau { get { return nextType == NextType.Tau; } }
    public Method method { get { return methodInfo.method; } }

    public bool Nonyielding { get { return symbols.IsNonyieldingPC(endPC); } }
    public bool UndefinedBehavior { get { return undefinedBehavior; } }
    public bool Stopping { get { return stopping; } }

    public bool TryGetBranchOutcome(out bool outcome)
    {
      outcome = BranchOutcome;
      return nextType == NextType.IfTrue ||
             nextType == NextType.WhileTrue ||
             nextType == NextType.AssertTrue ||
             nextType == NextType.IfFalse ||
             nextType == NextType.WhileFalse ||
             nextType == NextType.AssertFalse ||
             nextType == NextType.MallocSuccess ||
             nextType == NextType.MallocFailure ||
             nextType == NextType.CallocSuccess ||
             nextType == NextType.CallocFailure;
    }

    public bool BranchOutcome
    {
      get {
        return nextType != NextType.IfFalse &&
               nextType != NextType.WhileFalse &&
               nextType != NextType.AssertFalse &&
               nextType != NextType.MallocFailure &&
               nextType != NextType.CallocFailure;
      }
    }
  }
}
