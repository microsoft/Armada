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
    public readonly Type VarType;

    public NextFormal(string globallyUniqueVarName, string localVarName, Type varType)
    {
      GloballyUniqueVarName = globallyUniqueVarName;
      LocalVarName = localVarName;
      VarType = varType;
    }

    public NextFormal(string globallyUniqueVarName, string localVarName, string varTypeName)
    {
      GloballyUniqueVarName = globallyUniqueVarName;
      LocalVarName = localVarName;
      VarType = AH.ReferToType(varTypeName);
    }
  }

  public enum NextType { Update, Call, Return, CreateThread, Malloc, Calloc, Dealloc,
                         IfTrue, IfFalse, JumpPastElse, WhileTrue, WhileFalse, WhileEnd, WhileBreak, WhileContinue,
                         Assert, Somehow, Join, ExternStart, ExternContinue, ExternEnd, Terminate, Tau }

  public class NextRoutine : IConstraintCollector {
    private Program prog;
    private ArmadaSymbolTable symbols;
    private PredicateBuilder validStepBuilder;
    private PredicateBuilder crashAvoidanceBuilder;
    private ExpressionBuilder getNextStateBuilder;
    public ArmadaPC pc;
    public ArmadaPC endPC;
    private List<NextFormal> formals;
    private bool valid;

    public NextType nextType;
    public Method method;
    public ArmadaStatement armadaStatement;
    public Statement stmt;
    public Expression s;
    public Expression tid;
    public Expression t;
    public Expression locv;

    public NextRoutine(Program i_prog, ArmadaSymbolTable i_symbols, NextType i_nextType, MethodInfo methodInfo,
                       ArmadaStatement i_armadaStatement, Statement i_stmt, ArmadaPC i_pc, ArmadaPC i_endPC)
    {
      prog = i_prog;
      symbols = i_symbols;
      nextType = i_nextType;
      validStepBuilder = new PredicateBuilder(i_prog);
      crashAvoidanceBuilder = new PredicateBuilder(i_prog);
      getNextStateBuilder = new ExpressionBuilder(i_prog);
      method = methodInfo != null ? methodInfo.method : null;
      armadaStatement = i_armadaStatement;
      stmt = i_stmt;
      pc = i_pc;
      endPC = i_endPC;
      formals = new List<NextFormal>();
      valid = true;

      s = ReserveVariableName("s", "Armada_TotalState");
      tid = ReserveVariableName("tid", "Armada_ThreadHandle");
      locv = null;

      // s.stop_reason.Armada_NotStopped?
      var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
      var not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
      AddConjunct(not_stopped);

      // tid in s.threads
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      AddConjunct(tid_in_threads);

      // var t := s.threads[tid];
      t = AddVariableDeclaration("t", AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread"));

      // var locv := Armada_GetThreadLocalView(s, tid);
      locv = AH.MakeApply2("Armada_GetThreadLocalView", s, tid, "Armada_SharedMemory");
      locv = AddVariableDeclaration("locv", locv);

      if (pc != null) {
        var current_pc = AH.MakeExprDotName(t, "pc", "Armada_PC");
        var pc_correct = AH.MakeEqExpr(current_pc, AH.MakeNameSegment(pc.ToString(), "Armada_PC"));
        AddConjunct(pc_correct);

        // t.top.Armada_StackFrame_{methodName}?
        var top = AH.MakeExprDotName(t, "top", "Armada_StackFrame");
        var top_frame_correct = AH.MakeExprDotName(top, $"Armada_StackFrame_{pc.methodName}?", new BoolType());
        AddConjunct(top_frame_correct);

        if (methodInfo != null) {
          var constraints = methodInfo.GetEnablingConstraintCollector(pc);
          if (constraints != null && !constraints.Empty) {
            var enabling_condition = AH.MakeApply2($"Armada_EnablingConditions_{pc}", s, tid, new BoolType());
            AddConjunct(enabling_condition);
          }
        }
      }
    }

    public void AddFormal(NextFormal formal) { formals.Add(formal); }
    public IEnumerable<NextFormal> Formals { get { return formals; } }

    public string GetNameSuffix()
    {
      switch (nextType) {
        case NextType.Tau:
          return "Tau";
        case NextType.Return:
          return "ReturnFrom_" + pc.methodName + "_" + pc.Name + "_To_" + endPC.methodName + "_" + endPC.Name;
        default:
          return nextType.ToString("g") + "_" + pc.methodName + "_" + pc.Name;
      }
    }

    public string NameSuffix
    {
      get {
        return GetNameSuffix();
      }
    }

    public bool Valid { get { return valid; } }

    public Expression ReserveVariableName(string varName, Type ty)
    {
      validStepBuilder.ReserveVariableName(varName, ty);
      crashAvoidanceBuilder.ReserveVariableName(varName, ty);
      return getNextStateBuilder.ReserveVariableName(varName, ty);
    }

    public Expression ReserveVariableName(string varName, string typeName)
    {
      validStepBuilder.ReserveVariableName(varName, typeName);
      crashAvoidanceBuilder.ReserveVariableName(varName, typeName);
      return getNextStateBuilder.ReserveVariableName(varName, typeName);
    }

    public Expression AddVariableDeclaration(string varName, Expression value)
    {
      validStepBuilder.AddVariableDeclaration(varName, value);
      crashAvoidanceBuilder.AddVariableDeclaration(varName, value);
      return getNextStateBuilder.AddVariableDeclaration(varName, value);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(Expression constraint)
    {
      crashAvoidanceBuilder.AddConjunct(constraint);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList)
      {
        AddUndefinedBehaviorAvoidanceConstraint(e);
      }
    }
    
    public void AddConjunct(Expression conjunct)
    {
      validStepBuilder.AddConjunct(conjunct);
    }
    
    public void AddConjunct(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList) {
        validStepBuilder.AddConjunct(e);
      }
    }

    public void SetNextState(Expression e)
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

    public void Extract(ModuleDefinition m, ArmadaSymbolTable symbols, List<MemberDecl> newDefaultClassDecls,
                        List<DatatypeCtor> entryCtors, List<MatchCaseExpr> overallNextCases,
                        List<MatchCaseExpr> validStepCases, List<MatchCaseExpr> crashAvoidanceCases,
                        List<MatchCaseExpr> getNextStateCases)
    {
      if (!valid) {
        return;
      }

      var entryFormals = new List<Formal> { AH.MakeFormal("tid", "Armada_ThreadHandle") };
      var commonFormals = new List<Formal> {
        AH.MakeFormal("s", "Armada_TotalState"),
        AH.MakeFormal("tid", "Armada_ThreadHandle")
      };
      var overallNextFormals = new List<Formal> {
        AH.MakeFormal("s", "Armada_TotalState"),
        AH.MakeFormal("s'", "Armada_TotalState"),
        AH.MakeFormal("tid", "Armada_ThreadHandle")
      };
      var caseArguments = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      var commonMatchBodyArguments = new List<Expression>() {
        AH.MakeNameSegment("s", "Armada_TotalState"),
        AH.MakeNameSegment("tid", "Armada_ThreadHandle")
      };
      var overallNextMatchBodyArguments = new List<Expression>() {
        AH.MakeNameSegment("s", "Armada_TotalState"),
        AH.MakeNameSegment("s'", "Armada_TotalState"),
        AH.MakeNameSegment("tid", "Armada_ThreadHandle")
      };
      foreach (var f in formals) {
        var flattened_type = symbols.FlattenType(f.VarType);
        commonFormals.Add(AH.MakeFormal(f.LocalVarName, flattened_type));
        overallNextFormals.Add(AH.MakeFormal(f.LocalVarName, flattened_type));
        entryFormals.Add(AH.MakeFormal(f.GloballyUniqueVarName, flattened_type));
        caseArguments.Add(AH.MakeBoundVar(f.LocalVarName, flattened_type));
        commonMatchBodyArguments.Add(AH.MakeNameSegment(f.LocalVarName, flattened_type));
        overallNextMatchBodyArguments.Add(AH.MakeNameSegment(f.LocalVarName, flattened_type));
      }

      var nameSuffix = NameSuffix;
      var entryName = $"Armada_TraceEntry_{nameSuffix}";
      entryCtors.Add(AH.MakeDatatypeCtor(entryName, entryFormals));

      var validStepFn = AH.MakeNameSegment($"Armada_ValidStep_{nameSuffix}", (Type)null);
      var validStepMatchBody = AH.SetExprType(new ApplySuffix(Token.NoToken, validStepFn, commonMatchBodyArguments), new BoolType());
      validStepCases.Add(AH.MakeMatchCaseExpr(entryName, caseArguments, validStepMatchBody));
      var validStepPredBody = validStepBuilder.Extract();
      var validStepName = $"Armada_ValidStep_{nameSuffix}";
      var validStepPred = AH.MakePredicate(validStepName, commonFormals, validStepPredBody);
      newDefaultClassDecls.Add(validStepPred);

      var crashAvoidanceFn = AH.MakeNameSegment($"Armada_UndefinedBehaviorAvoidance_{nameSuffix}", (Type)null);
      var crashAvoidanceMatchBody = AH.SetExprType(new ApplySuffix(Token.NoToken, crashAvoidanceFn, commonMatchBodyArguments), new BoolType());
      crashAvoidanceCases.Add(AH.MakeMatchCaseExpr(entryName, caseArguments, crashAvoidanceMatchBody));
      var crashAvoidanceName = $"Armada_UndefinedBehaviorAvoidance_{nameSuffix}";
      var crashAvoidancePredBody = crashAvoidanceBuilder.Extract();
      var crashAvoidancePred = AH.MakePredicateWithReq(crashAvoidanceName, commonFormals, validStepMatchBody, crashAvoidancePredBody);
      newDefaultClassDecls.Add(crashAvoidancePred);

      var getNextStateFn = AH.MakeNameSegment($"Armada_GetNextState_{nameSuffix}", (Type)null);
      var getNextStateMatchBody = AH.SetExprType(new ApplySuffix(Token.NoToken, getNextStateFn, commonMatchBodyArguments), "Armada_TotalState");
      getNextStateCases.Add(AH.MakeMatchCaseExpr(entryName, caseArguments, getNextStateMatchBody));
      var getNextStateName = $"Armada_GetNextState_{nameSuffix}";
      var getNextStateFnBody = getNextStateBuilder.Extract();
      var getNextStateReq = AH.MakeAndExpr(validStepMatchBody, crashAvoidanceMatchBody);
      var getNextStateFunc = AH.MakeFunctionWithReq(getNextStateName, commonFormals, getNextStateReq, getNextStateFnBody);
      newDefaultClassDecls.Add(getNextStateFunc);

      // predicate Armada_Next_{nameSuffix}(s:Armada_TotalState, s':Armada_TotalState, ...) {
      //     && Armada_ValidStep_{nameSuffix}(s, ...)
      //     && s' == if Armada_UndefinedBehaviorAvoidance(s, ...) then Armada_GetNextState(s, ...)
      //              else s.(stop_reason := Armada_StopReasonUndefinedBehavior)
      // }

      var s_with_undefined_behavior =
        AH.MakeDatatypeUpdateExpr(s, "stop_reason", AH.MakeNameSegment("Armada_StopReasonUndefinedBehavior", "Armada_StopReason"));
      var target_s_prime = AH.MakeIfExpr(crashAvoidanceMatchBody, getNextStateMatchBody, s_with_undefined_behavior);
      var s_prime = AH.MakeNameSegment("s'", "Armada_TotalState");
      var s_prime_correct = AH.MakeEqExpr(s_prime, target_s_prime);
      var overallNextBody = AH.MakeAndExpr(validStepMatchBody, s_prime_correct);
      var overallNextName = $"Armada_Next_{nameSuffix}";
      var overallNextPred = AH.MakePredicate(overallNextName, overallNextFormals, overallNextBody);
      newDefaultClassDecls.Add(overallNextPred);

      var overallNextFn = AH.MakeNameSegment(overallNextName, (Type)null);
      var overallNextMatchBody = AH.SetExprType(new ApplySuffix(Token.NoToken, overallNextFn, overallNextMatchBodyArguments),
                                                new BoolType());
      overallNextCases.Add(AH.MakeMatchCaseExpr(entryName, caseArguments, overallNextMatchBody));
    }
  }
}
