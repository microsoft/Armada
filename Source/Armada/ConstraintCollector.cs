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

  public interface IFailureReporter {
    bool Valid { get; }
    void Fail(IToken tok, string reason);
    void Fail(string reason);
  }

  public class SimpleFailureReporter : IFailureReporter {
    private bool valid;
    private Program prog;
    
    public bool Valid { get { return valid; } }

    public SimpleFailureReporter(Program i_prog)
    {
      valid = true;
      prog = i_prog;
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
  }

  public interface IConstraintCollector : IFailureReporter {
    Expression ReserveVariableName(string varName, Type ty);
    Expression ReserveVariableName(string varName, string typeName);
    Expression AddVariableDeclaration(string varName, Expression value);
    void AddUndefinedBehaviorAvoidanceConstraint(Expression constraint);
    void AddUndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint constraint);
  }

  public class EnablingConstraintCollector : IConstraintCollector
  {
    private Program prog;
    private PredicateBuilder builder;
    private bool valid;
    private bool empty;

    public readonly Expression s;
    public readonly Expression tid;
    public readonly Expression t;
    public readonly Expression locv;
    public readonly Expression top;
    public readonly Expression ghosts;

    public EnablingConstraintCollector(Program i_prog)
    {
      prog = i_prog;
      builder = new PredicateBuilder(i_prog);
      valid = true;
      empty = true;

      s = ReserveVariableName("s", "Armada_TotalState");
      tid = ReserveVariableName("tid", "Armada_ThreadHandle");
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      t = AddVariableDeclaration("t", AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread"));
      locv = AddVariableDeclaration("locv", AH.MakeApply2("Armada_GetThreadLocalView", s, tid, "Armada_SharedMemory"));
      top = AH.MakeExprDotName(t, "top", "Armada_StackFrame");
      ghosts = AH.MakeExprDotName(s, "ghosts", "Armada_Ghosts");
    }

    public bool Valid { get { return valid; } }

    public bool Empty { get { return empty; } }

    public Expression ReserveVariableName(string varName, Type ty)
    {
      return builder.ReserveVariableName(varName, ty);
    }

    public Expression ReserveVariableName(string varName, string typeName)
    {
      return builder.ReserveVariableName(varName, typeName);
    }

    public Expression AddVariableDeclaration(string varName, Expression value)
    {
      return builder.AddVariableDeclaration(varName, value);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(Expression constraint)
    {
      empty = false;
      builder.AddConjunct(constraint);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList) {
        AddUndefinedBehaviorAvoidanceConstraint(e);
      }
    }
    
    public void AddConjunct(Expression conjunct)
    {
      empty = false;
      builder.AddConjunct(conjunct);
    }

    public void AddConjunct(UndefinedBehaviorAvoidanceConstraint constraint)
    {
      foreach (var e in constraint.AsList)
      {
        AddConjunct(e);
      }
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

    public Expression Extract()
    {
      if (!valid) {
        return null;
      }

      return builder.Extract();
    }
  }
}
