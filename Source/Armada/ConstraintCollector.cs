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
    string ReserveVariableName(string varName);
    string AddVariableDeclaration(string varName, string value);
    void AddUndefinedBehaviorAvoidanceConstraint(string constraint);
    void AddUndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint constraint);
  }

  public class EnablingConstraintCollector : IConstraintCollector
  {
    private Program prog;
    private PredicateBuilder builder;
    private bool valid;
    private bool empty;

    public readonly string s;
    public readonly string tid;
    public readonly string t;
    public readonly string locv;
    public readonly string top;
    public readonly string ghosts;

    public EnablingConstraintCollector(Program i_prog)
    {
      prog = i_prog;
      builder = new PredicateBuilder(i_prog, true);
      valid = true;
      empty = true;

      s = ReserveVariableName("s");
      tid = ReserveVariableName("tid");
      var threads = $"{s}.threads";
      t = AddVariableDeclaration("t", $"{threads}[{tid}]");
      locv = AddVariableDeclaration("locv", $"Armada_GetThreadLocalView({s}, {tid})");
      top = $"{t}.top";
      ghosts = $"{s}.ghosts";
    }

    public bool Valid { get { return valid; } }

    public bool Empty { get { return empty; } }

    public string ReserveVariableName(string varName)
    {
      return builder.ReserveVariableName(varName);
    }

    public string AddVariableDeclaration(string varName, string value)
    {
      return builder.AddVariableDeclaration(varName, value);
    }

    public void AddUndefinedBehaviorAvoidanceConstraint(string constraint)
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
    
    public void AddConjunct(string conjunct)
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

    public string Extract()
    {
      if (!valid) {
        return null;
      }

      return builder.Extract();
    }
  }
}
