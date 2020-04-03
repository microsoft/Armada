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

  public class UndefinedBehaviorAvoidanceConstraint
  {
    private List<Expression> constraints;

    public UndefinedBehaviorAvoidanceConstraint()
    {
      constraints = new List<Expression>();
    }

    public UndefinedBehaviorAvoidanceConstraint(Expression e)
    {
      constraints = new List<Expression>();
      if (e != null)
      {
        e = AH.SetExprType(e, new BoolType());
        constraints.Add(e);
      }
    }

    public UndefinedBehaviorAvoidanceConstraint(List<Expression> es)
    {
      constraints = new List<Expression>(es);
    }

    public UndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint other)
    {
      constraints = new List<Expression>(other.AsList);
    }

    public Expression Expr
    {
      get
      {
        return AH.CombineExpressionsWithAnd(constraints);
      }
    }

    public bool CanCauseUndefinedBehavior
    {
      get
      {
        return constraints.Any();
      }
    }

    public void Add(Expression other)
    {
      if (other != null) {
        constraints.Add(other);
      }
    }

    public void Add(List<Expression> other)
    {
      foreach (var e in other) {
        constraints.Add(e);
      }
    }

    public void Add(UndefinedBehaviorAvoidanceConstraint other)
    {
      Add(other.AsList);
    }

    public List<Expression> AsList { get { return constraints; } }

    public static UndefinedBehaviorAvoidanceConstraint operator+(UndefinedBehaviorAvoidanceConstraint c1, UndefinedBehaviorAvoidanceConstraint c2)
    {
      var ret = new UndefinedBehaviorAvoidanceConstraint(c1);
      ret.Add(c2);
      return ret;
    }

    public static UndefinedBehaviorAvoidanceConstraint operator+(UndefinedBehaviorAvoidanceConstraint c1, Expression c2)
    {
      var ret = new UndefinedBehaviorAvoidanceConstraint(c1);
      ret.Add(c2);
      return ret;
    }
  }

  public class ArmadaRValue
  {
    private UndefinedBehaviorAvoidanceConstraint crashAvoidance;
    private Expression val;

    public ArmadaRValue(UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, Expression i_val)
    {
      Debug.Assert(i_crashAvoidance != null);
      crashAvoidance = i_crashAvoidance;
      val = i_val;
    }

    public ArmadaRValue(Expression i_val)
    {
      crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      val = i_val;
    }

    public ArmadaRValue(UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, Expression i_val, Type i_ty)
    {
      crashAvoidance = i_crashAvoidance;
      val = i_val;
      if (val != null)
      {
        val = AH.SetExprType(val, i_ty);
      }
    }

    public UndefinedBehaviorAvoidanceConstraint UndefinedBehaviorAvoidance { get { return crashAvoidance; } }
    public Expression Val { get { return val; } }
    public bool CanCauseUndefinedBehavior { get { return crashAvoidance.CanCauseUndefinedBehavior; } }
  }

  public class ArmadaRValueList
  {
    private UndefinedBehaviorAvoidanceConstraint crashAvoidance;
    private List<Expression> vals;

    public ArmadaRValueList()
    {
      crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      vals = new List<Expression>();
    }

    public void Add(ArmadaRValue rvalue)
    {
      if (rvalue != null)
      {
        crashAvoidance.Add(rvalue.UndefinedBehaviorAvoidance);
        vals.Add(rvalue.Val);
      }
      else
      {
        vals.Add(null);
      }
    }

    public UndefinedBehaviorAvoidanceConstraint UndefinedBehaviorAvoidance { get { return crashAvoidance; } }
    public List<Expression> Vals { get { return vals; } }
    public bool CanCauseUndefinedBehavior { get { return crashAvoidance.CanCauseUndefinedBehavior; } }
  }

}
