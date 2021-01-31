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
    private List<string> constraints;

    public UndefinedBehaviorAvoidanceConstraint()
    {
      constraints = new List<string>();
    }

    public UndefinedBehaviorAvoidanceConstraint(string e)
    {
      constraints = new List<string>();
      if (e != null)
      {
        constraints.Add(e);
      }
    }

    public UndefinedBehaviorAvoidanceConstraint(List<string> es)
    {
      constraints = new List<string>(es);
    }

    public UndefinedBehaviorAvoidanceConstraint(UndefinedBehaviorAvoidanceConstraint other)
    {
      constraints = new List<string>(other.AsList);
    }

    public string Expr
    {
      get
      {
        return AH.CombineStringsWithAnd(constraints);
      }
    }

    public bool CanCauseUndefinedBehavior
    {
      get
      {
        return constraints.Any();
      }
    }

    public void Add(string other)
    {
      if (other != null) {
        constraints.Add(other);
      }
    }

    public void Add(List<string> other)
    {
      foreach (var e in other) {
        constraints.Add(e);
      }
    }

    public void Add(UndefinedBehaviorAvoidanceConstraint other)
    {
      Add(other.AsList);
    }

    public List<string> AsList { get { return constraints; } }

    public static UndefinedBehaviorAvoidanceConstraint operator+(UndefinedBehaviorAvoidanceConstraint c1, UndefinedBehaviorAvoidanceConstraint c2)
    {
      var ret = new UndefinedBehaviorAvoidanceConstraint(c1);
      ret.Add(c2);
      return ret;
    }

    public static UndefinedBehaviorAvoidanceConstraint operator+(UndefinedBehaviorAvoidanceConstraint c1, string c2)
    {
      var ret = new UndefinedBehaviorAvoidanceConstraint(c1);
      ret.Add(c2);
      return ret;
    }
  }

  public class ArmadaRValue
  {
    private UndefinedBehaviorAvoidanceConstraint crashAvoidance;
    private string val;

    public ArmadaRValue(UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, string i_val)
    {
      Debug.Assert(i_crashAvoidance != null);
      crashAvoidance = i_crashAvoidance;
      val = i_val;
    }

    public ArmadaRValue(string i_val)
    {
      crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      val = i_val;
    }

    public UndefinedBehaviorAvoidanceConstraint UndefinedBehaviorAvoidance { get { return crashAvoidance; } }
    public string Val { get { return val; } }
    public bool CanCauseUndefinedBehavior { get { return crashAvoidance.CanCauseUndefinedBehavior; } }
  }

  public class ArmadaRValueList
  {
    private UndefinedBehaviorAvoidanceConstraint crashAvoidance;
    private List<string> vals;

    public ArmadaRValueList()
    {
      crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
      vals = new List<string>();
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
    public List<string> Vals { get { return vals; } }
    public bool CanCauseUndefinedBehavior { get { return crashAvoidance.CanCauseUndefinedBehavior; } }
  }

}
