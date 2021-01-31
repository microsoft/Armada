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
using System.Security.Cryptography;

namespace Microsoft.Armada {

  public abstract class PredicateBuilderNodeData
  {
    public PredicateBuilderNodeData() { }
    public abstract string Extract();
    public virtual PredicateBuilderNodeData Simplify() { return this; }
  }

  public class PredicateBuilderNodeDataFalse : PredicateBuilderNodeData
  {
    public PredicateBuilderNodeDataFalse()
    {
    }
    
    public override string Extract() { return "false"; }
  }

  public class PredicateBuilderNodeDataTrue : PredicateBuilderNodeData
  {
    public PredicateBuilderNodeDataTrue()
    {
    }
    
    public override string Extract() { return "true"; }
  }

  public class PredicateBuilderNodeDataExpression : PredicateBuilderNodeData
  {
    private string expr;
    public PredicateBuilderNodeDataExpression(string i_expr)
    {
      expr = i_expr;
    }

    public override string Extract()
    {
      return expr;
    }
  }

  public class PredicateBuilderNodeDataVariableDeclaration : PredicateBuilderNodeData
  {
    private string varName;
    private string value;
    private PredicateBuilderNode child;

    public PredicateBuilderNodeDataVariableDeclaration(string i_varName, string i_value, PredicateBuilderNode i_child)
    {
      varName = i_varName;
      value = i_value;
      child = i_child;
    }

    public override string Extract()
    {
      return $"var {varName} := {value}; {child.Extract()}";
    }

    public override PredicateBuilderNodeData Simplify()
    {
      child.Simplify();
      if (child.Data is PredicateBuilderNodeDataTrue || child.Data is PredicateBuilderNodeDataFalse) {
        return child.Data;
      }
      return this;
    }
  }

  public class PredicateBuilderNodeDataConjunction : PredicateBuilderNodeData
  {
    private List<PredicateBuilderNode> children;

    public PredicateBuilderNodeDataConjunction(PredicateBuilderNode i_child1, PredicateBuilderNode i_child2)
    {
      children = new List<PredicateBuilderNode>{ i_child1, i_child2 };
    }

    public PredicateBuilderNodeDataConjunction(List<PredicateBuilderNode> i_children)
    {
      children = new List<PredicateBuilderNode>(i_children);
    }

    public override string Extract()
    {
      return AH.CombineStringsWithAnd(children.Select(child => child.Extract()));
    }

    public List<PredicateBuilderNode> Children { get { return children; } }

    public override PredicateBuilderNodeData Simplify()
    {
      // First, simplify all children.

      foreach (var child in children) {
        child.Simplify();
      }

      // Next, inline any conjunctions, e.g., changing A && (B && C) && (D && E && F) into A && B && C && D && E && F.
      // Also, remove any trues.  Also, if we encounter a false, just return false.

      var newChildren = new List<PredicateBuilderNode>();
      foreach (var child in children)
      {
        if (child.Data is PredicateBuilderNodeDataFalse cf) {
          return cf;
        }
        else if (child.Data is PredicateBuilderNodeDataTrue) {
          continue;
        }
        else if (child.Data is PredicateBuilderNodeDataConjunction cc) {
          newChildren.AddRange(cc.Children);
        }
        else {
          newChildren.Add(child);
        }
      }

      // If we don't have any children, return true; otherwise, return a conjunction of
      // those children.

      if (newChildren.Count == 0) {
        return new PredicateBuilderNodeDataTrue();
      }
      else {
        return new PredicateBuilderNodeDataConjunction(newChildren);
      }
    }
  }

  public class PredicateBuilderNodeDataDisjunction : PredicateBuilderNodeData
  {
    private List<PredicateBuilderNode> children;

    public PredicateBuilderNodeDataDisjunction(PredicateBuilderNode child1, PredicateBuilderNode child2)
    {
      children = new List<PredicateBuilderNode>{ child1, child2 };
    }

    public PredicateBuilderNodeDataDisjunction(List<PredicateBuilderNode> i_children)
    {
      children = new List<PredicateBuilderNode>(i_children);
    }

    public override string Extract()
    {
      return AH.CombineStringsWithOr(children.Select(child => child.Extract()));
    }

    public List<PredicateBuilderNode> Children { get { return children; } }

    public override PredicateBuilderNodeData Simplify()
    {
      // First, simplify all children.

      foreach (var child in children) {
        child.Simplify();
      }

      // Next, inline any disjunctions, e.g., changing A || (B || C) || (D || E || F) into A || B || C || D || E || F.
      // Also, remove any falses.  Also, if we encounter a true, just return true.

      var newChildren = new List<PredicateBuilderNode>();
      foreach (var child in children)
      {
        if (child.Data is PredicateBuilderNodeDataTrue ct) {
          return ct;
        }
        else if (child.Data is PredicateBuilderNodeDataFalse) {
          continue;
        }
        else if (child.Data is PredicateBuilderNodeDataDisjunction cd) {
          newChildren.AddRange(cd.Children);
        }
        else {
          newChildren.Add(child);
        }
      }

      // If we don't have any children, return false; otherwise, return a disjunction of
      // those children.

      if (newChildren.Count == 0) {
        return new PredicateBuilderNodeDataFalse();
      }
      else {
        return new PredicateBuilderNodeDataDisjunction(newChildren);
      }
    }
  }

  public class PredicateBuilderNode
  {
    private PredicateBuilderNodeData data;

    public PredicateBuilderNode(PredicateBuilderNodeData i_data)
    {
      data = i_data;
    }

    public PredicateBuilderNodeData Data
    {
      get { return data; }
      set { data = value; }
    }

    public string Extract()
    {
      return data.Extract();
    }

    public void Simplify()
    {
      data = data.Simplify();
    }

    public PredicateBuilderNode AddVariableDeclaration(string varName, string value)
    {
      var newNode = new PredicateBuilderNode(data);
      data = new PredicateBuilderNodeDataVariableDeclaration(varName, value, newNode);
      return newNode;
    }

    public PredicateBuilderNode AddConjunct(string conjunct)
    {
      var newNode = new PredicateBuilderNode(data);
      var conjunctNode = new PredicateBuilderNode(new PredicateBuilderNodeDataExpression(conjunct));
      data = new PredicateBuilderNodeDataConjunction(conjunctNode, newNode);
      return newNode;
    }

    public PredicateBuilderNode AddDisjunct(string disjunct)
    {
      var newNode = new PredicateBuilderNode(data);
      var disjunctNode = new PredicateBuilderNode(new PredicateBuilderNodeDataExpression(disjunct));
      data = new PredicateBuilderNodeDataDisjunction(disjunctNode, newNode);
      return newNode;
    }
  }

  public class PredicateBuilder {
    private Program prog;
    private bool valid;
    private PredicateBuilderNode top;
    private PredicateBuilderNode current;
    private Dictionary<string, int> variableUseCount;

    public PredicateBuilder(Program i_prog, bool defaultValue)
    {
      prog = i_prog;
      valid = true;
      if (defaultValue) {
        top = new PredicateBuilderNode(new PredicateBuilderNodeDataTrue());
      }
      else {
        top = new PredicateBuilderNode(new PredicateBuilderNodeDataFalse());
      }
      current = top;
      variableUseCount = new Dictionary<string, int>();
    }

    public bool Valid { get { return valid; } }

    public string ReserveVariableName(string varName)
    {
      if (variableUseCount.ContainsKey(varName)) {
        Fail($"Internal error:  Attempt to reserve variable name that's already in use ({varName}).");
        return null;
      }
      else {
        variableUseCount[varName] = 1;
        return varName;
      }
    }

    public string AddVariableDeclaration(string varName, string value)
    {
      if (!valid) {
        Debug.Assert(false);
        return null;
      }

      int count;
      if (variableUseCount.TryGetValue(varName, out count)) {
        variableUseCount[varName] = count + 1;
        varName = $"{varName}{count+1}";
      }
      else {
        variableUseCount[varName] = 1;
      }

      current = current.AddVariableDeclaration(varName, value);

      return varName;
    }

    public void AddConjunct(string conjunct)
    {
      current = current.AddConjunct(conjunct);
    }

    public void AddDisjunct(string disjunct)
    {
      current = current.AddDisjunct(disjunct);
    }

    public string Extract()
    {
      if (!valid) {
        Debug.Assert(false);
        return null;
      }

      top.Simplify();
      return top.Extract();
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

}
