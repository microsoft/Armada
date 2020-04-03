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

  public class ExpressionBuilder {
    private Program prog;
    private bool valid;
    private List<string> variableNames;
    private List<Expression> variableValues;
    private Dictionary<string, int> variableUseCount;
    private Expression body;

    public ExpressionBuilder(Program i_prog)
    {
      prog = i_prog;
      valid = true;
      variableNames = new List<string>();
      variableValues = new List<Expression>();
      variableUseCount = new Dictionary<string, int>();
      body = null;
    }

    public bool Valid { get { return valid; } }

    public Expression ReserveVariableName(string varName, Type ty)
    {
      if (variableUseCount.ContainsKey(varName)) {
        AH.PrintError(prog, $"Internal error:  Attempt to reserve variable name that's already in use ({varName}).");
        return null;
      }
      else {
        variableUseCount[varName] = 1;
        return AH.MakeNameSegment(varName, ty);
      }
    }

    public Expression ReserveVariableName(string varName, string typeName)
    {
      return ReserveVariableName(varName, AH.ReferToType(typeName));
    }

    public Expression AddVariableDeclaration(string varName, Expression value)
    {
      if (!valid) {
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

      variableNames.Add(varName);
      variableValues.Add(value);

      return AH.MakeNameSegment(varName, value.Type);
    }

    public void SetBody(Expression e)
    {
      body = e;
    }

    public Expression Extract()
    {
      if (body == null) {
        Fail("Internal error:  Attempt to extract before body is set");
      }

      if (!valid) {
        return null;
      }

      var e = body;
      for (int i = variableNames.Count - 1; i >= 0; --i) {
        e = AH.MakeLet1Expr(variableNames[i], variableValues[i], e);
      }
      return e;
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

  public class PredicateBuilderBlock {
    private List<string> variableNames;
    private List<Expression> variableValues;
    private List<Expression> conjuncts;

    public PredicateBuilderBlock()
    {
      variableNames = new List<string>();
      variableValues = new List<Expression>();
      conjuncts = new List<Expression>();
    }

    public void AddVariableDeclaration(string varName, Expression value)
    {
      variableNames.Add(varName);
      variableValues.Add(value);
    }

    public void AddConjunct(Expression conjunct) { conjuncts.Add(conjunct); }
 
    public Expression Extract(Expression extra)
    {
      Expression e;
      if (extra != null) {
        var conjunctsPlusExtra = new List<Expression>(conjuncts);
        conjunctsPlusExtra.Add(extra);
        e = AH.CombineExpressionsWithAnd(conjunctsPlusExtra);
      }
      else {
        if (conjuncts.Count == 0) {
          return null;
        }
        e = AH.CombineExpressionsWithAnd(conjuncts);
      }

      for (int i = variableNames.Count - 1; i >= 0; --i) {
        e = AH.MakeLet1Expr(variableNames[i], variableValues[i], e);
      }

      return e;
    }
  }

  public class PredicateBuilder {
    private Program prog;
    private bool valid;
    private List<PredicateBuilderBlock> blocks;
    private Dictionary<string, int> variableUseCount;

    public PredicateBuilder(Program i_prog)
    {
      prog = i_prog;
      valid = true;
      blocks = new List<PredicateBuilderBlock> { new PredicateBuilderBlock() };
      variableUseCount = new Dictionary<string, int>();
    }

    public bool Valid { get { return valid; } }

    public Expression ReserveVariableName(string varName, Type ty)
    {
      if (variableUseCount.ContainsKey(varName)) {
        Fail($"Internal error:  Attempt to reserve variable name that's already in use ({varName}).");
        return null;
      }
      else {
        variableUseCount[varName] = 1;
        return AH.MakeNameSegment(varName, ty);
      }
    }

    public Expression ReserveVariableName(string varName, string typeName)
    {
      return ReserveVariableName(varName, AH.ReferToType(typeName));
    }

    public Expression AddVariableDeclaration(string varName, Expression value)
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

      var block = new PredicateBuilderBlock();
      block.AddVariableDeclaration(varName, value);
      blocks.Insert(0, block);

      return AH.MakeNameSegment(varName, value.Type);
    }

    public void AddConjunct(Expression conjunct)
    {
      blocks[0].AddConjunct(conjunct);
    }

    public Expression Extract()
    {
      if (!valid) {
        Debug.Assert(false);
        return null;
      }

      Expression e = null;
      foreach (var block in blocks) {
        e = block.Extract(e);
      }

      return e ?? AH.MakeTrue();
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

  public class MapBuilder {
    private string mapName;
    private List<string> variableLets;
    private int count;

    public MapBuilder(string i_mapName = "m", string initMap = "map[]") {
      mapName = i_mapName;
      count = 0;
      variableLets = new List<string>();
      variableLets.Add($"var {mapName}0 := {initMap}");
    }

    public void Add(string keySet, string value)
    {
      count++;
      variableLets.Add($"var {mapName}{count} := AddSetToMap({mapName}{count - 1}, ({keySet}), ({value}))");
    }

    public string Extract()
    {
      return string.Join(";", variableLets) + $"; m{count}";
    }
  }
}
