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
    private List<string> variableValues;
    private Dictionary<string, int> variableUseCount;
    private string body;

    public ExpressionBuilder(Program i_prog)
    {
      prog = i_prog;
      valid = true;
      variableNames = new List<string>();
      variableValues = new List<string>();
      variableUseCount = new Dictionary<string, int>();
      body = null;
    }

    public bool Valid { get { return valid; } }

    public string ReserveVariableName(string varName)
    {
      if (variableUseCount.ContainsKey(varName)) {
        AH.PrintError(prog, $"Internal error:  Attempt to reserve variable name that's already in use ({varName}).");
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

      return varName;
    }

    public void SetBody(string e)
    {
      body = e;
    }

    public string Extract()
    {
      if (body == null) {
        Fail("Internal error:  Attempt to extract before body is set");
      }

      if (!valid) {
        return null;
      }

      return String.Concat(Enumerable.Range(0, variableNames.Count).Select(i => $"var {variableNames[i]} := {variableValues[i]};\n"))
             + body;
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
