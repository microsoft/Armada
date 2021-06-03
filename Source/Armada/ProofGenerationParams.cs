using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada
{
  public class ProofGenerationParams
  {
    public ProofGenerationParams(Program i_prog, ModuleDefinition i_mProof, LiteralModuleDecl i_mLow, LiteralModuleDecl i_mHigh)
    {
      prog = i_prog;
      proofFiles = new ProofFileCollection(i_prog, i_mProof);
      mLow = i_mLow;
      mHigh = i_mHigh;
      symbolsLow = mLow.ModuleDef.ArmadaSymbols;
      symbolsHigh = mHigh.ModuleDef.ArmadaSymbols;
      originalsLow = symbolsLow.DefaultClass;
      originalsHigh = symbolsHigh.DefaultClass;
      extraMaterial = new Dictionary<string, string>();
      opaqueUserDefs = new List<string>();
    }

    public readonly Program prog;
    public ProofFileCollection proofFiles;
    public readonly LiteralModuleDecl mLow, mHigh;
    public readonly ClassDecl originalsLow, originalsHigh;
    public readonly ArmadaSymbolTable symbolsLow, symbolsHigh;
    private Dictionary<string, string> extraMaterial;
    private List<string> opaqueUserDefs;

    public ProofFile MainProof { get { return proofFiles.MainProof; } }
    public ProofFile AuxiliaryProof(string auxName) { return proofFiles.AuxiliaryProof(auxName); }

    public void AddExtraMaterial(string name, string contents)
    {
      if (extraMaterial.ContainsKey(name)) {
        extraMaterial[name] += "\n" + contents;
      }
      else {
        extraMaterial[name] = contents;
      }
    }

    private string InsertExtraMaterial(string name, string contents, int minPos = 0)
    {
      // Remove any "ProofCustomizationGoesHere();" and replace it
      // with the extra material.  The extra material is whatever is
      // specified by the user or, if nothing is specified by them,
      // revelations of all user-defined opaque definitions.

      int insertionPos = contents.IndexOf("ProofCustomizationGoesHere();", minPos);
      if (insertionPos >= 0) {
        string extra = extraMaterial.ContainsKey(name) ? extraMaterial[name] + "\n"
                                                       : String.Concat(opaqueUserDefs.Select(f => $"reveal {f}();\n"));
        return contents.Substring(0, insertionPos) + extra + contents.Substring(insertionPos + 29);
      }

      // If there is no "ProofCustomizationGoesHere();", but the user
      // has provided extra material, put it after the first left
      // brace + newline.  (Don't put it after a left brace not
      // immediately followed by a newline because that might be
      // followed by a colon indicating an attribute.)

      if (extraMaterial.ContainsKey(name)) {
        var bracePos = contents.IndexOf("{\n");
        if (bracePos >= 0) {
          return contents.Substring(0, bracePos + 2) + extraMaterial[name] + contents.Substring(bracePos + 2);
        }
      }

      return contents;
    }

    public void AddOpaqueUserDef(string fnName)
    {
      opaqueUserDefs.Add(fnName);
    }

    public void AddDefaultClassDecl(MemberDecl d, string auxName = null)
    {
      proofFiles.AddDefaultClassDecl(d, auxName);
    }

    public void AddTopLevelDecl(TopLevelDecl d, string auxName = null)
    {
      proofFiles.AddTopLevelDecl(d, auxName);
    }

    public void AddLemma(string contents, string auxName = null)
    {
      Match match = Regex.Match(contents, @"^\s*lemma\s+({[^}]*}\s*)*([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[2].Value;
        int pos = match.Groups[2].Index;
        string expandedContents = InsertExtraMaterial(name, contents, pos);
        AddDefaultClassDecl((Lemma)AH.ParseTopLevelDecl(prog, name, expandedContents), auxName);
      }
      else {
        AH.PrintError(prog, $"Could not find lemma name in {contents}");
      }
    }

    public void AddFunction(string contents, string auxName = null)
    {
      Match match = Regex.Match(contents, @"^\s*function\s+([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddDefaultClassDecl((Function)AH.ParseTopLevelDecl(prog, name, contents), auxName);
      }
      else {
        AH.PrintError(prog, $"Could not find function name in {contents}");
      }
    }

    public void AddPredicate(string contents, string auxName = null)
    {
      Match match = Regex.Match(contents, @"^\s*predicate\s+([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(prog, name, contents), auxName);
      }
      else {
        AH.PrintError(prog, $"Could not find predicate name in {contents}");
        return;
      }
    }

    public void AddDatatype(string contents, string auxName = null)
    {
      Match match = Regex.Match(contents, @"^\s*datatype\s+([^\s<(=]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddTopLevelDecl((DatatypeDecl)AH.ParseTopLevelDecl(prog, name, contents), auxName);
      }
      else
      {
        AH.PrintError(prog, $"Could not find datatype name in {contents}");
      }
    }

    public void AddTypeSynonym(string contents, string auxName = null)
    {
      Match match = Regex.Match(contents, @"^\s*type\s+([^\s<(=]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddTopLevelDecl((TypeSynonymDecl)AH.ParseTopLevelDecl(prog, name, contents), auxName);
      }
      else
      {
        AH.PrintError(prog, $"Could not find type synonym name in {contents}");
      }
    }

    public void AddInclude(string fileName, string auxName = null)
    {
      proofFiles.AddInclude(fileName, auxName);
    }

    public void AddImport(string moduleName, string aliasName = null, string auxName = null)
    {
      proofFiles.AddImport(moduleName, aliasName, auxName);
    }
  }
}
