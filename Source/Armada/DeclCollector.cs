using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using static Microsoft.Armada.Predicate;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada
{

  public class DeclCollector
  {
    private Program prog;
    private List<TopLevelDecl> newTopLevelDecls;
    private List<MemberDecl> newDefaultClassDecls;

    public DeclCollector(Program i_prog)
    {
      prog = i_prog;
      newTopLevelDecls = new List<TopLevelDecl>();
      newDefaultClassDecls = new List<MemberDecl>();
    }

    public List<TopLevelDecl> NewTopLevelDecls { get { return newTopLevelDecls; } }
    public List<MemberDecl> NewDefaultClassDecls { get { return newDefaultClassDecls; } }

    public void AddTopLevelDecl(TopLevelDecl d)
    {
      newTopLevelDecls.Add(d);
    }

    public void AddDefaultClassDecl(MemberDecl d)
    {
      newDefaultClassDecls.Add(d);
    }

    public void CopyMathematicalDefaultClassMembers(ClassDecl defaultClass)
    {
      foreach (var m in defaultClass.Members) {
        if (m is Function || m is Lemma && ! m.Name.StartsWith("reveal_")) { // fix for duplicate export of opaque functions
          AddDefaultClassDecl(m);
        }
      }
    }

    public void CopyMathematicalTopLevelDecls(ModuleDefinition m)
    {
      foreach (var d in m.TopLevelDecls) {
        if (d is DatatypeDecl || d is NewtypeDecl || d is TypeSynonymDecl || d is AliasModuleDecl) {
          AddTopLevelDecl(d);
        }
      }
    }

    public void AddItem(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*((lemma)|(function)|(predicate)|(datatype)|(type))\s+");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        if (name == "lemma") {
          AddLemma(contents);
        }
        else if (name == "function") {
          AddFunction(contents);
        }
        else if (name == "predicate") {
          AddPredicate(contents);
        }
        else if (name == "datatype") {
          AddDatatype(contents);
        }
        else if (name == "type") {
          AddTypeSynonym(contents);
        }
        else {
          AH.PrintError(prog, "Can't add an item that doesn't start with lemma, function, predicate, datatype, or type");
        }
      }
      else
      {
        AH.PrintError(prog, "Can't add an item that doesn't start with lemma, function, predicate, datatype, or type");
      }
    }

    public void AddLemma(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*lemma\s+({[^}]*}\s*)*([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[2].Value;
        AddDefaultClassDecl((Lemma)AH.ParseTopLevelDecl(prog, name, contents));
      }
      else {
        AH.PrintError(prog, $"Could not find lemma name in {contents}");
      }
    }

    public void AddFunction(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*function\s+({[^}]*}\s*)*([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[2].Value;
        AddDefaultClassDecl((Function)AH.ParseTopLevelDecl(prog, name, contents));
      }
      else {
        AH.PrintError(prog, $"Could not find function name in {contents}");
      }
    }

    public void AddPredicate(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*predicate\s+({[^}]*}\s*)*([^\s<(]+)");
      if (match.Success)
      {
        string name = match.Groups[2].Value;
        AddDefaultClassDecl((Predicate)AH.ParseTopLevelDecl(prog, name, contents));
      }
      else {
        AH.PrintError(prog, $"Could not find predicate name in {contents}");
        return;
      }
    }

    public void AddDatatype(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*datatype\s+([^\s<(=]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddTopLevelDecl((DatatypeDecl)AH.ParseTopLevelDecl(prog, name, contents));
      }
      else
      {
        AH.PrintError(prog, $"Could not find datatype name in {contents}");
      }
    }

    public void AddTypeSynonym(string contents)
    {
      Match match = Regex.Match(contents, @"^\s*type\s+([^\s<(=]+)");
      if (match.Success)
      {
        string name = match.Groups[1].Value;
        AddTopLevelDecl((TypeSynonymDecl)AH.ParseTopLevelDecl(prog, name, contents));
      }
      else
      {
        AH.PrintError(prog, $"Could not find type synonym name in {contents}");
      }
    }

  }

}
