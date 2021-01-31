using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada
{
  public class ProofFile
  {
    private string dirName;
    private string auxName;
    private ModuleDefinition module;
    private List<MemberDecl> newDefaultClassDecls;
    private bool includeImportedFiles;

    public ProofFile(ModuleDefinition i_module, string i_dirName, bool i_includeImportedFiles = true)
    {
      dirName = i_dirName;
      auxName = null;
      module = i_module;
      includeImportedFiles = i_includeImportedFiles;
      Initialize();
    }

    public ProofFile(string i_dirName, string i_auxName, bool i_includeImportedFiles)
    {
      dirName = i_dirName;
      auxName = i_auxName;
      module = new ModuleDefinition(Token.NoToken, // tok
                                    ModuleName, // name
                                    new List<Microsoft.Boogie.IToken>(), // prefixIds
                                    false, // isAbstract
                                    false, // isProtected
                                    false, // isFacade
                                    Token.NoToken, // refinementBase
                                    null, // parent
                                    null, // attributes
                                    false, // isBuiltinName
                                    ArmadaModuleType.ArmadaProof, // moduleType
                                    null, // structsModuleType
                                    null, // abstracts
                                    null, // reduces
                                    null); // parser
      includeImportedFiles = i_includeImportedFiles;
      Initialize();
    }

    public string PathName
    {
      get { return (auxName == null) ? $"{dirName}.dfy" : $"{dirName}/{auxName}.dfy"; }
    }

    public string ModuleName
    {
      get { return $"ArmadaModule_{auxName}"; }
    }

    public string AuxName
    {
      get { return auxName; }
    }

    public bool IncludeImportedFiles
    {
      get { return includeImportedFiles; }
    }

    private void Initialize()
    {
      newDefaultClassDecls = new List<MemberDecl>();

      module.ArmadaTranslation =
        new ModuleDefinition(Token.NoToken, module.Name, new List<Microsoft.Boogie.IToken>(), false, false, false, null, module.Module, null, false);
      module.ArmadaIncludes = new List<string>();

      AddImport("ArmadaCommonDefinitions");
      AddImport("GeneralRefinementModule");

      AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/ArmadaCommonDefinitions.dfy");
      AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/spec/refinement.s.dfy");
    }

    private void Flush()
    {
      var c = new DefaultClassDecl(module.ArmadaTranslation, newDefaultClassDecls);
      AddTopLevelDecl(c);
    }

    public void Print(Program prog)
    {
      Flush();

      var pathName = ArmadaOptions.O.ArmadaOutputDir + "/" + this.PathName;
      Console.Out.WriteLine($"Printing proof to {pathName}");
      var tw = new System.IO.StreamWriter(pathName);
      var pr = new Printer(tw, ArmadaOptions.O.PrintMode);
      var fileBeingPrinted = Path.GetFullPath(prog.FullName);
      VisibilityScope scope = null;
      foreach (var includePath in module.ArmadaIncludes) {
        pr.PrintInclude(includePath);
      }
      pr.PrintModuleDefinition(module.ArmadaTranslation, scope, 0, new List<Microsoft.Boogie.IToken>(), fileBeingPrinted);
      tw.Flush();
    }

    public ModuleDefinition Module { get { return module; } }

    public void AddInclude (string s)
    {
      if (Path.IsPathRooted(s) || auxName == null)
      {
        module.ArmadaIncludes.Add(s);
      }
      else
      {
        module.ArmadaIncludes.Add("../" + s);
      }
    }

    public void AddInclude(ImportFileArmadaProofDecl ifd)
    {
      if (!ifd.UsedFiles.Contains(this.PathName)) {
        AddInclude(ifd.IncludePath);
      }
    }

    public void AddImport(string moduleName, string aliasName = null)
    {
      TopLevelDecl d;
      if (aliasName == null) {
        d = AH.MakeAliasModuleDecl(moduleName, module.ArmadaTranslation, true);
      }
      else {
        d = AH.MakeAliasModuleDecl(aliasName, moduleName, module.ArmadaTranslation, false);
      }
      AddTopLevelDecl(d);
    }

    public void AddImport(ImportModuleArmadaProofDecl imd)
    {
      if (!imd.UsedModules.Contains(this.ModuleName)) {
        AddImport(imd.IncludeModule);
      }
    }

    public void AddIncludeImport(string includeFile, string moduleName, string aliasName = null)
    {
      AddInclude(includeFile);
      AddImport(moduleName, aliasName);
    }

    public void IncludeAndImportGeneratedFile(string importedAuxName)
    {
      AddInclude($"{dirName}/{importedAuxName}.dfy");
      AddImport($"ArmadaModule_{importedAuxName}");
    }

    public void AddTopLevelDecl(TopLevelDecl d)
    {
      module.ArmadaTranslation.TopLevelDecls.Add(d);
    }

    public void AddDefaultClassDecl(MemberDecl d)
    {
      newDefaultClassDecls.Add(d);
    }

  }
  
  public class ProofFileCollection
  {
    private Program prog;
    private string name;
    private ProofFile mainProof;
    private Dictionary<string, ProofFile> auxiliaryProofs;
    private AbstractProofGenerator pg;

    public ProofFileCollection(Program i_prog, ModuleDefinition i_mainProof)
    {
      prog = i_prog;
      name = i_mainProof.Name;
      mainProof = new ProofFile(i_mainProof, name, true);
      auxiliaryProofs = new Dictionary<string, ProofFile>();
      pg = null;

      var dirName = $"{ArmadaOptions.O.ArmadaOutputDir}/{name}";
      if (!Directory.Exists(dirName))
      {
        Directory.CreateDirectory(dirName);
      }
    }

    public void Print()
    {
      mainProof.Print(prog);
      foreach (var proof in auxiliaryProofs.Values)
      {
        proof.Print(prog);
      }
    }

    public void AssociateProofGenerator(AbstractProofGenerator i_pg)
    {
      pg = i_pg;

      pg.AddCommonHeaderElements(mainProof);
      foreach (var proof in auxiliaryProofs.Values)
      {
        pg.AddCommonHeaderElements(proof);
      }
    }

    public ProofFile MainProof { get { return mainProof; } }

    public ProofFile AuxiliaryProof(string auxName)
    {
      return auxiliaryProofs[auxName];
    }

    public ProofFile CreateAuxiliaryProofFile(string auxName, bool includeImportedFiles = true)
    {
      if (auxiliaryProofs.ContainsKey(auxName)) {
        AH.PrintError(prog, Token.NoToken, $"Attempt to create an auxiliary proof file with an already-existing name ({auxName})");
        return null;
      }

      var proof = new ProofFile(name, auxName, includeImportedFiles);
      if (pg != null) {
        pg.AddCommonHeaderElements(proof);
      }
      auxiliaryProofs[auxName] = proof;
      return proof;
    }

    public ProofFile LookupFile(string auxName)
    {
      return (auxName == null) ? mainProof : auxiliaryProofs[auxName];
    }

    public void AddInclude(string path, string auxName = null)
    {
      LookupFile(auxName).AddInclude(path);
    }
    
    public void IncludeAndImportGeneratedFile(string importedAuxName, string auxName = null)
    {
      LookupFile(auxName).IncludeAndImportGeneratedFile(importedAuxName);
    }

    public void AddImport(string moduleName, string aliasName = null, string auxName = null)
    {
      LookupFile(auxName).AddImport(moduleName, aliasName);
    }

    public void AddTopLevelDecl(TopLevelDecl d, string auxName = null)
    {
      LookupFile(auxName).AddTopLevelDecl(d);
    }

    public void AddDefaultClassDecl(MemberDecl d, string auxName = null)
    {
      LookupFile(auxName).AddDefaultClassDecl(d);
    }
  }
}
