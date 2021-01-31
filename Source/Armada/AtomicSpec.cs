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
  ///////////////////////////////////////////////////////////////////////
  // PC TYPE
  ///////////////////////////////////////////////////////////////////////

  public enum PCAtomicType { Yielding, Recurrent, Nonyielding, Stopping };

  public class PCAtomicTypePair : Tuple<PCAtomicType, PCAtomicType>
  {
    public PCAtomicTypePair(PCAtomicType i_Item1, PCAtomicType i_Item2) : base(i_Item1, i_Item2)
    {
    }

    public override string ToString()
    {
      return Item1.ToString().Substring(0, 1) + Item2.ToString().Substring(0, 1);
    }
  }

  ///////////////////////////////////////////////////////////////////////
  // ATOMIC PATH PREFIX
  ///////////////////////////////////////////////////////////////////////

  public class AtomicPathPrefix
  {
    private AtomicSpec atomicSpec;
    private List<NextRoutine> nextRoutines;
    private bool tau;
    private ArmadaPC startPC;
    private ArmadaPC endPC;
    private PCAtomicType startType;
    private PCAtomicType endType;
    private string name;
    private List<AtomicPathPrefix> extensions;
    private AtomicPath path;

    public AtomicPathPrefix(AtomicSpec i_atomicSpec, List<NextRoutine> i_nextRoutines, bool i_tau, AtomicPathPrefix parent)
    {
      atomicSpec = i_atomicSpec;
      nextRoutines = new List<NextRoutine>(i_nextRoutines);
      tau = i_tau;
      startPC = nextRoutines[0].startPC;
      endPC = nextRoutines[nextRoutines.Count - 1].endPC;
      startType = atomicSpec.GetPCAtomicType(startPC);
      endType = nextRoutines[nextRoutines.Count - 1].Stopping ? PCAtomicType.Stopping : atomicSpec.GetPCAtomicType(endPC);
      extensions = new List<AtomicPathPrefix>();
      path = null;

      if (parent != null) {
        parent.AddExtension(this);
      }

      if (tau) {
        name = "Tau";
      }
      else {
        name = UndefinedBehavior ? "UB_" : "";
        name += $"From_{startPC.methodName}_{startPC.Name}";

        // It's possible for two atomic paths to have the same start
        // and end PCs.  But, every path has to have a distinct name,
        // so we sometimes have to name a path with more than just the
        // start and end PCs.
        //
        // One way for two atomic paths with the same start and end
        // PCs to differ is via returning to different PCs.  For
        // instance, consider the following code:
        //
        //   method {:atomic} A {
        //     S1;
        //   label L:
        //     S2;
        //   }
        //   
        //   method B {
        //     atomic {
        //       A();
        //       A();
        //       A();
        //     }
        //   }
        //
        // Here, there are two ways to get from label L to label L:
        // (1) by returning from B's first call to A and then making
        // B's second call to A, and (2) by returning from B's second
        // call to A and then making B's third call to A.  So, to make
        // sure such paths have different names, we include in the
        // name every returned-to PC in a step other than the last one
        // in the path.
        //
        // Another way for two atomic paths with the same start and
        // end PCs to differ is via branch outcomes.  For instance,
        // consider the following code:
        //
        //   atomic {
        //     if P {
        //       S1;
        //     }
        //     S2;
        //   }
        //
        // Here, there are two ways to get from the beginning to the
        // end: via the true branch of the if (passing through
        // statement S1) or via the false branch.  So we distinguish
        // the names of such paths by the branch outcomes.

        bool justBranched = false;
        for (var i = 0; i < nextRoutines.Count; ++i)
        {
          var nextRoutine = nextRoutines[i];
          if (i < nextRoutines.Count - 1 && nextRoutine.nextType == NextType.Return) {
            var returnToPC = nextRoutine.endPC;
            name += $"_Via_{returnToPC.methodName}_{returnToPC.Name}";
            justBranched = false;
          }

          bool branchOutcome;
          if (nextRoutine.TryGetBranchOutcome(out branchOutcome)) {
            if (!justBranched) {
              name += "_";
            }
            name += (branchOutcome ? "T" : "F");
            justBranched = true;
          }
        }

        if (endPC == null)
        {
          name += "_to_exit";
        }
        else
        {
          name += $"_To_{endPC.methodName}_{endPC.Name}";
        }
      }
    }

    public AtomicPathPrefix(AtomicSpec i_atomicSpec, ArmadaPC pc)
    {
      atomicSpec = i_atomicSpec;
      nextRoutines = new List<NextRoutine>();
      tau = false;
      startPC = endPC = pc;
      startType = endType = atomicSpec.GetPCAtomicType(pc);
      extensions = new List<AtomicPathPrefix>();
      path = null;
    }

    public bool Tau { get { return tau; } }
    public ArmadaPC StartPC { get { return startPC; } }
    public ArmadaPC EndPC { get { return endPC; } }
    public PCAtomicType StartType { get { return startType; } }
    public PCAtomicType EndType { get { return endType; } }
    public List<NextRoutine> NextRoutines { get { return nextRoutines; } }
    public NextRoutine LastNextRoutine { get { return nextRoutines[nextRoutines.Count - 1]; } }
    public int NumNextRoutines { get { return nextRoutines.Count; } }
    public string Name { get { return name; } }
    public AtomicSpec Spec { get { return atomicSpec; } }

    public void AddExtension(AtomicPathPrefix other) { extensions.Add(other); }
    public List<AtomicPathPrefix> Extensions { get { return extensions; } }
    public AtomicPath PathVal { get { return path; } set { path = value; } }

    public bool UndefinedBehavior { get { return (nextRoutines.Count == 0) ? false : LastNextRoutine.UndefinedBehavior; } }
    public bool Stopping { get { return (nextRoutines.Count == 0) ? false : LastNextRoutine.Stopping; } }

    public List<ArmadaPC> GetPCs()
    {
      var pcs = new List<ArmadaPC>{ startPC };
      pcs.AddRange(nextRoutines.Select(p => p.endPC));
      return pcs;
    }

    public List<NextRoutine> MapNextRoutines(Dictionary<NextRoutine, NextRoutine> nextRoutineMap)
    {
      return nextRoutines.Where(n => nextRoutineMap.ContainsKey(n)).Select(n => nextRoutineMap[n]).ToList();
    }

    public List<ArmadaPC> GetMappedPCs(Dictionary<ArmadaPC, ArmadaPC> pcMap)
    {
      return GetPCs().Where(pc => pcMap.ContainsKey(pc)).Select(pc => pcMap[pc]).ToList();
    }
  }

  ///////////////////////////////////////////////////////////////////////
  // ATOMIC PATH
  ///////////////////////////////////////////////////////////////////////

  public class AtomicPath
  {
    private AtomicPathPrefix pathPrefix;
    private bool stopping;
    private string name;

    public AtomicPath(AtomicPathPrefix i_pathPrefix)
    {
      pathPrefix = i_pathPrefix;
      stopping = i_pathPrefix.Stopping;
      name = pathPrefix.Name;
    }

    public bool Tau { get { return pathPrefix.Tau; } }
    public string Name { get { return name;  } }
    public ArmadaPC StartPC { get { return pathPrefix.StartPC; } }
    public ArmadaPC EndPC { get { return pathPrefix.EndPC; } }
    public PCAtomicType StartType { get { return pathPrefix.StartType; } }
    public PCAtomicType EndType { get { return pathPrefix.EndType; } }
    public bool Stopping { get { return stopping; } }

    public string PathType {
      get {
        if (Tau) { return "Tau"; }
        string s1 = StartType.ToString().Substring(0, 1);
        string s2 = stopping ? "S" : EndType.ToString().Substring(0, 1);
        return s1 + s2;
      }
    }
    public List<NextRoutine> NextRoutines { get { return pathPrefix.NextRoutines; } }
    public NextRoutine LastNextRoutine { get { return pathPrefix.LastNextRoutine; } }
    public int NumNextRoutines { get { return pathPrefix.NumNextRoutines; } }

    public IEnumerable<Tuple<NextRoutine, int>> NextRoutinesWithIndices
    {
      get
      {
        var i = 0;
        while (i < pathPrefix.NumNextRoutines) {
          yield return new Tuple<NextRoutine, int>(pathPrefix.NextRoutines[i], i);
          ++i;
        }
      }
    }

    public IEnumerable<Tuple<NextRoutine, int>> NextRoutinesWithFormalsWithIndices
    {
      get
      {
        var i = 0;
        while (i < pathPrefix.NumNextRoutines) {
          var nextRoutine = pathPrefix.NextRoutines[i];
          if (nextRoutine.HasFormals) {
            yield return new Tuple<NextRoutine, int>(pathPrefix.NextRoutines[i], i);
          }
          ++i;
        }
      }
    }

    public string OptionalNotForOK { get { return stopping ? "!" : ""; } }

    public List<ArmadaPC> GetPCs() { return pathPrefix.GetPCs(); }

    public bool Mappable(Dictionary<NextRoutine, NextRoutine> nextRoutineMap, bool i_stopping, bool avoidFinalUnmappedStoppingStep)
    {
      if (Tau) {
        return true;
      }
      if (stopping != i_stopping) {
        return false;
      }
      if (!NextRoutines.Where(n => nextRoutineMap.ContainsKey(n)).Any()) {
        return false;
      }
      if (avoidFinalUnmappedStoppingStep && stopping && !nextRoutineMap.ContainsKey(LastNextRoutine)) {
        return false;
      }
      return true;
    }

    public List<NextRoutine> MapNextRoutines(Dictionary<NextRoutine, NextRoutine> nextRoutineMap)
    {
      return pathPrefix.MapNextRoutines(nextRoutineMap);
    }

    public List<ArmadaPC> GetMappedPCs(Dictionary<ArmadaPC, ArmadaPC> pcMap)
    {
      return pathPrefix.GetMappedPCs(pcMap);
    }

    public IEnumerable<bool> BranchOutcomes
    {
      get
      {
        foreach (var nextRoutine in NextRoutines)
        {
          bool outcome;
          if (nextRoutine.TryGetBranchOutcome(out outcome))
          {
            yield return outcome;
          }
        }
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////
  // ATOMIC SPEC
  ///////////////////////////////////////////////////////////////////////

  public class AtomicSpec
  {
    private ProofGenerationParams pgp;
    private ArmadaSymbolTable symbols;
    private string auxName;
    private string prefix;
    private bool low;
    private string moduleName;
    private string typeState;
    private string specFunctions;
    private string spec;
    private string validStep;
    private string getNextState;
    private List<ArmadaPC> allPCs;
    private Dictionary<ArmadaPC, List<NextRoutine>> pcToNextRoutines;
    private HashSet<ArmadaPC> nonyieldingPCs;
    private HashSet<ArmadaPC> recurrentPCs;
    private List<AtomicPath> atomicPaths;
    private AtomicPath tauPath;
    private Dictionary<ArmadaPC, List<AtomicPathPrefix>> rootPathPrefixesByPC;

    public AtomicSpec(ProofGenerationParams i_pgp, ArmadaSymbolTable i_symbols, string i_auxName, string i_prefix, bool i_low,
                      string i_moduleName, string i_typeState, string i_specFunctions, string i_spec,
                      string i_validStep, string i_getNextState)
    {
      pgp = i_pgp;
      symbols = i_symbols;
      auxName = i_auxName;
      prefix = i_prefix;
      low = i_low;
      moduleName = i_moduleName;
      typeState = i_typeState;
      specFunctions = i_specFunctions;
      spec = i_spec;
      validStep = i_validStep;
      getNextState = i_getNextState;
    }

    public AtomicPath TauPath { get { return tauPath; } }
    public string Prefix { get { return prefix; } }
    public string TypeState { get { return typeState; } }
    public List<AtomicPath> AtomicPaths { get { return atomicPaths; } }
    public string ModuleName { get { return moduleName; } }
    public IEnumerable<ArmadaPC> AllPCs { get { return allPCs; } }
    public IEnumerable<AtomicPathPrefix> RootPathPrefixesByPC(ArmadaPC pc) { return rootPathPrefixesByPC[pc]; }
    public HashSet<ArmadaPC> RecurrentPCs { get { return recurrentPCs; } }
    public bool Low { get { return low; } }

    public void MakeSpec(HashSet<ArmadaPC> extraRecurrentPCs = null)
    {
      AddIncludesAndImports();
      DetermineNonyieldingPCs();
      DeterminePCToNextRoutinesMap();
      DetermineRecurrentPCs(extraRecurrentPCs);
      DetermineAtomicPaths();
      CreateAtomicSpec();
    }

    private void AddIncludesAndImports()
    {
      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", auxName);
      pgp.AddImport("util_option_s", null, auxName);
      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy", auxName);
      pgp.AddImport("util_collections_seqs_s", null, auxName);
      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy", auxName);
      pgp.AddImport("GenericArmadaLemmasModule", null, auxName);
      pgp.AddImport("GenericArmadaSpecModule", null, auxName);
      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaAtomic.i.dfy", auxName);
      pgp.AddImport("GenericArmadaAtomicModule", null, auxName);
    }

    public string GetConstructorString(AtomicPath atomicPath)
    {
      if (atomicPath.NextRoutines.Where(r => r.HasFormals).Any()) {
        // TODO: this does not work with introduced statements with *
        AH.PrintError(pgp.prog, "Armada currently doesn't support introducing a non-deterministic statement.");
      }

      var str = $"{prefix}_Path_{atomicPath.Name}({prefix}_PathSteps_{atomicPath.Name}(";
      str += String.Join(", ", atomicPath.NextRoutines.Select(r => $"{moduleName}.Armada_Step_{r.NameSuffix}()"));
      str += "))";
      return str;
    }

    ///////////////////////////////////////////////////////////////////////
    // COLLECTING INFO
    ///////////////////////////////////////////////////////////////////////

    private void DetermineNonyieldingPCs()
    {
      var pcs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllNonyieldingPCs(pcs);
      nonyieldingPCs = new HashSet<ArmadaPC>(pcs);
    }

    private void DeterminePCToNextRoutinesMap()
    {
      pcToNextRoutines = new Dictionary<ArmadaPC, List<NextRoutine>>();
      foreach (var nextRoutine in symbols.NextRoutines) {
        var pc = nextRoutine.startPC;
        if (pc == null) {
          continue;
        }
        if (!pcToNextRoutines.ContainsKey(pc)) {
          pcToNextRoutines[pc] = new List<NextRoutine>();
        }
        pcToNextRoutines[pc].Add(nextRoutine);
      }
    }

    ///////////////////////////////////////////////////////////////////////
    // FINDING RECURRENT PCS
    ///////////////////////////////////////////////////////////////////////

    /// <summary>
    /// In CheckForFiniteNonyieldingPathBetween, we only care about
    /// paths that reach end before visiting any other node twice
    /// (since if it visits another node twice, it's potentially
    /// infinite).  So, we keep track of nodes we've already visited
    /// and don't visit them again.
    /// </summary>

    private bool CheckForFiniteNonyieldingPathBetween(ArmadaPC start, ArmadaPC end, HashSet<ArmadaPC> alreadyVisited)
    {
      if (start == null || end == null) {
        return false;
      }
      if (!nonyieldingPCs.Contains(start)) {
        return false;
      }
      List<NextRoutine> nextRoutines;
      if (!pcToNextRoutines.TryGetValue(start, out nextRoutines)) {
        return false;
      }
      foreach (var nextRoutine in nextRoutines) {
        var nextPC = nextRoutine.endPC;
        if (nextPC.Equals(end)) {
          return true;
        }
        if (alreadyVisited.Contains(nextPC)) {
          continue;
        }
        alreadyVisited.Add(nextPC);
        if (CheckForFiniteNonyieldingPathBetween(nextPC, end, alreadyVisited)) {
          return true;
        }
        alreadyVisited.Remove(nextPC);
      }
      return false;
    }

    private bool DoesNonyieldingPathBetweenPCsExist(ArmadaPC start, ArmadaPC end)
    {
      var alreadyVisited = new HashSet<ArmadaPC>();
      return CheckForFiniteNonyieldingPathBetween(start, end, alreadyVisited);
    }

    private void DetermineRecurrentPCs(HashSet<ArmadaPC> extraRecurrentPCs)
    {
      if (extraRecurrentPCs != null) {
        recurrentPCs = new HashSet<ArmadaPC>(extraRecurrentPCs);
      }
      else {
        recurrentPCs = new HashSet<ArmadaPC>();
      }

      foreach (var pc in symbols.EnumeratePotentialRecurrentPCs())
      {
        if (!recurrentPCs.Contains(pc) && DoesNonyieldingPathBetweenPCsExist(pc, pc)) {
          recurrentPCs.Add(pc);
        }
      }
    }

    ///////////////////////////////////////////////////////////////////////
    // PC TYPES
    ///////////////////////////////////////////////////////////////////////

    public PCAtomicType GetPCAtomicType(ArmadaPC pc)
    {
      if (pc == null) {
        return PCAtomicType.Yielding;
      }
      if (recurrentPCs.Contains(pc)) {
        return PCAtomicType.Recurrent;
      }
      if (nonyieldingPCs.Contains(pc)) {
        return PCAtomicType.Nonyielding;
      }
      else {
        return PCAtomicType.Yielding;
      }
    }

    ///////////////////////////////////////////////////////////////////////
    // MAKING ATOMIC STEPS
    ///////////////////////////////////////////////////////////////////////

    private void DetermineAtomicPaths()
    {
      allPCs = new List<ArmadaPC>();
      symbols.AllMethods.AppendAllPCs(allPCs);

      var tauPathPrefix = new AtomicPathPrefix(this, new List<NextRoutine> { symbols.TauNextRoutine }, true, null);
      tauPath = new AtomicPath(tauPathPrefix);
      atomicPaths = new List<AtomicPath>{ tauPath };
      rootPathPrefixesByPC = new Dictionary<ArmadaPC, List<AtomicPathPrefix>>();

      foreach (var startPC in allPCs)
      {
        rootPathPrefixesByPC[startPC] = new List<AtomicPathPrefix>();
        if (GetPCAtomicType(startPC) != PCAtomicType.Nonyielding) {
          List<NextRoutine> nextRoutines;
          if (pcToNextRoutines.TryGetValue(startPC, out nextRoutines)) {
            foreach (var nextRoutine in nextRoutines)
            {
              var rootAtomicPathPrefix = new AtomicPathPrefix(this, new List<NextRoutine>{ nextRoutine }, false, null);
              rootPathPrefixesByPC[startPC].Add(rootAtomicPathPrefix);
              PopulateAtomicPathPrefix(rootAtomicPathPrefix);
            }
          }
        }
      }
    }

    private void PopulateAtomicPathPrefix(AtomicPathPrefix pathPrefix)
    {
      var currentPC = pathPrefix.EndPC;
      if (pathPrefix.Stopping || currentPC == null || GetPCAtomicType(currentPC) != PCAtomicType.Nonyielding) {
        pathPrefix.PathVal = new AtomicPath(pathPrefix);
        atomicPaths.Add(pathPrefix.PathVal);
        return;
      }

      List<NextRoutine> subsequentRoutines;
      if (pcToNextRoutines.TryGetValue(currentPC, out subsequentRoutines)) {
        foreach (var subsequentRoutine in subsequentRoutines)
        {
          var childNextRoutines = new List<NextRoutine>(pathPrefix.NextRoutines);
          childNextRoutines.Add(subsequentRoutine);
          var childPathPrefix = new AtomicPathPrefix(this, childNextRoutines, false, pathPrefix);
          PopulateAtomicPathPrefix(childPathPrefix);
        }
      }
    }

    ///////////////////////////////////////////////////////////////////////
    // EMITTING DAFNY CODE
    ///////////////////////////////////////////////////////////////////////

    private void CreateAtomicSpec()
    {
      CreateIsRecurrentPC();
      CreatePathDatatype();
      CreatePathTypeFunction();
      CreatePathStatesDatatype();
      foreach (var atomicPath in atomicPaths)
      {
        CreateFunctionsForAtomicPath(atomicPath);
      }
      CreateAtomicSpecFunctions();
      CreateFunctionsForAllAtomicPaths();
    }

    ///////////////////////////////////////////////////////////////////////
    // PATH DEFINITIONS AND FUNCTIONS
    ///////////////////////////////////////////////////////////////////////

    private void CreateIsRecurrentPC()
    {
      var body = String.Join(" || ", recurrentPCs.Select(pc => $"pc.{pc}?"));
      if (body.Length == 0) { body = "false"; }
      string str = $@"
        predicate {prefix}_IsRecurrentPC(pc:{moduleName}.Armada_PC)
        {{
          {body}
        }}
      ";
      pgp.AddPredicate(str, auxName);
    }

    private void CreatePathDatatype()
    {
      string str;

      foreach (var atomicPath in atomicPaths)
      {
        str = $"datatype {prefix}_PathSteps_{atomicPath.Name} = {prefix}_PathSteps_{atomicPath.Name}(";
        str += String.Join(", ", Enumerable.Range(0, atomicPath.NumNextRoutines).Select(i => $"step{i}: {moduleName}.Armada_Step"));
        str += ")\n";
        pgp.AddDatatype(str, auxName);
      }

      str = $"datatype {prefix}_Path = ";
      str += String.Join(" | ", atomicPaths.Select(
        atomicPath => $"{prefix}_Path_{atomicPath.Name}(steps_{atomicPath.Name}: {prefix}_PathSteps_{atomicPath.Name})"
      ));
      pgp.AddDatatype(str, auxName);
    }

    private void CreatePathTypeFunction()
    {
      var caseBodies = String.Join("\n", atomicPaths.Select(
        atomicPath => $"case {prefix}_Path_{atomicPath.Name}(_) => AtomicPathType_{atomicPath.PathType}"
      ));
      var str = $@"
        function {prefix}_GetPathType(path: {prefix}_Path) : AtomicPathType
        {{
          match path
          {caseBodies}
        }}
      ";
      pgp.AddFunction(str, auxName);
    }

    private void CreatePathStatesDatatype()
    {
      string str;

      foreach (var atomicPath in atomicPaths)
      {
        str = $"datatype {prefix}_PathStates_{atomicPath.Name} = {prefix}_PathStates_{atomicPath.Name}(";
        str += String.Join(", ", Enumerable.Range(0, atomicPath.NumNextRoutines + 1).Select(i => $"s{i}: {typeState}"));
        str += ")";
        pgp.AddDatatype(str, auxName);
      }
    }

    private void CreateFunctionsForAtomicPath(AtomicPath atomicPath)
    {
      var nextRoutines = atomicPath.NextRoutines;
      string str;

      str = $@"
        function {prefix}_GetPathStates_{atomicPath.Name}(
          s0: {typeState},
          tid: Armada_ThreadHandle,
          steps: {prefix}_PathSteps_{atomicPath.Name}
          ) : {prefix}_PathStates_{atomicPath.Name}
        {{
      ";
      str += String.Concat(
        Enumerable.Range(0, nextRoutines.Count).Select(i => $"    var s{i + 1} := {getNextState}(s{i}, steps.step{i}, tid);\n")
      );
      str += $"    {prefix}_PathStates_{atomicPath.Name}(";
      str += String.Join(", ", Enumerable.Range(0, nextRoutines.Count + 1).Select(i => $"s{i}"));
      str += ") }";
      pgp.AddFunction(str, auxName);

      str = $@"
        predicate {prefix}_ValidPath_{atomicPath.Name}(
          s: {typeState},
          tid: Armada_ThreadHandle,
          steps: {prefix}_PathSteps_{atomicPath.Name}
          )
        {{
          var states := {prefix}_GetPathStates_{atomicPath.Name}(s, tid, steps);
      ";
      str += String.Concat(Enumerable.Range(0, nextRoutines.Count).Select(i => $@"
          && steps.step{i}.Armada_Step_{nextRoutines[i].NameSuffix}?
          && {validStep}(states.s{i}, steps.step{i}, tid)
      "));
      str += "}";
      pgp.AddPredicate(str, auxName);
    }

    private void CreateFunctionsForAllAtomicPaths()
    {
      var str = $@"
        predicate {{:opaque}} {prefix}_ValidPath(s: {typeState}, path: {prefix}_Path, tid: Armada_ThreadHandle)
        {{
          match path
      ";
      str += String.Concat(atomicPaths.Select(atomicPath =>
          $"case {prefix}_Path_{atomicPath.Name}(steps) => {prefix}_ValidPath_{atomicPath.Name}(s, tid, steps)\n"
      ));
      str += "}";
      pgp.AddPredicate(str, auxName);

      str = $@"
        function {{:opaque}} {prefix}_GetStateAfterPath(s: {typeState}, atomicPath: {prefix}_Path, tid: Armada_ThreadHandle) : {typeState}
        {{
          match atomicPath
      ";
      foreach (var atomicPath in atomicPaths) {
        str += $@"
            case {prefix}_Path_{atomicPath.Name}(steps) =>
              {prefix}_GetPathStates_{atomicPath.Name}(s, tid, steps).s{atomicPath.NumNextRoutines}
        ";
      }
      str += "}\n";
      pgp.AddFunction(str, auxName);

      str = $@"
        predicate {prefix}_NextPath(s: {typeState}, s': {typeState}, atomicPath: {prefix}_Path, tid: Armada_ThreadHandle)
        {{
          {prefix}_ValidPath(s, atomicPath, tid) && s' == {prefix}_GetStateAfterPath(s, atomicPath, tid)
        }}
      ";
      pgp.AddPredicate(str, auxName);

      foreach (var atomicPath in atomicPaths)
      {
        str = $@"
          lemma lemma_{prefix}_OpenPath_{atomicPath.Name}(
            s: {typeState},
            path: {prefix}_Path,
            tid: Armada_ThreadHandle
            ) returns (
            steps: {prefix}_PathSteps_{atomicPath.Name},
            states: {prefix}_PathStates_{atomicPath.Name}
            )
            requires path.{prefix}_Path_{atomicPath.Name}?
            ensures  path == {prefix}_Path_{atomicPath.Name}(steps)
            ensures  {prefix}_ValidPath(s, path, tid) == {prefix}_ValidPath_{atomicPath.Name}(s, tid, steps)
            ensures  states == {prefix}_GetPathStates_{atomicPath.Name}(s, tid, steps)
            ensures  {prefix}_GetStateAfterPath(s, path, tid) == states.s{atomicPath.NumNextRoutines}
          {{
            reveal {prefix}_ValidPath();
            reveal {prefix}_GetStateAfterPath();
            steps := path.steps_{atomicPath.Name};
            states := {prefix}_GetPathStates_{atomicPath.Name}(s, tid, steps);
          }}
        ";
        pgp.AddLemma(str, auxName);
      }
    }

    ///////////////////////////////////////////////////////////////////////
    // ATOMIC SPEC
    ///////////////////////////////////////////////////////////////////////

    private void CreateAtomicSpecFunctions()
    {
      var str = $@"
        function {prefix}_GetSpecFunctions() : AtomicSpecFunctions<{typeState}, {prefix}_Path, {moduleName}.Armada_PC>
        {{
          var lasf := {specFunctions};
          AtomicSpecFunctions(lasf.init, {prefix}_ValidPath, {prefix}_GetStateAfterPath, {prefix}_GetPathType,
                              lasf.state_ok, lasf.get_thread_pc, lasf.is_pc_nonyielding)
        }}
      ";
      pgp.AddFunction(str, auxName);
    }

    ///////////////////////////////////////////////////////////////////////
    // LEMMAS
    ///////////////////////////////////////////////////////////////////////

    public void GeneratePCEffectLemmas()
    {
      string str;
      var pr = new PathPrinter(this);
      foreach (var atomicPath in atomicPaths)
      {
        str = $@"
          lemma lemma_{prefix}_PathHasPCEffect_{atomicPath.Name}(
            s: {typeState},
            path: {prefix}_Path,
            tid: Armada_ThreadHandle
            )
            requires path.{prefix}_Path_{atomicPath.Name}?
            requires var asf := {prefix}_GetSpecFunctions(); asf.path_valid(s, path, tid)
            ensures  var asf := {prefix}_GetSpecFunctions();
                     var pc := asf.get_thread_pc(s, tid);
                     var s' := asf.path_next(s, path, tid);
                     var pc' := asf.get_thread_pc(s', tid);
        ";
        if (atomicPath.Tau) {
          str += $"asf.state_ok(s) && pc.Some? && asf.state_ok(s') && pc'.Some? && pc'.v == pc.v";
        }
        else {
          str += $"asf.state_ok(s) && pc.Some? && pc.v.{atomicPath.StartPC}?";
          if (atomicPath.Stopping) {
            str += " && !asf.state_ok(s')";
          }
          else if (atomicPath.EndPC == null) {
            str += " && asf.state_ok(s') && pc'.None?";
          }
          else {
            str += $" && asf.state_ok(s') && pc'.Some? && pc'.v.{atomicPath.EndPC}?";
          }
        }
        str += "{\n";
        str += pr.GetOpenValidPathInvocation(atomicPath);
        str += "}\n";
        pgp.AddLemma(str, auxName);
      }

      str = $@"
        lemma lemma_{prefix}_PathImpliesThreadRunning(
          s: {typeState},
          path: {prefix}_Path,
          tid: Armada_ThreadHandle
          )
          ensures  var asf := {prefix}_GetSpecFunctions();
                   asf.path_valid(s, path, tid) ==> asf.state_ok(s) && asf.get_thread_pc(s, tid).Some?
        {{
          var asf := {prefix}_GetSpecFunctions();
          if asf.path_valid(s, path, tid) {{
            match path {{
      ";
      foreach (var atomicPath in atomicPaths)
      {
        str += $@"
            case {prefix}_Path_{atomicPath.Name}(_) =>
              lemma_{prefix}_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
        ";
      }
      str += "} } }\n";
      pgp.AddLemma(str, auxName);
    }

    ///////////////////////////////////////////////////////////////////////
    // SEARCHING FOR AN ATOMIC PATH
    ///////////////////////////////////////////////////////////////////////

    public AtomicPathPrefix FindAtomicPathPrefixByNextRoutines(List<NextRoutine> nextRoutines)
    {
      if (nextRoutines.Count == 0) {
        return null;
      }

      var firstRoutine = nextRoutines[0];
      if (firstRoutine.nextType == NextType.Tau) {
        return null;
      }

      AtomicPathPrefix pathPrefix = null;
      foreach (var nextRoutine in nextRoutines)
      {
        var children = (pathPrefix == null ? rootPathPrefixesByPC[firstRoutine.startPC] : pathPrefix.Extensions);
        pathPrefix = children.FirstOrDefault(p => p.LastNextRoutine == nextRoutine);
        if (pathPrefix == null) {
          return null;
        }
      }

      return pathPrefix;
    }

    public AtomicPath FindAtomicPathByNextRoutines(List<NextRoutine> nextRoutines)
    {
      if (nextRoutines.Count == 0) {
        return null;
      }

      var firstRoutine = nextRoutines[0];
      if (firstRoutine.nextType == NextType.Tau) {
        return tauPath;
      }

      var pathPrefix = FindAtomicPathPrefixByNextRoutines(nextRoutines);
      return pathPrefix == null ? null : pathPrefix.PathVal;
    }

    public AtomicPath FindAtomicPathByPCs(List<ArmadaPC> pcs, bool stopping)
    {
      if (pcs.Count == 0) {
        return null;
      }

      AtomicPathPrefix pathPrefix = null;

      for (var i = 1; i < pcs.Count; ++i)
      {
        var pc = pcs[i];
        var children = (i == 1) ? rootPathPrefixesByPC[pcs[0]] : pathPrefix.Extensions;
        var findStopping = stopping && (i == pcs.Count - 1);
        if (pc == null) {
          pathPrefix = children.FirstOrDefault(p => p.LastNextRoutine.endPC == null && p.Stopping == findStopping);
        }
        else {
          pathPrefix = children.FirstOrDefault(p => pc.Equals(p.LastNextRoutine.endPC) && p.Stopping == findStopping);
        }
        if (pathPrefix == null) {
          return null;
        }
      }

      return pathPrefix.PathVal;
    }

    ///////////////////////////////////////////////////////////////////////
    // PATH MAPPING
    ///////////////////////////////////////////////////////////////////////

    public Dictionary<AtomicPath, AtomicPath> CreatePathMap(AtomicSpec hAtomic)
    {
      return atomicPaths.ToDictionary(
               lPath => lPath,
               lPath => lPath.Tau ? hAtomic.TauPath : hAtomic.FindAtomicPathByPCs(lPath.GetPCs(), lPath.Stopping));
    }

    public Dictionary<AtomicPath, AtomicPath> CreatePathMap(AtomicSpec hAtomic,
                                                            Dictionary<NextRoutine, NextRoutine> nextRoutineMap,
                                                            bool avoidFinalUnmappedStoppingStep = true)
    {
      return atomicPaths.Where(p => p.Mappable(nextRoutineMap, p.Stopping, avoidFinalUnmappedStoppingStep)).ToDictionary(
               lPath => lPath,
               lPath => lPath.Tau ? hAtomic.TauPath
                                  : hAtomic.FindAtomicPathByNextRoutines(lPath.MapNextRoutines(nextRoutineMap)));
    }

    ///////////////////////////////////////////////////////////////////////
    // BASIC LEMMAS
    ///////////////////////////////////////////////////////////////////////

    public delegate bool PathToBoolDelegate(AtomicPath ap);
    public delegate string PathToStringDelegate(AtomicPath ap);

    public void GeneratePerAtomicPathLemma(string fileName, string lemmaName, PathToBoolDelegate pathFilter,
                                           PathToStringDelegate postconditionDelegate, PathToStringDelegate proofBodyDelegate)
    {
      string str;

      var pr = new PathPrinter(this);
      foreach (var atomicPath in atomicPaths.Where(ap => pathFilter(ap)))
      {
        str = $@"
          lemma lemma_{prefix}_{lemmaName}_{atomicPath.Name}(
            asf: AtomicSpecFunctions<{typeState}, {prefix}_Path, {moduleName}.Armada_PC>,
            s: {typeState},
            path: {prefix}_Path,
            tid: Armada_ThreadHandle
            )
            requires asf == {prefix}_GetSpecFunctions()
            requires path.{prefix}_Path_{atomicPath.Name}?
            requires asf.path_valid(s, path, tid)
            ensures  {postconditionDelegate(atomicPath)}
          {{
            { pr.GetOpenValidPathInvocation(atomicPath) }
            { proofBodyDelegate(atomicPath) }
            ProofCustomizationGoesHere();
          }}
        ";
        if (fileName == null) {
          pgp.AddLemma(str);
        }
        else {
          pgp.AddLemma(str, fileName);
        }
      }
    }

    public void GenerateOverallAtomicPathLemma(string fileName, string perPathLemmaName, string overallLemmaName,
                                               string overallPostcondition, PathToBoolDelegate pathFilter)
    {
      string str = $@"
        lemma lemma_{prefix}_{overallLemmaName}(
          asf: AtomicSpecFunctions<{typeState}, {prefix}_Path, {moduleName}.Armada_PC>,
          s: {typeState},
          path: {prefix}_Path,
          tid: Armada_ThreadHandle
          )
            requires asf == {prefix}_GetSpecFunctions()
            requires asf.path_valid(s, path, tid)
            ensures  {overallPostcondition}
          {{
            match path {{
      ";
      str += String.Join("\n", atomicPaths.Select(atomicPath =>
        $"case {prefix}_Path_{atomicPath.Name}(_) => " +
        (pathFilter(atomicPath) ? $"lemma_{prefix}_{perPathLemmaName}_{atomicPath.Name}(asf, s, path, tid);"
                                : "assert {overallPostcondition};")));
      str += "}\n}\n";
      if (fileName == null) {
        pgp.AddLemma(str);
      }
      else {
        pgp.AddLemma(str, fileName);
      }
    }

    public void GenerateAtomicPathRequiresOKLemma()
    {
      string str = $@"
        lemma lemma_{prefix}_AtomicPathRequiresOK()
          ensures AtomicPathRequiresOK({prefix}_GetSpecFunctions())
        {{
          var asf := {prefix}_GetSpecFunctions();
          forall s, path, tid | asf.path_valid(s, path, tid)
            ensures asf.state_ok(s)
          {{
            lemma_{prefix}_PathImpliesThreadRunning(s, path, tid);
          }}
        }}
      ";
      pgp.AddLemma(str, auxName);
    }

    public void GenerateAtomicSteppingThreadHasPCLemma()
    {
      string str = $@"
        lemma lemma_{prefix}_AtomicSteppingThreadHasPC()
          ensures AtomicSteppingThreadHasPC({prefix}_GetSpecFunctions())
        {{
          var asf := {prefix}_GetSpecFunctions();
          forall s, path, tid | asf.path_valid(s, path, tid)
            ensures asf.get_thread_pc(s, tid).Some?
          {{
            lemma_{prefix}_PathImpliesThreadRunning(s, path, tid);
          }}
        }}
      ";
      pgp.AddLemma(str, auxName);
    }

    public void GenerateAtomicTauLeavesPCUnchangedLemma()
    {
      var pr = new PathPrinter(this);
      string str = $@"
        lemma lemma_{prefix}_AtomicTauLeavesPCUnchanged()
          ensures AtomicTauLeavesPCUnchanged({prefix}_GetSpecFunctions())
        {{
           var asf := {prefix}_GetSpecFunctions();
           forall s, path, tid | asf.path_valid(s, path, tid) && asf.path_type(path).AtomicPathType_Tau?
            ensures var s' := asf.path_next(s, path, tid);
                    asf.get_thread_pc(s', tid) == asf.get_thread_pc(s, tid)
           {{
             { pr.GetOpenValidPathInvocation(TauPath) }
           }}
        }}
      ";
      pgp.AddLemma(str, auxName);
    }

    public void GenerateAtomicPathCantAffectOtherThreadPCsExceptViaForkLemma()
    {
      string postcondition = @"forall other_tid :: other_tid != tid ==>
                               var s' := asf.path_next(s, path, tid);
                               var pc := asf.get_thread_pc(s, other_tid);
                               var pc' := asf.get_thread_pc(s', other_tid);
                               (pc' != pc ==> pc.None? && !asf.is_pc_nonyielding(pc'.v))";
      GeneratePerAtomicPathLemma(auxName, "AtomicPathCantAffectOtherThreadPCsExceptViaFork",
                                 atomicPath => true,
                                 atomicPath => postcondition,
                                 atomicPath => "");
      GenerateOverallAtomicPathLemma(auxName,
                                     "AtomicPathCantAffectOtherThreadPCsExceptViaFork",
                                     "AtomicPathCantAffectOtherThreadPCsExceptViaFork",
                                     postcondition,
                                     ap => true);

      string str = $@"
        lemma lemma_{prefix}_AtomicThreadCantAffectOtherThreadPCExceptViaFork()
          ensures AtomicThreadCantAffectOtherThreadPCExceptViaFork({prefix}_GetSpecFunctions())
        {{
          var asf := {prefix}_GetSpecFunctions();
          forall s, path, tid, other_tid | asf.path_valid(s, path, tid) && other_tid != tid
            ensures var s' := asf.path_next(s, path, tid);
                    var pc := asf.get_thread_pc(s, other_tid);
                    var pc' := asf.get_thread_pc(s', other_tid);
                    (pc' != pc ==> pc.None? && !asf.is_pc_nonyielding(pc'.v))
          {{
            lemma_{prefix}_AtomicPathCantAffectOtherThreadPCsExceptViaFork(asf, s, path, tid);
          }}
        }}
      ";
      pgp.AddLemma(str, auxName);
    }

    public void GenerateAtomicPathTypeAlwaysMatchesPCTypesLemma()
    {
      string str = $@"
        lemma lemma_{prefix}_AtomicPathTypeAlwaysMatchesPCTypes()
          ensures AtomicPathTypeAlwaysMatchesPCTypes({prefix}_GetSpecFunctions())
        {{
          var asf := {prefix}_GetSpecFunctions();
          forall s, path, tid | asf.path_valid(s, path, tid)
            ensures AtomicPathTypeMatchesPCTypes(asf, s, path, tid)
          {{
            match path {{
      ";
      str += String.Join("\n", atomicPaths.Select(atomicPath => $@"
        case {prefix}_Path_{atomicPath.Name}(_) =>
          lemma_{prefix}_PathHasPCEffect_{atomicPath.Name}(s, path, tid);
      "));
      str += "}\n  }\n  }\n";
      pgp.AddLemma(str, auxName);
    }
  }
}
