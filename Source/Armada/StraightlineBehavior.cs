using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Armada
{
  ////////////////////////////////////////////////////////
  // Extractors for printing
  ////////////////////////////////////////////////////////

  abstract class Extractor
  {
    public virtual string SB { get { throw new Exception("This extractor doesn't support straightline behavior access"); } }
    public virtual string Proc { get { throw new Exception("This extractor doesn't support proc access"); } }
    public virtual string Tid { get { throw new Exception("This extractor doesn't support tid access"); } }
    public virtual string SStates { get { throw new Exception("This extractor doesn't support straightline states access"); } }
    public virtual string STrace { get { throw new Exception("This extractor doesn't support straightline trace access"); } }

    public virtual string SState(string pos) { return $"{SStates}[{pos}]"; }
    public virtual string SStep(string pos) { return $"{STrace}[{pos}]"; }

    public string SState(int pos) { return SState(pos.ToString()); }
    public string SStep(int pos) { return SStep(pos.ToString()); }

    public virtual string NumStates { get { return $"|{SStates}|"; } }
    public virtual string NumSteps { get { return $"|{STrace}|"; } }

    public virtual string State(string pos) { return $"{SState(pos)}.state"; }
    public virtual string State(int pos, int subpos = 0) { return State(pos.ToString()); }

    public virtual string PathAndTid(string pos) { return $"{SStep(pos)}.step"; }
    public string PathAndTid(int pos) { return PathAndTid(pos.ToString()); }

    public virtual string Path(string pos) { return $"{PathAndTid(pos)}.path"; }
    public string Path(int pos) { return Path(pos.ToString()); }

    public virtual string Step(int pos, int subpos) { return $"{Path(pos)}.step{subpos}"; }

    public virtual string StepTid(string pos) { return $"{PathAndTid(pos)}.tid"; }
    public string StepTid(int pos) { return StepTid(pos.ToString()); }

    public virtual string TidInThreads(string pos) { return $"{Tid} in {State(pos)}.s.threads"; }
    public string TidInThreads(int pos) { return TidInThreads(pos.ToString()); }

    public virtual string PC(string pos) { return $"{State(pos)}.s.threads[{Tid}].pc"; }
    public virtual string PC(int pos) { return PC(pos.ToString()); }

    public virtual string Stack(string pos) { return $"{State(pos)}.s.threads[{Tid}].stack"; }
    public virtual string Stack(int pos) { return Stack(pos.ToString()); }

    public virtual string GetOpenValidPathInvocation(AtomicPath path, int pos) { return ""; }
  }

  class ExtractorSB : Extractor
  {
    private string sb, tid, proc;
    public ExtractorSB(string i_sb, string i_tid, string i_proc) { sb = i_sb; tid = i_tid; proc = i_proc; }
    public override string Tid { get { return tid; } }
    public override string SB { get { return sb; } }
    public override string SStates { get { return $"sb.states"; } }
    public override string STrace { get { return $"sb.trace"; } }
    public override string Proc { get { return proc; } }
  }

  class ExtractorSTrace : Extractor
  {
    private string strace, proc;
    public ExtractorSTrace(string i_strace, string i_proc) { strace = i_strace; proc = i_proc; }
    public override string STrace { get { return strace; } }
    public override string Proc { get { return proc; } }
  }

  class ExtractorEnumeration : Extractor
  {
    private AtomicSpec atomicSpec;

    public ExtractorEnumeration(AtomicSpec i_atomicSpec)
    {
      atomicSpec = i_atomicSpec;
    }

    public override string Tid { get { return "tid"; } }

    public override string State(int pos, int subpos = 0)
    {
      if (subpos == 0) {
        return $"s{pos}";
      }
      else {
        return $"states{pos}.s{subpos}";
      }
    }

    public override string Step(int pos, int subpos = 0)
    {
      return $"steps{pos}.step{subpos}";
    }
    
    public override string Path(string pos) { return $"path{pos}"; }

    public override string GetOpenValidPathInvocation(AtomicPath path, int pos)
    {
      var pr = new PathPrinter(atomicSpec);
      pr.States = $"states{pos}";
      pr.Steps = $"steps{pos}";
      pr.State = State(pos);
      pr.Path = Path(pos);
      return pr.GetOpenValidPathInvocation(path);
    }
  }

  class ExtractorExpanded : Extractor
  {
    private PathExpander pathExpander;

    public ExtractorExpanded(PathExpander i_pathExpander)
    {
      pathExpander = i_pathExpander;
    }

    public override string Tid { get { return "tid"; } }
    public override string State(int pos, int subpos = 0)
      { return $"s{pathExpander.PathIndexToStepIndex(pos) + subpos}"; }
    public override string Step(int pos, int subpos)
      { return $"step{pathExpander.PathIndexToStepIndex(pos) + subpos}"; }
  }

  ////////////////////////////////////////////////////////
  // Path expanders
  ////////////////////////////////////////////////////////

  class PathExpander
  {
    private List<int> pathIndexToStepIndex;
    private List<AtomicPath> paths;
    private int maxStepIndex;

    public PathExpander(StraightlineBehavior sb)
    {
      paths = new List<AtomicPath>();
      maxStepIndex = 0;
      pathIndexToStepIndex = new List<int>{ 0 };
      foreach (var path in sb.GetPaths()) {
        AddPath(path);
      }
    }

    public void AddPath(AtomicPath path)
    {
      paths.Add(path);
      maxStepIndex += (path == null) ? 1 : path.NumNextRoutines;
      pathIndexToStepIndex.Add(maxStepIndex);
    }

    public int PathIndexToStepIndex(int pathIndex)
    {
      return pathIndexToStepIndex[pathIndex];
    }
  }

  ////////////////////////////////////////////////////////
  // Straightline states
  ////////////////////////////////////////////////////////

  abstract class StraightlineState
  {
    protected ArmadaPC pc;
    protected Dictionary<ArmadaPC, int> visitedLoopHeads;
    protected int pos;

    public StraightlineState(int i_pos, ArmadaPC i_pc, IDictionary<ArmadaPC, int> i_visitedLoopHeads)
    {
      pos = i_pos;
      pc = i_pc;
      visitedLoopHeads = new Dictionary<ArmadaPC, int>(i_visitedLoopHeads);
    }

    public ArmadaPC PC { get { return pc; } }

    public virtual IEnumerable<string> GetEndProperties(Extractor e)
    {
      var s = $"{e.SState(pos)}.aux.visited_loops == map [";
      s += String.Join(", ", visitedLoopHeads.Select(kv => $"L.{kv.Key} := {e.State(kv.Value)}"));
      s += "]";
      yield return s;
    }

    public abstract IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants);
    public abstract string Name { get; }
    public IDictionary<ArmadaPC, int> VisitedLoopHeads { get { return visitedLoopHeads; } }
    public bool IsLoopHeadVisited(ArmadaPC pc) { return visitedLoopHeads.ContainsKey(pc); }

    public virtual IEnumerable<Tuple<AtomicPath, CHLPathEffect>> PotentialSuccessorPaths { get { yield break;  } }
    public virtual string ProofOfLimitedNextSSteps(Extractor e) { return ""; }

    public virtual bool HasLocalInvariant(HashSet<ArmadaPC> pcsWithLocalInvariants,
                                          Dictionary<string, ArmadaPC> returnPCForMethod)
    {
      return pcsWithLocalInvariants.Contains(pc);
    }
  }

  class StraightlineStateNormal : StraightlineState
  {
    public StraightlineStateNormal(int i_pos, ArmadaPC i_pc, IDictionary<ArmadaPC, int> i_visitedLoopHeads)
      : base(i_pos, i_pc, i_visitedLoopHeads)
    {
    }

    public override IEnumerable<string> GetEndProperties(Extractor e)
    {
      yield return $"{e.SState(pos)}.aux.phase.StraightlinePhaseNormal?";
      yield return e.TidInThreads(pos);
      yield return $"{e.PC(pos)}.{pc}?";
      foreach (var s in base.GetEndProperties(e))
      {
        yield return s;
      }
    }

    public override IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants)
    {
      yield return new StraightlineStepYield(pos);
    }

    public override string Name
    {
      get
      {
        if (visitedLoopHeads.ContainsKey(pc)) {
          return $"NormalRevisited_{pc.Name}";
        }
        else {
          return $"Normal_{pc.Name}";
        }
      }
    }
  }

  class StraightlineStateLooped : StraightlineState
  {
    private List<Tuple<AtomicPath, CHLPathEffect>> potentialSuccessorPaths;

    public StraightlineStateLooped(int i_pos, ArmadaPC i_pc, IDictionary<ArmadaPC, int> i_visitedLoopHeads)
      : base(i_pos, i_pc, i_visitedLoopHeads)
    {
    }

    public override IEnumerable<Tuple<AtomicPath, CHLPathEffect>> PotentialSuccessorPaths { get { return potentialSuccessorPaths; } }

    public override IEnumerable<string> GetEndProperties(Extractor e)
    {
      yield return e.TidInThreads(pos);
      yield return $"{e.SState(pos)}.aux.phase.StraightlinePhaseLooped?";
      yield return $"{e.PC(pos)}.{pc}?";
      foreach (var s in base.GetEndProperties(e))
      {
        yield return s;
      }
    }

    public override IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants)
    {
      potentialSuccessorPaths =
        pathsStartingAtPC[pc].Select(path => new Tuple<AtomicPath, CHLPathEffect>(path, pathEffectMap[path])).ToList();
      bool hasLocalInvariant = pcsWithLocalInvariants.Contains(pc);
      foreach (var tup in potentialSuccessorPaths) {
        var atomicPath = tup.Item1;
        var effect = tup.Item2;
        if (effect is CHLPathEffectCall) {
          var ceffect = (CHLPathEffectCall)effect;
          yield return new StraightlineStepCall(pos, atomicPath, hasLocalInvariant, ceffect.EffectiveEndPC, ceffect.Callee);
        }
        else if (effect is CHLPathEffectNormal) {
          yield return new StraightlineStepNormal(pos, atomicPath, hasLocalInvariant);
        }
        // We don't return or exit in straightline behaviors, so ignore any atomic paths that do those
      }
    }

    public override string Name { get { return $"Looped_{pc.Name}"; } }

    public override string ProofOfLimitedNextSSteps(Extractor e)
    {
      var pos_plus_1 = $"{pos} + 1";

      string str = $@"
        var s := {e.State(pos)};
        var s' := {e.State(pos_plus_1)};
        var path := {e.Path(pos)};
        lemma_PathPossibilitiesStartingAtPC_{pc}(s, s', path, {e.Tid});
      ";

      foreach (var tup in potentialSuccessorPaths) {
        var atomicPath = tup.Item1;
        var effect = tup.Item2;

        if (effect is CHLPathEffectCall) {
          continue;
        }

        if (effect is CHLPathEffectNormal) {
          continue;
        }

        str += $@"
          if path.LAtomic_Path_{atomicPath.Name}? {{
            lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, {e.Tid});
            assert false;
          }}
        ";
      }

      return str;
    }
  }

  class StraightlineStateYielded : StraightlineState
  {
    private List<Tuple<AtomicPath, CHLPathEffect>> potentialSuccessorPaths;
    private bool atLoopHead;

    public StraightlineStateYielded(int i_pos, ArmadaPC i_pc, IDictionary<ArmadaPC, int> i_visitedLoopHeads)
      : base(i_pos, i_pc, i_visitedLoopHeads)
    {
      atLoopHead = false;
    }

    public override IEnumerable<Tuple<AtomicPath, CHLPathEffect>> PotentialSuccessorPaths { get { return potentialSuccessorPaths; } }

    public override IEnumerable<string> GetEndProperties(Extractor e)
    {
      yield return $"{e.SState(pos)}.aux.phase.StraightlinePhaseYielded?";
      yield return e.TidInThreads(pos);
      yield return $"{e.PC(pos)}.{pc}?";
      foreach (var s in base.GetEndProperties(e))
      {
        yield return s;
      }
    }

    public override IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants)
    {
      potentialSuccessorPaths =
        pathsStartingAtPC[pc].Select(path => new Tuple<AtomicPath, CHLPathEffect>(path, pathEffectMap[path])).ToList();
      atLoopHead = loopHeads.Contains(pc);

      if (visitedLoopHeads.ContainsKey(pc)) {
        yield break;
      }
      else if (atLoopHead) {
        yield return new StraightlineStepLoopModifies(pos, pc);
      }
      else {
        bool hasLocalInvariant = pcsWithLocalInvariants.Contains(pc);
        foreach (var tup in potentialSuccessorPaths) {
          var atomicPath = tup.Item1;
          var effect = tup.Item2;
          if (effect is CHLPathEffectCall) {
            var ceffect = (CHLPathEffectCall)effect;
            yield return new StraightlineStepCall(pos, atomicPath, hasLocalInvariant, ceffect.EffectiveEndPC, ceffect.Callee);
          }
          else if (effect is CHLPathEffectNormal) {
            yield return new StraightlineStepNormal(pos, atomicPath, hasLocalInvariant);
          }
          // We don't return or exit in straightline behaviors, so ignore any atomic paths that do those
        }
      }
    }

    public override string Name
    {
      get
      {
        if (visitedLoopHeads.ContainsKey(pc)) {
          return $"YieldedRevisited_{pc.Name}";
        }
        else {
          return $"Yielded_{pc.Name}";
        }
      }
    }

    public override string ProofOfLimitedNextSSteps(Extractor e)
    {
      if (visitedLoopHeads.ContainsKey(pc)) {
        return $"assert {e.PC(pos)} in {e.SState(pos)}.aux.visited_loops;\n";
      }

      if (atLoopHead) {
        return $"assert IsLoopHead({e.PC(pos)});\n";
      }

      var pos_plus_1 = $"{pos} + 1";

      string str = $@"
        var s := {e.State(pos)};
        var s' := {e.State(pos_plus_1)};
        var path := {e.Path(pos)};
        lemma_PathPossibilitiesStartingAtPC_{pc}(s, s', path, {e.Tid});
      ";

      foreach (var tup in potentialSuccessorPaths) {
        var atomicPath = tup.Item1;
        var effect = tup.Item2;

        if (effect is CHLPathEffectCall) {
          continue;
        }

        if (effect is CHLPathEffectNormal) {
          continue;
        }

        str += $@"
          if path.LAtomic_Path_{atomicPath.Name}? {{
            lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, {e.Tid});
            assert false;
          }}
        ";
      }

      return str;
    }
  }

  class StraightlineStateCalled : StraightlineState
  {
    private ArmadaPC returnPC;
    private string callee;

    public StraightlineStateCalled(int i_pos, ArmadaPC i_pc, ArmadaPC i_returnPC, IDictionary<ArmadaPC, int> i_visitedLoopHeads,
                                   string i_callee)
      : base(i_pos, i_pc, i_visitedLoopHeads)
    {
      returnPC = i_returnPC;
      callee = i_callee;
    }

    public override IEnumerable<string> GetEndProperties(Extractor e)
    {
      yield return $"{e.SState(pos)}.aux.phase.StraightlinePhaseCalled?";
      yield return e.TidInThreads(pos);
      yield return $"{e.PC(pos)}.{pc}?";
      yield return $"|{e.Stack(pos)}| > 0";
      yield return $"{e.Stack(pos)}[0].return_pc.{returnPC}?";
      foreach (var s in base.GetEndProperties(e))
      {
        yield return s;
      }
    }

    public override IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants)
    {
      yield return new StraightlineStepEnsures(pos, returnPC, callee);
    }

    public override string Name { get { return $"Called_{returnPC.Name}"; } }
  }

  class StraightlineStateEnsured : StraightlineState
  {
    private ArmadaPC returnPC;
    private string callee;
    private List<Tuple<AtomicPath, CHLPathEffect>> potentialSuccessorPaths;

    public StraightlineStateEnsured(int i_pos, ArmadaPC i_returnPC, IDictionary<ArmadaPC, int> i_visitedLoopHeads, string i_callee)
      : base(i_pos, null, i_visitedLoopHeads)
    {
      returnPC = i_returnPC;
      callee = i_callee;
    }

    public string Callee { get { return callee; } }

    public override IEnumerable<Tuple<AtomicPath, CHLPathEffect>> PotentialSuccessorPaths { get { return potentialSuccessorPaths; } }

    public override IEnumerable<string> GetEndProperties(Extractor e)
    {
      yield return $"{e.SState(pos)}.aux.phase.StraightlinePhaseEnsured?";
      yield return e.TidInThreads(pos);
      yield return $"PCToProc({e.PC(pos)}).LProcName_{callee}?";
      yield return $"IsReturnSite({e.PC(pos)})";
      yield return $"|{e.Stack(pos)}| > 0";
      yield return $"{e.Stack(pos)}[0].return_pc.{returnPC}?";
      foreach (var s in base.GetEndProperties(e))
      {
        yield return s;
      }
    }

    public override IEnumerable<StraightlineStep> GetSuccessorSteps(Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC,
                                                                    HashSet<ArmadaPC> loopHeads,
                                                                    Dictionary<AtomicPath, CHLPathEffect> pathEffectMap,
                                                                    Dictionary<string, ArmadaPC> returnPCForMethod,
                                                                    HashSet<ArmadaPC> pcsWithLocalInvariants)
    {
      potentialSuccessorPaths = pathsStartingAtPC[returnPCForMethod[callee]]
                                  .Select(path => new Tuple<AtomicPath, CHLPathEffect>(path, pathEffectMap[path])).ToList();

      bool hasLocalInvariant = pcsWithLocalInvariants.Contains(pc);
      foreach (var tup in potentialSuccessorPaths) {
        var atomicPath = tup.Item1;
        var effect = tup.Item2;
        if (effect is CHLPathEffectReturn) {
          var reffect = (CHLPathEffectReturn)effect;
          // Only return to the return PC at the top of the stack.
          if (reffect.EffectiveStartPC.Equals(returnPC)) {
            yield return new StraightlineStepReturn(pos, atomicPath, hasLocalInvariant, reffect.Returner);
          }
        }
        else if (effect is CHLPathEffectReturnThenCall) {
          var rceffect = (CHLPathEffectReturnThenCall)effect;
          // Only return to the return PC at the top of the stack.
          if (rceffect.EffectiveStartPC.Equals(returnPC)) {
            yield return new StraightlineStepReturnThenCall(pos, atomicPath, hasLocalInvariant, rceffect.EffectiveEndPC,
                                                            rceffect.Returner, rceffect.Callee);
          }
        }
        // After satisfying a post-condition, we should return to the caller, not exit.  So, ignore any
        // paths that exit.
      }
    }

    public override string Name { get { return $"Ensured_{returnPC.Name}"; } }

    public override string ProofOfLimitedNextSSteps(Extractor e)
    {
      var pos_plus_1 = $"{pos} + 1";

      string str = $@"
        var s := {e.State(pos)};
        var s' := {e.State(pos_plus_1)};
        var path := {e.Path(pos)};
        lemma_PathPossibilitiesReturningFrom_{callee}(s, s', path, {e.Tid});
      ";

      foreach (var tup in potentialSuccessorPaths) {
        var atomicPath = tup.Item1;
        var effect = tup.Item2;

        if (effect is CHLPathEffectReturn) {
          var reffect = (CHLPathEffectReturn)effect;
          if (reffect.EffectiveStartPC.Equals(returnPC)) {
            continue;
          }
        }

        if (effect is CHLPathEffectReturnThenCall) {
          var rceffect = (CHLPathEffectReturnThenCall)effect;
          if (rceffect.EffectiveStartPC.Equals(returnPC)) {
            continue;
          }
        }

        str += $@"
          if path.LAtomic_Path_{atomicPath.Name}? {{
            lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, {e.Tid});
            assert false;
          }}
        ";
      }

      return str;
    }

    public override bool HasLocalInvariant(HashSet<ArmadaPC> pcsWithLocalInvariants,
                                           Dictionary<string, ArmadaPC> returnPCForMethod)
    {
      return pcsWithLocalInvariants.Contains(returnPCForMethod[callee]);
    }
  }

  ////////////////////////////////////////////////////////
  // Straightline steps
  ////////////////////////////////////////////////////////

  abstract class StraightlineStep
  {
    protected int pos;

    public StraightlineStep(int i_pos) { pos = i_pos; }
    public virtual IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      yield return $"{e.NumSteps} > {pos}";
    }

    public virtual IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      yield break;
    }

    public abstract StraightlineState GetNextState(StraightlineState current);
    public virtual IEnumerable<bool> BranchOutcomes { get { yield break; } }
    public virtual IEnumerable<string> GetStatesAndSteps(Extractor e, bool typed) { yield break; }
    public virtual IEnumerable<string> GetPaths(Extractor e, bool typed) { yield break; }
    public virtual IEnumerable<string> GetOpenValidPathInvocations(Extractor e) { yield break; }
  }

  abstract class StraightlineStepPath : StraightlineStep
  {
    protected AtomicPath atomicPath;
    protected bool hasLocalInvariant;

    public StraightlineStepPath(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant) : base(i_pos)
    {
      atomicPath = i_atomicPath;
      hasLocalInvariant = i_hasLocalInvariant;
    }

    public AtomicPath Path { get { return atomicPath; } }
    public override IEnumerable<bool> BranchOutcomes { get { return atomicPath.BranchOutcomes; } }

    public override IEnumerable<string> GetStatesAndSteps(Extractor e, bool typed)
    {
      for (var i = 0; i < atomicPath.NumNextRoutines; ++i) {
        if (i > 0) {
          yield return typed ? $"{e.State(pos, i)}: LPlusState" : e.State(pos, i);
        }
        var nextRoutine = atomicPath.NextRoutines[i];
        yield return typed ? $"{e.Step(pos, i)}: L.Armada_Step" : e.Step(pos, i);
      }
    }
    
    public override IEnumerable<string> GetPaths(Extractor e, bool typed)
    {
      yield return typed ? $"{e.Path(pos)}: LAtomic_Path" : e.Path(pos);
    }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      if (hasLocalInvariant) {
        var fn = crRelative ? "cr.local_inv" : "LocalInv";
        yield return $"{fn}({e.State(pos)}, {e.Tid})";
      }

      if (expanded) {
        for (var i = 0; i < atomicPath.NumNextRoutines; ++i) {
          var nextRoutine = atomicPath.NextRoutines[i];
          var suffix = nextRoutine.NameSuffix;
          var s = e.State(pos, i);
          var s_prime = e.State(pos, i + 1);
          var step = e.Step(pos, i);
          yield return $"LPlus_ValidStep({s}, {step}, {e.Tid}) && {s_prime} == LPlus_GetNextState({s}, {step}, {e.Tid})";
          if (nextRoutine.HasFormals) {
            yield return $"{step}.Armada_Step_{suffix}? && L.Armada_ValidStep_{suffix}({s}.s, {e.Tid}, {step}.params_{suffix}) && {s_prime}.s == L.Armada_GetNextState_{suffix}({s}.s, {e.Tid}, {step}.params_{suffix})";
          }
          else {
            yield return $"L.Armada_ValidStep_{suffix}({s}.s, {e.Tid}) && {s_prime}.s == L.Armada_GetNextState_{suffix}({s}.s, {e.Tid})";
          }
        }
      }
      else {
        yield return $"LAtomic_NextPath({e.State(pos)}, {e.State(pos+1)}, {e.Path(pos)}, {e.Tid}) && {e.Path(pos)}.LAtomic_Path_{atomicPath.Name}?";
      }
    }

    public override IEnumerable<string> GetOpenValidPathInvocations(Extractor e)
    {
      yield return e.GetOpenValidPathInvocation(atomicPath, pos);
    }
  }

  class StraightlineStepNormal : StraightlineStepPath
  {
    public StraightlineStepNormal(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant)
      : base(i_pos, i_atomicPath, i_hasLocalInvariant)
    {
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepNormal?";
      yield return $"{e.Path(pos)}.LAtomic_Path_{atomicPath.Name}?";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateNormal(pos + 1, atomicPath.EndPC, current.VisitedLoopHeads);
    }
  }

  class StraightlineStepLoopModifies : StraightlineStep
  {
    private ArmadaPC pc;

    public StraightlineStepLoopModifies(int i_pos, ArmadaPC i_pc) : base(i_pos)
    {
      pc = i_pc;
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepLoopModifies?";
      yield return $"{e.SStep(pos)}.pc.{pc}?";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      var updatedDict = new Dictionary<ArmadaPC, int>(current.VisitedLoopHeads);
      updatedDict[current.PC] = pos;
      return new StraightlineStateLooped(pos + 1, current.PC, updatedDict);
    }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      var fn = crRelative ? "cr.loop_modifies_clauses" : "LoopModifiesClauses";
      yield return $"{fn}(L.{pc}, {e.State(pos)}, {e.State(pos + 1)}, {e.Tid})";
    }
  }

  class StraightlineStepYield : StraightlineStep
  {
    public StraightlineStepYield(int i_pos) : base(i_pos)
    {
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepYield?";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateYielded(pos + 1, current.PC, current.VisitedLoopHeads);
    }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      var fn = crRelative ? "cr.yield_pred" : "YieldPredicate";
      yield return $"{fn}({e.State(pos)}, {e.State(pos + 1)}, {e.Tid})";
    }
  }

  class StraightlineStepCall : StraightlineStepPath
  {
    private ArmadaPC returnPC;
    private string callee;

    public StraightlineStepCall(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant, ArmadaPC i_returnPC, string i_callee)
      : base(i_pos, i_atomicPath, i_hasLocalInvariant)
    {
      returnPC = i_returnPC;
      callee = i_callee;
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepCall?";
      yield return $"{e.Path(pos)}.LAtomic_Path_{atomicPath.Name}?";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateCalled(pos + 1, atomicPath.EndPC, returnPC, current.VisitedLoopHeads, callee);
    }

    private string Callee { get { return callee; } }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      foreach (var s in base.GetEnumerationClauses(e, expanded, crRelative)) {
        yield return s;
      }

      var fn = crRelative ? "cr.requires_clauses" : "RequiresClauses";
      yield return $"{fn}(LProcName_{callee}, {e.State(pos + 1)}, {e.Tid})";
    }
  }

  class StraightlineStepEnsures : StraightlineStep
  {
    private ArmadaPC returnPC;
    string callee;

    public StraightlineStepEnsures(int i_pos, ArmadaPC i_returnPC, string i_callee) : base(i_pos)
    {
      returnPC = i_returnPC;
      callee = i_callee;
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepEnsures?";
      yield return $"{e.SStep(pos)}.callee.LProcName_{callee}?";
    }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      var fn = crRelative ? "cr.ensures_clauses" : "EnsuresClauses";
      yield return $"{fn}(LProcName_{callee}, {e.State(pos)}, {e.State(pos + 1)}, {e.Tid}) && ThreadAtReturnSite({e.State(pos+1)}, {e.Tid}, LProcName_{callee})";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateEnsured(pos + 1, returnPC, current.VisitedLoopHeads, callee);
    }

    private string Callee { get { return callee; } }
  }

  class StraightlineStepReturn : StraightlineStepPath
  {
    private string returner;

    public StraightlineStepReturn(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant, string i_returner)
      : base(i_pos, i_atomicPath, i_hasLocalInvariant)
    {
      returner = i_returner;
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepReturn?";
      yield return $"{e.Path(pos)}.LAtomic_Path_{atomicPath.Name}?";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateNormal(pos + 1, atomicPath.EndPC, current.VisitedLoopHeads);
    }

    private string Returner { get { return returner; } }
  }

  class StraightlineStepReturnThenCall : StraightlineStepPath
  {
    private ArmadaPC returnPC;
    private string returner;
    private string callee;

    public StraightlineStepReturnThenCall(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant,
                                          ArmadaPC i_returnPC, string i_returner, string i_callee)
      : base(i_pos, i_atomicPath, i_hasLocalInvariant)
    {
      returnPC = i_returnPC;
      returner = i_returner;
      callee = i_callee;
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      foreach (var c in base.GetSatisfiesDescriptorClauses(e)) {
        yield return c;
      }
      yield return $"{e.SStep(pos)}.StraightlineStepReturnThenCall?";
      yield return $"{e.Path(pos)}.LAtomic_Path_{atomicPath.Name}?";
    }

    public override IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      foreach (var s in base.GetEnumerationClauses(e, expanded, crRelative)) {
        yield return s;
      }
      var fn = crRelative ? "cr.requires_clauses" : "RequiresClauses";
      yield return $"{fn}(LProcName_{callee}, {e.State(pos+1)}, {e.Tid})";
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateCalled(pos + 1, atomicPath.EndPC, returnPC, current.VisitedLoopHeads, callee);
    }

    private string Returner { get { return returner; } }
    private string Callee { get { return callee; } }
  }

  class StraightlineStepBeyondEnd : StraightlineStepPath
  {
    public StraightlineStepBeyondEnd(int i_pos, AtomicPath i_atomicPath, bool i_hasLocalInvariant)
      : base(i_pos, i_atomicPath, i_hasLocalInvariant)
    {
    }

    public override IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      throw new Exception("Shouldn't invoke GetSatisfiesDescriptorClauses for behavior that goes beyond end");
    }

    public override StraightlineState GetNextState(StraightlineState current)
    {
      return new StraightlineStateNormal(pos + 1, atomicPath.EndPC, current.VisitedLoopHeads);
    }
  }


  ////////////////////////////////////////////////////////
  // Straightline behaviors
  ////////////////////////////////////////////////////////

  class StraightlineBehavior
  {
    private StraightlineBehavior predecessor;
    private StraightlineStep lastStep;
    private int numSteps;
    private StraightlineState lastState;
    private List<StraightlineBehavior> successors;
    private string methodName;
    private string name;

    public StraightlineBehavior(StraightlineBehavior i_predecessor, StraightlineStep i_lastStep)
    {
      predecessor = i_predecessor;
      lastStep = i_lastStep;
      numSteps = predecessor.NumSteps + 1;
      lastState = lastStep.GetNextState(predecessor.LastState);
      successors = new List<StraightlineBehavior>();
      methodName = predecessor.MethodName;
      if (lastStep is StraightlineStepBeyondEnd) {
        name = null;
      }
      else {
        name = MakeName();
        predecessor.NoteSuccessor(this);
      }
    }

    public StraightlineBehavior(ArmadaPC initialPC)
    {
      predecessor = null;
      lastStep = null;
      numSteps = 0;
      lastState = new StraightlineStateNormal(0, initialPC, new Dictionary<ArmadaPC, int>());
      successors = new List<StraightlineBehavior>();
      methodName = initialPC.methodName;
      name = MakeName();
    }

    private void NoteSuccessor(StraightlineBehavior successor) { successors.Add(successor); }

    public int NumSteps { get { return numSteps; } }
    public StraightlineState LastState { get { return lastState; } }
    public IEnumerable<StraightlineBehavior> Successors { get { return successors; } }
    public string MethodName { get { return methodName; } }
    public string Name { get { return name; } }

    private string MakeName()
    {
      string str = methodName;
      var branchString = String.Concat(BranchOutcomes.Select(b => b ? "Y" : "N"));
      if (!String.IsNullOrEmpty(branchString)) {
        str += "_" + branchString;
      }
      str += "_" + lastState.Name;
      return str;
    }

    public IEnumerable<bool> BranchOutcomes
    {
      get
      {
        if (predecessor == null)
        {
          yield break;
        }

        foreach (var b in predecessor.BranchOutcomes)
        {
          yield return b;
        }
        foreach (var b in lastStep.BranchOutcomes)
        {
          yield return b;
        }
      }
    }

    public IEnumerable<Tuple<AtomicPath, CHLPathEffect>> PotentialSuccessorPaths { get { return lastState.PotentialSuccessorPaths; } }

    public IEnumerable<string> GetSatisfiesDescriptorClauses(Extractor e)
    {
      if (lastStep is StraightlineStepBeyondEnd) {
        throw new Exception("Shouldn't invoke GetSatisfiesDescriptorClauses for behavior that goes beyond end");
      }
      if (predecessor == null)
      {
        yield return $"{e.Proc}.LProcName_{methodName}?";
      }
      else
      {
        yield return $"StraightlineBehaviorSatisfiesDescriptor_{predecessor.Name}({e.STrace}, {e.Proc})";
      }
      if (lastStep != null)
      {
        foreach (var c in lastStep.GetSatisfiesDescriptorClauses(e))
        {
          yield return c;
        }
      }
    }

    public string GetProofOfEndProperties(Extractor e)
    {
      string str = "";

      if (predecessor != null) {
        str += $"lemma_StraightlineBehaviorEndProperties_{predecessor.Name}({e.SB}, {e.Tid}, {e.Proc});\n";
      }

      if (lastStep != null) {
        var pos = NumSteps - 1;
        var pos_plus_1 = $"{NumSteps - 1} + 1";
        str += $@"
          var sspec := GetLAtomicStraightlineSpec({e.Tid}, {e.Proc});
          assert ActionTuple({e.SState(pos)}, {e.SState(pos_plus_1)}, {e.SStep(pos)}) in sspec.next;
        ";

        if (lastStep is StraightlineStepPath) {
          var pathStep = (StraightlineStepPath)lastStep;
          var atomicPath = pathStep.Path;
          str += $"lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}({e.State(pos)}, {e.State(pos_plus_1)}, {e.Path(pos)}, {e.Tid});\n";
        }
      }

      return str;
    }

    public IEnumerable<string> GetStatesAndPaths(Extractor e, bool typed)
    {
      if (predecessor != null) {
        foreach (var s in predecessor.GetStatesAndPaths(e, typed)) {
          yield return s;
        }
      }

      if (lastStep != null) {
        foreach (var s in lastStep.GetPaths(e, typed)) {
          yield return s;
        }
      }

      yield return typed ? $"{e.State(numSteps)}: LPlusState" : e.State(numSteps);
    }

    private IEnumerable<string> GetEnumerationClausesForSteps(Extractor e, bool expanded, bool crRelative)
    {
      if (predecessor != null) {
        foreach (var s in predecessor.GetEnumerationClausesForSteps(e, expanded, crRelative)) {
          yield return s;
        }
      }

      if (lastStep != null) {
        foreach (var s in lastStep.GetEnumerationClauses(e, expanded, crRelative)) {
          yield return s;
        }
      }
    }

    private IEnumerable<int> GetNeededInvariantPositions(Extractor e, bool includeFinalState)
    {
      if (predecessor != null) {
        if (lastStep is StraightlineStepBeyondEnd) {
          // If the last step is beyond the end of the straightline behavior, then just
          // recursively call the predecessor.
          
          foreach (var i in predecessor.GetNeededInvariantPositions(e, includeFinalState)) {
            yield return i;
          }
        }
        else {
          // Recursively call GetNeededInvariantPositions on our predecessor to get all
          // earlier invariant positions.  Pass includedFinalState = false since the
          // predecessor's final state isn't our final state.
        
          foreach (var i in predecessor.GetNeededInvariantPositions(e, false)) {
            yield return i;
          }

          // Include the final state if the last step is something other than a path step,
          // or if the caller of this function set includeFinalState to true.

          if (includeFinalState || !(lastStep is StraightlineStepPath)) {
            yield return numSteps;
          }
        }
      }
      else {
        // If there is no predecessor, include the state (s0).

        yield return numSteps;
      }
    }

    public IEnumerable<string> GetEnumerationClauses(Extractor e, bool expanded = false, bool crRelative = false)
    {
      var ifn = crRelative ? "cr.established_inv" : "InductiveInv";
      var gfn = crRelative ? "cr.global_inv" : "GlobalInv";
      var rfn = crRelative ? "cr.requires_clauses" : "RequiresClauses";

      yield return AH.CombineStringsWithAnd(GetNeededInvariantPositions(e, true).Select(i => $"{ifn}({e.State(i)})"));
      yield return AH.CombineStringsWithAnd(GetNeededInvariantPositions(e, true).Select(i => $"{gfn}({e.State(i)})"));
      yield return $"{rfn}(LProcName_{methodName}, {e.State(0)}, {e.Tid})";

      foreach (var s in GetEnumerationClausesForSteps(e, expanded, crRelative)) {
        yield return s;
      }
    }

    public IEnumerable<string> GetOpenValidPathInvocations(Extractor e)
    {
      if (predecessor != null) {
        foreach (var s in predecessor.GetOpenValidPathInvocations(e)) {
          yield return s;
        }
      }

      if (lastStep != null) {
        foreach (var s in lastStep.GetOpenValidPathInvocations(e)) {
          yield return s;
        }
      }
    }

    public IEnumerable<AtomicPath> GetPaths()
    {
      if (predecessor != null) {
        foreach (var path in predecessor.GetPaths()) {
          yield return path;
        }
      }
      if (lastStep is StraightlineStepPath pathStep) {
        yield return pathStep.Path;
      }
      else if (lastStep != null) {
        yield return null;
      }
    }

    public IEnumerable<string> GetStatesAndSteps(Extractor e, bool typed)
    {
      if (predecessor != null) {
        foreach (var s in predecessor.GetStatesAndSteps(e, typed)) {
          yield return s;
        }
      }

      if (lastStep != null) {
        foreach (var s in lastStep.GetStatesAndSteps(e, typed)) {
          yield return s;
        }
      }

      yield return typed ? $"{e.State(numSteps, 0)}: LPlusState" : e.State(numSteps, 0);
    }
  }
}
