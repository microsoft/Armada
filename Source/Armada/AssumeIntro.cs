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
  public class AssumeIntroHelpers
  {
    public static string GetCommonPathStateString(int i, bool behavior)
    {
      return behavior ? $"b.states[{i}]" : $"ss{i}";
    }

    public static string GetCommonPathStepString(int i, bool behavior)
    {
      return behavior ? $"b.trace[{i}]" : $"sstep{i}";
    }

    public static string GetCommonPathSS(List<PCNode> states, bool ssAvailable)
    {
      return ssAvailable ? "ss" : $"b.states[{states.Count-1}]";
    }

    public static string GetCommonPathRequiresString(ArmadaSymbolTable symbols, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                                                     Dictionary<ArmadaPC, int> visitedLoops, bool behavior, bool useVisitedLoops, bool ssAvailable)
    {
      string str = "";
      int i;
      for (i = 0; i < steps.Count; ++i) {
        var step = steps.ElementAt(i);
        var typ = step.GetStraightlineStepTypeAsString();
        str += $"requires {GetCommonPathStepString(i, behavior)}.StraightlineStep{typ}?\n";
        if (typ == "Normal") {
          str += $"requires {GetCommonPathStepString(i, behavior)}.step.Armada_TraceEntry_{step.Next.NameSuffix}?\n";
        }
        else if (typ == "Call") {
          str += $"requires {GetCommonPathStepString(i, behavior)}.call_step.Armada_TraceEntry_{step.Next.NameSuffix}?\n";
        }
        else if (typ == "Loop") {
          str += $"requires {GetCommonPathStepString(i, behavior)}.guard_step.Armada_TraceEntry_{step.Next.NameSuffix}?\n";
        }
      }
      for (i = 0; i < states.Count; ++i) {
        str += $"requires tid in {GetCommonPathStateString(i, behavior)}.state.s.threads\n";
      }
      for (i = 0; i < states.Count; ++i) {
        var node = states.ElementAt(i);
        str += $"requires {GetCommonPathStateString(i, behavior)}.state.s.threads[tid].pc.{node.PC}?\n";
      }
      if (useVisitedLoops) {
        var ss = GetCommonPathSS(states, ssAvailable);
        foreach (var p in visitedLoops) {
          if (p.Value < 0) {
            str += $"requires L.{p.Key} !in {ss}.visited_loops\n";
          }
          else {
            str += $"requires L.{p.Key} in {ss}.visited_loops\n";
            str += $"requires {ss}.visited_loops[L.{p.Key}] == {GetCommonPathStateString(p.Value, behavior)}.state\n";
          }
        }
      }
      return str;
    }
  }

  public class AssumeIntroProofGenerator : AbstractProofGenerator
  {
    public abstract class PathLemmaGenerator
    {
      protected ProofGenerationParams pgp;
      protected string pathName;
      protected string methodName;
      protected List<PCNode> states;
      protected List<StepDescriptor> steps;
      protected Dictionary<ArmadaPC, int> visitedLoops;
      protected List<bool> branches;

      public PathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName, List<PCNode> i_states,
                                List<StepDescriptor> i_steps, Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
      {
        pgp = i_pgp;
        pathName = i_pathName;
        methodName = i_methodName;
        states = i_states;
        steps = i_steps;
        visitedLoops = i_visitedLoops;
        branches = i_branches;
      }

      protected abstract string GetLemmaType();

      protected virtual List<string> GetExtraFormals() { return new List<string>(); }

      protected virtual List<string> GetExtraInvocationParameters() { return new List<string>(); }

      protected virtual bool UseVisitedLoops { get { return false; } }

      protected virtual string GetExtraRequires() { return ""; }

      protected abstract string GetEnsures(bool behavior);

      public void GenerateLemmas()
      {
        GeneratePathLemma();
        GeneratePathBehaviorLemma();
      }

      protected virtual string GetPathLemmaBody()
      {
        return "";
      }

      public virtual void GeneratePathLemma()
      {
        var lemmaType = GetLemmaType();
        var lemmaName = $"lemma_{lemmaType}PathLemma_" + pathName;
        var procName = "LProcName_" + methodName;
        var str = "lemma " + lemmaName + "(";
        var lemmaParams = new List<string> { "cr:CHLRequest", "tid:Armada_ThreadHandle", "ss:SState" };
        lemmaParams.AddRange(Enumerable.Range(0, states.Count).Select(n => $"ss{n}:SState"));
        lemmaParams.AddRange(Enumerable.Range(0, steps.Count).Select(n => $"sstep{n}:SStep"));
        lemmaParams.AddRange(GetExtraFormals());
        int i;
        str += String.Join(", ", lemmaParams);
        str += ")\n";
        str += "requires cr == GetConcurrentHoareLogicRequest()\n";
        str += $"requires ss == ss{states.Count-1}\n";
        str += $"requires ss.state.s.stop_reason.Armada_NotStopped?\n";
        str += $"requires StraightlineSpecInit(cr, ss0, tid, {procName})\n";
        for (i = 0; i < steps.Count; ++i) {
          str += $"requires StraightlineSpecNext(cr, ss{i}, ss{i+1}, sstep{i}, tid, {procName})\n";
        }
        str += AssumeIntroHelpers.GetCommonPathRequiresString(pgp.symbolsLow, methodName, states, steps, visitedLoops, false, UseVisitedLoops, true);
        str += GetExtraRequires();
        str += GetEnsures(false);
        str += "{\n";
        str += GetPathLemmaBody();
        str += "}\n";
        pgp.AddLemma(str, "path_" + pathName);
      }

      public void GeneratePathBehaviorLemma()
      {
        var lemmaType = GetLemmaType();
        var lemmaName = $"lemma_{lemmaType}PathBehaviorLemma_" + pathName;
        var procName = "LProcName_" + methodName;
        var lemmaParams = new List<string> { "cr:CHLRequest", "b:AnnotatedBehavior<SState, SStep>", "tid:Armada_ThreadHandle", "ss:SState" };
        lemmaParams.AddRange(GetExtraFormals());
        var str = "lemma " + lemmaName + "(" + String.Join(", ", lemmaParams) + ")\n";
        str += "requires cr == GetConcurrentHoareLogicRequest()\n";
        str += $"requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, {procName}))\n";
        str += $"requires |b.states| == {states.Count}\n";
        str += $"requires ss == b.states[{states.Count-1}]\n";
        str += "requires ss.state.s.stop_reason.Armada_NotStopped?\n";
        str += AssumeIntroHelpers.GetCommonPathRequiresString(pgp.symbolsLow, methodName, states, steps, visitedLoops, true, UseVisitedLoops, true);
        str += GetExtraRequires();
        str += GetEnsures(true);
        str += "{";
        str += $"  var sspec := GetStraightlineSpec(cr, tid, {procName});\n";
        for (int i = 0; i < steps.Count; ++i) {
          str += $@"
            var n{i} := {i};
            assert ActionTuple(b.states[n{i}], b.states[n{i}+1], b.trace[n{i}]) in sspec.next;
            assert StraightlineSpecNext(cr, b.states[n{i}], b.states[n{i}+1], b.trace[n{i}], tid, {procName});
          ";
        }
        var callParams = new List<string> { "cr", "tid", "ss" };
        callParams.AddRange(Enumerable.Range(0, states.Count).Select(n => $"b.states[{n}]"));
        callParams.AddRange(Enumerable.Range(0, steps.Count).Select(n => $"b.trace[{n}]"));
        callParams.AddRange(GetExtraInvocationParameters());
        var callParamsJoined = String.Join(", ", callParams);
        str += $"  lemma_{lemmaType}PathLemma_{AssumeIntroProofGenerator.GetPathName(methodName, states, branches)}({callParamsJoined});\n";
        str += "}";
        pgp.AddLemma(str, "path_" + pathName);
      }
    }

    public class SpecificGlobalInvariantPathLemmaGenerator : PathLemmaGenerator
    {
      private string invariantName;
      private string invariantFullPath;

      public SpecificGlobalInvariantPathLemmaGenerator(string i_invariantName, string i_invariantFullPath,
                                                       ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                       List<PCNode> i_states,
                                                       List<StepDescriptor> i_steps, Dictionary<ArmadaPC, int> i_visitedLoops,
                                                       List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        invariantName = i_invariantName;
        invariantFullPath = i_invariantFullPath;
      }

      protected override string GetLemmaType()
      {
        return "SpecificGlobalInv_" + invariantName + "_";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override string GetEnsures(bool behavior)
      {
        return $"ensures {invariantFullPath}(s')\n";
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
          requires s'.s.stop_reason.Armada_NotStopped?
        ";
      }
    }

    public class SpecificLocalInvariantPathLemmaGenerator : PathLemmaGenerator
    {
      private string invariantName;

      public SpecificLocalInvariantPathLemmaGenerator(string i_invariantName, ProofGenerationParams i_pgp, string i_pathName,
                                                      string i_methodName, List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                      Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        invariantName = i_invariantName;
      }

      protected override string GetLemmaType()
      {
        return "SpecificLocalInv_" + invariantName + "_";
      }

      protected override string GetEnsures(bool behavior)
      {
        return $"ensures {invariantName}(ss.state, tid)\n";
      }
    }

    public class SpecificYieldPredicatePathLemmaGenerator : PathLemmaGenerator
    {
      private string predicateName;
      private string predicateFullPath;

      public SpecificYieldPredicatePathLemmaGenerator(string i_predicateName, string i_predicateFullPath,
                                                      ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                      List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                      Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        predicateName = i_predicateName;
        predicateFullPath = i_predicateFullPath;
      }

      protected override string GetLemmaType()
      {
        return "SpecificYieldPredicateForOtherActor_" + predicateName + "_";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "other_tid:Armada_ThreadHandle", "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override string GetEnsures(bool behavior)
      {
        return $"ensures {predicateFullPath}(ss.state, s', other_tid)\n";
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
          requires tid != other_tid
          requires s'.s.stop_reason.Armada_NotStopped?
          requires other_tid in ss.state.s.threads
        ";
      }
    }

    public class GlobalInvariantsPathLemmaGenerator : PathLemmaGenerator
    {
      private Dictionary<string, string> globalInvariantNames;

      public GlobalInvariantsPathLemmaGenerator(Dictionary<string, string> i_globalInvariantNames,
                                                ProofGenerationParams i_pgp, string i_pathName, string i_methodName, List<PCNode> i_states,
                                                List<StepDescriptor> i_steps, Dictionary<ArmadaPC, int> i_visitedLoops,
                                                List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        globalInvariantNames = i_globalInvariantNames;
      }

      protected override string GetLemmaType()
      {
        return "GlobalInvariants";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures cr.global_inv(s')\n";
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
        ";
      }

      protected override string GetPathLemmaBody()
      {
        string str = "if s'.s.stop_reason.Armada_NotStopped? {";
        var callParams = new List<string> { "cr", "tid", "ss" };
        callParams.AddRange(Enumerable.Range(0, states.Count).Select(n => $"ss{n}"));
        callParams.AddRange(Enumerable.Range(0, steps.Count).Select(n => $"sstep{n}"));
        callParams.Add("s'");
        callParams.Add("step");
        var callParamsJoined = String.Join(", ", callParams);
        var pathName = AssumeIntroProofGenerator.GetPathName(methodName, states, branches);
        foreach (var globalInvariantPair in globalInvariantNames)
        {
          str += $"  lemma_SpecificGlobalInv_{globalInvariantPair.Key}_PathLemma_{pathName}({callParamsJoined});\n";
        }
        str += "}";
        return str;
      }

      public override void GeneratePathLemma()
      {
        foreach (var globalInvariantPair in globalInvariantNames)
        {
          var specificGlobalInvariantGenerator =
            new SpecificGlobalInvariantPathLemmaGenerator(globalInvariantPair.Key, globalInvariantPair.Value,
                                                          pgp, pathName, methodName, states, steps, visitedLoops,
                                                          branches);
          specificGlobalInvariantGenerator.GeneratePathLemma();
        }

        base.GeneratePathLemma();
      }

      protected override List<string> GetExtraInvocationParameters()
      {
        return new List<string> { "s'", "step" };
      }
    }

    public class LocalInvariantsPathLemmaGenerator : PathLemmaGenerator
    {
      private List<string> localInvariantNames;

      public LocalInvariantsPathLemmaGenerator(List<string> i_localInvariantNames,
                                               ProofGenerationParams i_pgp, string i_pathName, string i_methodName, List<PCNode> i_states,
                                               List<StepDescriptor> i_steps, Dictionary<ArmadaPC, int> i_visitedLoops,
                                               List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        localInvariantNames = i_localInvariantNames;
      }

      protected override string GetLemmaType()
      {
        return "LocalInvariants";
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures cr.local_inv(ss.state, tid)\n";
      }

      protected override string GetExtraRequires()
      {
        return "requires tid in cr.actor_info(ss.state)\n";
      }

      protected override string GetPathLemmaBody()
      {
        string str = "";
        var callParams = new List<string> { "cr", "tid", "ss" };
        callParams.AddRange(Enumerable.Range(0, states.Count).Select(n => $"ss{n}"));
        callParams.AddRange(Enumerable.Range(0, steps.Count).Select(n => $"sstep{n}"));
        var callParamsJoined = String.Join(", ", callParams);
        var pathName = AssumeIntroProofGenerator.GetPathName(methodName, states, branches);
        foreach (var localInvariantName in localInvariantNames)
        {
          str += $"  lemma_SpecificLocalInv_{localInvariantName}_PathLemma_{pathName}({callParamsJoined});\n";
        }
        return str;
      }

      public override void GeneratePathLemma()
      {
        foreach (var localInvariantName in localInvariantNames)
        {
          var specificLocalInvariantGenerator =
            new SpecificLocalInvariantPathLemmaGenerator(localInvariantName, pgp, pathName, methodName, states,
                                                         steps, visitedLoops, branches);
          specificLocalInvariantGenerator.GeneratePathLemma();
        }

        base.GeneratePathLemma();
      }
    }

    public class EnablementConditionsPathLemmaGenerator : PathLemmaGenerator
    {
      public EnablementConditionsPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                    List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                    Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "EnablementConditions";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override List<string> GetExtraInvocationParameters()
      {
        return new List<string> { "s'", "step" };
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ss.started
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures cr.enablement_condition(ss.state, tid)\n";
      }

      protected override string GetPathLemmaBody()
      {
        return @"
          lemma_StoreBufferAppendHasEffectOfAppendedEntryAlways_L();
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
        ";
      }
    }

    public class PreconditionsForCallsPathLemmaGenerator : PathLemmaGenerator
    {
      public PreconditionsForCallsPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                     List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                     Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "PreconditionsForCalls";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override List<string> GetExtraInvocationParameters()
      {
        return new List<string> { "s'", "step" };
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ss.started
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
          requires tid in cr.actor_info(ss.state)
          requires tid in cr.actor_info(s')
          requires var pc := cr.actor_info(ss.state)[tid].pc; cr.pc_type(pc).CallSite?
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return $@"
          ensures cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[tid].pc), s', tid)
        ";
      }
    }

    public class PreconditionsForForksPathLemmaGenerator : PathLemmaGenerator
    {
      public PreconditionsForForksPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                     List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                     Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "PreconditionsForForks";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "other_tid:Armada_ThreadHandle", "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override List<string> GetExtraInvocationParameters()
      {
        return new List<string> { "other_tid", "s'", "step" };
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ss.started
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
          requires tid in cr.actor_info(ss.state)
          requires tid in cr.actor_info(s')
          requires other_tid !in cr.actor_info(ss.state)
          requires other_tid in cr.actor_info(s')
          requires var pc := cr.actor_info(ss.state)[tid].pc; cr.pc_type(pc).ForkSite?
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return $@"
          ensures cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[other_tid].pc), s', other_tid)
        ";
      }
    }

    public class PostconditionsPathLemmaGenerator : PathLemmaGenerator
    {
      public PostconditionsPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName, List<PCNode> i_states,
                                              List<StepDescriptor> i_steps, Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "Postconditions";
      }

      protected override string GetExtraRequires()
      {
        return $@"
          requires tid in cr.actor_info(ss.state)
          requires var pc := cr.actor_info(ss.state)[tid].pc; cr.pc_type(pc).ReturnSite?
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        string initialState = (behavior ? "b.states[0]" : "ss0");
        return $"ensures cr.ensures_clauses(LProcName_{methodName}, {initialState}.state, ss.state, tid)\n";
      }
    }

    public class LoopModifiesClausesOnEntryPathLemmaGenerator : PathLemmaGenerator
    {
      public LoopModifiesClausesOnEntryPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                          List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                          Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "LoopModifiesClausesOnEntry";
      }

      protected override bool UseVisitedLoops { get { return true; } }

      protected override string GetExtraRequires()
      {
        return @"
          requires tid in cr.actor_info(ss.state)
          requires var pc := cr.actor_info(ss.state)[tid].pc;
                   cr.pc_type(pc).LoopHead? && pc in cr.loop_modifies_clauses && pc !in ss.visited_loops
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures var pc := cr.actor_info(ss.state)[tid].pc; cr.loop_modifies_clauses[pc](ss.state, ss.state, tid)\n";
      }
    }

    public class LoopModifiesClausesOnJumpBackPathLemmaGenerator : PathLemmaGenerator
    {
      public LoopModifiesClausesOnJumpBackPathLemmaGenerator(ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                             List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                             Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
      }

      protected override string GetLemmaType()
      {
        return "LoopModifiesClausesOnJumpBack";
      }

      protected override bool UseVisitedLoops { get { return true; } }

      protected override string GetExtraRequires()
      {
        return @"
          requires tid in cr.actor_info(ss.state)
          requires var pc := cr.actor_info(ss.state)[tid].pc;
                   cr.pc_type(pc).LoopHead? && pc in cr.loop_modifies_clauses && pc in ss.visited_loops
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures var pc := cr.actor_info(ss.state)[tid].pc; cr.loop_modifies_clauses[pc](ss.visited_loops[pc], ss.state, tid)\n";
      }
    }

    public class YieldPredicateForOtherActorPathLemmaGenerator : PathLemmaGenerator
    {
      private Dictionary<string, string> yieldPredicateNames;

      public YieldPredicateForOtherActorPathLemmaGenerator(Dictionary<string, string> i_yieldPredicateNames,
                                                           ProofGenerationParams i_pgp, string i_pathName, string i_methodName,
                                                           List<PCNode> i_states, List<StepDescriptor> i_steps,
                                                           Dictionary<ArmadaPC, int> i_visitedLoops, List<bool> i_branches)
        : base(i_pgp, i_pathName, i_methodName, i_states, i_steps, i_visitedLoops, i_branches)
      {
        yieldPredicateNames = i_yieldPredicateNames;
      }

      protected override string GetLemmaType()
      {
        return "YieldPredicateForOtherActor";
      }

      protected override List<string> GetExtraFormals()
      {
        return new List<string> { "other_tid:Armada_ThreadHandle", "s':LPlusState", "step:L.Armada_TraceEntry" };
      }

      protected override List<string> GetExtraInvocationParameters()
      {
        return new List<string> { "other_tid", "s'", "step" };
      }

      protected override string GetExtraRequires()
      {
        return @"
          requires ss.started
          requires ActionTuple(ss.state, s', step) in cr.spec.next
          requires cr.idmap(step).Some?
          requires cr.idmap(step).v == tid
          requires tid != other_tid
        ";
      }

      protected override string GetEnsures(bool behavior)
      {
        return "ensures cr.yield_pred(ss.state, s', other_tid)\n";
      }

      protected override string GetPathLemmaBody()
      {
        string str = @"
          var s := ss.state;
          if s'.s.stop_reason.Armada_NotStopped? {
            assert s.s.stop_reason.Armada_NotStopped?;
          }
          if other_tid in s.s.threads {
            assert other_tid in s'.s.threads;
            assert s'.s.threads[other_tid].pc == s.s.threads[other_tid].pc;
            assert s'.s.threads[other_tid].stack == s.s.threads[other_tid].stack;
          }
          if s'.s.stop_reason.Armada_NotStopped? && other_tid in s.s.threads {
        ";
        var callParams = new List<string> { "cr", "tid", "ss" };
        callParams.AddRange(Enumerable.Range(0, states.Count).Select(n => $"ss{n}"));
        callParams.AddRange(Enumerable.Range(0, steps.Count).Select(n => $"sstep{n}"));
        callParams.Add("other_tid");
        callParams.Add("s'");
        callParams.Add("step");
        var callParamsJoined = String.Join(", ", callParams);
        var pathName = AssumeIntroProofGenerator.GetPathName(methodName, states, branches);
        foreach (var yieldPredicatePair in yieldPredicateNames)
        {
          str += $"  lemma_SpecificYieldPredicateForOtherActor_{yieldPredicatePair.Key}_PathLemma_{pathName}({callParamsJoined});\n";
        }
        str += "}";
        return str;
      }

      public override void GeneratePathLemma()
      {
        foreach (var yieldPredicatePair in yieldPredicateNames)
        {
          var specificYieldPredicateGenerator =
            new SpecificYieldPredicatePathLemmaGenerator(yieldPredicatePair.Key, yieldPredicatePair.Value,
                                                         pgp, pathName, methodName, states, steps, visitedLoops, branches);
          specificYieldPredicateGenerator.GeneratePathLemma();
        }

        base.GeneratePathLemma();
      }
    }

    public class AssumeIntroPCNodeVisitor : IPCNodeVisitor
    {
      public readonly AssumeIntroProofGenerator proofGenerator;

      public AssumeIntroPCNodeVisitor(AssumeIntroProofGenerator i_proofGenerator)
      {
        proofGenerator = i_proofGenerator;
      }

      public void Visit(string methodName, List<PCNode> states, List<StepDescriptor> steps,
                        Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
      {
        var pathName = AssumeIntroProofGenerator.GetPathName(methodName, states, branches);
        proofGenerator.GeneratePathProofFile(pathName);
        proofGenerator.GeneratePerPathLemma(pathName, methodName, states, steps, visitedLoops, branches);
        proofGenerator.GeneratePathPrefixLemma(pathName, methodName, states, steps, visitedLoops, branches);
      }
    }

    private AssumeIntroStrategyDecl strategy;
    private Dictionary<string, string> globalInvariantNames;
    private Dictionary<string, string> yieldPredicateNames;
    private Dictionary<ArmadaPC, List<string>> localInvariantNames;
    private List<string> methodsWithPostconditions;
    private List<ArmadaPC> loopHeads;
    private HashSet<ArmadaPC> pcsWithEnablingConditions;
    private ProofFile pathPrefixFile;
    private ProofFile defsFile;

    public AssumeIntroProofGenerator(ProofGenerationParams i_pgp, AssumeIntroStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      globalInvariantNames = new Dictionary<string, string>();
      yieldPredicateNames = new Dictionary<string, string>();
      localInvariantNames = new Dictionary<ArmadaPC, List<string>>();
      methodsWithPostconditions = new List<string>();
      loopHeads = new List<ArmadaPC>();
      pcsWithEnablingConditions = new HashSet<ArmadaPC>();
      pathPrefixFile = null;
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence())
      {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofGivenMap();
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateConcurrentHoareLogicRequest();
      GenerateLocalViewCommutativityLemmas();
      GenerateGenericStoreBufferLemmas_L();
      GenerateLemmasAboutGetNextState();
      GenerateProofThatCHLRequestIsValid();
      GenerateLemmasForAssumeIntroProof();
      GenerateFinalProof();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/ConcurrentHoareLogic.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("ConcurrentHoareLogicSpecModule");
      pgp.MainProof.AddImport("ConcurrentHoareLogicModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.MainProof.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy",
                                     "GenericArmadaLemmasModule");
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC Info
    ////////////////////////////////////////////////////////////////////////

    private void GeneratePCToProc()
    {
      string str = @"
        function PCToProc(pc:L.Armada_PC) : LProcName
        {
          match pc
      ";
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => LProcName_{pc.methodName}";
      }
      str += "}";
      pgp.AddFunction(str, "defs");
    }

    private void GenerateIsEntryPoint()
    {
      string str = @"
        predicate IsEntryPoint(pc:L.Armada_PC)
        {
          match pc
      ";
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => ";
        if (pc.instructionCount == 0)
        {
          str += "true\n";
        }
        else
        {
          str += "false\n";
        }
      }
      str += "}\n";
      pgp.AddPredicate(str, "defs");
    }

    enum PCType { Normal, Call, Fork, Return, LoopHead }

    private void GeneratePCType()
    {
      var pcType = new Dictionary<ArmadaPC, PCType>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        switch (nextRoutine.nextType)
        {
          case NextType.Call:
            {
              pcType[nextRoutine.pc] = PCType.Call;
            }
            break;

          case NextType.CreateThread:
            pcType[nextRoutine.pc] = PCType.Fork;
            break;

          case NextType.Update:
          case NextType.Malloc:
          case NextType.Calloc:
          case NextType.IfTrue:
          case NextType.IfFalse:
          case NextType.JumpPastElse:
          case NextType.WhileTrue:
          case NextType.WhileFalse:
          case NextType.WhileEnd:
          case NextType.WhileBreak:
          case NextType.WhileContinue:
          case NextType.Assert:
          case NextType.Somehow:
          case NextType.Join:
          case NextType.ExternStart:
          case NextType.ExternContinue:
          case NextType.ExternEnd:
            pcType[nextRoutine.pc] = PCType.Normal;
            break;

          case NextType.Return:
          case NextType.Terminate:
          case NextType.Tau:
            break;
        }
      }

      foreach (var pc in loopHeads) {
        pcType[pc] = PCType.LoopHead;
      }

      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        var methodInfo = pgp.symbolsLow.AllMethods.LookupMethod(methodName);
        foreach (var returnPC in methodInfo.ReturnPCs)
        {
          pcType[returnPC] = PCType.Return;
        }
      }

      string str = @"
        function GetPCType(pc:L.Armada_PC) : PCType<L.Armada_PC>
        {
          match pc
      ";
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $"      case {pc} => ";
        switch (pcType[pc])
        {
          case PCType.Normal:
            str += "NormalPC";
            break;
          case PCType.Call:
            str += "CallSite";
            break;
          case PCType.Fork:
            str += "ForkSite";
            break;
          case PCType.Return:
            str += "ReturnSite";
            break;
          case PCType.LoopHead:
            str += "LoopHead";
            break;
        }
        str += "\n";
      }
      str += "}";
      pgp.AddFunction(str, "defs");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Concurrent Hoare logic request
    ////////////////////////////////////////////////////////////////////////

    private void GenerateConcurrentHoareLogicRequest()
    {
      defsFile = pgp.proofFiles.CreateAuxiliaryProofFile("defs");
      defsFile.IncludeAndImportGeneratedFile("specs");
      defsFile.IncludeAndImportGeneratedFile("convert");
      defsFile.IncludeAndImportGeneratedFile("invariants");
      defsFile.IncludeAndImportGeneratedFile("utility");
      defsFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/ConcurrentHoareLogic.i.dfy");
      defsFile.AddImport("ConcurrentHoareLogicSpecModule");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      defsFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("defs");

      var lplusstate = AH.ReferToType("LPlusState");
      var handle = AH.ReferToType("Armada_ThreadHandle");
      var lstep = AH.ReferToType("L.Armada_TraceEntry");
      var lpc = AH.ReferToType("L.Armada_PC");
      var lproc = AH.ReferToType("LProcName");
      var chlrequest = AH.MakeGenericTypeSpecific("ConcurrentHoareLogicRequest", new List<Type> { lplusstate, handle, lstep, lpc, lproc });
      defsFile.AddTypeSynonymDecl("CHLRequest", chlrequest);
      var straightlineState = AH.MakeGenericTypeSpecific("StraightlineState", new List<Type> { lplusstate, lpc });
      defsFile.AddTypeSynonymDecl("SState", straightlineState);
      var straightlineStep = AH.MakeGenericTypeSpecific("StraightlineStep", new List<Type> { lplusstate, lstep });
      defsFile.AddTypeSynonymDecl("SStep", straightlineStep);

      var datatypeCtors = new List<DatatypeCtor>();
      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        datatypeCtors.Add(AH.MakeDatatypeCtor($"LProcName_{methodName}", new List<Formal>()));
      }
      defsFile.AddDatatypeDecl("LProcName", datatypeCtors);

      string str;

      str = @"
        function MapStepToThread(step:L.Armada_TraceEntry) : Option<Armada_ThreadHandle>
        {
          if step.Armada_TraceEntry_Tau? then None else Some(step.tid)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function GetThreadPCStack(t:L.Armada_Thread) : PCStack<L.Armada_PC>
        {
          PCStack(t.pc, MapSeqToSeq(t.stack, (e:L.Armada_ExtendedFrame) => e.return_pc))
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function ActorInfo(s:LPlusState) : imap<Armada_ThreadHandle, PCStack<L.Armada_PC>>
        {
          imap tid | tid in s.s.threads :: GetThreadPCStack(s.s.threads[tid])
        }
      ";
      pgp.AddFunction(str, "defs");

      GenerateLOneStepSpec(true);
      GeneratePCToProc();
      GenerateIsEntryPoint();
      ParseProgram();
      GeneratePCType();
      GenerateGlobalInvariant();
      GenerateLocalInvariant();
      GenerateEnablementCondition();
      GenerateYieldPredicate();
      GenerateRequiresClauses();
      GenerateEnsuresClauses();
      GenerateInvariantProof(pgp);

      str = @"
        predicate GenericLoopModifiesClause(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {
          && (s'.s.stop_reason.Armada_NotStopped? ==> s.s.stop_reason.Armada_NotStopped?)
          && (s'.s.stop_reason.Armada_NotStopped? && tid in s.s.threads && tid in s'.s.threads ==>
                s'.s.threads[tid].stack == s.s.threads[tid].stack)
        }
      ";
      pgp.AddPredicate(str, "defs");

      var mapLiteral = string.Join(", ", loopHeads.Select(pc => $"L.{pc} := LoopInvariant_{pc}"));
      str = $@"
        function GetLoopModifiesClauses() : map<L.Armada_PC, (LPlusState, LPlusState, Armada_ThreadHandle)->bool>
        {{
          map [{mapLiteral}]
        }}
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function GetConcurrentHoareLogicRequest() : CHLRequest
        {
          ConcurrentHoareLogicRequest(GetLOneStepSpec(), MapStepToThread, ActorInfo, PCToProc, IsEntryPoint, GetPCType, InductiveInv, GlobalInv, LocalInv, EnablementCondition, YieldPredicate, RequiresClauses, EnsuresClauses, GetLoopModifiesClauses())
        }
      ";
      pgp.AddFunction(str, "defs");
    }

    private void ParseProgram()
    {
      foreach (var methodName in pgp.symbolsHigh.MethodNames)
      {
        var methodInfo = pgp.symbolsHigh.AllMethods.LookupMethod(methodName);
        var method = methodInfo.method;
        TurnRequirementsIntoLocalPredicates(method);
        CreatePostconditionsPredicate(method);
        if (method.Body is null)
        {
          // PC 1 corresponds to the head of the loop that repeatedly checks for the postcondition
          var pc = new ArmadaPC(pgp.symbolsLow, methodName, 1);
          loopHeads.Add(pc);
          ProcessWhileStatementInvariants(pc, new List<MaybeFreeExpression>());
        }
        else
        {
          foreach (var stmt in methodInfo.ParsedBody) {
            if (stmt is ArmadaWhileStatement) {
              var s = (ArmadaWhileStatement)stmt;
              var lowPC = s.StartPC.CloneWithNewSymbolTable(pgp.symbolsLow);
              loopHeads.Add(lowPC);
              ProcessWhileStatementInvariants(lowPC, ((WhileStmt)s.Stmt).Invariants);
            }
          }
        }
      }
    }

    private List<Formal> GetFormalsForLocalPredicate()
    {
      return new List<Formal> { AH.MakeFormal("s", "LPlusState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
    }
    private List<Formal> GetFormalsForLocalTwoStatePredicate()
    {
      return new List<Formal> { AH.MakeFormal("s", "LPlusState"), AH.MakeFormal("s'", "LPlusState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
    }

    private string CreateStackCorrectAtStartPredicate(Method method)
    {
      var stackInvName = $"StackCorrectAtStart_{method.Name}";
      var splus = AH.MakeNameSegment("s", "LPlusState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var s = AH.MakeExprDotName(splus, "s", "LState");

      // predicate {stackInvName}(s:LPlusState, tid:Armada_ThreadHandle)
      // {
      //   s.s.stop_reason.Armada_NotStopped? ==>
      //     && tid in s.s.threads
      //     && s.s.threads[tid].top.Armada_StackFrame_{method.Name}?
      //     && s.s.threads[tid].pc.{initialPC}?
      //     && <for each initialized variable, that variable is initialized correctly>
      // }

      var preds = new List<Expression>();

      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      preds.Add(tid_in_threads);

      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      var top = AH.MakeExprDotName(thread, "top", AH.MakeStackFrameType());
      var method_running = AH.MakeExprDotName(top, $"Armada_StackFrame_{method.Name}?", new BoolType());
      preds.Add(method_running);

      var pc = AH.MakeExprDotName(thread, "pc", "L.Armada_PC");
      var initialPC = new ArmadaPC(pgp.symbolsLow, method.Name, 0);
      var pc_correct = AH.MakeExprDotName(pc, $"{initialPC}?", new BoolType());
      preds.Add(pc_correct);

      var smst = pgp.symbolsLow.GetMethodSymbolTable(method.Name);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new RequiresResolutionContext(s, tid, method.Name, pgp.symbolsLow, failureReporter, "L");
        var ty = pgp.symbolsLow.FlattenType(v.ty);
        var lhsRVal = v.GetRValue(v.InitialValue.tok, context);
        var rhsRVal = context.ResolveAsRValue(v.InitialValue);
        if (rhsRVal.UndefinedBehaviorAvoidance.CanCauseUndefinedBehavior) {
          preds.Add(rhsRVal.UndefinedBehaviorAvoidance.Expr);
        }

        preds.Add(AH.MakeEqExpr(lhsRVal.Val, rhsRVal.Val));
      }

      var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
      var s_not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
      var body = AH.MakeImpliesExpr(s_not_stopped, AH.CombineExpressionsWithAnd(preds));
      var formals = new List<Formal> { AH.MakeFormal("s", "LPlusState"), AH.MakeFormal("tid", "Armada_ThreadHandle") };
      var pred = AH.MakePredicate(stackInvName, formals, body);

      pgp.AddDefaultClassDecl(pred, "defs");
      return stackInvName;
    }

    private void TurnRequirementsIntoLocalPredicates(Method method)
    {
      var preconditionNames = new List<string>();

      var stackInvName = CreateStackCorrectAtStartPredicate(method);
      preconditionNames.Add(stackInvName);

      var splus = AH.MakeNameSegment("s", "LPlusState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var s = AH.MakeExprDotName(splus, "s", "LState");
      var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
      var s_not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      var top = AH.MakeExprDotName(thread, "top", AH.MakeStackFrameType());
      var method_running = AH.MakeExprDotName(top, $"Armada_StackFrame_{method.Name}?", new BoolType());
      var conditions = AH.CombineExpressionsWithAnd(new List<Expression> { s_not_stopped, tid_in_threads, method_running });

      var formals = GetFormalsForLocalPredicate();

      int reqCount = 0;
      foreach (var req in method.Req)
      {
        // predicate Precondition_{reqCount}_{method.Name}(s:LPlusState, tid:Armada_ThreadHandle)
        // {
        //   s.s.stop_reason.Armada_NotStopped? && tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_{method.Name}?
        //     ==> <things that prevent requires clause expression from crashing> && <requires clause>
        // }

        reqCount++;
        var reqName = $"Precondition_{reqCount}_{method.Name}";
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new RequiresResolutionContext(s, tid, method.Name, pgp.symbolsLow, failureReporter, "L");
        if (!failureReporter.Valid) {
          reqCount--;
          continue;
        }
        var rvalue = context.ResolveAsRValue(req.E);
        var e = rvalue.CanCauseUndefinedBehavior ? AH.MakeAndExpr(rvalue.UndefinedBehaviorAvoidance.Expr, rvalue.Val) : rvalue.Val;
        e = AH.MakeImpliesExpr(conditions, e);
        var fn = AH.MakePredicate(reqName, formals, e);
        pgp.AddDefaultClassDecl(fn, "defs");
        preconditionNames.Add(reqName);
      }

      var ultimatePredName = $"Preconditions_{method.Name}";
      string str = $"predicate {ultimatePredName}(s:LPlusState, tid:Armada_ThreadHandle) {{\n";
      bool first = true;
      foreach (var preconditionName in preconditionNames)
      {
        if (!first) { str += "&& "; }
        str += $"{preconditionName}(s, tid)\n";
        first = false;
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private Expression GetExpressionIndicatingThreadExistsInBothStates(Expression s, Expression s_prime, Expression tid)
    {
      var clauses = new List<Expression>();

      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      var threads_prime = AH.MakeExprDotName(s_prime, "threads", AH.MakeThreadsType());
      var tid_in_threads_prime = AH.MakeInExpr(tid, threads_prime);

      return AH.MakeAndExpr(tid_in_threads, tid_in_threads_prime);
    }

    private Expression GetExpressionIndicatingThreadIsInMethodInBothStates(Expression s, Expression s_prime, Expression tid,
                                                                           string methodName)
    {
      var clauses = new List<Expression>();

      var s_prime_stop_reason = AH.MakeExprDotName(s_prime, "stop_reason", "Armada_StopReason");
      var s_prime_not_stopped = AH.MakeExprDotName(s_prime_stop_reason, "Armada_NotStopped?", new BoolType());
      clauses.Add(s_prime_not_stopped);
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var tid_in_threads = AH.MakeInExpr(tid, threads);
      clauses.Add(tid_in_threads);
      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      var top = AH.MakeExprDotName(thread, "top", "Armada_StackFrame");
      var thread_running_method = AH.MakeExprDotName(top, $"Armada_StackFrame_{methodName}?", new BoolType());
      clauses.Add(thread_running_method);
      var threads_prime = AH.MakeExprDotName(s_prime, "threads", AH.MakeThreadsType());
      var tid_in_threads_prime = AH.MakeInExpr(tid, threads_prime);
      clauses.Add(tid_in_threads_prime);
      var thread_prime = AH.MakeSeqSelectExpr(threads_prime, tid, "Armada_Thread");
      var top_prime = AH.MakeExprDotName(thread_prime, "top", "Armada_StackFrame");
      var thread_prime_running_method = AH.MakeExprDotName(top_prime, $"Armada_StackFrame_{methodName}?", new BoolType());
      clauses.Add(thread_prime_running_method);

      return AH.CombineExpressionsWithAnd(clauses);
    }

    private void CreatePostconditionsPredicate(Method method)
    {
      var splus = AH.MakeNameSegment("s", "LPlusState");
      var splus_prime = AH.MakeNameSegment("s'", "LPlusState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");
      var s = AH.MakeExprDotName(splus, "s", "LState");
      var s_prime = AH.MakeExprDotName(splus_prime, "s", "LState");

      var clauses = new List<Expression>();

      // Add a clause indicating that the stack hasn't changed

      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      var stack = AH.MakeExprDotName(thread, "stack", AH.MakeStackType());
      var threads_prime = AH.MakeExprDotName(s_prime, "threads", AH.MakeThreadsType());
      var thread_prime = AH.MakeSeqSelectExpr(threads_prime, tid, "Armada_Thread");
      var stack_prime = AH.MakeExprDotName(thread_prime, "stack", AH.MakeStackType());
      clauses.Add(AH.MakeEqExpr(stack_prime, stack));

      // For each ensures clause, add a clause

      if (method.Ens != null) {
        foreach (var ens in method.Ens)
        {
          var failureReporter = new SimpleFailureReporter(pgp.prog);
          var context = new EnsuresResolutionContext(s, s_prime, tid, method.Name, pgp.symbolsLow, failureReporter, "L");
          if (!failureReporter.Valid) {
            continue;
          }
          var rvalue = context.ResolveAsRValue(ens.E);
          if (rvalue.CanCauseUndefinedBehavior)
          {
            clauses.Add(rvalue.UndefinedBehaviorAvoidance.Expr);
          }
          clauses.Add(rvalue.Val);
        }
      }

      // Create a post-condition two-state function out of the collected clauses

      var fnName = $"Postconditions_{method.Name}";
      var body = AH.CombineExpressionsWithAnd(clauses);
      var thread_in_method_in_both_states = GetExpressionIndicatingThreadIsInMethodInBothStates(s, s_prime, tid, method.Name);
      body = AH.MakeImpliesExpr(thread_in_method_in_both_states, body);
      var fn = AH.MakeFunction(fnName, GetFormalsForLocalTwoStatePredicate(), body);
      pgp.AddDefaultClassDecl(fn, "defs");
    }

    private void ProcessWhileStatementInvariants(ArmadaPC pc, List<MaybeFreeExpression> invariants)
    {
      var splus = AH.MakeNameSegment("s", "LPlusState");
      var splus_prime = AH.MakeNameSegment("s'", "LPlusState");
      var tid = AH.MakeNameSegment("tid", "Armada_ThreadHandle");

      var s = AH.MakeExprDotName(splus, "s", "LState");
      var s_prime = AH.MakeExprDotName(splus_prime, "s", "LState");
      var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
      var threads_prime = AH.MakeExprDotName(s_prime, "threads", AH.MakeThreadsType());
      var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
      var thread_prime = AH.MakeSeqSelectExpr(threads_prime, tid, "Armada_Thread");
      var top = AH.MakeExprDotName(thread, "top", AH.MakeStackFrameType());
      var top_prime = AH.MakeExprDotName(thread_prime, "top", AH.MakeStackFrameType());
      var stack = AH.MakeExprDotName(thread, "stack", AH.MakeStackType());
      var stack_prime = AH.MakeExprDotName(thread_prime, "stack", AH.MakeStackType());
      var method_running = AH.MakeExprDotName(top, $"Armada_StackFrame_{pc.methodName}?", new BoolType());
      var method_running_prime = AH.MakeExprDotName(top_prime, $"Armada_StackFrame_{pc.methodName}?", new BoolType());
      var stop_reason = AH.MakeExprDotName(s, "stop_reason", "Armada_StopReason");
      var stop_reason_prime = AH.MakeExprDotName(s_prime, "stop_reason", "Armada_StopReason");
      var not_stopped = AH.MakeExprDotName(stop_reason, "Armada_NotStopped?", new BoolType());
      var not_stopped_prime = AH.MakeExprDotName(stop_reason_prime, "Armada_NotStopped?", new BoolType());

      // predicate LoopInvariant_{pc}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
      // {
      //   s'.s.stop_reason.Armada_NotStopped? ==>
      //     && s.s.stop_reason.Armada_NotStopped?
      //     && tid in s.s.threads
      //     && tid in s'.s.threads
      //     && s.s.threads.top.Armada_StackFrame_{pc.methodName}?
      //     && s'.s.threads.top.Armada_StackFrame_{pc.methodName}?
      //     && s'.s.threads[tid].stack == s.s.threads[tid].stack
      //     && <Input and ExternOld variables unchanged>
      //     && <custom loop invariants>
      // }

      var preds = new List<Expression>();
      preds.Add(not_stopped);
      preds.Add(AH.MakeInExpr(tid, threads));
      preds.Add(AH.MakeInExpr(tid, threads_prime));
      preds.Add(method_running);
      preds.Add(method_running_prime);
      preds.Add(AH.MakeEqExpr(stack_prime, stack));

      var smst = pgp.symbolsLow.GetMethodSymbolTable(pc.methodName);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.varType == ArmadaVarType.Input || v.varType == ArmadaVarType.ExternOld))
      {
        var v_cur = AH.MakeExprDotName(top, $"{pc.methodName}'{v.name}", v.ty);
        var v_next = AH.MakeExprDotName(top_prime, $"{pc.methodName}'{v.name}", v.ty);
        preds.Add(AH.MakeEqExpr(v_cur, v_next));
      }

      foreach (var inv in invariants)
      {
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new EnsuresResolutionContext(s, s_prime, tid, pc.methodName, pgp.symbolsLow, failureReporter, "L");
        if (!failureReporter.Valid) {
          continue;
        }
        var rvalue = context.ResolveAsRValue(inv.E);
        var e = rvalue.CanCauseUndefinedBehavior ? AH.MakeAndExpr(rvalue.UndefinedBehaviorAvoidance.Expr, rvalue.Val) : rvalue.Val;
        preds.Add(e);
      }

      var body = AH.MakeImpliesExpr(not_stopped_prime, AH.CombineExpressionsWithAnd(preds));
      var fn = AH.MakePredicate($"LoopInvariant_{pc}", GetFormalsForLocalTwoStatePredicate(), body);
      pgp.AddDefaultClassDecl(fn, "defs");
    }

    private void GenerateLocalInvariant()
    {
      // predicate LocalInv(s:LPlusState, tid:Armada_ThreadHandle)
      // {
      //   s.s.stop_reason.Armada_NotStopped? && tid in s.s.threads ==>
      //     match s.s.threads[tid].pc
      //       case Armada_PC_main_0 => true
      //       case Armada_PC_main_1 => LocalInvariant_1_Armada_PC_main_1(s, tid) && LocalInvariant_2_Armada_PC_main_1(s, tid)
      //       ...
      // }

      var str = @"
        predicate LocalInv(s:LPlusState, tid:Armada_ThreadHandle)
        {
          s.s.stop_reason.Armada_NotStopped? && tid in s.s.threads ==>
            match s.s.threads[tid].pc
      ";
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        str += $"    case {pc} => ";
        if (localInvariantNames.ContainsKey(pc) && localInvariantNames[pc].Any()) {
          str += String.Join(" && ", localInvariantNames[pc].Select(name => name + "(s, tid)"));
        }
        else {
          str += "true";
        }
        str += "\n";
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateEnablementCondition()
    {
      // predicate EnablementCondition(s:LPlusState, tid:Armada_ThreadHandle)
      // {
      //   s.s.stop_reason.Armada_NotStopped? && tid in s.s.threads ==>
      //     match s.s.threads[tid].pc
      //       case {pc} => H.Armada_EnablingConditions_{pc}(ConvertTotalState_LPlusH(s), tid)
      //       ...
      //       <others> => true
      // }

      var str = @"
        predicate EnablementCondition(s:LPlusState, tid:Armada_ThreadHandle)
        {
          s.s.stop_reason.Armada_NotStopped? && tid in s.s.threads ==>
            match s.s.threads[tid].pc
      ";
      var pcs = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(pcs);
      foreach (var pc in pcs)
      {
        var methodInfo = pgp.symbolsHigh.AllMethods.LookupMethod(pc.methodName);
        var collector = methodInfo.GetEnablingConstraintCollector(pc);
        if (collector == null || collector.Empty)
        {
          str += $"    case {pc} => true\n";
        }
        else
        {
          str += $"    case {pc} => H.Armada_EnablingConditions_{pc}(ConvertTotalState_LPlusH(s), tid)\n";
          pcsWithEnablingConditions.Add(pc);
        }
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateGlobalInvariant()
    {
      string allInvClauses = "";
      string str;

      var userInvariants = pgp.symbolsLow.GlobalInvariants;

      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is CHLInvariantArmadaProofDecl) {
          var d = (CHLInvariantArmadaProofDecl)topDecl;
          var invKey = d.InvariantName;
          var invName = d.InvariantName;
          if (d.Code != null) {
            invName = $"UserInv_{invKey}";
            str = $@"
              predicate {invName}(s:LPlusState)
              {{
                { d.Code }
              }}
            ";
            pgp.AddPredicate(str, "defs");
          }
          else if (userInvariants.ContainsKey(invKey)) {
            var inv = userInvariants[invKey];
            invName = $"UserInv_{invKey}";
            str = $@"
              predicate {invName}(splus:LPlusState)
              {{
                L.{inv.TranslatedName}(splus.s)
              }}
              ";
            pgp.AddPredicate(str, "defs");
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No invariant named {invKey} found among the invariants");
            continue;
          }
          globalInvariantNames[invKey] = invName;
          allInvClauses += $"  && {invName}(splus)\n";
        }
      }

      if (allInvClauses.Length == 0) {
        allInvClauses = "true";
      }

      str = $@"
        predicate GlobalInv(splus:LPlusState)
        {{
          {allInvClauses}
        }}
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateYieldPredicate()
    {
      string allYieldClauses = "";
      string str;

      var userYPs = pgp.symbolsLow.YieldPredicates;

      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is CHLYieldPredicateArmadaProofDecl) {
          var d = (CHLYieldPredicateArmadaProofDecl)topDecl;
          var ypKey = d.YieldPredicateName;
          var ypName = d.YieldPredicateName;
          if (d.Code != null) {
            ypName = $"UserYP_{ypKey}";
            str = $@"
              predicate {ypName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              {{
                {d.Code}
              }}
            ";
            pgp.AddPredicate(str, "defs");
          }
          else if (userYPs.ContainsKey(ypKey)) {
            ypName = $"UserYP_{ypKey}";
            var yp = userYPs[ypKey];
            str = $@"
              predicate {ypName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              {{
                tid in s.s.threads && tid in s'.s.threads ==> L.{yp.TranslatedName}(s.s, s'.s, tid)
              }}
            ";
            pgp.AddPredicate(str, "defs");
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No yield predicate named {ypKey} found among the yield predicates");
            continue;
          }
          yieldPredicateNames[ypKey] = ypName;
          allYieldClauses += $"  && {ypName}(s, s', tid)\n";
        }
      }
      if (allYieldClauses.Length == 0) {
        allYieldClauses = "true";
      }

      str = $@"
        predicate YieldPredicate(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {{
            && (s'.s.stop_reason.Armada_NotStopped? ==> s.s.stop_reason.Armada_NotStopped?)
            && (tid in s.s.threads ==>
                  && tid in s'.s.threads
                  && s'.s.threads[tid].pc == s.s.threads[tid].pc
                  && s'.s.threads[tid].top == s.s.threads[tid].top
                  && s'.s.threads[tid].stack == s.s.threads[tid].stack)
            && (s'.s.stop_reason.Armada_NotStopped? && tid in s.s.threads && L.Armada_IsNonyieldingPC(s.s.threads[tid].pc) ==> s' == s)
            && (s'.s.stop_reason.Armada_NotStopped? && tid in s.s.threads ==> {allYieldClauses})
        }}
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateRequiresClauses()
    {
      var str = @"
        predicate RequiresClauses(proc:LProcName, s:LPlusState, tid:Armada_ThreadHandle)
        {
          match proc
      ";
      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        str += $"    case LProcName_{methodName} => Preconditions_{methodName}(s, tid)";
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateEnsuresClauses()
    {
      var str = @"
        predicate EnsuresClauses(proc:LProcName, s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {
          match proc
      ";
      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        str += $"    case LProcName_{methodName} => Postconditions_{methodName}(s, s', tid)";
      }
      str += "}";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateProofThatCHLRequestIsValid()
    {
      GenerateSpecSatisfiesProgramControlFlowLemmas();
      GenerateGlobalInvLemmas();
      GenerateYieldPredicateLemmas();
      GenerateInitialInvariantLemmas();
      GeneratePerPathLemmas();
      GenerateIsValidConcurrentHoareLogicRequest();
    }

    private void GenerateSpecSatisfiesProgramControlFlowLemmas()
    {
      string str = @"
        lemma lemma_SpecSatisfiesProgramControlFlowAtInitialization()
          ensures forall s, actor ::
                     && s in GetLOneStepSpec().init
                     && actor in ActorInfo(s)
                     ==> var PCStack(pc, stack) := ActorInfo(s)[actor];
                         && IsEntryPoint(pc)
                         && |stack| == 0
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_SpecSatisfiesProgramControlFlowAfterFork()
          ensures forall s, s', step, forked_actor ::
                    && ActionTuple(s, s', step) in GetLOneStepSpec().next
                    && forked_actor !in ActorInfo(s)
                    && forked_actor in ActorInfo(s')
                    ==> && MapStepToThread(step).Some?
                        && MapStepToThread(step).v in ActorInfo(s)
                        && GetPCType(ActorInfo(s)[MapStepToThread(step).v].pc).ForkSite?
                        && var PCStack(pc', stack') := ActorInfo(s')[forked_actor];
                        && IsEntryPoint(pc')
                        && |stack'| == 0
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_SpecSatisfiesProgramControlFlowOtherActorsUnaffected()
          ensures forall s, s', step, other_actor ::
                    && ActionTuple(s, s', step) in GetLOneStepSpec().next
                    && MapStepToThread(step) != Some(other_actor)
                    && other_actor in ActorInfo(s)
                    ==> && other_actor in ActorInfo(s')
                        && ActorInfo(s')[other_actor] == ActorInfo(s)[other_actor]
        {
        }
      ";
      pgp.AddLemma(str);

      GenerateSpecSatisfiesProgramControlFlowEffectOnStack();

      str = @"
        lemma lemma_SpecSatisfiesProgramControlFlow()
          ensures SpecSatisfiesProgramControlFlow(GetLOneStepSpec(), MapStepToThread, ActorInfo, PCToProc, IsEntryPoint, GetPCType)
        {
          lemma_SpecSatisfiesProgramControlFlowAtInitialization();
          lemma_SpecSatisfiesProgramControlFlowAfterFork();
          lemma_SpecSatisfiesProgramControlFlowOtherActorsUnaffected();
          lemma_SpecSatisfiesProgramControlFlowEffectOnStack();
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateSpecSatisfiesProgramControlFlowEffectOnStack()
    {
      string overallStr = @"
        lemma lemma_SpecSatisfiesProgramControlFlowEffectOnStack()
          ensures forall s, s', step ::
                     && MapStepToThread(step).Some?
                     && ActionTuple(s, s', step) in GetLOneStepSpec().next
                     ==> var actor := MapStepToThread(step).v;
                         && actor in ActorInfo(s)
                         && var PCStack(pc, stack) := ActorInfo(s)[actor];
                         && (|| (&& GetPCType(pc).CallSite?
                               && actor in ActorInfo(s')
                               && var PCStack(pc', stack') := ActorInfo(s')[actor];
                               && IsEntryPoint(pc')
                               && |stack'| > 0
                               && stack == stack'[1..]
                               && PCToProc(stack'[0]) == PCToProc(pc)
                               )
                            || (&& GetPCType(pc).ReturnSite?
                               && |stack| > 0
                               && actor in ActorInfo(s')
                               && var PCStack(pc', stack') := ActorInfo(s')[actor];
                               && pc' == stack[0]
                               && stack' == stack[1..]
                               )
                            || (&& GetPCType(pc).ReturnSite?
                               && |stack| == 0
                               // If the stack is empty when we return, the thread exits, which we model as no longer being in ActorInfo
                               && actor !in ActorInfo(s')
                               )
                            || (&& actor in ActorInfo(s')
                               && var PCStack(pc', stack') := ActorInfo(s')[actor];
                               && PCToProc(pc') == PCToProc(pc)
                               && stack' == stack
                               )
                            )
        {
          forall s, s', step |
              && MapStepToThread(step).Some?
              && ActionTuple(s, s', step) in GetLOneStepSpec().next
              ensures var actor := MapStepToThread(step).v;
                      && actor in ActorInfo(s)
                      && var PCStack(pc, stack) := ActorInfo(s)[actor];
                      && (|| (&& GetPCType(pc).CallSite?
                            && actor in ActorInfo(s')
                            && var PCStack(pc', stack') := ActorInfo(s')[actor];
                            && IsEntryPoint(pc')
                            && |stack'| > 0
                            && stack == stack'[1..]
                            && PCToProc(stack'[0]) == PCToProc(pc)
                            )
                         || (&& GetPCType(pc).ReturnSite?
                            && |stack| > 0
                            && actor in ActorInfo(s')
                            && var PCStack(pc', stack') := ActorInfo(s')[actor];
                            && pc' == stack[0]
                            && stack' == stack[1..]
                            )
                         || (&& GetPCType(pc).ReturnSite?
                            && |stack| == 0
                            // If the stack is empty when we return, the thread exits, which we model as no longer being in ActorInfo
                            && actor !in ActorInfo(s')
                            )
                         || (&& actor in ActorInfo(s')
                            && var PCStack(pc', stack') := ActorInfo(s')[actor];
                            && PCToProc(pc') == PCToProc(pc)
                            && stack' == stack
                            )
                         )
          {
            var actor := MapStepToThread(step).v;
            var PCStack(pc, stack) := ActorInfo(s)[actor];

            match step
      ";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        var nextRoutineName = nextRoutine.NameSuffix;
        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        overallStr += $@"
            case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) =>
              lemma_SpecSatisfiesProgramControlFlowEffectOnStack_{nextRoutineName}(s, s', step, actor, pc, stack);
        ";

        string str = $@"
                lemma lemma_SpecSatisfiesProgramControlFlowEffectOnStack_{nextRoutineName}(
                  s:LPlusState,
                  s':LPlusState,
                  step:L.Armada_TraceEntry,
                  actor:Armada_ThreadHandle,
                  pc:L.Armada_PC,
                  stack:seq<L.Armada_PC>
                  )
                  requires ActionTuple(s, s', step) in GetLOneStepSpec().next
                  requires step.Armada_TraceEntry_{nextRoutineName}?
                  requires MapStepToThread(step).Some?
                  requires actor == MapStepToThread(step).v
                  requires actor in ActorInfo(s)
                  requires PCStack(pc, stack) == ActorInfo(s)[actor]
        ";

        switch (nextRoutine.nextType)
        {
          case NextType.Call:
            {
              str += $@"
                  ensures  pc.{nextRoutine.pc}?
                  ensures  GetPCType(pc).CallSite?
                  ensures  actor in ActorInfo(s')
                  ensures  var PCStack(pc', stack') := ActorInfo(s')[actor];
                           || (&& IsEntryPoint(pc') // normal case
                               && |stack'| > 0
                               && stack == stack'[1..]
                               && PCToProc(stack'[0]) == PCToProc(pc))
                           || (&& PCToProc(pc') == PCToProc(pc) // crash case
                               && stack' == stack)
                {{
                  assert LPlus_NextOneStep(s, s', step);
                }}
              ";
            }
            break;

          case NextType.Return:
            {
              var calleeName = GetCalleeNameForCallStmt(nextRoutine.stmt);
              str += $@"
                  ensures  GetPCType(pc).ReturnSite?
                  ensures  |stack| > 0
                  ensures  actor in ActorInfo(s')
                  ensures  var PCStack(pc', stack') := ActorInfo(s')[actor];
                           || (&& pc' == stack[0] // normal case
                               && stack' == stack[1..])
                           || (&& PCToProc(pc') == PCToProc(pc) // crash case
                               && stack' == stack)
                {{
                  assert LPlus_NextOneStep(s, s', step);
                }}
              ";
            }
            break;

          case NextType.Terminate:
            {
              str += $@"
                  ensures  GetPCType(pc).ReturnSite?
                  ensures  |stack| == 0
                  ensures  actor !in ActorInfo(s')
                {{
                  assert LPlus_NextOneStep(s, s', step);
                }}
              ";
            }
            break;

          default:
            {
              str += @"
                ensures  actor in ActorInfo(s')
                ensures  var PCStack(pc', stack') := ActorInfo(s')[actor]; PCToProc(pc') == PCToProc(pc) && stack' == stack
              {
                assert LPlus_NextOneStep(s, s', step);
              }
              ";
            }
            break;
        }
        pgp.AddLemma(str);
      }

      overallStr += "          }\n}";
      pgp.AddLemma(overallStr);
    }

    private void GenerateGlobalInvLemmas()
    {
      string str;
      string lemmaInvocations = "";

      foreach (var globalInvariantPair in globalInvariantNames)
      {
        str = $@"
          lemma lemma_ActorlessActionsMaintainSpecificGlobalInv_{globalInvariantPair.Key}(
            s:LPlusState,
            s':LPlusState,
            step:L.Armada_TraceEntry
            )
            requires step.Armada_TraceEntry_Tau?
            requires InductiveInv(s)
            requires GlobalInv(s)
            requires LPlus_NextOneStep(s, s', step)
            requires L.Armada_Next_Tau(s.s, s'.s, step.tid)
            ensures  {globalInvariantPair.Value}(s')
          {{
          }}
        ";
        pgp.AddLemma(str);
        lemmaInvocations += $@"
          lemma_ActorlessActionsMaintainSpecificGlobalInv_{globalInvariantPair.Key}(s, s', step);
        ";
      }

      str = $@"
        lemma lemma_ActorlessActionsMaintainGlobalInv(
          s:LPlusState,
          s':LPlusState,
          step:L.Armada_TraceEntry
          )
          requires step.Armada_TraceEntry_Tau?
          requires InductiveInv(s)
          requires GlobalInv(s)
          requires LPlus_NextOneStep(s, s', step)
          requires L.Armada_Next_Tau(s.s, s'.s, step.tid)
          ensures  GlobalInv(s')
        {{
          { lemmaInvocations }
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateYieldPredicateLemmas()
    {
      string str;

      foreach (var yieldPredicatePair in yieldPredicateNames)
      {
        string yieldPredicateName = yieldPredicatePair.Key;
        string fullyQualifiedYPName = yieldPredicatePair.Value;

        str = $@"
          lemma lemma_YieldPredicateReflexive_{yieldPredicateName}(s:LPlusState, actor:Armada_ThreadHandle)
            requires s.s.stop_reason.Armada_NotStopped?
            requires actor in s.s.threads
            ensures {fullyQualifiedYPName}(s, s, actor)
          {{
          }}
        ";
        pgp.AddLemma(str);

        str = $@"
          lemma lemma_YieldPredicateTransitive_{yieldPredicateName}(s1:LPlusState, s2:LPlusState, s3:LPlusState, actor:Armada_ThreadHandle)
            requires s2.s.stop_reason.Armada_NotStopped?
            requires s3.s.stop_reason.Armada_NotStopped?
            requires actor in s1.s.threads
            requires actor in s2.s.threads
            requires actor in s3.s.threads
            requires {fullyQualifiedYPName}(s1, s2, actor)
            requires {fullyQualifiedYPName}(s2, s3, actor)
            ensures  {fullyQualifiedYPName}(s1, s3, actor)
          {{
          }}
        ";
        pgp.AddLemma(str);

        str = $@"
          lemma lemma_ActorlessActionsMaintainYieldPredicate_{yieldPredicateName}(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry,
                                                                                  actor:Armada_ThreadHandle)
            requires step.Armada_TraceEntry_Tau?
            requires InductiveInv(s)
            requires GlobalInv(s)
            requires LPlus_NextOneStep(s, s', step)
            requires L.Armada_Next_Tau(s.s, s'.s, step.tid)
            requires GlobalInv(s')
            ensures  {fullyQualifiedYPName}(s, s', actor)
          {{
          }}
        ";
        pgp.AddLemma(str);
      }

      str = @"
        lemma lemma_YieldPredicateReflexive()
          ensures YieldPredicateReflexive(YieldPredicate);
        {
          forall s, actor
            ensures YieldPredicate(s, s, actor)
          {
            if s.s.stop_reason.Armada_NotStopped? && actor in s.s.threads {
      ";
      foreach (var yieldPredicateName in yieldPredicateNames.Keys)
      {
        str += $"        lemma_YieldPredicateReflexive_{yieldPredicateName}(s, actor);";
      }
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_YieldPredicateTransitive()
          ensures YieldPredicateTransitive(YieldPredicate);
        {
          forall s1, s2, s3, actor | YieldPredicate(s1, s2, actor) && YieldPredicate(s2, s3, actor)
            ensures YieldPredicate(s1, s3, actor)
          {
            if s2.s.stop_reason.Armada_NotStopped? && s3.s.stop_reason.Armada_NotStopped? && actor in s1.s.threads && actor in s2.s.threads && actor in s3.s.threads {
      ";
      foreach (var yieldPredicateName in yieldPredicateNames.Keys)
      {
        str += $"        lemma_YieldPredicateTransitive_{yieldPredicateName}(s1, s2, s3, actor);";
      }
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_YieldPredicateDoesntAffectActorInfo()
          ensures YieldPredicateDoesntAffectActorInfo(ActorInfo, YieldPredicate);
        {
          forall s, s', actor | actor in ActorInfo(s) && YieldPredicate(s, s', actor)
            ensures actor in ActorInfo(s')
            ensures ActorInfo(s')[actor] == ActorInfo(s)[actor]
          {
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ActorlessActionsMaintainYieldPredicateAndGlobalInvariant(cr:CHLRequest)
          requires cr == GetConcurrentHoareLogicRequest()
          ensures ActorlessActionsMaintainYieldPredicateAndGlobalInvariant(cr)
        {
          forall s, s', step, actor
            | && cr.established_inv(s)
              && cr.global_inv(s)
              && ActionTuple(s, s', step) in cr.spec.next
              && cr.idmap(step).None?
            ensures YieldPredicate(s, s', actor)
            ensures GlobalInv(s')
          {
            assert step.Armada_TraceEntry_Tau?;
            assert InductiveInv(s);
            assert GlobalInv(s);
            assert LPlus_NextOneStep(s, s', step);
            assert L.Armada_Next_Tau(s.s, s'.s, step.tid);
            lemma_ActorlessActionsMaintainGlobalInv(s, s', step);
      ";
      foreach (var yieldPredicateName in yieldPredicateNames.Keys)
      {
        str += $@"
            lemma_ActorlessActionsMaintainYieldPredicate_{yieldPredicateName}(s, s', step, actor);
        ";
      }
      str += @"
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateInitialInvariantLemmas()
    {
      string str;
      string body = "";

      foreach (var globalInvariantName in globalInvariantNames)
      {
        str = $@"
          lemma lemma_GlobalInvariantSatisfiedInitially_{globalInvariantName.Key}(s:LPlusState)
            requires LPlus_Init(s)
            ensures  {globalInvariantName.Value}(s)
          {{
          }}
        ";
        pgp.AddLemma(str);

        body += $"lemma_GlobalInvariantSatisfiedInitially_{globalInvariantName.Key}(s);\n";
      }

      str = $@"
        lemma lemma_GlobalInvariantSatisfiedInitially(s:LPlusState)
          requires LPlus_Init(s)
          ensures  GlobalInv(s)
        {{
          {body}
        }}
      ";
      pgp.AddLemma(str);

      body = "";
      var initialPC = new ArmadaPC(pgp.symbolsLow, "main", 0);
      if (localInvariantNames.ContainsKey(initialPC)) {
        foreach (var localInvariantName in localInvariantNames[initialPC])
        {
          str = $@"
            lemma lemma_LocalInvariantSatisfiedInitially_{localInvariantName}(s:LPlusState, tid:Armada_ThreadHandle)
              requires LPlus_Init(s)
              requires tid in ActorInfo(s)
              ensures  {localInvariantName}(s, tid)
            {{
            }}
          ";
          pgp.AddLemma(str);

          body += $"lemma_LocalInvariantSatisfiedInitially_{localInvariantName}(s, tid);\n";
        }
      }

      str = $@"
        lemma lemma_LocalInvariantSatisfiedInitially(s:LPlusState, tid:Armada_ThreadHandle)
          requires LPlus_Init(s)
          requires tid in ActorInfo(s)
          ensures  LocalInv(s, tid)
        {{
          {body}
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RequiresClausesSatisfiedInitially(s:LPlusState, tid:Armada_ThreadHandle)
          requires LPlus_Init(s)
          requires tid in ActorInfo(s)
          ensures  RequiresClauses(LProcName_main, s, tid)
        {
          assert Preconditions_main(s, tid);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_DesiredInvariantsSatisfiedInitially(cr:CHLRequest)
          requires cr == GetConcurrentHoareLogicRequest()
          ensures  DesiredInvariantsSatisfiedInitially(cr)
        {
          forall s | s in cr.spec.init
            ensures cr.global_inv(s)
          {
            lemma_GlobalInvariantSatisfiedInitially(s);
          }
          forall s, actor | s in cr.spec.init && actor in cr.actor_info(s)
            ensures cr.local_inv(s, actor)
            ensures cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s)[actor].pc), s, actor)
          {
            lemma_LocalInvariantSatisfiedInitially(s, actor);
            lemma_RequiresClausesSatisfiedInitially(s, actor);
            assert cr.pc_to_proc(cr.actor_info(s)[actor].pc) == LProcName_main;
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateIsValidConcurrentHoareLogicRequest()
    {
      string str;

      str = @"
        lemma lemma_InductiveInvIsInvariantOfOneStepSpec()
          ensures IsInvariantPredicateOfSpec(InductiveInv, GetLOneStepSpec())
        {
          var spec := GetLOneStepSpec();
          forall s | s in spec.init
            ensures InductiveInv(s)
          {
            lemma_InitImpliesInductiveInv(s);
          }
          forall s, s', step | InductiveInv(s) && ActionTuple(s, s', step) in spec.next
            ensures InductiveInv(s')
          {
            lemma_NextOneStepMaintainsInductiveInv(s, s', step);
          }
          lemma_EstablishInvariantPredicatePure(InductiveInv, spec);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_IsValidConcurrentHoareLogicRequest(cr:CHLRequest)
          requires cr == GetConcurrentHoareLogicRequest()
          ensures  IsValidConcurrentHoareLogicRequest(cr)
        {
          lemma_InductiveInvIsInvariantOfOneStepSpec();
          lemma_SpecSatisfiesProgramControlFlow();
          lemma_YieldPredicateReflexive();
          lemma_YieldPredicateTransitive();
          lemma_YieldPredicateDoesntAffectActorInfo();
          lemma_ActorlessActionsMaintainYieldPredicateAndGlobalInvariant(cr);
          lemma_DesiredInvariantsSatisfiedInitially(cr);
          lemma_StraightlineSpecRequirements(cr);
        }
        ";
      pgp.AddLemma(str);
    }

    private void GeneratePathLemmasForAllMethods()
    {
      var visitor = new AssumeIntroPCNodeVisitor(this);
      foreach (var methodName in pgp.symbolsLow.MethodNames) {
        var methodInfo = pgp.symbolsLow.AllMethods.LookupMethod(methodName);
        PCGraph.Visit(pgp.symbolsLow, methodInfo, visitor);
      }
    }

    private static string GetPathName(string methodName, List<PCNode> states, List<bool> branches)
    {
      if (states.Count == 1) {
        return methodName + "_Prestart";
      }
      else {
        var finalPC = states[states.Count-1].PC;
        if (branches.Count == 0) {
          return methodName + "_" + finalPC.Name;
        }
        else {
          return methodName + "_" + String.Join("", branches.Select(b => b ? "T" : "F")) + "_" + finalPC.Name;
        }
      }
    }

    private void GeneratePathProofFile(string pathName)
    {
      string fileName = "path_" + pathName;
      var proofFile = pgp.proofFiles.CreateAuxiliaryProofFile(fileName);
      proofFile.IncludeAndImportGeneratedFile("specs");
      proofFile.IncludeAndImportGeneratedFile("defs");
      proofFile.IncludeAndImportGeneratedFile("utility");
      proofFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/ConcurrentHoareLogic.i.dfy");
      proofFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      proofFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy", "util_collections_seqs_s");
      proofFile.AddImport("ConcurrentHoareLogicSpecModule");

      pathPrefixFile.IncludeAndImportGeneratedFile(fileName);
    }

    private void GeneratePerPathLemma(string pathName, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                                      Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      PathLemmaGenerator g;

      var lemmaName = "lemma_PathBehaviorLemma_" + pathName;
      var procName = "LProcName_" + methodName;
      var str = "lemma " + lemmaName + "(cr:CHLRequest, b:AnnotatedBehavior<SState, SStep>, tid:Armada_ThreadHandle, ss:SState)\n";
      str += "requires cr == GetConcurrentHoareLogicRequest()\n";
      str += $"requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, {procName}))\n";
      str += $"requires |b.states| == {states.Count}\n";
      str += $"requires ss == b.states[{states.Count-1}]\n";
      str += "requires ss.state.s.stop_reason.Armada_NotStopped?\n";
      str += AssumeIntroHelpers.GetCommonPathRequiresString(pgp.symbolsLow, methodName, states, steps, visitedLoops, true, true, true);
      str += $"ensures StraightlineBehaviorSatisfiesAllConditions(cr, b, tid, LProcName_{methodName})\n";
      str += "{";
      str += "var pc := cr.actor_info(ss.state)[tid].pc;\n";

      g = new GlobalInvariantsPathLemmaGenerator(globalInvariantNames, pgp, pathName, methodName, states, steps, visitedLoops, branches);
      g.GenerateLemmas();

      var ss = states[states.Count-1];
      var pc = ss.PC;

      str += $@"
        forall s', step |
          && ActionTuple(ss.state, s', step) in cr.spec.next
          && cr.idmap(step).Some?
          && cr.idmap(step).v == tid
          ensures cr.global_inv(s')
        {{
          lemma_GlobalInvariantsPathBehaviorLemma_{pathName}(cr, b, tid, ss, s', step);
        }}
      ";

      str += $@"
        forall s', step |
          && ss.started
          && ActionTuple(ss.state, s', step) in cr.spec.next
          && cr.idmap(step).Some?
          && cr.idmap(step).v == tid
          ensures cr.enablement_condition(ss.state, tid)
        {{
      ";
      if (pcsWithEnablingConditions.Contains(pc)) {
        g = new EnablementConditionsPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
        g.GenerateLemmas();
        str += $"          lemma_EnablementConditionsPathBehaviorLemma_{pathName}(cr, b, tid, ss, s', step);\n";
      }
      else {
        str += "          assert EnablementCondition(ss.state, tid);\n";
      }
      str += "}\n";

      if (localInvariantNames.ContainsKey(pc)) {
        g = new LocalInvariantsPathLemmaGenerator(localInvariantNames[pc], pgp, pathName, methodName, states,
                                                  steps, visitedLoops, branches);
        g.GenerateLemmas();
        str += $"  lemma_LocalInvariantsPathBehaviorLemma_{pathName}(cr, b, tid, ss);\n";
      }
      else {
        str += "  assert LocalInv(ss.state, tid);\n";
      }

      str += @"
        forall s', step |
          && ss.started
          && ActionTuple(ss.state, s', step) in cr.spec.next
          && cr.idmap(step).Some?
          && cr.idmap(step).v == tid
          && tid in cr.actor_info(ss.state)
          && tid in cr.actor_info(s')
          && cr.pc_type(pc).CallSite?
          ensures cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[tid].pc), s', tid)
        {
      ";

      if (ss is NormalPCNode && ((NormalPCNode)ss).Next != null && ((NormalPCNode)ss).Next.nextType == NextType.Call) {
        g = new PreconditionsForCallsPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
        g.GenerateLemmas();
        str += $"    lemma_PreconditionsForCallsPathBehaviorLemma_{pathName}(cr, b, tid, ss, s', step);\n";
      }
      else {
        str += "    assert !cr.pc_type(pc).CallSite?;\n";
      }
      str += "}\n";

      str += @"
        forall other_tid, s', step |
          && ss.started
          && ActionTuple(ss.state, s', step) in cr.spec.next
          && cr.idmap(step).Some?
          && cr.idmap(step).v == tid
          && tid in cr.actor_info(ss.state)
          && tid in cr.actor_info(s')
          && other_tid !in cr.actor_info(ss.state)
          && other_tid in cr.actor_info(s')
          && cr.pc_type(pc).ForkSite?
          ensures cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[other_tid].pc), s', other_tid)
        {
      ";
      if (ss is NormalPCNode && ((NormalPCNode)ss).Next != null && ((NormalPCNode)ss).Next.nextType == NextType.CreateThread) {
        g = new PreconditionsForForksPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
        g.GenerateLemmas();
        str += $"    lemma_PreconditionsForForksPathBehaviorLemma_{pathName}(cr, b, tid, ss, other_tid, s', step);\n";
      }
      else {
        str += "    assert !cr.pc_type(pc).ForkSite?;\n";
      }
      str += "}\n";

      str += @"
        if ss.started && tid in cr.actor_info(ss.state) && cr.pc_type(pc).ReturnSite? {
      ";
      if (ss is ReturningPCNode) {
        g = new PostconditionsPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
        g.GenerateLemmas();
        str += $"lemma_PostconditionsPathBehaviorLemma_{pathName}(cr, b, tid, ss);\n";
        str += $"assert last(b.states) == b.states[{states.Count - 1}];\n";
      }
      else if (ss is StartingPCNode) {
        str += "assert !ss.started;\n";
      }
      else {
        str += "assert !cr.pc_type(pc).ReturnSite?;\n";
      }
      str += "}\n";

      str += @"
          if && tid in cr.actor_info(ss.state)
             && cr.pc_type(pc).LoopHead?
             && pc in cr.loop_modifies_clauses {
      ";
      if (loopHeads.Contains(ss.PC)) {
        if (visitedLoops.ContainsKey(ss.PC) && visitedLoops[ss.PC] >= 0) {
          g = new LoopModifiesClausesOnJumpBackPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
          g.GenerateLemmas();

          str += $@"
             assert pc in ss.visited_loops;
             lemma_LoopModifiesClausesOnJumpBackPathBehaviorLemma_{pathName}(cr, b, tid, ss);
          ";
        }
        else {
          g = new LoopModifiesClausesOnEntryPathLemmaGenerator(pgp, pathName, methodName, states, steps, visitedLoops, branches);
          g.GenerateLemmas();

          str += $@"
             assert pc !in ss.visited_loops;
             lemma_LoopModifiesClausesOnEntryPathBehaviorLemma_{pathName}(cr, b, tid, ss);
          ";
        }
      }
      else {
        str += "assert false;\n";
      }
      str += "}\n";

      g = new YieldPredicateForOtherActorPathLemmaGenerator(yieldPredicateNames, pgp, pathName, methodName, states, steps,
                                                            visitedLoops, branches);
      g.GenerateLemmas();

      str += $@"
        forall other_tid, s', step |
          && ss.started
          && ActionTuple(ss.state, s', step) in cr.spec.next
          && cr.idmap(step).Some?
          && cr.idmap(step).v == tid
          && tid != other_tid
          ensures cr.yield_pred(ss.state, s', other_tid)
        {{
          lemma_YieldPredicateForOtherActorPathBehaviorLemma_{pathName}(cr, b, tid, ss, other_tid, s', step);
        }}
      ";

      str += "}";
      pgp.AddLemma(str, "path_" + pathName);
    }

    private void GeneratePathPrefixLemma(string pathName, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                                         Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      var lemmaName = "lemma_PathPrefixLemma_" + pathName;
      var procName = "LProcName_" + methodName;
      var str = "lemma " + lemmaName + "(cr:CHLRequest, b:AnnotatedBehavior<SState, SStep>, tid:Armada_ThreadHandle)\n";
      str += "requires cr == GetConcurrentHoareLogicRequest()\n";
      str += $"requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, {procName}))\n";
      str += $"requires |b.states| >= {states.Count}\n";
      str += "requires last(b.states).state.s.stop_reason.Armada_NotStopped?\n";
      str += AssumeIntroHelpers.GetCommonPathRequiresString(pgp.symbolsLow, methodName, states, steps, visitedLoops, true, true, false);
      str += $"ensures  StraightlineBehaviorSatisfiesAllConditions(cr, b, tid, {procName})\n";
      str += "{\n";
      str += $"  var ss := b.states[{states.Count-1}];\n";
      str += $"  lemma_IfFinalSStateOKThenAnySStateOK(cr, b, tid, {procName}, {states.Count-1});\n";
      str += "  assert ss.state.s.stop_reason.Armada_NotStopped?;\n";

      str += $"  if |b.states| == {states.Count} {{\n";
      str += $"    lemma_PathBehaviorLemma_{pathName}(cr, b, tid, ss);\n";
      str += "    return;\n";
      str += "  }\n";

      str += $"  var sstep := b.trace[{steps.Count}];\n";
      str += $"  var ss' := b.states[{states.Count}];\n";
      str += $"  var sspec := GetStraightlineSpec(cr, tid, {procName});\n";

      str += $"  lemma_IfFinalSStateOKThenAnySStateOK(cr, b, tid, {procName}, {states.Count});\n";
      str += "  assert ss'.state.s.stop_reason.Armada_NotStopped?;\n";

      str += $"  var i := {states.Count-1};\n";
      str += $"  assert ActionTuple(b.states[i], b.states[i+1], b.trace[i]) in sspec.next;\n";
      str += $"  assert StraightlineSpecNext(cr, ss, ss', sstep, tid, {procName});\n";
      str += $"  lemma_AllButFirstSStateOfBehaviorStarted(cr, b, tid, {procName}, {states.Count-1});\n";

      var lastState = states[states.Count - 1];
      if (lastState is ReturningPCNode) {
        str += "  assert tid in ss'.state.s.threads;\n";
        str += "  var pc := ss'.state.s.threads[tid].pc;\n";
        str += "  assert cr.pc_type(pc).ReturnSite?;\n";
        str += "  assert false;\n";
      }
      else if (lastState is LoopRestartPCNode) {
        str += "  assert tid in ss'.state.s.threads;\n";
        str += "  var pc := ss'.state.s.threads[tid].pc;\n";
        str += "  assert pc in ss'.visited_loops;\n";
        str += "  assert false;\n";
      }
      else if (lastState is NormalPCNode || lastState is StartingPCNode) {
        var successor = (lastState is NormalPCNode) ? ((NormalPCNode)lastState).Successor : ((StartingPCNode)lastState).Successor;
        str += "  assert tid in ss'.state.s.threads;\n";
        str += "  var pc := ss'.state.s.threads[tid].pc;\n";
        str += $"  assert pc.{successor.PC}?;\n";
        var extendedStates = new List<PCNode>(states);
        extendedStates.Add(successor);
        var extendedPathName = GetPathName(methodName, extendedStates, branches);
        str += $"  lemma_PathPrefixLemma_{extendedPathName}(cr, b, tid);\n";
      }
      else if (lastState is IfPCNode || lastState is WhilePCNode) {
        var successorWhenTrue = (lastState is IfPCNode) ? ((IfPCNode)lastState).SuccessorWhenTrue : ((WhilePCNode)lastState).SuccessorWhenTrue;
        var successorWhenFalse = (lastState is IfPCNode) ? ((IfPCNode)lastState).SuccessorWhenFalse : ((WhilePCNode)lastState).SuccessorWhenFalse;

        var extendedStatesWhenTrue = new List<PCNode>(states);
        extendedStatesWhenTrue.Add(successorWhenTrue);
        var extendedStatesWhenFalse = new List<PCNode>(states);
        extendedStatesWhenFalse.Add(successorWhenFalse);
        var extendedBranchesWhenTrue = new List<bool>(branches);
        extendedBranchesWhenTrue.Add(true);
        var extendedBranchesWhenFalse = new List<bool>(branches);
        extendedBranchesWhenFalse.Add(false);
        var extendedPathNameWhenTrue = GetPathName(methodName, extendedStatesWhenTrue, extendedBranchesWhenTrue);
        var extendedPathNameWhenFalse = GetPathName(methodName, extendedStatesWhenFalse, extendedBranchesWhenFalse);

        str += "  assert tid in ss'.state.s.threads;\n";
        str += "  var pc := ss'.state.s.threads[tid].pc;\n";
        str += $"  if pc.{successorWhenTrue.PC}? {{\n";
        str += $"    lemma_PathPrefixLemma_{extendedPathNameWhenTrue}(cr, b, tid);\n";
        str += "  }\n";
        str += "  else {\n";
        str += $"    assert pc.{successorWhenFalse.PC}?;\n";
        str += $"    lemma_PathPrefixLemma_{extendedPathNameWhenFalse}(cr, b, tid);\n";
        str += "  }\n";
      }

      str += "}\n";
      pgp.AddLemma(str, "pathprefix");
    }

    private void GeneratePerPathLemmas()
    {
      pathPrefixFile = pgp.proofFiles.CreateAuxiliaryProofFile("pathprefix");
      pathPrefixFile.IncludeAndImportGeneratedFile("specs");
      pathPrefixFile.IncludeAndImportGeneratedFile("defs");
      pathPrefixFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/ConcurrentHoareLogic.i.dfy");
      pathPrefixFile.AddImport("ConcurrentHoareLogicSpecModule");
      pathPrefixFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy",
                                      "util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("pathprefix");
      GenerateFinalStraightlineLemmas();
      GenerateStraightlineBehaviorPredicates();
      GenerateStraightlineBehaviorLemmas();
      GeneratePathLemmasForAllMethods();
    }

    private void GenerateStraightlineBehaviorPredicates()
    {
      string str;

      str = @"
        predicate StraightlineBehaviorSatisfiesGlobalInvariants(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                actor:Armada_ThreadHandle, proc:LProcName)
        {
          forall s', step ::
              (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
              && var s := last(b.states).state;
              && ActionTuple(s, s', step) in cr.spec.next
              && cr.idmap(step).Some?
              && cr.idmap(step).v == actor
              )
              ==> cr.global_inv(s')
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesLocalInvariants(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                               actor:Armada_ThreadHandle, proc:LProcName)
        {
          AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc)) ==> cr.local_inv(last(b.states).state, actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesEnablementConditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                    actor:Armada_ThreadHandle, proc:LProcName)
        {
          forall s', step ::
              (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
               && last(b.states).started
               && var s := last(b.states).state;
               && ActionTuple(s, s', step) in cr.spec.next
               && cr.idmap(step).Some?
               && cr.idmap(step).v == actor
              )
              ==> cr.enablement_condition(last(b.states).state, actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesPreconditionsForCalls(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                     actor:Armada_ThreadHandle, proc:LProcName)
        {
          forall s', step ::
              (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
               && last(b.states).started
               && var s := last(b.states).state;
               && ActionTuple(s, s', step) in cr.spec.next
               && cr.idmap(step).Some?
               && cr.idmap(step).v == actor
               && actor in cr.actor_info(s)
               && actor in cr.actor_info(s')
               && var pc := cr.actor_info(s)[actor].pc;
               && cr.pc_type(pc).CallSite?
              )
              ==> cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[actor].pc), s', actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesPreconditionsForForks(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                     actor:Armada_ThreadHandle, proc:LProcName)
        {
          forall other_actor, s', step ::
              (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
               && last(b.states).started
               && var s := last(b.states).state;
               && ActionTuple(s, s', step) in cr.spec.next
               && cr.idmap(step).Some?
               && cr.idmap(step).v == actor
               && actor in cr.actor_info(s)
               && actor in cr.actor_info(s')
               && other_actor !in cr.actor_info(s)
               && other_actor in cr.actor_info(s')
               && var pc := cr.actor_info(s)[actor].pc;
               && cr.pc_type(pc).ForkSite?
               )
               ==> cr.requires_clauses(cr.pc_to_proc(cr.actor_info(s')[other_actor].pc), s', other_actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesPostconditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                              actor:Armada_ThreadHandle, proc:LProcName)
        {
          (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
           && last(b.states).started
           && var s := last(b.states).state;
           && actor in cr.actor_info(s)
           && var pc := cr.actor_info(s)[actor].pc;
           && cr.pc_type(pc).ReturnSite?
           )
           ==> cr.ensures_clauses(proc, b.states[0].state, last(b.states).state, actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                          actor:Armada_ThreadHandle, proc:LProcName)
        {
          (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
           && var s := last(b.states).state;
           && actor in cr.actor_info(s)
           && var pc := cr.actor_info(s)[actor].pc;
           && cr.pc_type(pc).LoopHead?
           && pc in cr.loop_modifies_clauses
           && pc !in last(b.states).visited_loops
           )
           ==> var s := last(b.states).state;
               var pc := cr.actor_info(s)[actor].pc;
               cr.loop_modifies_clauses[pc](s, s, actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                             actor:Armada_ThreadHandle, proc:LProcName)
        {
          (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
           && var s := last(b.states).state;
           && actor in cr.actor_info(s)
           && var pc := cr.actor_info(s)[actor].pc;
           && cr.pc_type(pc).LoopHead?
           && pc in cr.loop_modifies_clauses
           && pc in last(b.states).visited_loops
           )
           ==> var s := last(b.states).state;
               var pc := cr.actor_info(s)[actor].pc;
               cr.loop_modifies_clauses[pc](last(b.states).visited_loops[pc], s, actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesYieldPredicateForOtherActor(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                           actor:Armada_ThreadHandle, proc:LProcName)
        {
          forall other_actor, s', step ::
              (&& AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
               && last(b.states).started
               && var s := last(b.states).state;
               && ActionTuple(s, s', step) in cr.spec.next
               && cr.idmap(step).Some?
               && cr.idmap(step).v == actor
               && actor != other_actor)
              ==> cr.yield_pred(last(b.states).state, s', other_actor)
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StraightlineBehaviorSatisfiesAllConditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                             actor:Armada_ThreadHandle, proc:LProcName)
        {
          && StraightlineBehaviorSatisfiesGlobalInvariants(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesLocalInvariants(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesEnablementConditions(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesPreconditionsForCalls(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesPreconditionsForForks(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesPostconditions(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack(cr, b, actor, proc)
          && StraightlineBehaviorSatisfiesYieldPredicateForOtherActor(cr, b, actor, proc)
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateStraightlineBehaviorLemmas()
    {
      string str;

      str = @"
        lemma lemma_IfFinalSStateOKThenAnySStateOK(cr: CHLRequest, b:AnnotatedBehavior<SState, SStep>, tid:Armada_ThreadHandle,
                                                   proc:LProcName, i:int)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, proc))
          requires last(b.states).state.s.stop_reason.Armada_NotStopped?
          requires 0 <= i < |b.states|
          ensures  b.states[i].state.s.stop_reason.Armada_NotStopped?
          decreases |b.states| - i
        {
          if i == |b.states|-1 {
              assert b.states[i].state.s.stop_reason.Armada_NotStopped?;
              return;
          }

          var sspec := GetStraightlineSpec(cr, tid, proc);
          assert ActionTuple(b.states[i], b.states[i+1], b.trace[i]) in sspec.next;
          lemma_IfFinalSStateOKThenAnySStateOK(cr, b, tid, proc, i+1);
          assert b.states[i+1].state.s.stop_reason.Armada_NotStopped?;
          match b.trace[i]
              case StraightlineStepStart() =>
                  assert b.states[i].state.s.stop_reason.Armada_NotStopped?;
              case StraightlineStepNormal(post_stmt_state, _) =>
                  assert post_stmt_state.s.stop_reason.Armada_NotStopped?;
                  assert b.states[i].state.s.stop_reason.Armada_NotStopped?;
              case StraightlineStepCall(post_call_state, pre_return_state, post_return_state, _, _) =>
                  assert post_return_state.s.stop_reason.Armada_NotStopped?;
                  assert pre_return_state.s.stop_reason.Armada_NotStopped?;
                  assert post_call_state.s.stop_reason.Armada_NotStopped?;
                  assert b.states[i].state.s.stop_reason.Armada_NotStopped?;
              case StraightlineStepLoop(post_loops_state, post_guard_state, _) =>
                  assert post_guard_state.s.stop_reason.Armada_NotStopped?;
                  assert post_loops_state.s.stop_reason.Armada_NotStopped?;
                  assert b.states[i].state.s.stop_reason.Armada_NotStopped?;
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesGlobalInvariants(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                            actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesGlobalInvariants(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLocalInvariants(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                           actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesLocalInvariants(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesEnablementConditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                                actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesEnablementConditions(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPreconditionsForCalls(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                                 actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesPreconditionsForCalls(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPreconditionsForForks(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                                 actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesPreconditionsForForks(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPostconditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                          actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesPostconditions(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLoopModifiesClausesOnEntry(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                                      actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLoopModifiesClausesOnJumpBack(
          cr: CHLRequest,
          b: AnnotatedBehavior<SState, SStep>,
          actor:Armada_ThreadHandle,
          proc:LProcName
          )
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesYieldPredicateForOtherActor(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                                       actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesYieldPredicateForOtherActor(cr, b, actor, proc);
        {
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_IfFinalSStateNotOKThenBehaviorSatisfiesAllConditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                                         actor:Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, actor, proc))
          requires !last(b.states).state.s.stop_reason.Armada_NotStopped?
          ensures  StraightlineBehaviorSatisfiesAllConditions(cr, b, actor, proc);
        {
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesGlobalInvariants(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLocalInvariants(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesEnablementConditions(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPreconditionsForCalls(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPreconditionsForForks(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesPostconditions(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLoopModifiesClausesOnEntry(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesLoopModifiesClausesOnJumpBack(cr, b, actor, proc);
          lemma_IfFinalSStateNotOKThenBehaviorSatisfiesYieldPredicateForOtherActor(cr, b, actor, proc);
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_AllButFirstSStateOfBehaviorStarted(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>, tid: Armada_ThreadHandle,
                                                       proc: LProcName, i:int)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, proc))
          requires 0 <= i < |b.states|
          ensures  b.states[i].started == (i > 0)
        {
          if i == 0 {
              return;
          }
          var prev := i-1;
          var sspec := GetStraightlineSpec(cr, tid, proc);
          assert ActionTuple(b.states[prev], b.states[prev + 1], b.trace[prev]) in sspec.next;
          assert StraightlineSpecNext(cr, b.states[prev], b.states[prev + 1], b.trace[prev], tid, proc);
        }
      ";
      pgp.AddLemma(str, "pathprefix");
    }

    private void GenerateFinalStraightlineLemmas()
    {
      string elseClauses = String.Join("", pgp.symbolsLow.MethodNames.Select(methodName => $@"
        else if proc == LProcName_{methodName} {{
          lemma_PathPrefixLemma_{methodName}_Prestart(cr, b, tid);
        }}
        "));
      string str = $@"
        lemma lemma_StraightlineBehaviorSatisfiesAllConditions(cr: CHLRequest, b: AnnotatedBehavior<SState, SStep>,
                                                               tid: Armada_ThreadHandle, proc:LProcName)
          requires cr == GetConcurrentHoareLogicRequest()
          requires AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, proc))
          ensures  StraightlineBehaviorSatisfiesAllConditions(cr, b, tid, proc)
        {{
          if !last(b.states).state.s.stop_reason.Armada_NotStopped? {{
            lemma_IfFinalSStateNotOKThenBehaviorSatisfiesAllConditions(cr, b, tid, proc);
          }}
          {elseClauses}
        }}
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_StraightlineSpecPreservesGlobalInvariantOnTermination(cr:CHLRequest)
          requires cr == GetConcurrentHoareLogicRequest()
          ensures  StraightlineSpecPreservesGlobalInvariantOnTermination(cr)
        {
           forall s, s', step |
             && cr.established_inv(s)
             && cr.global_inv(s)
             && ActionTuple(s, s', step) in cr.spec.next
             && (forall any_actor :: any_actor !in cr.actor_info(s'))
             ensures cr.global_inv(s')
           {
             assert step.tid !in cr.actor_info(s');
             assert step.tid !in s'.s.threads;
           }
        }
      ";
      pgp.AddLemma(str, "pathprefix");

      str = @"
        lemma lemma_StraightlineSpecRequirements(cr: CHLRequest)
          requires cr == GetConcurrentHoareLogicRequest()
          ensures  StraightlineSpecRequirements(cr);
        {
          forall b, tid, proc | AnnotatedBehaviorSatisfiesSpec(b, GetStraightlineSpec(cr, tid, proc))
            ensures StraightlineBehaviorSatisfiesAllConditions(cr, b, tid, proc)
          {
            lemma_StraightlineBehaviorSatisfiesAllConditions(cr, b, tid, proc);
          }
          lemma_StraightlineSpecPreservesGlobalInvariantOnTermination(cr);
        }
      ";
      pgp.AddLemma(str, "pathprefix");
    }

    private void GenerateStateRefinerSatisfiesRelationLemma()
    {
      string str = @"
        lemma lemma_StateRefinerSatisfiesRelation(ls:LPlusState)
          requires InductiveInv(ls)
          requires GlobalInv(ls)
          ensures  RefinementPair(ls, ConvertTotalState_LPlusH(ls)) in GetLPlusHRefinementRelation()
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLInitImpliesHInitLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      var str = @"
        lemma lemma_LInitImpliesHInit(ls:LPlusState) returns (hconfig:H.Armada_Config)
          requires LPlus_Init(ls)
          ensures  H.Armada_InitConfig(ConvertTotalState_LPlusH(ls), hconfig)
        {
          var hs := ConvertTotalState_LPlusH(ls);
          hconfig := ConvertConfig_LH(ls.config);

          lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
          assert H.Armada_InitConfig(hs, hconfig);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLNextPlusEnablementConditionImpliesHNextLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var hNextRoutine = nextRoutineMap[nextRoutine];
      var hNextRoutineName = hNextRoutine.NameSuffix;

      string str = $@"
        lemma lemma_LNextPlusEnablementConditionImpliesHNext_{nextRoutineName}(ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires InductiveInv(ls)
            requires GlobalInv(ls)
            requires MapStepToThread(lstep).Some? ==>
                && var actor := MapStepToThread(lstep).v;
                && EnablementCondition(ls, actor)
                && LocalInv(ls, actor)
            ensures  H.Armada_NextOneStep(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertTraceEntry_LH(lstep))
        {{
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var tid := lstep.tid;
          var hstep := ConvertTraceEntry_LH(lstep);

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          assert H.Armada_ValidStep_{hNextRoutineName}(hs, tid{hstep_params});
          if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(ls.s, tid{lstep_params}) {{
            assert H.Armada_UndefinedBehaviorAvoidance_{hNextRoutineName}(hs, tid{hstep_params});
            var alt_hs' := H.Armada_GetNextState_{hNextRoutineName}(hs, tid{hstep_params});
            assert hs'.stop_reason == alt_hs'.stop_reason;
            if tid in hs'.threads {{
              assert hs'.threads[tid] == alt_hs'.threads[tid];
            }}
            assert hs'.threads == alt_hs'.threads;
            assert hs'.mem == alt_hs'.mem;
            assert hs' == alt_hs';
            assert H.Armada_Next_{hNextRoutineName}(hs, hs', tid{hstep_params});
          }}
          else {{
            assert !H.Armada_UndefinedBehaviorAvoidance_{hNextRoutineName}(hs, tid{hstep_params});
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLNextPlusEnablementConditionImpliesHNextLemmaForTauNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var hNextRoutineName = nextRoutine.NameSuffix;

      string str = $@"
        lemma lemma_LNextPlusEnablementConditionImpliesHNext_{nextRoutineName}(ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires InductiveInv(ls)
            requires GlobalInv(ls)
            requires MapStepToThread(lstep).Some? ==>
                && var actor := MapStepToThread(lstep).v;
                && EnablementCondition(ls, actor)
                && LocalInv(ls, actor)
            ensures  H.Armada_NextOneStep(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertTraceEntry_LH(lstep))
        {{
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var tid := lstep.tid;
          var hstep := ConvertTraceEntry_LH(lstep);

          var lentry := ls.s.threads[tid].storeBuffer[0];
          assert H.Armada_ValidStep_{nextRoutineName}(hs, tid{hstep_params});
          assert H.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(hs, tid{hstep_params});
          var hentry := hs.threads[tid].storeBuffer[0];
          var lmem := ls.s.mem;
          var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
          var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

          var alt_hs' := H.Armada_GetNextState_{nextRoutineName}(hs, tid{hstep_params});
          assert hs'.threads[tid].storeBuffer == alt_hs'.threads[tid].storeBuffer;
          assert hs'.threads[tid] == alt_hs'.threads[tid];
          assert hs'.threads == alt_hs'.threads;
          assert hs' == alt_hs';
          assert H.Armada_Next_{nextRoutineName}(hs, hs', tid{hstep_params});
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLNextPlusEnablementConditionImpliesHNextLemma()
    {
      var finalCases = "";
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var nextRoutineName = nextRoutine.NameSuffix;

        if (nextRoutine.nextType == NextType.Tau) {
          GenerateLNextPlusEnablementConditionImpliesHNextLemmaForTauNextRoutine(nextRoutine);
        }
        else {
          GenerateLNextPlusEnablementConditionImpliesHNextLemmaForNormalNextRoutine(nextRoutine);
        }

        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LNextPlusEnablementConditionImpliesHNext_{nextRoutineName}(ls, ls', lstep);";
      }

      string str = @"
        lemma lemma_LNextPlusEnablementConditionImpliesHNext(ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires InductiveInv(ls)
            requires GlobalInv(ls)
            requires MapStepToThread(lstep).Some? ==>
                && var actor := MapStepToThread(lstep).v;
                && EnablementCondition(ls, actor)
                && LocalInv(ls, actor)
            ensures  H.Armada_NextOneStep(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertTraceEntry_LH(lstep))
        {
          match lstep {
      ";
      str += finalCases;
      str += @"
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GeneratePerformCHLAssumeIntro()
    {
      string str;

      str = @"
        lemma lemma_LowAndHighMatchYielding()
          ensures forall pc:L.Armada_PC :: L.Armada_IsNonyieldingPC(pc) <==> H.Armada_IsNonyieldingPC(ConvertPC_LH(pc))
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma {:timeLimitMultiplier 2} lemma_PerformCHLAssumeIntroMultipleSubsteps(
          ub:AnnotatedBehavior<LPlusState, L.Armada_TraceEntry>,
          tau: bool,
          tid: Armada_ThreadHandle,
          ls:LPlusState,
          ls':LPlusState,
          lsteps:seq<L.Armada_TraceEntry>,
          hs:HState,
          hs':HState,
          hsteps:seq<H.Armada_TraceEntry>,
          lstates: seq<LPlusState>,
          hstates: seq<HState>
          )
          requires AnnotatedBehaviorSatisfiesSpec(ub, GetLOneStepSpec())
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> step.Armada_TraceEntry_Tau? == tau
          requires var s := last(ub.states).s;
                   s.stop_reason.Armada_NotStopped? ==>
                   (forall any_tid :: any_tid in s.threads && (any_tid != tid || tau) ==> !L.Armada_IsNonyieldingPC(s.threads[any_tid].pc))
          requires ls == last(ub.states)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires hs == ConvertTotalState_LPlusH(ls)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires |hsteps| == |lsteps|
          requires forall i :: 0 <= i < |lsteps| ==> hsteps[i] == ConvertTraceEntry_LH(lsteps[i])
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps)
          ensures  Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          ensures  |hstates| == |lstates|
          ensures  forall i :: 0 <= i < |lstates| ==> hstates[i] == ConvertTotalState_LPlusH(lstates[i])
          decreases |lsteps|
        {
          if |lsteps| > 0 {
            var ls_next := LPlus_GetNextStateAlways(ls, lsteps[0]);
            var ub' := AnnotatedBehavior(ub.states + [ls_next], ub.trace + [lsteps[0]]);
            var hs_next := ConvertTotalState_LPlusH(ls_next);
            assert hsteps[0] == ConvertTraceEntry_LH(lsteps[0]);
            lemma_EstablishLOneStepNext(tau, tid, ls, ls_next, lsteps[0]);
            assert forall any_tid :: any_tid in ls_next.s.threads && (any_tid != tid || tau)
                               ==> !L.Armada_IsNonyieldingPC(ls_next.s.threads[any_tid].pc);
            var cr := GetConcurrentHoareLogicRequest();
            lemma_IsValidConcurrentHoareLogicRequest(cr);
            lemma_ExtendStateNextSeqRight(ub.states, ub.trace, cr.spec.next, ls_next, lsteps[0]);
            lemma_AllCHLInvariantsHoldAtStep(cr, ub', |ub.trace|, lsteps[0].tid);
            lemma_LNextPlusEnablementConditionImpliesHNext(ls, ls_next, lsteps[0]);
            lemma_NextOneStepImpliesGetNextState_H(hs, hs_next, hsteps[0]);
            assert last(ub'.states) == ls_next;
            forall i | 0 <= i < |lsteps[1..]|
              ensures hsteps[1..][i] == ConvertTraceEntry_LH(lsteps[1..][i])
            {
              var iplus := 1+i;
              calc {
                hsteps[1..][i];
                  { lemma_IndexIntoDrop(hsteps, 1, i); }
                hsteps[iplus];
                ConvertTraceEntry_LH(lsteps[iplus]);
                  { lemma_IndexIntoDrop(lsteps, 1, i); }
                ConvertTraceEntry_LH(lsteps[1..][i]);
              }
            }
            var asf := LPlus_GetSpecFunctions();
            calc {
              lstates[1..];
                { lemma_ArmadaGetStateSequenceDrop(asf, ls, lsteps, lstates); }
              Armada_GetStateSequence(asf, asf.step_next(ls, lsteps[0]), lsteps[1..]);
              Armada_GetStateSequence(asf, ls_next, lsteps[1..]);
              Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls_next, lsteps[1..]);
            }
            lemma_PerformCHLAssumeIntroMultipleSubsteps(ub', tau, tid, ls_next, ls', lsteps[1..], hs_next, hs', hsteps[1..],
                                                        lstates[1..], hstates[1..]);
            forall i | 0 <= i < |lstates|
              ensures hstates[i] == ConvertTotalState_LPlusH(lstates[i])
            {
              if i > 0 {
                var iminus := i-1;
                calc {
                  hstates[i];
                    { lemma_IndexIntoDrop(hstates, 1, iminus); }
                  hstates[1..][iminus];
                  ConvertTotalState_LPlusH(lstates[1..][iminus]);
                    { lemma_IndexIntoDrop(lstates, 1, iminus); }
                  ConvertTotalState_LPlusH(lstates[i]);
                }
              }
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertMultistepMaintainsMatching(tau: bool, tid: Armada_ThreadHandle, steps: seq<L.Armada_TraceEntry>)
          requires forall step :: step in steps ==> step.tid == tid
          requires forall step :: step in steps ==> step.Armada_TraceEntry_Tau? == tau
          ensures forall step :: step in MapSeqToSeq(steps, ConvertTraceEntry_LH) ==> step.tid == tid
          ensures forall step :: step in MapSeqToSeq(steps, ConvertTraceEntry_LH) ==> step.Armada_TraceEntry_Tau? == tau
          decreases |steps|
        {
          if |steps| > 0 {
            assert tau ==> steps[0].Armada_TraceEntry_Tau?;
            lemma_ConvertMultistepMaintainsMatching(tau, tid, steps[1..]);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformCHLAssumeIntroOneStep(
          lb:AnnotatedBehavior<LPlusState, LStep>,
          pos:int
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          requires 0 <= pos < |lb.states| - 1
          ensures  var ls := lb.states[pos];
                   var ls' := lb.states[pos+1];
                   var lstep := lb.trace[pos];
                   var hs := ConvertTotalState_LPlusH(ls);
                   var hs' := ConvertTotalState_LPlusH(ls');
                   var hstep := ConvertMultistep_LH(lstep);
                   H.Armada_Next(hs, hs', hstep)
        {
          var ls := lb.states[pos];
          var ls' := lb.states[pos+1];
          var lstep := lb.trace[pos];
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var hstep := ConvertMultistep_LH(lstep);

          var ub := lemma_UnrollBehavior(lb, pos);
          assert ActionTuple(lb.states[pos], lb.states[pos+1], lb.trace[pos]) in GetLPlusSpec().next;
          var lstates := Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lstep.steps);
          var hstates := Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hstep.steps);
          lemma_PerformCHLAssumeIntroMultipleSubsteps(ub, lstep.tau, lstep.tid, ls, ls', lstep.steps, hs, hs', hstep.steps,
                                                      lstates, hstates);
          lemma_ConvertMultistepMaintainsMatching(lstep.tau, lstep.tid, lstep.steps);
          lemma_LowAndHighMatchYielding();
          forall i | 0 < i < |hstep.steps|
            ensures hstep.tid in hstates[i].threads
            ensures H.Armada_IsNonyieldingPC(hstates[i].threads[hstep.tid].pc)
          {
            assert hstates[i] == ConvertTotalState_LPlusH(lstates[i]);
            assert lstep.tid in lstates[i].s.threads;
            assert L.Armada_IsNonyieldingPC(lstates[i].s.threads[lstep.tid].pc);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_PerformCHLAssumeIntro(
          lb:AnnotatedBehavior<LPlusState, LStep>
          ) returns (
          hb:AnnotatedBehavior<HState, HStep>
          )
          requires AnnotatedBehaviorSatisfiesSpec(lb, GetLPlusSpec())
          ensures  BehaviorRefinesBehavior(lb.states, hb.states, GetLPlusHRefinementRelation())
          ensures  AnnotatedBehaviorSatisfiesSpec(hb, GetHSpec())
        {
          var l0 := lb.states[0];
          var h0 := ConvertTotalState_LPlusH(l0);
          var relation := GetLPlusHRefinementRelation();
          var hspec := GetHSpec();

          var hconfig := lemma_LInitImpliesHInit(l0);
          var hstates := [h0];
          var htrace := [];
          var lh_map := [RefinementRange(0, 0)];
          var pos := 0;

          while pos < |lb.states| - 1
            invariant 0 <= pos < |lb.states|
            invariant |htrace| == |hstates|-1
            invariant hstates[0] in hspec.init
            invariant forall i :: 0 <= i < |htrace| ==> H.Armada_Next(hstates[i], hstates[i+1], htrace[i])
            invariant last(hstates) == ConvertTotalState_LPlusH(lb.states[pos])
            invariant BehaviorRefinesBehaviorUsingRefinementMap(lb.states[..pos+1], hstates, relation, lh_map)
          {
            var ls := lb.states[pos];
            var ls' := lb.states[pos+1];
            var lstep := lb.trace[pos];
            assert ActionTuple(ls, ls', lstep) in GetLPlusSpec().next;

            var hs := ConvertTotalState_LPlusH(ls);
            var hs' := ConvertTotalState_LPlusH(ls');
            var hstep := ConvertMultistep_LH(lstep);
            lemma_PerformCHLAssumeIntroOneStep(lb, pos);

            htrace := htrace + [hstep];
            hstates := hstates + [hs'];
            lh_map := lh_map + [RefinementRange(|hstates|-1, |hstates|-1)];
            pos := pos + 1;
          }

          hb := AnnotatedBehavior(hstates, htrace);
          assert lb.states[..pos+1] == lb.states;
          assert BehaviorRefinesBehaviorUsingRefinementMap(lb.states, hb.states, relation, lh_map);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasForAssumeIntroProof()
    {
      GenerateStateRefinerSatisfiesRelationLemma();
      GenerateLInitImpliesHInitLemma();
      GenerateLNextPlusEnablementConditionImpliesHNextLemma();
      GeneratePerformCHLAssumeIntro();
    }

    private void GenerateFinalProof()
    {
      var str = @"
        lemma lemma_ProveRefinementViaAssumeIntro()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var lspec := L.Armada_Spec();
          var hspec := H.Armada_Spec();
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);
            var ahb := lemma_PerformCHLAssumeIntro(alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, GetLPlusHRefinementRelation());
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
