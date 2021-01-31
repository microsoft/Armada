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

namespace Microsoft.Armada
{
  public class PathPrinter
  {
    protected string state;
    protected string nextState;
    protected string tid;
    protected string steps;
    protected string states;
    protected string step;
    protected string path;
    protected string paramsParam;
    protected AtomicSpec atomicSpec;

    public PathPrinter(AtomicSpec i_atomicSpec)
    {
      state = "s";
      nextState = "s'";
      tid = "tid";
      steps = "steps";
      states = "states";
      step = "step";
      path = "path";
      paramsParam = "params";
      atomicSpec = i_atomicSpec;
    }

    public virtual string State { get { return state; } set { state = value; } }
    public virtual string NextState { get { return nextState; } set { nextState = value; } }
    public virtual string Tid { get { return tid; } set { tid = value; } }
    public virtual string Steps { get { return steps; } set { steps = value; } }
    public virtual string States { get { return states; } set { states = value; } }
    public virtual string Step { get { return step; } set { step = value; } }
    public virtual string Path { get { return path; } set { path = value; } }
    public virtual string ParamsParam { get { return paramsParam; } set { paramsParam = value; } }
    public virtual string TotalStateType { get { return atomicSpec.TypeState; } }
    public virtual string Prefix { get { return atomicSpec.Prefix; } }
    public virtual string ModuleName { get { return atomicSpec.ModuleName; } }

    public virtual string StepsType(AtomicPath path)
    {
      return $"{Prefix}_PathSteps_{path.Name}";
    }

    public virtual string CaseEntry(AtomicPath path)
    {
      return $"case {Prefix}_Path_{path.Name}({ParamsParam})";
    }

    public virtual string CaseEntryWithUnderscores(AtomicPath path)
    {
      return $"case {Prefix}_Path_{path.Name}(_)";
    }

    public virtual string PathFormals(AtomicPath path)
    {
      return $"{State}:{TotalStateType}, {Tid}:Armada_ThreadHandle, {Steps}:{StepsType(path)}";
    }

    public virtual string PathSteps(AtomicPath path)
    {
      return $"{State}, {Tid}, {Steps}";
    }

    public virtual string GetOpenValidPathInvocation(AtomicPath atomicPath)
    {
      string str = $@"
         var {Steps}, {States} := lemma_{Prefix}_OpenPath_{atomicPath.Name}({State}, {Path}, {Tid});
      ";
/*
         assert {Path} == {Prefix}_Path_{atomicPath.Name}({Steps});
         assert {Prefix}_ValidPath_{atomicPath.Name}({State}, {Tid}, {Steps});
         assert {States} == {Prefix}_GetPathStates_{atomicPath.Name}({State}, {Tid}, {Steps});
         assert {Prefix}_GetStateAfterPath({State}, {Path}, {Tid}) == {States}.s{atomicPath.NumNextRoutines};
*/
      foreach (var i in Enumerable.Range(0, atomicPath.NumNextRoutines))
      {
        var nextRoutine = atomicPath.NextRoutines[i];
        var stepPrinter = new ModuleStepPrinter(ModuleName);
        stepPrinter.State = atomicSpec.Low ? $"{States}.s{i}.s" :  $"{States}.s{i}";
        stepPrinter.Step = $"{Steps}.step{i}";
        stepPrinter.Tid = Tid;
        str += stepPrinter.GetOpenValidStepInvocation(nextRoutine);
      }
      return str;
    }

    public virtual string GetOpenPathInvocation(AtomicPath atomicPath)
    {
      string str = $@"
         var {Steps}, {States} := lemma_{Prefix}_OpenPath_{atomicPath.Name}({State}, {Path}, {Tid});
      ";
/*
         assert {Path} == {Prefix}_Path_{atomicPath.Name}({Steps});
         assert {Prefix}_ValidPath({State}, {Path}, {Tid}) == {Prefix}_ValidPath_{atomicPath.Name}({State}, {Tid}, {Steps});
         assert {States} == {Prefix}_GetPathStates_{atomicPath.Name}({State}, {Tid}, {Steps});
         assert {Prefix}_GetStateAfterPath({State}, {Path}, {Tid}) == {States}.s{atomicPath.NumNextRoutines};
*/
      foreach (var i in Enumerable.Range(0, atomicPath.NumNextRoutines))
      {
        var nextRoutine = atomicPath.NextRoutines[i];
        var stepPrinter = new ModuleStepPrinter(ModuleName);
        stepPrinter.State = atomicSpec.Low ? $"{States}.s{i}.s" :  $"{States}.s{i}";
        stepPrinter.Step = $"{Steps}.step{i}";
        stepPrinter.Tid = Tid;
        str += stepPrinter.GetOpenStepInvocation(nextRoutine);
      }
      return str;
    }

    public virtual string GetAssertValidPathInvocation(AtomicPath atomicPath)
    {
      string str = "";
      foreach (var i in Enumerable.Range(0, atomicPath.NumNextRoutines))
      {
        var nextRoutine = atomicPath.NextRoutines[i];
        var stepPrinter = new ModuleStepPrinter(ModuleName);
        stepPrinter.State = atomicSpec.Low ? $"{States}.s{i}.s" :  $"{States}.s{i}";
        stepPrinter.NextState = atomicSpec.Low ? $"{States}.s{i + 1}.s" :  $"{States}.s{i + 1}";
        stepPrinter.Step = $"{Steps}.step{i}";
        stepPrinter.Tid = Tid;
        str += stepPrinter.GetAssertValidStepInvocation(nextRoutine);
      }
      str += $@"
        assert {Prefix}_ValidPath_{atomicPath.Name}({State}, {Tid}, {Steps});
        assert {Prefix}_ValidPath({State}, {Path}, {Tid});
        assert {NextState} == {Prefix}_GetStateAfterPath({State}, {Path}, {Tid});
      ";
      return str;
    }
  }

  public class PrefixedVarsPathPrinter : PathPrinter
  {
    public PrefixedVarsPathPrinter(AtomicSpec i_atomicSpec) : base(i_atomicSpec)
    {
      var prefix = atomicSpec.Low ? "l" : "h";
      State = prefix + State;
      NextState = prefix + NextState;
      States = prefix + States;
      Steps = prefix + Steps;
      Path = prefix + Path;
    }
  }

  public class ReductionPathPrinter : PathPrinter
  {
    public ReductionPathPrinter(AtomicSpec i_atomicSpec, string i_uniq, string i_state, string i_nextState, string i_path, string i_tid)
      : base(i_atomicSpec)
    {
      State = i_state;
      NextState = i_nextState;
      Path = i_path;
      Steps = i_uniq + "_steps";
      States = i_uniq + "_states";
      Tid = i_tid;
    }
  }
}
