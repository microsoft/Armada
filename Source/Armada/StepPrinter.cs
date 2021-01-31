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
  public class StepPrinter
  {
    private string state;
    private string nextState;
    private string tid;
    private string step;
    private string paramsParam;

    public StepPrinter()
    {
      state = "s";
      nextState = "s'";
      tid = "tid";
      step = "step";
      paramsParam = "params";
    }

    public virtual string State { get { return state; } set { state = value; } }
    public virtual string NextState { get { return nextState; } set { nextState = value; } }
    public virtual string Tid { get { return tid; } set { tid = value; } }
    public virtual string Step { get { return step; } set { step = value; } }
    public virtual string ParamsParam { get { return paramsParam; } set { paramsParam = value; } }

    public virtual string TotalStateType { get { return "Armada_TotalState"; } }

    public virtual string Params(NextRoutine nextRoutine)
    {
      return $"step.params_{nextRoutine.NameSuffix}";
    }

    public virtual string CaseEntry(NextRoutine nextRoutine)
    {
      var p = nextRoutine.HasFormals ? paramsParam : "";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({p})";
    }

    public virtual string CaseEntryWithUnderscores(NextRoutine nextRoutine)
    {
      var p = nextRoutine.HasFormals ? "_" : "";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({p})";
    }

    public virtual string StepParams(NextRoutine nextRoutine)
    {
      var extra = nextRoutine.HasFormals ? $", {Params(nextRoutine)}" : "";
      return $"{State}, {Tid}{extra}";
    }

    public virtual string ValidStepInvocation(NextRoutine nextRoutine)
    {
      return $"Armada_ValidStep_{nextRoutine.NameSuffix}({StepParams(nextRoutine)})";
    }

    public virtual string GetNextStateInvocation(NextRoutine nextRoutine)
    {
      return $"Armada_GetNextState_{nextRoutine.NameSuffix}({StepParams(nextRoutine)})";
    }
  }

  public class ModuleStepPrinter : StepPrinter
  {
    private string moduleName;

    public ModuleStepPrinter(string i_moduleName)
    {
      moduleName = i_moduleName;
    }

    public override string TotalStateType { get { return $"{moduleName}.Armada_TotalState"; } }

    public override string ValidStepInvocation(NextRoutine nextRoutine)
    {
      var s = base.ValidStepInvocation(nextRoutine);
      return $"{moduleName}.{s}";
    }

    public override string GetNextStateInvocation(NextRoutine nextRoutine)
    {
      var s = base.GetNextStateInvocation(nextRoutine);
      return $"{moduleName}.{s}";
    }

    public virtual string GetOpenValidStepInvocation(NextRoutine nextRoutine)
    {
      return $@"
        lemma_OpenStep_{moduleName}_{nextRoutine.NameSuffix}({State}, {Step}, {Tid});
      ";
      /*
        assert {ValidStepInvocation(nextRoutine)};
        assert {moduleName}.Armada_GetNextState({State}, {Step}, {Tid}) == {GetNextStateInvocation(nextRoutine)};
      */
    }

    public virtual string GetOpenStepInvocation(NextRoutine nextRoutine)
    {
      return $@"
        lemma_OpenStep_{moduleName}_{nextRoutine.NameSuffix}({State}, {Step}, {Tid});
      ";
      /*
        assert {moduleName}.Armada_ValidStep({State}, {Step}, {Tid}) <==>
                 {Tid} in {State}.threads && {State}.stop_reason.Armada_NotStopped? && {ValidStepInvocation(nextRoutine)};
        assert {moduleName}.Armada_ValidStep({State}, {Step}, {Tid}) ==>
                 {GetNextStateInvocation(nextRoutine)} == {moduleName}.Armada_GetNextState({State}, {Step}, {Tid});
      */
    }

    public virtual string GetAssertValidStepInvocation(NextRoutine nextRoutine)
    {
      return $@"
        assert {ValidStepInvocation(nextRoutine)};
        assert {moduleName}.Armada_ValidStep({State}, {Step}, {Tid});
        assert {NextState} == {moduleName}.Armada_GetNextState({State}, {Step}, {Tid});
      ";
    }
  }

  public class LPlusStepPrinter : ModuleStepPrinter
  {
    public LPlusStepPrinter() : base("L")
    {
      State = State + ".s";
    }

    public override string TotalStateType { get { return "LPlusState"; } }
  }
}
