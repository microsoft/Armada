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
  public abstract class PCInfo
  {
    protected readonly ArmadaPC PC;

    public PCInfo(ArmadaPC pc)
    {
      PC = pc;
    }

    public bool IsEntryPoint
    {
      get
      {
        return PC.instructionCount == 0;
      }
    }

    protected string IsEntryPointAsString
    {
      get
      {
        return IsEntryPoint ? "true" : "false";
      }
    }

    public abstract string GetDafnyDescriptor();
  }

  public class ReturnSitePCInfo : PCInfo
  {
    public ReturnSitePCInfo(ArmadaPC pc) : base(pc)
    {
    }

    public override string GetDafnyDescriptor()
    {
      return $"ReturnSite({IsEntryPointAsString})";
    }
  }

  public class CallSitePCInfo : PCInfo
  {
    public CallSitePCInfo(ArmadaPC pc) : base(pc)
    {
    }

    public override string GetDafnyDescriptor()
    {
      return $"CallSite({IsEntryPointAsString})";
    }
  }

  public class ForkSitePCInfo : PCInfo
  {
    public ForkSitePCInfo(ArmadaPC pc) : base(pc)
    {
    }

    public override string GetDafnyDescriptor()
    {
      return $"ForkSite({IsEntryPointAsString})";
    }
  }

  public class NormalPCInfo : PCInfo
  {
    public NormalPCInfo(ArmadaPC pc) : base(pc)
    {
    }

    public override string GetDafnyDescriptor()
    {
      return $"NormalPC({IsEntryPointAsString})";
    }
  }

  public enum StepDescriptorType { Start, Direct, WhileTrue, WhileFalse, IfTrue, IfFalse };

  public class StepDescriptor
  {
    private StepDescriptorType stepType;
    private NextRoutine nextRoutine;

    public StepDescriptor(StepDescriptorType i_stepType, NextRoutine i_nextRoutine)
    {
      stepType = i_stepType;
      nextRoutine = i_nextRoutine;
    }

    public string GetStraightlineStepTypeAsString()
    {
      if (stepType == StepDescriptorType.WhileTrue || stepType == StepDescriptorType.WhileFalse) {
        return "Loop";
      }
      else if (stepType == StepDescriptorType.Start) {
        return "Start";
      }
      else if (stepType == StepDescriptorType.Direct && nextRoutine.nextType == NextType.Call) {
        return "Call";
      }
      else {
        return "Normal";
      }
    }

    public StepDescriptorType StepType { get { return stepType; } }
    public NextRoutine Next { get { return nextRoutine; } }
  }

  public abstract class PCNode
  {
    protected readonly ArmadaPC pc;

    public PCNode(ArmadaPC i_pc)
    {
      pc = i_pc;
    }

    public abstract void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches);

    public ArmadaPC PC { get { return pc; } }
  }

  public class NormalPCNode : PCNode
  {
    private NextRoutine nextRoutine;
    private readonly PCNode successor;

    public NormalPCNode(ArmadaPC i_pc, NextRoutine i_nextRoutine, PCNode i_successor) : base(i_pc)
    {
      nextRoutine = i_nextRoutine;
      successor = i_successor;
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      steps.Add(new StepDescriptor(StepDescriptorType.Direct, nextRoutine));
      successor.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      states.RemoveAt(states.Count - 1);
    }

    public PCNode Successor { get { return successor; } }
    public NextRoutine Next { get { return nextRoutine; } }
  }

  public class StartingPCNode : PCNode
  {
    private readonly PCNode successor;

    public StartingPCNode(ArmadaPC i_pc, PCNode i_successor) : base(i_pc)
    {
      successor = i_successor;
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      steps.Add(new StepDescriptor(StepDescriptorType.Start, null));
      successor.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      states.RemoveAt(states.Count - 1);
    }

    public PCNode Successor { get { return successor; } }
  }

  public class ReturningPCNode : PCNode
  {
    public ReturningPCNode(ArmadaPC i_pc) : base(i_pc)
    {
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      states.RemoveAt(states.Count - 1);
    }
  }

  public class LoopRestartPCNode : PCNode
  {
    public LoopRestartPCNode(ArmadaPC i_pc) : base(i_pc)
    {
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      states.RemoveAt(states.Count - 1);
    }
  }

  public class IfPCNode : PCNode
  {
    private NextRoutine nextRoutineWhenTrue;
    private NextRoutine nextRoutineWhenFalse;
    private readonly PCNode successorWhenTrue;
    private readonly PCNode successorWhenFalse;

    public IfPCNode(ArmadaPC i_pc, NextRoutine i_nextRoutineWhenTrue, NextRoutine i_nextRoutineWhenFalse,
                    PCNode i_successorWhenTrue, PCNode i_successorWhenFalse) : base(i_pc)
    {
      nextRoutineWhenTrue = i_nextRoutineWhenTrue;
      nextRoutineWhenFalse = i_nextRoutineWhenFalse;
      successorWhenTrue = i_successorWhenTrue;
      successorWhenFalse = i_successorWhenFalse;
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      steps.Add(new StepDescriptor(StepDescriptorType.IfTrue, nextRoutineWhenTrue));
      branches.Add(true);
      successorWhenTrue.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      steps.Add(new StepDescriptor(StepDescriptorType.IfFalse, nextRoutineWhenFalse));
      branches.RemoveAt(branches.Count - 1);
      branches.Add(false);
      successorWhenFalse.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      states.RemoveAt(states.Count - 1);
      branches.RemoveAt(branches.Count - 1);
    }

    public PCNode SuccessorWhenTrue { get { return successorWhenTrue; } }
    public PCNode SuccessorWhenFalse { get { return successorWhenFalse; } }
  }

  public class WhilePCNode : PCNode
  {
    private NextRoutine nextRoutineWhenTrue;
    private NextRoutine nextRoutineWhenFalse;
    private readonly PCNode successorWhenTrue;
    private readonly PCNode successorWhenFalse;

    public WhilePCNode(ArmadaPC i_pc, NextRoutine i_nextRoutineWhenTrue, NextRoutine i_nextRoutineWhenFalse, PCNode i_successorWhenTrue,
                       PCNode i_successorWhenFalse) : base(i_pc)
    {
      nextRoutineWhenTrue = i_nextRoutineWhenTrue;
      nextRoutineWhenFalse = i_nextRoutineWhenFalse;
      successorWhenTrue = i_successorWhenTrue;
      successorWhenFalse = i_successorWhenFalse;
    }

    public override void Visit(IPCNodeVisitor visitor, string methodName, List<PCNode> states, List<StepDescriptor> steps,
                               Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches)
    {
      states.Add(this);
      visitor.Visit(methodName, states, steps, visitedLoops, branches);
      visitedLoops[pc] = states.Count - 1;
      steps.Add(new StepDescriptor(StepDescriptorType.WhileTrue, nextRoutineWhenTrue));
      branches.Add(true);
      successorWhenTrue.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      steps.Add(new StepDescriptor(StepDescriptorType.WhileFalse, nextRoutineWhenFalse));
      branches.RemoveAt(branches.Count - 1);
      branches.Add(false);
      successorWhenFalse.Visit(visitor, methodName, states, steps, visitedLoops, branches);
      steps.RemoveAt(steps.Count - 1);
      states.RemoveAt(states.Count - 1);
      branches.RemoveAt(branches.Count - 1);
      visitedLoops[pc] = -1;
    }

    public PCNode SuccessorWhenTrue { get { return successorWhenTrue; } }
    public PCNode SuccessorWhenFalse { get { return successorWhenFalse; } }
  }

  public interface IPCNodeVisitor
  {
    void Visit(string methodName, List<PCNode> states, List<StepDescriptor> steps, Dictionary<ArmadaPC, int> visitedLoops, List<bool> branches);
  }

  public class PCGraph
  {
    private static PCNode GeneratePCStructureForMethodWithBody(MethodInfo methodInfo, HashSet<ArmadaPC> loopHeads)
    {
      ArmadaStatement parsedBody = methodInfo.ParsedBody;
      PCNode endNode = new ReturningPCNode(parsedBody.EndPC);
      PCNode startNode = parsedBody.GeneratePCStructureForStatement(endNode, null, null, loopHeads);
      return new StartingPCNode(parsedBody.StartPC, startNode);
    }

    private static PCNode GeneratePCStructureForMethodWithNoBody(ArmadaSymbolTable symbols, MethodInfo methodInfo, HashSet<ArmadaPC> loopHeads)
    {
      Method method = methodInfo.method;

      var startPC = new ArmadaPC(symbols, method.Name, 0);
      var midPC = new ArmadaPC(symbols, method.Name, 1);
      var endPC = new ArmadaPC(symbols, method.Name, 2);

      PCNode endNode = new ReturningPCNode(endPC);
      PCNode loopRestartNode = new LoopRestartPCNode(midPC);
      PCNode midNode = new WhilePCNode(midPC, method.externContinueNextRoutine, method.externEndNextRoutine, loopRestartNode, endNode);
      PCNode startNode = new NormalPCNode(startPC, method.externStartNextRoutine, midNode);
      loopHeads.Add(midPC);
      return new StartingPCNode(startPC, startNode);
    }

    public static void Visit(ArmadaSymbolTable symbols, MethodInfo methodInfo, IPCNodeVisitor visitor)
    {
      var states = new List<PCNode>();
      var steps = new List<StepDescriptor>();
      var loopHeads = new HashSet<ArmadaPC>();
      var branches = new List<bool>();

      var rootNode = methodInfo.method.Body == null ? GeneratePCStructureForMethodWithNoBody(symbols, methodInfo, loopHeads)
                                                    : GeneratePCStructureForMethodWithBody(methodInfo, loopHeads);

      var visitedLoops = loopHeads.ToDictionary(h => h, h => -1);
      rootNode.Visit(visitor, methodInfo.method.Name, states, steps, visitedLoops, branches);
    }
  }
}
