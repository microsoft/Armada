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
  ////////////////////////////////////////////////
  // CHLPathEffect
  ////////////////////////////////////////////////

  abstract class CHLPathEffect
  {
    // A path's effective procedure can be obtained by calling ProcName.  Usually, that's the
    // procedure where the path starts.  However, when the first thing that happens is a return,
    // it's the procedure returned to.

    // The start and end PCs are the actual PC values at the start and end of running the path.
    // The effective start and end PCs, however, are always in the effective procedure of the path.
    // They correspond to the PC at the top of the stack at the time.
    // So, if the path starts out by returning, the effective start PC is the PC popped off the
    // stack by the return.
    // And, if the path ends by calling, the end PC is the PC pushed onto the stack by the call.

    // The effective PCs are useful because they can be unambiguously used to name a sequence of
    // paths in a straightline behavior.  The procedure name, effective end PC, and branch outcomes
    // uniquely identify a straightline behavior.  They're also useful in constructing a sequence
    // corresponding to a straightline behavior:  the effective end PC of one step is the effective
    // start PC of the next.

    public CHLPathEffect(ArmadaPC i_startPC, ArmadaPC i_endPC, ArmadaPC i_effectiveStartPC, ArmadaPC i_effectiveEndPC)
    {
      startPC = i_startPC;
      endPC = i_endPC;
      effectiveStartPC = i_effectiveStartPC;
      effectiveEndPC = i_effectiveEndPC;
    }

    protected ArmadaPC startPC;
    protected ArmadaPC endPC;
    protected ArmadaPC effectiveStartPC;
    protected ArmadaPC effectiveEndPC;

    public ArmadaPC StartPC { get { return startPC; } }
    public ArmadaPC EndPC { get { return endPC; } }
    public ArmadaPC EffectiveStartPC { get { return effectiveStartPC; } }
    public ArmadaPC EffectiveEndPC { get { return effectiveEndPC; } }

    public virtual string ProcName { get; }
    public virtual string Constructor { get; }
    public virtual string Callee { get { return null; } }

    public virtual bool CanFollow(StraightlineState state) { return false; }
  }

  class CHLPathEffectNormal : CHLPathEffect
  {
    public CHLPathEffectNormal(ArmadaPC i_startPC, ArmadaPC i_endPC) : base(i_startPC, i_endPC, i_startPC, i_endPC)
    {
    }

    public override string ProcName { get { return startPC.methodName; } }
    public override string Constructor { get { return "CHLStepEffectNormal()"; } }

    public override bool CanFollow(StraightlineState state) { return state is StraightlineStateYielded; }
  }

  class CHLPathEffectReturn : CHLPathEffect
  {
    public CHLPathEffectReturn(ArmadaPC i_startPC, ArmadaPC i_endPC, ArmadaPC i_effectiveStartPC)
      : base(i_startPC, i_endPC, i_effectiveStartPC, i_endPC)
    {
    }

    public string Returner { get { return startPC.methodName; } }
    public override string ProcName { get { return endPC.methodName; } }
    public override string Constructor { get { return "CHLStepEffectReturn()"; } }

    public override bool CanFollow(StraightlineState state) { return state is StraightlineStateEnsured; }
  }

  class CHLPathEffectCall : CHLPathEffect
  {
    public CHLPathEffectCall(ArmadaPC i_startPC, ArmadaPC i_endPC, ArmadaPC i_effectiveEndPC)
      : base(i_startPC, i_endPC, i_startPC, i_effectiveEndPC)
    {
    }

    public override string Callee { get { return endPC.methodName; } }
    public override string ProcName { get { return startPC.methodName; } }
    public override string Constructor { get { return $"CHLStepEffectCall(LProcName_{endPC.methodName})"; } }

    public override bool CanFollow(StraightlineState state) { return state is StraightlineStateYielded; }
  }

  class CHLPathEffectReturnThenCall : CHLPathEffect
  {
    public CHLPathEffectReturnThenCall(ArmadaPC i_startPC, ArmadaPC i_endPC, ArmadaPC i_effectiveStartPC, ArmadaPC i_effectiveEndPC)
      : base(i_startPC, i_endPC, i_effectiveStartPC, i_effectiveEndPC)
    {
    }

    public string Returner { get { return startPC.methodName; } }
    public override string Callee { get { return endPC.methodName; } }
    public override string ProcName { get { return effectiveStartPC.methodName; } }
    public override string Constructor { get { return $"CHLStepEffectReturnThenCall(LProcName_{endPC.methodName})"; } }

    public override bool CanFollow(StraightlineState state) { return state is StraightlineStateEnsured; }
  }

  class CHLPathEffectActorless : CHLPathEffect
  {
    public CHLPathEffectActorless() : base(null, null, null, null)
    {
    }

    public override string ProcName { get { return "main"; } }
    public override string Constructor { get { return "CHLStepEffectActorless()"; } }
  }

  class CHLPathEffectExit : CHLPathEffect
  {
    public CHLPathEffectExit(ArmadaPC i_startPC) : base(i_startPC, null, i_startPC, null)
    {
    }

    public override string ProcName { get { return startPC.methodName; } }
    public override string Constructor { get { return "CHLStepEffectExit()"; } }

    public override bool CanFollow(StraightlineState state) { return state is StraightlineStateYielded; }
  }

  class CHLPathEffectStop : CHLPathEffect
  {
    public CHLPathEffectStop(ArmadaPC i_startPC) : base(i_startPC, null, null, null)
    {
    }

    public override string ProcName { get { return startPC.methodName; } }
    public override string Constructor { get { return "CHLStepEffectStop()"; } }

    public override bool CanFollow(StraightlineState state) { return false; }
  }

  ////////////////////////////////////////////////
  // CHLPredicateInfo
  ////////////////////////////////////////////////

  class CHLPredicateInfo
  {
    public readonly string Key;
    public readonly string Value;
    public readonly bool Opaque;

    public CHLPredicateInfo(string i_key, string i_value, bool i_opaque)
    {
      Key = i_key;
      Value = i_value;
      Opaque = i_opaque;
    }
  }

  ////////////////////////////////////////////////
  // AssumeIntroPathGenerator
  ////////////////////////////////////////////////

  public class AssumeIntroProofGenerator : AbstractProofGenerator
  {
    private AssumeIntroStrategyDecl strategy;
    private List<ArmadaPC> lpcs;
    private List<CHLPredicateInfo> globalInvariantInfos;
    private List<CHLPredicateInfo> yieldPredicateInfos;
    private Dictionary<string, List<string>> extraPreconditionsForMethod;
    private Dictionary<string, List<string>> extraPostconditionsForMethod;
    private Dictionary<ArmadaPC, List<string>> extraLoopModifiesClausesForPC;
    private Dictionary<ArmadaPC, List<string>> extraLocalInvariantClausesForPC;
    private HashSet<ArmadaPC> lExtraRecurrentPCs, hExtraRecurrentPCs;
    private List<string> methodsWithPostconditions;
    private HashSet<ArmadaPC> loopHeads;
    private HashSet<ArmadaPC> pcsWithEnablingConditions;
    private HashSet<ArmadaPC> pcsWithLocalInvariants;
    private ProofFile pcstackFile;
    private ProofFile sbdFile;
    private ProofFile exhaustiveFile;
    private Dictionary<string, ArmadaPC> returnPCForMethod;
    private Dictionary<AtomicPath, CHLPathEffect> pathEffectMap;
    private Dictionary<ArmadaPC, List<AtomicPath>> pathsStartingAtPC;
    private List<StraightlineBehavior> straightlineBehaviorDescriptors;
    private Dictionary<string, StraightlineBehavior> emptyStraightlineBehaviorForMethod;
    private List<StraightlineBehavior> sbdsEndingNormal, sbdsEndingEnsured, sbdsEndingYielded;
    private Dictionary<string, List<string>> preconditionsForMethod;

    public AssumeIntroProofGenerator(ProofGenerationParams i_pgp, AssumeIntroStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      lpcs = new List<ArmadaPC>();
      i_pgp.symbolsLow.AllMethods.AppendAllPCs(lpcs);
      globalInvariantInfos = new List<CHLPredicateInfo>();
      yieldPredicateInfos = new List<CHLPredicateInfo>();
      extraPreconditionsForMethod = new Dictionary<string, List<string>>();
      extraPostconditionsForMethod = new Dictionary<string, List<string>>();
      extraLoopModifiesClausesForPC = new Dictionary<ArmadaPC, List<string>>();
      extraLocalInvariantClausesForPC = new Dictionary<ArmadaPC, List<string>>();
      methodsWithPostconditions = new List<string>();
      loopHeads = new HashSet<ArmadaPC>();
      pcsWithEnablingConditions = new HashSet<ArmadaPC>();
      pcsWithLocalInvariants = new HashSet<ArmadaPC>();
      returnPCForMethod = new Dictionary<string, ArmadaPC>();
      pathEffectMap = new Dictionary<AtomicPath, CHLPathEffect>();
      pathsStartingAtPC = new Dictionary<ArmadaPC, List<AtomicPath>>();
      straightlineBehaviorDescriptors = new List<StraightlineBehavior>();
      emptyStraightlineBehaviorForMethod = new Dictionary<string, StraightlineBehavior>();
      sbdsEndingEnsured = new List<StraightlineBehavior>();
      sbdsEndingYielded = new List<StraightlineBehavior>();
      sbdsEndingNormal = new List<StraightlineBehavior>();
      preconditionsForMethod = new Dictionary<string, List<string>>();
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence())
      {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }

      if (!CheckForBackwardGotos())
      {
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      CreateExtraRecurrentPCs();
      CreateReturnPCForMethod();
      GenerateNextRoutineMap();
      DeterminePCsWithEnablingConditions();
      GenerateProofGivenMap();
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateCustomCHLClauses();
      ParseProgram();
      GenerateAtomicSpecs(true, lExtraRecurrentPCs, hExtraRecurrentPCs);
      CreatePathEffectMap();
      CreateStoppingPathsStartingAtPC();
      GeneratePathPCStackEffectLemmas();
      CreateStraightlineBehaviors();
      GenerateStraightlineBehaviorDescriptors();
      GenerateStraightlineBehaviorDescriptorExhaustiveLemmas();
      GenerateStraightlineBehaviorDescriptorContinuationLemmas();
      GenerateStraightlineBehaviorDescriptorEnumerationLemmas();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
      GenerateConcurrentHoareLogicRequest();
      GenerateLocalViewCommutativityLemmas();
      GenerateGenericStoreBufferLemmas_L();
      GenerateProofThatCHLRequestIsValid();
      GenerateLemmasForAssumeIntroProof();
      GenerateFinalProof();
    }

    private void CreateExtraRecurrentPCs()
    {
      lExtraRecurrentPCs = new HashSet<ArmadaPC>();
      foreach (var pc in pgp.symbolsLow.EnumeratePotentialRecurrentPCs()) {
        if (pgp.symbolsLow.IsNonyieldingPC(pc)) {
          lExtraRecurrentPCs.Add(pc);
        }
      }

      hExtraRecurrentPCs = new HashSet<ArmadaPC>();
      foreach (var pc in pgp.symbolsHigh.EnumeratePotentialRecurrentPCs()) {
        if (pgp.symbolsHigh.IsNonyieldingPC(pc)) {
          hExtraRecurrentPCs.Add(pc);
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogic.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("ConcurrentHoareLogicSpecModule");
      pgp.MainProof.AddImport("AtomicConcurrentHoareLogicSpecModule");
      pgp.MainProof.AddImport("AtomicConcurrentHoareLogicModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");
      pgp.MainProof.AddImport("GenericArmadaSpecModule");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");

      pgp.proofFiles.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy",
                                "defs");
      pgp.proofFiles.AddImport("ConcurrentHoareLogicSpecModule", null, "defs");
      pgp.proofFiles.AddImport("AtomicConcurrentHoareLogicSpecModule", null, "defs");
    }

    ////////////////////////////////////////////////////////////////////////
    /// PC Info
    ////////////////////////////////////////////////////////////////////////

    private void CreateReturnPCForMethod()
    {
      returnPCForMethod = pgp.symbolsLow.MethodNames.ToDictionary(
        methodName => methodName,
        methodName => pgp.symbolsLow.AllMethods.LookupMethod(methodName).ReturnPC
      );
    }

    private CHLPathEffect GetCHLPathEffect(AtomicPath atomicPath)
    {
      if (atomicPath.Stopping) {
        return new CHLPathEffectStop(atomicPath.StartPC);
      }
      if (atomicPath.Tau) {
        return new CHLPathEffectActorless();
      }

      // Because all entry points and return sites of methods are considered yield or recurrent
      // points, a path can only return (or exit) as its first routine and can only call as its last
      // routine.  So, those are the only routines we need to look at to tell whether a path calls
      // or returns.

      var firstRoutine = atomicPath.NextRoutines[0];
      var lastRoutine = atomicPath.LastNextRoutine;

      if (firstRoutine.nextType == NextType.TerminateThread) {
        return new CHLPathEffectExit(lastRoutine.startPC);
      }
      else if (firstRoutine.nextType == NextType.TerminateProcess) {
        return new CHLPathEffectStop(lastRoutine.startPC);
      }
      else if (firstRoutine.nextType == NextType.Return) {
        var effectiveStartPC = firstRoutine.endPC;
        if (lastRoutine.nextType == NextType.Call) {
          var effectiveEndPC = ((ArmadaCallStatement)lastRoutine.armadaStatement).EndPC;
          return new CHLPathEffectReturnThenCall(atomicPath.StartPC, atomicPath.EndPC, effectiveStartPC, effectiveEndPC);
        }
        else {
          return new CHLPathEffectReturn(atomicPath.StartPC, atomicPath.EndPC, effectiveStartPC);
        }
      }
      else if (lastRoutine.nextType == NextType.Call) {
        var effectiveEndPC = ((ArmadaCallStatement)lastRoutine.armadaStatement).EndPC;
        return new CHLPathEffectCall(atomicPath.StartPC, atomicPath.EndPC, effectiveEndPC);
      }

      // There were no returns or calls, so this path just has a normal effect.

      return new CHLPathEffectNormal(atomicPath.StartPC, atomicPath.EndPC);
    }

    private void CreatePathEffectMap()
    {
      foreach (var atomicPath in lAtomic.AtomicPaths)
      {
        var effect = GetCHLPathEffect(atomicPath);
        pathEffectMap[atomicPath] = effect;
      }
    }

    private void CreateStoppingPathsStartingAtPC()
    {
      foreach (var pc in lpcs)
      {
        pathsStartingAtPC[pc] = new List<AtomicPath>();
      }
      foreach (var atomicPath in lAtomic.AtomicPaths.Where(ap => !ap.Tau))
      {
        pathsStartingAtPC[atomicPath.StartPC].Add(atomicPath);
      }
    }

    ////////////////////////////////////////////////////////////////////////
    /// Static checks
    ////////////////////////////////////////////////////////////////////////

    private bool CheckForBackwardGotos()
    {
      var allMethodsInfo = pgp.symbolsLow.AllMethods;
      foreach (var methodName in allMethodsInfo.AllMethodNames) {
        var methodInfo = allMethodsInfo.LookupMethod(methodName);
        if (methodInfo.method.Body != null) {
          foreach (var stmt in methodInfo.ParsedBody) {
            if (stmt is ArmadaGotoStatement) {
              var startPC = stmt.StartPC;
              var s = (GotoStmt)(stmt.Stmt);
              var targetPC = pgp.symbolsLow.GetPCForMethodAndLabel(methodInfo.method.Name + "_" + s.Target);
              if (targetPC == null || targetPC.instructionCount <= startPC.instructionCount) {
                AH.PrintError(pgp.prog, s.Tok, $"Only forward gotos are supported by assume-intro proofs");
                return false;
              }
            }
          }
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Concurrent Hoare logic request
    ////////////////////////////////////////////////////////////////////////

    private void GenerateConcurrentHoareLogicRequest()
    {
      string str;

      str = "datatype LProcName = ";
      str += String.Join(" | ", pgp.symbolsLow.MethodNames.Select(methodName => $"LProcName_{methodName}"));
      pgp.AddDatatype(str, "defs");

      str = $@"
        type CHLRequest = ConcurrentHoareLogicRequest<LPlusState, Armada_ThreadHandle, PathAndTid<LAtomic_Path>, L.Armada_PC, LProcName>
      ";
      pgp.AddTypeSynonym(str, "defs");

      str = @"
        type AtomicCHLRequest = AtomicConcurrentHoareLogicRequest<LPlusState, LAtomic_Path, L.Armada_PC, LProcName,
                                                                  H.Armada_TotalState, HAtomic_Path, H.Armada_PC>
      ";
      pgp.AddTypeSynonym(str, "defs");

      str = "type LAtomicStraightlineState = StraightlineState<LPlusState, L.Armada_PC>";
      pgp.AddTypeSynonym(str, "defs");

      str = "type LAtomicStraightlineStep = StraightlineStep<PathAndTid<LAtomic_Path>, L.Armada_PC, LProcName>";
      pgp.AddTypeSynonym(str, "defs");

      str = "type LAtomicStraightlineBehavior = AnnotatedBehavior<LAtomicStraightlineState, LAtomicStraightlineStep>";
      pgp.AddTypeSynonym(str, "defs");

      str = "type LAtomicStraightlineBehaviorSpec = AnnotatedBehaviorSpec<LAtomicStraightlineState, LAtomicStraightlineStep>";
      pgp.AddTypeSynonym(str, "defs");

      str = @"
        function PCToProc(pc:L.Armada_PC) : LProcName
        {
          match pc
      ";
      foreach (var pc in lpcs)
      {
        str += $"    case {pc} => LProcName_{pc.methodName}";
      }
      str += "}";
      pgp.AddFunction(str, "defs");

      str = @"
        predicate StateOK(s:LPlusState)
        {
          s.s.stop_reason.Armada_NotStopped?
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        function GetCHLSpec() : AnnotatedBehaviorSpec<LPlusState, PathAndTid<LAtomic_Path>>
        {
          var asf := LAtomic_GetSpecFunctions();
          AnnotatedBehaviorSpec(iset s | asf.init(s),
                                iset s, s', path, tid | asf.path_valid(s, path, tid) && s' == asf.path_next(s, path, tid)
                                                      :: ActionTuple(s, s', PathAndTid(path, tid)))
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function PathAndTidToTid(path_and_tid:PathAndTid<LAtomic_Path>) : Option<Armada_ThreadHandle>
        {
          if path_and_tid.path.LAtomic_Path_Tau? then None else Some(path_and_tid.tid)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function GetThreadPCStack(s:LPlusState, tid:Armada_ThreadHandle) : Option<PCStack<L.Armada_PC, LProcName>>
        {
          if tid in s.s.threads then
            var t := s.s.threads[tid];
            Some(PCStack(t.pc, MapSeqToSeq(t.stack, (e:L.Armada_ExtendedFrame) => PCToProc(e.return_pc))))
          else
            None
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function PathToProc(path: LAtomic_Path) : LProcName
        {
          match path
      ";
      str += String.Concat(lAtomic.AtomicPaths.Select(path => $@"
            case LAtomic_Path_{path.Name}(_) => LProcName_{pathEffectMap[path].ProcName}
      "));
      str += "}";
      pgp.AddFunction(str, "defs");

      str = @"
        function PathAndTidToProc(path_and_tid: PathAndTid<LAtomic_Path>) : LProcName
        {
          PathToProc(path_and_tid.path)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function PathToEffect(path: LAtomic_Path) : CHLStepEffect<LProcName>
        {
          match path
      ";
      str += String.Concat(lAtomic.AtomicPaths.Select(path => $@"
            case LAtomic_Path_{path.Name}(_) => {pathEffectMap[path].Constructor}
      "));
      str += "}";
      pgp.AddFunction(str, "defs");

      str = @"
        function PathAndTidToEffect(path_and_tid: PathAndTid<LAtomic_Path>) : CHLStepEffect<LProcName>
        {
          PathToEffect(path_and_tid.path)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        predicate IsEntryPoint(pc: L.Armada_PC)
        {
      ";
      str += String.Join(" || ", lpcs.Where(pc => pc.instructionCount == 0).Select(pc => $"pc.{pc}?"));
      str += "}";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate IsLoopHead(pc: L.Armada_PC)
        {
      ";
      str += AH.CombineStringsWithOr(loopHeads.Select(pc => $"pc.{pc}?"));
      str += "}";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate IsReturnSite(pc: L.Armada_PC)
        {
      ";
      str += String.Join(" || ", returnPCForMethod.Select(e => $"pc.{e.Value}?"));
      str += "}";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate ThreadAtReturnSite(s: LPlusState, tid: Armada_ThreadHandle, proc: LProcName)
        {
          && tid in s.s.threads
          && var pc := s.s.threads[tid].pc;
          && IsReturnSite(pc)
          && PCToProc(pc) == proc
        }
      ";
      pgp.AddPredicate(str, "defs");

      GenerateGlobalInvariant();
      GenerateLocalInv();
      GenerateYieldPredicate();
      GenerateRequiresClauses();
      GenerateEnsuresClauses();

      GenerateInvariantProof(pgp);

      var mapLiteral = string.Join(", ", loopHeads.Select(pc => $"L.{pc} := LoopModifies_{pc}"));
      str = @"
        predicate LoopModifiesClauses(pc:L.Armada_PC, s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {
          && s.config == s'.config
          && match pc
      ";
      str += String.Concat(loopHeads.Select(pc => $"case {pc} => LoopModifies_{pc}(s, s', tid)\n"));
      str += @"
            case _ => false
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        function GetConcurrentHoareLogicRequest() : CHLRequest
        {
          ConcurrentHoareLogicRequest(GetCHLSpec(), PathAndTidToTid, PathAndTidToProc, GetThreadPCStack,
                                      StateOK, PCToProc, IsEntryPoint, IsLoopHead,
                                      IsReturnSite, PathAndTidToEffect, InductiveInv, GlobalInv, LocalInv,
                                      YieldPredicate, RequiresClauses, EnsuresClauses, LoopModifiesClauses)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function GetAtomicConcurrentHoareLogicRequest() : AtomicCHLRequest
        {
          AtomicConcurrentHoareLogicRequest(GetConcurrentHoareLogicRequest(), LAtomic_GetSpecFunctions(), HAtomic_GetSpecFunctions(),
                                            GetLPlusHRefinementRelation(), ConvertTotalState_LPlusH, ConvertAtomicPath_LH, ConvertPC_LH)
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
        TurnRequirementsIntoLocalPredicates(pgp.symbolsLow, method);
        CreatePostconditionsPredicate(method);
        if (method.Body is null)
        {
          // PC 1 corresponds to the head of the loop that repeatedly checks for the postcondition
          var pc = new ArmadaPC(pgp.symbolsLow, methodName, 1);
          loopHeads.Add(pc);
          ProcessWhileStatementInvariants(pc, new List<MaybeFreeExpression>(), new List<Expression>());
        }
        else
        {
          foreach (var stmt in methodInfo.ParsedBody) {
            if (stmt is ArmadaWhileStatement) {
              var s = (ArmadaWhileStatement)stmt;
              var ws = (WhileStmt)s.Stmt;
              var lowPC = s.StartPC.CloneWithNewSymbolTable(pgp.symbolsLow);
              loopHeads.Add(lowPC);
              ProcessWhileStatementInvariants(lowPC, ws.Invariants, ws.Ens);
            }
          }
        }
      }
    }

    private string CreateStackCorrectAtStartPredicate(Method method)
    {
      var stackInvName = $"StackCorrectAtStart_{method.Name}";

      // predicate {stackInvName}(s:LPlusState, tid:Armada_ThreadHandle)
      // {
      //   && tid in s.s.threads
      //   && s.s.threads[tid].top.Armada_StackFrame_{method.Name}?
      //   && s.s.threads[tid].pc.{initialPC}?
      //   && <for each initialized variable, that variable's initialization doesn't crash>
      // }

      var initialPC = new ArmadaPC(pgp.symbolsLow, method.Name, 0);
      var preds = new List<string>{ "tid in s.s.threads", $"s.s.threads[tid].top.Armada_StackFrame_{method.Name}?",
                                    $"s.s.threads[tid].pc.{initialPC}?" };

      var smst = pgp.symbolsLow.GetMethodSymbolTable(method.Name);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.InitialValue != null))
      {
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new RequiresResolutionContext("s.s", "tid", method.Name, pgp.symbolsLow, failureReporter, "L");
        var ty = pgp.symbolsLow.FlattenType(v.ty);
        var lhsRVal = v.GetRValue(v.InitialValue.tok, context);
        var rhsRVal = context.ResolveAsRValue(v.InitialValue);
        if (rhsRVal.UndefinedBehaviorAvoidance.CanCauseUndefinedBehavior) {
          preds.Add(rhsRVal.UndefinedBehaviorAvoidance.Expr);
        }

        preds.Add($"({lhsRVal.Val}) == ({rhsRVal.Val})");
      }

      var str = $@"
        predicate {stackInvName}(s: LPlusState, tid: Armada_ThreadHandle)
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");
      return stackInvName;
    }

    private void TurnRequirementsIntoLocalPredicates(ArmadaSymbolTable symbols, Method method)
    {
      var preconditionNames = new List<string>();
      preconditionsForMethod[method.Name] = preconditionNames;

      var stackInvName = CreateStackCorrectAtStartPredicate(method);
      if (extraPreconditionsForMethod.ContainsKey(method.Name)) {
        preconditionNames.AddRange(extraPreconditionsForMethod[method.Name]);
      }

      int reqCount = 0;
      foreach (var req in method.Req)
      {
        // predicate Precondition_{reqCount}_{method.Name}(s: LPlusState, tid: Armada_ThreadHandle)
        //   requires tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_{method.Name}?
        // {
        //   <things that prevent requires clause expression from crashing> && <requires clause>
        // }

        reqCount++;
        var reqName = $"Precondition_{reqCount}_{method.Name}";
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new RequiresResolutionContext("s.s", "tid", method.Name, pgp.symbolsLow, failureReporter, "L");
        if (!failureReporter.Valid) {
          reqCount--;
          continue;
        }
        var rvalue = context.ResolveAsRValue(req.E);
        var body = rvalue.CanCauseUndefinedBehavior ? $"({rvalue.UndefinedBehaviorAvoidance.Expr}) && ({rvalue.Val})" : rvalue.Val;

        var fn = $@"
          predicate {reqName}(s: LPlusState, tid: Armada_ThreadHandle)
            requires tid in s.s.threads && s.s.threads[tid].top.Armada_StackFrame_{method.Name}?
          {{
            {body}
          }}
        ";
        pgp.AddPredicate(fn, "defs");
        preconditionNames.Add(reqName);
      }

      string str = $@"
        predicate Preconditions_{method.Name}(s:LPlusState, tid:Armada_ThreadHandle)
        {{
          {stackInvName}(s, tid)
      ";
      str += String.Concat(preconditionNames.Select(name => $" && {name}(s, tid)"));
      str += "}\n";
      pgp.AddPredicate(str, "defs");
    }

    private void CreatePostconditionsPredicate(Method method)
    {
      var clauses = new List<string> {
        "s.config == s'.config",
        "tid in s.s.threads",
        $"s.s.threads[tid].top.Armada_StackFrame_{method.Name}?",
        "tid in s'.s.threads",
        $"s'.s.threads[tid].top.Armada_StackFrame_{method.Name}?",
        "s'.s.threads[tid].stack == s.s.threads[tid].stack"     // Include a clause indicating that the stack hasn't changed
      };

      // For each ensures clause, add a clause

      if (method.Ens != null) {
        foreach (var ens in method.Ens)
        {
          var failureReporter = new SimpleFailureReporter(pgp.prog);
          var context = new EnsuresResolutionContext("s.s", "s'.s", "tid", method.Name, pgp.symbolsLow, failureReporter, "L");
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

      // For each extra CHL postcondition, add a clause

      if (extraPostconditionsForMethod.ContainsKey(method.Name)) {
        foreach (var postconditionName in extraPostconditionsForMethod[method.Name]) {
          clauses.Add($"{postconditionName}(s, s', tid)");
        }
      }
      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is CHLYieldPredicateArmadaProofDecl d) {
          if (method.Name == "main") {
            continue;
          }
          if (Attributes.FindExpressions(d.Attributes, "excludeMethod")?
              .Any(expr => (expr as NameSegment).Name == method.Name) ?? false) {
            continue;
          }
          if (Attributes.Contains(d.Attributes, "excludeAll")) {
            continue;
          }
          var ypKey = d.YieldPredicateName;
          if (d.Code != null || pgp.symbolsLow.YieldPredicates.ContainsKey(ypKey)) {
            var pred = $"UserYP_{ypKey}(s, s', tid)";
            clauses.Add(pred);
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No yield predicate named {ypKey} found among the yield predicates");
            continue;
          }
        }
      }

      // Create a post-condition two-state function out of the collected clauses

      var fn = $@"
        predicate Postconditions_{method.Name}(s: LPlusState, s': LPlusState, tid: Armada_ThreadHandle)
        {{
          {AH.CombineStringsWithAnd(clauses)}
        }}
      ";
      pgp.AddPredicate(fn, "defs");
    }

    private void ProcessWhileStatementInvariants(ArmadaPC pc, List<MaybeFreeExpression> invariants, List<Expression> ens)
    {
      // predicate LoopModifies_{pc}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
      // {
      //   && tid in s.s.threads
      //   && tid in s'.s.threads
      //   && s.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?
      //   && s'.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?
      //   && s'.s.threads[tid].pc.{pc}?
      //   && s'.s.threads[tid].stack == s.s.threads[tid].stack
      //   && <Input and ExternOld variables unchanged>
      //   && <custom loop invariants>
      // }

      var preds = new List<string> {
        "tid in s.s.threads",
        "tid in s'.s.threads",
        $"s.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?",
        $"s'.s.threads[tid].top.Armada_StackFrame_{pc.methodName}?",
        $"s'.s.threads[tid].pc.{pc}?",
        "s'.s.threads[tid].stack == s.s.threads[tid].stack"
      };

      var smst = pgp.symbolsLow.GetMethodSymbolTable(pc.methodName);
      foreach (var v in smst.AllVariablesInOrder.Where(v => v.varType == ArmadaVarType.Input || v.varType == ArmadaVarType.ExternOld))
      {
        preds.Add($"s.s.threads[tid].top.{pc.methodName}.{v.name} == s'.s.threads[tid].top.{pc.methodName}.{v.name}");
      }

      var failureReporter = new SimpleFailureReporter(pgp.prog);
      var ensContext = new EnsuresResolutionContext("s.s", "s'.s", "tid", pc.methodName, pgp.symbolsLow, failureReporter, "L");
      foreach (var clause in ens)
      {
        var rvalue = ensContext.ResolveAsRValue(clause);
        var e = rvalue.CanCauseUndefinedBehavior ? $"({rvalue.UndefinedBehaviorAvoidance.Expr}) && ({rvalue.Val})" : rvalue.Val;
        preds.Add(e);
      }

      if (extraLoopModifiesClausesForPC.ContainsKey(pc)) {
        foreach (var clauseName in extraLoopModifiesClausesForPC[pc]) {
          preds.Add($"{clauseName}(s, s', tid)");
        }
      }

      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is CHLYieldPredicateArmadaProofDecl d) {
          if (Attributes.FindExpressions(d.Attributes, "excludeLoop")?
              .Any(expr => (expr as NameSegment).Name == pc.methodName + "_" + pc.Name) ?? false) {
            continue;
          }
          if (Attributes.Contains(d.Attributes, "excludeAll")) {
            continue;
          }
          var ypKey = d.YieldPredicateName;
          if (d.Code != null || pgp.symbolsLow.YieldPredicates.ContainsKey(ypKey)) {
            preds.Add($"UserYP_{ypKey}(s, s', tid)");
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No yield predicate named {ypKey} found among the yield predicates");
            continue;
          }
        }
      }

      var fn = $@"
        predicate LoopModifies_{pc}(s: LPlusState, s': LPlusState, tid: Armada_ThreadHandle)
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(fn, "defs");
    }

    private void DeterminePCsWithEnablingConditions()
    {
      foreach (var pc in lpcs)
      {
        var methodInfo = pgp.symbolsHigh.AllMethods.LookupMethod(pc.methodName);
        var collector = methodInfo.GetEnablingConstraintCollector(pcMap[pc]);
        if (collector != null && !collector.Empty)
        {
          pcsWithEnablingConditions.Add(pc);
          pcsWithLocalInvariants.Add(pc);
        }
      }
    }

    private void GenerateLocalInv()
    {
      string str;

      str = @"
        predicate PCHasLocalInvariant(pc:L.Armada_PC)
        {
      ";
      str += AH.CombineStringsWithOr(pcsWithLocalInvariants.Select(pc => $"pc.{pc}?"));
      str += "}";
      pgp.AddPredicate(str, "defs");

      if (pcsWithLocalInvariants.Any()) {
        str = @"
          predicate LocalInv(s:LPlusState, tid:Armada_ThreadHandle)
          {
            tid in s.s.threads ==>
              H.Armada_UniversalStepConstraint(ConvertTotalState_LPlusH(s), tid) &&
              var t := s.s.threads[tid];
              PCHasLocalInvariant(t.pc) && InductiveInv(s) ==>
                match t.pc
        ";
        foreach (var pc in pcsWithLocalInvariants) {
          str += $"case {pc} => t.top.Armada_StackFrame_{pc.methodName}?";
          if (pcsWithEnablingConditions.Contains(pc)) {
            str += $" && H.Armada_EnablingConditions_{pcMap[pc]}(ConvertTotalState_LPlusH(s), tid)";
          }
          if (extraLocalInvariantClausesForPC.ContainsKey(pc)) {
            foreach (var fnName in extraLocalInvariantClausesForPC[pc]) {
              str += $" && {fnName}(s, tid)";
            }
          }
          str += "\n";
        }
        str += "}\n";
        pgp.AddPredicate(str, "defs");
      }
      else {
        str = @"
          predicate LocalInv(s:LPlusState, tid:Armada_ThreadHandle)
          {
            tid in s.s.threads ==> PCHasLocalInvariant(s.s.threads[tid].pc)
          }
        ";
        pgp.AddPredicate(str, "defs");
      }
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
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          if (d.Code != null) {
            invName = $"UserInv_{invKey}";
            str = $@"
              predicate {attrs} {invName}(s: LPlusState)
              {{
                var threads := s.s.threads;
                var globals := s.s.mem.globals;
                var ghosts := s.s.ghosts;
                var tid_init := s.config.tid_init;
                { d.Code }
              }}
            ";
            pgp.AddPredicate(str, "defs");
            if (d.CanBeRevealed()) {
              pgp.AddOpaqueUserDef(invName);
            }
          }
          else if (userInvariants.ContainsKey(invKey)) {
            var inv = userInvariants[invKey];
            invName = $"UserInv_{invKey}";
            str = $@"
              predicate {attrs} {invName}(s: LPlusState)
              {{
                L.{inv.TranslatedName}(s.s)
              }}
              ";
            pgp.AddPredicate(str, "defs");
            if (d.CanBeRevealed()) {
              pgp.AddOpaqueUserDef(invName);
            }
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No invariant named {invKey} found among the invariants");
            continue;
          }
          globalInvariantInfos.Add(new CHLPredicateInfo(invKey, invName, d.CanBeRevealed()));
          allInvClauses += $"  && {invName}(s)\n";
        }
      }

      var body = (allInvClauses.Length == 0) ? "true" : $"InductiveInv(s) ==> {allInvClauses}";

      str = $@"
        predicate GlobalInv(s: LPlusState)
        {{
          var threads := s.s.threads;
          var globals := s.s.mem.globals;
          var ghosts := s.s.ghosts;
          var tid_init := s.config.tid_init;
          {body}
        }}
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateCustomCHLClauses()
    {
      string str;
      foreach (var topDecl in pgp.MainProof.Module.TopLevelDecls) {
        if (topDecl is CHLLocalInvariantArmadaProofDecl) {
          var d = (CHLLocalInvariantArmadaProofDecl)topDecl;
          var pc = pgp.symbolsLow.GetPCForMethodAndLabel(d.PCName);
          if (pc == null) {
            AH.PrintError(pgp.prog, $"Could not find PC corresponding to CHL local invariant clause with specified label {d.PCName}");
          }
          var methodName = pc.methodName;
          var fnName = $"UserLocalInvariant_{methodName}_{pc.Name}_{d.ClauseName}";
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          str = $@"
            predicate {attrs} {fnName}(s:LPlusState, tid:Armada_ThreadHandle)
              requires tid in s.s.threads
              requires s.s.threads[tid].top.Armada_StackFrame_{methodName}?
              requires InductiveInv(s)
            {{
              var threads := s.s.threads;
              var globals := s.s.mem.globals;
              var ghosts := s.s.ghosts;
              var tid_init := s.config.tid_init;
              { d.Code }
            }}
          ";
          pgp.AddPredicate(str, "defs");
          if (d.CanBeRevealed()) {
            pgp.AddOpaqueUserDef(fnName);
          }
          pcsWithLocalInvariants.Add(pc);
          if (!extraLocalInvariantClausesForPC.ContainsKey(pc)) {
            extraLocalInvariantClausesForPC[pc] = new List<string>{ fnName };
          }
          else {
            extraLocalInvariantClausesForPC[pc].Add(fnName);
          }
        }
        else if (topDecl is CHLPreconditionArmadaProofDecl) {
          var d = (CHLPreconditionArmadaProofDecl)topDecl;
          var methodName = d.MethodName;
          var preconditionName = $"UserPrecondition_{methodName}_{d.PreconditionName}";
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          str = $@"
            predicate {attrs} {preconditionName}(s:LPlusState, tid:Armada_ThreadHandle)
              requires tid in s.s.threads
              requires s.s.threads[tid].top.Armada_StackFrame_{methodName}?
            {{
              var threads := s.s.threads;
              var globals := s.s.mem.globals;
              var ghosts := s.s.ghosts;
              var tid_init := s.config.tid_init;
              { d.Code }
            }}
          ";
          pgp.AddPredicate(str, "defs");
          if (d.CanBeRevealed()) {
            pgp.AddOpaqueUserDef(preconditionName);
          }
          if (!extraPreconditionsForMethod.ContainsKey(methodName)) {
            extraPreconditionsForMethod[methodName] = new List<string>{ preconditionName };
          }
          else {
            extraPreconditionsForMethod[methodName].Add(preconditionName);
          }
        }
        else if (topDecl is CHLPostconditionArmadaProofDecl) {
          var d = (CHLPostconditionArmadaProofDecl)topDecl;
          var methodName = d.MethodName;
          var postconditionName = $"UserPostcondition_{methodName}_{d.PostconditionName}";
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          str = $@"
            predicate {attrs} {postconditionName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              requires tid in s.s.threads
              requires s.s.threads[tid].top.Armada_StackFrame_{methodName}?
              requires tid in s'.s.threads
              requires s'.s.threads[tid].top.Armada_StackFrame_{methodName}?
            {{
              var threads := s.s.threads;
              var globals := s.s.mem.globals;
              var ghosts := s.s.ghosts;
              var tid_init := s.config.tid_init;
              var threads' := s'.s.threads;
              var globals' := s'.s.mem.globals;
              var ghosts' := s'.s.ghosts;
              { d.Code }
            }}
          ";
          pgp.AddPredicate(str, "defs");
          if (d.CanBeRevealed()) {
            pgp.AddOpaqueUserDef(postconditionName);
          }
          if (!extraPostconditionsForMethod.ContainsKey(methodName)) {
            extraPostconditionsForMethod[methodName] = new List<string>{ postconditionName };
          }
          else {
            extraPostconditionsForMethod[methodName].Add(postconditionName);
          }
        }
        else if (topDecl is CHLLoopModifiesClauseArmadaProofDecl) {
          var d = (CHLLoopModifiesClauseArmadaProofDecl)topDecl;
          var pc = pgp.symbolsLow.GetPCForMethodAndLabel(d.PCName);
          if (pc == null) {
            AH.PrintError(pgp.prog, $"Could not find PC corresponding to CHL loop modifies clause with specified label {d.PCName}");
          }
          var methodName = pc.methodName;
          var fnName = $"UserLoopModifies_{methodName}_{pc.Name}_{d.ClauseName}";
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          str = $@"
            predicate {attrs} {fnName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              requires tid in s.s.threads
              requires s.s.threads[tid].top.Armada_StackFrame_{methodName}?
              requires tid in s'.s.threads
              requires s'.s.threads[tid].top.Armada_StackFrame_{methodName}?
            {{
              var threads := s.s.threads;
              var globals := s.s.mem.globals;
              var ghosts := s.s.ghosts;
              var tid_init := s.config.tid_init;
              var threads' := s'.s.threads;
              var globals' := s'.s.mem.globals;
              var ghosts' := s'.s.ghosts;
              { d.Code }
            }}
          ";
          pgp.AddPredicate(str, "defs");
          if (d.CanBeRevealed()) {
            pgp.AddOpaqueUserDef(fnName);
          }
          if (!extraLoopModifiesClausesForPC.ContainsKey(pc)) {
            extraLoopModifiesClausesForPC[pc] = new List<string>{ fnName };
          }
          else {
            extraLoopModifiesClausesForPC[pc].Add(fnName);
          }
        }
      }
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
          var attrs = d.CanBeRevealed() ? "{:opaque}" : "";
          if (d.Code != null) {
            ypName = $"UserYP_{ypKey}";
            str = $@"
              predicate {attrs} {ypName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              {{
                var threads := s.s.threads;
                var globals := s.s.mem.globals;
                var ghosts := s.s.ghosts;
                var tid_init := s.config.tid_init;
                var threads' := s'.s.threads;
                var globals' := s'.s.mem.globals;
                var ghosts' := s'.s.ghosts;
                {d.Code}
              }}
            ";
            pgp.AddPredicate(str, "defs");
            if (d.CanBeRevealed()) {
              pgp.AddOpaqueUserDef(ypName);
            }
          }
          else if (userYPs.ContainsKey(ypKey)) {
            ypName = $"UserYP_{ypKey}";
            var yp = userYPs[ypKey];
            str = $@"
              predicate {attrs} {ypName}(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
              {{
                tid in s.s.threads && tid in s'.s.threads ==> L.{yp.TranslatedName}(s.s, s'.s, tid)
              }}
            ";
            pgp.AddPredicate(str, "defs");
            if (d.CanBeRevealed()) {
              pgp.AddOpaqueUserDef(ypName);
            }
          }
          else {
            AH.PrintError(pgp.prog, d.tok, $"No yield predicate named {ypKey} found among the yield predicates");
            continue;
          }
          yieldPredicateInfos.Add(new CHLPredicateInfo(ypKey, ypName, d.CanBeRevealed()));
          allYieldClauses += $"  && {ypName}(s, s', tid)\n";
        }
      }

      str = @"
        predicate YieldPredicateBasic(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {
          && tid in s.s.threads
          && tid in s'.s.threads
          && s'.s.threads[tid].pc == s.s.threads[tid].pc
          && s'.s.threads[tid].top == s.s.threads[tid].top
          && s'.s.threads[tid].stack == s.s.threads[tid].stack
          && s'.config == s.config
          && s'.s.stop_reason.Armada_NotStopped?
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = $@"
        predicate YieldPredicate(s:LPlusState, s':LPlusState, tid:Armada_ThreadHandle)
        {{
          YieldPredicateBasic(s, s', tid)
          {allYieldClauses}
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

    private void GeneratePathPCStackEffectLemmas()
    {
      pcstackFile = pgp.proofFiles.CreateAuxiliaryProofFile("pcstack");
      pcstackFile.IncludeAndImportGeneratedFile("specs");
      pcstackFile.IncludeAndImportGeneratedFile("pceffect");
      pcstackFile.IncludeAndImportGeneratedFile("revelations");
      pcstackFile.IncludeAndImportGeneratedFile("latomic");
      pcstackFile.IncludeAndImportGeneratedFile("defs");
      pcstackFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      pcstackFile.AddImport("ConcurrentHoareLogicSpecModule");
      pcstackFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      pcstackFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      pcstackFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      pcstackFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      pcstackFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("pcstack");

      string str;
      var pr = new PathPrinter(lAtomic);
      foreach (var atomicPath in lAtomic.AtomicPaths)
      {
        str = $@"
          lemma lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle
            )
            requires LAtomic_NextPath(s, s', path, tid)
            requires path.LAtomic_Path_{atomicPath.Name}?
            ensures  tid in s.s.threads
            ensures  s.s.stop_reason.Armada_NotStopped?
            ensures  s'.config == s.config
        ";

        // What PC it starts at

        if (!atomicPath.Tau) {
          str += $"ensures  s.s.threads[tid].pc.{atomicPath.StartPC}?\n";
        }

        // What constraints there are on the initial stack

        var effect = pathEffectMap[atomicPath];
        if (effect is CHLPathEffectReturn) {
          var reffect = (CHLPathEffectReturn)effect;
          str += $@"
            ensures |s.s.threads[tid].stack| > 0
            ensures s.s.threads[tid].stack[0].return_pc.{reffect.EffectiveStartPC}?
          ";
        }
        else if (effect is CHLPathEffectReturnThenCall) {
          var rceffect = (CHLPathEffectReturnThenCall)effect;
          str += $@"
            ensures |s.s.threads[tid].stack| > 0
            ensures s.s.threads[tid].stack[0].return_pc.{rceffect.EffectiveStartPC}?
          ";
        }
        else if (effect is CHLPathEffectExit) {
          str += "ensures |s.s.threads[tid].stack| == 0\n";
        }

        // Constraints on the subsequent PC and stack

        if (atomicPath.Stopping) {
          str += "ensures !s'.s.stop_reason.Armada_NotStopped?\n";
        }
        else {
          str += "ensures s'.s.stop_reason.Armada_NotStopped?\n";

          // Constraints on the subsequent PC

          if (atomicPath.Tau) {
            str += "ensures tid in s'.s.threads\n";
          }
          else if (atomicPath.EndPC == null) {
            str += $"ensures tid !in s'.s.threads\n";
          }
          else {
            str += $@"
              ensures tid in s'.s.threads
              ensures s'.s.threads[tid].pc.{atomicPath.EndPC}?
            ";
          }

          // Constraints on the subsequent stack

          if (effect is CHLPathEffectNormal) {
            str += "ensures s'.s.threads[tid].stack == s.s.threads[tid].stack\n";
          }
          else if (effect is CHLPathEffectCall) {
            var ceffect = (CHLPathEffectCall)effect;
            str += $@"
              ensures |s'.s.threads[tid].stack| > 0
              ensures s'.s.threads[tid].stack[0].return_pc.{ceffect.EffectiveEndPC}?
              ensures s'.s.threads[tid].stack[1..] == s.s.threads[tid].stack
            ";
          }
          else if (effect is CHLPathEffectReturn) {
            str += $@"
              ensures s'.s.threads[tid].stack == s.s.threads[tid].stack[1..]
            ";
          }
          else if (effect is CHLPathEffectReturnThenCall) {
            var rceffect = (CHLPathEffectReturnThenCall)effect;
            str += $@"
              ensures |s'.s.threads[tid].stack| > 0
              ensures s'.s.threads[tid].stack[0].return_pc.{rceffect.EffectiveEndPC}?
              ensures s'.s.threads[tid].stack[1..] == s.s.threads[tid].stack[1..]
            ";
          }
          else if (effect is CHLPathEffectActorless) {
            str += "ensures s'.s.threads[tid].stack == s.s.threads[tid].stack\n";
          }
        }

        str += $@"
          {{
            { pr.GetOpenValidPathInvocation(atomicPath) }
          }}
        ";
        pgp.AddLemma(str, "pcstack");
      }

      str = @"
        lemma lemma_PathImpliesThreadRunning(
          s: LPlusState,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          ensures  var asf := LAtomic_GetSpecFunctions();
                   asf.path_valid(s, path, tid) ==> asf.state_ok(s) && asf.get_thread_pc(s, tid).Some?
        {
          var asf := LAtomic_GetSpecFunctions();
          if asf.path_valid(s, path, tid) {
            var s' := asf.path_next(s, path, tid);
            match path {
      ";
      str += String.Concat(lAtomic.AtomicPaths.Select(atomicPath => $@"
            case LAtomic_Path_{atomicPath.Name}(_) =>
              lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, tid);
      "));
      str += "} } }\n";
      pgp.AddLemma(str, "pcstack");

      str = @"
        lemma lemma_PathLeavesConfigUnchanged(
          s: LPlusState,
          s': LPlusState,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          requires LAtomic_NextPath(s, s', path, tid)
          ensures  s'.config == s.config
        {
          match path {
      ";
      str += String.Concat(lAtomic.AtomicPaths.Select(atomicPath => $@"
            case LAtomic_Path_{atomicPath.Name}(_) =>
              lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, tid);
      "));
      str += "} }\n";
      pgp.AddLemma(str, "pcstack");

      str = @"
        lemma lemma_CHLStepEffectsCorrect()
          ensures  CHLStepEffectsCorrect(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall s, s', step | ActionTuple(s, s', step) in cr.spec.next
            ensures CorrectCHLStepEffect(cr, s, s', step)
          {
            var path: LAtomic_Path := step.path;
            var tid := step.tid;

            match path {
      ";
      str += String.Concat(lAtomic.AtomicPaths.Select(p => $@"
            case LAtomic_Path_{p.Name}(_) =>
              lemma_LAtomic_PathHasPCStackEffect_{p.Name}(s, s', path, tid);
      "));
      str += "} } }\n";
      pgp.AddLemma(str, "pcstack");

      foreach (var pc in lpcs)
      {
        str = $@"
          predicate PathPossibilitiesStartingAtPC_{pc}(path: LAtomic_Path)
          {{
        ";
        str += AH.CombineStringsWithOr(pathsStartingAtPC[pc].Select(p => $"path.LAtomic_Path_{p.Name}?"));
        str += "}";
        pgp.AddPredicate(str, "pcstack");

        str = $@"
          lemma lemma_PathPossibilitiesStartingAtPC_{pc}(s: LPlusState, s': LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
            requires LAtomic_NextPath(s, s', path, tid)
            requires !path.LAtomic_Path_Tau?
            requires tid in s.s.threads
            requires s.s.threads[tid].pc.{pc}?
            ensures  PathPossibilitiesStartingAtPC_{pc}(path)
          {{
            match path {{
        ";
        str += String.Concat(lAtomic.AtomicPaths.Where(p => !p.Tau).Select(p => $@"
            case LAtomic_Path_{p.Name}(_) =>
              lemma_LAtomic_PathHasPCStackEffect_{p.Name}(s, s', path, tid);
        "));
        str += "} }";
        pgp.AddLemma(str, "pcstack");
      }

      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        str = $@"
          predicate PathPossibilitiesReturningFrom_{methodName}(path: LAtomic_Path)
          {{
        ";
        str += AH.CombineStringsWithOr(pathsStartingAtPC[returnPCForMethod[methodName]]
                                       .Select(p => $"path.LAtomic_Path_{p.Name}?"));
        str += "}";
        pgp.AddPredicate(str, "pcstack");

        str = $@"
          lemma lemma_PathPossibilitiesReturningFrom_{methodName}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle
            )
            requires LAtomic_NextPath(s, s', path, tid)
            requires !path.LAtomic_Path_Tau?
            requires tid in s.s.threads
            requires IsReturnSite(s.s.threads[tid].pc)
            requires PCToProc(s.s.threads[tid].pc).LProcName_{methodName}?
            ensures  PathPossibilitiesReturningFrom_{methodName}(path)
          {{
            match path {{
        ";
        str += String.Concat(lAtomic.AtomicPaths.Where(p => !p.Tau).Select(p => $@"
            case LAtomic_Path_{p.Name}(_) =>
              lemma_LAtomic_PathHasPCStackEffect_{p.Name}(s, s', path, tid);
        "));
        str += "} }";
        pgp.AddLemma(str, "pcstack");
      }
    }

    private void GenerateProofThatCHLRequestIsValid()
    {
      GenerateGlobalInvLemmas();
      GenerateYieldPredicateLemmas();
      GenerateInitialInvariantLemmas();
      GenerateStepsDontAffectOtherActorsLemmas();
      GenerateForkedActorsStartAtEntryPointsWithEmptyStacks();
      GenerateStraightlineBehaviorProofs();
    }

    private void GenerateStepsDontAffectOtherActorsLemmas()
    {
      var othersFile = pgp.proofFiles.CreateAuxiliaryProofFile("others");
      othersFile.IncludeAndImportGeneratedFile("specs");
      othersFile.IncludeAndImportGeneratedFile("defs");
      othersFile.IncludeAndImportGeneratedFile("revelations");
      othersFile.IncludeAndImportGeneratedFile("latomic");
      othersFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      othersFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaAtomic.i.dfy");
      othersFile.AddImport("ConcurrentHoareLogicSpecModule");
      othersFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      othersFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      othersFile.AddImport("util_collections_seqs_s");
      othersFile.AddImport("GenericArmadaAtomicModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("others");

      string postcondition = @"forall other_tid ::
                               (other_tid != tid || asf.path_type(path).AtomicPathType_Tau?) && other_tid in s.s.threads ==>
                               var s' := asf.path_next(s, path, tid);
                               && other_tid in s'.s.threads
                               && s'.s.threads[other_tid].pc == s.s.threads[other_tid].pc
                               && s'.s.threads[other_tid].top == s.s.threads[other_tid].top
                               && s'.s.threads[other_tid].stack == s.s.threads[other_tid].stack";
      lAtomic.GeneratePerAtomicPathLemma("others",
                                         "AtomicPathCantAffectOtherThreadsExceptViaFork",
                                         atomicPath => true,
                                         atomicPath => postcondition,
                                         atomicPath => "",
                                         false);
      lAtomic.GenerateOverallAtomicPathLemma("others",
                                             "AtomicPathCantAffectOtherThreadsExceptViaFork",
                                             "AtomicPathCantAffectOtherThreadsExceptViaFork",
                                             postcondition,
                                             ap => true);

      string str = $@"
        lemma lemma_StepsDontChangeOtherActorsExceptViaFork()
          ensures StepsDontChangeOtherActorsExceptViaFork(GetConcurrentHoareLogicRequest())
        {{
          var cr := GetConcurrentHoareLogicRequest();
          forall s, s', step, other_actor | StepsDontChangeOtherActorsExceptViaForkConditions(cr, s, s', step, other_actor)
            ensures cr.get_actor_pc_stack(s', other_actor) == cr.get_actor_pc_stack(s, other_actor)
          {{
            var asf := LAtomic_GetSpecFunctions();
            lemma_LAtomic_AtomicPathCantAffectOtherThreadsExceptViaFork(asf, s, step.path, step.tid);
          }}
        }}
      ";
      pgp.AddLemma(str, "others");
    }

    private void GenerateForkedActorsStartAtEntryPointsWithEmptyStacks()
    {
      var forkedStacksFile = pgp.proofFiles.CreateAuxiliaryProofFile("ForkedStack");
      forkedStacksFile.IncludeAndImportGeneratedFile("specs");
      forkedStacksFile.IncludeAndImportGeneratedFile("defs");
      forkedStacksFile.IncludeAndImportGeneratedFile("revelations");
      forkedStacksFile.IncludeAndImportGeneratedFile("latomic");
      forkedStacksFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      forkedStacksFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaAtomic.i.dfy");
      forkedStacksFile.AddImport("ConcurrentHoareLogicSpecModule");
      forkedStacksFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      forkedStacksFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      forkedStacksFile.AddImport("util_collections_seqs_s");
      forkedStacksFile.AddImport("GenericArmadaAtomicModule");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("ForkedStack");

      string str;

      var postcondition = @"forall forked_tid :: forked_tid !in s.s.threads && forked_tid in asf.path_next(s, path, tid).s.threads ==>
                        var cr := GetConcurrentHoareLogicRequest();
                        var s' := asf.path_next(s, path, tid);
                        && cr.step_to_actor(PathAndTid(path, tid)).Some?
                        && !cr.step_to_effect(PathAndTid(path, tid)).CHLStepEffectExit?
                        && var PCStack(pc', stack') := cr.get_actor_pc_stack(s', forked_tid).v;
                        && cr.is_entry_point(pc')
                        && |stack'| == 0";
      lAtomic.GeneratePerAtomicPathLemma("ForkedStack",
                                         "ForkedActorsStartAtEntryPointsWithEmptyStacks",
                                         atomicPath => true,
                                         atomicPath => postcondition,
                                         atomicPath => "",
                                         false);
      lAtomic.GenerateOverallAtomicPathLemma("ForkedStack",
                                             "ForkedActorsStartAtEntryPointsWithEmptyStacks",
                                             "ForkedActorsStartAtEntryPointsWithEmptyStacks",
                                             postcondition,
                                             atomicPath => true);
      str = $@"
        lemma lemma_ForkedActorsStartAtEntryPointsWithEmptyStacks()
          ensures ForkedActorsStartAtEntryPointsWithEmptyStacks(GetConcurrentHoareLogicRequest())
        {{
          var cr := GetConcurrentHoareLogicRequest();
          forall s, s', step, forked_actor | ForkedActorsStartAtEntryPointsWithEmptyStacksConditions(cr, s, s', step, forked_actor)
            ensures cr.step_to_actor(step).Some?
            ensures !cr.step_to_effect(step).CHLStepEffectExit?
            ensures var PCStack(pc', stack') := cr.get_actor_pc_stack(s', forked_actor).v;
                    && cr.is_entry_point(pc')
                    && |stack'| == 0
          {{
            var asf := LAtomic_GetSpecFunctions();
            lemma_LAtomic_ForkedActorsStartAtEntryPointsWithEmptyStacks(asf, s, step.path, step.tid);
          }}
        }}
      ";
      pgp.AddLemma(str, "ForkedStack");
    }

    private void GenerateGlobalInvLemmas()
    {
      string str;
      string lemmaInvocations = "";

      var pr = new PathPrinter(lAtomic);
      foreach (var globalInvariantInfo in globalInvariantInfos)
      {
        str = $@"
          lemma lemma_ActorlessStepsMaintainSpecificGlobalInv_{globalInvariantInfo.Key}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle
            )
            requires path.LAtomic_Path_Tau?
            requires InductiveInv(s)
            requires GlobalInv(s)
            requires LAtomic_NextPath(s, s', path, tid)
            requires InductiveInv(s')
            ensures  {globalInvariantInfo.Value}(s')
          {{
            { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);
        lemmaInvocations += $@"
          lemma_ActorlessStepsMaintainSpecificGlobalInv_{globalInvariantInfo.Key}(s, s', path, tid);
        ";
      }

      str = $@"
        lemma lemma_ActorlessStepsMaintainGlobalInv(
          s: LPlusState,
          s': LPlusState,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          requires path.LAtomic_Path_Tau?
          requires InductiveInv(s)
          requires GlobalInv(s)
          requires LAtomic_NextPath(s, s', path, tid)
          ensures  GlobalInv(s')
          ensures  s'.s.stop_reason.Armada_NotStopped?
        {{
          if InductiveInv(s') {{
            { lemmaInvocations }
          }}
          lemma_LAtomic_PathHasPCStackEffect_Tau(s, s', path, tid);
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateYieldPredicateLemmas()
    {
      string str;

      var pr = new PathPrinter(lAtomic);

      foreach (var yieldPredicateInfo in yieldPredicateInfos)
      {
        string yieldPredicateName = yieldPredicateInfo.Key;
        string fullyQualifiedYPName = yieldPredicateInfo.Value;

        str = $@"
          lemma lemma_YieldPredicateReflexive_{yieldPredicateName}(s:LPlusState, actor:Armada_ThreadHandle)
            requires s.s.stop_reason.Armada_NotStopped?
            requires actor in s.s.threads
            ensures {fullyQualifiedYPName}(s, s, actor)
          {{
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);

        str = $@"
          lemma lemma_YieldPredicateTransitive_{yieldPredicateName}(
            s1: LPlusState,
            s2: LPlusState,
            s3: LPlusState,
            actor: Armada_ThreadHandle
            )
            requires InductiveInv(s1)
            requires GlobalInv(s1)
            requires InductiveInv(s2)
            requires GlobalInv(s2)
            requires actor in s1.s.threads
            requires actor in s2.s.threads
            requires actor in s3.s.threads
            requires YieldPredicate(s1, s2, actor)
            requires YieldPredicate(s2, s3, actor)
            ensures  {fullyQualifiedYPName}(s1, s3, actor)
          {{
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);

        str = $@"
          lemma lemma_ActorlessStepsMaintainYieldPredicate_{yieldPredicateName}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            actor: Armada_ThreadHandle
            )
            requires path.LAtomic_Path_Tau?
            requires InductiveInv(s)
            requires GlobalInv(s)
            requires LAtomic_NextPath(s, s', path, tid)
            requires GlobalInv(s')
            ensures  {fullyQualifiedYPName}(s, s', actor)
          {{
            { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);
      }

      str = @"
        lemma lemma_YieldPredicateReflexive()
          ensures YieldPredicateReflexive(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall s, actor {:trigger cr.yield_pred(s, s, actor)} | cr.state_ok(s) && cr.get_actor_pc_stack(s, actor).Some?
            ensures cr.yield_pred(s, s, actor)
          {
      ";
      foreach (var yieldPredicateInfo in yieldPredicateInfos)
      {
        str += $"lemma_YieldPredicateReflexive_{yieldPredicateInfo.Key}(s, actor);\n";
      }
      str += @"
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_YieldPredicateTransitive()
          ensures YieldPredicateTransitive(GetConcurrentHoareLogicRequest())
        {
          forall s1, s2, s3, actor |
            && InductiveInv(s1)
            && GlobalInv(s1)
            && InductiveInv(s2)
            && GlobalInv(s2)
            && YieldPredicate(s1, s2, actor)
            && YieldPredicate(s2, s3, actor)
            ensures YieldPredicate(s1, s3, actor)
          {
            if actor in s1.s.threads && actor in s2.s.threads && actor in s3.s.threads {
      ";
      foreach (var yieldPredicateInfo in yieldPredicateInfos)
      {
        str += $"        lemma_YieldPredicateTransitive_{yieldPredicateInfo.Key}(s1, s2, s3, actor);";
      }
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_ActorlessStepsMaintainYieldPredicateAndGlobalInvariant()
          ensures ActorlessStepsMaintainYieldPredicateAndGlobalInvariant(GetConcurrentHoareLogicRequest())
        {{
          var cr := GetConcurrentHoareLogicRequest();
          forall s, s', step, actor | ActorlessStepsMaintainYieldPredicateAndGlobalInvariantConditions(cr, s, s', step, actor)
            ensures YieldPredicate(s, s', actor)
            ensures GlobalInv(s')
            ensures s'.s.stop_reason.Armada_NotStopped?
          {{
            var path: LAtomic_Path := step.path;
            var tid := step.tid;

            assert path.LAtomic_Path_Tau?;

            { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
            ProofCustomizationGoesHere();

            assert InductiveInv(s);
            assert GlobalInv(s);
            assert LAtomic_NextPath(s, s', step.path, step.tid);
            lemma_ActorlessStepsMaintainGlobalInv(s, s', step.path, step.tid);
      ";
      foreach (var yieldPredicateInfo in yieldPredicateInfos)
      {
        str += $@"
            lemma_ActorlessStepsMaintainYieldPredicate_{yieldPredicateInfo.Key}(s, s', step.path, step.tid, actor);
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

      foreach (var globalInvariantInfo in globalInvariantInfos)
      {
        str = $@"
          lemma lemma_GlobalInvariantSatisfiedInitially_{globalInvariantInfo.Key}(s:LPlusState)
            requires LPlus_Init(s)
            ensures  {globalInvariantInfo.Value}(s)
          {{
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str);

        body += $"lemma_GlobalInvariantSatisfiedInitially_{globalInvariantInfo.Key}(s);\n";
      }

      str = $@"
        lemma lemma_GlobalInvariantSatisfiedInInitialState(s:LPlusState)
          requires LPlus_Init(s)
          ensures  GlobalInv(s)
        {{
          {body}
        }}
      ";
      pgp.AddLemma(str);

      body = "";

      str = @"
        lemma lemma_RequiresClausesSatisfiedInInitialState(s:LPlusState, tid:Armada_ThreadHandle)
          requires LPlus_Init(s)
          requires tid in s.s.threads
          ensures  RequiresClauses(LProcName_main, s, tid)
        {
          assert Preconditions_main(s, tid);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_GlobalInvariantSatisfiedInitially()
          ensures  GlobalInvariantSatisfiedInitially(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall s | s in cr.spec.init
            ensures cr.global_inv(s)
          {
            lemma_GlobalInvariantSatisfiedInInitialState(s);
          }
       }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_RequiresClausesSatisfiedInitially()
          ensures  RequiresClausesSatisfiedInitially(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall s, actor | RequiresClausesSatisfiedInitiallyConditions(cr, s, actor)
            ensures cr.requires_clauses(cr.pc_to_proc(cr.get_actor_pc_stack(s, actor).v.pc), s, actor)
          {
            lemma_RequiresClausesSatisfiedInInitialState(s, actor);
            assert cr.pc_to_proc(cr.get_actor_pc_stack(s, actor).v.pc) == LProcName_main;
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateIsValidConcurrentHoareLogicRequest()
    {
      string str;

      var pr = new PathPrinter(lAtomic);

      str = @"
        lemma lemma_IsInvariantPredicateOfSpec()
          ensures IsInvariantPredicateOfSpec(InductiveInv, GetCHLSpec())
        {
          var inv := InductiveInv;
          var spec := GetCHLSpec();

          forall s | s in spec.init
            ensures inv(s)
          {
            lemma_InitImpliesInductiveInv(s);
          }

          forall s, s', step | inv(s) && ActionTuple(s, s', step) in spec.next
            ensures inv(s')
          {
            lemma_AtomicPathMaintainsInductiveInv(s, s', step.path, step.tid);
          }

          lemma_EstablishInvariantPredicatePure(inv, spec);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LoopHeadsArentReturnSites()
          ensures LoopHeadsArentReturnSites(IsLoopHead, IsReturnSite)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ActorsBeginAtEntryPointsWithEmptyStacks()
          ensures ActorsBeginAtEntryPointsWithEmptyStacks(GetConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_ActorlessStepsDontChangeActors()
          ensures ActorlessStepsDontChangeActors(GetConcurrentHoareLogicRequest())
        {{
          var cr := GetConcurrentHoareLogicRequest();
          forall s, s', step, actor {{:trigger ActorlessStepsDontChangeActorsConditions(cr, s, s', step, actor)}}
            | ActorlessStepsDontChangeActorsConditions(cr, s, s', step, actor)
            ensures cr.get_actor_pc_stack(s', actor) == cr.get_actor_pc_stack(s, actor)
          {{
            var path: LAtomic_Path := step.path;
            var tid := step.tid;

            { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_IsValidConcurrentHoareLogicRequest()
          ensures  IsValidConcurrentHoareLogicRequest(GetConcurrentHoareLogicRequest())
        {
          lemma_IsInvariantPredicateOfSpec();
          lemma_LoopHeadsArentReturnSites();
          lemma_YieldPredicateReflexive();
          lemma_YieldPredicateTransitive();
          lemma_ActorsBeginAtEntryPointsWithEmptyStacks();
          lemma_GlobalInvariantSatisfiedInitially();
          lemma_RequiresClausesSatisfiedInitially();
          lemma_ActorlessStepsDontChangeActors();
          lemma_ActorlessStepsMaintainYieldPredicateAndGlobalInvariant();
          lemma_CHLStepEffectsCorrect();
          lemma_ForkedActorsStartAtEntryPointsWithEmptyStacks();
          lemma_StepsDontChangeOtherActorsExceptViaFork();
          lemma_StraightlineBehaviorsSatisfyGlobalInvariant();
          lemma_StraightlineBehaviorsSatisfyLocalInvariant();
          lemma_StraightlineBehaviorsSatisfyPreconditionsForCalls();
          lemma_StraightlineBehaviorsSatisfyPreconditionsForForks();
          lemma_StraightlineBehaviorsSatisfyPostconditions();
          lemma_StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntry();
          lemma_StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBack();
          lemma_StraightlineBehaviorsSatisfyYieldPredicate();
        }
        ";
      pgp.AddLemma(str);
    }

    private void AddAllSuffixesOfStraightlineBehavior(StraightlineBehavior behavior)
    {
      straightlineBehaviorDescriptors.Add(behavior);
      if (behavior.LastState is StraightlineStateNormal) {
        sbdsEndingNormal.Add(behavior);
      }
      if (behavior.LastState is StraightlineStateYielded) {
        sbdsEndingYielded.Add(behavior);
      }
      if (behavior.LastState is StraightlineStateEnsured) {
        sbdsEndingEnsured.Add(behavior);
      }
      foreach (var successorStep in behavior.LastState.GetSuccessorSteps(pathsStartingAtPC, loopHeads,
                                                                         pathEffectMap, returnPCForMethod, pcsWithLocalInvariants)) {
        var extension = new StraightlineBehavior(behavior, successorStep);
        AddAllSuffixesOfStraightlineBehavior(extension);
      }
    }

    private void CreateStraightlineBehaviors()
    {
      foreach (var methodName in pgp.symbolsLow.MethodNames)
      {
        var entryPoint = new ArmadaPC(pgp.symbolsLow, methodName, 0);
        var behavior = new StraightlineBehavior(entryPoint);
        emptyStraightlineBehaviorForMethod[methodName] = behavior;
        AddAllSuffixesOfStraightlineBehavior(behavior);
      }
    }

    private void GenerateStraightlineBehaviorDescriptors()
    {
      sbdFile = pgp.proofFiles.CreateAuxiliaryProofFile("sbd");
      sbdFile.IncludeAndImportGeneratedFile("specs");
      sbdFile.IncludeAndImportGeneratedFile("defs");
      sbdFile.IncludeAndImportGeneratedFile("revelations");
      sbdFile.IncludeAndImportGeneratedFile("latomic");
      sbdFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      sbdFile.AddImport("ConcurrentHoareLogicSpecModule");
      sbdFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      sbdFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      sbdFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("sbd");

      string str;

      str = "datatype StraightlineBehaviorDescriptor = ";
      str += String.Join(" | ", straightlineBehaviorDescriptors.Select(sb => $"SBD_{sb.Name}"));
      pgp.AddDatatype(str, "sbd");

      var extractorSTrace = new ExtractorSTrace("strace", "proc");
      foreach (var sbd in straightlineBehaviorDescriptors)
      {
        str = $@"
          predicate StraightlineBehaviorSatisfiesDescriptor_{sbd.Name}(strace:seq<LAtomicStraightlineStep>, proc:LProcName)
          {{
        ";
        str += String.Join(" && ", sbd.GetSatisfiesDescriptorClauses(extractorSTrace));
        str += "}";
        pgp.AddPredicate(str, "sbd");

        str = $@"
          predicate StraightlineBehaviorFullySatisfiesDescriptor_{sbd.Name}(strace:seq<LAtomicStraightlineStep>, proc:LProcName)
          {{
            && |strace| == {sbd.NumSteps}
            && StraightlineBehaviorSatisfiesDescriptor_{sbd.Name}(strace, proc)
          }}
        ";
        pgp.AddPredicate(str, "sbd");
      }

      str = @"
        predicate StraightlineBehaviorFullySatisfiesDescriptor(strace:seq<LAtomicStraightlineStep>, proc:LProcName,
                                                               sbd:StraightlineBehaviorDescriptor)
        {
          match sbd
      ";
      str += String.Concat(straightlineBehaviorDescriptors.Select(sbd => $@"
        case SBD_{sbd.Name} => StraightlineBehaviorFullySatisfiesDescriptor_{sbd.Name}(strace, proc)
      "));
      str += "}\n";
      pgp.AddPredicate(str, "sbd");
    }

    private void GenerateStraightlineBehaviorDescriptorExhaustiveLemmas()
    {
      exhaustiveFile = pgp.proofFiles.CreateAuxiliaryProofFile("exhaustive");
      exhaustiveFile.IncludeAndImportGeneratedFile("specs");
      exhaustiveFile.IncludeAndImportGeneratedFile("defs");
      exhaustiveFile.IncludeAndImportGeneratedFile("revelations");
      exhaustiveFile.IncludeAndImportGeneratedFile("latomic");
      exhaustiveFile.IncludeAndImportGeneratedFile("sbd");
      exhaustiveFile.IncludeAndImportGeneratedFile("pcstack");
      exhaustiveFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      exhaustiveFile.AddImport("ConcurrentHoareLogicSpecModule");
      exhaustiveFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      exhaustiveFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      exhaustiveFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("exhaustive");

      string str;

      str = @"
        function GetLAtomicStraightlineSpec(tid:Armada_ThreadHandle, proc:LProcName) : LAtomicStraightlineBehaviorSpec
        {
          GetStraightlineSpec(GetConcurrentHoareLogicRequest(), tid, proc)
        }
      ";
      pgp.AddFunction(str, "exhaustive");

      var extractorSB = new ExtractorSB("sb", "tid", "proc");

      foreach (var sbd in straightlineBehaviorDescriptors)
      {
        str = $@"
          lemma lemma_StraightlineBehaviorEndProperties_{sbd.Name}(
            sb:LAtomicStraightlineBehavior,
            tid:Armada_ThreadHandle,
            proc:LProcName
            )
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
            requires StraightlineBehaviorSatisfiesDescriptor_{sbd.Name}(sb.trace, proc)
            ensures  proc.LProcName_{sbd.MethodName}?
        ";
        foreach (var c in sbd.LastState.GetEndProperties(extractorSB))
        {
          str += $"ensures {c}\n";
        }
        str += "{\n";
        str += sbd.GetProofOfEndProperties(extractorSB);
        str += "}\n";
        pgp.AddLemma(str, "exhaustive");
      }

      foreach (var sbd in straightlineBehaviorDescriptors)
      {
        str = $@"
          lemma lemma_GetFullDescriptorForStraightlineBehavior_{sbd.Name}(
            sb:LAtomicStraightlineBehavior,
            tid:Armada_ThreadHandle,
            proc:LProcName
            ) returns (
            sbd:StraightlineBehaviorDescriptor
            )
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
            requires StraightlineBehaviorSatisfiesDescriptor_{sbd.Name}(sb.trace, proc)
            ensures  StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, sbd)
          {{
            if |sb.trace| == {sbd.NumSteps} {{
              sbd := SBD_{sbd.Name};
              return;
            }}
        ";
        foreach (var successor in sbd.Successors) {
          str += $@"
            if StraightlineBehaviorSatisfiesDescriptor_{successor.Name}(sb.trace, proc) {{
              sbd := lemma_GetFullDescriptorForStraightlineBehavior_{successor.Name}(sb, tid, proc);
              return;
            }}
          ";
        }

        str += $@"
          lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);

          var sspec := GetLAtomicStraightlineSpec(tid, proc);
          assert ActionTuple(sb.states[{sbd.NumSteps}], sb.states[{sbd.NumSteps}+1], sb.trace[{sbd.NumSteps}]) in sspec.next;
        ";
        str += sbd.LastState.ProofOfLimitedNextSSteps(extractorSB);
        str += "}";
        pgp.AddLemma(str, "exhaustive");
      }

      str = $@"
        lemma lemma_GetFullDescriptorForStraightlineBehavior(
          sb:LAtomicStraightlineBehavior,
          tid:Armada_ThreadHandle,
          proc:LProcName
          ) returns (
          sbd:StraightlineBehaviorDescriptor
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          ensures  StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, sbd)
        {{
          match proc {{
      ";
      str += String.Concat(emptyStraightlineBehaviorForMethod.Select(item => $@"
            case LProcName_{item.Key} =>
              sbd := lemma_GetFullDescriptorForStraightlineBehavior_{item.Value.Name}(sb, tid, proc);
      "));
      str += "} }\n";
      pgp.AddLemma(str, "exhaustive");
    }

    private void GenerateStraightlineBehaviorDescriptorEndLemma(string phase, IEnumerable<StraightlineBehavior> sbds)
    {
      string str;

      str = $@"
        predicate StraightlineBehaviorDescriptorEnds{phase}Possibilities(sbd:StraightlineBehaviorDescriptor)
        {{
      ";
      str += AH.CombineStringsWithOr(sbds.Select(sbd => $"sbd.SBD_{sbd.Name}?"));
      str += "}";
      pgp.AddPredicate(str, "continuation");

      str = $@"
        lemma lemma_GetFullDescriptorForStraightlineBehaviorEnding{phase}(
          sb:LAtomicStraightlineBehavior,
          tid:Armada_ThreadHandle,
          proc:LProcName
          ) returns (
          sbd:StraightlineBehaviorDescriptor
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          requires last(sb.states).aux.phase.StraightlinePhase{phase}?
          ensures  StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, sbd)
          ensures  StraightlineBehaviorDescriptorEnds{phase}Possibilities(sbd)
        {{
          sbd := lemma_GetFullDescriptorForStraightlineBehavior(sb, tid, proc);
          match sbd {{
      ";
      str += String.Concat(straightlineBehaviorDescriptors.Select(sbd => $@"
            case SBD_{sbd.Name} =>
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
      "));
      str += "} }\n";
      pgp.AddLemma(str, "continuation");
    }

    private void GenerateStraightlineBehaviorDescriptorContinuationLemmas()
    {
      var continuationFile = pgp.proofFiles.CreateAuxiliaryProofFile("continuation");
      continuationFile.IncludeAndImportGeneratedFile("specs");
      continuationFile.IncludeAndImportGeneratedFile("defs");
      continuationFile.IncludeAndImportGeneratedFile("latomic");
      continuationFile.IncludeAndImportGeneratedFile("sbd");
      continuationFile.IncludeAndImportGeneratedFile("pcstack");
      continuationFile.IncludeAndImportGeneratedFile("exhaustive");
      continuationFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      continuationFile.AddImport("ConcurrentHoareLogicSpecModule");
      continuationFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      continuationFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      continuationFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("continuation");

      GenerateStraightlineBehaviorDescriptorEndLemma("Ensured", sbdsEndingEnsured);
      GenerateStraightlineBehaviorDescriptorEndLemma("Yielded", sbdsEndingYielded);

      string str;

      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured))
      {
        str = $@"
          predicate StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(path:LAtomic_Path)
          {{
        ";
        str += AH.CombineStringsWithOr(sbd.PotentialSuccessorPaths
                                          .Where(tup => tup.Item2.CanFollow(sbd.LastState))
                                          .Select(tup => $"path.LAtomic_Path_{tup.Item1.Name}?"));
        str += "}";
        pgp.AddPredicate(str, "continuation");

        str = $@"
          lemma lemma_StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            tid: Armada_ThreadHandle,
            proc: LProcName,
            s': LPlusState,
            path: LAtomic_Path
            )
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires !path.LAtomic_Path_Tau?
            requires !PathToEffect(path).CHLStepEffectStop?
            requires var effect := PathToEffect(path);
         ";
        if (sbd.LastState is StraightlineStateEnsured) {
          str += $"effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall?\n";
        }
        else {
          str += $"!effect.CHLStepEffectReturn? && !effect.CHLStepEffectReturnThenCall?\n";
        }
        str += $@"
            ensures  StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(path)
          {{
            var ss := last(sb.states);
            assert ss == sb.states[{sbd.NumSteps}];
            var s := sb.states[{sbd.NumSteps}].state;
            assert s == ss.state;
            lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
        ";
        if (sbd.LastState is StraightlineStateEnsured) {
          var callee = ((StraightlineStateEnsured) sbd.LastState).Callee;
          str += $"lemma_PathPossibilitiesReturningFrom_{callee}(s, s', path, tid);\n";
        }
        else {
          str += $"lemma_PathPossibilitiesStartingAtPC_{sbd.LastState.PC}(s, s', path, tid);\n";
        }
        str += String.Concat(sbd.PotentialSuccessorPaths.Where(tup => !tup.Item2.CanFollow(sbd.LastState)).Select(tup => $@"
              if path.LAtomic_Path_{tup.Item1.Name}? {{
                lemma_LAtomic_PathHasPCStackEffect_{tup.Item1.Name}(s, s', path, tid);
                assert false;
              }}
          "));
          str += "}\n";
        pgp.AddLemma(str, "continuation");
      }
    }

    private void GenerateStraightlineBehaviorDescriptorEnumerationLemmas()
    {
      var enumerationFile = pgp.proofFiles.CreateAuxiliaryProofFile("enumeration");
      enumerationFile.IncludeAndImportGeneratedFile("specs");
      enumerationFile.IncludeAndImportGeneratedFile("defs");
      enumerationFile.IncludeAndImportGeneratedFile("latomic");
      enumerationFile.IncludeAndImportGeneratedFile("invariants");
      enumerationFile.IncludeAndImportGeneratedFile("sbd");
      enumerationFile.IncludeAndImportGeneratedFile("pcstack");
      enumerationFile.IncludeAndImportGeneratedFile("exhaustive");
      enumerationFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      enumerationFile.AddImport("ConcurrentHoareLogicSpecModule");
      enumerationFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      enumerationFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      enumerationFile.AddImport("util_collections_seqs_s");

      string str;

      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured).Concat(sbdsEndingNormal)) {
        str = $@"
          lemma lemma_EnumerateStraightlineBehaviorHelper_{sbd.Name}(
            cr: CHLRequest,
            sb: LAtomicStraightlineBehavior,
            tid: Armada_ThreadHandle,
            proc: LProcName
            )
            requires cr.spec == GetCHLSpec()
            requires cr.step_to_actor == PathAndTidToTid
            requires cr.step_to_proc == PathAndTidToProc
            requires cr.get_actor_pc_stack == GetThreadPCStack
            requires cr.state_ok == StateOK
            requires cr.pc_to_proc == PCToProc
            requires cr.is_entry_point == IsEntryPoint
            requires cr.is_loop_head == IsLoopHead
            requires cr.is_return_site == IsReturnSite
            requires cr.step_to_effect == PathAndTidToEffect
            requires proc.LProcName_{sbd.MethodName}?
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetStraightlineSpec(cr, tid, proc))
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
        ";
        foreach (var s in sbd.GetEnumerationClauses(extractorSB, false /* expanded */, true /* crRelative */)) {
          str += $"ensures {s}\n";
        }
        str += $@"
          {{
            var sspec := GetStraightlineSpec(cr, tid, proc);
        ";
        str += String.Concat(Enumerable.Range(0, sbd.NumSteps).Select(i => $@"
            assert ActionTuple(sb.states[{i}], sb.states[{i}+1], sb.trace[{i}]) in sspec.next;
        "));
        str += "}\n";
        pgp.AddLemma(str, "enumeration");

        str = $@"
          lemma lemma_EnumerateStraightlineBehavior_{sbd.Name}(
            sb:LAtomicStraightlineBehavior,
            tid:Armada_ThreadHandle,
            proc:LProcName
            )
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
        ";
        foreach (var s in sbd.GetEnumerationClauses(extractorSB)) {
          str += $"ensures {s}\n";
        }
        str += $@"
          {{
            assert proc.LProcName_{sbd.MethodName}?;
            lemma_EnumerateStraightlineBehaviorHelper_{sbd.Name}(GetConcurrentHoareLogicRequest(), sb, tid, proc);
          }}
        ";
        str += "}\n";
        pgp.AddLemma(str, "enumeration");
      }
    }

    private void GenerateStraightlineBehaviorsSatisfyGlobalInvariantProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("GlobalInvAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("GlobalInvAlways");

      // If the global invariant is just "true", generate a very simple lemma:

      if (!globalInvariantInfos.Any()) {
        str = @"
          lemma lemma_StraightlineBehaviorsSatisfyGlobalInvariant()
            ensures StraightlineBehaviorsSatisfyGlobalInvariant(GetConcurrentHoareLogicRequest())
          {
            var cr := GetConcurrentHoareLogicRequest();
            forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')}
              | StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')
              ensures cr.global_inv(s')
            {
            }
          }
        ";
        pgp.AddLemma(str, "GlobalInvAlways");

        return;
      }

      // Otherwise, create two files for each global invariant, one to reason about all straightline behaviors
      // and one to reason about specific straightline behaviors.

      foreach (var item in globalInvariantInfos)
      {
        var invName = item.Key;

        var invFile = pgp.proofFiles.CreateAuxiliaryProofFile($"GlobalInv_{invName}");
        invFile.IncludeAndImportGeneratedFile("specs");
        invFile.IncludeAndImportGeneratedFile("defs");
        invFile.IncludeAndImportGeneratedFile("revelations");
        invFile.IncludeAndImportGeneratedFile("invariants");
        invFile.IncludeAndImportGeneratedFile("latomic");
        alwaysFile.IncludeAndImportGeneratedFile($"GlobalInv_{invName}");
      }

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured))
      {
        foreach (var atomicPath in sbd.PotentialSuccessorPaths.Where(tup => tup.Item2.CanFollow(sbd.LastState))
                                                              .Select(tup => tup.Item1))
        {
          var beyondEnd = new StraightlineStepBeyondEnd(sbd.NumSteps, atomicPath, pcsWithLocalInvariants.Contains(sbd.LastState.PC));
          var sbdPlus = new StraightlineBehavior(sbd, beyondEnd);
          var pathExpander = new PathExpander(sbdPlus);
          var extractorExpanded = new ExtractorExpanded(pathExpander);

          var expandedParamDeclarations =
            String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }
                               .Concat(sbdPlus.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues =
            String.Join(", ", new List<string>{ "tid" }
                                .Concat(sbdPlus.GetStatesAndSteps(extractorEnumeration, false)));

          var enumeratedParamDeclarations =
            String.Join(", ", new List<string> { "tid: Armada_ThreadHandle" }
                               .Concat(sbdPlus.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues =
            String.Join(", ", new List<string>{ "tid" }
                                .Concat(sbd.GetStatesAndPaths(extractorSB, false))
                                .Concat(new List<string>{ "path", "s'" }));

          foreach (var globalInvariantInfo in globalInvariantInfos)
          {
            var invName = globalInvariantInfo.Key;
            var invPred = globalInvariantInfo.Value;
            str = $@"
              lemma lemma_ExpandedStraightlineBehaviorSatisfiesGlobalInvariant_{invName}_{sbd.Name}_Then_{atomicPath.Name}(
                {expandedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
            str += $@"
                requires InductiveInv({extractorExpanded.State(sbd.NumSteps + 1)})
                ensures  {invPred}({extractorExpanded.State(sbd.NumSteps + 1)})
              {{
                ProofCustomizationGoesHere();
              }}
            ";
            pgp.AddLemma(str, $"GlobalInv_{invName}");

            str = $@"
              lemma lemma_EnumeratedStraightlineBehaviorSatisfiesGlobalInvariant_{invName}_{sbd.Name}_Then_{atomicPath.Name}(
                {enumeratedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorEnumeration, false).Select(r => "requires " + r + "\n"));
            str += $@"
                requires InductiveInv(s{sbd.NumSteps + 1})
                ensures  {invPred}(s{sbd.NumSteps + 1})
              {{
                { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
                { extractorEnumeration.GetOpenValidPathInvocation(atomicPath, sbd.NumSteps) }
                lemma_ExpandedStraightlineBehaviorSatisfiesGlobalInvariant_{invName}_{sbd.Name}_Then_{atomicPath.Name}(
                  {expandedParamValues}
                );
              }}
            ";
            pgp.AddLemma(str, $"GlobalInv_{invName}");
          }

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesGlobalInvariant_{sbd.Name}_Then_{atomicPath.Name}(
              sb: LAtomicStraightlineBehavior,
              path: LAtomic_Path,
              tid: Armada_ThreadHandle,
              s': LPlusState
              )
              requires path.LAtomic_Path_{atomicPath.Name}?
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
              requires LocalInv(last(sb.states).state, tid)
              requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
              ensures  GlobalInv(s')
            {{
              var proc := LProcName_{sbd.MethodName};
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
              if InductiveInv(s') {{
          ";
          str += String.Concat(globalInvariantInfos.Select(info => info.Key).Select(invName => $@"
                lemma_EnumeratedStraightlineBehaviorSatisfiesGlobalInvariant_{invName}_{sbd.Name}_Then_{atomicPath.Name}(
                  {enumeratedParamValues}
                );
          "));
          str += "} }";
          pgp.AddLemma(str, "GlobalInvAlways");
        }

        var optionalNot = (sbd.LastState is StraightlineStateYielded) ? "!" : "";
        str = $@"
          lemma lemma_StraightlineBehaviorSatisfiesGlobalInvariant_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            s': LPlusState
            )
            requires !path.LAtomic_Path_Tau?
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
            requires LocalInv(last(sb.states).state, tid)
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires !PathToEffect(path).CHLStepEffectStop?
            requires var effect := PathToEffect(path);
                     {optionalNot}(effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall?)
            ensures  GlobalInv(s')
          {{
            lemma_StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(sb, tid, LProcName_{sbd.MethodName}, s', path);
            match path {{
        ";
        foreach (var tup in sbd.PotentialSuccessorPaths)
        {
          var path = tup.Item1;
          var effect = tup.Item2;
          str += $"case LAtomic_Path_{path.Name}(_) =>\n";
          if (tup.Item2.CanFollow(sbd.LastState)) {
            str += $"lemma_StraightlineBehaviorSatisfiesGlobalInvariant_{sbd.Name}_Then_{path.Name}(sb, path, tid, s');\n";
          }
          else {
            str += $"assert PathToEffect(path) == {effect.Constructor};\n assert false;\n";
          }
        }
        str += "} }\n";
        pgp.AddLemma(str, "GlobalInvAlways");
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesGlobalInvariant(
          sb: LAtomicStraightlineBehavior,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle,
          s': LPlusState
          )
          requires !path.LAtomic_Path_Tau?
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, PathToProc(path)))
          requires LocalInv(last(sb.states).state, tid)
          requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
          requires !PathToEffect(path).CHLStepEffectStop?
          requires var phase := last(sb.states).aux.phase;
                   var effect := PathToEffect(path);
                   if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
                     phase.StraightlinePhaseEnsured?
                   else
                     phase.StraightlinePhaseYielded?
          ensures  GlobalInv(s')
        {
          var proc := PathToProc(path);
          var phase := last(sb.states).aux.phase;
          if phase.StraightlinePhaseEnsured? {
            var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingEnsured(sb, tid, proc);
            assert StraightlineBehaviorDescriptorEndsEnsuredPossibilities(sbd);
            match sbd {
      ";
      str += String.Concat(sbdsEndingEnsured.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesGlobalInvariant_{sbd.Name}(sb, path, tid, s');
      "));
      str += @"
            }
          }
          else {
            var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
            assert StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
            match sbd {
      ";
      str += String.Concat(sbdsEndingYielded.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesGlobalInvariant_{sbd.Name}(sb, path, tid, s');
      "));
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str, "GlobalInvAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyGlobalInvariant()
          ensures StraightlineBehaviorsSatisfyGlobalInvariant(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')}
            | StraightlineBehaviorsSatisfyGlobalInvariantConditions(cr, sb, step, s')
            ensures cr.global_inv(s')
          {
            lemma_StraightlineBehaviorSatisfiesGlobalInvariant(sb, step.path, step.tid, s');
          }
        }
      ";
      pgp.AddLemma(str, "GlobalInvAlways");
    }

    private void GenerateStraightlineBehaviorsSatisfyLocalInvariantProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("LocalInvAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("LocalInvAlways");

      var enumeratedFile = pgp.proofFiles.CreateAuxiliaryProofFile("LocalInv");
      enumeratedFile.IncludeAndImportGeneratedFile("specs");
      enumeratedFile.IncludeAndImportGeneratedFile("defs");
      enumeratedFile.IncludeAndImportGeneratedFile("revelations");
      enumeratedFile.IncludeAndImportGeneratedFile("invariants");
      enumeratedFile.IncludeAndImportGeneratedFile("latomic");
      enumeratedFile.IncludeAndImportGeneratedFile("convert");
      enumeratedFile.IncludeAndImportGeneratedFile("utility");
      alwaysFile.IncludeAndImportGeneratedFile("LocalInv");

      var trivialUniversalStepConstraint = !pgp.symbolsHigh.UniversalStepConstraints.Any();

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");

      foreach (var sbd in sbdsEndingYielded)
      {
        // If there is no enabling condition for the PC at the end of this behavior, then
        // it's trivial to prove that the enabling condition (true) holds.

        if (trivialUniversalStepConstraint && !sbd.LastState.HasLocalInvariant(pcsWithLocalInvariants, returnPCForMethod)) {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              path: LAtomic_Path,
              tid: Armada_ThreadHandle,
              s': LPlusState,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              ensures  LocalInv(last(sb.states).state, tid)
              {{
                lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
                assert !PCHasLocalInvariant(last(sb.states).state.s.threads[tid].pc);
              }}
          ";
          pgp.AddLemma(str, "LocalInvAlways");
          continue;
        }

        foreach (var atomicPath in sbd.PotentialSuccessorPaths.Select(tup => tup.Item1))
        {
          // We pass hasLocalInvariant = false to the constructor for StraightlineStepBeyondEnd because we don't
          // get to assume that LocalInv holds just before that final step.

          var sbdPlus = new StraightlineBehavior(sbd, new StraightlineStepBeyondEnd(sbd.NumSteps, atomicPath, false));
          var pathExpander = new PathExpander(sbdPlus);
          var extractorExpanded = new ExtractorExpanded(pathExpander);

          var expandedParamDeclarations = String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }
                                                  .Concat(sbdPlus.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues = String.Join(", ", new List<string>{ "tid" }
                                                        .Concat(sbdPlus.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations = String.Join(", ", new List<string>{ "tid:Armada_ThreadHandle" }
                                                                 .Concat(sbdPlus.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues = String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndPaths(extractorSB, false))
                                                           .Concat(new List<string>{ "path", "s'" }));

          str = $@"
            lemma lemma_ExpandedStraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{atomicPath.Name}(
              {expandedParamDeclarations}
            )
          ";
          str += String.Concat(sbdPlus.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LocalInv({extractorExpanded.State(sbd.NumSteps)}, tid)
            {{
              lemma_StoreBufferAppendHasEffectOfAppendedEntryAlways_L();
              lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
              ProofCustomizationGoesHere();
            }}
          ";
          pgp.AddLemma(str, "LocalInv");

          str = $@"
            lemma lemma_EnumeratedStraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{atomicPath.Name}(
              {enumeratedParamDeclarations}
            )
          ";
          str += String.Concat(sbdPlus.GetEnumerationClauses(extractorEnumeration).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LocalInv(s{sbd.NumSteps}, tid)
            {{
              { String.Concat(sbdPlus.GetOpenValidPathInvocations(extractorEnumeration)) }
              lemma_ExpandedStraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{atomicPath.Name}({expandedParamValues});
            }}
          ";
          pgp.AddLemma(str, "LocalInv");

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{atomicPath.Name}(
              sb: LAtomicStraightlineBehavior,
              path: LAtomic_Path,
              tid: Armada_ThreadHandle,
              s': LPlusState
              )
              requires path.LAtomic_Path_{atomicPath.Name}?
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
              requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
              ensures  LocalInv(last(sb.states).state, tid)
            {{
              var proc := LProcName_{sbd.MethodName};
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
              lemma_EnumeratedStraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{atomicPath.Name}({enumeratedParamValues});
            }}
          ";
          pgp.AddLemma(str, "LocalInvAlways");
        }

        str = $@"
          lemma lemma_StraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            s': LPlusState,
            proc: LProcName
            )
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
            requires tid in last(sb.states).state.s.threads
            requires PCToProc(last(sb.states).state.s.threads[tid].pc) == proc
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires !path.LAtomic_Path_Tau?
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
            ensures  LocalInv(last(sb.states).state, tid)
          {{
            lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
            assert proc.LProcName_{sbd.MethodName}?;
            lemma_PathPossibilitiesStartingAtPC_{sbd.LastState.PC}(last(sb.states).state, s', path, tid);
            match path {{
        ";
        str += String.Concat(sbd.PotentialSuccessorPaths.Select(tup => tup.Item1).Select(path => $@"
              case LAtomic_Path_{path.Name}(_) =>
                lemma_StraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}_Then_{path.Name}(sb, path, tid, s');
        "));
        str += "} }\n";
        pgp.AddLemma(str, "LocalInvAlways");
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesLocalInvariant(
          sb: LAtomicStraightlineBehavior,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle,
          s': LPlusState,
          proc: LProcName
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          requires tid in last(sb.states).state.s.threads
          requires PCToProc(last(sb.states).state.s.threads[tid].pc) == proc
          requires last(sb.states).aux.phase.StraightlinePhaseYielded?
          requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
          requires !path.LAtomic_Path_Tau?
          ensures  LocalInv(last(sb.states).state, tid)
        {
          var phase := last(sb.states).aux.phase;
          var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
          match sbd {
      ";
      str += String.Concat(sbdsEndingYielded.Select(sbd => $@"
            case SBD_{sbd.Name} =>
              lemma_StraightlineBehaviorSatisfiesLocalInvariant_{sbd.Name}(sb, path, tid, s', proc);
      "));
      str += @"
          }
        }
      ";
      pgp.AddLemma(str, "LocalInvAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyLocalInvariant()
          ensures StraightlineBehaviorsSatisfyLocalInvariant(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, sb, step, s')}
            | StraightlineBehaviorsSatisfyLocalInvariantConditions(cr, sb, step, s')
            ensures cr.local_inv(last(sb.states).state, cr.step_to_actor(step).v)
          {
            var actor := cr.step_to_actor(step).v;
            var pc := cr.get_actor_pc_stack(last(sb.states).state, actor).v.pc;
            var proc := cr.pc_to_proc(pc);
            lemma_StraightlineBehaviorSatisfiesLocalInvariant(sb, step.path, step.tid, s', proc);
          }
        }
      ";
      pgp.AddLemma(str, "LocalInvAlways");
    }

    private void GenerateStraightlineBehaviorsSatisfyPreconditionsForCallsProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("CallsAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("CallsAlways");

      var stackCorrectFile = pgp.proofFiles.CreateAuxiliaryProofFile("StackCorrect");
      stackCorrectFile.IncludeAndImportGeneratedFile("specs");
      stackCorrectFile.IncludeAndImportGeneratedFile("defs");
      stackCorrectFile.IncludeAndImportGeneratedFile("revelations");
      stackCorrectFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("StackCorrect");

      // For each call statement, demonstrate that it establishes the StackCorrectAtStart_{methodName} predicate.

      foreach (var kv in pathEffectMap.Where(kv => kv.Value is CHLPathEffectCall || kv.Value is CHLPathEffectReturnThenCall))
      {
        var atomicPath = kv.Key;
        var callee = kv.Value.Callee;
        var pr = new PathPrinter(lAtomic);
        str = $@"
          lemma lemma_AtomicPathEnsuresStackCorrectAtStart_{atomicPath.Name}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle
            )
            requires LAtomic_NextPath(s, s', path, tid)
            requires path.LAtomic_Path_{atomicPath.Name}?
            ensures  StackCorrectAtStart_{callee}(s', tid)
          {{
            { pr.GetOpenValidPathInvocation(atomicPath) }
          }}
        ";
        pgp.AddLemma(str, "StackCorrect");
      }

      foreach (var preconditionName in preconditionsForMethod.Values.SelectMany(x => x))
      {
        var specificPreconditionFile = pgp.proofFiles.CreateAuxiliaryProofFile($"Call_{preconditionName}");
        specificPreconditionFile.IncludeAndImportGeneratedFile("specs");
        specificPreconditionFile.IncludeAndImportGeneratedFile("defs");
        specificPreconditionFile.IncludeAndImportGeneratedFile("revelations");
        specificPreconditionFile.IncludeAndImportGeneratedFile("invariants");
        specificPreconditionFile.IncludeAndImportGeneratedFile("latomic");
        alwaysFile.IncludeAndImportGeneratedFile($"Call_{preconditionName}");
      }

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured)) {
        foreach (var tup in sbd.PotentialSuccessorPaths
                 .Where(tup => (sbd.LastState is StraightlineStateYielded && tup.Item2 is CHLPathEffectCall)
                               || (sbd.LastState is StraightlineStateEnsured && tup.Item2 is CHLPathEffectReturnThenCall))) {
          var atomicPath = tup.Item1;
          var effect = tup.Item2;
          var callee = effect.Callee;
          var beyondEnd = new StraightlineStepBeyondEnd(sbd.NumSteps, atomicPath, pcsWithLocalInvariants.Contains(sbd.LastState.PC));
          var sbdPlus = new StraightlineBehavior(sbd, beyondEnd);
          var pathExpander = new PathExpander(sbdPlus);
          var extractorExpanded = new ExtractorExpanded(pathExpander);

          var expandedParamDeclarations = String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }
                                                              .Concat(sbdPlus.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues = String.Join(", ", new List<string>{ "tid" }
                                                        .Concat(sbdPlus.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations =
            String.Join(", ", new List<string>{ "tid:Armada_ThreadHandle" }
                               .Concat(sbdPlus.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues =
            String.Join(", ", new List<string>{ "tid" }
                                .Concat(sbd.GetStatesAndPaths(extractorSB, false))
                                .Concat(new List<string>{ "path", "s'" }));

          foreach (var preconditionName in preconditionsForMethod[callee])
          {
            str = $@"
              lemma lemma_ExpandedStraightlineBehaviorSatisfiesPreconditionForCall_{preconditionName}_{sbd.Name}_Then_{atomicPath.Name}(
                {expandedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
            str += $@"
                requires StackCorrectAtStart_{callee}({extractorExpanded.State(sbd.NumSteps + 1)}, tid)
                ensures  {preconditionName}({extractorExpanded.State(sbd.NumSteps + 1)}, tid)
              {{
                ProofCustomizationGoesHere();
              }}
            ";
            pgp.AddLemma(str, $"Call_{preconditionName}");

            str = $@"
              lemma lemma_EnumeratedStraightlineBehaviorSatisfiesPreconditionForCall_{preconditionName}_{sbd.Name}_Then_{atomicPath.Name}(
                {enumeratedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorEnumeration).Select(r => "requires " + r + "\n"));
            str += $@"
                requires StackCorrectAtStart_{callee}(s{sbd.NumSteps + 1}, tid)
                ensures  {preconditionName}(s{sbd.NumSteps + 1}, tid)
              {{
                { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
                { extractorEnumeration.GetOpenValidPathInvocation(atomicPath, sbd.NumSteps) }
                lemma_ExpandedStraightlineBehaviorSatisfiesPreconditionForCall_{preconditionName}_{sbd.Name}_Then_{atomicPath.Name}(
                  {expandedParamValues}
                );
              }}
            ";
            pgp.AddLemma(str, $"Call_{preconditionName}");
          }

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForCall_{sbd.Name}_Then_{atomicPath.Name}(
              sb: LAtomicStraightlineBehavior,
              path: LAtomic_Path,
              tid: Armada_ThreadHandle,
              s': LPlusState
              )
              requires path.LAtomic_Path_{atomicPath.Name}?
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
              requires LocalInv(last(sb.states).state, tid)
              requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
          ";
          if (sbd.LastState is StraightlineStateYielded) {
            str += "requires PathToEffect(path).CHLStepEffectCall?\n";
          }
          else {
            str += "requires PathToEffect(path).CHLStepEffectReturnThenCall?\n";
          }
          str += $@"
              ensures  RequiresClauses(PathToEffect(path).callee, s', tid)
            {{
              var proc := LProcName_{sbd.MethodName};
              assert PathToEffect(path).callee.LProcName_{callee}?;
              lemma_AtomicPathEnsuresStackCorrectAtStart_{atomicPath.Name}(last(sb.states).state, s', path, tid);
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
          ";
          str += String.Concat(preconditionsForMethod[callee].Select(name => $@"
              lemma_EnumeratedStraightlineBehaviorSatisfiesPreconditionForCall_{name}_{sbd.Name}_Then_{atomicPath.Name}(
                {enumeratedParamValues}
              );
          "));
          str += "}";
          pgp.AddLemma(str, "CallsAlways");
        }

        str = $@"
          lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForCall_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            s': LPlusState
            )
            requires !path.LAtomic_Path_Tau?
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
            requires LocalInv(last(sb.states).state, tid)
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
        ";
        if (sbd.LastState is StraightlineStateYielded) {
          str += "requires PathToEffect(path).CHLStepEffectCall?\n";
        }
        else {
          str += "requires PathToEffect(path).CHLStepEffectReturnThenCall?\n";
        }
        str += $@"
            ensures  RequiresClauses(PathToEffect(path).callee, s', tid)
          {{
            lemma_StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(sb, tid, LProcName_{sbd.MethodName}, s', path);
            match path {{
        ";
        foreach (var tup in sbd.PotentialSuccessorPaths)
        {
          var path = tup.Item1;
          var effect = tup.Item2;
          str += $@"
              case LAtomic_Path_{path.Name}(_) =>
          ";
          if ((sbd.LastState is StraightlineStateYielded && effect is CHLPathEffectCall) ||
              (sbd.LastState is StraightlineStateEnsured && effect is CHLPathEffectReturnThenCall)) {
            str += $"lemma_StraightlineBehaviorSatisfiesPreconditionsForCall_{sbd.Name}_Then_{path.Name}(sb, path, tid, s');\n";
          }
          else {
            str += $"assert PathToEffect(path) == {effect.Constructor};\n assert false;\n";
          }
        }
        str += "} }\n";
        pgp.AddLemma(str, "CallsAlways");
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForCall(
          sb: LAtomicStraightlineBehavior,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle,
          s': LPlusState
          )
          requires !path.LAtomic_Path_Tau?
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, PathToProc(path)))
          requires LocalInv(last(sb.states).state, tid)
          requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
          requires var phase := last(sb.states).aux.phase;
                   var effect := PathToEffect(path);
                   || (effect.CHLStepEffectCall? && phase.StraightlinePhaseYielded?)
                   || (effect.CHLStepEffectReturnThenCall? && phase.StraightlinePhaseEnsured?)
          ensures  RequiresClauses(PathToEffect(path).callee, s', tid)
        {
          var proc := PathToProc(path);
          var phase := last(sb.states).aux.phase;
          var sbd;
          if phase.StraightlinePhaseEnsured? {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingEnsured(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingEnsured.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesPreconditionsForCall_{sbd.Name}(sb, path, tid, s');
      "));
      str += @"
            }
          }
          else {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingYielded.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesPreconditionsForCall_{sbd.Name}(sb, path, tid, s');
      "));
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str, "CallsAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyPreconditionsForCalls()
          ensures StraightlineBehaviorsSatisfyPreconditionsForCalls(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, step, s' {:trigger StraightlineBehaviorsSatisfyPreconditionsForCallsConditions(cr, sb, step, s')}
            | StraightlineBehaviorsSatisfyPreconditionsForCallsConditions(cr, sb, step, s')
            ensures var actor := cr.step_to_actor(step).v;
                    var callee := cr.step_to_effect(step).callee;
                    cr.requires_clauses(callee, s', actor)
          {
            lemma_StraightlineBehaviorSatisfiesPreconditionsForCall(sb, step.path, step.tid, s');
          }
        }
      ";
      pgp.AddLemma(str, "CallsAlways");
    }

    private bool AtomicPathForks(AtomicPath path)
    {
      return path.NextRoutines.Where(r => r.nextType == NextType.CreateThread).Any();
    }

    private void GenerateStraightlineBehaviorsSatisfyPreconditionsForForksProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("ForksAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("ForksAlways");

      var forksFile = pgp.proofFiles.CreateAuxiliaryProofFile("Forks");
      forksFile.IncludeAndImportGeneratedFile("specs");
      forksFile.IncludeAndImportGeneratedFile("defs");
      forksFile.IncludeAndImportGeneratedFile("revelations");
      forksFile.IncludeAndImportGeneratedFile("latomic");
      forksFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("Forks");

      var nonforkersFile = pgp.proofFiles.CreateAuxiliaryProofFile("Nonforkers");
      nonforkersFile.IncludeAndImportGeneratedFile("specs");
      nonforkersFile.IncludeAndImportGeneratedFile("defs");
      nonforkersFile.IncludeAndImportGeneratedFile("revelations");
      nonforkersFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("Nonforkers");

      // For each non-stopping atomic path that can't fork, create a lemma saying it doesn't fork.

      var pr = new PathPrinter(lAtomic);

      foreach (var atomicPath in pathsStartingAtPC.Values.SelectMany(x => x).Where(path => !AtomicPathForks(path)))
      {
        str = $@"
          lemma lemma_AtomicPathDoesntFork_{atomicPath.Name}(
            s: LPlusState,
            s': LPlusState,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            other_tid: Armada_ThreadHandle
            )
            requires LAtomic_NextPath(s, s', path, tid)
            requires path.LAtomic_Path_{atomicPath.Name}?
            requires other_tid != tid
            requires other_tid !in s.s.threads
            ensures  other_tid !in s'.s.threads
          {{
            { pr.GetOpenValidPathInvocation(atomicPath) }
          }}
        ";
        pgp.AddLemma(str, "Nonforkers");
      }

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured))
      {
        var optionalNot = (sbd.LastState is StraightlineStateYielded) ? "!" : "";

        foreach (var atomicPath in sbd.PotentialSuccessorPaths.Where(tup => tup.Item2.CanFollow(sbd.LastState))
                                                              .Select(tup => tup.Item1))
        {
          if (AtomicPathForks(atomicPath)) {
            var beyondEnd = new StraightlineStepBeyondEnd(sbd.NumSteps, atomicPath, pcsWithLocalInvariants.Contains(sbd.LastState.PC));
            var sbdPlus = new StraightlineBehavior(sbd, beyondEnd);
            var pathExpander = new PathExpander(sbdPlus);
            var extractorExpanded = new ExtractorExpanded(pathExpander);

            var expandedParamDeclarations =
              String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle", "forked_tid: Armada_ThreadHandle", "forked_proc: LProcName" }
                                 .Concat(sbdPlus.GetStatesAndSteps(extractorExpanded, true)));
            var expandedParamValues =
              String.Join(", ", new List<string>{ "tid", "forked_tid", "forked_proc" }
                                  .Concat(sbdPlus.GetStatesAndSteps(extractorEnumeration, false)));
            var enumeratedParamDeclarations =
              String.Join(", ", new List<string> { "tid: Armada_ThreadHandle", "forked_tid: Armada_ThreadHandle", "forked_proc: LProcName" }
                                 .Concat(sbdPlus.GetStatesAndPaths(extractorEnumeration, true)));
            var enumeratedParamValues =
              String.Join(", ", new List<string>{ "tid", "forked_tid", "forked_proc" }
                                  .Concat(sbd.GetStatesAndPaths(extractorSB, false))
                                  .Concat(new List<string>{ "path", "s'" }));

            str = $@"
              lemma lemma_ExpandedStraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{atomicPath.Name}(
                {expandedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
            str += $@"
                requires forked_tid != tid
                requires forked_tid !in {extractorExpanded.State(sbd.NumSteps)}.s.threads
                requires forked_tid in {extractorExpanded.State(sbd.NumSteps + 1)}.s.threads
                requires forked_proc == PCToProc({extractorExpanded.State(sbd.NumSteps + 1)}.s.threads[forked_tid].pc)
                ensures  RequiresClauses(forked_proc, {extractorExpanded.State(sbd.NumSteps + 1)}, forked_tid)
                {{
                  ProofCustomizationGoesHere();
                }}
            ";
            pgp.AddLemma(str, "Forks");

            str = $@"
              lemma lemma_EnumeratedStraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{atomicPath.Name}(
                {enumeratedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorEnumeration, false).Select(r => "requires " + r + "\n"));
            str += $@"
                requires forked_tid != tid
                requires forked_tid !in s{sbd.NumSteps}.s.threads
                requires forked_tid in s{sbd.NumSteps + 1}.s.threads
                requires forked_proc == PCToProc(s{sbd.NumSteps + 1}.s.threads[forked_tid].pc)
                ensures  RequiresClauses(forked_proc, s{sbd.NumSteps + 1}, forked_tid)
                {{
                  { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
                  { extractorEnumeration.GetOpenValidPathInvocation(atomicPath, sbd.NumSteps) }
                  lemma_ExpandedStraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{atomicPath.Name}(
                    {expandedParamValues}
                  );
                }}
            ";
            pgp.AddLemma(str, "Forks");

            str = $@"
              lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{atomicPath.Name}(
                sb: LAtomicStraightlineBehavior,
                path: LAtomic_Path,
                tid: Armada_ThreadHandle,
                s': LPlusState,
                forked_tid: Armada_ThreadHandle,
                forked_proc: LProcName
                )
                requires path.LAtomic_Path_{atomicPath.Name}?
                requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
                requires LocalInv(last(sb.states).state, tid)
                requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
                requires forked_tid != tid
                requires forked_tid !in last(sb.states).state.s.threads
                requires forked_tid in s'.s.threads
                requires forked_proc == PCToProc(s'.s.threads[forked_tid].pc)
                requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
                requires !PathToEffect(path).CHLStepEffectStop?
                requires var effect := PathToEffect(path);
                         {optionalNot}(effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall?)
                ensures  RequiresClauses(forked_proc, s', forked_tid)
              {{
                var proc := LProcName_{sbd.MethodName};
                lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
                lemma_EnumeratedStraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{atomicPath.Name}(
                  {enumeratedParamValues}
                );
              }}
            ";
            pgp.AddLemma(str, "ForksAlways");
          }
        }

        str = $@"
          lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            s': LPlusState,
            forked_tid: Armada_ThreadHandle,
            forked_proc: LProcName
            )
            requires !path.LAtomic_Path_Tau?
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
            requires LocalInv(last(sb.states).state, tid)
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires forked_tid != tid
            requires forked_tid !in last(sb.states).state.s.threads
            requires forked_tid in s'.s.threads
            requires forked_proc == PCToProc(s'.s.threads[forked_tid].pc)
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
            requires !PathToEffect(path).CHLStepEffectStop?
            requires var effect := PathToEffect(path);
                     {optionalNot}(effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall?)
            ensures  RequiresClauses(forked_proc, s', forked_tid)
          {{
            lemma_StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(sb, tid, LProcName_{sbd.MethodName}, s', path);
            match path {{
        ";
        foreach (var tup in sbd.PotentialSuccessorPaths)
        {
          var path = tup.Item1;
          var effect = tup.Item2;
          str += $"case LAtomic_Path_{path.Name}(_) =>\n";
          if (!effect.CanFollow(sbd.LastState)) {
            str += $@"
                assert PathToEffect(path) == {effect.Constructor};
                assert false;
            ";
          }
          else if (AtomicPathForks(path)) {
            str += $@"
                lemma_StraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}_Then_{path.Name}(sb, path, tid, s', forked_tid,
                                                                                                     forked_proc);
            ";
          }
          else {
            str += $@"
                lemma_AtomicPathDoesntFork_{path.Name}(last(sb.states).state, s', path, tid, forked_tid);
                assert false;
            ";
          }
        }
        str += "} }\n";
        pgp.AddLemma(str, "ForksAlways");
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesPreconditionsForForks(
          sb: LAtomicStraightlineBehavior,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle,
          s': LPlusState,
          forked_tid: Armada_ThreadHandle,
          forked_proc: LProcName
          )
          requires !path.LAtomic_Path_Tau?
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, PathToProc(path)))
          requires LocalInv(last(sb.states).state, tid)
          requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
          requires forked_tid != tid
          requires forked_tid !in last(sb.states).state.s.threads
          requires forked_tid in s'.s.threads
          requires forked_proc == PCToProc(s'.s.threads[forked_tid].pc)
          requires !PathToEffect(path).CHLStepEffectStop?
          requires var phase := last(sb.states).aux.phase;
                   var effect := PathToEffect(path);
                   if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
                     phase.StraightlinePhaseEnsured?
                   else
                     phase.StraightlinePhaseYielded?
          ensures  RequiresClauses(forked_proc, s', forked_tid)
        {
          var proc := PathToProc(path);
          var phase := last(sb.states).aux.phase;
          var sbd;
          if phase.StraightlinePhaseEnsured? {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingEnsured(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingEnsured.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}(sb, path, tid, s', forked_tid, forked_proc);
      "));
      str += @"
            }
          }
          else {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingYielded.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesPreconditionsForForks_{sbd.Name}(sb, path, tid, s', forked_tid, forked_proc);
      "));
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str, "ForksAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyPreconditionsForForks()
          ensures StraightlineBehaviorsSatisfyPreconditionsForForks(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, step, s', forked_actor
            {:trigger StraightlineBehaviorsSatisfyPreconditionsForForksConditions(cr, sb, step, s', forked_actor)}
            | StraightlineBehaviorsSatisfyPreconditionsForForksConditions(cr, sb, step, s', forked_actor)
            ensures var forked_pc := cr.get_actor_pc_stack(s', forked_actor).v.pc;
                    var forked_proc := cr.pc_to_proc(forked_pc);
                    cr.requires_clauses(forked_proc, s', forked_actor)
          {
            var forked_pc := cr.get_actor_pc_stack(s', forked_actor).v.pc;
            var forked_proc := cr.pc_to_proc(forked_pc);
            lemma_StraightlineBehaviorSatisfiesPreconditionsForForks(sb, step.path, step.tid, s', forked_actor, forked_proc);
          }
        }
      ";
      pgp.AddLemma(str, "ForksAlways");
    }

    private bool EndsAtReturnPC(StraightlineBehavior sbd)
    {
      return returnPCForMethod[sbd.MethodName].Equals(sbd.LastState.PC);
    }

    private void GenerateStraightlineBehaviorsSatisfyPostconditionsProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("PostconditionsAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("PostconditionsAlways");

      var postconditionsFile = pgp.proofFiles.CreateAuxiliaryProofFile("Postconditions");
      postconditionsFile.IncludeAndImportGeneratedFile("specs");
      postconditionsFile.IncludeAndImportGeneratedFile("defs");
      postconditionsFile.IncludeAndImportGeneratedFile("revelations");
      postconditionsFile.IncludeAndImportGeneratedFile("invariants");
      postconditionsFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("Postconditions");

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded)
      {
        if (EndsAtReturnPC(sbd)) {
          var pathExpander = new PathExpander(sbd);
          var extractorExpanded = new ExtractorExpanded(pathExpander);
          var expandedParamDeclarations =
            String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }.Concat(sbd.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues =
            String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations =
            String.Join(", ", new List<string>{ "tid:Armada_ThreadHandle" }.Concat(sbd.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues = String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndPaths(extractorSB, false)));

          str = $@"
            lemma lemma_ExpandedStraightlineBehaviorSatisfiesPostcondition_{sbd.Name}({expandedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  Postconditions_{sbd.MethodName}({extractorExpanded.State(0)}, {extractorExpanded.State(sbd.NumSteps)}, tid)
              {{
                ProofCustomizationGoesHere();
              }}
          ";
          pgp.AddLemma(str, "Postconditions");

          str = $@"
            lemma lemma_EnumeratedStraightlineBehaviorSatisfiesPostcondition_{sbd.Name}({enumeratedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorEnumeration, false).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  Postconditions_{sbd.MethodName}(s0, s{sbd.NumSteps}, tid)
              {{
                { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
                lemma_ExpandedStraightlineBehaviorSatisfiesPostcondition_{sbd.Name}({expandedParamValues});
              }}
          ";
          pgp.AddLemma(str, "Postconditions");

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesPostcondition_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              ensures  EnsuresClauses(proc, sb.states[0].state, last(sb.states).state, tid)
            {{
              assert proc.LProcName_{sbd.MethodName}?;
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
              lemma_EnumeratedStraightlineBehaviorSatisfiesPostcondition_{sbd.Name}({enumeratedParamValues});
            }}
          ";
          pgp.AddLemma(str, "PostconditionsAlways");
        }
        else {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesPostcondition_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var s := last(sb.states).state; tid in s.s.threads && IsReturnSite(s.s.threads[tid].pc)
              ensures  false
            {{
              var pc := last(sb.states).state.s.threads[tid].pc;
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              assert !IsReturnSite(pc);
            }}
          ";
          pgp.AddLemma(str, "PostconditionsAlways");
        }
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesPostcondition(
          sb: LAtomicStraightlineBehavior,
          tid: Armada_ThreadHandle,
          proc: LProcName
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          requires var phase := last(sb.states).aux.phase; phase.StraightlinePhaseYielded?
          requires var s := last(sb.states).state; tid in s.s.threads && IsReturnSite(s.s.threads[tid].pc)
          ensures  EnsuresClauses(proc, sb.states[0].state, last(sb.states).state, tid)
        {
          var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
          assert StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
          match sbd {
      ";
      foreach (var sbd in straightlineBehaviorDescriptors) {
        str += $"case SBD_{sbd.Name} =>\n";
        if (sbd.LastState is StraightlineStateYielded) {
          str += $"lemma_StraightlineBehaviorSatisfiesPostcondition_{sbd.Name}(sb, tid, proc);\n";
        }
        else {
          str += $@"
            assert !StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
            assert false;
          ";
        }
      }
      str += "} }\n";
      pgp.AddLemma(str, "PostconditionsAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyPostconditions()
          ensures StraightlineBehaviorsSatisfyPostconditions(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyPostconditionsConditions(cr, sb, actor, proc)}
            | StraightlineBehaviorsSatisfyPostconditionsConditions(cr, sb, actor, proc)
            ensures cr.ensures_clauses(proc, sb.states[0].state, last(sb.states).state, actor)
          {
            lemma_StraightlineBehaviorSatisfiesPostcondition(sb, actor, proc);
          }
        }
      ";
      pgp.AddLemma(str, "PostconditionsAlways");
    }

    private bool EndsAtVisitedLoopHead(StraightlineBehavior sbd)
    {
      var pc = sbd.LastState.PC;
      return loopHeads.Contains(pc) && sbd.LastState.IsLoopHeadVisited(pc);
    }

    private bool EndsAtUnvisitedLoopHead(StraightlineBehavior sbd)
    {
      var pc = sbd.LastState.PC;
      return loopHeads.Contains(pc) && !sbd.LastState.IsLoopHeadVisited(pc);
    }

    private void GenerateStraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("LoopEntryAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("LoopEntryAlways");

      var loopEntryFile = pgp.proofFiles.CreateAuxiliaryProofFile("LoopEntry");
      loopEntryFile.IncludeAndImportGeneratedFile("specs");
      loopEntryFile.IncludeAndImportGeneratedFile("defs");
      loopEntryFile.IncludeAndImportGeneratedFile("revelations");
      loopEntryFile.IncludeAndImportGeneratedFile("invariants");
      loopEntryFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("LoopEntry");

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded)
      {
        if (EndsAtUnvisitedLoopHead(sbd)) {
          var pathExpander = new PathExpander(sbd);
          var extractorExpanded = new ExtractorExpanded(pathExpander);
          var expandedParamDeclarations =
            String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }.Concat(sbd.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues =
            String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations =
            String.Join(", ", new List<string>{ "tid:Armada_ThreadHandle" }.Concat(sbd.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues = String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndPaths(extractorSB, false)));

          str = $@"
            lemma lemma_ExpandedStraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}({expandedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LoopModifies_{sbd.LastState.PC}({extractorExpanded.State(sbd.NumSteps)},
                                                       {extractorExpanded.State(sbd.NumSteps)}, tid)
            {{
              ProofCustomizationGoesHere();
            }}
          ";
          pgp.AddLemma(str, "LoopEntry");

          str = $@"
            lemma lemma_EnumeratedStraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}({enumeratedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorEnumeration).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LoopModifies_{sbd.LastState.PC}(s{sbd.NumSteps}, s{sbd.NumSteps}, tid)
            {{
              { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
              lemma_ExpandedStraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}({expandedParamValues});
            }}
          ";
          pgp.AddLemma(str, "LoopEntry");

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires tid in last(sb.states).state.s.threads
              ensures  var s := last(sb.states).state; LoopModifiesClauses(s.s.threads[tid].pc, s, s, tid)
            {{
              var s := last(sb.states).state;
              var pc := s.s.threads[tid].pc;
              assert proc.LProcName_{sbd.MethodName}?;
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
              lemma_EnumeratedStraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}({enumeratedParamValues});
              assert LoopModifies_{sbd.LastState.PC}(s, s, tid);
              forall ensures pc.{sbd.LastState.PC}? {{
                lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              }}
              assert LoopModifiesClauses(pc, s, s, tid);
            }}
          ";
          pgp.AddLemma(str, "LoopEntryAlways");
        }
        else if (EndsAtVisitedLoopHead(sbd)) {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var StraightlineState(s, aux) := last(sb.states);
                       tid in s.s.threads && s.s.threads[tid].pc !in aux.visited_loops
              ensures  false
            {{
              var StraightlineState(s, aux) := last(sb.states);
              var pc := s.s.threads[tid].pc;
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              assert pc in aux.visited_loops;
            }}
          ";
          pgp.AddLemma(str, "LoopEntryAlways");
        }
        else {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var s :=  last(sb.states).state;
                       tid in s.s.threads && IsLoopHead(s.s.threads[tid].pc)
              ensures  false
            {{
              var StraightlineState(s, aux) := last(sb.states);
              var pc := s.s.threads[tid].pc;
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              assert !IsLoopHead(pc);
            }}
          ";
          pgp.AddLemma(str, "LoopEntryAlways");
        }
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry(
          sb: LAtomicStraightlineBehavior,
          tid: Armada_ThreadHandle,
          proc: LProcName
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          requires var StraightlineState(s, aux) := last(sb.states);
                   && aux.phase.StraightlinePhaseYielded?
                   && tid in s.s.threads
                   && IsLoopHead(s.s.threads[tid].pc)
                   && s.s.threads[tid].pc !in aux.visited_loops
          ensures  var s := last(sb.states).state; LoopModifiesClauses(s.s.threads[tid].pc, s, s, tid)
        {
          var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
          assert StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
          var StraightlineState(s, aux) := last(sb.states);
          var pc := s.s.threads[tid].pc;
          match sbd {
      ";
      foreach (var sbd in straightlineBehaviorDescriptors) {
        str += $"case SBD_{sbd.Name} =>\n";
        if (sbd.LastState is StraightlineStateYielded) {
          str += $"lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry_{sbd.Name}(sb, tid, proc);\n";
        }
        else {
          str += $@"
            assert !StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
            assert false;
          ";
        }
      }
      str += "} }\n";
      pgp.AddLemma(str, "LoopEntryAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntry()
          ensures StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntry(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions(cr, sb, actor, proc)}
            | StraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryConditions(cr, sb, actor, proc)
            ensures var s := last(sb.states).state;
                    var pc := cr.get_actor_pc_stack(s, actor).v.pc;
                    cr.loop_modifies_clauses(pc, s, s, actor)
          {
            assert cr.get_actor_pc_stack(last(sb.states).state, actor).Some?;
            lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnEntry(sb, actor, proc);
          }
        }
      ";
      pgp.AddLemma(str, "LoopEntryAlways");
    }

    private bool RevisitsLoopHead(Tuple<AtomicPath, CHLPathEffect> tup, StraightlineBehavior sbd)
    {
      var atomicPath = tup.Item1;
      var effect = tup.Item2;
      return (   (sbd.LastState is StraightlineStateYielded && effect is CHLPathEffectNormal)
              || (sbd.LastState is StraightlineStateEnsured && effect is CHLPathEffectReturn))
             && atomicPath.EndPC != null
             && sbd.LastState.IsLoopHeadVisited(atomicPath.EndPC);
    }

    private void GenerateStraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("LoopBackAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/chl/AtomicConcurrentHoareLogicSpec.i.dfy");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("LoopBackAlways");

      var loopJumpBackFile = pgp.proofFiles.CreateAuxiliaryProofFile("LoopBack");
      loopJumpBackFile.IncludeAndImportGeneratedFile("specs");
      loopJumpBackFile.IncludeAndImportGeneratedFile("defs");
      loopJumpBackFile.IncludeAndImportGeneratedFile("revelations");
      loopJumpBackFile.IncludeAndImportGeneratedFile("latomic");
      loopJumpBackFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("LoopBack");

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded)
      {
        if (EndsAtVisitedLoopHead(sbd)) {
          var pos = sbd.LastState.VisitedLoopHeads[sbd.LastState.PC];
          var pathExpander = new PathExpander(sbd);
          var extractorExpanded = new ExtractorExpanded(pathExpander);
          var expandedParamDeclarations =
            String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle" }.Concat(sbd.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues =
            String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations =
            String.Join(", ", new List<string>{ "tid:Armada_ThreadHandle" }.Concat(sbd.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues = String.Join(", ", new List<string>{ "tid" }.Concat(sbd.GetStatesAndPaths(extractorSB, false)));

          str = $@"
            lemma lemma_ExpandedStraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}({expandedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LoopModifies_{sbd.LastState.PC}({extractorExpanded.State(pos)}, {extractorExpanded.State(sbd.NumSteps)}, tid)
              ensures  {extractorExpanded.State(pos)}.config == {extractorExpanded.State(sbd.NumSteps)}.config
            {{
              ProofCustomizationGoesHere();
            }}
          ";
          pgp.AddLemma(str, "LoopBack");

          str = $@"
            lemma lemma_EnumeratedStraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}({enumeratedParamDeclarations})
          ";
          str += String.Concat(sbd.GetEnumerationClauses(extractorEnumeration).Select(r => "requires " + r + "\n"));
          str += $@"
              ensures  LoopModifies_{sbd.LastState.PC}(s{pos}, s{sbd.NumSteps}, tid)
              ensures  s{pos}.config == s{sbd.NumSteps}.config
            {{
              { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
              lemma_ExpandedStraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}({expandedParamValues});
            }}
          ";
          pgp.AddLemma(str, "LoopBack");

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var StraightlineState(s, aux) := last(sb.states);
                       tid in s.s.threads && s.s.threads[tid].pc in aux.visited_loops
              ensures  var StraightlineState(s, aux) := last(sb.states);
                       var pc := s.s.threads[tid].pc;
                       LoopModifiesClauses(pc, aux.visited_loops[pc], s, tid)
            {{
              var StraightlineState(s, aux) := last(sb.states);
              var pc := s.s.threads[tid].pc;
              assert proc.LProcName_{sbd.MethodName}?;
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
              lemma_EnumeratedStraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}({enumeratedParamValues});
              assert LoopModifies_{sbd.LastState.PC}(sb.states[{pos}].state, last(sb.states).state, tid);
              assert sb.states[{pos}].state.config == last(sb.states).state.config;
              forall
                ensures pc.{sbd.LastState.PC}?
                ensures aux.visited_loops[pc] == sb.states[{pos}].state
              {{
                lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              }}
              assert LoopModifiesClauses(pc, aux.visited_loops[pc], s, tid);
            }}
          ";
          pgp.AddLemma(str, "LoopBackAlways");
        }
        else if (EndsAtUnvisitedLoopHead(sbd)) {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var StraightlineState(s, aux) := last(sb.states);
                       tid in s.s.threads && s.s.threads[tid].pc in aux.visited_loops
              ensures  false
            {{
              var StraightlineState(s, aux) := last(sb.states);
              var pc := s.s.threads[tid].pc;
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              assert pc !in aux.visited_loops;
            }}
          ";
          pgp.AddLemma(str, "LoopBackAlways");
        }
        else {
          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}(
              sb: LAtomicStraightlineBehavior,
              tid: Armada_ThreadHandle,
              proc: LProcName
              )
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, proc, SBD_{sbd.Name})
              requires var s := last(sb.states).state;
                       tid in s.s.threads && IsLoopHead(s.s.threads[tid].pc)
              ensures  false
            {{
              var StraightlineState(s, aux) := last(sb.states);
              var pc := s.s.threads[tid].pc;
              lemma_StraightlineBehaviorEndProperties_{sbd.Name}(sb, tid, proc);
              assert !IsLoopHead(pc);
            }}
          ";
          pgp.AddLemma(str, "LoopBackAlways");
        }
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack(
          sb: LAtomicStraightlineBehavior,
          tid: Armada_ThreadHandle,
          proc: LProcName
          )
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, proc))
          requires var StraightlineState(s, aux) := last(sb.states);
                   && aux.phase.StraightlinePhaseYielded?
                   && tid in s.s.threads
                   && IsLoopHead(s.s.threads[tid].pc)
                   && s.s.threads[tid].pc in aux.visited_loops
          ensures  var StraightlineState(s, aux) := last(sb.states);
                   var pc := s.s.threads[tid].pc;
                   LoopModifiesClauses(pc, aux.visited_loops[pc], s, tid)
        {
          var sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
          assert StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
          var StraightlineState(s, aux) := last(sb.states);
          var pc := s.s.threads[tid].pc;
          match sbd {
      ";
      foreach (var sbd in straightlineBehaviorDescriptors) {
        str += $"case SBD_{sbd.Name} =>\n";
        if (sbd.LastState is StraightlineStateYielded) {
          str += $"lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack_{sbd.Name}(sb, tid, proc);\n";
        }
        else {
          str += $@"
            assert !StraightlineBehaviorDescriptorEndsYieldedPossibilities(sbd);
            assert false;
          ";
        }
      }
      str += "} }\n";
      pgp.AddLemma(str, "LoopBackAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBack()
          ensures StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBack(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, actor, proc {:trigger StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions(cr, sb, actor, proc)}
            | StraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackConditions(cr, sb, actor, proc)
            ensures var StraightlineState(s, aux) := last(sb.states);
                    var pc := cr.get_actor_pc_stack(s, actor).v.pc;
                    cr.loop_modifies_clauses(pc, aux.visited_loops[pc], s, actor)
          {
            lemma_StraightlineBehaviorSatisfiesLoopModifiesClausesOnJumpBack(sb, actor, proc);
          }
        }
      ";
      pgp.AddLemma(str, "LoopBackAlways");
    }

    private void GenerateStraightlineBehaviorsSatisfyYieldPredicatesProof()
    {
      string str;

      var alwaysFile = pgp.proofFiles.CreateAuxiliaryProofFile("YieldAlways");
      alwaysFile.IncludeAndImportGeneratedFile("specs");
      alwaysFile.IncludeAndImportGeneratedFile("invariants");
      alwaysFile.IncludeAndImportGeneratedFile("defs");
      alwaysFile.IncludeAndImportGeneratedFile("latomic");
      alwaysFile.IncludeAndImportGeneratedFile("others");
      alwaysFile.IncludeAndImportGeneratedFile("sbd");
      alwaysFile.IncludeAndImportGeneratedFile("pcstack");
      alwaysFile.IncludeAndImportGeneratedFile("exhaustive");
      alwaysFile.IncludeAndImportGeneratedFile("continuation");
      alwaysFile.IncludeAndImportGeneratedFile("enumeration");
      alwaysFile.AddImport("ConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("AtomicConcurrentHoareLogicSpecModule");
      alwaysFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("YieldAlways");

      // If the yield predicate is just "true", generate a very simple lemma:

      if (!yieldPredicateInfos.Any()) {
        str = @"
          lemma lemma_StraightlineBehaviorsSatisfyYieldPredicate()
            ensures StraightlineBehaviorsSatisfyYieldPredicate(GetConcurrentHoareLogicRequest())
          {
            var cr := GetConcurrentHoareLogicRequest();
            forall sb, step, s', other_actor {:trigger StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)}
              | StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)
              ensures cr.yield_pred(last(sb.states).state, s', other_actor)
            {
              var asf := LAtomic_GetSpecFunctions();
              var s := last(sb.states).state;
              var s' := asf.path_next(s, step.path, step.tid);
              lemma_LAtomic_AtomicPathCantAffectOtherThreadsExceptViaFork(asf, s, step.path, step.tid);
              lemma_PathLeavesConfigUnchanged(s, s', step.path, step.tid);
              assert ActionTuple(s, s', PathAndTid(step.path, step.tid)) in cr.spec.next;
              lemma_CHLStepEffectsCorrect();
              assert YieldPredicateBasic(s, s', other_actor);
            }
          }
        ";
        pgp.AddLemma(str, "YieldAlways");

        return;
      }

      // Otherwise, create a file for each yield predicate conjunct

      foreach (var item in yieldPredicateInfos)
      {
        var predName = item.Key;
        var specificPredFile = pgp.proofFiles.CreateAuxiliaryProofFile($"Yield_{predName}");
        specificPredFile.IncludeAndImportGeneratedFile("specs");
        specificPredFile.IncludeAndImportGeneratedFile("defs");
        specificPredFile.IncludeAndImportGeneratedFile("revelations");
        specificPredFile.IncludeAndImportGeneratedFile("invariants");
        specificPredFile.IncludeAndImportGeneratedFile("latomic");
        alwaysFile.IncludeAndImportGeneratedFile($"Yield_{predName}");
      }

      var extractorEnumeration = new ExtractorEnumeration(lAtomic);
      var extractorSB = new ExtractorSB("sb", "tid", "proc");
      foreach (var sbd in sbdsEndingYielded.Concat(sbdsEndingEnsured))
      {
        foreach (var atomicPath in sbd.PotentialSuccessorPaths.Where(tup => tup.Item2.CanFollow(sbd.LastState)).Select(tup => tup.Item1))
        {
          var beyondEnd = new StraightlineStepBeyondEnd(sbd.NumSteps, atomicPath, pcsWithLocalInvariants.Contains(sbd.LastState.PC));
          var sbdPlus = new StraightlineBehavior(sbd, beyondEnd);
          var pathExpander = new PathExpander(sbdPlus);
          var extractorExpanded = new ExtractorExpanded(pathExpander);

          var expandedParamDeclarations =
            String.Join(", ", new List<string>{ "tid: Armada_ThreadHandle", "other_tid: Armada_ThreadHandle" }
                               .Concat(sbdPlus.GetStatesAndSteps(extractorExpanded, true)));
          var expandedParamValues =
            String.Join(", ", new List<string>{ "tid", "other_tid" }
                                .Concat(sbdPlus.GetStatesAndSteps(extractorEnumeration, false)));
          var enumeratedParamDeclarations =
            String.Join(", ", new List<string> { "tid: Armada_ThreadHandle", "other_tid: Armada_ThreadHandle" }
                               .Concat(sbdPlus.GetStatesAndPaths(extractorEnumeration, true)));
          var enumeratedParamValues =
            String.Join(", ", new List<string>{ "tid", "other_tid" }
                                .Concat(sbd.GetStatesAndPaths(extractorSB, false))
                                .Concat(new List<string>{ "path", "s'" }));

          foreach (var yieldPredicateInfo in yieldPredicateInfos)
          {
            var predName = yieldPredicateInfo.Key;
            var predFun = yieldPredicateInfo.Value;

            str = $@"
              lemma lemma_ExpandedStraightlineBehaviorSatisfiesYieldPredicate_{predName}_{sbd.Name}_Then_{atomicPath.Name}(
                {expandedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorExpanded, true).Select(r => "requires " + r + "\n"));
            str += $@"
                requires tid != other_tid
                requires other_tid in {extractorExpanded.State(sbd.NumSteps)}.s.threads
                ensures  {predFun}({extractorExpanded.State(sbd.NumSteps)}, {extractorExpanded.State(sbd.NumSteps + 1)}, other_tid)
              {{
                ProofCustomizationGoesHere();
              }}
            ";
            pgp.AddLemma(str, $"Yield_{predName}");

            str = $@"
              lemma lemma_EnumeratedStraightlineBehaviorSatisfiesYieldPredicate_{predName}_{sbd.Name}_Then_{atomicPath.Name}(
                {enumeratedParamDeclarations}
              )
            ";
            str += String.Concat(sbdPlus.GetEnumerationClauses(extractorEnumeration).Select(r => "requires " + r + "\n"));
            str += $@"
                requires tid != other_tid
                requires other_tid in s{sbd.NumSteps}.s.threads
                ensures  {predFun}(s{sbd.NumSteps}, s{sbd.NumSteps + 1}, other_tid)
              {{
                { String.Concat(sbd.GetOpenValidPathInvocations(extractorEnumeration)) }
                { extractorEnumeration.GetOpenValidPathInvocation(atomicPath, sbd.NumSteps) }
                lemma_ExpandedStraightlineBehaviorSatisfiesYieldPredicate_{predName}_{sbd.Name}_Then_{atomicPath.Name}(
                  {expandedParamValues}
                );
              }}
            ";
            pgp.AddLemma(str, $"Yield_{predName}");
          }

          str = $@"
            lemma lemma_StraightlineBehaviorSatisfiesYieldPredicate_{sbd.Name}_Then_{atomicPath.Name}(
              sb: LAtomicStraightlineBehavior,
              path: LAtomic_Path,
              tid: Armada_ThreadHandle,
              s': LPlusState,
              other_tid: Armada_ThreadHandle
              )
              requires path.LAtomic_Path_{atomicPath.Name}?
              requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
              requires LocalInv(last(sb.states).state, tid)
              requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
              requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
              requires tid != other_tid
              requires other_tid in last(sb.states).state.s.threads
              ensures  YieldPredicate(last(sb.states).state, s', other_tid)
            {{
              var proc := LProcName_{sbd.MethodName};
              var asf := LAtomic_GetSpecFunctions();
              var s := last(sb.states).state;
              lemma_LAtomic_AtomicPathCantAffectOtherThreadsExceptViaFork(asf, s, path, tid);
              lemma_PathLeavesConfigUnchanged(s, s', path, tid);
              lemma_LAtomic_PathHasPCStackEffect_{atomicPath.Name}(s, s', path, tid);
              assert YieldPredicateBasic(s, s', other_tid);
              lemma_EnumerateStraightlineBehavior_{sbd.Name}(sb, tid, proc);
          ";
          str += String.Concat(yieldPredicateInfos.Select(kv => kv.Key).Select(predName => $@"
              lemma_EnumeratedStraightlineBehaviorSatisfiesYieldPredicate_{predName}_{sbd.Name}_Then_{atomicPath.Name}({enumeratedParamValues});
          "));
          str += "}";
          pgp.AddLemma(str, "YieldAlways");
        }

        var optionalNot = (sbd.LastState is StraightlineStateYielded) ? "!" : "";
        str = $@"
          lemma lemma_StraightlineBehaviorSatisfiesYieldPredicate_{sbd.Name}(
            sb: LAtomicStraightlineBehavior,
            path: LAtomic_Path,
            tid: Armada_ThreadHandle,
            s': LPlusState,
            other_tid: Armada_ThreadHandle
            )
            requires !path.LAtomic_Path_Tau?
            requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, LProcName_{sbd.MethodName}))
            requires LocalInv(last(sb.states).state, tid)
            requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
            requires StraightlineBehaviorFullySatisfiesDescriptor(sb.trace, LProcName_{sbd.MethodName}, SBD_{sbd.Name})
            requires !PathToEffect(path).CHLStepEffectStop?
            requires var effect := PathToEffect(path);
                     {optionalNot}(effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall?)
            requires tid != other_tid
            requires other_tid in last(sb.states).state.s.threads
            ensures  YieldPredicate(last(sb.states).state, s', other_tid)
          {{
            lemma_StraightlineBehaviorNonstoppingContinuationPossibilities_{sbd.Name}(sb, tid, LProcName_{sbd.MethodName}, s', path);
            match path {{
        ";
        foreach (var tup in sbd.PotentialSuccessorPaths)
        {
          var path = tup.Item1;
          var effect = tup.Item2;
          str += $"case LAtomic_Path_{path.Name}(_) =>\n";
          if (effect.CanFollow(sbd.LastState)) {
            str += $"lemma_StraightlineBehaviorSatisfiesYieldPredicate_{sbd.Name}_Then_{path.Name}(sb, path, tid, s', other_tid);\n";
          }
          else {
            str += $@"
                assert PathToEffect(path) == {effect.Constructor};
                assert false;
            ";
          }
        }
        str += "} }\n";
        pgp.AddLemma(str, "YieldAlways");
      }

      str = @"
        lemma lemma_StraightlineBehaviorSatisfiesYieldPredicate(
          sb: LAtomicStraightlineBehavior,
          path: LAtomic_Path,
          tid: Armada_ThreadHandle,
          s': LPlusState,
          other_tid: Armada_ThreadHandle
          )
          requires !path.LAtomic_Path_Tau?
          requires AnnotatedBehaviorSatisfiesSpec(sb, GetLAtomicStraightlineSpec(tid, PathToProc(path)))
          requires LocalInv(last(sb.states).state, tid)
          requires LAtomic_NextPath(last(sb.states).state, s', path, tid)
          requires !PathToEffect(path).CHLStepEffectStop?
          requires var phase := last(sb.states).aux.phase;
                   var effect := PathToEffect(path);
                   if effect.CHLStepEffectReturn? || effect.CHLStepEffectReturnThenCall? then
                     phase.StraightlinePhaseEnsured?
                   else
                     phase.StraightlinePhaseYielded?
          requires tid != other_tid
          requires other_tid in last(sb.states).state.s.threads
          ensures  YieldPredicate(last(sb.states).state, s', other_tid)
        {
          var proc := PathToProc(path);
          var phase := last(sb.states).aux.phase;
          var sbd;
          if phase.StraightlinePhaseEnsured? {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingEnsured(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingEnsured.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesYieldPredicate_{sbd.Name}(sb, path, tid, s', other_tid);
      "));
      str += @"
            }
          }
          else {
            sbd := lemma_GetFullDescriptorForStraightlineBehaviorEndingYielded(sb, tid, proc);
            match sbd {
      ";
      str += String.Concat(sbdsEndingYielded.Select(sbd => $@"
              case SBD_{sbd.Name} =>
                lemma_StraightlineBehaviorSatisfiesYieldPredicate_{sbd.Name}(sb, path, tid, s', other_tid);
      "));
      str += @"
            }
          }
        }
      ";
      pgp.AddLemma(str, "YieldAlways");

      str = @"
        lemma lemma_StraightlineBehaviorsSatisfyYieldPredicate()
          ensures StraightlineBehaviorsSatisfyYieldPredicate(GetConcurrentHoareLogicRequest())
        {
          var cr := GetConcurrentHoareLogicRequest();
          forall sb, step, s', other_actor {:trigger StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)}
            | StraightlineBehaviorsSatisfyYieldPredicateConditions(cr, sb, step, s', other_actor)
            ensures cr.yield_pred(last(sb.states).state, s', other_actor)
          {
            lemma_StraightlineBehaviorSatisfiesYieldPredicate(sb, step.path, step.tid, s', other_actor);
          }
        }
      ";
      pgp.AddLemma(str, "YieldAlways");
    }

    private void GenerateStraightlineBehaviorProofs()
    {
      GenerateStraightlineBehaviorsSatisfyGlobalInvariantProof();
      GenerateStraightlineBehaviorsSatisfyLocalInvariantProof();
      GenerateStraightlineBehaviorsSatisfyPreconditionsForCallsProof();
      GenerateStraightlineBehaviorsSatisfyPreconditionsForForksProof();
      GenerateStraightlineBehaviorsSatisfyPostconditionsProof();
      GenerateStraightlineBehaviorsSatisfyLoopModifiesClausesOnEntryProof();
      GenerateStraightlineBehaviorsSatisfyLoopModifiesClausesOnJumpBackProof();
      GenerateStraightlineBehaviorsSatisfyYieldPredicatesProof();
    }

    private void GenerateLInitImpliesHInitLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      var str = @"
        lemma lemma_LInitImpliesHInit()
          ensures LInitImpliesHInit(GetAtomicConcurrentHoareLogicRequest())
        {
          var ar := GetAtomicConcurrentHoareLogicRequest();
          forall ls | ar.l.init(ls)
            ensures ar.h.init(ar.lstate_to_hstate(ls))
          {
            var hs := ConvertTotalState_LPlusH(ls);
            var hconfig := ConvertConfig_LH(ls.config);

            lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
            assert H.Armada_InitConfig(hs, hconfig);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLNextPlusLocalInvariantImpliesHNextLemmaForNormalPath(AtomicPath atomicPath)
    {
      var hAtomicPath = pathMap[atomicPath];
      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      string str = $@"
        lemma lemma_LNextPlusLocalInvariantImpliesHNext_{atomicPath.Name}(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires lpath.LAtomic_Path_{atomicPath.Name}?
          requires InductiveInv(ls)
          requires LocalInv(ls, tid)
          requires GlobalInv(ls)
          ensures  HAtomic_NextPath(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertAtomicPath_LH(lpath), tid)
        {{
          { lpr.GetOpenValidPathInvocation(atomicPath) }

          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := ConvertTotalState_LPlusH(ls');
          var hpath := ConvertAtomicPath_LH(lpath);

          { hpr.GetOpenPathInvocation(hAtomicPath) }

          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          ProofCustomizationGoesHere();
      ";
      for (var i = 0; i < atomicPath.NumNextRoutines; ++i) {
        var nextRoutine = atomicPath.NextRoutines[i];
        var pos = i+1;
        str += $"var hs{pos} := ConvertTotalState_LPlusH(lstates.s{pos});\n";
        if (nextRoutine.Stopping) {
          str += $@"
            assert !hs{pos}.stop_reason.Armada_NotStopped?;
            assert !hstates.s{pos}.stop_reason.Armada_NotStopped?;
          ";
        }
        else {
          str += $@"
            assert hs{pos}.stop_reason.Armada_NotStopped?;
            assert hstates.s{pos}.stop_reason.Armada_NotStopped?;
          ";
          if (nextRoutine.nextType == NextType.TerminateThread) {
            str += $@"
              assert tid !in hs{pos}.threads;
              assert tid !in hstates.s{pos}.threads;
            ";
          }
          else {
            str += $@"
              assert hs{pos}.threads[tid] == hstates.s{pos}.threads[tid];
            ";
          }

          str += $@"
            assert hs{pos}.threads == hstates.s{pos}.threads;
            assert hs{pos}.mem == hstates.s{pos}.mem;
            assert hs{pos} == hstates.s{pos};
          ";
        }
      }
      str += $@"
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateLNextPlusLocalInvariantImpliesHNextLemmaForTauPath(AtomicPath atomicPath)
    {
      GenerateLiftAtomicPathLemmaForTauPath(atomicPath);

      // This is just like lemma_LiftAtomicPath_Tau in AbstractProofGenerator, except it also gets
      // to assume GlobalInv(ls) in the preconditions.  (It also has a slightly different calling
      // convention:  it receives ls' as well.)

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);
      var hAtomicPath = pathMap[atomicPath];

      string str = $@"
        lemma lemma_LNextPlusLocalInvariantImpliesHNext_Tau(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires lpath.LAtomic_Path_Tau?
          requires InductiveInv(ls)
          requires GlobalInv(ls)
          ensures  HAtomic_NextPath(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertAtomicPath_LH(lpath), tid)
        {{
          { lpr.GetOpenValidPathInvocation(atomicPath) }

          var hs := ConvertTotalState_LPlusH(ls);
          var hpath := ConvertAtomicPath_LH(lpath);
          var hs' := ConvertTotalState_LPlusH(ls');

          { hpr.GetOpenPathInvocation(hAtomicPath) }

          var lentry := ls.s.threads[tid].storeBuffer[0];
          var hentry := hs.threads[tid].storeBuffer[0];
          var lmem := ls.s.mem;
          var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
          var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
          lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

          var alt_hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
          ProofCustomizationGoesHere();
          assert hs'.threads[tid] == alt_hs'.threads[tid];
          assert hs'.threads == alt_hs'.threads;
          assert hs' == alt_hs';

          /* { hpr.GetAssertValidPathInvocation(hAtomicPath) } */
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateLNextPlusLocalInvariantImpliesHNextLemma()
    {
      var finalCases = "";
      foreach (var atomicPath in lAtomic.AtomicPaths) {
        if (atomicPath.Tau) {
          GenerateLNextPlusLocalInvariantImpliesHNextLemmaForTauPath(atomicPath);
        }
        else {
          GenerateLNextPlusLocalInvariantImpliesHNextLemmaForNormalPath(atomicPath);
        }

        finalCases += $@"
          case LAtomic_Path_{atomicPath.Name}(_) =>
            lemma_LNextPlusLocalInvariantImpliesHNext_{atomicPath.Name}(ls, ls', lpath, tid);
        ";
      }

      string str = $@"
        lemma lemma_LNextPlusLocalInvariantImpliesHNext(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle
          )
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires InductiveInv(ls)
          requires !lpath.LAtomic_Path_Tau? ==> LocalInv(ls, tid)
          requires GlobalInv(ls)
          ensures  HAtomic_NextPath(ConvertTotalState_LPlusH(ls), ConvertTotalState_LPlusH(ls'), ConvertAtomicPath_LH(lpath), tid)
        {{
          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateIsValidAtomicConcurrentHoareLogicRequestLemmas()
    {
      string str;

      GenerateIsValidConcurrentHoareLogicRequest();

      str = @"
        lemma lemma_LPathImpliesHPath()
          ensures LPathImpliesHPath(GetAtomicConcurrentHoareLogicRequest())
        {
          var ar := GetAtomicConcurrentHoareLogicRequest();
          forall ls, lpath, tid | LPathImpliesHPathConditions(ar, ls, lpath, tid)
            ensures var ls' := ar.l.path_next(ls, lpath, tid);
                    var hs := ar.lstate_to_hstate(ls);
                    var hpath := ar.lpath_to_hpath(lpath);
                    var hs' := ar.lstate_to_hstate(ls');
                    && ar.h.path_valid(hs, hpath, tid)
                    && hs' == ar.h.path_next(hs, hpath, tid)
          {
            var ls' := ar.l.path_next(ls, lpath, tid);
            lemma_LNextPlusLocalInvariantImpliesHNext(ls, ls', lpath, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_EmbeddedRequestCorresponds()
          ensures EmbeddedRequestCorresponds(GetAtomicConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_AtomicInitImpliesOK()
          ensures AtomicInitImpliesOK(LAtomic_GetSpecFunctions())
        {{
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AtomicPathRequiresOK()
          ensures AtomicPathRequiresOK(LAtomic_GetSpecFunctions())
        {
          var asf := LAtomic_GetSpecFunctions();
          forall s, path, tid | asf.path_valid(s, path, tid)
            ensures asf.state_ok(s)
          {
            lemma_PathImpliesThreadRunning(s, path, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AtomicSteppingThreadHasPC()
          ensures AtomicSteppingThreadHasPC(LAtomic_GetSpecFunctions())
        {
          var asf := LAtomic_GetSpecFunctions();
          forall s, path, tid | asf.path_valid(s, path, tid)
            ensures asf.get_thread_pc(s, tid).Some?
          {
            lemma_PathImpliesThreadRunning(s, path, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      lAtomic.GenerateAtomicTauLeavesPCUnchangedLemma();

      str = @"
        lemma lemma_LStateToHStateMapsPCsCorrectly()
          ensures LStateToHStateMapsPCsCorrectly(GetAtomicConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      lAtomic.GenerateAtomicPathCantAffectOtherThreadPCsExceptViaForkLemma();

      str = @"
        lemma lemma_LHPathPropertiesMatch()
          ensures LHPathPropertiesMatch(GetAtomicConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionPreservesOK()
          ensures StateConversionPreservesOK(GetAtomicConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StateConversionSatisfiesRelation()
          ensures StateConversionSatisfiesRelation(GetAtomicConcurrentHoareLogicRequest())
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_IsValidAtomicConcurrentHoareLogicRequest()
          ensures IsValidAtomicConcurrentHoareLogicRequest(GetAtomicConcurrentHoareLogicRequest())
        {
          lemma_IsValidConcurrentHoareLogicRequest();
          lemma_LPathImpliesHPath();
          lemma_EmbeddedRequestCorresponds();
          lemma_AtomicInitImpliesOK();
          lemma_AtomicPathRequiresOK();
          lemma_AtomicSteppingThreadHasPC();
          lemma_LAtomic_AtomicTauLeavesPCUnchanged();
          lemma_LAtomic_AtomicThreadCantAffectOtherThreadPCExceptViaFork();
          lemma_LStateToHStateMapsPCsCorrectly();
          lemma_LInitImpliesHInit();
          lemma_LHPathPropertiesMatch();
          lemma_StateConversionPreservesOK();
          lemma_StateConversionSatisfiesRelation();
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLemmasForAssumeIntroProof()
    {
      GenerateLInitImpliesHInitLemma();
      GenerateLNextPlusLocalInvariantImpliesHNextLemma();
      GenerateIsValidAtomicConcurrentHoareLogicRequestLemmas();

      var str = @"
        lemma lemma_LiftLAtomicToHAtomic() returns (refinement_relation:RefinementRelation<LPlusState, H.Armada_TotalState>)
          ensures SpecRefinesSpec(AtomicSpec(LAtomic_GetSpecFunctions()), AtomicSpec(HAtomic_GetSpecFunctions()), refinement_relation)
          ensures refinement_relation == GetLPlusHRefinementRelation()
        {
          var ar := GetAtomicConcurrentHoareLogicRequest();
          lemma_IsValidAtomicConcurrentHoareLogicRequest();
          lemma_LiftAtomicToAtomicUsingCHLRequest(ar);
          refinement_relation := GetLPlusHRefinementRelation();
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
