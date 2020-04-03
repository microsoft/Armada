using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class VarHidingProofGenerator : AbstractProofGenerator
  {
    private VariableHidingStrategyDecl strategy;
    private HashSet<string> hiddenVariables;
    private HashSet<ArmadaPC> suppressedPCs;

    public VarHidingProofGenerator(ProofGenerationParams i_pgp, VariableHidingStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      hiddenVariables = new HashSet<string>(strategy.Variables);
      suppressedPCs = new HashSet<ArmadaPC>();
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }

      AddIncludesAndImports();

      var differ = new ASTDiff(pgp.originalsLow, pgp.originalsHigh);
      pcMap = differ.VariableHiding();
      ExtendPCMapWithExternalAndStructsMethods();
      ComputeSuppressedPCs();
      GenerateNextRoutineMap(false); // Don't warn on missing next routines, since some low-level routines don't map to high-level ones

      GenerateProofGivenMap();
    }

    private void ComputeSuppressedPCs()
    {
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        if (IsSuppressedNextRoutine(nextRoutine)) {
          suppressedPCs.Add(nextRoutine.stmt.Parsed.StartPC);
        }
      }
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateLemmasAboutGetNextState();
      GenerateOnlyHiddenAssignmentsBeforeYielding();
      GenerateConvertAndSuppressSteps();
      GenerateIntermediateStepsNonyieldingLemmas();
      GenerateVarHidingRequest();
      GenerateInvariantProof(pgp);
      GenerateHidingSatisfiesRelationLemma();
      GenerateHidingPreservesInitLemma();
      GenerateLocalViewCommutativityLemmas();
      GenerateLiftStepLemmas();
      GenerateFinalProof();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Checking that the layers are similar enough to generate a proof
    ////////////////////////////////////////////////////////////////////////

    // We have to override the default implementation of CheckGlobalsEquivalence because we need to
    // skip hidden variables.

    protected override bool CheckGlobalsEquivalence()
    {
      var globalVarsLow = pgp.symbolsLow.Globals.VariableNames.Where(s => !hiddenVariables.Contains(s)).ToArray();
      var globalVarsHigh = pgp.symbolsHigh.Globals.VariableNames.ToArray();

      if (globalVarsLow.Length != globalVarsHigh.Length) {
        AH.PrintError(pgp.prog, $"There are {globalVarsLow.Length} global variables in level {pgp.mLow.Name} (not counting hidden ones) but {globalVarsHigh.Length} in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < globalVarsLow.Length; ++i) {
        if (globalVarsLow[i] != globalVarsHigh[i]) {
          AH.PrintError(pgp.prog, $"Global variable number {i+1} (not counting hidden ones) in level {pgp.mLow.Name} is {globalVarsLow[i]}, which doesn't match global variable number {i+1} in level {pgp.mHigh.Name} which is {globalVarsHigh[i]}");
          return false;
        }
        var name = globalVarsLow[i];
        if (!CheckGlobalVariableEquivalence(name, pgp.symbolsLow.Globals.Lookup(name), pgp.symbolsHigh.Globals.Lookup(name))) {
          return false;
        }
      }

      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/varhiding/VarHiding.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("VarHidingSpecModule");
      pgp.MainProof.AddImport("VarHidingModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");

      pgp.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "convert");
      pgp.AddImport("util_option_s", null, "convert");
    }

    ////////////////////////////////////////////////////////////////////////
    /// Abstraction functions
    ////////////////////////////////////////////////////////////////////////

    protected override void GenerateConvertGlobals_LH()
    {
      var g = AH.MakeNameSegment("globals", "L.Armada_Globals");
      var ps = new List<Expression>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable) {
          var p = AH.MakeExprDotName(g, v.FieldName, v.ty);
          ps.Add(p);
        }
      }
      var body = AH.MakeApplyN("H.Armada_Globals", ps, "H.Armada_Globals");
      var formals = new List<Formal> { AH.MakeFormal("globals", "L.Armada_Globals") };
      var fn = AH.MakeFunction("ConvertGlobals_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertGlobalStaticVar_LH()
    {
      var v = AH.MakeNameSegment("v", "L.Armada_GlobalStaticVar");
      var es = new List<Expression>();
      foreach (var varName in hiddenVariables) {
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          var e = AH.MakeNotExpr(AH.MakeExprDotName(v, $"Armada_GlobalStaticVar_{varName}?", new BoolType()));
          es.Add(e);
        }
      }
      var body = AH.CombineExpressionsWithAnd(es);
      var formals = new List<Formal> { AH.MakeFormal("v", "L.Armada_GlobalStaticVar") };
      var pred = AH.MakePredicate("CanConvertGlobalStaticVar_LH", formals, body);
      pgp.AddDefaultClassDecl(pred, "convert");

      var cases = new List<MatchCaseExpr>();
      var case_body = AH.MakeNameSegment("H.Armada_GlobalStaticVarNone", "H.Armada_GlobalStaticVar");
      cases.Add(AH.MakeMatchCaseExpr("Armada_GlobalStaticVarNone", case_body));
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var gv = pgp.symbolsLow.Globals.Lookup(varName);
        if (gv is GlobalUnaddressableArmadaVariable) {
          case_body = AH.MakeNameSegment($"H.Armada_GlobalStaticVar_{varName}", "H.Armada_GlobalStaticVar");
          cases.Add(AH.MakeMatchCaseExpr($"Armada_GlobalStaticVar_{varName}", case_body));
        }
      }
      body = AH.MakeMatchExpr(v, cases, "H.Armada_GlobalStaticVar");
      var req = AH.MakeApply1("CanConvertGlobalStaticVar_LH", v, new BoolType());
      var fn = AH.MakeFunctionWithReq("ConvertGlobalStaticVar_LH", formals, req, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateConvertStoreBufferLocation_LH()
    {
      string str;

      str = @"
        predicate CanConvertStoreBufferLocation_LH(loc:L.Armada_StoreBufferLocation)
        {
          loc.Armada_StoreBufferLocation_Unaddressable? ==> CanConvertGlobalStaticVar_LH(loc.v)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferLocation_LH(loc:L.Armada_StoreBufferLocation) : H.Armada_StoreBufferLocation
          requires CanConvertStoreBufferLocation_LH(loc)
        {
          match loc
            case Armada_StoreBufferLocation_Unaddressable(v, fields) =>
              H.Armada_StoreBufferLocation_Unaddressable(ConvertGlobalStaticVar_LH(v), fields)
            case Armada_StoreBufferLocation_Addressable(p) =>
              H.Armada_StoreBufferLocation_Addressable(p)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBufferEntry_LH()
    {
      string str;

      str = @"
        predicate CanConvertStoreBufferEntry_LH(entry:L.Armada_StoreBufferEntry)
        {
          CanConvertStoreBufferLocation_LH(entry.loc)
        }
      ";
      pgp.AddPredicate(str, "convert");

      str = @"
        function ConvertStoreBufferEntry_LH(entry:L.Armada_StoreBufferEntry) : H.Armada_StoreBufferEntry
          requires CanConvertStoreBufferEntry_LH(entry)
        {
          H.Armada_StoreBufferEntry(ConvertStoreBufferLocation_LH(entry.loc), entry.value)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override void GenerateConvertStoreBuffer_LH()
    {
      string str = @"
        function ConvertStoreBuffer_LH(entries:seq<L.Armada_StoreBufferEntry>) : seq<H.Armada_StoreBufferEntry>
        {
          FilterMapSeqToSeq(entries, e => if CanConvertStoreBufferEntry_LH(e) then Some(ConvertStoreBufferEntry_LH(e)) else None)
        }
      ";
      pgp.AddFunction(str, "convert");
    }

    protected override MatchCaseExpr GetTraceEntryCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      var highRoutine = LiftNextRoutine(nextRoutine);
      ps.AddRange(highRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType)));

      string hname = LiftNextRoutine(nextRoutine).NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected override MatchCaseExpr GetTraceEntryCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      if (IsSuppressedNextRoutine(nextRoutine)) {
        // This is the case of an update statement that gets suppressed because it only updates hidden variables.
        return GetTraceEntryCaseForSuppressedNextRoutine_LH(nextRoutine);
      }
      else {
        return GetTraceEntryCaseForNormalNextRoutine_LH(nextRoutine);
      }
    }

    private void GenerateOnlyHiddenAssignmentsBeforeYielding()
    {
      string str;

      str = @"
        lemma lemma_UnhiddenStepMakingHighYieldingMakesLowOnlyHiddenAssignmentsBeforeYielding(
          ls: LState,
          ls': LState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires L.Armada_NextOneStep(ls, ls', lstep)
          requires hs == ConvertTotalState_LH(ls)
          requires hs' == ConvertTotalState_LH(ls')
          requires !lstep.Armada_TraceEntry_Tau?
          requires !ShouldSuppressTraceEntry(ls, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs', hstep.tid)
          ensures  Armada_ThreadYielding(L.Armada_GetSpecFunctions(), ls', lstep.tid) || OnlyHiddenAssignmentsBeforeYielding(ls'.threads[lstep.tid].pc)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_OnlyHiddenAssignmentsBeforeYielding(s: LState, s': LState, step: L.Armada_TraceEntry)
          requires L.Armada_NextOneStep(s, s', step)
          requires step.tid in s.threads
          requires OnlyHiddenAssignmentsBeforeYielding(s.threads[step.tid].pc)
          requires !step.Armada_TraceEntry_Tau?
          requires L.Armada_IsNonyieldingPC(s.threads[step.tid].pc)
          ensures  ShouldSuppressTraceEntry(s, step)
          ensures  step.tid in s'.threads
          ensures  OnlyHiddenAssignmentsBeforeYielding(s'.threads[step.tid].pc)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_YieldPointMapsToYieldPoint(pc:L.Armada_PC)
          ensures  !L.Armada_IsNonyieldingPC(pc) ==> !H.Armada_IsNonyieldingPC(ConvertPC_LH(pc))
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateConvertAndSuppressSteps()
    {
      string str;

      str = @"
        predicate ShouldSuppressTraceEntry(s: LState, entry: L.Armada_TraceEntry)
        {
          || (&& entry.Armada_TraceEntry_Tau?
             && entry.tid in s.threads
             && |s.threads[entry.tid].storeBuffer| > 0
             && !CanConvertStoreBufferEntry_LH(s.threads[entry.tid].storeBuffer[0]))
      ";
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (IsSuppressedNextRoutine(nextRoutine)) {
          str += $"  || entry.Armada_TraceEntry_{nextRoutine.NameSuffix}?";
        }
      }
      str += "}\n";
      pgp.AddPredicate(str);

      str = @"
        function ConvertAndSuppressSteps(s: LState, steps: seq<L.Armada_TraceEntry>) : seq<H.Armada_TraceEntry>
          decreases |steps|
        {
          if |steps| == 0 then
            []
          else
            var s' := L.Armada_GetNextStateAlways(s, steps[0]);
            if ShouldSuppressTraceEntry(s, steps[0]) then
              ConvertAndSuppressSteps(s', steps[1..])
            else
              [ConvertTraceEntry_LH(steps[0])] + ConvertAndSuppressSteps(s', steps[1..])
        }
      ";
      pgp.AddFunction(str);

      str = @"
        function ConvertAndSuppressMultistep(s: LPlusState, entry: LStep) : HStep
        {
          Armada_Multistep(ConvertAndSuppressSteps(s.s, entry.steps), entry.tid, entry.tau)
        }
      ";
      pgp.AddFunction(str);

      str = @"
        lemma lemma_ConvertAndSuppressStepsMaintainsMatching(s: LState, tau: bool, tid: Armada_ThreadHandle, steps: seq<L.Armada_TraceEntry>)
          requires forall step :: step in steps ==> step.tid == tid
          requires forall step :: step in steps ==> step.Armada_TraceEntry_Tau? == tau
          ensures forall step :: step in ConvertAndSuppressSteps(s, steps) ==> step.tid == tid
          ensures forall step :: step in ConvertAndSuppressSteps(s, steps) ==> step.Armada_TraceEntry_Tau? == tau
          ensures |ConvertAndSuppressSteps(s, steps)| <= |steps|
          decreases |steps|
        {
          if |steps| > 0 {
            var s' := L.Armada_GetNextStateAlways(s, steps[0]);
            lemma_ConvertAndSuppressStepsMaintainsMatching(s', tau, tid, steps[1..]);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private HashSet<ArmadaPC> ComputePCsWithOnlyHiddenAssignmentsBeforeYielding()
    {
      var allPCsList = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllPCs(allPCsList);

      var nonyieldingPCsList = new List<ArmadaPC>();
      pgp.symbolsLow.AllMethods.AppendAllNonyieldingPCs(nonyieldingPCsList);
      var nonyieldingPCs = new HashSet<ArmadaPC>(nonyieldingPCsList);

      var onlyHiddenAssignmentsBeforeYieldingPCs = new HashSet<ArmadaPC>();

      // Start out by enumerating all the PCs that yield, i.e., the
      // ones that are among all PCs but not among the nonyielding
      // ones.  Obviously, these PCs don't have any hidden assignments
      // before yielding.

      foreach (var pc in allPCsList) {
        if (!nonyieldingPCs.Contains(pc)) {
          onlyHiddenAssignmentsBeforeYieldingPCs.Add(pc);
        }
      }

      // Compute a list of all suppressed next routines, corresponding
      // to hidden assignments.  This will be useful for the next
      // step.

      var suppressedNextRoutines = new List<NextRoutine>();
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (IsSuppressedNextRoutine(nextRoutine)) {
          suppressedNextRoutines.Add(nextRoutine);
        }
      }

      // For each suppressed next routine, if its end PC is among the
      // PCs we've computed so far, put its start PC into the list.
      // Keep doing this until we have an iteration through all
      // suppressed next routines that doesn't add any new PC to our
      // to-be-returned set.

      bool done = false;
      while (!done) {
        done = true;
        foreach (var nextRoutine in suppressedNextRoutines) {
          if (onlyHiddenAssignmentsBeforeYieldingPCs.Contains(nextRoutine.stmt.Parsed.EndPC) &&
              !onlyHiddenAssignmentsBeforeYieldingPCs.Contains(nextRoutine.stmt.Parsed.StartPC)) {
            onlyHiddenAssignmentsBeforeYieldingPCs.Add(nextRoutine.stmt.Parsed.StartPC);
            done = false;
          }
        }
      }

      return onlyHiddenAssignmentsBeforeYieldingPCs;
    }

    private void GenerateIntermediateStepsNonyieldingLemmas()
    {
      HashSet<ArmadaPC> onlyHiddenAssignmentsBeforeYieldingPCs = ComputePCsWithOnlyHiddenAssignmentsBeforeYielding();

      string str;

      str = @"
        predicate OnlyHiddenAssignmentsBeforeYielding(pc:L.Armada_PC)
        {
      ";
      foreach (var pc in onlyHiddenAssignmentsBeforeYieldingPCs) {
        str += $"    || pc.{pc}?\n";
      }
      str += "  }\n";
      pgp.AddPredicate(str);

      str = @"
        lemma lemma_IntermediateStatesNonyieldingHelper(
          ls:LPlusState,
          ls':LPlusState,
          hs:HState,
          hs':HState,
          lsteps:seq<L.Armada_TraceEntry>,
          hsteps:seq<H.Armada_TraceEntry>,
          lstates:seq<LPlusState>,
          hstates:seq<HState>,
          tid:Armada_ThreadHandle,
          lpos:int,
          hpos:int
          )
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> !step.Armada_TraceEntry_Tau?
          requires var lstates := Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps);
                   forall i :: 0 < i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[i], tid)
          requires hs == ConvertTotalState_LPlusH(ls)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires hsteps == ConvertAndSuppressSteps(ls.s, lsteps)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps)
          requires 0 < lpos < |lsteps|
          requires 0 <= hpos < |hsteps|
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lstates[lpos], ls', lsteps[lpos..])
          requires hstates[hpos] == ConvertTotalState_LPlusH(lstates[lpos])
          requires hsteps[hpos..] == ConvertAndSuppressSteps(lstates[lpos].s, lsteps[lpos..])
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[lpos], tid) || OnlyHiddenAssignmentsBeforeYielding(lstates[lpos].s.threads[tid].pc)
          requires Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[hpos], tid)
          ensures  false
        {
          var lp := lpos;
          while lp < |lsteps|
            invariant lpos <= lp <= |lsteps|
            invariant hstates[hpos] == ConvertTotalState_LPlusH(lstates[lp])
            invariant hsteps[hpos..] == ConvertAndSuppressSteps(lstates[lp].s, lsteps[lp..])
            invariant Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lstates[lp], ls', lsteps[lp..])
            invariant Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[lpos], tid) || OnlyHiddenAssignmentsBeforeYielding(lstates[lp].s.threads[tid].pc)
          {
            lemma_ArmadaGetStateSequenceOnePos(LPlus_GetSpecFunctions(), ls, lsteps, lp);
            lemma_OnlyHiddenAssignmentsBeforeYielding(lstates[lp].s, lstates[lp+1].s, lsteps[lp]);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma {:timeLimitMultiplier 2} lemma_IntermediateStatesNonyielding(
          vr:VHRequest,
          ls:LPlusState,
          ls':LPlusState,
          hs:HState,
          hs':HState,
          lsteps:seq<L.Armada_TraceEntry>,
          hsteps:seq<H.Armada_TraceEntry>,
          tid:Armada_ThreadHandle,
          lstates:seq<LPlusState>,
          hstates:seq<HState>
          )
          requires vr == GetVarHidingRequest()
          requires vr.inv(ls)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> !step.Armada_TraceEntry_Tau?
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires forall i :: 0 < i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[i], tid)
          requires hs == ConvertTotalState_LPlusH(ls)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires hsteps == ConvertAndSuppressSteps(ls.s, lsteps)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall step :: step in hsteps ==> !step.Armada_TraceEntry_Tau?
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps);
          ensures  forall i :: 0 < i < |hsteps| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          ensures  Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs', tid)
        {
          if tid in ls'.s.threads {
            lemma_YieldPointMapsToYieldPoint(ls'.s.threads[tid].pc);
          }
          assert hs'.stop_reason.Armada_NotStopped? && tid in hs'.threads ==> !H.Armada_IsNonyieldingPC(hs'.threads[tid].pc);

          if |hsteps| < 2 {
            forall i | 0 < i < |hsteps|
              ensures !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
            {
              assert false;
            }
            return;
          }

          if hpos :| 0 < hpos < |hsteps| && Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[hpos], tid) {
            var lpos := lemma_FindFirstNonsuppressedStepPreceding(vr, ls, ls', hs, hs', lsteps, hsteps, lstates, hstates, tid, false, hpos);
            lemma_ArmadaGetStateSequenceOnePos(LPlus_GetSpecFunctions(), ls, lsteps, lpos);
            lemma_UnhiddenStepMakingHighYieldingMakesLowOnlyHiddenAssignmentsBeforeYielding(
              lstates[lpos].s, lstates[lpos+1].s, lsteps[lpos], hstates[hpos-1], hstates[hpos], hsteps[hpos-1]);
            lemma_IntermediateStatesNonyieldingHelper(ls, ls', hs, hs', lsteps, hsteps, lstates, hstates, tid, lpos+1, hpos);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma {:timeLimitMultiplier 2} lemma_FindFirstNonsuppressedStepPreceding(
          vr:VHRequest,
          ls:LPlusState,
          ls':LPlusState,
          hs:HState,
          hs':HState,
          lsteps:seq<L.Armada_TraceEntry>,
          hsteps:seq<H.Armada_TraceEntry>,
          lstates:seq<LPlusState>,
          hstates:seq<HState>,
          tid:Armada_ThreadHandle,
          tau:bool,
          hpos:int
          ) returns (
          lpos:int
          )
          requires vr == GetVarHidingRequest()
          requires vr.inv(ls)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls, tid)
          requires Armada_ThreadYielding(LPlus_GetSpecFunctions(), ls', tid)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> step.Armada_TraceEntry_Tau? == tau
          requires var lstates := Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps);
                   forall i :: 0 < i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lstates[i], tid)
          requires hs == ConvertTotalState_LPlusH(ls)
          requires hs' == ConvertTotalState_LPlusH(ls')
          requires hsteps == ConvertAndSuppressSteps(ls.s, lsteps)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall step :: step in hsteps ==> step.Armada_TraceEntry_Tau? == tau
          requires lstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps)
          requires 0 < hpos < |hsteps|
          ensures  0 <= lpos < |lsteps|
          ensures  Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lstates[lpos], ls', lsteps[lpos..])
          ensures  hstates[hpos-1] == ConvertTotalState_LPlusH(lstates[lpos])
          ensures  hstates[hpos] == ConvertTotalState_LPlusH(lstates[lpos+1])
          ensures  hsteps[hpos-1..] == ConvertAndSuppressSteps(lstates[lpos].s, lsteps[lpos..])
          ensures  !ShouldSuppressTraceEntry(lstates[lpos].s, lsteps[lpos])
        {
          var lp := 0;
          var hp := 0;
          while hp < hpos-1 || ShouldSuppressTraceEntry(lstates[lp].s, lsteps[lp])
            invariant 0 <= lp <= |lsteps|
            invariant 0 <= hp <= hpos-1
            invariant hstates[hp] == ConvertTotalState_LPlusH(lstates[lp])
            invariant Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lstates[lp], ls', lsteps[lp..])
            invariant hsteps[hp..] == ConvertAndSuppressSteps(lstates[lp].s, lsteps[lp..])
            invariant vr.inv(lstates[lp])
            decreases |lsteps| - lp
          {
            lemma_ArmadaGetStateSequenceOnePos(LPlus_GetSpecFunctions(), ls, lsteps, lp);
            lemma_LiftStepWithoutVariable(vr, lstates[lp], lstates[lp+1], lsteps[lp]);
            lemma_ArmadaGetStateSequenceOnePos(H.Armada_GetSpecFunctions(), hs, hsteps, hp);
            if !ShouldSuppressTraceEntry(lstates[lp].s, lsteps[lp]) {
              lemma_NextOneStepImpliesGetNextState_H(ConvertTotalState_LPlusH(lstates[lp]), ConvertTotalState_LPlusH(lstates[lp + 1]), ConvertTraceEntry_LH(lsteps[lp]));
              calc {
                hstates[hp+1];
                H.Armada_GetNextStateAlways(hstates[hp], hsteps[hp]);
                H.Armada_GetNextStateAlways(ConvertTotalState_LPlusH(lstates[lp]), ConvertTraceEntry_LH(lsteps[lp]));
                ConvertTotalState_LPlusH(lstates[lp + 1]);
              }
              hp := hp + 1;
            }
            lemma_NextOneStepMaintainsInductiveInv(lstates[lp], lstates[lp+1], lsteps[lp]);
            lp := lp + 1;
          }

          lpos := lp;
          lemma_ArmadaGetStateSequenceOnePos(LPlus_GetSpecFunctions(), ls, lsteps, lpos);
          lemma_LiftStepWithoutVariable(vr, lstates[lpos], lstates[lpos+1], lsteps[lpos]);
          lemma_NextOneStepImpliesGetNextState_H(ConvertTotalState_LPlusH(lstates[lpos]), ConvertTotalState_LPlusH(lstates[lpos+1]),
                                                 ConvertTraceEntry_LH(lsteps[lpos]));
          var hpos_prev := hpos-1;
          lemma_ArmadaGetStateSequenceOnePos(H.Armada_GetSpecFunctions(), hs, hsteps, hpos_prev);
          assert hstates[hpos_prev+1] == H.Armada_GetNextStateAlways(hstates[hpos_prev], hsteps[hpos_prev]);
        }
      ";
      pgp.AddLemma(str);
    }

    ////////////////////////////////////////////////////////////////////////
    /// Variable-hiding request
    ////////////////////////////////////////////////////////////////////////

    private void GenerateVarHidingRequest()
    {
      string str;

      var lplusstate = AH.ReferToType("LPlusState");
      var hstate = AH.ReferToType("HState");
      var lstep = AH.ReferToType("LStep");
      var hstep = AH.ReferToType("HStep");
      var vhrequest = AH.MakeGenericTypeSpecific("VarHidingRequest", new List<Type>{ lplusstate, hstate, lstep, hstep });
      pgp.MainProof.AddTypeSynonymDecl("VHRequest", vhrequest);

      if (suppressedPCs.Count > 0) {
        str = @"
          predicate IsSuppressedPC(pc:L.Armada_PC)
          {
        ";
        str += string.Join(" || ", suppressedPCs.Select(s => $"pc.{s}?"));
        str += "\n}\n";
      }
      else {
        str = @"
          predicate IsSuppressedPC(pc:L.Armada_PC)
          {
            false
          }
        ";
      }
      pgp.AddPredicate(str);

      str = @"
        function GetVarHidingRequest() : VHRequest
        {
          VarHidingRequest(GetLPlusSpec(), GetHSpec(), GetLPlusHRefinementRelation(), InductiveInv, ConvertTotalState_LPlusH,
                           ConvertAndSuppressMultistep)
        }
      ";
      pgp.AddFunction(str);
    }

    private void GenerateHidingSatisfiesRelationLemma()
    {
      string str = @"
        lemma lemma_HidingSatisfiesRelation(vr:VHRequest)
          requires vr == GetVarHidingRequest()
          ensures  HidingSatisfiesRelation(vr)
        {
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateHidingPreservesInitLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      var str = @"
        lemma lemma_HidingPreservesInit(vr:VHRequest)
          requires vr == GetVarHidingRequest()
          ensures  HidingPreservesInit(vr)
        {
          forall ls | ls in vr.lspec.init
            ensures vr.hider(ls) in vr.hspec.init
          {
            var hs := vr.hider(ls);
            var hconfig := ConvertConfig_LH(ls.config);

            lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
            assert H.Armada_InitConfig(hs, hconfig);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateLocalViewCommutativityLemmas()
    {
      string str;

      string cases = "";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        if (hiddenVariables.Contains(varName)) {
          continue;
        }
        var globalVar = pgp.symbolsLow.Globals.Lookup(varName);
        if (globalVar is AddressableArmadaVariable || globalVar.NoTSO()) {
          continue;
        }
        cases += $"case Armada_GlobalStaticVar_{varName} => {{ }}";
      }
      str = $@"
        lemma lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(
          lglobals:L.Armada_Globals, lv:L.Armada_GlobalStaticVar, fields:seq<Armada_Field>, value:Armada_PrimitiveValue,
          hv:H.Armada_GlobalStaticVar, hglobals1:H.Armada_Globals, hglobals2:H.Armada_Globals)
          requires CanConvertGlobalStaticVar_LH(lv)
          requires hv == ConvertGlobalStaticVar_LH(lv)
          requires hglobals1 == ConvertGlobals_LH(L.Armada_ApplyTauUnaddressable(lglobals, lv, fields, value))
          requires hglobals2 == H.Armada_ApplyTauUnaddressable(ConvertGlobals_LH(lglobals), hv, fields, value)
          ensures  hglobals1 == hglobals2
        {{
          match lv
            case Armada_GlobalStaticVarNone =>
            {{
              var hglobals := ConvertGlobals_LH(lglobals);
              assert hglobals1 == hglobals == hglobals2;
            }}
            { cases }
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem:L.Armada_SharedMemory, lentry:L.Armada_StoreBufferEntry)
          requires !CanConvertStoreBufferEntry_LH(lentry)
          ensures  ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry)) == ConvertSharedMemory_LH(lmem)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem:L.Armada_SharedMemory, lentry:L.Armada_StoreBufferEntry,
                                                             hentry:H.Armada_StoreBufferEntry, hmem1:H.Armada_SharedMemory,
                                                             hmem2:H.Armada_SharedMemory)
          requires CanConvertStoreBufferEntry_LH(lentry)
          requires hentry == ConvertStoreBufferEntry_LH(lentry)
          requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry))
          requires hmem2 == H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry)
          ensures  hmem1 == hmem2
        {
          match lentry.loc
            case Armada_StoreBufferLocation_Unaddressable(lv, lfields) =>
            {
              var hv := ConvertGlobalStaticVar_LH(lv);
              lemma_ApplyStoreBufferEntryUnaddressableCommutesWithConvert(lmem.globals, lv, lfields, lentry.value, hv, hmem1.globals,
                                                                          hmem2.globals);
            }
            case Armada_StoreBufferLocation_Addressable(p) =>
            {
            }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ApplyStoreBufferCommutesWithConvert(lmem:L.Armada_SharedMemory, lbuf:seq<L.Armada_StoreBufferEntry>,
                                                        hbuf:seq<H.Armada_StoreBufferEntry>, hmem1:H.Armada_SharedMemory,
                                                        hmem2:H.Armada_SharedMemory)
          requires hbuf == ConvertStoreBuffer_LH(lbuf)
          requires hmem1 == ConvertSharedMemory_LH(L.Armada_ApplyStoreBuffer(lmem, lbuf))
          requires hmem2 == H.Armada_ApplyStoreBuffer(ConvertSharedMemory_LH(lmem), hbuf)
          ensures  hmem1 == hmem2
          decreases |lbuf| + |hbuf|
        {
          if |lbuf| == 0 {
              return;
          }

          var lmem' := L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]);

          if CanConvertStoreBufferEntry_LH(lbuf[0]) {
              var hmem1' := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]));
              var hmem2' := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hbuf[0]);
              lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lbuf[0], hbuf[0], hmem1', hmem2');
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf[1..], hmem1, hmem2);
          }
          else {
              lemma_ApplyingUnconvertibleStoreBufferEntryDoesntChangeHState(lmem, lbuf[0]);
              assert ConvertSharedMemory_LH(lmem') == ConvertSharedMemory_LH(lmem);
              assert hbuf == ConvertStoreBuffer_LH(lbuf[1..]);
              lemma_ApplyStoreBufferCommutesWithConvert(lmem', lbuf[1..], hbuf, hmem1, hmem2);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_GetThreadLocalViewCommutesWithConvert(ls:LState, hs:HState, tid:Armada_ThreadHandle)
          requires hs == ConvertTotalState_LH(ls)
          requires tid in ls.threads;
          ensures  ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(hs, tid)
        {
          assert tid in hs.threads;
          lemma_ApplyStoreBufferCommutesWithConvert(ls.mem, ls.threads[tid].storeBuffer,
                                                    hs.threads[tid].storeBuffer,
                                                    ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)),
                                                    H.Armada_GetThreadLocalView(hs, tid));
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_GetThreadLocalViewAlwaysCommutesWithConvert()
          ensures forall ls:L.Armada_TotalState, tid:Armada_ThreadHandle :: tid in ls.threads ==>
                    ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) == H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
        {
          forall ls:L.Armada_TotalState, tid:Armada_ThreadHandle | tid in ls.threads
            ensures ConvertSharedMemory_LH(L.Armada_GetThreadLocalView(ls, tid)) ==
                    H.Armada_GetThreadLocalView(ConvertTotalState_LH(ls), tid)
          {
              var hs := ConvertTotalState_LH(ls);
              lemma_GetThreadLocalViewCommutesWithConvert(ls, hs, tid);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StoreBufferAppendConversion(buf: seq<L.Armada_StoreBufferEntry>, entry: L.Armada_StoreBufferEntry)
          ensures  ConvertStoreBuffer_LH(buf + [entry]) ==
                     if CanConvertStoreBufferEntry_LH(entry) then
                       ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)]
                     else
                       ConvertStoreBuffer_LH(buf)
        {
          assert [entry][1..] == [];

          if |buf| == 0 {
            assert buf + [entry] == [entry];
            assert ConvertStoreBuffer_LH(buf + [entry]) == ConvertStoreBuffer_LH([entry]);
            assert ConvertStoreBuffer_LH(buf) == [];

            if CanConvertStoreBufferEntry_LH(entry) {
              calc {
                  ConvertStoreBuffer_LH([entry]);
                  [ConvertStoreBufferEntry_LH(entry)] + ConvertStoreBuffer_LH([entry][1..]);
                  [ConvertStoreBufferEntry_LH(entry)] + ConvertStoreBuffer_LH([]);
                  [ConvertStoreBufferEntry_LH(entry)] + [];
                  [ConvertStoreBufferEntry_LH(entry)];
              }
            }
            else {
              calc {
                  ConvertStoreBuffer_LH([entry]);
                  ConvertStoreBuffer_LH([entry][1..]);
                  ConvertStoreBuffer_LH([]);
                  [];
              }
            }
          }
          else {
            calc {
              ConvertStoreBuffer_LH(buf + [entry]);
              {
                assert buf == [buf[0]] + buf[1..];
              }
              ConvertStoreBuffer_LH([buf[0]] + buf[1..] + [entry]);
              {
                assert [buf[0]] + buf[1..] + [entry] == [buf[0]] + (buf[1..] + [entry]);
              }
              ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
            }
            if CanConvertStoreBufferEntry_LH(buf[0]) {
              calc {
                ConvertStoreBuffer_LH(buf + [entry]);
                ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
                [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..] + [entry]);
              }
              lemma_StoreBufferAppendConversion(buf[1..], entry);
              if CanConvertStoreBufferEntry_LH(entry) {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + (ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)];
                  ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)];
                }
              }
              else {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  [ConvertStoreBufferEntry_LH(buf[0])] + ConvertStoreBuffer_LH(buf[1..]);
                  ConvertStoreBuffer_LH(buf);
                }
              }
            }
            else {
              assert ConvertStoreBuffer_LH(buf) == ConvertStoreBuffer_LH(buf[1..]);
              calc {
                ConvertStoreBuffer_LH(buf + [entry]);
                ConvertStoreBuffer_LH([buf[0]] + (buf[1..] + [entry]));
                ConvertStoreBuffer_LH((buf[1..] + [entry]));
              }
              lemma_StoreBufferAppendConversion(buf[1..], entry);
              if CanConvertStoreBufferEntry_LH(entry) {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  ConvertStoreBuffer_LH(buf[1..]) + [ConvertStoreBufferEntry_LH(entry)];
                  ConvertStoreBuffer_LH(buf) + [ConvertStoreBufferEntry_LH(entry)];
                }
              }
              else {
                calc {
                  ConvertStoreBuffer_LH(buf + [entry]);
                  ConvertStoreBuffer_LH(buf[1..]);
                  ConvertStoreBuffer_LH(buf);
                }
              }
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StoreBufferAppendAlwaysCommutesWithConvert()
          ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)} :: CanConvertStoreBufferEntry_LH(lentry) ==> H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) == ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
        {
          forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry: L.Armada_StoreBufferEntry {:trigger L.Armada_StoreBufferAppend(lbuf, lentry)}
            | CanConvertStoreBufferEntry_LH(lentry)
            ensures H.Armada_StoreBufferAppend(ConvertStoreBuffer_LH(lbuf), ConvertStoreBufferEntry_LH(lentry)) == ConvertStoreBuffer_LH(L.Armada_StoreBufferAppend(lbuf, lentry))
          {
            lemma_StoreBufferAppendConversion(lbuf, lentry);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertStoreBufferCommutesOverBeheadment(buf:seq<L.Armada_StoreBufferEntry>)
          requires |buf| > 0
          requires CanConvertStoreBufferEntry_LH(buf[0])
          ensures  ConvertStoreBuffer_LH(buf[1..]) == ConvertStoreBuffer_LH(buf)[1..]
        {
          var hbuf1 := ConvertStoreBuffer_LH(buf[1..]);
          var hbuf2 := ConvertStoreBuffer_LH(buf)[1..];
          assert |hbuf1| == |hbuf2|;

          forall i | 0 <= i < |buf| - 1
            ensures hbuf1[i] == hbuf2[i]
          {
          }

          assert hbuf1 == hbuf2;
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid:Armada_ThreadHandle)
          ensures forall s:L.Armada_TotalState, entry:L.Armada_StoreBufferEntry {:trigger L.Armada_AppendToThreadStoreBuffer(s, tid, entry)} ::
            tid in s.threads && !CanConvertStoreBufferEntry_LH(entry) ==>
            ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_LH(s)
        {
          forall s:L.Armada_TotalState, entry:L.Armada_StoreBufferEntry {:trigger L.Armada_AppendToThreadStoreBuffer(s, tid, entry)} |
            tid in s.threads && !CanConvertStoreBufferEntry_LH(entry)
            ensures ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry)) == ConvertTotalState_LH(s)
          {
            var hs := ConvertTotalState_LH(s);
            var hs' := ConvertTotalState_LH(L.Armada_AppendToThreadStoreBuffer(s, tid, entry));
            lemma_StoreBufferAppendConversion(s.threads[tid].storeBuffer, entry);
            assert hs.threads[tid].storeBuffer == hs'.threads[tid].storeBuffer;
            assert hs.threads == hs'.threads;
            assert hs == hs';
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateLiftStepLemmaForSuppressedNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{TranslateFormalNameUsingPcMap(f, nextRoutine.pc, pcMap)}"));

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(vr:VHRequest, ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires vr == GetVarHidingRequest()
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            ensures  ShouldSuppressTraceEntry(ls.s, lstep)
            ensures  vr.hider(ls) == vr.hider(ls')
        {{
            var hs := vr.hider(ls);
            var hs' := vr.hider(ls');
            var tid := lstep.tid;
            var hstep := ConvertTraceEntry_LH(lstep);

            lemma_AppendingHiddenStoreBufferEntryAlwaysDoesntAffectHighLevel(tid);
            assert hs'.stop_reason == hs.stop_reason;
            assert hs'.threads[tid] == hs.threads[tid];
            assert hs' == hs;
        }}
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", LiftNextRoutine(nextRoutine).Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var hNextRoutineName = LiftNextRoutine(nextRoutine).NameSuffix;

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(vr:VHRequest, ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires vr == GetVarHidingRequest()
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            ensures  !ShouldSuppressTraceEntry(ls.s, lstep)
            ensures  H.Armada_NextOneStep(vr.hider(ls), vr.hider(ls'), ConvertTraceEntry_LH(lstep))
        {{
            var hs := vr.hider(ls);
            var hs' := vr.hider(ls');
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

    protected override void GenerateLiftStepLemmaForTauNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(vr:VHRequest, ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires vr == GetVarHidingRequest()
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            ensures  if ShouldSuppressTraceEntry(ls.s, lstep) then
                       vr.hider(ls) == vr.hider(ls')
                     else
                       H.Armada_NextOneStep(vr.hider(ls), vr.hider(ls'), ConvertTraceEntry_LH(lstep))
        {{
            var hs := vr.hider(ls);
            var hs' := vr.hider(ls');
            var tid := lstep.tid;
            var hstep := ConvertTraceEntry_LH(lstep);

            var lentry := ls.s.threads[tid].storeBuffer[0];
            if CanConvertStoreBufferEntry_LH(lentry) {{
              assert H.Armada_ValidStep_{nextRoutineName}(hs, tid{hstep_params});
              assert H.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(hs, tid{hstep_params});
              var hentry := hs.threads[tid].storeBuffer[0];
              var lmem := ls.s.mem;
              var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
              var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
              lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

              var alt_hs' := H.Armada_GetNextState_{nextRoutineName}(hs, tid{hstep_params});
              assert hs' == alt_hs';
              assert H.Armada_Next_{nextRoutineName}(hs, hs', tid{hstep_params});
            }}
            else {{
              assert hs'.threads[tid].storeBuffer == hs.threads[tid].storeBuffer;
              assert hs'.threads[tid] == hs.threads[tid];
              assert hs'.threads == hs.threads;
              assert hs'.stop_reason == hs.stop_reason;
              assert hs' == hs;
            }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private bool IsSuppressedNextRoutine(NextRoutine nextRoutine)
    {
      return nextRoutine.nextType is NextType.Update && pcMap[nextRoutine.stmt.Parsed.StartPC] == pcMap[nextRoutine.stmt.Parsed.EndPC];
    }

    protected override void GenerateLiftStepLemmas()
    {
      var finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (IsSuppressedNextRoutine(nextRoutine)) {
          // This is the case of an update statement that gets suppressed because it only updates hidden variables.
          GenerateLiftStepLemmaForSuppressedNextRoutine(nextRoutine);
        }
        else if (nextRoutine.nextType == NextType.Tau) {
          GenerateLiftStepLemmaForTauNextRoutine(nextRoutine);
        }
        else {
          GenerateLiftStepLemmaForNormalNextRoutine(nextRoutine);
        }
        var nextRoutineName = nextRoutine.NameSuffix;
        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LiftNext_{nextRoutineName}(vr, ls, ls', lstep);";
      }

      string str = $@"
        lemma lemma_LiftStepWithoutVariable(vr:VHRequest, ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry)
            requires vr == GetVarHidingRequest()
            requires vr.inv(ls)
            requires LPlus_NextOneStep(ls, ls', lstep)
            ensures  if ShouldSuppressTraceEntry(ls.s, lstep) then
                       vr.hider(ls) == vr.hider(ls')
                     else
                       H.Armada_NextOneStep(vr.hider(ls), vr.hider(ls'), ConvertTraceEntry_LH(lstep))
        {{
          match lstep {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LiftMultipleStepsWithoutVariable(vr: VHRequest, ls: LPlusState, ls': LPlusState, steps: seq<L.Armada_TraceEntry>)
          requires vr == GetVarHidingRequest()
          requires vr.inv(ls)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', steps)
          ensures  Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), vr.hider(ls), vr.hider(ls'), ConvertAndSuppressSteps(ls.s, steps))
          decreases |steps|
        {
          if |steps| == 0 {
            return;
          }

          var lsplus1 := LPlus_GetNextStateAlways(ls, steps[0]);
          lemma_LiftStepWithoutVariable(vr, ls, lsplus1, steps[0]);
          if !ShouldSuppressTraceEntry(ls.s, steps[0]) {
            lemma_NextOneStepImpliesGetNextState_H(vr.hider(ls), vr.hider(lsplus1), ConvertTraceEntry_LH(steps[0]));
          }
          lemma_LiftMultipleStepsWithoutVariable(vr, lsplus1, ls', steps[1..]);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str;

      str = @"
        lemma lemma_AllActionsLiftableWithoutVariable(vr: VHRequest)
          requires vr == GetVarHidingRequest()
          ensures AllActionsLiftableWithoutVariable(vr)
        {
          forall ls, ls', lstep | ActionTuple(ls, ls', lstep) in vr.lspec.next && vr.inv(ls) && vr.hider(ls) != vr.hider(ls')
            ensures ActionTuple(vr.hider(ls), vr.hider(ls'), vr.step_refiner(ls, lstep)) in vr.hspec.next
          {
            lemma_LiftMultipleStepsWithoutVariable(vr, ls, ls', lstep.steps);
            lemma_ConvertAndSuppressStepsMaintainsMatching(ls.s, lstep.tau, lstep.tid, lstep.steps);
            var hs := vr.hider(ls);
            var hs' := vr.hider(ls');
            var hstep := vr.step_refiner(ls, lstep);
            if !lstep.tau {
                var lstates := Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lstep.steps);
                var hstates := Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hstep.steps);
                lemma_IntermediateStatesNonyielding(vr, ls, ls', hs, hs', lstep.steps, hstep.steps, lstep.tid, lstates, hstates);
            }
            assert H.Armada_Next(hs, hs', hstep);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ValidVarHidingRequest(vr:VHRequest)
            requires vr == GetVarHidingRequest()
            ensures  ValidVarHidingRequest(vr)
        {
            lemma_InductiveInvIsInvariant();
            lemma_AllActionsLiftableWithoutVariable(vr);
            lemma_HidingSatisfiesRelation(vr);
            lemma_HidingPreservesInit(vr);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ProveRefinementViaVarHiding()
            ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
            var lspec := L.Armada_Spec();
            var hspec := H.Armada_Spec();
            var vr := GetVarHidingRequest();

            forall lb | BehaviorSatisfiesSpec(lb, lspec)
                ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
            {
                var alb := lemma_GetLPlusAnnotatedBehavior(lb);
                lemma_ValidVarHidingRequest(vr);
                var ahb := lemma_PerformVarHiding(vr, alb);
                assert BehaviorRefinesBehavior(alb.states, ahb.states, vr.relation);
                lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
                lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
            }
        }
      ";
      pgp.AddLemma(str);
    }
  }

}
