using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class StackVarHidingProofGenerator : AbstractProofGenerator
  {
    private StackVariableHidingStrategyDecl strategy;
    private string hiddenVariablesMethodName;
    private HashSet<string> hiddenVariables;
    private HashSet<ArmadaPC> suppressedPCs;

    public StackVarHidingProofGenerator(ProofGenerationParams i_pgp, StackVariableHidingStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      hiddenVariablesMethodName = strategy.MethodName;
      hiddenVariables = new HashSet<string>(strategy.Variables);
      suppressedPCs = new HashSet<ArmadaPC>();
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the stack-variable-hiding strategy");
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

    protected override bool CheckVariableNameListEquivalence(IEnumerable<string> varNames_l, IEnumerable<string> varNames_h,
                                                             ArmadaSingleMethodSymbolTable s_l, ArmadaSingleMethodSymbolTable s_h,
                                                             string methodName, string descriptor)
    {
      string[] vars_l;
      if (methodName == hiddenVariablesMethodName) {
        vars_l = varNames_l.Where(v => !hiddenVariables.Contains(v)).ToArray();
      }
      else {
        vars_l = varNames_l.ToArray();
      }
      var vars_h = varNames_h.ToArray();
      if (vars_l.Length != vars_h.Length) {
        AH.PrintError(pgp.prog, $"Method {methodName} has {vars_l.Length} {descriptor} non-hidden variables in level {pgp.mLow.Name} but {vars_h.Length} of them in level {pgp.mHigh.Name}");
        return false;
      }

      for (int i = 0; i < vars_l.Length; ++i) {
        var name_l = vars_l[i];
        var name_h = vars_h[i];
        if (name_l != name_h) {
          AH.PrintError(pgp.prog, $"In method {methodName}, {descriptor} non-hidden variable number {i+1} is named {name_l} in level {pgp.mLow.Name} but named {name_h} in level {pgp.mHigh.Name}");
          return false;
        }
        var v_l = s_l.LookupVariable(name_l);
        var v_h = s_h.LookupVariable(name_h);
        if (!AH.TypesMatch(v_l.ty, v_h.ty)) {
          AH.PrintError(pgp.prog, $"In method {methodName}, the {descriptor} variable named {name_l} has type {v_l.ty} in level {pgp.mLow.Name} but type {v_h.ty} in level {pgp.mHigh.Name}");
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

    private bool IsVariableHidden(string methodName, string varName)
    {
      return methodName == hiddenVariablesMethodName && hiddenVariables.Contains(varName);
    }

    protected override void GenerateConvertStackFrame_LH()
    {
      var cases = new List<MatchCaseExpr>();
      var methodNames = pgp.symbolsLow.MethodNames;
      foreach (var methodName in methodNames) {
        var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        var ps = new List<Expression>();
        var bvs = new List<BoundVar>();
        foreach (var v in smst.AllVariablesInOrder) {
          var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
          if (!IsVariableHidden(methodName, v.FieldName)) {
            var e = AH.MakeNameSegment(v.FieldName, ty);
            ps.Add(e);
          }
          var bv = AH.MakeBoundVar(v.FieldName, v.GetFlattenedType(pgp.symbolsLow));
          bvs.Add(bv);
        }
        var case_body = AH.MakeApplyN($"H.Armada_StackFrame_{methodName}", ps, "H.Armada_StackFrame");
        cases.Add(AH.MakeMatchCaseExpr($"Armada_StackFrame_{methodName}", bvs, case_body));
      }

      var source = AH.MakeNameSegment("frame", "L.Armada_StackFrame");
      var body = AH.MakeMatchExpr(source, cases, "H.Armada_StackFrame");
      var formals = new List<Formal> { AH.MakeFormal("frame", "L.Armada_StackFrame") };
      var fn = AH.MakeFunction("ConvertStackFrame_LH", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
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

    ////////////////////////////////////////////////////////////////////////
    /// Lifting routines
    ////////////////////////////////////////////////////////////////////////

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
