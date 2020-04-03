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

  public class StarWeakeningProofGenerator : AbstractProofGenerator
  {
    private StarWeakeningStrategyDecl strategy;
    private HashSet<ArmadaPC> weakenedPCs;

    public StarWeakeningProofGenerator(ProofGenerationParams i_pgp, StarWeakeningStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      weakenedPCs = new HashSet<ArmadaPC>();
    }

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();
      
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/starweakening/StarWeakening.i.dfy");
      pgp.MainProof.AddImport("StarWeakeningModule");
      pgp.MainProof.AddImport("StarWeakeningSpecModule");
      pgp.MainProof.AddImport("InvariantsModule");


      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddImport("util_option_s");


      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddImport("util_collections_seqs_s");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddImport("util_collections_seqs_i");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddImport("util_collections_sets_i");

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");
      pgp.MainProof.AddImport("util_collections_maps_i");
    }

    protected override void GenerateConvertTraceEntry_LH()
    {
      var cases = new List<MatchCaseExpr>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        cases.Add(GetTraceEntryCaseForNextRoutine_LH(nextRoutine));
      }

      ExpressionBuilder bodyBuilder = new ExpressionBuilder(pgp.prog);

      var ls = AH.MakeNameSegment("ls", "L.Armada_TraceEntry");
      var entry = AH.MakeNameSegment("entry", "L.Armada_TraceEntry");
      var tid = AH.MakeExprDotName(entry, "tid", "L.Armada_ThreadHandle");

      var locv = AH.MakeApply2("L.Armada_GetThreadLocalView", ls, tid, "L.Armada_SharedMemory");
      var threads = AH.MakeExprDotName(ls, "threads", "map<Armada_ThreadHandle, Armada_Thread>");
      var t = AH.MakeSeqSelectExpr(threads, tid, "L.Armada_Thread");
      // var t = AH.ParseExpression(pgp.prog, "", "ls.threads[tid]");

      locv = bodyBuilder.AddVariableDeclaration("locv", locv);
      t = bodyBuilder.AddVariableDeclaration("t", t);

      var source = AH.MakeNameSegment("entry", "L.Armada_TraceEntry");
      var body = AH.MakeMatchExpr(source, cases, "H.Armada_TraceEntry");
      bodyBuilder.SetBody(body);

      var formals = new List<Formal> { AH.MakeFormal ("ls", "LState"), AH.MakeFormal("entry", "L.Armada_TraceEntry") };
      var validTraceEntryPredicate = AH.MakeApply2("L.Armada_ValidStep", ls, entry, new BoolType());

      var fn = AH.MakeFunctionWithReq("ConvertTraceEntry_LH", formals, validTraceEntryPredicate, bodyBuilder.Extract());
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    private void GenerateStepRefiner()
    {
      var str = @"
        predicate ValidStepSequence(ls: LState, lsteps: seq<L.Armada_TraceEntry>)
          decreases |lsteps|
        {
          if |lsteps| == 0 then
            true
          else
            var ls' := L.Armada_GetNextStateAlways(ls, lsteps[0]); L.Armada_ValidStep(ls, lsteps[0]) && ValidStepSequence(ls', lsteps[1..])
        }
      ";
      pgp.AddPredicate(str);

      str = @"
        function ConvertStepSequence_LH(ls: LState, lsteps: seq<L.Armada_TraceEntry>): seq<H.Armada_TraceEntry>
          requires ValidStepSequence(ls, lsteps)
          decreases |lsteps|
        {
          if |lsteps| == 0 then
            []
          else
            var ls' := L.Armada_GetNextStateAlways(ls, lsteps[0]); [ConvertTraceEntry_LH(ls, lsteps[0])] + ConvertStepSequence_LH(ls', lsteps[1..])
        }
      ";
      pgp.AddFunction(str);

      str = @"  
        function StepRefiner(lps: LPlusState, entry: LStep): HStep
          requires ValidStepSequence(lps.s, entry.steps)
        {
          Armada_Multistep(ConvertStepSequence_LH(lps.s, entry.steps), entry.tid, entry.tau)
        }
      ";
      pgp.AddFunction(str);
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }
      GetWeakenedPCSet();
      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofHeader();
      GenerateStarWeakeningRequest();
      GenerateStateAbstractionFunctions_LH();
      GeneratePCFunctions_L();
      foreach (var globalVarName in strategy.GlobalVars)
      {
        GenerateNoStoreBufferEntriesLemmas(globalVarName);
      }
      GenerateConvertTraceEntry_LH();
      GenerateStepRefiner();
      GenerateLocalViewCommutativityLemmas();
      GenerateLiftNextLemmas();
      GenerateAllActionsLiftableWeakenedLemmas();
      GenerateInitStatesEquivalentLemma();
      GenerateIsInvariantPredicateLemma();
      GenerateFinalProof();
    }

    private void GetWeakenedPCSet()
    {
      foreach (var lbl in strategy.Labels) {
        var pc = pgp.symbolsLow.GetPCForMethodAndLabel(lbl.val);
        if (pc == null) {
          AH.PrintError(pgp.prog, $"Specified non-existent label {lbl.val} in star-weakening strategy description.  Remember to prefix label names with the method name and an underscore, e.g., use main_lb1 if you have label lb1: in method main.");
        }
        else {
          weakenedPCs.Add(pc);
        }
      }
    }

    private bool LhsEquivalentAcrossConvert(Expression a, Expression b) {
      /*
      if (a is NameSegment) {
        return (b is NameSegment) && ((NameSegment)a).Name == ((NameSegment)b).Name;
      }
      */
      return Printer.ExprToString(a) == Printer.ExprToString(b);
    }

    protected MatchCaseExpr GetTraceEntryCaseForUpdateToSomehowNextRoutine_LH(NextRoutine nextRoutine) {
      var highNextRoutine = nextRoutineMap[nextRoutine];
      var lowStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
      var lowExprs = lowStmt.Lhss;

      var highStmt = (SomehowStmt)highNextRoutine.armadaStatement.Stmt;
      var highExprs = highStmt.Mod.Expressions;

      var pi = GetMatchingLowLevelLhssForHighLevelLhss(lowExprs, highExprs);

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      ps.AddRange(nextRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType))); // Use the tid (and any other) parameters from the bound vars in the case statement

      for (int i = 0; i < highExprs.Count; i++) {
        var context = new NormalResolutionContext(nextRoutine, pgp.symbolsLow);
        // Add the pi[i]'th rhs from the low-level update statement
        var rhs = lowStmt.Rhss.ElementAt(pi[i]);
        Expression newRhs;
        if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = context.ResolveAsRValue(erhs.Expr);
          newRhs = newRhsRValue.Val;
        }
        else {
          AH.PrintError(pgp.prog, "Havoc RHS not yet supported");
          return null;
        }
        
        ps.Add(newRhs);
      }

      string nextRoutineName = nextRoutine.NameSuffix;
      string hname = nextRoutineMap[nextRoutine].NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected List<int> GetMatchingLowLevelLhssForHighLevelLhss(List<Expression> lowLhss, List<Expression> highLhss)
    {
      var pi = new List<int>();
      for (int i = 0; i < highLhss.Count; i++) {
        int pi_i = -1;
        for (int j = 0; j < lowLhss.Count; j++) {
          // Want to find the last lowExpr that matches; this handles `x, x := 1, 2` to `x := *` correctly
          if(LhsEquivalentAcrossConvert(highLhss[i], lowLhss[j])) {
            pi_i = j;
          }
        }
        if (pi_i == -1) {
          AH.PrintError(pgp.prog, $"Unable to find matching LHS for {Printer.ExprToString(highLhss[i])}");
        }
        pi.Add(pi_i);
      }
      return pi;
    }

    protected MatchCaseExpr GetTraceEntryCaseForUpdateToUpdateNextRoutine_LH(NextRoutine nextRoutine) {
      var highNextRoutine = nextRoutineMap[nextRoutine];
      var lowStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
      var lowExprs = lowStmt.Lhss;

      var highStmt = (UpdateStmt)highNextRoutine.armadaStatement.Stmt;
      var highExprs = highStmt.Lhss;

      var pi = GetMatchingLowLevelLhssForHighLevelLhss(lowExprs, highExprs);

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      // ps.AddRange(nextRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType))); // Use the tid (and any other) parameters from the bound vars in the case statement

      for (int i = 0; i < highExprs.Count; i++) {
        var context = new NormalResolutionContext(nextRoutine, pgp.symbolsLow);
        // Add the pi[i]'th rhs from the low-level update statement
        var rhs = lowStmt.Rhss.ElementAt(pi[i]);
        Expression newRhs;
        if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = context.ResolveAsRValue(erhs.Expr);
          newRhs = newRhsRValue.Val;
        }
        else { // rhs must be HavocRhs here
          newRhs = AH.MakeNameSegment($"nondet{i}", lowExprs[pi[i]].Type);
        }
        if (highStmt.Rhss.ElementAt(i) is HavocRhs) { // If the high level is a havoc-rhs, then it needs to be given the values
          ps.Add(newRhs);
        }
      }

      string nextRoutineName = nextRoutine.NameSuffix;
      string hname = nextRoutineMap[nextRoutine].NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected MatchCaseExpr GetTraceEntryCaseForIfToIfNextRoutine_LH(NextRoutine nextRoutine) {
      var highNextRoutine = nextRoutineMap[nextRoutine];
      var lowStmt = (IfStmt)nextRoutine.armadaStatement.Stmt;
      var highStmt = (IfStmt)highNextRoutine.armadaStatement.Stmt;

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      string nextRoutineName = nextRoutine.NameSuffix;
      string hname = nextRoutineMap[nextRoutine].NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected override MatchCaseExpr GetTraceEntryCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      var highNextRoutine = nextRoutineMap[nextRoutine];

      if (highNextRoutine.nextType == NextType.Update
            && nextRoutine.nextType == NextType.Update) {
        // e.g.  low-level: v_1 := e_1;
        //      high-level: v_1 := *
        //
        // Also low-level: v_1 ::= e_1;
        //      high-level: v_1 ::= *
        return GetTraceEntryCaseForUpdateToUpdateNextRoutine_LH(nextRoutine);
      }
      else if ((highNextRoutine.nextType == NextType.IfTrue || highNextRoutine.nextType == NextType.IfFalse)
               && (nextRoutine.nextType == NextType.IfTrue || nextRoutine.nextType == NextType.IfFalse)) {
        // e.g.  low-level: if p {}
        //      high-level: if * {}
        return GetTraceEntryCaseForIfToIfNextRoutine_LH(nextRoutine);
      }
      else if (highNextRoutine.nextType == NextType.Somehow
            && nextRoutine.nextType == NextType.Update) {
        // low-level: v_1, ..., v_n ::= e_1, ..., e_n;
        // high-level: for some permutation pi \in S_n,
        // somehow modifies v_{pi_1}
        //         ...
        //         modifies v_{pi_n}
        //
        // In order for star weakening to be possible, it is necessary for a permutation as above to exist.
        // This can be made part of CheckEquivalence
        //
        // Then, the low level step of NextStep()
        // newval{j} is the non-det variable that holds the new value of v_{pi_j}. So,
        // the j'th value in the list of hstep params given in the constructor called by 
        // ConvertTraceEntry_LH should be e_{pi_j}.
        return GetTraceEntryCaseForUpdateToSomehowNextRoutine_LH(nextRoutine);
      }
      else if (highNextRoutine.nextType == nextRoutine.nextType) {
        return GetTraceEntryCaseForNormalNextRoutine_LH(nextRoutine);
      }
      AH.PrintError(pgp.prog, "Invalid statement for weakening.");
      return null;
    }

    protected override MatchCaseExpr GetTraceEntryCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      var highNextRoutine = nextRoutineMap[nextRoutine];
      string nextRoutineName = nextRoutine.NameSuffix;

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      ps.AddRange(highNextRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType)));

      string hname = nextRoutineMap[nextRoutine].NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    private void GenerateIsInvariantPredicateLemma()
    {
      // var inv = new VarHidingRequestInvariantInfo();
      // AddInvariant(inv);
      GenerateInvariantProof(pgp);
    }

    private void GenerateStarWeakeningRequest()
    {
      var lplusstate = AH.ReferToType("LPlusState");
      var hstate = AH.ReferToType("HState");
      var lstep = AH.ReferToType("LStep");
      var hstep = AH.ReferToType("HStep");
      var wrequest = AH.MakeGenericTypeSpecific("StarWeakeningRequest", new List<Type>{ lplusstate, hstate, lstep, hstep });
      pgp.MainProof.AddTypeSynonymDecl("WRequest", wrequest);

      var str = @"
      function GetStarWeakeningRequest(): WRequest
      {
        StarWeakeningRequest(GetLPlusSpec(), GetHSpec(), GetLPlusHRefinementRelation(), iset lps : LPlusState | InductiveInv(lps) :: lps, ConvertTotalState_LPlusH, StepRefiner)
      }
      ";
      pgp.AddFunction(str);
    }

    protected override void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      
      var nextRoutineName = nextRoutine.NameSuffix;

      NextRoutine highNextRoutine = nextRoutineMap[nextRoutine];
      string highNextRoutineName = highNextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lentry.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", highNextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      bool needIsValidStepLemma = false;

      if (nextRoutine.stmt != null && nextRoutine.pc != null && weakenedPCs.Contains(nextRoutine.pc)) {
        needIsValidStepLemma = true;
        GenerateConvertImpliesValidStepLemma(nextRoutine);
      }

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(wr: WRequest, lps: LPlusState, lps':LPlusState, lentry: L.Armada_TraceEntry)
          requires wr == GetStarWeakeningRequest()
          requires LPlus_NextOneStep(lps, lps', lentry)
          requires lentry.Armada_TraceEntry_{nextRoutineName}?
          requires lps in wr.inv
          ensures H.Armada_NextOneStep(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), ConvertTraceEntry_LH(lps.s, lentry))
        {{
          var hs := wr.converter(lps);
          var hs' := wr.converter(lps');
          var tid := lentry.tid;
          var hstep := ConvertTraceEntry_LH(lps.s, lentry);
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          { (needIsValidStepLemma ? $@"lemma_TraceEntry_{nextRoutineName}_ImpliesConvertedIsValidStep(wr, lps, lps', lentry, hstep);" : "" )}
          assert H.Armada_ValidStep_{highNextRoutineName}(hs, tid{hstep_params});
          if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(lps.s, tid{lstep_params}) {{
            assert H.Armada_UndefinedBehaviorAvoidance_{highNextRoutineName}(hs, tid{hstep_params});
            var alt_hs' := H.Armada_GetNextState_{highNextRoutineName}(hs, tid{hstep_params});
            assert hs'.stop_reason == alt_hs'.stop_reason;
            if tid in hs'.threads {{
              assert hs'.threads[tid] == alt_hs'.threads[tid];
            }}
            assert hs'.threads == alt_hs'.threads;
            assert hs'.mem == alt_hs'.mem;
            assert hs' == alt_hs';
            assert H.Armada_Next_{highNextRoutineName}(hs, hs', tid{hstep_params});
          }} else {{
            assert !H.Armada_UndefinedBehaviorAvoidance_{highNextRoutineName}(hs, tid{hstep_params});
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateLiftStepLemmaForTauNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      NextRoutine highNextRoutine = nextRoutineMap[nextRoutine];
      string highNextRoutineName = highNextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", highNextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(wr:WRequest, lps:LPlusState, lps':LPlusState, lstep:L.Armada_TraceEntry)
          requires wr == GetStarWeakeningRequest()
          requires LPlus_NextOneStep(lps, lps', lstep)
          requires lstep.Armada_TraceEntry_{nextRoutineName}?
          requires lps in wr.inv
          ensures H.Armada_NextOneStep(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), ConvertTraceEntry_LH(lps.s, lstep))
        {{
            var hs := wr.converter(lps);
            var hs' := wr.converter(lps');
            var tid := lstep.tid;
            var hstep := ConvertTraceEntry_LH(lps.s, lstep);

            var lentry := lps.s.threads[tid].storeBuffer[0];
            assert H.Armada_ValidStep_{highNextRoutineName}(hs, tid{hstep_params});
            assert H.Armada_UndefinedBehaviorAvoidance_{highNextRoutineName}(hs, tid{hstep_params});
            var hentry := hs.threads[tid].storeBuffer[0];
            var lmem := lps.s.mem;
            var hmem1 := ConvertSharedMemory_LH(L.Armada_ApplyStoreBufferEntry(lmem, lentry));
            var hmem2 := H.Armada_ApplyStoreBufferEntry(ConvertSharedMemory_LH(lmem), hentry);
            lemma_ApplyStoreBufferEntryCommutesWithConvert(lmem, lentry, hentry, hmem1, hmem2);

            var alt_hs' := H.Armada_GetNextState_{highNextRoutineName}(hs, tid{hstep_params});
            assert hmem1 == hmem2;
            assert hs'.threads[tid].storeBuffer == alt_hs'.threads[tid].storeBuffer;
            assert hs'.threads[tid] == alt_hs'.threads[tid];
            assert hs'.threads == alt_hs'.threads;
            assert hs' == alt_hs';
            assert H.Armada_Next_{highNextRoutineName}(hs, hs', tid{hstep_params});
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateConvertImpliesValidStepLemma(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      NextRoutine highNextRoutine = nextRoutineMap[nextRoutine];
      string highNextRoutineName = highNextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lentry.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", highNextRoutine.Formals.Select(f => $", hentry.{f.GloballyUniqueVarName}"));

      string body = "";
      foreach (var globalVarName in strategy.GlobalVars) {
        body += $@"
          DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_AlwaysMatchesGlobalView();
        ";
      }

      var str = $@"
        lemma lemma_TraceEntry_{nextRoutineName}_ImpliesConvertedIsValidStep(wr: WRequest, lps: LPlusState, lps': LPlusState, lentry: L.Armada_TraceEntry, hentry: H.Armada_TraceEntry)
          requires wr == GetStarWeakeningRequest()
          requires LPlus_NextOneStep(lps, lps', lentry)
          requires lentry.Armada_TraceEntry_{nextRoutineName}?
          requires lps in wr.inv
          requires hentry == ConvertTraceEntry_LH(lps.s, lentry);
          ensures H.Armada_ValidStep_{highNextRoutineName}(ConvertTotalState_LPlusH(lps), lentry.tid{hstep_params});
        {{
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          {body}
        }}
      ";
      pgp.AddLemma(str);

    }

    private void GenerateNoStoreBufferEntriesLemmas(string globalVarName)
    {
      var str =$@"
        predicate H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs: HState)
        {{
          forall storeBufferEntry, tid :: tid in hs.threads && storeBufferEntry in hs.threads[tid].storeBuffer && storeBufferEntry.loc.Armada_StoreBufferLocation_Unaddressable?
            ==> storeBufferEntry.loc.v != H.Armada_GlobalStaticVar_{globalVarName}
        }}
      ";
      pgp.AddPredicate(str, "invariants");

      
      str =$@"
        predicate L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(lps: LPlusState)
        {{
          forall storeBufferEntry, tid :: tid in lps.s.threads && storeBufferEntry in lps.s.threads[tid].storeBuffer && storeBufferEntry.loc.Armada_StoreBufferLocation_Unaddressable?
            ==> storeBufferEntry.loc.v != L.Armada_GlobalStaticVar_{globalVarName}
        }}
      ";
      pgp.AddPredicate(str, "invariants");
      AddInvariant(new InternalInvariantInfo($@"GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer", $@"L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer", new List<string>()));

      str = $@"
        lemma DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(mem: H.Armada_SharedMemory, storeBuffer: seq<H.Armada_StoreBufferEntry>)
          requires forall storeBufferEntry :: storeBufferEntry in storeBuffer && storeBufferEntry.loc.Armada_StoreBufferLocation_Unaddressable?
          ==> storeBufferEntry.loc.v != H.Armada_GlobalStaticVar_{globalVarName}
          ensures H.Armada_ApplyStoreBuffer(mem, storeBuffer).globals.{globalVarName} == mem.globals.{globalVarName}
          decreases |storeBuffer|
        {{
          if |storeBuffer| == 0 {{
          }}
          else {{
            var mem' := H.Armada_ApplyStoreBufferEntry(mem, storeBuffer[0]);
            assert mem'.globals.{globalVarName} == mem.globals.{globalVarName};
            DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(mem, storeBuffer[1..]);
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_MatchesGlobalView(hs: HState, tid: Armada_ThreadHandle)
          requires tid in hs.threads
          requires H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs)
          ensures hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
        {{
          DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(hs.mem, hs.threads[tid].storeBuffer);
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_AlwaysMatchesGlobalView()
        ensures forall hs, tid :: H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs) && tid in hs.threads ==> hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
        {{
          forall hs, tid |
            H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs) && tid in hs.threads
            ensures hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
            {{
              DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_MatchesGlobalView(hs, tid);
            }}
        }}
      ";
      pgp.AddLemma(str);


      str = $@"
        lemma Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer_LPlusImpliesH(lps: LPlusState, hs: HState)
          requires L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(lps)
          requires hs == ConvertTotalState_LPlusH(lps)
          ensures H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs)
        {{
        }}
      ";
      pgp.AddLemma(str);

    }

    private void GenerateLiftNextLemmas()
    {
      var finalCases = "";
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.nextType == NextType.Tau) {
          GenerateLiftStepLemmaForTauNextRoutine(nextRoutine);
        }
        else {
          GenerateLiftStepLemmaForNormalNextRoutine(nextRoutine);
        }
        var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        var nextRoutineName = nextRoutine.NameSuffix;
        finalCases += $"case Armada_TraceEntry_{nextRoutineName}(_{lstep_params}) => lemma_LiftNext_{nextRoutineName}(wr, lps, lps', lentry);";
      }
      string str =$@"
        lemma lemma_LNextOneImpliesHNextOne(wr: WRequest, lps:LPlusState, lps':LPlusState, hs:HState, hs':HState,
          lentry: L.Armada_TraceEntry, hentry: H.Armada_TraceEntry)
          requires wr == GetStarWeakeningRequest()
          requires lps in wr.inv
          requires LPlus_NextOneStep(lps, lps', lentry)
          requires hs == ConvertTotalState_LPlusH(lps)
          requires hs' == ConvertTotalState_LPlusH(lps')
          requires hentry == ConvertTraceEntry_LH(lps.s, lentry)
          ensures H.Armada_NextOneStep(hs, hs', hentry)
        {{
          match lentry {{
            {finalCases}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateAllActionsLiftableWeakenedLemmas()
    {
      string str = @"  
        lemma lemma_NextMultipleStepsImpliesValidStepSequence(lps: LPlusState, lps': LPlusState, steps: seq<L.Armada_TraceEntry>)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lps, lps', steps)
          ensures ValidStepSequence(lps.s, steps)
          decreases |steps|
        {
          if |steps| == 0 {
          } else {
            assert L.Armada_ValidStep(lps.s, steps[0]);
            assert Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), LPlus_GetNextStateAlways(lps, steps[0]), lps', steps[1..]);
            lemma_NextMultipleStepsImpliesValidStepSequence(LPlus_GetNextStateAlways(lps, steps[0]), lps', steps[1..]);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LNextMultipleImpliesHNextMultiple(wr: WRequest, lps: LPlusState, lps': LPlusState, steps: seq<L.Armada_TraceEntry>)
          requires wr == GetStarWeakeningRequest()
          requires lps in wr.inv
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lps, lps', steps)
          ensures ValidStepSequence(lps.s, steps) && Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), ConvertStepSequence_LH(lps.s, steps))
          decreases |steps|
        {
          if |steps| == 0 {
            return;
          }
          var lps_next := LPlus_GetNextStateAlways(lps, steps[0]);
          var hs, hs_next, hs' := ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps_next), ConvertTotalState_LPlusH(lps');
          lemma_NextMultipleStepsImpliesValidStepSequence(lps, lps', steps);
          var hsteps := ConvertStepSequence_LH(lps.s, steps);
          lemma_NextOneStepMaintainsInductiveInv(lps, lps_next, steps[0]);
          assert lps_next in wr.inv;
          lemma_LNextMultipleImpliesHNextMultiple(wr, lps_next, lps', steps[1..]);
          lemma_LNextOneImpliesHNextOne(wr, lps, lps_next, hs, hs_next, steps[0], hsteps[0]);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_GetStateSequenceCommutesWithConvert(wr: WRequest, lps: LPlusState, lpstates: seq<LPlusState>, hs: HState, hstates: seq<HState>, lsteps:seq<L.Armada_TraceEntry>, hsteps:seq<H.Armada_TraceEntry>)
          requires wr == GetStarWeakeningRequest()
          requires lps in wr.inv
          requires ValidStepSequence(lps.s, lsteps) && hsteps == ConvertStepSequence_LH(lps.s, lsteps)
          requires hs == ConvertTotalState_LPlusH(lps)
          requires lpstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lps, lsteps)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps)
          ensures Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps) == MapSeqToSeq(Armada_GetStateSequence(LPlus_GetSpecFunctions(), lps, lsteps), ConvertTotalState_LPlusH)
          decreases |lsteps|
        {
          if |lsteps| == 0 {
          }
          else {
            var lps_next, hs_next := lpstates[1], hstates[1];
            assert LPlus_NextOneStep(lps, lps_next, lsteps[0]);
            lemma_NextOneStepMaintainsInductiveInv(lps, lps_next, lsteps[0]);
            assert lps_next in wr.inv;
            lemma_LNextOneImpliesHNextOne(wr, lps, lps_next, hs, ConvertTotalState_LPlusH(lps_next), lsteps[0], hsteps[0]);
            assert hstates[1] == ConvertTotalState_LPlusH(lpstates[1]); 
            lemma_GetStateSequenceCommutesWithConvert(wr, lps_next, lpstates[1..], hs_next, hstates[1..], lsteps[1..], hsteps[1..]);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_IntermediateStatesNonyielding(wr: WRequest, lps: LPlusState, lps': LPlusState, hs: HState, hs': HState, lsteps: seq<L.Armada_TraceEntry>, hsteps: seq<H.Armada_TraceEntry>, tid: Armada_ThreadHandle, tau: bool, lpstates: seq<LPlusState>, hstates: seq<HState>)
          requires wr == GetStarWeakeningRequest()
          requires lps in wr.inv
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), lps, lps', lsteps)
          requires tid in lps.s.threads ==> !L.Armada_IsNonyieldingPC(lps.s.threads[tid].pc)
          requires tid in lps'.s.threads ==> !L.Armada_IsNonyieldingPC(lps'.s.threads[tid].pc)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires forall step :: step in lsteps ==> step.Armada_TraceEntry_Tau? == tau
          requires lpstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), lps, lsteps)
          requires forall i :: 0 < i < |lsteps| ==> tid in lpstates[i].s.threads && L.Armada_IsNonyieldingPC(lpstates[i].s.threads[tid].pc)
          requires hs == ConvertTotalState_LPlusH(lps)
          requires hs' == ConvertTotalState_LPlusH(lps')
          requires ValidStepSequence(lps.s, lsteps)
          requires hsteps ==  ConvertStepSequence_LH(lps.s, lsteps)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          requires forall step :: step in hsteps ==> step.tid == tid
          requires forall step :: step in hsteps ==> step.Armada_TraceEntry_Tau? == tau
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps);
          ensures  forall i :: 0 < i < |hsteps| ==> tid in hstates[i].threads && H.Armada_IsNonyieldingPC(hstates[i].threads[tid].pc)
          ensures tid in hs'.threads ==> !H.Armada_IsNonyieldingPC(hs'.threads[tid].pc)
        {
          lemma_GetStateSequenceCommutesWithConvert(wr, lps, Armada_GetStateSequence(LPlus_GetSpecFunctions(), lps, lsteps), hs, Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps), lsteps, hsteps);
          forall i | 0 < i < |hsteps|
            ensures tid in hstates[i].threads
            ensures H.Armada_IsNonyieldingPC(hstates[i].threads[tid].pc)
          {
            assert tid in lpstates[i].s.threads;
            assert L.Armada_IsNonyieldingPC(lpstates[i].s.threads[tid].pc);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertStepSequenceMaintainsMatching(s: LState, tau: bool, tid: Armada_ThreadHandle, steps: seq<L.Armada_TraceEntry>)
          requires ValidStepSequence(s, steps)
          requires forall step :: step in steps ==> step.tid == tid
          requires forall step :: step in steps ==> step.Armada_TraceEntry_Tau? == tau
          ensures forall step :: step in ConvertStepSequence_LH(s, steps) ==> step.tid == tid
          ensures forall step :: step in ConvertStepSequence_LH(s, steps) ==> step.Armada_TraceEntry_Tau? == tau
          decreases |steps|
        {
          if |steps| > 0 {
            var s' := L.Armada_GetNextStateAlways(s, steps[0]);
            lemma_ConvertStepSequenceMaintainsMatching(s', tau, tid, steps[1..]);
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
          lemma lemma_LNextImpliesHNext(wr: WRequest, lps: LPlusState, lps': LPlusState, lstep: LStep)
          requires wr == GetStarWeakeningRequest()
          requires LPlus_Next(lps, lps', lstep)
          requires lps in wr.inv
          ensures ValidStepSequence(lps.s, lstep.steps)
          ensures H.Armada_Next(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), StepRefiner(lps, lstep))
        {
          var hs, hs' := ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps');
          lemma_NextMultipleStepsImpliesValidStepSequence(lps, lps', lstep.steps);
          var hstep := StepRefiner(lps, lstep);
          lemma_LNextMultipleImpliesHNextMultiple(wr, lps, lps', lstep.steps);
          assert Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), hstep.steps);
          assert hstep.tid in hs.threads ==> !H.Armada_IsNonyieldingPC(hs.threads[hstep.tid].pc);
          assert hstep.tid in hs'.threads ==> !H.Armada_IsNonyieldingPC(hs'.threads[hstep.tid].pc);
          var states := Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hstep.steps);
          assert forall step :: step in lstep.steps ==> step.Armada_TraceEntry_Tau? == lstep.tau;
          lemma_ConvertStepSequenceMaintainsMatching(lps.s, lstep.tau, lstep.tid, lstep.steps);
          var hstates := Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hstep.steps);
          lemma_IntermediateStatesNonyielding(wr, lps, lps', hs, hs', lstep.steps, hstep.steps, lstep.tid, lstep.tau, Armada_GetStateSequence(LPlus_GetSpecFunctions(), lps, lstep.steps), hstates);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AllActionsLiftableWeakened()
          ensures AllActionsLiftableStarWeakened(GetStarWeakeningRequest())
        {
          var wr := GetStarWeakeningRequest();

          forall lps, lps', lstep |
            && ActionTuple(lps, lps', lstep) in wr.lspec.next
            && lps in wr.inv
            ensures ActionTuple(wr.converter(lps), wr.converter(lps'), wr.step_refiner(lps, lstep)) in wr.hspec.next
            ensures StepRefiner.requires(lps, lstep);
          {
            lemma_LNextImpliesHNext(wr, lps, lps', lstep);
            lemma_NextMultipleStepsImpliesValidStepSequence(lps, lps', lstep.steps);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateInitStatesEquivalentLemma()
    {
      string str = @"
        lemma lemma_LInitImpliesHInit(lps:LPlusState, hs:HState, hconf:H.Armada_Config)
          requires LPlus_Init(lps)
          requires hs == ConvertTotalState_LPlusH(lps)
          requires hconf == ConvertConfig_LH(lps.config)
          ensures H.Armada_InitConfig(hs, hconf)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
         lemma lemma_InitStatesEquivalent(wr:WRequest)
          requires wr == GetStarWeakeningRequest()
          ensures InitStatesEquivalent(wr)
        {
          forall initial_lps | initial_lps in wr.lspec.init
            ensures wr.converter(initial_lps) in wr.hspec.init
          {
            lemma_LInitImpliesHInit(initial_lps, ConvertTotalState_LPlusH(initial_lps), ConvertConfig_LH(initial_lps.config));
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str = @"
        lemma lemma_ProveRefinementViaWeakening()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var lspec := L.Armada_Spec();
          var hspec := H.Armada_Spec();
          var wr := GetStarWeakeningRequest();
          
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);

            lemma_InitStatesEquivalent(wr);
            lemma_AllActionsLiftableWeakened();
            lemma_InductiveInvIsInvariant();
            
            assert ValidStarWeakeningRequest(wr);
            var ahb := lemma_PerformStarWeakening(wr, alb);
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
