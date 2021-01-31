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
      : base(i_pgp, true)
    {
      strategy = i_strategy;
      weakenedPCs = new HashSet<ArmadaPC>();
    }

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();
      
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

    protected override void GenerateConvertStep_LH()
    {
      var cases = new List<string>();

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        cases.Add(GetStepCaseForNextRoutine_LH(nextRoutine));
      }

      var fn = $@"
        function ConvertStep_LH(ls: LPlusState, step: L.Armada_Step, tid: Armada_ThreadHandle) : H.Armada_Step
          requires L.Armada_ValidStep(ls.s, step, tid)
        {{
          reveal L.Armada_ValidStepCases();
          var locv := L.Armada_GetThreadLocalView(ls.s, tid);
          var t := ls.s.threads[tid];
          match step
            {String.Concat(cases)}
        }}
      ";
      pgp.AddFunction(fn, "convert");
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
      GenerateAtomicSpecs();
      GenerateStateAbstractionFunctions_LH();
      GeneratePCFunctions_L();
      foreach (var globalVarName in strategy.GlobalVars)
      {
        GenerateNoStoreBufferEntriesLemmas(globalVarName);
      }
      GenerateConvertStep_LH();
      GenerateAllConvertImpliesValidStepLemmas();
      GenerateConvertAtomicPath_LH();
      GenerateLocalViewCommutativityLemmas();
      GenerateInvariantProof(pgp);
      GenerateEstablishInitRequirementsLemma();
      GenerateEstablishStateOKRequirementLemma();
      GenerateEstablishRelationRequirementLemma();
      GenerateLiftingRelation();
      GenerateLiftAtomicPathLemmas();
      GenerateEstablishAtomicPathLiftableLemma();
      GenerateEstablishAtomicPathsLiftableLemma(false, false);
      GenerateLiftLAtomicToHAtomicLemma(false, false);
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

    protected string GetStepCaseForUpdateToSomehowNextRoutine_LH(NextRoutine nextRoutine)
    {
      var hNextRoutine = nextRoutineMap[nextRoutine];
      var lowStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
      var lowExprs = lowStmt.Lhss;

      var hStmt = (SomehowStmt)hNextRoutine.armadaStatement.Stmt;
      var hExprs = hStmt.Mod.Expressions;

      var pi = GetMatchingLowLevelLhssForHighLevelLhss(lowExprs, hExprs);
      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      var ps = nextRoutine.Formals.Select(f => $"params{f.LocalVarName}").ToList();

      for (int i = 0; i < hExprs.Count; i++) {
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new NormalResolutionContext("L", nextRoutine.method.Name, pgp.symbolsLow, failureReporter);
        // Add the pi[i]'th rhs from the low-level update statement
        var rhs = lowStmt.Rhss.ElementAt(pi[i]);
        if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = context.ResolveAsRValue(erhs.Expr);
          ps.Add(newRhsRValue.Val);
        }
        else {
          AH.PrintError(pgp.prog, "Havoc RHS not yet supported");
          return null;
        }
      }

      string hname = hNextRoutine.NameSuffix;
      var caseBody = hNextRoutine.HasFormals ? $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))"
                                               : $"H.Armada_Step_{hname}";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => {caseBody}\n";
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

    protected string GetStepCaseForUpdateToUpdateNextRoutine_LH(NextRoutine nextRoutine)
    {
      var hNextRoutine = nextRoutineMap[nextRoutine];
      var lowStmt = (UpdateStmt)nextRoutine.armadaStatement.Stmt;
      var lowExprs = lowStmt.Lhss;

      var hStmt = (UpdateStmt)hNextRoutine.armadaStatement.Stmt;
      var hExprs = hStmt.Lhss;

      var pi = GetMatchingLowLevelLhssForHighLevelLhss(lowExprs, hExprs);
      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      var ps = new List<string>();

      for (int i = 0; i < hExprs.Count; i++) {
        var failureReporter = new SimpleFailureReporter(pgp.prog);
        var context = new NormalResolutionContext("L", nextRoutine.method.Name, pgp.symbolsLow, failureReporter);
        // Add the pi[i]'th rhs from the low-level update statement
        var rhs = lowStmt.Rhss.ElementAt(pi[i]);
        string newRhs;
        if (rhs is ExprRhs) {
          var erhs = (ExprRhs)rhs;
          var newRhsRValue = context.ResolveAsRValue(erhs.Expr);
          newRhs = newRhsRValue.Val;
        }
        else { // rhs must be HavocRhs here
          newRhs = $"params.nondet{i}";
        }
        if (hStmt.Rhss.ElementAt(i) is HavocRhs) { // If the high level is a havoc-rhs, then it needs to be given the values
          ps.Add(newRhs);
        }
      }

      string hname = hNextRoutine.NameSuffix;
      var caseBody = hNextRoutine.HasFormals ? $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))"
                                               : $"H.Armada_Step_{hname}";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => {caseBody}\n";
    }

    protected string GetStepCaseForIfToIfNextRoutine_LH(NextRoutine nextRoutine)
    {
      string hname = nextRoutineMap[nextRoutine].NameSuffix;
      return $"case Armada_Step_{nextRoutine.NameSuffix}() => H.Armada_Step_{hname}\n";
    }

    protected override string GetStepCaseForNextRoutine_LH(NextRoutine nextRoutine)
    {
      var hNextRoutine = LiftNextRoutine(nextRoutine);

      if (hNextRoutine == null) {
        return GetStepCaseForSuppressedNextRoutine_LH(nextRoutine);
      }

      if (hNextRoutine.nextType == NextType.Update
            && nextRoutine.nextType == NextType.Update) {
        // e.g.  low-level: v_1 := e_1;
        //      high-level: v_1 := *
        //
        // Also low-level: v_1 ::= e_1;
        //      high-level: v_1 ::= *
        return GetStepCaseForUpdateToUpdateNextRoutine_LH(nextRoutine);
      }
      else if ((hNextRoutine.nextType == NextType.IfTrue || hNextRoutine.nextType == NextType.IfFalse)
               && (nextRoutine.nextType == NextType.IfTrue || nextRoutine.nextType == NextType.IfFalse)) {
        // e.g.  low-level: if p {}
        //      high-level: if * {}
        return GetStepCaseForIfToIfNextRoutine_LH(nextRoutine);
      }
      else if (hNextRoutine.nextType == NextType.Somehow
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
        // ConvertStep_LH should be e_{pi_j}.
        return GetStepCaseForUpdateToSomehowNextRoutine_LH(nextRoutine);
      }
      else if (hNextRoutine.nextType == nextRoutine.nextType) {
        return GetStepCaseForNormalNextRoutine_LH(nextRoutine);
      }
      AH.PrintError(pgp.prog, "Invalid statement for weakening.");
      return null;
    }

    protected override string GetStepCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      var bvs = nextRoutine.HasFormals ? $"params: L.Armada_StepParams_{nextRoutine.NameSuffix}" : "";
      var ps = nextRoutine.Formals.Select(f => $"params.{f.LocalVarName}");

      var hNextRoutine = nextRoutineMap[nextRoutine];
      string hname = hNextRoutine.NameSuffix;
      var caseBody = hNextRoutine.HasFormals ? $"H.Armada_Step_{hname}(H.Armada_StepParams_{hname}({AH.CombineStringsWithCommas(ps)}))"
                                             : $"H.Armada_Step_{hname}";
      return $"case Armada_Step_{nextRoutine.NameSuffix}({bvs}) => {caseBody}\n";
    }

    protected override void GenerateLiftAtomicPathLemmaForNormalPath(AtomicPath atomicPath, string typeComparison,
                                                                     string extraSignatureLines, string extraProof)
    {
      var isValidStepLemmaInvocations = String.Concat(atomicPath.NextRoutines
          .Where(nextRoutine => nextRoutine.stmt != null && nextRoutine.startPC != null && weakenedPCs.Contains(nextRoutine.startPC))
          .Select((nextRoutine, idx) => $@"
             lemma_Step_{nextRoutine.NameSuffix}_ImpliesConvertedIsValidStep(
               lstates.s{idx}, lstates.s{idx+1}, lsteps.step{idx}, hsteps.step{idx}, tid);
          "));
      base.GenerateLiftAtomicPathLemmaForNormalPath(atomicPath, typeComparison, extraSignatureLines,
                                                    extraProof + "\n" + isValidStepLemmaInvocations);
    }

    private void GenerateConvertImpliesValidStepLemma(NextRoutine nextRoutine)
    {
      NextRoutine hNextRoutine = nextRoutineMap[nextRoutine];
      string hNextRoutineName = hNextRoutine.NameSuffix;

      var hstep_params = String.Join("", hNextRoutine.Formals.Select(f => $", hentry.{f.GloballyUniqueVarName}"));

      var lpr = new ModuleStepPrinter("L");
      lpr.State = "ls.s";
      lpr.NextState = "ls'.s";
      lpr.Step = "lstep";
      var hpr = new ModuleStepPrinter("H");
      hpr.State = "hs";
      hpr.NextState = "hs'";
      hpr.Step = "hstep";

      var str = $@"
        lemma lemma_Step_{nextRoutine.NameSuffix}_ImpliesConvertedIsValidStep(
          ls: LPlusState,
          ls': LPlusState,
          lstep: L.Armada_Step,
          hstep: H.Armada_Step,
          tid: Armada_ThreadHandle
          )
          requires LPlus_ValidStep(ls, lstep, tid)
          requires ls' == LPlus_GetNextState(ls, lstep, tid)
          requires lstep.Armada_Step_{nextRoutine.NameSuffix}?
          requires InductiveInv(ls)
          requires hstep == ConvertStep_LH(ls, lstep, tid)
          ensures  H.Armada_ValidStep(ConvertTotalState_LPlusH(ls), hstep, tid)
        {{
          { lpr.GetOpenValidStepInvocation(nextRoutine) }
          var hs := ConvertTotalState_LPlusH(ls);
          var hs' := H.Armada_GetNextState(hs, hstep, tid);
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
      ";
      foreach (var globalVarName in strategy.GlobalVars) {
        str += $"lemma_DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_AlwaysMatchesGlobalView();\n";
      }
      str += hpr.GetOpenStepInvocation(hNextRoutine);
      str += "ProofCustomizationGoesHere(); }";
      pgp.AddLemma(str, "lift");
    }

    private void GenerateAllConvertImpliesValidStepLemmas()
    {
      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        if (nextRoutine.stmt != null && nextRoutine.startPC != null && weakenedPCs.Contains(nextRoutine.startPC)) {
          GenerateConvertImpliesValidStepLemma(nextRoutine);
        }
      }
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
      pgp.AddPredicate(str, "defs");

      
      str =$@"
        predicate L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(ls: LPlusState)
        {{
          forall storeBufferEntry, tid :: tid in ls.s.threads && storeBufferEntry in ls.s.threads[tid].storeBuffer && storeBufferEntry.loc.Armada_StoreBufferLocation_Unaddressable?
            ==> storeBufferEntry.loc.v != L.Armada_GlobalStaticVar_{globalVarName}
        }}
      ";
      pgp.AddPredicate(str, "defs");
      AddInvariant(new InternalInvariantInfo($@"GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer", $@"L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer", new List<string>()));

      str = $@"
        lemma lemma_DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(mem: H.Armada_SharedMemory, storeBuffer: seq<H.Armada_StoreBufferEntry>)
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
            lemma_DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(mem, storeBuffer[1..]);
          }}
        }}
      ";
      pgp.AddLemma(str, "utility");

      str = $@"
        lemma lemma_DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_MatchesGlobalView(hs: HState, tid: Armada_ThreadHandle)
          requires tid in hs.threads
          requires H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs)
          ensures hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
        {{
          lemma_DoesNotAppearInStoreBufferImplies_GlobalStaticVar_{globalVarName}_UnchangedByApplyStoreBuffer(hs.mem, hs.threads[tid].storeBuffer);
        }}
      ";
      pgp.AddLemma(str, "utility");

      str = $@"
        lemma lemma_DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_AlwaysMatchesGlobalView()
        ensures forall hs, tid :: H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs) && tid in hs.threads ==> hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
        {{
          forall hs, tid |
            H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs) && tid in hs.threads
            ensures hs.mem.globals.{globalVarName} == H.Armada_GetThreadLocalView(hs, tid).globals.{globalVarName}
            {{
              lemma_DoesNotAppearInStoreBufferImpliesThreadLocalViewOf_GlobalStaticVar_{globalVarName}_MatchesGlobalView(hs, tid);
            }}
        }}
      ";
      pgp.AddLemma(str, "utility");


      str = $@"
        lemma Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer_LPlusImpliesH(ls: LPlusState, hs: HState)
          requires L_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(ls)
          requires hs == ConvertTotalState_LPlusH(ls)
          ensures H_Armada_GlobalStaticVar_{globalVarName}_DoesNotAppearInStoreBuffer(hs)
        {{
        }}
      ";
      pgp.AddLemma(str, "utility");
    }
  }
}
