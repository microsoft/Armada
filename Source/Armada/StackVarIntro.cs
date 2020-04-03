using System.Collections.Generic;
using System.Linq;
using System;

namespace Microsoft.Armada
{
  public class StackVarIntroProofGenerator : VarIntroProofGenerator
  {
    protected new StackVariableIntroStrategyDecl strategy;
    public StackVarIntroProofGenerator(ProofGenerationParams i_pgp, StackVariableIntroStrategyDecl i_strategy)
      : base(i_pgp, i_strategy)
    {
      strategy = i_strategy;
    }

    protected override void GenerateConvertStackFrame_LH()
    {
      var cases = new List<MatchCaseExpr>();
      var methodNames = pgp.symbolsLow.MethodNames;
      foreach (var methodName in methodNames) {
        var smst = pgp.symbolsLow.GetMethodSymbolTable(methodName);
        var ps = new List<Expression>();
        var bvs = new List<BoundVar>();
        var lowVarNames = new List<string>(smst.AllVariableNamesInOrder);
        foreach (var varName in lowVarNames)
        {
          var v = smst.LookupVariable(varName);
          var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
          var e = AH.MakeNameSegment(v.FieldName, ty);
          ps.Add(e);
          var bv = AH.MakeBoundVar(v.FieldName, v.GetFlattenedType(pgp.symbolsLow));
          bvs.Add(bv);
        }

        smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
        var highVars = new List<ArmadaVariable>(smst.AllVariablesInOrder);

        if (highVars.Count() != lowVarNames.Count()) {
          for (var i = 0; i < highVars.Count(); ++i) {
            if (!lowVarNames.Contains(highVars[i].name)) {
              var v = highVars[i];
              var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
              ps.Insert(i, AH.MakeNameSegment(strategy.InitializationExpression, ty));
            }
          }
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

    protected override void GenerateConvertStackFrame_HL()
    {
      var cases = new List<MatchCaseExpr>();
      var methodNames = pgp.symbolsHigh.MethodNames;
      foreach (var methodName in methodNames) {
        var smst = pgp.symbolsHigh.GetMethodSymbolTable(methodName);
        var ps = new List<Expression>();
        var bvs = new List<BoundVar>();
        foreach (var v in smst.AllVariablesInOrder) {
          var ty = (v is AddressableArmadaVariable) ? AH.ReferToType("Armada_Pointer") : v.ty;
          var e = AH.MakeNameSegment(v.FieldName, ty);
          if (methodName != strategy.MethodName || v.name != strategy.VariableName) {
            ps.Add(e);
          }
          var bv = AH.MakeBoundVar(v.FieldName, v.GetFlattenedType(pgp.symbolsHigh));
          bvs.Add(bv);
        }
        var case_body = AH.MakeApplyN($"L.Armada_StackFrame_{methodName}", ps, "L.Armada_StackFrame");
        cases.Add(AH.MakeMatchCaseExpr($"Armada_StackFrame_{methodName}", bvs, case_body));
      }

      var source = AH.MakeNameSegment("frame", "H.Armada_StackFrame");
      var body = AH.MakeMatchExpr(source, cases, "L.Armada_StackFrame");
      var formals = new List<Formal> { AH.MakeFormal("frame", "H.Armada_StackFrame") };
      var fn = AH.MakeFunction("ConvertStackFrame_HL", formals, body);
      pgp.AddDefaultClassDecl(fn, "convert");
    }

    protected override void GenerateLemmasWhenAtNewInstructionNextStepMakesProgress() {
      string str = @"
        lemma lemma_AppendNewEntrySame(buffer: seq<H.Armada_StoreBufferEntry>)
          ensures forall entry :: !CanConvertStoreBufferEntry_HL(entry) ==> ConvertStoreBuffer_HL(buffer + [entry]) == ConvertStoreBuffer_HL(buffer)
        {
          forall entry | !CanConvertStoreBufferEntry_HL(entry)
            ensures ConvertStoreBuffer_HL(buffer + [entry]) == ConvertStoreBuffer_HL(buffer)
            {
              lemma_FilterMapSeqsToSeq(buffer, [entry], e => if CanConvertStoreBufferEntry_HL(e) then Some(ConvertStoreBufferEntry_HL(e)) else None);
            }
        }";

      pgp.AddLemma(str);

      str = @"
        lemma lemma_WhenAtNewInstructionNextStepMakesProgress(
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry,
          tid: Armada_ThreadHandle
          )
          requires hs.stop_reason.Armada_NotStopped?
          requires tid in hs.threads
          requires NewInstructionThread_H(hs, tid)
          requires hstep == NextStepThread_H(hs, tid)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires VarIntroInvariant(hs)
          ensures  ConvertTotalState_HL(hs') == ConvertTotalState_HL(hs)
          ensures  H.Armada_NextOneStep(hs, hs', hstep)
          ensures  0 <= ProgressMeasureState_H(hs', tid) < ProgressMeasureState_H(hs, tid)
        {
          var threads := hs.threads;
          var new_threads := hs'.threads;
          assert forall tid' :: tid' in threads && tid' != tid ==> threads[tid'] == new_threads[tid'];
          assert ConvertThread_HL(new_threads[tid]) == ConvertThread_HL(threads[tid]) ==> ConvertThreads_HL(new_threads) == ConvertThreads_HL(threads);
          assert VarIntroInvariant(hs');
          assert ConvertTotalState_HL(hs) == ConvertTotalState_HL(hs');
          assert H.Armada_NextOneStep(hs, hs', hstep);
          assert 0 <= ProgressMeasureState_H(hs', tid) < ProgressMeasureState_H(hs, tid);
        }
      ";

      pgp.AddLemma(str);
    }

    protected override MatchCaseExpr GetTraceEntryCaseForNormalNextRoutine_LH(NextRoutine nextRoutine)
    {
      string nextRoutineName = nextRoutine.NameSuffix;

      var bvs = new List<BoundVar> { AH.MakeBoundVar("tid", "Armada_ThreadHandle") };
      bvs.AddRange(nextRoutine.Formals.Select(f => AH.MakeBoundVar(f.LocalVarName, AddModuleNameToArmadaType(f.VarType, "L"))));

      var ps = new List<Expression> { AH.MakeNameSegment("tid", "Armada_ThreadHandle") };
      ps.AddRange(nextRoutine.Formals.Select(f => AH.MakeNameSegment(f.LocalVarName, f.VarType)));

      if (nextRoutine.nextType == NextType.Call &&
          ((ArmadaCallStatement)nextRoutine.armadaStatement).CalleeName == strategy.MethodName ||
          nextRoutine.nextType == NextType.CreateThread &&
          ((nextRoutine.stmt as UpdateStmt).Rhss[0] as CreateThreadRhs).MethodName.val == strategy.MethodName) {
        var highRoutine = LiftNextRoutine(nextRoutine);
        var highFormals = new List<NextFormal>(highRoutine.Formals);
        for (var i = 0; i < highFormals.Count(); ++ i) {
          if (! nextRoutine.Formals.Any(f => f.LocalVarName == highFormals[i].LocalVarName)) {
            ps.Insert(i + 1, AH.MakeNameSegment(strategy.InitializationExpression, highFormals[i].VarType));
            break;
          }
        }
      }

      string hname = LiftNextRoutine(nextRoutine).NameSuffix;
      var case_body = AH.MakeApplyN($"H.Armada_TraceEntry_{hname}", ps, "H.Armada_TraceEntry");
      var case0 = AH.MakeMatchCaseExpr($"Armada_TraceEntry_{nextRoutineName}", bvs, case_body);
      return case0;
    }

    protected override void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", nextRoutine.Formals.Select(f => $", hstep.{TranslateFormalNameUsingPcMap(f, nextRoutine.pc, pcMap)}"));

      var hNextRoutine = LiftNextRoutine(nextRoutine);
      hstep_params = String.Join("", hNextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));
      string hNextRoutineName = hNextRoutine.NameSuffix;

      string optionalRequires = "";
      string optionalProof = "";

      if (nextRoutine.nextType == NextType.Update && ! ((UpdateStmt)nextRoutine.stmt).BypassStoreBuffers) {
        optionalProof = "";
      }
      else if (nextRoutine.nextType == NextType.Call || nextRoutine.nextType == NextType.Return) {
        optionalProof = "assert ls'.threads[tid] == ConvertTotalState_HL(hs').threads[tid];";
      }
      else if (nextRoutine.nextType == NextType.Terminate) {
        optionalRequires = "requires !(hs.stop_reason.Armada_NotStopped? && lstep.tid in hs.threads && NewInstructionStoreBufferEntries_H(hs.threads[lstep.tid].storeBuffer))";
      }

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(
            ls:LState,
            ls':LState,
            lstep:L.Armada_TraceEntry,
            hs:HState,
            hs':HState,
            hstep:H.Armada_TraceEntry
            )
            {optionalRequires}
            requires !NewInstructionThread_H(hs, lstep.tid)
            requires L.Armada_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires ls == ConvertTotalState_HL(hs)
            ensures  H.Armada_NextOneStep(hs, hs', hstep)
            ensures  ls' == ConvertTotalState_HL(hs')
        {{
            var tid := lstep.tid;

            lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
            lemma_StoreBufferAppendAlwaysCommutesWithConvert();
            assert H.Armada_ValidStep_{hNextRoutineName}(hs, tid{hstep_params});
            if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(ls, tid{lstep_params}) {{
              {optionalProof}
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

    protected override void GenerateVarIntroRequest()
    {
      // function generation

      GenerateReturnToPC_HL();

      GenerateVarIntroInvariant();
      GenerateVarIntroInvariantProof();

      GenerateNextState_H();
      GenerateNewInstructionPC_H();
      GenerateNewTSOInstruction_H();
      GenerateNewInstructionThread_H();
      GenerateNewInstructionStoreBufferEntries_H();

      GenerateNextStepThread_H();

      GenerateProgressMeasureThread_H();
      GenerateProgressMeasureState_H();

      // lemma generation

      GenerateLemmasWhenAtNewInstructionNextStepMakesProgress();

      GenerateLocalViewCommutativityLemmas();
      GenerateLiftStepLemmas();
      GenerateIntroSatisfiesRelation();
      GenerateIntroPreservesInit();
    }
  };
};
