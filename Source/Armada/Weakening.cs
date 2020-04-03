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

  public class WeakeningProofGenerator : AbstractProofGenerator
  {
    private WeakeningStrategyDecl strategy;

    public WeakeningProofGenerator(ProofGenerationParams i_pgp, WeakeningStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
    }



    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();
      
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/weakening/Weakening.i.dfy");
      pgp.MainProof.AddImport("WeakeningModule");
      pgp.MainProof.AddImport("WeakeningSpecModule");
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

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/generic/GenericArmadaLemmas.i.dfy");
      pgp.MainProof.AddImport("GenericArmadaLemmasModule");
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, "Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }
      AddIncludesAndImports();

      GeneratePCFunctions_L();
      GenerateAppendStoreBufferOtherWay();
      GenerateInvariantProof(pgp);
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofHeader();
      GenerateWeakeningRequest();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateLocalViewCommutativityLemmas();
      GenerateLiftNextLemmas();
      GenerateAllActionsLiftableWeakenedLemmas();
      GenerateInitStatesEquivalentLemma();
      GenerateFinalProof();
    }

    private void GenerateWeakeningRequest()
    {
      var lplusstate = AH.ReferToType("LPlusState");
      var hstate = AH.ReferToType("HState");
      var lstep = AH.ReferToType("LStep");
      var hstep = AH.ReferToType("HStep");
      var wrequest = AH.MakeGenericTypeSpecific("WeakeningRequest", new List<Type>{ lplusstate, hstate, lstep, hstep });
      pgp.MainProof.AddTypeSynonymDecl("WRequest", wrequest);

      var str = @"
      function GetWeakeningRequest(): WRequest
      {
        WeakeningRequest(GetLPlusSpec(), GetHSpec(), GetLPlusHRefinementRelation(), iset lps : LPlusState | InductiveInv(lps) :: lps, ConvertTotalState_LPlusH, ConvertMultistep_LH)
      }
      ";
      pgp.AddFunction(str);
    }

    protected override void GenerateLiftStepLemmaForNormalNextRoutine(NextRoutine nextRoutine)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      NextRoutine highNextRoutine = LiftNextRoutine(nextRoutine);
      string highNextRoutineName = highNextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lentry.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", highNextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(wr: WRequest, lps: LPlusState, lps':LPlusState, lentry: L.Armada_TraceEntry)
          requires wr == GetWeakeningRequest()
          requires LPlus_NextOneStep(lps, lps', lentry)
          requires lentry.Armada_TraceEntry_{nextRoutineName}?
          requires lps in wr.inv
          ensures H.Armada_NextOneStep(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), ConvertTraceEntry_LH(lentry))
        {{
          var hs := wr.converter(lps);
          var hs' := wr.converter(lps');
          var tid := lentry.tid;
          var hstep := ConvertTraceEntry_LH(lentry);
          lemma_GetThreadLocalViewAlwaysCommutesWithConvert();
          lemma_StoreBufferAppendAlwaysCommutesWithConvert();
          assert H.Armada_ValidStep_{highNextRoutineName}(hs, tid{hstep_params});
          if L.Armada_UndefinedBehaviorAvoidance_{nextRoutineName}(lps.s, tid{lstep_params}) {{
            assert H.Armada_UndefinedBehaviorAvoidance_{highNextRoutineName}(hs, tid{hstep_params});
            var alt_hs' := H.Armada_GetNextState_{highNextRoutineName}(hs, tid{hstep_params});
            assert hs'.stop_reason == alt_hs'.stop_reason;
            if tid in hs'.threads {{
              assert hs'.threads[tid].stack == alt_hs'.threads[tid].stack;
              assert hs'.threads[tid] == alt_hs'.threads[tid];
            }}
            assert hs'.threads == alt_hs'.threads;
            assert hs'.mem.heap.values == alt_hs'.mem.heap.values;
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

      NextRoutine highNextRoutine = LiftNextRoutine(nextRoutine);
      string highNextRoutineName = highNextRoutine.NameSuffix;

      var lstep_params = String.Join("", nextRoutine.Formals.Select(f => $", lstep.{f.GloballyUniqueVarName}"));
      var hstep_params = String.Join("", highNextRoutine.Formals.Select(f => $", hstep.{f.GloballyUniqueVarName}"));

      var str = $@"
        lemma lemma_LiftNext_{nextRoutineName}(wr:WRequest, lps:LPlusState, lps':LPlusState, lstep:L.Armada_TraceEntry)
          requires wr == GetWeakeningRequest()
          requires lps in wr.inv
          requires LPlus_NextOneStep(lps, lps', lstep)
          requires lstep.Armada_TraceEntry_{nextRoutineName}?
          ensures H.Armada_NextOneStep(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), ConvertTraceEntry_LH(lstep))
        {{
            var hs := wr.converter(lps);
            var hs' := wr.converter(lps');
            var tid := lstep.tid;
            var hstep := ConvertTraceEntry_LH(lstep);

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
        lentry:L.Armada_TraceEntry, hentry:H.Armada_TraceEntry)
        requires wr == GetWeakeningRequest()
        requires lps in wr.inv
        requires LPlus_NextOneStep(lps, lps', lentry)
        requires hs == ConvertTotalState_LPlusH(lps)
        requires hs' == ConvertTotalState_LPlusH(lps')
        requires hentry == ConvertTraceEntry_LH(lentry)
        ensures H.Armada_NextOneStep(hs, hs', hentry)
      {{
        var wr := GetWeakeningRequest();
        match lentry {{
          {finalCases}
        }}
      }}
    ";
      pgp.AddLemma(str);
    }

    private void GenerateAllActionsLiftableWeakenedLemmas()
    {
      var str = @"
        lemma lemma_YieldPointMapsToYieldPoint(pc: L.Armada_PC)
          ensures L.Armada_IsNonyieldingPC(pc) <==> H.Armada_IsNonyieldingPC(ConvertPC_LH(pc))
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_ConvertTotalStateMaintainsThreadYielding(lps: LPlusState, hs:H.Armada_TotalState, tid:Armada_ThreadHandle)
          requires hs == ConvertTotalState_LPlusH(lps)
          ensures  Armada_ThreadYielding(LPlus_GetSpecFunctions(), lps, tid) <==> Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hs, tid)
        {
          if tid in lps.s.threads {
            assert tid in hs.threads;
            var pc := lps.s.threads[tid].pc;
            assert hs.threads[tid].pc == ConvertPC_LH(pc);
            lemma_YieldPointMapsToYieldPoint(pc);
          }
          else {
            assert tid !in hs.threads;
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_LNextImpliesHNext(wr: WRequest, lps:LPlusState, lps':LPlusState, lstep:LStep)
          requires wr == GetWeakeningRequest()
          requires lps in wr.inv
          requires LPlus_Next(lps, lps', lstep)
          ensures H.Armada_Next(ConvertTotalState_LPlusH(lps), ConvertTotalState_LPlusH(lps'), GetWeakeningRequest().step_refiner(lstep))
        {
          var lasf := LPlus_GetSpecFunctions();
          var hasf := H.Armada_GetSpecFunctions();
          var hs := ConvertTotalState_LPlusH(lps);
          var hs' := ConvertTotalState_LPlusH(lps');
          var tid := lstep.tid;
          var lsteps := lstep.steps;
          var lpstates := Armada_GetStateSequence(lasf, lps, lsteps);
          var hsteps := MapSeqToSeq(lsteps, ConvertTraceEntry_LH);
          var hstates := MapSeqToSeq(lpstates, ConvertTotalState_LPlusH);

          var pos := 0;
          while pos < |lsteps|
            invariant 0 <= pos <= |lsteps|
            invariant Armada_NextMultipleSteps(hasf, hs, hstates[pos], hsteps[..pos])
            invariant hstates[..pos+1] == Armada_GetStateSequence(hasf, hs, hsteps[..pos])
            invariant lpstates[pos] in wr.inv
          {
            lemma_ArmadaNextMultipleStepsImpliesValidStep(lasf, lps, lps', lsteps, lpstates, pos);
            assert LPlus_NextOneStep(lpstates[pos], lpstates[pos+1], lsteps[pos]);
            lemma_NextOneStepMaintainsInductiveInv(lpstates[pos], lpstates[pos+1], lsteps[pos]);
            lemma_LNextOneImpliesHNextOne(wr, lpstates[pos], lpstates[pos+1], hstates[pos], hstates[pos+1], lsteps[pos], hsteps[pos]);

            lemma_ExtendArmadaNextMultipleSteps(hasf, hs, hstates[pos], hstates[pos+1], hsteps[..pos], hsteps[pos]);
            lemma_ExtendArmadaGetStateSequence(hasf, hs, hsteps[..pos], hstates[..pos+1], hstates[pos+1], hsteps[pos]);
            assert hsteps[..pos] + [hsteps[pos]] == hsteps[..pos+1];
            assert hstates[..pos+1] + [hstates[pos+1]] == hstates[..pos+1+1];
            pos := pos + 1;
          }

          assert hsteps[..pos] == hsteps;
          assert hstates[..pos+1] == hstates;

          forall step | step in hsteps
            ensures hasf.step_to_thread(step) == tid
            ensures hasf.is_step_tau(step) == lstep.tau
          {
            var i :| 0 <= i < |hsteps| && step == hsteps[i];
            assert hsteps[i] == ConvertTraceEntry_LH(lsteps[i]);
            assert hasf.step_to_thread(step) == lasf.step_to_thread(lsteps[i]) == lstep.tid;
            assert hasf.is_step_tau(step) == lasf.is_step_tau(lsteps[i]) == lstep.tau;
          }

          forall i | 0 < i < |hsteps|
            ensures !Armada_ThreadYielding(hasf, hstates[i], tid)
          {
            assert !Armada_ThreadYielding(lasf, lpstates[i], tid);
            lemma_ConvertTotalStateMaintainsThreadYielding(lpstates[i], hstates[i], tid);
          }

          lemma_ArmadaNextMultipleStepsLastElement(lasf, lps, lps', lsteps, lpstates);
          assert last(hstates) == hs';
          lemma_ConvertTotalStateMaintainsThreadYielding(lps', hs', tid);

          var hstep := Armada_Multistep(hsteps, tid, lstep.tau);

          assert hstep == GetWeakeningRequest().step_refiner(lstep);
          assert H.Armada_Next(hs, hs', hstep);
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_AllActionsLiftableWeakened()
          ensures WeakeningSpecModule.AllActionsLiftableWeakened(GetWeakeningRequest())
        {
          var wr := GetWeakeningRequest();

          forall s, s', lstep |
            && ActionTuple(s, s', lstep) in wr.lspec.next
            && s in wr.inv
            ensures ActionTuple(wr.converter(s), wr.converter(s'), wr.step_refiner(lstep)) in wr.hspec.next;
          {
            lemma_LNextImpliesHNext(wr, s, s', lstep);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateInitStatesEquivalentLemma()
    {
      string str = @"
        lemma lemma_LPlusInitImpliesHInit(lps:LPlusState, hs:HState, hconf:H.Armada_Config)
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
          requires wr == GetWeakeningRequest()
          ensures InitStatesEquivalent(wr)
        {
          forall initial_ls | initial_ls in wr.lspec.init
            ensures wr.converter(initial_ls) in wr.hspec.init
          {
            lemma_LPlusInitImpliesHInit(initial_ls, ConvertTotalState_LPlusH(initial_ls), ConvertConfig_LH(initial_ls.config));
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
          var wr := GetWeakeningRequest();
    
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);

            lemma_InitStatesEquivalent(wr);
            lemma_AllActionsLiftableWeakened();
            lemma_InductiveInvIsInvariant();
      
            assert ValidWeakeningRequest(wr);
            var ahb := lemma_PerformWeakening(wr, alb);
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
