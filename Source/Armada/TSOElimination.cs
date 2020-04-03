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
  public class TSOField
  {
    public readonly string fieldName;
    public readonly int fieldNum;
    public readonly Type ty;
    public readonly bool isArray;
    public readonly int whichArray;
    public readonly ArmadaStruct outerStruct;

    public TSOField(string i_fieldName, int i_fieldNum, Type i_ty, bool i_isArray, int i_whichArray, ArmadaStruct i_outerStruct)
    {
      fieldName = i_fieldName;
      fieldNum = i_fieldNum;
      ty = i_ty;
      isArray = i_isArray;
      whichArray = i_whichArray;
      outerStruct = i_outerStruct;
    }
  }

  public class TSOFieldList
  {
    private List<TSOField> fields;
    private int numArrays;
    private string fieldSpec;
    private string indexList;
    private string indexParamList;
    private string validIndices;

    public TSOFieldList()
    {
      fields = new List<TSOField>();
      numArrays = 0;
      fieldSpec = "";
      indexList = "";
      indexParamList = "";
      validIndices = "";
    }

    public ArmadaStruct AddField(ArmadaSymbolTable symbols, ArmadaStruct outerStruct, string fieldName, Type ty)
    {
      ArmadaStruct innerStruct = null;
      string structName;

      if (ty is SizedArrayType) {
        var subtype = ((SizedArrayType)ty).Range;
        if (!AH.IsPrimitiveType(subtype) && subtype is UserDefinedType) {
          structName = ((UserDefinedType)subtype).Name;
          innerStruct = symbols.LookupStruct(structName);
        }
        fields.Add(new TSOField(fieldName, fields.Count(), ty, true, numArrays, outerStruct));
        fields.Add(new TSOField(null, fields.Count(), subtype, false, -1, null));
        validIndices += $" && 0 <= idx{numArrays} < |g{fieldSpec}.{fieldName}|";
        fieldSpec += $".{fieldName}[idx{numArrays}]";
        indexList += $", idx{numArrays}";
        indexParamList += $", idx{numArrays}:int";
        ++numArrays;
      }
      else {
        if (!AH.IsPrimitiveType(ty) && ty is UserDefinedType) {
          structName = ((UserDefinedType)ty).Name;
          innerStruct = symbols.LookupStruct(structName);
        }
        fields.Add(new TSOField(fieldName, fields.Count(), ty, false, -1, outerStruct));
        fieldSpec += $".{fieldName}";
      }

      return innerStruct;
    }

    public TSOField GetVar() { return fields[0]; }
    public int NumFields { get { return fields.Count(); } }
    public TSOField GetField(int i) { return fields[i]; }
    public int NumArrays { get { return numArrays; } }
    public string FieldSpec { get { return fieldSpec; } }
    public string IndexList { get { return indexList; } }
    public string IndexParamList { get { return indexParamList; } }
    public string IndexListWithoutLeadingComma { get { return indexList.Length > 2 ? indexList.Substring(2) : ""; } }
    public string IndexParamListWithoutLeadingComma { get { return indexParamList.Length > 2 ? indexParamList.Substring(2) : ""; } }
    public string ValidIndices { get { return validIndices.Length > 0 ? validIndices : "true"; } }
  }

  public class TSOEliminationNoConflictingOwnershipInvariantInfo : InvariantInfo
  {
    private TSOFieldList fields;
    private string ownershipPredicate;

    public TSOEliminationNoConflictingOwnershipInvariantInfo(TSOFieldList i_fields, string i_ownershipPredicate)
      : base("NoConflictingOwnership", "NoConflictingOwnership", new List<string>{ "InductiveInv" })
    {
      fields = i_fields;
      ownershipPredicate = i_ownershipPredicate;
    }

    public override string GenerateSpecificNextLemma(ProofGenerationParams pgp, NextRoutine nextRoutine, IEnumerable<InvariantInfo> allInvariants)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      string nextLemmaName = $"lemma_NoConflictingOwnershipPreservedByNext_{nextRoutineName}";

      string str = $@"
        lemma {nextLemmaName}(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
          requires InductiveInv(s)
          requires LPlus_NextOneStep(s, s', step)
          requires step.Armada_TraceEntry_{nextRoutineName}?
          ensures  NoConflictingOwnership(s')
        {{
          if s'.s.stop_reason.Armada_NotStopped? {{
            assert s.s.stop_reason.Armada_NotStopped?;
            forall tid1, tid2{fields.IndexList} |
              && tid1 in s'.s.threads
              && tid2 in s'.s.threads
              && {ownershipPredicate}(s', tid1{fields.IndexList})
              && {ownershipPredicate}(s', tid2{fields.IndexList})
              ensures tid1 == tid2
            {{
              assert tid1 in s.s.threads && tid2 in s.s.threads && {ownershipPredicate}(s, tid1{fields.IndexList}) && {ownershipPredicate}(s, tid2{fields.IndexList}) ==> tid1 == tid2;
            }}
          }}
        }}
      ";
      pgp.AddLemma(str, "invariants");

      return nextLemmaName;
    }
  }

  public class TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo : InvariantInfo
  {
    private TSOFieldList fields;
    private string ownershipPredicate;

    public TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo(TSOFieldList i_fields, string i_ownershipPredicate)
      : base("NonOwnersLackStoreBufferEntries", "NonOwnersLackStoreBufferEntries", new List<string>{ "InductiveInv" })
    {
      fields = i_fields;
      ownershipPredicate = i_ownershipPredicate;
    }

    public override string GenerateSpecificNextLemma(ProofGenerationParams pgp, NextRoutine nextRoutine, IEnumerable<InvariantInfo> allInvariants)
    {
      var nextRoutineName = nextRoutine.NameSuffix;

      string nextLemmaName = $"lemma_NonOwnersLackStoreBufferEntriesPreservedByNext_{nextRoutineName}";

      string str = $@"
        lemma {nextLemmaName}(s:LPlusState, s':LPlusState, step:L.Armada_TraceEntry)
          requires InductiveInv(s)
          requires LPlus_NextOneStep(s, s', step)
          requires step.Armada_TraceEntry_{nextRoutineName}?
          ensures  NonOwnersLackStoreBufferEntries(s')
        {{
          var tid := step.tid;
          forall any_tid, entry{fields.IndexList} |
            && any_tid in s'.s.threads
            && !{ownershipPredicate}(s', any_tid{fields.IndexList})
            && entry in s'.s.threads[any_tid].storeBuffer
            ensures !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList})
          {{
            if any_tid != tid {{
              assert !{ownershipPredicate}(s, any_tid{fields.IndexList});
              assert s'.s.threads[any_tid] == s.s.threads[any_tid];
              assert entry in s.s.threads[any_tid].storeBuffer;
              assert !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList});
            }}
            else {{
              assert !{ownershipPredicate}(s, tid{fields.IndexList});
              if entry in s.s.threads[any_tid].storeBuffer {{
                assert !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList});
              }}
            }}
          }}
        }}
      ";
      pgp.AddLemma(str, "invariants");

      return nextLemmaName;
    }
  }

  public class TSOEliminationProofGenerator : AbstractProofGenerator
  {
    private TSOEliminationStrategyDecl strategy;
    private TSOFieldList fields;
    private string ownershipPredicate;

    public TSOEliminationProofGenerator(ProofGenerationParams i_pgp, TSOEliminationStrategyDecl i_strategy)
      : base(i_pgp)
    {
      strategy = i_strategy;
      ownershipPredicate = null;
    }

    public override void GenerateProof()
    {
      if (!CheckEquivalence()) {
        AH.PrintError(pgp.prog, $"Levels {pgp.mLow.Name} and {pgp.mHigh.Name} aren't sufficiently equivalent to perform refinement proof generation using the variable-hiding strategy");
        return;
      }

      if (!CheckFields()) {
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofGivenMap();
    }

    public bool CheckFields()
    {
      int numFieldNames = strategy.Fields.Count();

      if (numFieldNames < 1) {
        AH.PrintError(pgp.prog, "No field list found in TSO elimination strategy description");
        return false;
      }

      string varName = strategy.Fields[0];
      ArmadaVariable v = pgp.symbolsLow.Globals.Lookup(varName);
      if (v == null) {
        AH.PrintError(pgp.prog, strategy.tok, $"No global variable named {varName}");
        return false;
      }

      fields = new TSOFieldList();
      ArmadaStruct s = fields.AddField(pgp.symbolsLow, null, varName, v.ty);

      for (int i = 1; i < numFieldNames; ++i) {
        string fieldName = strategy.Fields[i];

        if (s == null) {
          AH.PrintError(pgp.prog, strategy.tok, $"Can't find field named {fieldName} within non-struct");
          return false;
        }

        Type ty = s.LookupFieldType(fieldName);
        if (ty == null) {
          AH.PrintError(pgp.prog, strategy.tok, $"No field named {fieldName} exists in struct {s.Name}");
          return false;
        }

        s = fields.AddField(pgp.symbolsLow, s, fieldName, ty);
      }

      if (s != null) {
        AH.PrintError(pgp.prog, "The field list given for the TSO-elimination strategy ends in the middle of a struct.  It has to go all the way to a primitive field.");
        return false;
      }
      return true;
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/tsoelimination/TSOElimination.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("TSOEliminationSpecModule");
      pgp.MainProof.AddImport("TSOEliminationModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");

      pgp.proofFiles.IncludeAndImportGeneratedFile("convert", "invariants");
    }

    private void InitializeAuxiliaryProofFiles()
    {
      var defsFile = pgp.proofFiles.CreateAuxiliaryProofFile("defs");
      defsFile.IncludeAndImportGeneratedFile("specs");
      defsFile.IncludeAndImportGeneratedFile("convert");
      defsFile.IncludeAndImportGeneratedFile("invariants");
      defsFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/tsoelimination/TSOElimination.i.dfy");
      defsFile.AddImport("TSOEliminationSpecModule");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      defsFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      defsFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("defs");

      var tsoutilFile = pgp.proofFiles.CreateAuxiliaryProofFile("tsoutil");
      tsoutilFile.IncludeAndImportGeneratedFile("specs");
      tsoutilFile.IncludeAndImportGeneratedFile("convert");
      tsoutilFile.IncludeAndImportGeneratedFile("invariants");
      tsoutilFile.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/strategies/tsoelimination/TSOElimination.i.dfy");
      tsoutilFile.AddImport("TSOEliminationSpecModule");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      tsoutilFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("tsoutil");

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var nextFileName = "next_" + nextRoutine.NameSuffix;
        var nextFile = pgp.proofFiles.CreateAuxiliaryProofFile(nextFileName);
        nextFile.IncludeAndImportGeneratedFile("specs");
        nextFile.IncludeAndImportGeneratedFile("convert");
        nextFile.IncludeAndImportGeneratedFile("invariants");
        nextFile.IncludeAndImportGeneratedFile("defs");
        nextFile.IncludeAndImportGeneratedFile("tsoutil");
        nextFile.IncludeAndImportGeneratedFile("utility");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
        nextFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
        nextFile.AddImport("util_collections_seqs_s");
        pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile(nextFileName);
      }
    }

    private void GenerateProofGivenMap()
    {
      GenerateProofHeader();
      GeneratePCFunctions_L();
      InitializeAuxiliaryProofFiles();
      AddStackMatchesMethodInvariant();
      GenerateOwnershipPredicate();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertTraceEntry_LH();
      GenerateConvertAndSuppressSteps();
      GenerateLocalViewCommutativityLemmas();
      GenerateNextState_H();
      GenerateStrategyInvariants();
      GenerateInvariantProof(pgp);
      GenerateGenericStoreBufferLemmas_L();
      GenerateEmptyStoreBufferLemmas();
      GenerateValidIndicesLemmas();
      GenerateUnchangedLemmas();
      GenerateStoreBufferMatchesLemmas();
      GenerateStatesMatchExceptPredicates();
      GenerateIntermediateRelation();
      GenerateIsSkippedTauStep();
      GenerateTSOEliminationRequest();
      GenerateInitialConditionsHoldLemma();
      GenerateIntermediateRelationImpliesRelationLemma();
      GenerateRegularStepsLiftableLemma();
      GenerateRegularStepMaintainsTotalStateMatchesExceptVar();
      GenerateRegularStepMaintainsGlobalsNoThreadOwnsMatch();
      GenerateRegularStepMaintainsHighLevelStoreBuffersLackVar();
      GenerateRegularStepMaintainsOwnersLocalViewsMatch();
      GenerateRegularStepMaintainsIntermediateRelation();
      GenerateSkippedTauStepMaintainsRelation();
      GenerateStepMaintainsRelation();
      GenerateValidRequestLemma();
      GenerateFinalProof();
    }

    private void GenerateConvertAndSuppressSteps()
    {
      string str;

      str = @"
        function ConvertAndSuppressSteps(ls: LState, hs: HState, steps: seq<L.Armada_TraceEntry>) : seq<H.Armada_TraceEntry>
          decreases |steps|
        {
          if |steps| == 0 then
            []
          else
            var ls' := L.Armada_GetNextStateAlways(ls, steps[0]);
            if IsSkippedTauStep(ls, hs, steps[0]) then
              ConvertAndSuppressSteps(ls', hs, steps[1..])
            else
              var hstep := ConvertTraceEntry_LH(steps[0]);
              var hs' := H.Armada_GetNextStateAlways(hs, hstep);
              [ConvertTraceEntry_LH(steps[0])] + ConvertAndSuppressSteps(ls', hs', steps[1..])
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        function ConvertAndSuppressStepSequence(ls: LPlusState, hs: HState, entry: LStep) : HStep
        {
          Armada_Multistep(ConvertAndSuppressSteps(ls.s, hs, entry.steps), entry.tid, entry.tau)
        }
      ";
      pgp.AddFunction(str, "defs");

      str = @"
        lemma lemma_ConvertAndSuppressStepsMaintainsMatching(ls: LState, hs: HState, tau:bool, tid:Armada_ThreadHandle,
                                                             steps: seq<L.Armada_TraceEntry>)
          requires forall step :: step in steps ==> step.tid == tid
          requires forall step :: step in steps ==> step.Armada_TraceEntry_Tau? == tau
          ensures  forall step :: step in ConvertAndSuppressSteps(ls, hs, steps) ==> step.tid == tid
          ensures  forall step :: step in ConvertAndSuppressSteps(ls, hs, steps) ==> step.Armada_TraceEntry_Tau? == tau
          ensures  |ConvertAndSuppressSteps(ls, hs, steps)| <= |steps|
          decreases |steps|
        {
          if |steps| > 0 {
            var ls' := L.Armada_GetNextStateAlways(ls, steps[0]);
            if IsSkippedTauStep(ls, hs, steps[0]) {
              lemma_ConvertAndSuppressStepsMaintainsMatching(ls', hs, tau, tid, steps[1..]);
            }
            else {
              var hstep := ConvertTraceEntry_LH(steps[0]);
              var hs' := H.Armada_GetNextStateAlways(hs, hstep);
              lemma_ConvertAndSuppressStepsMaintainsMatching(ls', hs', tau, tid, steps[1..]);
            }
          }
        }
      ";
      pgp.AddLemma(str, "defs");
    }

    protected void GenerateStrategyInvariants()
    {
      string str;

      str = $@"
        predicate NoConflictingOwnership(s: LPlusState)
        {{
          s.s.stop_reason.Armada_NotStopped? ==>
          forall tid1, tid2{fields.IndexList} ::
            && tid1 in s.s.threads
            && tid2 in s.s.threads
            && {ownershipPredicate}(s, tid1{fields.IndexList})
            && {ownershipPredicate}(s, tid2{fields.IndexList})
            ==> tid1 == tid2
        }}
      ";
      pgp.AddPredicate(str, "invariants");
      AddInvariant(new TSOEliminationNoConflictingOwnershipInvariantInfo(fields, ownershipPredicate));

      str = @"
        predicate NonOwnersLackStoreBufferEntries(s: LPlusState)
        {
      ";
      str += $"  forall tid{fields.IndexList} ::\n";
      str += "    && tid in s.s.threads\n";
      str += $"    && !{ownershipPredicate}(s, tid{fields.IndexList})\n";
      str += $"    ==> StoreBufferLacksIndices_L(s.s.threads[tid].storeBuffer{fields.IndexList})\n";
      str += "}\n";
      pgp.AddPredicate(str, "invariants");
      AddInvariant(new TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo(fields, ownershipPredicate));
    }

    private void GenerateOwnershipPredicate()
    {
      var str = $@"
        predicate OwnershipPredicate(s:LPlusState, tid:Armada_ThreadHandle{fields.IndexParamList})
        {{
          { strategy.OwnershipPredicate }
        }}
      ";
      pgp.AddPredicate(str, "invariants");
      ownershipPredicate = "OwnershipPredicate";
    }

    private void GenerateStatesMatchExceptPredicates()
    {
      string str;
      TSOField f;

      str = @"
        predicate StoreBufferLocationConcernsVar_L(loc:L.Armada_StoreBufferLocation)
        {
          && loc.Armada_StoreBufferLocation_Unaddressable?
      ";
      str += $"  && loc.v.Armada_GlobalStaticVar_{fields.GetVar().fieldName}?\n";
      str += $"  && |loc.fields| == {fields.NumFields-1}\n";
      for (int i = 1; i < fields.NumFields; ++i) {
        f = fields.GetField(i);
        if (f.fieldName != null) {
          str += $"  && loc.fields[{i-1}].Armada_FieldStruct?\n";
          str += $"  && loc.fields[{i-1}].f.Armada_FieldType_{f.outerStruct.Name}'{f.fieldName}?\n";
        }
        else {
          str += $"  && loc.fields[{i-1}].Armada_FieldArrayIndex?\n";
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate StoreBufferLocationConcernsVar_H(loc:H.Armada_StoreBufferLocation)
        {
          && loc.Armada_StoreBufferLocation_Unaddressable?
      ";
      str += $"  && loc.v.Armada_GlobalStaticVar_{fields.GetVar().fieldName}?\n";
      str += $"  && |loc.fields| == {fields.NumFields-1}\n";
      for (int i = 1; i < fields.NumFields; ++i) {
        f = fields.GetField(i);
        if (f.fieldName != null) {
          str += $"  && loc.fields[{i-1}].Armada_FieldStruct?\n";
          str += $"  && loc.fields[{i-1}].f.Armada_FieldType_{f.outerStruct.Name}'{f.fieldName}?\n";
        }
        else {
          str += $"  && loc.fields[{i-1}].Armada_FieldArrayIndex?\n";
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate StoreBufferMatchesExceptVar(lbuf:seq<L.Armada_StoreBufferEntry>, hbuf:seq<H.Armada_StoreBufferEntry>)
        {
          if |lbuf| == 0 then
            |hbuf| == 0
          else if StoreBufferLocationConcernsVar_L(lbuf[0].loc) then
            StoreBufferMatchesExceptVar(lbuf[1..], hbuf)
          else
            && |hbuf| > 0
            && hbuf[0] == ConvertStoreBufferEntry_LH(lbuf[0])
            && StoreBufferMatchesExceptVar(lbuf[1..], hbuf[1..])
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate GlobalsMatchesExceptVar(lglobals:L.Armada_Globals, hglobals:H.Armada_Globals)
        {
          true
      ";
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable && varName != fields.GetVar().fieldName) {
          str += $"  && hglobals.{varName} == lglobals.{varName}\n";
        }
      }

      var fieldSpec = $"globals";
      var indices = new List<string>();
      var indexConstraints = new List<string>();
      for (int i = 0; i < fields.NumFields; ++i) {
        f = fields.GetField(i);

        if (f.fieldName != null) {
          if (i > 0) {
            foreach (var otherFieldName in f.outerStruct.FieldNames) {
              if (otherFieldName != f.fieldName) {
                if (indices.Any()) {
                  var commaSeparatedIndices = string.Join(", ", indices);
                  var combinedIndexConstraints = string.Join(" && ", indexConstraints);
                  str += $"  && (forall {commaSeparatedIndices} :: {combinedIndexConstraints} ==> h{fieldSpec}.{otherFieldName} == l{fieldSpec}.{otherFieldName})\n";
                }
                else {
                  str += $"  && h{fieldSpec}.{otherFieldName} == l{fieldSpec}.{otherFieldName}\n";
                }
              }
            }
          }

          fieldSpec += $".{f.fieldName}";
          if (f.isArray) {
            if (indices.Any()) {
              var commaSeparatedIndices = string.Join(", ", indices);
              var combinedIndexConstraints = string.Join(" && ", indexConstraints);
              str += $"  && (forall {commaSeparatedIndices} :: {combinedIndexConstraints} ==> |h{fieldSpec}| == |l{fieldSpec}|)\n";
            }
            else {
              str += $"  && |h{fieldSpec}| == |l{fieldSpec}|\n";
            }
            indices.Add($"idx{f.whichArray}");
            indexConstraints.Add($"0 <= idx{f.whichArray} < |l{fieldSpec}|");
            fieldSpec += $"[idx{f.whichArray}]";
          }
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate SharedMemoryMatchesExceptVar(lmem: L.Armada_SharedMemory, hmem: H.Armada_SharedMemory)
        {
          && GlobalsMatchesExceptVar(lmem.globals, hmem.globals)
          && hmem.heap == lmem.heap
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        lemma lemma_GlobalsMatchExceptVarPreservedByApplyingStoreBufferEntryThatDoesntConcernVar_L(
          lmem: L.Armada_SharedMemory,
          hmem: H.Armada_SharedMemory,
          lentry: L.Armada_StoreBufferEntry
          )
          requires SharedMemoryMatchesExceptVar(lmem, hmem)
          requires StoreBufferLocationConcernsVar_L(lentry.loc)
          ensures  SharedMemoryMatchesExceptVar(L.Armada_ApplyStoreBufferEntry(lmem, lentry), hmem)
        {
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        lemma lemma_GlobalsMatchExceptVarPreservedByApplyingStoreBufferEntryThatDoesntConcernVar_H(
          lmem: L.Armada_SharedMemory,
          hmem: H.Armada_SharedMemory,
          hentry: H.Armada_StoreBufferEntry
          )
          requires SharedMemoryMatchesExceptVar(lmem, hmem)
          requires StoreBufferLocationConcernsVar_H(hentry.loc)
          ensures  SharedMemoryMatchesExceptVar(lmem, H.Armada_ApplyStoreBufferEntry(hmem, hentry))
        {
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        lemma lemma_GlobalsMatchExceptVarPreservedByApplyingMatchingStoreBufferEntries(
          lmem: L.Armada_SharedMemory,
          hmem: H.Armada_SharedMemory,
          lentry: L.Armada_StoreBufferEntry,
          hentry: H.Armada_StoreBufferEntry
          )
          requires SharedMemoryMatchesExceptVar(lmem, hmem)
          requires hentry == ConvertStoreBufferEntry_LH(lentry)
          ensures  SharedMemoryMatchesExceptVar(L.Armada_ApplyStoreBufferEntry(lmem, lentry), H.Armada_ApplyStoreBufferEntry(hmem, hentry))
        {
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        lemma lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(
          lmem: L.Armada_SharedMemory,
          hmem: H.Armada_SharedMemory,
          lbuf: seq<L.Armada_StoreBufferEntry>,
          hbuf: seq<H.Armada_StoreBufferEntry>
          )
          requires SharedMemoryMatchesExceptVar(lmem, hmem)
          requires StoreBufferMatchesExceptVar(lbuf, hbuf)
          ensures  SharedMemoryMatchesExceptVar(L.Armada_ApplyStoreBuffer(lmem, lbuf), H.Armada_ApplyStoreBuffer(hmem, hbuf))
          decreases |lbuf| + |hbuf|
        {
          var llocv := L.Armada_ApplyStoreBuffer(lmem, lbuf);
          var hlocv := H.Armada_ApplyStoreBuffer(hmem, hbuf);
      
          if |lbuf| == 0 {
          }
          else if StoreBufferLocationConcernsVar_L(lbuf[0].loc) {
            lemma_GlobalsMatchExceptVarPreservedByApplyingStoreBufferEntryThatDoesntConcernVar_L(lmem, hmem, lbuf[0]);
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]), hmem, lbuf[1..], hbuf);
          } else {
            lemma_GlobalsMatchExceptVarPreservedByApplyingMatchingStoreBufferEntries(lmem, hmem, lbuf[0], hbuf[0]);
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(L.Armada_ApplyStoreBufferEntry(lmem, lbuf[0]), H.Armada_ApplyStoreBufferEntry(hmem, hbuf[0]), lbuf[1..], hbuf[1..]);
          }
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        lemma lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways()
          ensures forall lmem, hmem, lbuf, hbuf ::
                    SharedMemoryMatchesExceptVar(lmem, hmem) && StoreBufferMatchesExceptVar(lbuf, hbuf) ==>
                    SharedMemoryMatchesExceptVar(L.Armada_ApplyStoreBuffer(lmem, lbuf), H.Armada_ApplyStoreBuffer(hmem, hbuf))
        {
          forall lmem, hmem, lbuf, hbuf | SharedMemoryMatchesExceptVar(lmem, hmem) && StoreBufferMatchesExceptVar(lbuf, hbuf)
            ensures SharedMemoryMatchesExceptVar(L.Armada_ApplyStoreBuffer(lmem, lbuf), H.Armada_ApplyStoreBuffer(hmem, hbuf))
          {
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(lmem, hmem, lbuf, hbuf);
          }
        }
      ";
      pgp.AddLemma(str, "invariants");

      str = @"
        predicate ExtendedFrameMatchesExceptVar(lframe:L.Armada_ExtendedFrame, hframe:H.Armada_ExtendedFrame)
        {
          && hframe.return_pc == ConvertPC_LH(lframe.return_pc)
          && hframe.frame == ConvertStackFrame_LH(lframe.frame)
          && hframe.new_ptrs == lframe.new_ptrs
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate StackMatchesExceptVar(lstack:seq<L.Armada_ExtendedFrame>, hstack:seq<H.Armada_ExtendedFrame>)
        {
          && |hstack| == |lstack|
          && (forall i :: 0 <= i < |lstack| ==> ExtendedFrameMatchesExceptVar(lstack[i], hstack[i]))
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate ThreadMatchesExceptVar(lthread:L.Armada_Thread, hthread:H.Armada_Thread)
        {
          && hthread.pc == ConvertPC_LH(lthread.pc)
          && hthread.top == ConvertStackFrame_LH(lthread.top)
          && hthread.new_ptrs == lthread.new_ptrs
          && StackMatchesExceptVar(lthread.stack, hthread.stack)
          && StoreBufferMatchesExceptVar(lthread.storeBuffer, hthread.storeBuffer)
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate ThreadsMatchesExceptVar(lthreads:map<Armada_ThreadHandle, L.Armada_Thread>,
                                          hthreads:map<Armada_ThreadHandle, H.Armada_Thread>)
        {
          && (forall tid :: tid in lthreads <==> tid in hthreads)
          && (forall tid :: tid in lthreads ==> ThreadMatchesExceptVar(lthreads[tid], hthreads[tid]))
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate TotalStateMatchesExceptVar(ls:LState, hs:HState)
        {
          && hs.stop_reason == ls.stop_reason
          && ThreadsMatchesExceptVar(ls.threads, hs.threads)
          && SharedMemoryMatchesExceptVar(ls.mem, hs.mem)
          && hs.addrs == ConvertAddrs_LH(ls.addrs)
          && hs.ghosts == ConvertGhosts_LH(ls.ghosts)
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate LocalViewsMatchExceptVar(ls:LState, hs:HState)
        {
          forall any_tid :: any_tid in ls.threads && any_tid in hs.threads ==>
            SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls, any_tid), H.Armada_GetThreadLocalView(hs, any_tid))
        }
      ";
      pgp.AddPredicate(str, "invariants");
    }

    private void GenerateIsSkippedTauStep()
    {
      string str = @"
        predicate IsSkippedTauStep(ls:LState, hs:HState, step:L.Armada_TraceEntry)
        {
          && step.Armada_TraceEntry_Tau?
          && var tid := step.tid;
          && tid in ls.threads
          && |ls.threads[tid].storeBuffer| > 0
          && StoreBufferLocationConcernsVar_L(ls.threads[tid].storeBuffer[0].loc)
          && !(&& tid in hs.threads
               && |hs.threads[tid].storeBuffer| > 0
               && hs.threads[tid].storeBuffer[0] == ConvertStoreBufferEntry_LH(ls.threads[tid].storeBuffer[0])
               && StoreBufferMatchesExceptVar(ls.threads[tid].storeBuffer[1..], hs.threads[tid].storeBuffer[1..]))
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateIntermediateRelation()
    {
      string str;

      str = $@"
        predicate NoThreadOwns(s: LPlusState{fields.IndexParamList})
        {{
          forall tid :: tid in s.s.threads ==> !{ownershipPredicate}(s, tid{fields.IndexList})
        }}
      ";
      pgp.AddPredicate(str, "invariants");

      var fieldIndices = new List<int>();
      for (int i = 0; i < fields.NumFields; ++i) {
        var f = fields.GetField(i);
        if (f.isArray) {
          fieldIndices.Add(i);
        }
      }

      str = $@"
        predicate ValidIndices_L(g:L.Armada_Globals{fields.IndexParamList})
        {{
          {fields.ValidIndices}
        }}
      ";
      str += "{\n";
      pgp.AddPredicate(str, "invariants");

      str = $@"
        predicate ValidIndices_H(g:H.Armada_Globals{fields.IndexParamList})
        {{
          {fields.ValidIndices}
        }}
      ";
      pgp.AddPredicate(str, "invariants");

      str = $"predicate StoreBufferLocationConcernsIndices_L(loc:L.Armada_StoreBufferLocation{fields.IndexParamList})\n";
      str += "{\n";
      str += "  && StoreBufferLocationConcernsVar_L(loc)\n";
      for (int i = 0; i < fieldIndices.Count; ++i) {
        str += $"  && loc.fields[{fieldIndices[i]}].i == idx{i}\n";
      }
      str += "}\n";
      pgp.AddPredicate(str, "invariants");

      str = $@"
        predicate StoreBufferLacksIndices_L(buf: seq<L.Armada_StoreBufferEntry>{fields.IndexParamList})
        {{
          forall entry :: entry in buf ==> !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList})
        }}
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate StoreBufferLacksVar_H(buf: seq<H.Armada_StoreBufferEntry>)
        {
          forall entry :: entry in buf ==> !StoreBufferLocationConcernsVar_H(entry.loc)
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = $@"
        predicate GlobalsNoThreadOwnsMatchSpecific(ls: LPlusState, hs: HState{fields.IndexParamList})
        {{
          var lg, hg := ls.s.mem.globals, hs.mem.globals;
          && NoThreadOwns(ls{fields.IndexList})
          && ValidIndices_L(lg{fields.IndexList})
          && ValidIndices_H(hg{fields.IndexList})
          ==> hg{fields.FieldSpec} == lg{fields.FieldSpec}
        }}
      ";
      str += "}\n";
      
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate GlobalsNoThreadOwnsMatch(ls: LPlusState, hs: HState)
        {
      ";
      if (fields.NumArrays > 0) {
        str += $"  forall {fields.IndexListWithoutLeadingComma} :: ";
      }
      str += $"  GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})";
      str += "}\n";
      
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate HighLevelStoreBuffersLackVar(hs: HState)
        {
          forall tid :: tid in hs.threads ==> StoreBufferLacksVar_H(hs.threads[tid].storeBuffer)
        }
      ";
      pgp.AddPredicate(str, "invariants");

      str = $@"
        predicate LocalViewsMatchSpecific(ls: LState, hs: HState, tid:Armada_ThreadHandle{fields.IndexParamList})
          requires tid in ls.threads
          requires tid in hs.threads
        {{
          var lg := L.Armada_GetThreadLocalView(ls, tid).globals;
          var hg := H.Armada_GetThreadLocalView(hs, tid).globals;
          && ValidIndices_L(lg{fields.IndexList})
          && ValidIndices_H(hg{fields.IndexList})
          ==> lg{fields.FieldSpec} == hg{fields.FieldSpec}
        }}
      ";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate OwnersLocalViewsMatch(ls: LPlusState, hs: HState)
        {
      ";
      str += $"  forall tid{fields.IndexList} ::\n";
      str += $"    tid in ls.s.threads && tid in hs.threads && {ownershipPredicate}(ls, tid{fields.IndexList}) ==> LocalViewsMatchSpecific(ls.s, hs, tid{fields.IndexList})\n";
      str += "}\n";
      pgp.AddPredicate(str, "invariants");

      str = @"
        predicate IntermediateRelation(ls: LPlusState, hs: HState)
        {
          && TotalStateMatchesExceptVar(ls.s, hs)
          && (ls.s.stop_reason.Armada_NotStopped? ==>
                && GlobalsNoThreadOwnsMatch(ls, hs)
                && HighLevelStoreBuffersLackVar(hs)
                && OwnersLocalViewsMatch(ls, hs)
             )
        }
      ";
      pgp.AddPredicate(str, "invariants");
    }

    private void GenerateTSOEliminationRequest()
    {
      var lplusstate = AH.ReferToType("LPlusState");
      var hstate = AH.ReferToType("HState");
      var handle = AH.ReferToType("Armada_ThreadHandle");
      var lstep = AH.ReferToType("LStep");
      var hstep = AH.ReferToType("HStep");
      var terequest = AH.MakeGenericTypeSpecific("TSOEliminationRequest", new List<Type> { lplusstate, hstate, handle, lstep, hstep });
      pgp.AddTypeSynonymDecl("TERequest", terequest, "defs");

      string str = @"
        function GetTSOEliminationRequest() : TERequest
        {
          TSOEliminationRequest(GetLPlusSpec(), GetHSpec(), GetLPlusHRefinementRelation(), InductiveInv, ConvertTotalState_LPlusH,
                                ConvertAndSuppressStepSequence, NextState_H, IntermediateRelation)
        }
      ";
      pgp.AddFunction(str, "defs");
    }

    private void GenerateInitialConditionsHoldLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      string str;

      str = $@"
        lemma lemma_InitImpliesIntermediateRelation(ls: LPlusState, hs: HState)
          requires LPlus_Init(ls)
          requires hs == ConvertTotalState_LPlusH(ls)
          ensures  IntermediateRelation(ls, hs)
        {{
          assert TotalStateMatchesExceptVar(ls.s, hs);
          forall tid{fields.IndexList} | tid in ls.s.threads
              ensures !{ownershipPredicate}(ls, tid{fields.IndexList})
          {{
          }}
          assert GlobalsNoThreadOwnsMatch(ls, hs);
          assert OwnersLocalViewsMatch(ls, hs);
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_InitialConditionsHold(ter:TERequest)
          requires ter == GetTSOEliminationRequest()
          ensures  InitialConditionsHold(ter)
        {
          forall ls | ls in ter.lspec.init
            ensures var hs := ter.initial_state_refiner(ls);
                    && hs in ter.hspec.init
                    && ter.intermediate_relation(ls, hs)
          {
            var hs := ter.initial_state_refiner(ls);
            var hconfig := ConvertConfig_LH(ls.config);

            lemma_ConvertTotalStatePreservesInit(ls.s, hs, ls.config, hconfig);
            assert H.Armada_InitConfig(hs, hconfig);
            lemma_InitImpliesIntermediateRelation(ls, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateEmptyStoreBufferLemmas()
    {
      string str;

      str = $@"
        lemma lemma_IfStoreBufferLacksIndicesThenViewMatches_L(mem: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>, mem': L.Armada_SharedMemory{fields.IndexParamList})
          requires StoreBufferLacksIndices_L(buf{fields.IndexList})
          requires ValidIndices_L(L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
          requires ValidIndices_L(mem.globals{fields.IndexList})
          requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
          ensures  mem'.globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
          decreases |buf|
        {{
          if |buf| > 0 {{
            var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
            assert mem_next.globals{fields.FieldSpec} == mem.globals{fields.FieldSpec};
            var mem_next' := L.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
            lemma_IfStoreBufferLacksIndicesThenViewMatches_L(mem_next, buf[1..], mem_next'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L({fields.IndexParamListWithoutLeadingComma})
          ensures forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry> ::
                    && StoreBufferLacksIndices_L(buf{fields.IndexList})
                    && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
                    && ValidIndices_L(mem.globals{fields.IndexList})
                    ==> L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
        {{
          forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry> |
            && StoreBufferLacksIndices_L(buf{fields.IndexList})
            && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
            && ValidIndices_L(mem.globals{fields.IndexList})
            ensures L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
          {{
            var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
            lemma_IfStoreBufferLacksIndicesThenViewMatches_L(mem, buf, mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_IfStoreBufferLacksIndicesThenViewMatches_H(mem: H.Armada_SharedMemory, buf: seq<H.Armada_StoreBufferEntry>, mem': H.Armada_SharedMemory{fields.IndexParamList})
          requires StoreBufferLacksVar_H(buf)
          requires ValidIndices_H(H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
          requires ValidIndices_H(mem.globals{fields.IndexList})
          requires mem' == H.Armada_ApplyStoreBuffer(mem, buf)
          ensures  mem'.globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
          decreases |buf|
        {{
          if |buf| > 0 {{
            var mem_next := H.Armada_ApplyStoreBufferEntry(mem, buf[0]);
            assert mem_next.globals{fields.FieldSpec} == mem.globals{fields.FieldSpec};
            var mem_next' := H.Armada_ApplyStoreBuffer(mem_next, buf[1..]);
            lemma_IfStoreBufferLacksIndicesThenViewMatches_H(mem_next, buf[1..], mem_next'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_H({fields.IndexParamListWithoutLeadingComma})
          ensures forall mem:H.Armada_SharedMemory, buf:seq<H.Armada_StoreBufferEntry> ::
                    && StoreBufferLacksVar_H(buf)
                    && ValidIndices_H(H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
                    && ValidIndices_H(mem.globals{fields.IndexList})
                    ==> H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
        {{
          forall mem:H.Armada_SharedMemory, buf:seq<H.Armada_StoreBufferEntry> |
            && StoreBufferLacksVar_H(buf)
            && ValidIndices_H(H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})
            && ValidIndices_H(mem.globals{fields.IndexList})
            ensures H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.FieldSpec} == mem.globals{fields.FieldSpec}
          {{
            var mem' := H.Armada_ApplyStoreBuffer(mem, buf);
            lemma_IfStoreBufferLacksIndicesThenViewMatches_H(mem, buf, mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");
    }

    private void GenerateValidIndicesLemmas()
    {
      string str;

      str = $@"
        lemma lemma_ValidIndicesUnaffectedByApplyStoreBuffer_L(
          mem: L.Armada_SharedMemory,
          buf:seq<L.Armada_StoreBufferEntry>,
          mem': L.Armada_SharedMemory{fields.IndexParamList}
          )
          requires mem' == L.Armada_ApplyStoreBuffer(mem, buf)
          ensures  ValidIndices_L(mem.globals{fields.IndexList}) <==> ValidIndices_L(mem'.globals{fields.IndexList})
          decreases |buf|
        {{
          if |buf| > 0 {{
            var mem_next := L.Armada_ApplyStoreBufferEntry(mem, buf[0]);
            lemma_ValidIndicesUnaffectedByApplyStoreBuffer_L(mem_next, buf[1..], mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexParamListWithoutLeadingComma})
          ensures forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>
                    {{:trigger L.Armada_ApplyStoreBuffer(mem, buf), ValidIndices_L(mem.globals{fields.IndexList})}}
                    {{:trigger ValidIndices_L(L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})}} ::
                    var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
                    ValidIndices_L(mem.globals{fields.IndexList}) <==> ValidIndices_L(mem'.globals{fields.IndexList});
        {{
          forall mem:L.Armada_SharedMemory, buf:seq<L.Armada_StoreBufferEntry>
            {{:trigger L.Armada_ApplyStoreBuffer(mem, buf), ValidIndices_L(mem.globals{fields.IndexList})}}
            {{:trigger ValidIndices_L(L.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})}}
            ensures var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
                    ValidIndices_L(mem.globals{fields.IndexList}) <==> ValidIndices_L(mem'.globals{fields.IndexList});
          {{
            var mem' := L.Armada_ApplyStoreBuffer(mem, buf);
            lemma_ValidIndicesUnaffectedByApplyStoreBuffer_L(mem, buf, mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_ValidIndicesUnaffectedByApplyStoreBuffer_H(
          mem: H.Armada_SharedMemory,
          buf:seq<H.Armada_StoreBufferEntry>,
          mem': H.Armada_SharedMemory{fields.IndexParamList}
          )
          requires mem' == H.Armada_ApplyStoreBuffer(mem, buf)
          ensures  ValidIndices_H(mem.globals{fields.IndexList}) <==> ValidIndices_H(mem'.globals{fields.IndexList})
          decreases |buf|
        {{
          if |buf| > 0 {{
            var mem_next := H.Armada_ApplyStoreBufferEntry(mem, buf[0]);
            lemma_ValidIndicesUnaffectedByApplyStoreBuffer_H(mem_next, buf[1..], mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_H({fields.IndexParamListWithoutLeadingComma})
          ensures forall mem:H.Armada_SharedMemory, buf:seq<H.Armada_StoreBufferEntry>
                    {{:trigger H.Armada_ApplyStoreBuffer(mem, buf), ValidIndices_H(mem.globals{fields.IndexList})}}
                    {{:trigger ValidIndices_H(H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})}} ::
                    var mem' := H.Armada_ApplyStoreBuffer(mem, buf);
                    ValidIndices_H(mem.globals{fields.IndexList}) <==> ValidIndices_H(mem'.globals{fields.IndexList});
        {{
          forall mem:H.Armada_SharedMemory, buf:seq<H.Armada_StoreBufferEntry>
            {{:trigger H.Armada_ApplyStoreBuffer(mem, buf), ValidIndices_H(mem.globals{fields.IndexList})}}
            {{:trigger ValidIndices_H(H.Armada_ApplyStoreBuffer(mem, buf).globals{fields.IndexList})}}
            ensures var mem' := H.Armada_ApplyStoreBuffer(mem, buf);
                    ValidIndices_H(mem.globals{fields.IndexList}) <==> ValidIndices_H(mem'.globals{fields.IndexList});
          {{
            var mem' := H.Armada_ApplyStoreBuffer(mem, buf);
            lemma_ValidIndicesUnaffectedByApplyStoreBuffer_H(mem, buf, mem'{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");
    }

    private void GenerateUnchangedLemmas()
    {
      string str;

      str = $@"
        lemma lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L(
          mem1:L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>{fields.IndexParamList}
          )
          requires ValidIndices_L(mem1.globals{fields.IndexList})
          requires ValidIndices_L(mem2.globals{fields.IndexList})
          requires ValidIndices_L(L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.IndexList})
          requires ValidIndices_L(L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.IndexList})
          requires mem1.globals{fields.FieldSpec} == mem2.globals{fields.FieldSpec}
          ensures  L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.FieldSpec} == L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.FieldSpec}
          decreases |buf|
        {{
          if |buf| > 0 {{
            var mem1' := L.Armada_ApplyStoreBufferEntry(mem1, buf[0]);
            var mem2' := L.Armada_ApplyStoreBufferEntry(mem2, buf[0]);
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L(mem1', mem2', buf[1..]{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");

      str = $@"
        lemma lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexParamListWithoutLeadingComma})
          ensures forall mem1:L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>
                    {{:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}} ::
                    && ValidIndices_L(mem1.globals{fields.IndexList})
                    && ValidIndices_L(mem2.globals{fields.IndexList})
                    && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.IndexList})
                    && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.IndexList})
                    && mem1.globals{fields.FieldSpec} == mem2.globals{fields.FieldSpec}
                    ==> L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.FieldSpec} == L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.FieldSpec}
        {{
          forall mem1:L.Armada_SharedMemory, mem2: L.Armada_SharedMemory, buf: seq<L.Armada_StoreBufferEntry>
            {{:trigger L.Armada_ApplyStoreBuffer(mem1, buf), L.Armada_ApplyStoreBuffer(mem2, buf)}} |
            && ValidIndices_L(mem1.globals{fields.IndexList})
            && ValidIndices_L(mem2.globals{fields.IndexList})
            && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.IndexList})
            && ValidIndices_L(L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.IndexList})
            && mem1.globals{fields.FieldSpec} == mem2.globals{fields.FieldSpec}
            ensures L.Armada_ApplyStoreBuffer(mem1, buf).globals{fields.FieldSpec} == L.Armada_ApplyStoreBuffer(mem2, buf).globals{fields.FieldSpec}
          {{
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchanged_L(mem1, mem2, buf{fields.IndexList});
          }}
        }}
      ";
      pgp.AddLemma(str, "tsoutil");
    }

    private void GenerateStoreBufferMatchesLemmas()
    {
      string str;

      str = @"
        lemma lemma_AppendVarToStoreBufferDoesntAffectMatch(
          lbuf: seq<L.Armada_StoreBufferEntry>,
          hbuf: seq<H.Armada_StoreBufferEntry>,
          entry: L.Armada_StoreBufferEntry
          )
          requires StoreBufferLocationConcernsVar_L(entry.loc)
          requires StoreBufferMatchesExceptVar(lbuf, hbuf)
          ensures StoreBufferMatchesExceptVar(lbuf + [entry], hbuf);
        {
          assert |lbuf| > 0 ==> lbuf + [entry] == [lbuf[0]] + (lbuf[1..] + [entry]);
      
          if |lbuf| == 0 {
          }
          else if StoreBufferLocationConcernsVar_L(lbuf[0].loc) {
            lemma_AppendVarToStoreBufferDoesntAffectMatch(lbuf[1..], hbuf, entry);
          }
          else {
            lemma_AppendVarToStoreBufferDoesntAffectMatch(lbuf[1..], hbuf[1..], entry);
          }
        }
      ";
      pgp.AddLemma(str, "tsoutil");

      str = @"
        lemma lemma_AppendVarToStoreBufferDoesntAffectMatchAlways()
          ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, hbuf: seq<H.Armada_StoreBufferEntry>, entry: L.Armada_StoreBufferEntry
                  {:trigger StoreBufferMatchesExceptVar(lbuf, hbuf), L.Armada_StoreBufferAppend(lbuf, entry)} ::
                  && StoreBufferLocationConcernsVar_L(entry.loc)
                  && StoreBufferMatchesExceptVar(lbuf, hbuf)
                  ==> StoreBufferMatchesExceptVar(L.Armada_StoreBufferAppend(lbuf, entry), hbuf)
        {
          forall lbuf: seq<L.Armada_StoreBufferEntry>, hbuf: seq<H.Armada_StoreBufferEntry>, entry: L.Armada_StoreBufferEntry
            {:trigger StoreBufferMatchesExceptVar(lbuf, hbuf), L.Armada_StoreBufferAppend(lbuf, entry)}
            | && StoreBufferLocationConcernsVar_L(entry.loc)
              && StoreBufferMatchesExceptVar(lbuf, hbuf)
            ensures StoreBufferMatchesExceptVar(L.Armada_StoreBufferAppend(lbuf, entry), hbuf)
          {
            lemma_AppendVarToStoreBufferDoesntAffectMatch(lbuf, hbuf, entry);
          }
        }
      ";
      pgp.AddLemma(str, "tsoutil");

      str = @"
        lemma lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatch(
          lbuf:seq<L.Armada_StoreBufferEntry>,
          lentry:L.Armada_StoreBufferEntry,
          hbuf:seq<H.Armada_StoreBufferEntry>,
          hentry:H.Armada_StoreBufferEntry
          )
          requires StoreBufferMatchesExceptVar(lbuf, hbuf)
          requires !StoreBufferLocationConcernsVar_L(lentry.loc)
          requires hentry == ConvertStoreBufferEntry_LH(lentry)
          ensures  StoreBufferMatchesExceptVar(lbuf + [lentry], hbuf + [hentry])
          decreases |lbuf| + |hbuf|;
        {
          var lbuf' := lbuf + [lentry];
          var hbuf' := hbuf + [hentry];
      
          assert |lbuf| > 0 ==> lbuf'[0] == lbuf[0] && lbuf'[1..] == lbuf[1..] + [lentry];
          assert |hbuf| > 0 ==> hbuf'[0] == hbuf[0] && hbuf'[1..] == hbuf[1..] + [hentry];
      
          if |lbuf| == 0 {
          }
          else if StoreBufferLocationConcernsVar_L(lbuf[0].loc) {
            lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatch(lbuf[1..], lentry, hbuf, hentry);
          }
          else {
            lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatch(lbuf[1..], lentry, hbuf[1..], hentry);
          }
        }
      ";
      pgp.AddLemma(str, "tsoutil");

      str = @"
        lemma lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatchAlways()
          ensures forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry, hbuf: seq<H.Armada_StoreBufferEntry>, hentry
                    {:trigger L.Armada_StoreBufferAppend(lbuf, lentry), H.Armada_StoreBufferAppend(hbuf, hentry)} ::
                    && hentry == ConvertStoreBufferEntry_LH(lentry)
                    && StoreBufferMatchesExceptVar(lbuf, hbuf)
                    && !StoreBufferLocationConcernsVar_L(lentry.loc)
                    ==> StoreBufferMatchesExceptVar(L.Armada_StoreBufferAppend(lbuf, lentry), H.Armada_StoreBufferAppend(hbuf, hentry))
        {
          forall lbuf: seq<L.Armada_StoreBufferEntry>, lentry, hbuf: seq<H.Armada_StoreBufferEntry>, hentry
            {:trigger L.Armada_StoreBufferAppend(lbuf, lentry), H.Armada_StoreBufferAppend(hbuf, hentry)} |
            && hentry == ConvertStoreBufferEntry_LH(lentry)
            && StoreBufferMatchesExceptVar(lbuf, hbuf)
            && !StoreBufferLocationConcernsVar_L(lentry.loc)
            ensures StoreBufferMatchesExceptVar(L.Armada_StoreBufferAppend(lbuf, lentry), H.Armada_StoreBufferAppend(hbuf, hentry))
          {
            lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatch(lbuf, lentry, hbuf, hentry);
          }
        }
      ";
      pgp.AddLemma(str, "tsoutil");
    }

    private void GenerateIntermediateRelationImpliesRelationLemma()
    {
      string str = @"
        lemma lemma_IntermediateRelationImpliesRelation(ter:TERequest)
          requires ter == GetTSOEliminationRequest()
          ensures  IntermediateRelationImpliesRelation(ter)
        {
          forall ls, hs | ter.intermediate_relation(ls, hs)
            ensures RefinementPair(ls, hs) in ter.relation
          {
            assert IntermediateRelation(ls, hs);
            assert LPlusHStateRefinement(ls, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularStepsLiftableLemma()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines) {
        var nextRoutineName = nextRoutine.NameSuffix;

        str = $@"
          lemma lemma_RegularStepLiftable_{nextRoutineName}(ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry, hs:HState)
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires OwnersLocalViewsMatch(ls, hs)
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            ensures  var hstep := ConvertTraceEntry_LH(lstep);
                     var hs' := H.Armada_GetNextStateAlways(hs, hstep);
                     H.Armada_NextOneStep(hs, hs', hstep)
          {{
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);
        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"    case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RegularStepLiftable_{nextRoutineName}(ls, ls', lstep, hs);\n";
      }

      str = $@"
        lemma lemma_RegularStepLiftable(ls:LPlusState, ls':LPlusState, lstep:L.Armada_TraceEntry, hs:HState)
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          ensures  var hstep := ConvertTraceEntry_LH(lstep);
                   var hs' := H.Armada_GetNextStateAlways(hs, hstep);
                   H.Armada_NextOneStep(hs, hs', hstep)
        {{
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          match lstep {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularStepMaintainsTotalStateMatchesExceptVar()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        var nextRoutineName = nextRoutine.NameSuffix;
        str = $@"
          lemma lemma_RegularStepMaintainsTotalStateMatchesExceptVar_{nextRoutineName}(
            ls: LPlusState,
            ls': LPlusState,
            lstep: L.Armada_TraceEntry,
            hs: HState,
            hs': HState,
            hstep: H.Armada_TraceEntry
            )
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires OwnersLocalViewsMatch(ls, hs)
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires H.Armada_NextOneStep(hs, hs', hstep)
            ensures  TotalStateMatchesExceptVar(ls'.s, hs')
          {{
            lemma_AppendVarToStoreBufferDoesntAffectMatchAlways();
            lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatchAlways();
            lemma_IfMapKeysMatchThenCardinalitiesMatch(ls.s.threads, hs.threads);
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);
        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"    case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RegularStepMaintainsTotalStateMatchesExceptVar_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep);\n";
      }

      str = $@"
        lemma lemma_RegularStepMaintainsTotalStateMatchesExceptVar(
          ls: LPlusState,
          ls': LPlusState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  TotalStateMatchesExceptVar(ls'.s, hs')
        {{
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          match lstep {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularStepMaintainsGlobalsNoThreadOwnsMatch()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        var nextRoutineName = nextRoutine.NameSuffix;
        str = $@"
          lemma lemma_RegularStepMaintainsGlobalsNoThreadOwnsMatchSpecific_{nextRoutineName}(
            ls: LPlusState,
            ls':LPlusState,
            lstep: L.Armada_TraceEntry,
            hs: HState,
            hs': HState,
            hstep: H.Armada_TraceEntry{fields.IndexParamList}
            )
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires H.Armada_NextOneStep(hs, hs', hstep)
            ensures  GlobalsNoThreadOwnsMatchSpecific(ls', hs'{fields.IndexList})
          {{
            var lg', hg' := ls'.s.mem.globals, hs'.mem.globals;
            var tid := lstep.tid;
            if NoThreadOwns(ls'{fields.IndexList}) && ValidIndices_L(lg'{fields.IndexList}) && ValidIndices_H(hg'{fields.IndexList}) {{
              assert !{ownershipPredicate}(ls', tid{fields.IndexList});
              if !{ownershipPredicate}(ls, tid{fields.IndexList}) {{
                forall any_tid | any_tid in ls.s.threads
                  ensures !{ownershipPredicate}(ls, any_tid{fields.IndexList})
                {{
                  assert !{ownershipPredicate}(ls', any_tid{fields.IndexList});
                  if any_tid != tid {{
                    assert ls'.s.threads[any_tid] == ls.s.threads[any_tid];
                  }}
                }}
                assert NoThreadOwns(ls{fields.IndexList});
              }}
              assert hg'{fields.FieldSpec} == lg'{fields.FieldSpec};
            }}
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);
        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"    case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RegularStepMaintainsGlobalsNoThreadOwnsMatchSpecific_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep{fields.IndexList});\n";
      }

      str = @"
        lemma lemma_RegularStepMaintainsGlobalsNoThreadOwnsMatch(
          ls: LPlusState,
          ls':LPlusState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  GlobalsNoThreadOwnsMatch(ls', hs')
        {
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          var lg', hg' := ls'.s.mem.globals, hs'.mem.globals;
      ";
      if (fields.NumArrays > 0) {
        str += $@"
          forall {fields.IndexListWithoutLeadingComma}
            ensures GlobalsNoThreadOwnsMatchSpecific(ls', hs'{fields.IndexList})
          {{
            assert GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList});
            match lstep {{
              { finalCases }
            }}
          }}
        ";
      }
      else {
        str += $@"
          assert GlobalsNoThreadOwnsMatchSpecific(ls, hs);
          match lstep {{
            { finalCases }
          }}
        ";
      }
      str += "}\n";
      pgp.AddLemma(str);
    }
    
    private void GenerateRegularStepMaintainsHighLevelStoreBuffersLackVar()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        var nextRoutineName = nextRoutine.NameSuffix;
        str = $@"
          lemma lemma_RegularStepMaintainsHighLevelStoreBuffersLackVar_{nextRoutineName}(
            ls: LPlusState,
            ls':LPlusState,
            lstep: L.Armada_TraceEntry,
            hs: HState,
            hs': HState,
            hstep: H.Armada_TraceEntry
            )
            requires InductiveInv(ls)
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires H.Armada_NextOneStep(hs, hs', hstep)
            ensures  HighLevelStoreBuffersLackVar(hs')
          {{
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);

        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $"  case Armada_TraceEntry_{nextRoutineName}(_{step_params}) => lemma_RegularStepMaintainsHighLevelStoreBuffersLackVar_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep);\n";
      }

      str = $@"
        lemma lemma_RegularStepMaintainsHighLevelStoreBuffersLackVar(
          ls: LPlusState,
          ls':LPlusState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  HighLevelStoreBuffersLackVar(hs')
        {{
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          match lstep {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularStepMaintainsOwnersLocalViewsMatch()
    {
      string str;

      string finalCases = "";

      foreach (var nextRoutine in pgp.symbolsLow.NextRoutines)
      {
        var nextRoutineName = nextRoutine.NameSuffix;
        str = $@"
          lemma {{:timeLimitMultiplier 2}} lemma_RegularStepMaintainsActingOwnersLocalViewsMatchSpecific_{nextRoutineName}(
            ls: LPlusState,
            ls':LPlusState,
            lstep: L.Armada_TraceEntry,
            hs: HState,
            hs': HState,
            hstep: H.Armada_TraceEntry{fields.IndexParamList}
            )
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires HighLevelStoreBuffersLackVar(hs')
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires H.Armada_NextOneStep(hs, hs', hstep)
            requires lstep.tid in ls'.s.threads
            requires lstep.tid in hs'.threads
            requires {ownershipPredicate}(ls', lstep.tid{fields.IndexList})
            ensures  LocalViewsMatchSpecific(ls'.s, hs', lstep.tid{fields.IndexList})
           {{
            var lg := L.Armada_GetThreadLocalView(ls.s, lstep.tid).globals;
            var hg := H.Armada_GetThreadLocalView(hs, lstep.tid).globals;
            var lg' := L.Armada_GetThreadLocalView(ls'.s, lstep.tid).globals;
            var hg' := H.Armada_GetThreadLocalView(hs', lstep.tid).globals;
            assert {ownershipPredicate}(ls, lstep.tid{fields.IndexList}) ==>
                   LocalViewsMatchSpecific(ls.s, hs, lstep.tid{fields.IndexList});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_ApplyStoreBufferCommutesWithAppendAlways_L();
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
            assert ls'.s.mem == ls.s.mem && lstep.tid in ls.s.threads && ls'.s.threads[lstep.tid].storeBuffer == ls.s.threads[lstep.tid].storeBuffer ==> lg' == lg;
            assert hs'.mem == hs.mem && lstep.tid in hs.threads && hs'.threads[lstep.tid].storeBuffer == hs.threads[lstep.tid].storeBuffer ==> hg' == hg;
            if ValidIndices_L(lg'{fields.IndexList}) && ValidIndices_H(hg'{fields.IndexList}) && ValidIndices_L(lg{fields.IndexList}) && ValidIndices_H(hg{fields.IndexList}) {{
              if lg'{fields.FieldSpec} == lg{fields.FieldSpec} {{
                assert hg'{fields.FieldSpec} == hg{fields.FieldSpec};
                assert hg{fields.FieldSpec} == lg{fields.FieldSpec};
                assert lg'{fields.FieldSpec} == hg'{fields.FieldSpec};
              }}
              else {{
                assert lg'{fields.FieldSpec} == hg'{fields.FieldSpec};
              }}
            }}
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);

        str = $@"
          lemma lemma_RegularStepMaintainsOtherOwnersLocalViewsMatchSpecific_{nextRoutineName}(
            ls: LPlusState,
            ls':LPlusState,
            lstep: L.Armada_TraceEntry,
            hs: HState,
            hs': HState,
            hstep: H.Armada_TraceEntry,
            other_tid:Armada_ThreadHandle{fields.IndexParamList}
            )
            requires InductiveInv(ls)
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires lstep.tid in ls.s.threads
            requires lstep.tid in hs.threads
            requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires HighLevelStoreBuffersLackVar(hs')
            requires LPlus_NextOneStep(ls, ls', lstep)
            requires lstep.Armada_TraceEntry_{nextRoutineName}?
            requires !IsSkippedTauStep(ls.s, hs, lstep)
            requires hstep == ConvertTraceEntry_LH(lstep)
            requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
            requires H.Armada_NextOneStep(hs, hs', hstep)
            requires other_tid in ls'.s.threads
            requires other_tid in hs'.threads
            requires other_tid != lstep.tid
            requires {ownershipPredicate}(ls', other_tid{fields.IndexList})
            requires !{ownershipPredicate}(ls', lstep.tid{fields.IndexList})
            ensures  LocalViewsMatchSpecific(ls'.s, hs', other_tid{fields.IndexList})
          {{
            assert {ownershipPredicate}(ls, other_tid{fields.IndexList});
            var lg' := L.Armada_GetThreadLocalView(ls'.s, other_tid).globals;
            var hg' := H.Armada_GetThreadLocalView(hs', other_tid).globals;
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            if ValidIndices_L(lg'{fields.IndexList}) && ValidIndices_H(hg'{fields.IndexList}) {{
              assert lg'{fields.FieldSpec} == hg'{fields.FieldSpec};
            }}
          }}
        ";
        pgp.AddLemma(str, "next_" + nextRoutineName);

        var step_params = String.Join("", nextRoutine.Formals.Select(f => $", _"));
        finalCases += $@"
          case Armada_TraceEntry_{nextRoutineName}(_{step_params}) =>
            if any_tid == lstep.tid {{
              lemma_RegularStepMaintainsActingOwnersLocalViewsMatchSpecific_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep{fields.IndexList});
            }}
            else {{
              lemma_RegularStepMaintainsOtherOwnersLocalViewsMatchSpecific_{nextRoutineName}(ls, ls', lstep, hs, hs', hstep, any_tid{fields.IndexList});
            }}
        ";
      }

      str = $@"
        lemma lemma_RegularStepMaintainsOwnersLocalViewsMatch(
          ls: LPlusState,
          ls':LPlusState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires HighLevelStoreBuffersLackVar(hs')
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  OwnersLocalViewsMatch(ls', hs')
        {{
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          forall any_tid{fields.IndexList}
            | any_tid in ls'.s.threads && {ownershipPredicate}(ls', any_tid{fields.IndexList})
            ensures LocalViewsMatchSpecific(ls'.s, hs', any_tid{fields.IndexList})
          {{
            assert any_tid != lstep.tid ==> !{ownershipPredicate}(ls', lstep.tid{fields.IndexList});
            match lstep {{
              { finalCases }
            }}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularStepMaintainsIntermediateRelation()
    {
      string str;

      str = @"
        lemma lemma_RegularStepMaintainsIntermediateRelation(
          ls: LPlusState,
          ls':LPlusState,
          lstep: L.Armada_TraceEntry,
          hs: HState,
          hs': HState,
          hstep: H.Armada_TraceEntry
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires !IsSkippedTauStep(ls.s, hs, lstep)
          requires hstep == ConvertTraceEntry_LH(lstep)
          requires hs' == H.Armada_GetNextStateAlways(hs, hstep)
          requires H.Armada_NextOneStep(hs, hs', hstep)
          ensures  IntermediateRelation(ls', hs')
        {
          assert ls.s.stop_reason.Armada_NotStopped?;
          lemma_RegularStepMaintainsTotalStateMatchesExceptVar(ls, ls', lstep, hs, hs', hstep);
          if ls'.s.stop_reason.Armada_NotStopped? {
            lemma_RegularStepMaintainsGlobalsNoThreadOwnsMatch(ls, ls', lstep, hs, hs', hstep);
            lemma_RegularStepMaintainsHighLevelStoreBuffersLackVar(ls, ls', lstep, hs, hs', hstep);
            lemma_RegularStepMaintainsOwnersLocalViewsMatch(ls, ls', lstep, hs, hs', hstep);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateSkippedTauStepMaintainsRelation()
    {
      string str;

      str = @"
        lemma lemma_SkippedTauStepMaintainsTotalStateMatchesExceptVar(
          ls:LPlusState,
          ls':LPlusState,
          lstep:L.Armada_TraceEntry,
          hs:HState
          )
          requires InductiveInv(ls)
          requires TotalStateMatchesExceptVar(ls.s, hs)
          requires lstep.tid in ls.s.threads
          requires lstep.tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires IsSkippedTauStep(ls.s, hs, lstep)
          ensures  TotalStateMatchesExceptVar(ls'.s, hs)
        {
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_SkippedTauStepMaintainsGlobalsNoThreadOwnsMatch(
          ls:LPlusState,
          ls':LPlusState,
          lstep:L.Armada_TraceEntry,
          hs:HState
          )
          requires InductiveInv(ls)
          requires TotalStateMatchesExceptVar(ls.s, hs)
          requires lstep.tid in ls.s.threads
          requires lstep.tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
          requires GlobalsNoThreadOwnsMatch(ls, hs)
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires IsSkippedTauStep(ls.s, hs, lstep)
          ensures  GlobalsNoThreadOwnsMatch(ls', hs)
        {
      ";
      if (fields.NumArrays > 0) {
        str += $"forall {fields.IndexListWithoutLeadingComma} ensures GlobalsNoThreadOwnsMatchSpecific(ls', hs{fields.IndexList}) {{\n";
      }
      str += $@"
            var tid := lstep.tid;
            assert L.Armada_ApplyStoreBuffer(ls.s.mem, ls.s.threads[tid].storeBuffer) ==
                   L.Armada_ApplyStoreBuffer(ls'.s.mem, ls'.s.threads[tid].storeBuffer);
      
            if NoThreadOwns(ls'{fields.IndexList}) {{
              forall tid | tid in ls.s.threads
                ensures !{ownershipPredicate}(ls, tid{fields.IndexList})
              {{
                assert !{ownershipPredicate}(ls', tid{fields.IndexList});
              }}
              assert NoThreadOwns(ls{fields.IndexList});
      
              var buf := ls.s.threads[tid].storeBuffer;
              var entry := buf[0];
              assert GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList});
        
              if StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList}) {{
                assert {ownershipPredicate}(ls, tid{fields.IndexList});
              }}
          }}
        }}
      ";
      if (fields.NumArrays > 0) {
        str += "}\n";
      }
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_SkippedTauStepMaintainsOwnersLocalViewsMatch(
          ls:LPlusState,
          ls':LPlusState,
          lstep:L.Armada_TraceEntry,
          hs:HState
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires lstep.tid in ls.s.threads
          requires lstep.tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, lstep.tid), H.Armada_GetThreadLocalView(hs, lstep.tid))
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires IsSkippedTauStep(ls.s, hs, lstep)
          ensures  OwnersLocalViewsMatch(ls', hs);
        {{
          var tid := lstep.tid;
          assert L.Armada_ApplyStoreBuffer(ls.s.mem, ls.s.threads[tid].storeBuffer) ==
                 L.Armada_ApplyStoreBuffer(ls'.s.mem, ls'.s.threads[tid].storeBuffer);
      
          forall any_tid{fields.IndexList} | any_tid in ls'.s.threads && {ownershipPredicate}(ls', any_tid{fields.IndexList})
            ensures LocalViewsMatchSpecific(ls'.s, hs, any_tid{fields.IndexList})
          {{
            if {ownershipPredicate}(ls', any_tid{fields.IndexList}) {{
              assert {ownershipPredicate}(ls, any_tid{fields.IndexList});
              assert LocalViewsMatchSpecific(ls.s, hs, any_tid{fields.IndexList});
              lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
              lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_H({fields.IndexListWithoutLeadingComma});
              lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            }}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_SkippedTauStepMaintainsRelation(
          ls:LPlusState,
          ls':LPlusState,
          lstep:L.Armada_TraceEntry,
          hs:HState
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires lstep.tid in ls.s.threads
          requires lstep.tid in hs.threads
          requires LPlus_NextOneStep(ls, ls', lstep)
          requires IsSkippedTauStep(ls.s, hs, lstep)
          ensures  IntermediateRelation(ls', hs)
        {
          var tid := lstep.tid;
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          lemma_SkippedTauStepMaintainsTotalStateMatchesExceptVar(ls, ls', lstep, hs);
          if ls'.s.stop_reason.Armada_NotStopped? {
            lemma_SkippedTauStepMaintainsGlobalsNoThreadOwnsMatch(ls, ls', lstep, hs);
            lemma_SkippedTauStepMaintainsOwnersLocalViewsMatch(ls, ls', lstep, hs);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateStepMaintainsRelation()
    {
      string str;

      str = @"
        lemma lemma_StepSequenceLiftable(ls:LPlusState, ls':LPlusState, lsteps:seq<L.Armada_TraceEntry>, hs:HState)
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          ensures  var hsteps := ConvertAndSuppressSteps(ls.s, hs, lsteps);
                   var hs' := ApplySteps_H(hs, hsteps);
                   Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          decreases |lsteps|
        {
          if |lsteps| > 0 {
            var ls_next := LPlus_GetNextStateAlways(ls, lsteps[0]);
            lemma_NextOneStepMaintainsInductiveInv(ls, ls_next, lsteps[0]);
            if IsSkippedTauStep(ls.s, hs, lsteps[0]) {
              lemma_SkippedTauStepMaintainsRelation(ls, ls_next, lsteps[0], hs);
              lemma_StepSequenceLiftable(ls_next, ls', lsteps[1..], hs);
            }
            else {
              var hstep := ConvertTraceEntry_LH(lsteps[0]);
              var hs_next := H.Armada_GetNextStateAlways(hs, hstep);
              lemma_RegularStepLiftable(ls, ls_next, lsteps[0], hs);
              lemma_RegularStepMaintainsIntermediateRelation(ls, ls_next, lsteps[0], hs, hs_next, hstep);
              lemma_StepSequenceLiftable(ls_next, ls', lsteps[1..], hs_next);
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StepSequenceMaintainsIntermediateRelation(
          ls: LPlusState,
          ls':LPlusState,
          lsteps: seq<L.Armada_TraceEntry>,
          hs: HState,
          hs': HState,
          hsteps: seq<H.Armada_TraceEntry>,
          tid: Armada_ThreadHandle,
          lpstates: seq<LPlusState>,
          hstates: seq<HState>
          )
          requires InductiveInv(ls)
          requires IntermediateRelation(ls, hs)
          requires Armada_NextMultipleSteps(LPlus_GetSpecFunctions(), ls, ls', lsteps)
          requires hsteps == ConvertAndSuppressSteps(ls.s, hs, lsteps)
          requires hs' == ApplySteps_H(hs, hsteps)
          requires Armada_NextMultipleSteps(H.Armada_GetSpecFunctions(), hs, hs', hsteps)
          requires forall step :: step in lsteps ==> step.tid == tid
          requires lpstates == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)
          requires forall i :: 0 < i < |lsteps| ==> !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lpstates[i], tid)
          requires hstates == Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hsteps);
          ensures  IntermediateRelation(ls', hs')
          ensures  forall i :: 0 < i < |hsteps| ==> !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
          decreases |lsteps|
        {
          if |lsteps| > 0 {
            var ls_next := LPlus_GetNextStateAlways(ls, lsteps[0]);
            lemma_NextOneStepMaintainsInductiveInv(ls, ls_next, lsteps[0]);

            // Help prove the inductive requirement
            var lpstates' := Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls_next, lsteps[1..]); 
            forall i | 0 < i < |lsteps[1..]| 
              ensures !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lpstates'[i], tid)
            {
              var j := i+1;
              assert 0 < j < |lsteps|;
              assert !Armada_ThreadYielding(LPlus_GetSpecFunctions(), lpstates[j], tid);
              assert lpstates'[i] == lpstates[i+1]; // OBSERVE: Help with sequence reasoning
            }

            if IsSkippedTauStep(ls.s, hs, lsteps[0]) {
              lemma_SkippedTauStepMaintainsRelation(ls, ls_next, lsteps[0], hs);
              lemma_StepSequenceMaintainsIntermediateRelation(ls_next, ls', lsteps[1..], hs, hs', hsteps, tid,
                                                              Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls_next, lsteps[1..]), hstates);
            }
            else {
              var hstep := ConvertTraceEntry_LH(lsteps[0]);
              var hs_next := H.Armada_GetNextStateAlways(hs, hstep);
              assert hstep == hsteps[0];
              lemma_RegularStepMaintainsIntermediateRelation(ls, ls_next, lsteps[0], hs, hs_next, hstep);
              lemma_StepSequenceMaintainsIntermediateRelation(ls_next, ls', lsteps[1..], hs_next, hs', hsteps[1..], tid,
                                                              Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls_next, lsteps[1..]),
                                                              Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs_next, hsteps[1..]));
              var lstates := Armada_GetStateSequence(L.Armada_GetSpecFunctions(), ls.s, lsteps);
              forall i | 0 < i < |hsteps|
                ensures !Armada_ThreadYielding(H.Armada_GetSpecFunctions(), hstates[i], tid)
              {
                var hstates' := Armada_GetStateSequence(H.Armada_GetSpecFunctions(), H.Armada_GetNextStateAlways(hs, hsteps[0]), hsteps[1..]);
                if i == 1 { 
                  assert lstates[i] == Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lsteps)[i].s;  // OBSERVE: Trigger a postcondition of LPlusSpec_GetStateSequence
                } else {
                  assert hstates[i] == hstates'[i-1];   // OBSERVE: Help with sequence reasoning
                } 
              }
            }
          }
        }
      ";
      pgp.AddLemma(str);

      str = @"
        lemma lemma_StepMaintainsRelation(ter:TERequest)
          requires ter == GetTSOEliminationRequest()
          ensures  StepMaintainsRelation(ter)
        {
          forall ls, ls', lstep, hs |
            && ter.inv(ls)
            && ter.intermediate_relation(ls, hs)
            && ActionTuple(ls, ls', lstep) in ter.lspec.next
            ensures var hstep := ter.step_refiner(ls, hs, lstep);
                    var hs' := ter.next_state(hs, hstep);
                    && ActionTuple(hs, hs', hstep) in ter.hspec.next
                    && ter.intermediate_relation(ls', hs')
          {
            var hstep := ter.step_refiner(ls, hs, lstep);
            var hs' := ter.next_state(hs, hstep);
            lemma_StepSequenceLiftable(ls, ls', lstep.steps, hs);
            lemma_StepSequenceMaintainsIntermediateRelation(ls, ls', lstep.steps, hs, hs', hstep.steps, lstep.tid,
                                                            Armada_GetStateSequence(LPlus_GetSpecFunctions(), ls, lstep.steps),
                                                            Armada_GetStateSequence(H.Armada_GetSpecFunctions(), hs, hstep.steps));
            lemma_ConvertAndSuppressStepsMaintainsMatching(ls.s, hs, lstep.tau, lstep.tid, lstep.steps);
            assert H.Armada_Next(hs, hs', hstep); // OBSERVE
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateValidRequestLemma()
    {
      string str = @"
        lemma lemma_ValidTSOEliminationRequest(ter:TERequest)
          requires ter == GetTSOEliminationRequest()
          ensures  ValidTSOEliminationRequest(ter);
        {
          lemma_InitialConditionsHold(ter);
          lemma_InductiveInvIsInvariant();
          lemma_IntermediateRelationImpliesRelation(ter);
          lemma_StepMaintainsRelation(ter);
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateFinalProof()
    {
      string str = @"
        lemma lemma_ProveRefinementViaTSOElimination()
          ensures SpecRefinesSpec(L.Armada_Spec(), H.Armada_Spec(), GetLHRefinementRelation())
        {
          var lspec := L.Armada_Spec();
          var hspec := H.Armada_Spec();
          var ter := GetTSOEliminationRequest();
    
          forall lb | BehaviorSatisfiesSpec(lb, lspec)
            ensures BehaviorRefinesSpec(lb, hspec, GetLHRefinementRelation())
          {
            var alb := lemma_GetLPlusAnnotatedBehavior(lb);
            lemma_ValidTSOEliminationRequest(ter);
            var ahb := lemma_PerformTSOElimination(ter, alb);
            assert BehaviorRefinesBehavior(alb.states, ahb.states, ter.relation);
            lemma_IfLPlusBehaviorRefinesBehaviorThenLBehaviorDoes(lb, alb.states, ahb.states);
            lemma_IfAnnotatedBehaviorSatisfiesSpecThenBehaviorDoes(ahb);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
