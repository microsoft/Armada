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
  public abstract class TSOField
  {
    public readonly string enclosingFieldSpec;

    public TSOField(string i_enclosingFieldSpec)
    {
      enclosingFieldSpec = i_enclosingFieldSpec;
    }

    public string EnclosingFieldSpec { get { return enclosingFieldSpec; } }
  }

  public class StructTSOField : TSOField
  {
    private ArmadaStruct outerStruct;
    private string fieldName;
    private int fieldPos;

    public StructTSOField(string i_enclosingFieldSpec, ArmadaStruct i_outerStruct, string i_fieldName, int i_fieldPos)
      : base(i_enclosingFieldSpec)
    {
      outerStruct = i_outerStruct;
      fieldName = i_fieldName;
      fieldPos = i_fieldPos;
    }

    public ArmadaStruct OuterStruct { get { return outerStruct; } }
    public string FieldName { get { return fieldName; } }
    public int FieldPos { get { return fieldPos; } }
  }

  public class ArrayTSOField : TSOField
  {
    private int whichArray;

    public ArrayTSOField(string i_enclosingFieldSpec, int i_whichArray) : base(i_enclosingFieldSpec)
    {
      whichArray = i_whichArray;
    }

    public int WhichArray { get { return whichArray; } }
  }

  public class TSOFieldList
  {
    private bool valid;
    private string varName;
    private Type varType;
    private List<TSOField> fields;
    private int numArrays;
    private string fieldSpec;
    private string indexList;
    private string indexParamList;
    private List<string> indexConstraints;

    public TSOFieldList(ProofGenerationParams pgp, TSOEliminationStrategyDecl strategy)
    {
      valid = false;

      if (!strategy.Fields.Any()) {
        AH.PrintError(pgp.prog, "No field list found in TSO elimination strategy description");
        return;
      }

      varName = strategy.Fields[0];
      ArmadaVariable v = pgp.symbolsLow.Globals.Lookup(varName);
      if (v == null) {
        AH.PrintError(pgp.prog, strategy.tok, $"No global variable named {varName}");
        return;
      }

      varType = v.ty;
      fieldSpec = $".{varName}";
      fields = new List<TSOField>();
      numArrays = 0;
      indexList = "";
      indexParamList = "";
      indexConstraints = new List<string>();

      Type currentType = varType;
      int strategyFieldsUsed = 1;
      while (true) {
        currentType = AddArrayFields(pgp, currentType);
        if (strategyFieldsUsed < strategy.Fields.Count) {
          currentType = AddStructField(pgp, strategy.tok, currentType, strategy.Fields[strategyFieldsUsed]);
          if (currentType == null) {
            return;
          }
          ++strategyFieldsUsed;
        }
        else {
          break;
        }
      }

      if (!AH.IsPrimitiveType(currentType)) {
        AH.PrintError(pgp.prog, "The field list given for the TSO-elimination strategy ends in the middle of a struct.  It has to go all the way to a primitive field.");
        return;
      }

      valid = true;
    }

    private Type AddArrayFields(ProofGenerationParams pgp, Type currentType)
    {
      if (!(currentType is SizedArrayType)) {
        return currentType;
      }

      var subtype = ((SizedArrayType)currentType).Range;
      var innerType = AddArrayFields(pgp, subtype);
      fields.Add(new ArrayTSOField(fieldSpec, numArrays));

      indexConstraints.Add($"0 <= idx{numArrays} < |g{fieldSpec}|");
      fieldSpec += $"[idx{numArrays}]";
      indexList += $", idx{numArrays}";
      indexParamList += $", idx{numArrays}:int";

      ++numArrays;

      return innerType;
    }

    private Type AddStructField(ProofGenerationParams pgp, Microsoft.Boogie.IToken strategyTok, Type currentType, string fieldName)
    {
      if (!(currentType is UserDefinedType)) {
        AH.PrintError(pgp.prog, strategyTok, $"Can't find field named {fieldName} in non-struct {currentType}");
        return null;
      }

      var structName = ((UserDefinedType)currentType).Name;
      ArmadaStruct s = pgp.symbolsLow.LookupStruct(structName);

      if (s == null) {
        AH.PrintError(pgp.prog, strategyTok, $"Can't find field named {fieldName} within non-struct {structName}");
        return null;
      }

      currentType = s.LookupFieldType(fieldName);
      if (currentType == null) {
        AH.PrintError(pgp.prog, strategyTok, $"No field named {fieldName} exists in struct {s.Name}");
        return null;
      }
      var fieldPos = s.GetFieldPos(fieldName);

      fields.Add(new StructTSOField(fieldSpec, s, fieldName, fieldPos));
      fieldSpec += $".{fieldName}";
      return currentType;
    }

    public bool Valid { get { return valid; } }
    public string GetVar() { return varName; }
    public Type GetVarType() { return varType; }
    public int NumFields { get { return fields.Count(); } }
    public TSOField GetField(int i) { return fields[i]; }
    public int NumArrays { get { return numArrays; } }
    public string FieldSpec { get { return fieldSpec; } }
    public string IndexList { get { return indexList; } }
    public string IndexParamList { get { return indexParamList; } }
    public string IndexListWithoutLeadingComma { get { return indexList.Length > 2 ? indexList.Substring(2) : ""; } }
    public string IndexParamListWithoutLeadingComma { get { return indexParamList.Length > 2 ? indexParamList.Substring(2) : ""; } }
    public List<string> IndexConstraints { get { return indexConstraints; } }
  }

  public class TSOEliminationNoConflictingOwnershipInvariantInfo : InvariantInfo
  {
    private TSOFieldList fields;
    private string ownershipPredicate;

    public TSOEliminationNoConflictingOwnershipInvariantInfo(TSOFieldList i_fields, string i_ownershipPredicate)
      : base("NoConflictingOwnership", "NoConflictingOwnership", new List<string>{ "InductiveInv" }, "", false)
    {
      fields = i_fields;
      ownershipPredicate = i_ownershipPredicate;
    }

    public override string GenerateSpecificNextLemma(ProofGenerationParams pgp, AtomicPath atomicPath,
                                                     IEnumerable<InvariantInfo> allInvariants, AtomicSpec atomicSpec,
                                                     bool onlyNonstoppingPaths)
    {
      string name = atomicPath.Name;
      string specificPathLemmaName = $"lemma_NoConflictingOwnershipPreservedByPath_{name}";

      var pr = new PathPrinter(atomicSpec);
      string str = $@"
        lemma {specificPathLemmaName}(s: LPlusState, s': LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(s)
          requires LAtomic_NextPath(s, s', path, tid)
          requires path.LAtomic_Path_{name}?
          ensures  NoConflictingOwnership(s')
        {{
          { pr.GetOpenValidPathInvocation(atomicPath) }
          ProofCustomizationGoesHere();
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

      return specificPathLemmaName;
    }
  }

  public class TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo : InvariantInfo
  {
    private TSOFieldList fields;
    private string ownershipPredicate;

    public TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo(TSOFieldList i_fields, string i_ownershipPredicate)
      : base("NonOwnersLackStoreBufferEntries", "NonOwnersLackStoreBufferEntries", new List<string>{ "InductiveInv" }, "", false)
    {
      fields = i_fields;
      ownershipPredicate = i_ownershipPredicate;
    }

    public override string GenerateSpecificNextLemma(ProofGenerationParams pgp, AtomicPath atomicPath,
                                                     IEnumerable<InvariantInfo> allInvariants, AtomicSpec atomicSpec,
                                                     bool onlyNonstoppingPaths)
    {
      string name = atomicPath.Name;
      string specificPathLemmaName = $"lemma_NonOwnersLackStoreBufferEntriesPreservedByPath_{name}";

      var pr = new PathPrinter(atomicSpec);

      string str = $@"
        lemma {specificPathLemmaName}(s: LPlusState, s': LPlusState, path: LAtomic_Path, tid: Armada_ThreadHandle)
          requires InductiveInv(s)
          requires LAtomic_NextPath(s, s', path, tid)
          requires path.LAtomic_Path_{name}?
          ensures  NonOwnersLackStoreBufferEntries(s')
        {{
          { pr.GetOpenValidPathInvocation(atomicPath) }
          ProofCustomizationGoesHere();
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

      return specificPathLemmaName;
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

      fields = new TSOFieldList(pgp, strategy);
      if (!fields.Valid) {
        return;
      }

      AddIncludesAndImports();
      MakeTrivialPCMap();
      GenerateNextRoutineMap();
      GenerateProofGivenMap();
    }

    ////////////////////////////////////////////////////////////////////////
    /// Includes and imports
    ////////////////////////////////////////////////////////////////////////

    protected override void AddIncludesAndImports()
    {
      base.AddIncludesAndImports();

      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.s.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/sets.i.dfy");
      pgp.MainProof.AddInclude(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy");

      pgp.MainProof.AddImport("InvariantsModule");
      pgp.MainProof.AddImport("util_option_s");
      pgp.MainProof.AddImport("util_collections_seqs_s");
      pgp.MainProof.AddImport("util_collections_seqs_i");
      pgp.MainProof.AddImport("util_collections_sets_i");
      pgp.MainProof.AddImport("util_collections_maps_i");
    }

    private void InitializeAuxiliaryProofFiles()
    {
      var tsoutilFile = pgp.proofFiles.CreateAuxiliaryProofFile("tsoutil");
      tsoutilFile.IncludeAndImportGeneratedFile("specs");
      tsoutilFile.IncludeAndImportGeneratedFile("convert");
      tsoutilFile.IncludeAndImportGeneratedFile("defs");
      tsoutilFile.IncludeAndImportGeneratedFile("invariants");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/option.s.dfy", "util_option_s");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/maps.i.dfy", "util_collections_maps_i");
      tsoutilFile.AddIncludeImport(ArmadaOptions.O.ArmadaCommonDefsPath + "/Armada/util/collections/seqs.i.dfy", "util_collections_seqs_i");
      tsoutilFile.AddImport("util_collections_seqs_s");
      pgp.proofFiles.MainProof.IncludeAndImportGeneratedFile("tsoutil");

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var nextFileName = "next_" + atomicPath.Name;
        var nextFile = pgp.proofFiles.CreateAuxiliaryProofFile(nextFileName);
        nextFile.IncludeAndImportGeneratedFile("specs");
        nextFile.IncludeAndImportGeneratedFile("revelations");
        nextFile.IncludeAndImportGeneratedFile("convert");
        nextFile.IncludeAndImportGeneratedFile("invariants");
        nextFile.IncludeAndImportGeneratedFile("defs");
        nextFile.IncludeAndImportGeneratedFile("tsoutil");
        nextFile.IncludeAndImportGeneratedFile("utility");
        nextFile.IncludeAndImportGeneratedFile("latomic");
        nextFile.IncludeAndImportGeneratedFile("hatomic");
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
      GenerateAtomicSpecs();
      GeneratePCFunctions_L();
      lAtomic.GeneratePCEffectLemmas();
      InitializeAuxiliaryProofFiles();
      AddStackMatchesMethodInvariant();
      GenerateOwnershipPredicate();
      GenerateStateAbstractionFunctions_LH();
      GenerateConvertStep_LH();
      GenerateConvertAtomicPath_LH();
      GenerateLocalViewCommutativityLemmas();
      GenerateStrategyInvariants();
      GenerateInvariantProof(pgp);
      GenerateGenericStoreBufferLemmas_L();
      GenerateEmptyStoreBufferLemmas();
      GenerateValidIndicesLemmas();
      GenerateUnchangedLemmas();
      GenerateStoreBufferMatchesLemmas();
      GenerateStatesMatchExceptPredicates();
      GenerateLiftingRelation();
      GenerateIsSkippedTauPath();
      GenerateRegularPathsLiftableLemma();
      GenerateRegularPathMaintainsTotalStateMatchesExceptVar();
      GenerateRegularPathMaintainsGlobalsNoThreadOwnsMatch();
      GenerateRegularPathMaintainsHighLevelStoreBuffersLackVar();
      GenerateRegularPathMaintainsOwnersLocalViewsMatch();
      GenerateRegularPathMaintainsLiftingRelation();
      GenerateSkippedTauPathMaintainsRelation();
      GenerateEstablishInitRequirementsLemma();
      GenerateEstablishStateOKRequirementLemma();
      GenerateEstablishRelationRequirementLemma();
      GenerateEstablishAtomicPathLiftableLemma();
      GenerateEstablishAtomicPathsLiftableLemma(true, false);
      GenerateLiftLAtomicToHAtomicLemma(true, false);
      GenerateFinalProof();
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
      pgp.AddPredicate(str, "defs");
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
      pgp.AddPredicate(str, "defs");
      AddInvariant(new TSOEliminationNonOwnersLackStoreBufferEntriesInvariantInfo(fields, ownershipPredicate));
    }

    private void GenerateOwnershipPredicate()
    {
      var str = $@"
        predicate OwnershipPredicate(s:LPlusState, tid:Armada_ThreadHandle{fields.IndexParamList})
        {{
          var threads := s.s.threads;
          var globals := s.s.mem.globals;
          var ghosts := s.s.ghosts;
          var tid_init := s.config.tid_init;
          { strategy.OwnershipPredicate }
        }}
      ";
      pgp.AddPredicate(str, "defs");
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
      str += $"  && loc.v.Armada_GlobalStaticVar_{fields.GetVar()}?\n";
      str += $"  && |loc.fields| == {fields.NumFields}\n";
      for (int i = 0; i < fields.NumFields; ++i) {
        f = fields.GetField(i);
        if (f is StructTSOField sf) {
          str += $"  && loc.fields[{i}] == {sf.FieldPos}\n";
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StoreBufferLocationConcernsVar_H(loc:H.Armada_StoreBufferLocation)
        {
          && loc.Armada_StoreBufferLocation_Unaddressable?
      ";
      str += $"  && loc.v.Armada_GlobalStaticVar_{fields.GetVar()}?\n";
      str += $"  && |loc.fields| == {fields.NumFields}\n";
      for (int i = 0; i < fields.NumFields; ++i) {
        f = fields.GetField(i);
        if (f is StructTSOField sf) {
          str += $"  && loc.fields[{i}] == {sf.FieldPos}\n";
        }
      }
      str += "  }\n";
      pgp.AddPredicate(str, "defs");

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
      pgp.AddPredicate(str, "defs");

      var preds = new List<string>();
      foreach (var varName in pgp.symbolsLow.Globals.VariableNames) {
        var v = pgp.symbolsLow.Globals.Lookup(varName);
        if (v is GlobalUnaddressableArmadaVariable && varName != fields.GetVar()) {
          preds.Add($"hglobals.{varName} == lglobals.{varName}");
        }
      }

      var indices = new List<string>();
      var indexConstraints = new List<string>();
      for (int i = 0; i < fields.NumFields; ++i) {
        f = fields.GetField(i);

        if (f is StructTSOField sf) {
          foreach (var otherFieldName in sf.OuterStruct.FieldNames) {
            if (otherFieldName != sf.FieldName) {
              if (indices.Any()) {
                preds.Add($@"
                  forall {AH.CombineStringsWithCommas(indices)} ::
                    {AH.CombineStringsWithAnd(indexConstraints)} ==>
                    hglobals{f.EnclosingFieldSpec}.{otherFieldName} == lglobals{f.EnclosingFieldSpec}.{otherFieldName}
                ");
              }
              else {
                preds.Add($"hglobals{f.EnclosingFieldSpec}.{otherFieldName} == lglobals{f.EnclosingFieldSpec}.{otherFieldName}");
              }
            }
          }
        }
        else if (f is ArrayTSOField af) {
          if (indices.Any()) {
            preds.Add($@"
              forall {AH.CombineStringsWithCommas(indices)} ::
                {AH.CombineStringsWithAnd(indexConstraints)} ==>
                |hglobals{f.EnclosingFieldSpec}| == |lglobals{f.EnclosingFieldSpec}|
            ");
          }
          else {
            preds.Add($"|hglobals{f.EnclosingFieldSpec}| == |lglobals{f.EnclosingFieldSpec}|");
          }
          indices.Add($"idx{af.WhichArray}");
          indexConstraints.Add($"0 <= idx{af.WhichArray} < |lglobals{f.EnclosingFieldSpec}|");
        }
      }

      str = $@"
        predicate GlobalsMatchesExceptVar(lglobals: L.Armada_Globals, hglobals: H.Armada_Globals)
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate SharedMemoryMatchesExceptVar(lmem: L.Armada_SharedMemory, hmem: H.Armada_SharedMemory)
        {
          && GlobalsMatchesExceptVar(lmem.globals, hmem.globals)
          && hmem.heap == lmem.heap
        }
      ";
      pgp.AddPredicate(str, "defs");

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
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StackMatchesExceptVar(lstack:seq<L.Armada_ExtendedFrame>, hstack:seq<H.Armada_ExtendedFrame>)
        {
          && |hstack| == |lstack|
          && (forall i :: 0 <= i < |lstack| ==> ExtendedFrameMatchesExceptVar(lstack[i], hstack[i]))
        }
      ";
      pgp.AddPredicate(str, "defs");

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
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate ThreadsMatchesExceptVar(lthreads:map<Armada_ThreadHandle, L.Armada_Thread>,
                                          hthreads:map<Armada_ThreadHandle, H.Armada_Thread>)
        {
          && (forall tid :: tid in lthreads <==> tid in hthreads)
          && (forall tid :: tid in lthreads ==> ThreadMatchesExceptVar(lthreads[tid], hthreads[tid]))
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate TotalStateMatchesExceptVar(ls:LState, hs:HState)
        {
          && hs.stop_reason == ls.stop_reason
          && ThreadsMatchesExceptVar(ls.threads, hs.threads)
          && SharedMemoryMatchesExceptVar(ls.mem, hs.mem)
          && hs.addrs == ConvertAddrs_LH(ls.addrs)
          && hs.ghosts == ConvertGhosts_LH(ls.ghosts)
          && hs.joinable_tids == ls.joinable_tids
        }
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate LocalViewsMatchExceptVar(ls:LState, hs:HState)
        {
          forall any_tid :: any_tid in ls.threads && any_tid in hs.threads ==>
            SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls, any_tid), H.Armada_GetThreadLocalView(hs, any_tid))
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    private void GenerateIsSkippedTauPath()
    {
      string str = @"
        predicate IsSkippedTauPath(ls: LPlusState, hs: HState, path: LAtomic_Path, tid: Armada_ThreadHandle)
        {
          && path.LAtomic_Path_Tau?
          && tid in ls.s.threads
          && |ls.s.threads[tid].storeBuffer| > 0
          && StoreBufferLocationConcernsVar_L(ls.s.threads[tid].storeBuffer[0].loc)
          && !(&& tid in hs.threads
               && |hs.threads[tid].storeBuffer| > 0
               && hs.threads[tid].storeBuffer[0] == ConvertStoreBufferEntry_LH(ls.s.threads[tid].storeBuffer[0])
               && StoreBufferMatchesExceptVar(ls.s.threads[tid].storeBuffer[1..], hs.threads[tid].storeBuffer[1..]))
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    protected override void GenerateLiftingRelation()
    {
      string str;

      str = $@"
        predicate NoThreadOwns(s: LPlusState{fields.IndexParamList})
        {{
          forall tid :: tid in s.s.threads ==> !{ownershipPredicate}(s, tid{fields.IndexList})
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = $@"
        predicate ValidIndices_L(g:L.Armada_Globals{fields.IndexParamList})
        {{
          {AH.CombineStringsWithAnd(fields.IndexConstraints)}
        }}
      ";
      str += "{\n";
      pgp.AddPredicate(str, "defs");

      str = $@"
        predicate ValidIndices_H(g:H.Armada_Globals{fields.IndexParamList})
        {{
          {AH.CombineStringsWithAnd(fields.IndexConstraints)}
        }}
      ";
      pgp.AddPredicate(str, "defs");

      var preds = new List<string>() { "StoreBufferLocationConcernsVar_L(loc)" };
      for (int i = 0; i < fields.NumFields; ++i) {
        if (fields.GetField(i) is ArrayTSOField af) {
          preds.Add($"loc.fields[{i}] == idx{af.WhichArray}");
        }
      }
      str = $@"
        predicate StoreBufferLocationConcernsIndices_L(loc:L.Armada_StoreBufferLocation{fields.IndexParamList})
        {{
          {AH.CombineStringsWithAnd(preds)}
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = $@"
        predicate StoreBufferLacksIndices_L(buf: seq<L.Armada_StoreBufferEntry>{fields.IndexParamList})
        {{
          forall entry :: entry in buf ==> !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList})
        }}
      ";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate StoreBufferLacksVar_H(buf: seq<H.Armada_StoreBufferEntry>)
        {
          forall entry :: entry in buf ==> !StoreBufferLocationConcernsVar_H(entry.loc)
        }
      ";
      pgp.AddPredicate(str, "defs");

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
      
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate GlobalsNoThreadOwnsMatch(ls: LPlusState, hs: HState)
        {
      ";
      if (fields.NumArrays > 0) {
        str += $"  forall {fields.IndexListWithoutLeadingComma} :: ";
      }
      str += $"  GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})";
      str += "}\n";
      
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate HighLevelStoreBuffersLackVar(hs: HState)
        {
          forall tid :: tid in hs.threads ==> StoreBufferLacksVar_H(hs.threads[tid].storeBuffer)
        }
      ";
      pgp.AddPredicate(str, "defs");

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
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate OwnersLocalViewsMatch(ls: LPlusState, hs: HState)
        {
      ";
      str += $"  forall tid{fields.IndexList} ::\n";
      str += $"    tid in ls.s.threads && tid in hs.threads && {ownershipPredicate}(ls, tid{fields.IndexList}) ==> LocalViewsMatchSpecific(ls.s, hs, tid{fields.IndexList})\n";
      str += "}\n";
      pgp.AddPredicate(str, "defs");

      str = @"
        predicate LiftingRelation(ls: LPlusState, hs: HState)
        {
          && TotalStateMatchesExceptVar(ls.s, hs)
          && (ls.s.stop_reason.Armada_NotStopped? ==>
                && GlobalsNoThreadOwnsMatch(ls, hs)
                && HighLevelStoreBuffersLackVar(hs)
                && OwnersLocalViewsMatch(ls, hs)
             )
        }
      ";
      pgp.AddPredicate(str, "defs");
    }

    protected override void GenerateEstablishInitRequirementsLemma()
    {
      GenerateLemmasHelpfulForProvingInitPreservation_LH();

      string str;

      str = $@"
        lemma lemma_InitImpliesLiftingRelation(ls: LPlusState, hs: HState)
          requires LPlus_Init(ls)
          requires hs == ConvertTotalState_LPlusH(ls)
          ensures  LiftingRelation(ls, hs)
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
        lemma lemma_EstablishInitRequirements(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          inv:LPlusState->bool,
          relation:(LPlusState, HState)->bool
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires inv == InductiveInv
          requires relation == LiftingRelation
          ensures  AtomicInitImpliesInv(lasf, inv)
          ensures  forall ls :: lasf.init(ls) ==> exists hs :: hasf.init(hs) && relation(ls, hs)
        {
          forall ls | lasf.init(ls)
            ensures inv(ls)
            ensures exists hs :: hasf.init(hs) && relation(ls, hs)
          {
            lemma_InitImpliesInductiveInv(ls);
            var hs := ConvertTotalState_LPlusH(ls);
            var hconfig := ConvertConfig_LH(ls.config);
            assert H.Armada_InitConfig(hs, hconfig);
            lemma_InitImpliesLiftingRelation(ls, hs);
            assert hasf.init(hs) && relation(ls, hs);
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

    private void GenerateRegularPathsLiftableLemma()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var name = atomicPath.Name;

        str = $@"
          lemma lemma_RegularPathLiftable_{name}(ls: LPlusState, ls': LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle, hs: HState)
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires OwnersLocalViewsMatch(ls, hs)
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            ensures  HAtomic_ValidPath(hs, ConvertAtomicPath_LH(lpath), tid)
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            var hpath := ConvertAtomicPath_LH(lpath);
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            { hpr.GetOpenPathInvocation(pathMap[atomicPath]) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "next_" + name);
        finalCases += $"    case LAtomic_Path_{name}(_) => lemma_RegularPathLiftable_{name}(ls, ls', lpath, tid, hs);\n";
      }

      str = $@"
        lemma lemma_RegularPathLiftable(ls: LPlusState, ls': LPlusState, lpath: LAtomic_Path, tid: Armada_ThreadHandle, hs: HState)
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          ensures  HAtomic_ValidPath(hs, ConvertAtomicPath_LH(lpath), tid)
        {{
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularPathMaintainsTotalStateMatchesExceptVar()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var name = atomicPath.Name;

        str = $@"
          lemma lemma_RegularPathMaintainsTotalStateMatchesExceptVar_{name}(
            ls: LPlusState,
            ls': LPlusState,
            lpath: LAtomic_Path,
            tid: Armada_ThreadHandle,
            hs: HState,
            hs': HState,
            hpath: HAtomic_Path
            )
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires OwnersLocalViewsMatch(ls, hs)
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            requires hpath == ConvertAtomicPath_LH(lpath)
            requires HAtomic_NextPath(hs, hs', hpath, tid)
            ensures  TotalStateMatchesExceptVar(ls'.s, hs')
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            lemma_AppendVarToStoreBufferDoesntAffectMatchAlways();
            lemma_AppendCorrespondingStoreBufferEntriesMaintainsMatchAlways();
            lemma_IfMapKeysMatchThenCardinalitiesMatch(ls.s.threads, hs.threads);
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            { hpr.GetOpenValidPathInvocation(pathMap[atomicPath]) }
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "next_" + name);
        finalCases += $"    case LAtomic_Path_{name}(_) => lemma_RegularPathMaintainsTotalStateMatchesExceptVar_{name}(ls, ls', lpath, tid, hs, hs', hpath);\n";
      }

      str = $@"
        lemma lemma_RegularPathMaintainsTotalStateMatchesExceptVar(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hs': HState,
          hpath: HAtomic_Path
          )
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_NextPath(hs, hs', hpath, tid)
          ensures  TotalStateMatchesExceptVar(ls'.s, hs')
        {{
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularPathMaintainsGlobalsNoThreadOwnsMatch()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      foreach (var atomicPath in lAtomic.AtomicPaths)
      {
        var name = atomicPath.Name;

        str = $@"
          lemma lemma_RegularPathMaintainsGlobalsNoThreadOwnsMatchSpecific_{name}(
            ls: LPlusState,
            ls':LPlusState,
            lpath: LAtomic_Path,
            tid: Armada_ThreadHandle,
            hs: HState,
            hs': HState,
            hpath: HAtomic_Path{fields.IndexParamList}
            )
            requires InductiveInv(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires hpath == ConvertAtomicPath_LH(lpath)
            requires HAtomic_NextPath(hs, hs', hpath, tid)
            ensures  GlobalsNoThreadOwnsMatchSpecific(ls', hs'{fields.IndexList})
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            { hpr.GetOpenValidPathInvocation(pathMap[atomicPath]) }
            var lg', hg' := ls'.s.mem.globals, hs'.mem.globals;
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            ProofCustomizationGoesHere();
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
        pgp.AddLemma(str, "next_" + name);
        finalCases += $"    case LAtomic_Path_{name}(_) => lemma_RegularPathMaintainsGlobalsNoThreadOwnsMatchSpecific_{name}(ls, ls', lpath, tid, hs, hs', hpath{fields.IndexList});\n";
      }

      str = @"
        lemma lemma_RegularPathMaintainsGlobalsNoThreadOwnsMatch(
          ls: LPlusState,
          ls':LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hs': HState,
          hpath: HAtomic_Path
          )
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_NextPath(hs, hs', hpath, tid)
          ensures  GlobalsNoThreadOwnsMatch(ls', hs')
        {
          var lg', hg' := ls'.s.mem.globals, hs'.mem.globals;
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
      ";
      if (fields.NumArrays > 0) {
        str += $@"
          forall {fields.IndexListWithoutLeadingComma}
            ensures GlobalsNoThreadOwnsMatchSpecific(ls', hs'{fields.IndexList})
          {{
            assert GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList});
            match lpath {{
              { finalCases }
            }}
          }}
        ";
      }
      else {
        str += $@"
          assert GlobalsNoThreadOwnsMatchSpecific(ls, hs);
          match lpath {{
            { finalCases }
          }}
        ";
      }
      str += "}\n";
      pgp.AddLemma(str);
    }
    
    private void GenerateRegularPathMaintainsHighLevelStoreBuffersLackVar()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var name = atomicPath.Name;

        str = $@"
          lemma lemma_RegularPathMaintainsHighLevelStoreBuffersLackVar_{name}(
            ls: LPlusState,
            ls':LPlusState,
            lpath: LAtomic_Path,
            tid: Armada_ThreadHandle,
            hs: HState,
            hs': HState,
            hpath: HAtomic_Path
            )
            requires InductiveInv(ls)
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            requires hpath == ConvertAtomicPath_LH(lpath)
            requires HAtomic_NextPath(hs, hs', hpath, tid)
            ensures  HighLevelStoreBuffersLackVar(hs')
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            { hpr.GetOpenValidPathInvocation(pathMap[atomicPath]) }
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            ProofCustomizationGoesHere();
          }}
        ";
        pgp.AddLemma(str, "next_" + name);
        finalCases += $"  case LAtomic_Path_{name}(_) => lemma_RegularPathMaintainsHighLevelStoreBuffersLackVar_{name}(ls, ls', lpath, tid, hs, hs', hpath);\n";
      }

      str = $@"
        lemma lemma_RegularPathMaintainsHighLevelStoreBuffersLackVar(
          ls: LPlusState,
          ls':LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hs': HState,
          hpath: HAtomic_Path
          )
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_NextPath(hs, hs', hpath, tid)
          ensures  HighLevelStoreBuffersLackVar(hs')
        {{
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          match lpath {{
            { finalCases }
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularPathMaintainsOwnersLocalViewsMatch()
    {
      string str;

      string finalCases = "";

      var lpr = new PrefixedVarsPathPrinter(lAtomic);
      var hpr = new PrefixedVarsPathPrinter(hAtomic);

      foreach (var atomicPath in lAtomic.AtomicPaths) {
        var name = atomicPath.Name;

        str = $@"
          lemma {{:timeLimitMultiplier {2 * atomicPath.NumNextRoutines + 2}}} lemma_RegularPathMaintainsActingOwnersLocalViewsMatchSpecific_{name}(
            ls: LPlusState,
            ls':LPlusState,
            lpath: LAtomic_Path,
            tid: Armada_ThreadHandle,
            hs: HState,
            hs': HState,
            hpath: HAtomic_Path{fields.IndexParamList}
            )
            requires InductiveInv(ls)
            requires InductiveInv(ls')
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires HighLevelStoreBuffersLackVar(hs')
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            requires hpath == ConvertAtomicPath_LH(lpath)
            requires HAtomic_NextPath(hs, hs', hpath, tid)
            requires tid in ls'.s.threads
            requires tid in hs'.threads
            requires {ownershipPredicate}(ls', tid{fields.IndexList})
            ensures  LocalViewsMatchSpecific(ls'.s, hs', tid{fields.IndexList})
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            { hpr.GetOpenValidPathInvocation(pathMap[atomicPath]) }
            var lg := L.Armada_GetThreadLocalView(ls.s, tid).globals;
            var hg := H.Armada_GetThreadLocalView(hs, tid).globals;
            var lg' := L.Armada_GetThreadLocalView(ls'.s, tid).globals;
            var hg' := H.Armada_GetThreadLocalView(hs', tid).globals;
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            ProofCustomizationGoesHere();
            assert {{:error ""The TSO elimination strategy doesn't allow going directly from a state where one thread has ownership to one where a different thread has ownership.  The owning thread must take a step that releases ownership.""}} !{ownershipPredicate}(ls, tid{fields.IndexList}) ==> NoThreadOwns(ls{fields.IndexList});
            assert {ownershipPredicate}(ls, tid{fields.IndexList}) ==> LocalViewsMatchSpecific(ls.s, hs, tid{fields.IndexList});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_ApplyStoreBufferCommutesWithAppendAlways_L();
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
            assert ls'.s.mem == ls.s.mem && tid in ls.s.threads && ls'.s.threads[tid].storeBuffer == ls.s.threads[tid].storeBuffer ==> lg' == lg;
            assert hs'.mem == hs.mem && tid in hs.threads && hs'.threads[tid].storeBuffer == hs.threads[tid].storeBuffer ==> hg' == hg;
            if ValidIndices_L(lg{fields.IndexList}) && ValidIndices_H(hg{fields.IndexList}) {{
              assert NoThreadOwns(ls{fields.IndexList}) ==> LocalViewsMatchSpecific(ls.s, hs, tid{fields.IndexList});
              assert hg{fields.FieldSpec} == lg{fields.FieldSpec};
        ";
        for (var i = 1; i <= atomicPath.NumNextRoutines; ++i) {
          str += $@"
              var lg{i} := L.Armada_GetThreadLocalView(lstates.s{i}.s, tid).globals;
              var hg{i} := H.Armada_GetThreadLocalView(hstates.s{i}, tid).globals;
              if ValidIndices_L(lg{i}{fields.IndexList}) && ValidIndices_H(hg{i}{fields.IndexList}) {{
                if lg{i}{fields.FieldSpec} == lg{fields.FieldSpec} {{
                  assert hg{i}{fields.FieldSpec} == hg{fields.FieldSpec};
                  assert lg{i}{fields.FieldSpec} == hg{i}{fields.FieldSpec};
                }}
                  else {{
                  assert lg{i}{fields.FieldSpec} == hg{i}{fields.FieldSpec};
                }}
              }}
          ";
        }
        str += $@"
              assert lg' == lg{atomicPath.NumNextRoutines};
              assert hg' == hg{atomicPath.NumNextRoutines};
            }}
          }}
        ";
        pgp.AddLemma(str, "next_" + name);

        str = $@"
          lemma lemma_RegularPathMaintainsOtherOwnersLocalViewsMatchSpecific_{name}(
            ls: LPlusState,
            ls':LPlusState,
            lpath: LAtomic_Path,
            tid: Armada_ThreadHandle,
            hs: HState,
            hs': HState,
            hpath: HAtomic_Path,
            other_tid:Armada_ThreadHandle{fields.IndexParamList}
            )
            requires InductiveInv(ls)
            requires NonOwnersLackStoreBufferEntries(ls)
            requires TotalStateMatchesExceptVar(ls.s, hs)
            requires tid in ls.s.threads
            requires tid in hs.threads
            requires GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList})
            requires OwnersLocalViewsMatch(ls, hs)
            requires HighLevelStoreBuffersLackVar(hs)
            requires ls.s.stop_reason.Armada_NotStopped?
            requires ls'.s.stop_reason.Armada_NotStopped?
            requires HighLevelStoreBuffersLackVar(hs')
            requires LAtomic_NextPath(ls, ls', lpath, tid)
            requires lpath.LAtomic_Path_{name}?
            requires !IsSkippedTauPath(ls, hs, lpath, tid)
            requires hpath == ConvertAtomicPath_LH(lpath)
            requires HAtomic_NextPath(hs, hs', hpath, tid)
            requires other_tid in ls'.s.threads
            requires other_tid in hs'.threads
            requires other_tid != tid
            requires {ownershipPredicate}(ls', other_tid{fields.IndexList})
            requires !{ownershipPredicate}(ls', tid{fields.IndexList})
            ensures  LocalViewsMatchSpecific(ls'.s, hs', other_tid{fields.IndexList})
          {{
            { lpr.GetOpenValidPathInvocation(atomicPath) }
            { hpr.GetOpenValidPathInvocation(pathMap[atomicPath]) }
            lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVarAlways();
            var lg' := L.Armada_GetThreadLocalView(ls'.s, other_tid).globals;
            var hg' := H.Armada_GetThreadLocalView(hs', other_tid).globals;
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_IfStoreBufferLacksIndicesThenViewMatchesAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            ProofCustomizationGoesHere();
            if ValidIndices_L(lg'{fields.IndexList}) && ValidIndices_H(hg'{fields.IndexList}) {{
              assert lg'{fields.FieldSpec} == hg'{fields.FieldSpec};
            }}
          }}
        ";
        pgp.AddLemma(str, "next_" + name);

        finalCases += $@"
          case LAtomic_Path_{name}(_) =>
            if any_tid == tid {{
              lemma_RegularPathMaintainsActingOwnersLocalViewsMatchSpecific_{name}(ls, ls', lpath, tid, hs, hs', hpath{fields.IndexList});
            }}
            else {{
              lemma_RegularPathMaintainsOtherOwnersLocalViewsMatchSpecific_{name}(ls, ls', lpath, tid, hs, hs', hpath, any_tid{fields.IndexList});
            }}
        ";
      }

      str = $@"
        lemma lemma_RegularPathMaintainsOwnersLocalViewsMatch(
          ls: LPlusState,
          ls':LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hs': HState,
          hpath: HAtomic_Path
          )
          requires InductiveInv(ls)
          requires InductiveInv(ls')
          requires LiftingRelation(ls, hs)
          requires ls.s.stop_reason.Armada_NotStopped?
          requires ls'.s.stop_reason.Armada_NotStopped?
          requires HighLevelStoreBuffersLackVar(hs')
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_NextPath(hs, hs', hpath, tid)
          ensures  OwnersLocalViewsMatch(ls', hs')
        {{
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          forall any_tid{fields.IndexList}
            | any_tid in ls'.s.threads && any_tid in hs'.threads && {ownershipPredicate}(ls', any_tid{fields.IndexList})
            ensures LocalViewsMatchSpecific(ls'.s, hs', any_tid{fields.IndexList})
          {{
            assert any_tid != tid ==> !{ownershipPredicate}(ls', tid{fields.IndexList});
            match lpath {{
              { finalCases }
            }}
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    private void GenerateRegularPathMaintainsLiftingRelation()
    {
      string str;

      str = @"
        lemma lemma_RegularPathMaintainsLiftingRelation(
          ls: LPlusState,
          ls':LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState,
          hs': HState,
          hpath: HAtomic_Path
          )
          requires InductiveInv(ls)
          requires InductiveInv(ls')
          requires LiftingRelation(ls, hs)
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires !IsSkippedTauPath(ls, hs, lpath, tid)
          requires hpath == ConvertAtomicPath_LH(lpath)
          requires HAtomic_NextPath(hs, hs', hpath, tid)
          ensures  LiftingRelation(ls', hs')
        {
          lemma_LAtomic_PathImpliesThreadRunning(ls, lpath, tid);
          lemma_RegularPathMaintainsTotalStateMatchesExceptVar(ls, ls', lpath, tid, hs, hs', hpath);
          if ls'.s.stop_reason.Armada_NotStopped? {
            lemma_RegularPathMaintainsGlobalsNoThreadOwnsMatch(ls, ls', lpath, tid, hs, hs', hpath);
            lemma_RegularPathMaintainsHighLevelStoreBuffersLackVar(ls, ls', lpath, tid, hs, hs', hpath);
            lemma_RegularPathMaintainsOwnersLocalViewsMatch(ls, ls', lpath, tid, hs, hs', hpath);
          }
        }
      ";
      pgp.AddLemma(str);
    }

    private void GenerateSkippedTauPathMaintainsRelation()
    {
      string str;

      var pr = new PrefixedVarsPathPrinter(lAtomic);

      str = $@"
        lemma lemma_SkippedTauPathMaintainsTotalStateMatchesExceptVar(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          )
          requires InductiveInv(ls)
          requires TotalStateMatchesExceptVar(ls.s, hs)
          requires tid in ls.s.threads
          requires tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, tid), H.Armada_GetThreadLocalView(hs, tid))
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires IsSkippedTauPath(ls, hs, lpath, tid)
          ensures  TotalStateMatchesExceptVar(ls'.s, hs)
        {{
          { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
          ProofCustomizationGoesHere();
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_SkippedTauPathMaintainsGlobalsNoThreadOwnsMatch(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          )
          requires InductiveInv(ls)
          requires TotalStateMatchesExceptVar(ls.s, hs)
          requires tid in ls.s.threads
          requires tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, tid), H.Armada_GetThreadLocalView(hs, tid))
          requires GlobalsNoThreadOwnsMatch(ls, hs)
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires IsSkippedTauPath(ls, hs, lpath, tid)
          ensures  GlobalsNoThreadOwnsMatch(ls', hs)
        {{
          { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
          ProofCustomizationGoesHere();
      ";
      if (fields.NumArrays > 0) {
        str += $"forall {fields.IndexListWithoutLeadingComma} ensures GlobalsNoThreadOwnsMatchSpecific(ls', hs{fields.IndexList}) {{\n";
      }
      str += $@"
            assert L.Armada_ApplyStoreBuffer(ls.s.mem, ls.s.threads[tid].storeBuffer) ==
                   L.Armada_ApplyStoreBuffer(ls'.s.mem, ls'.s.threads[tid].storeBuffer);
            var lg, lg', hg := ls.s.mem.globals, ls'.s.mem.globals, hs.mem.globals;
      
            if ValidIndices_L(lg'{fields.IndexList}) && ValidIndices_H(hg{fields.IndexList}) {{
              var buf := ls.s.threads[tid].storeBuffer;
              var entry := buf[0];
              if !StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList}) {{
                assert lg'{fields.FieldSpec} == lg{fields.FieldSpec};
              }}

              if NoThreadOwns(ls'{fields.IndexList}) {{
                forall any_tid | any_tid in ls.s.threads
                  ensures !{ownershipPredicate}(ls, any_tid{fields.IndexList})
                {{
                  assert !{ownershipPredicate}(ls', any_tid{fields.IndexList});
                }}
                assert NoThreadOwns(ls{fields.IndexList});
      
                assert GlobalsNoThreadOwnsMatchSpecific(ls, hs{fields.IndexList});
        
                if StoreBufferLocationConcernsIndices_L(entry.loc{fields.IndexList}) {{
                  assert {ownershipPredicate}(ls, tid{fields.IndexList});
                }}
             }}
          }}
        }}
      ";
      if (fields.NumArrays > 0) {
        str += "}\n";
      }
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_SkippedTauPathMaintainsOwnersLocalViewsMatch(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          )
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires tid in ls.s.threads
          requires tid in hs.threads
          requires SharedMemoryMatchesExceptVar(L.Armada_GetThreadLocalView(ls.s, tid), H.Armada_GetThreadLocalView(hs, tid))
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires IsSkippedTauPath(ls, hs, lpath, tid)
          ensures  OwnersLocalViewsMatch(ls', hs);
        {{
          { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
          ProofCustomizationGoesHere();
          assert L.Armada_ApplyStoreBuffer(ls.s.mem, ls.s.threads[tid].storeBuffer) ==
                 L.Armada_ApplyStoreBuffer(ls'.s.mem, ls'.s.threads[tid].storeBuffer);
      
          forall any_tid{fields.IndexList} | any_tid in ls'.s.threads && {ownershipPredicate}(ls', any_tid{fields.IndexList})
            ensures LocalViewsMatchSpecific(ls'.s, hs, any_tid{fields.IndexList})
          {{
            assert {ownershipPredicate}(ls, any_tid{fields.IndexList});
            assert LocalViewsMatchSpecific(ls.s, hs, any_tid{fields.IndexList});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_L({fields.IndexListWithoutLeadingComma});
            lemma_ValidIndicesUnaffectedByApplyStoreBufferAlways_H({fields.IndexListWithoutLeadingComma});
            lemma_IfVarUnchangedAndStoreBufferUnchangedThenViewUnchangedAlways_L({fields.IndexListWithoutLeadingComma});
            var loc := ls.s.threads[tid].storeBuffer[0].loc;
            if StoreBufferLocationConcernsIndices_L(loc{fields.IndexList}) {{
              assert LocalViewsMatchSpecific(ls'.s, hs, any_tid{fields.IndexList});
            }}
            else {{
              assert LocalViewsMatchSpecific(ls'.s, hs, any_tid{fields.IndexList});
            }}
          }}
        }}
      ";
      pgp.AddLemma(str);

      str = $@"
        lemma lemma_SkippedTauPathMaintainsRelation(
          ls: LPlusState,
          ls': LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          )
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires tid in ls.s.threads
          requires tid in hs.threads
          requires LAtomic_NextPath(ls, ls', lpath, tid)
          requires IsSkippedTauPath(ls, hs, lpath, tid)
          ensures  LiftingRelation(ls', hs)
        {{
          { pr.GetOpenValidPathInvocation(lAtomic.TauPath) }
          lemma_GlobalsMatchExceptVarImpliesLocalViewGlobalsMatchExceptVar(ls.s.mem, hs.mem, ls.s.threads[tid].storeBuffer,
                                                                           hs.threads[tid].storeBuffer);
          lemma_SkippedTauPathMaintainsTotalStateMatchesExceptVar(ls, ls', lpath, tid, hs);
          ProofCustomizationGoesHere();
          if ls'.s.stop_reason.Armada_NotStopped? {{
            lemma_SkippedTauPathMaintainsGlobalsNoThreadOwnsMatch(ls, ls', lpath, tid, hs);
            lemma_SkippedTauPathMaintainsOwnersLocalViewsMatch(ls, ls', lpath, tid, hs);
          }}
        }}
      ";
      pgp.AddLemma(str);
    }

    protected override void GenerateEstablishAtomicPathLiftableLemma()
    {
      string str = @"
        lemma lemma_EstablishAtomicPathLiftable(
          lasf:AtomicSpecFunctions<LPlusState, LAtomic_Path, L.Armada_PC>,
          hasf:AtomicSpecFunctions<HState, HAtomic_Path, H.Armada_PC>,
          ls: LPlusState,
          lpath: LAtomic_Path,
          tid: Armada_ThreadHandle,
          hs: HState
          ) returns (
          hpath: HAtomic_Path
          )
          requires lasf == LAtomic_GetSpecFunctions()
          requires hasf == HAtomic_GetSpecFunctions()
          requires InductiveInv(ls)
          requires LiftingRelation(ls, hs)
          requires LAtomic_ValidPath(ls, lpath, tid)
          requires !AtomicPathSkippable(lasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs)
          ensures  LiftAtomicPathSuccessful(lasf, hasf, InductiveInv, LiftingRelation, ls, lpath, tid, hs, hpath)
        {
          var inv := InductiveInv;
          var relation := LiftingRelation;
          var ls' := lasf.path_next(ls, lpath, tid);
          if IsSkippedTauPath(ls, hs, lpath, tid) {
            lemma_SkippedTauPathMaintainsRelation(ls, ls', lpath, tid, hs);
            lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath, tid);
            lemma_LAtomic_PathHasPCEffect_Tau(ls, lpath, tid);
            assert AtomicPathSkippable(lasf, inv, relation, ls, lpath, tid, hs);
            assert false;
          }
          else {
            var ls' := LAtomic_GetStateAfterPath(ls, lpath, tid);
            lemma_AtomicPathMaintainsInductiveInv(ls, ls', lpath,  tid);
            assert inv(ls');
            hpath := ConvertAtomicPath_LH(lpath);
            lemma_RegularPathLiftable(ls, ls', lpath, tid, hs);
            var hs' := HAtomic_GetStateAfterPath(hs, hpath, tid);
            lemma_RegularPathMaintainsLiftingRelation(ls, ls', lpath, tid, hs, hs', hpath);
            assert LiftAtomicPathSuccessful(lasf, hasf, inv, relation, ls, lpath, tid, hs, hpath);
          }
        }
      ";
      pgp.AddLemma(str);
    }
  }
}
