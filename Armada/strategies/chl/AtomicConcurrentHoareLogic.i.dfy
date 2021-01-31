include "../../util/option.s.dfy"
include "../../util/collections/seqs.s.dfy"
include "../../util/collections/seqs.i.dfy"
include "../refinement/GeneralRefinementLemmas.i.dfy"
include "../refinement/RefinementConvolution.i.dfy"
include "../refinement/AnnotatedBehavior.i.dfy"
include "../invariants.i.dfy"
include "../generic/GenericArmadaLemmas.i.dfy"
include "../generic/LiftAtomicToAtomic.i.dfy"
include "ConcurrentHoareLogicSpec.i.dfy"
include "AtomicConcurrentHoareLogicLemmas.i.dfy"

module AtomicConcurrentHoareLogicModule {

  import opened util_option_s
  import opened util_collections_seqs_s
  import opened util_collections_seqs_i
  import opened GeneralRefinementModule
  import opened GeneralRefinementLemmasModule
  import opened RefinementConvolutionModule
  import opened AnnotatedBehaviorModule
  import opened InvariantsModule
  import opened ArmadaCommonDefinitions
  import opened GenericArmadaSpecModule
  import opened GenericArmadaLemmasModule
  import opened GenericArmadaAtomicModule
  import opened LiftAtomicToAtomicModule
  import opened ConcurrentHoareLogicSpecModule
  import opened AtomicConcurrentHoareLogicSpecModule
  import opened AtomicConcurrentHoareLogicLemmasModule

  lemma lemma_LiftAtomicToAtomicUsingCHLRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>(
    ar:AtomicConcurrentHoareLogicRequest<LState, LPath, LPC, LProc, HState, HPath, HPC>
    )
    requires IsValidAtomicConcurrentHoareLogicRequest(ar)
    ensures  SpecRefinesSpec(AtomicSpec(ar.l), AtomicSpec(ar.h), ar.relation)
  {
    var inv := ExtractInv(ar);
    var relation := ExtractLiftingRelation(ar);
    lemma_EstablishInitRequirements(ar, inv, relation);
    lemma_EstablishAtomicPathsLiftable(ar, inv, relation);
    lemma_LiftAtomicToAtomicGivenAtomicPathsLiftable(ar.l, ar.h, inv, relation, ar.relation);
  }

}
