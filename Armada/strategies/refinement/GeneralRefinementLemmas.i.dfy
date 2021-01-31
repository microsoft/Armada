include "../../spec/refinement.s.dfy"
include "../../util/collections/seqs.i.dfy"

module GeneralRefinementLemmasModule {

  import opened util_collections_seqs_i
  import opened util_collections_seqs_s
  import opened GeneralRefinementModule

  predicate RefinementRelationReflexive<T(!new)>(relation:RefinementRelation<T, T>)
  {
    forall x :: RefinementPair(x, x) in relation
  }

  lemma lemma_IfRefinementRelationReflexiveThenBehaviorRefinesItself<T>(b:seq<T>, relation:RefinementRelation<T, T>)
    requires |b| > 0
    requires RefinementRelationReflexive(relation)
    ensures  BehaviorRefinesBehavior(b, b, relation)
  {
    var lh_map := ConvertMapToSeq(|b|, map i | 0 <= i < |b| :: RefinementRange(i, i));
    assert BehaviorRefinesBehaviorUsingRefinementMap(b, b, relation, lh_map);
  }

  lemma lemma_LaterFirstBeyondEarlierLastInRefinementMap(
    low_level_behavior_size:int,
    high_level_behavior_size:int,
    lh_map:RefinementMap,
    i:int,
    j:int
    )
    requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map)
    requires 0 <= i <= j < low_level_behavior_size
    ensures  i < j ==> lh_map[i].last <= lh_map[j].first
    decreases j - i
  {
    if j == i || j == i + 1 {
      return;
    }
    
    lemma_LaterFirstBeyondEarlierLastInRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map, i+1, j);
  }

  lemma lemma_GetPrefixOfBehaviorsAndRefinementMap<L, H>(
    lb:seq<L>,
    hb:seq<H>,
    lh_map:RefinementMap,
    lh_relation:RefinementRelation<L, H>,
    new_low_behavior_size:int
    ) returns (
    lb':seq<L>,
    hb':seq<H>,
    lh_map':RefinementMap
    )
    requires BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, lh_relation, lh_map)
    requires 0 < new_low_behavior_size <= |lb|
    ensures  |lb'| == new_low_behavior_size
    ensures  lb' == lb[..new_low_behavior_size]
    ensures  lh_map' == lh_map[..new_low_behavior_size]
    ensures  new_low_behavior_size > 0 ==> 0 <= lh_map[new_low_behavior_size-1].last < |hb|
    ensures  if new_low_behavior_size > 0 then hb' == hb[ .. lh_map[new_low_behavior_size-1].last + 1] else hb' == []
    ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', lh_relation, lh_map')
  {
    if new_low_behavior_size == |lb| {
      lb' := lb;
      hb' := hb;
      lh_map' := lh_map;
      return;
    }
    
    var j := new_low_behavior_size - 1;
    assert lh_map[j].last == lh_map[j+1].first || lh_map[j].last == lh_map[j+1].first - 1;
    
    lb' := lb[..new_low_behavior_size];
    lh_map' := lh_map[..new_low_behavior_size];
    hb' := hb[.. last(lh_map').last+1];
    
    forall pair | pair in lh_map'
      ensures 0 <= pair.first <= pair.last < |hb'|;
    {
      var i :| 0 <= i < |lh_map'| && pair == lh_map'[i];
      lemma_LaterFirstBeyondEarlierLastInRefinementMap(|lb|, |hb|, lh_map, i, j);
    }
    
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', lh_relation, lh_map');
  }
  
  lemma lemma_RefinementMapIsReversible(
    low_level_behavior_size:int,
    high_level_behavior_size:int,
    lh_map:RefinementMap,
    hpos:int
    ) returns (
    lpos:int
    )
    requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map)
    requires 0 <= hpos < high_level_behavior_size
    ensures  0 <= lpos < low_level_behavior_size
    ensures  lh_map[lpos].first <= hpos <= lh_map[lpos].last
  {
    if last(lh_map).first <= hpos <= last(lh_map).last {
      lpos := |lh_map| - 1;
      return;
    }
    
    var j := |lh_map| - 2;
    assert lh_map[j+1].first == lh_map[j].last || lh_map[j+1].first == lh_map[j].last + 1;
    
    var new_low_level_behavior_size := low_level_behavior_size - 1;
    var lh_map' := lh_map[..new_low_level_behavior_size];
    var new_high_level_behavior_size := last(lh_map').last + 1;
    
    forall pair | pair in lh_map'
      ensures 0 <= pair.first <= pair.last < new_high_level_behavior_size;
    {
      var i :| 0 <= i < |lh_map'| && pair == lh_map'[i];
      lemma_LaterFirstBeyondEarlierLastInRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map, i, j);
    }
    
    assert IsValidRefinementMap(new_low_level_behavior_size, new_high_level_behavior_size, lh_map');
    lpos := lemma_RefinementMapIsReversible(new_low_level_behavior_size, new_high_level_behavior_size, lh_map', hpos);
  }
  
  lemma lemma_ConcatenatingBehaviorsPreservesRefinement<L, H>(
    lb1:seq<L>,
    lb2:seq<L>,
    hb1:seq<H>,
    hb2:seq<H>,
    relation:RefinementRelation<L, H>
    )
    requires BehaviorRefinesBehavior(lb1, hb1, relation)
    requires BehaviorRefinesBehavior(lb2, hb2, relation)
    ensures  BehaviorRefinesBehavior(lb1 + lb2, hb1 + hb2, relation)
  {
    var lh_map1 :| BehaviorRefinesBehaviorUsingRefinementMap(lb1, hb1, relation, lh_map1);
    var lh_map2 :| BehaviorRefinesBehaviorUsingRefinementMap(lb2, hb2, relation, lh_map2);
    var lh_map2_adjusted := MapSeqToSeq(lh_map2, (x:RefinementRange) => RefinementRange(x.first + |hb1|, x.last + |hb1|));
    var lh_map := lh_map1 + lh_map2_adjusted;
    var lb := lb1 + lb2;
    var hb := hb1 + hb2;
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorRightOne<T>(lb:seq<T>, hb:seq<T>, relation:RefinementRelation<T, T>, s:T)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementRelationReflexive(relation)
    ensures  BehaviorRefinesBehavior(lb + [s], hb + [s], relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

    var lb' := lb + [s];
    var hb' := hb + [s];
    var lh_map' := lh_map + [RefinementRange(|hb|, |hb|)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorRightOne_LH<T, U>(lb:seq<T>, hb:seq<U>, relation:RefinementRelation<T, U>, ls:T, hs:U)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementPair(ls, hs) in relation
    ensures  BehaviorRefinesBehavior(lb + [ls], hb + [hs], relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

    var lb' := lb + [ls];
    var hb' := hb + [hs];
    var lh_map' := lh_map + [RefinementRange(|hb|, |hb|)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorRightOne_LStutter<T, U>(lb:seq<T>, hb:seq<U>, relation:RefinementRelation<T, U>, hs:U)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementPair(last(lb), hs) in relation
    ensures  BehaviorRefinesBehavior(lb, hb + [hs], relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
    var last_range := last(lh_map);
    var last_range' := last_range.(last := |hb|);

    var hb' := hb + [hs];
    var lh_map' := lh_map[|lh_map|-1 := last_range'];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb', relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorRightOne_HStutter<T, U>(lb:seq<T>, hb:seq<U>, relation:RefinementRelation<T, U>, ls:T)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementPair(ls, last(hb)) in relation
    ensures  BehaviorRefinesBehavior(lb + [ls], hb, relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

    var lb' := lb + [ls];
    var lh_map' := lh_map + [RefinementRange(|hb|-1, |hb|-1)];
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb, relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorLeftOne<T>(lb:seq<T>, hb:seq<T>, relation:RefinementRelation<T, T>, s:T)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementRelationReflexive(relation)
    ensures  BehaviorRefinesBehavior([s] + lb, [s] + hb, relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

    var lb' := [s] + lb;
    var hb' := [s] + hb;
    var lh_map' := [RefinementRange(0, 0)] + MapSeqToSeq(lh_map, (x:RefinementRange) => RefinementRange(x.first+1, x.last+1));
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorLeftOne_LH<T, U>(lb:seq<T>, hb:seq<U>, relation:RefinementRelation<T, U>, ls:T, hs:U)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementPair(ls, hs) in relation
    ensures  BehaviorRefinesBehavior([ls] + lb, [hs] + hb, relation)
  {
    var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

    var lb' := [ls] + lb;
    var hb' := [hs] + hb;
    var lh_map' := [RefinementRange(0, 0)] + MapSeqToSeq(lh_map, (x:RefinementRange) => RefinementRange(x.first+1, x.last+1));
    assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', relation, lh_map');
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorRight<T>(lb:seq<T>, hb:seq<T>, relation:RefinementRelation<T, T>, eb:seq<T>)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementRelationReflexive(relation);
    ensures  BehaviorRefinesBehavior(lb + eb, hb + eb, relation)
    decreases |eb|
  {
    if |eb| == 0 {
      assert lb + eb == lb;
      assert hb + eb == hb;
    }
    else {
      lemma_ExtendBehaviorRefinesBehaviorRightOne(lb, hb, relation, eb[0]);
      lemma_ExtendBehaviorRefinesBehaviorRight(lb + [eb[0]], hb + [eb[0]], relation, eb[1..]);

      lemma_SequenceIsCarPlusCdr(eb);
      lemma_SequenceConcatenationAssociative(lb, [eb[0]], eb[1..]);
      lemma_SequenceConcatenationAssociative(hb, [eb[0]], eb[1..]);
    }
  }

  lemma lemma_ExtendBehaviorRefinesBehaviorLeft<T>(lb:seq<T>, hb:seq<T>, relation:RefinementRelation<T, T>, eb:seq<T>)
    requires BehaviorRefinesBehavior(lb, hb, relation)
    requires RefinementRelationReflexive(relation);
    ensures  BehaviorRefinesBehavior(eb + lb, eb + hb, relation)
    decreases |eb|
  {
    if |eb| == 0 {
      assert eb + lb == lb;
      assert eb + hb == hb;
    }
    else {
      lemma_ExtendBehaviorRefinesBehaviorLeftOne(lb, hb, relation, last(eb));
      lemma_ExtendBehaviorRefinesBehaviorLeft([last(eb)] + lb, [last(eb)] + hb, relation, all_but_last(eb));

      lemma_AllButLastPlusLastIsSeq(eb);
      lemma_SequenceConcatenationAssociative(all_but_last(eb), [last(eb)], lb);
      lemma_SequenceConcatenationAssociative(all_but_last(eb), [last(eb)], hb);
    }
  }

  lemma lemma_ExtendBehaviorSatisfiesSpecRightOne<State>(b:seq<State>, spec:Spec<State>, s':State)
    requires BehaviorSatisfiesSpec(b, spec)
    requires StatePair(last(b), s') in spec.next
    ensures  BehaviorSatisfiesSpec(b + [s'], spec)
  {
  }
    

}
