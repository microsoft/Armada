include "GeneralRefinementLemmas.i.dfy"

module RefinementConvolutionModule {

    import opened GeneralRefinementLemmasModule
    import opened GeneralRefinementModule
    import opened util_collections_seqs_s

    predicate RefinementRelationsConvolve<L(!new), M(!new), H(!new)>(
        lm_relation:RefinementRelation<L, M>,
        mh_relation:RefinementRelation<M, H>,
        lh_relation:RefinementRelation<L, H>
        )
    {
        forall l, m, h :: RefinementPair(l, m) in lm_relation && RefinementPair(m, h) in mh_relation ==> RefinementPair(l, h) in lh_relation
    }

    predicate RefinementRelationTransitive<T>(relation:RefinementRelation<T, T>)
    {
        RefinementRelationsConvolve(relation, relation, relation)
    }

    predicate BehaviorRefinesWhatOtherBehaviorRefines<LState, MState, HState(!new)>(
        lb:seq<LState>,
        mb:seq<MState>,
        lh_relation:RefinementRelation<LState, HState>,
        mh_relation:RefinementRelation<MState, HState>
        )
    {
        forall hb :: BehaviorRefinesBehavior(mb, hb, mh_relation) ==> BehaviorRefinesBehavior(lb, hb, lh_relation)
    }

    lemma lemma_RefinementConvolution<L, M, H>(
        lb:seq<L>,
        mb:seq<M>,
        hb:seq<H>,
        lm_relation:RefinementRelation<L, M>,
        mh_relation:RefinementRelation<M, H>,
        lh_relation:RefinementRelation<L, H>,
        lm_map:RefinementMap,
        mh_map:RefinementMap
        ) returns (
        lh_map:RefinementMap
        )
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, lm_relation, lm_map);
        requires BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, mh_relation, mh_map);
        requires RefinementRelationsConvolve(lm_relation, mh_relation, lh_relation);
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, lh_relation, lh_map);
    {
        if |lb| == 0 {
            lh_map := [];
            return;
        }

        if |lb| == 1 {
            lh_map := [ RefinementRange(0, |hb|-1) ];
            assert IsValidRefinementMap(|lb|, |hb|, lh_map);
            forall i, j {:trigger RefinementPair(lb[i], hb[j]) in lh_relation} |
                    0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |hb|
                ensures RefinementPair(lb[i], hb[j]) in lh_relation;
            {
                var k := lemma_RefinementMapIsReversible(|mb|, |hb|, mh_map, j);
                assert lm_map[i].first <= k <= lm_map[i].last;
                assert RefinementPair(lb[i], mb[k]) in lm_relation;
                assert RefinementPair(mb[k], hb[j]) in mh_relation;
            }
            return;
        }

        var lb', mb', lm_map' := lemma_GetPrefixOfBehaviorsAndRefinementMap(lb, mb, lm_map, lm_relation, |lb|-1);
        var mb'', hb', mh_map' := lemma_GetPrefixOfBehaviorsAndRefinementMap(mb, hb, mh_map, mh_relation, |mb'|);
        assert mb'' == mb';

        var lh_map' := lemma_RefinementConvolution(lb', mb', hb', lm_relation, mh_relation, lh_relation, lm_map', mh_map');

        var second_from_last := |lm_map|-2;
        assert    lm_map[second_from_last].last == lm_map[second_from_last+1].first
               || lm_map[second_from_last].last + 1 == lm_map[second_from_last+1].first;

        var new_first;
        var witness_to_correspondence;

        if lm_map[second_from_last].last == lm_map[second_from_last+1].first {
            new_first := last(lh_map').last;
            witness_to_correspondence := lm_map[second_from_last].last;
        }
        else {
            assert lm_map[second_from_last].last + 1 == lm_map[second_from_last+1].first;
            var k := lm_map[second_from_last].last;
            assert mh_map[k].last == mh_map[k+1].first || mh_map[k].last + 1 == mh_map[k+1].first;

            if mh_map[k].last == mh_map[k+1].first {
                new_first := last(lh_map').last;
                witness_to_correspondence := k+1;
            }
            else {
                assert mh_map[k].last + 1 == mh_map[k+1].first;
                new_first := last(lh_map').last + 1;
                witness_to_correspondence := lm_map[second_from_last+1].first;
            }
        }

        assert new_first == last(lh_map').last || new_first == last(lh_map').last + 1;
        assert lm_map[second_from_last+1].first <= witness_to_correspondence <= lm_map[second_from_last+1].last;
        assert mh_map[witness_to_correspondence].first <= new_first <= mh_map[witness_to_correspondence].last;

        lh_map := lh_map' + [ RefinementRange(new_first, |hb|-1) ];

        forall i | 0 <= i < |lh_map|-1
          ensures lh_map[i+1].first == lh_map[i].last || lh_map[i+1].first == lh_map[i].last + 1
        {
          if i < |lh_map|-2 {
            assert lh_map[i] == lh_map'[i];
            assert lh_map[i+1] == lh_map'[i+1];
            assert lh_map'[i+1].first == lh_map'[i].last || lh_map'[i+1].first == lh_map'[i].last + 1;
          }
          else {
            assert lh_map[i] == lh_map'[i];
            assert lh_map[i+1].first == new_first;
            assert lh_map[i+1].last == |hb|-1;
            assert lh_map[i+1].first == lh_map[i].last || lh_map[i+1].first == lh_map[i].last + 1;
          }
        }

        assert IsValidRefinementMap(|lb|, |hb|, lh_map);

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in lh_relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in lh_relation;
        {
            if i < |lb'| {
                assert lh_map'[i] == lh_map[i];
                assert lh_map'[i].first <= j <= lh_map'[i].last;
                assert RefinementPair(lb'[i], hb'[j]) in lh_relation;
            }
            else {
                assert lm_map[i] == lm_map[second_from_last+1];
                assert lm_map[i].first <= witness_to_correspondence <= lm_map[i].last;
                var mid := lemma_RefinementMapIsReversible(|mb|, |hb|, mh_map, j);
                assert mh_map[mid].first <= j <= mh_map[mid].last;

                if mid < witness_to_correspondence {
                    lemma_LaterFirstBeyondEarlierLastInRefinementMap(|mb|, |hb|, mh_map, mid, witness_to_correspondence);
                    assert new_first <= j <= mh_map[mid].last <= mh_map[witness_to_correspondence].first <= new_first;
                    assert j == new_first;
                    assert RefinementPair(lb[i], mb[witness_to_correspondence]) in lm_relation;
                    assert RefinementPair(mb[witness_to_correspondence], hb[j]) in mh_relation;
                }
                else {
                    assert RefinementPair(lb[i], mb[mid]) in lm_relation;
                    assert RefinementPair(mb[mid], hb[j]) in mh_relation;
                }
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, lh_relation, lh_map);
    }

    lemma lemma_RefinementConvolutionPure<L, M, H>(
        lb:seq<L>,
        mb:seq<M>,
        hb:seq<H>,
        lm_relation:RefinementRelation<L, M>,
        mh_relation:RefinementRelation<M, H>,
        lh_relation:RefinementRelation<L, H>
        )
        requires BehaviorRefinesBehavior(lb, mb, lm_relation);
        requires BehaviorRefinesBehavior(mb, hb, mh_relation);
        requires RefinementRelationsConvolve(lm_relation, mh_relation, lh_relation);
        ensures  BehaviorRefinesBehavior(lb, hb, lh_relation);
    {
        var lm_map :| BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, lm_relation, lm_map);
        var mh_map :| BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, mh_relation, mh_map);
        var lh_map := lemma_RefinementConvolution(lb, mb, hb, lm_relation, mh_relation, lh_relation, lm_map, mh_map);
    }

    lemma lemma_RefinementConvolutionTransitive<T>(
        lb:seq<T>,
        mb:seq<T>,
        hb:seq<T>,
        relation:RefinementRelation<T, T>
        )
        requires BehaviorRefinesBehavior(lb, mb, relation);
        requires BehaviorRefinesBehavior(mb, hb, relation);
        requires RefinementRelationTransitive(relation);
        ensures  BehaviorRefinesBehavior(lb, hb, relation);
    {
        lemma_RefinementConvolutionPure(lb, mb, hb, relation, relation, relation);
    }

    lemma lemma_EstablishBehaviorRefinesWhatOtherBehaviorRefines<LState, MState, HState>(
        lb:seq<LState>,
        mb:seq<MState>,
        lm_relation:RefinementRelation<LState, MState>,
        mh_relation:RefinementRelation<MState, HState>,
        lh_relation:RefinementRelation<LState, HState>
        )
        requires BehaviorRefinesBehavior(lb, mb, lm_relation);
        requires RefinementRelationsConvolve(lm_relation, mh_relation, lh_relation);
        ensures  BehaviorRefinesWhatOtherBehaviorRefines(lb, mb, lh_relation, mh_relation);
    {
        forall hb | BehaviorRefinesBehavior(mb, hb, mh_relation)
            ensures BehaviorRefinesBehavior(lb, hb, lh_relation);
        {
            lemma_RefinementConvolutionPure(lb, mb, hb, lm_relation, mh_relation, lh_relation);
        }
    }

}
