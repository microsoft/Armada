include "sets.i.dfy"

module util_collections_maps_i
{
  import opened util_collections_sets_i

    function AddSetToMap<K,V>(m:map<K,V>, ks:set<K>, v:V) : map<K,V>
      // requires forall k :: k in ks ==> !(k in m)
      ensures forall k :: k in m ==> k in AddSetToMap(m,ks,v) && AddSetToMap(m,ks,v)[k] == m[k]
      ensures forall k :: k in ks && k !in m ==> k in AddSetToMap(m,ks,v) && AddSetToMap(m,ks,v)[k] == v
    {
      map k | k in ks + m.Keys :: if k in m then m[k] else v
    }

    function MapMapToMap_internal<K, V1, V2>(m:map<K, V1>, f:V1->V2) : (m':map<K, V2>)
        ensures m'.Keys == m.Keys
        ensures forall k :: k in m' ==> m'[k] == f(m[k])
    {
        map k | k in m :: f(m[k])
    }

    lemma lemma_MapMapToMapMaintainsSize<K, V1, V2>(m: map<K, V1>, f:V1->V2)
        ensures |MapMapToMap_internal(m, f)| == |m|
    {
        var m' := MapMapToMap_internal(m, f);
        var keys := set k | k in m;
        var keys' := set k | k in m';
        assert keys' == keys;
        calc {
            |m'|;
            |keys'|;
            |keys|;
            |m|;
        }
    }

    function MapMapToMap<K, V1, V2>(m:map<K, V1>, f:V1->V2) : (m':map<K, V2>)
        ensures m'.Keys == m.Keys
        ensures forall k :: k in m' ==> m'[k] == f(m[k])
        ensures |m'| == |m|
    {
        lemma_MapMapToMapMaintainsSize(m, f);
        MapMapToMap_internal(m, f)
    }

    function Map2MapToMap_internal<K1(!new), V1, K2(!new), V2>(m:map<K1, V1>, fk:K1->K2, fk_inv:K2->K1, fv:V1->V2) : (m':map<K2, V2>)
        requires Inverses(fk, fk_inv)
    {
        var keys' := MapSetToSet(m.Keys, fk);
        map k | k in keys' :: fv(m[fk_inv(k)])
    }

    lemma lemma_SetExtensionality<T>(s1:set<T>, s2:set<T>)
        requires forall x :: x in s1 <==> x in s2
        ensures  s1 == s2
    {
    }

    lemma lemma_Map2MapToMap<K1(!new), V1, K2(!new), V2>(m:map<K1, V1>, fk:K1->K2, fk_inv:K2->K1, fv:V1->V2, m':map<K2, V2>)
        requires Inverses(fk, fk_inv)
        requires m' == Map2MapToMap_internal(m, fk, fk_inv, fv)
        ensures  m'.Keys == MapSetToSet(m.Keys, fk)
        ensures  forall k :: k in m' ==> m'[k] == fv(m[fk_inv(k)])
    {
        var keys' := MapSetToSet(m.Keys, fk);

        forall k | k in m'
            ensures k in keys'
            ensures m'[k] == fv(m[fk_inv(k)])
        {
        }

        lemma_SetExtensionality(m'.Keys, keys');
    }

    function Map2MapToMap<K1(!new), V1, K2(!new), V2>(m:map<K1, V1>, fk:K1->K2, fk_inv:K2->K1, fv:V1->V2) : (m':map<K2, V2>)
        requires Inverses(fk, fk_inv)
        ensures  m'.Keys == MapSetToSet(m.Keys, fk)
        ensures  forall k :: k in m' ==> m'[k] == fv(m[fk_inv(k)])
    {
        var m' := Map2MapToMap_internal(m, fk, fk_inv, fv);
        lemma_Map2MapToMap(m, fk, fk_inv, fv, m');
        m'
    }

    predicate MapHasUniqueKey<T, U>(m:map<T, U>, k:T)
    {
        && k in m
        && (forall k' :: k' in m ==> k' == k)
    }

    lemma EmptyMapPredicateInvalid<S, T>(m:map<S, T>, P:T->bool)
      requires |set x | x in m && P(m[x])| == 0
      ensures forall x :: x in m ==> ! P(m[x])
    {
      forall x | x in m
        ensures ! P(m[x])
      {
        if P(m[x]) {
          assert x in (set x | x in m && P(m[x]));
        }
      }
    }

    lemma lemma_IfMapKeysMatchThenCardinalitiesMatch<K, V1, V2>(m1:map<K, V1>, m2:map<K, V2>)
      requires forall k :: k in m1 <==> k in m2
      ensures  |m1| == |m2|
    {
      var keys1 := set k | k in m1;
      var keys2 := set k | k in m2;
      assert m1.Keys == keys1;
      assert m2.Keys == keys2;
      assert keys1 == keys2;
      calc {
        |m1|;
        |m1.Keys|;
        |keys1|;
        |keys2|;
        |m2.Keys|;
        |m2|;
      }
    }
}
