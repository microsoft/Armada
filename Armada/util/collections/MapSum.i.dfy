include "maps.s.dfy"
include "sets.i.dfy"

module util_collections_MapSum_i {

  import opened util_collections_maps_s
  import opened util_collections_sets_i

  lemma MapNonEmptyDomainNonEmpty<K, V>(m: map<K, V>)
    requires |m| > 0
    ensures |mapdomain(m)| > 0
  {
    var k :| k in m;
    assert k in mapdomain(m);
  }

  function chooseone<T>(m: set<T>): T
    requires |m| > 0
  {
    var k :| k in m;
    k
  }

  function MapSum<K, V>(m: map<K, V>, f:V->int): int
  {
    if |m| == 0 then
      0
    else
      MapNonEmptyDomainNonEmpty(m);
      var k := chooseone(mapdomain(m));
      var m0 := mapremove(m, k);
      f(m[k]) + MapSum(m0, f)
  }

  lemma lemma_MapSumNonNegativeIfAllElementsNonNegative<K, V>(m: map<K, V>, f:V->int)
    requires forall k :: k in m ==> f(m[k]) >= 0
    ensures  MapSum(m, f) >= 0
  {
  }

  lemma lemma_MapSumLessIfOneElementLessAndRestSame<K, V>(m1:map<K, V>, m2:map<K, V>, k: K, f:V->int)
    requires forall k :: k in m1 <==> k in m2
    requires k in m1
    requires forall k0 :: k0 != k && k0 in m1 ==> m1[k0] == m2[k0]
    requires f(m1[k]) < f(m2[k])
    ensures  MapSum(m1, f) < MapSum(m2, f)
  {
    assert (mapdomain(m1) == mapdomain(m2));
    if |m1| == 0 {
    }
    else {
      MapNonEmptyDomainNonEmpty(m1);
      MapNonEmptyDomainNonEmpty(m2);
      var k0 := chooseone(mapdomain(m1));
      if k0 == k {
        assert mapremove(m1, k0) == mapremove(m2, k0);
      }
      else {
        lemma_MapSumLessIfOneElementLessAndRestSame(mapremove(m1, k0), mapremove(m2, k0), k, f);
      }
    }
  }


  lemma lemma_MapSumLessOrEqualIfOneElementLessOrEqualAndRestSame<K, V>(m1:map<K, V>, m2:map<K, V>, k: K, f:V->int)
    requires forall k :: k in m1 <==> k in m2
    requires k in m1
    requires forall k0 :: k0 != k && k0 in m1 ==> m1[k0] == m2[k0]
    requires f(m1[k]) <= f(m2[k])
    ensures  MapSum(m1, f) <= MapSum(m2, f)
  {
    assert (mapdomain(m1) == mapdomain(m2));
    if |m1| == 0 {
    }
    else {
      MapNonEmptyDomainNonEmpty(m1);
      MapNonEmptyDomainNonEmpty(m2);
      var k0 := chooseone(mapdomain(m1));
      if k0 == k {
        assert mapremove(m1, k0) == mapremove(m2, k0);
      }
      else {
        lemma_MapSumLessOrEqualIfOneElementLessOrEqualAndRestSame(mapremove(m1, k0), mapremove(m2, k0), k, f);
      }
    }
  }
}
