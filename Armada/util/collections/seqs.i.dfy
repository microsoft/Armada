include "../option.s.dfy"
include "seqs.s.dfy"

module util_collections_seqs_i
{
  import opened util_option_s
  import opened util_collections_seqs_s

  function {:opaque} ConvertMapToSeq<T>(n:int, m:map<int, T>) : seq<T>
    requires n >= 0;
    requires forall i {:trigger i in m} :: 0 <= i < n ==> i in m;
    ensures  |ConvertMapToSeq(n, m)| == n;
    ensures  var s := ConvertMapToSeq(n, m);
             forall i {:trigger s[i]} :: 0 <= i < n ==> s[i] == m[i];
  {
    if n == 0 then []
    else ConvertMapToSeq(n-1, m) + [m[n-1]]
  }

  function {:opaque} MapSeqToSeq<T, U>(s:seq<T>, f:T->U) : (s':seq<U>)
    ensures |s'| == |s|
    ensures forall i {:trigger s'[i]} {:trigger f(s[i])} :: 0 <= i < |s| ==> s'[i] == f(s[i])
  {
    if |s| == 0 then
      []
    else
      [f(s[0])] + MapSeqToSeq(s[1..], f)
  }

  lemma lemma_MapSeqToSeqDrop<T, U>(s:seq<T>, f:T->U, n:int)
    requires 0 <= n <= |s|
    ensures MapSeqToSeq(s, f)[n..] == MapSeqToSeq(s[n..], f)
  {
  }

  lemma lemma_MapSeqToSeqTake<T, U>(s:seq<T>, f:T->U, n:int)
    requires 0 <= n <= |s|
    ensures MapSeqToSeq(s, f)[..n] == MapSeqToSeq(s[..n], f)
  {
  }

  function FilterSeqToSeq<T>(s:seq<T>, f:T->bool) : (s':seq<T>)
    ensures forall x :: x in s' ==> f(x)
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + FilterSeqToSeq(s[1..], f)
    else
      FilterSeqToSeq(s[1..], f)
  }

  lemma FilterSeqToSeqDecreasesLength<T>(s:seq<T>, f:T->bool)
    ensures |FilterSeqToSeq(s, f)| <= |s|
  {
  }

  function FilterMapSeqToSeq<T, U>(s:seq<T>, f:T->Option<U>) : (s':seq<U>)
  {
    if |s| == 0 then
      []
    else if f(s[0]).Some? then
      [f(s[0]).v] + FilterMapSeqToSeq(s[1..], f)
    else
      FilterMapSeqToSeq(s[1..], f)
  }

  lemma lemma_FilterMapSeqsToSeq<T, U>(s1:seq<T>, s2:seq<T>, f:T->Option<U>)
    ensures FilterMapSeqToSeq(s1, f) + FilterMapSeqToSeq(s2, f) == FilterMapSeqToSeq(s1 + s2, f)
  {
    if |s1| == 0 {
      assert s2 == s1 + s2;
    }
    else {
      assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    }
  }

  lemma FilterMapSeqToSeq_FilterEmpty<T, U>(s: seq<T>, f: T->Option<U>)
    requires forall e :: e in s ==> f(e).None?
    ensures FilterMapSeqToSeq(s, f) == []
  {
    if |s| == 0 {

    }
    else {
      if (f(s[0]).Some?) {

      }
      else {
        FilterMapSeqToSeq_FilterEmpty(s[1..], f);
      }
    }
  }

  function RepeatingValue<T>(x:T, n:int) : (s:seq<T>)
    requires n >= 0
    ensures  |s| == n
    ensures  forall e :: e in s ==> e == x
    ensures  forall i :: 0 <= i < |s| ==> s[i] == x
  {
    if n == 0 then [] else [x] + RepeatingValue(x, n-1)
  }

  //////////////////////////////
  // UTILITY LEMMAS
  //////////////////////////////

  lemma lemma_SequenceIsCarPlusCdr<T>(s:seq<T>)
    requires |s| > 0
    ensures  s == [s[0]] + s[1..];
  {
  }

  lemma lemma_SequenceConcatenationAssociative<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>)
    ensures s1 + (s2 + s3) == (s1 + s2) + s3;
  {
  }

  lemma lemma_DroppingHeadOfConcatenation<T>(s1:seq<T>, s2:seq<T>)
    requires |s1| > 0
    ensures  s1[1..] + s2 == (s1 + s2)[1..]
  {
  }

  lemma lemma_IndexIntoDrop<T>(s:seq<T>, i:int, j:int)
    requires 0 <= i
    requires 0 <= j
    requires i + j < |s|
    ensures  s[i..][j] == s[i+j]
  {
  }

  lemma lemma_IndexIntoConcatenation<T>(s1:seq<T>, s2:seq<T>, i:int)
    requires 0 <= i < |s1| + |s2|
    ensures  (s1 + s2)[i] == if i < |s1| then s1[i] else s2[i-|s1|]
  {
  }

  lemma lemma_LastOfConcatenationIsLastOfLatter<T>(s1:seq<T>, s2:seq<T>)
    requires |s2| > 0
    ensures  last(s1 + s2) == last(s2)
  {
  }

  lemma lemma_AllButLastPlusLastIsSeq<T>(s:seq<T>)
    requires |s| > 0
    ensures  all_but_last(s) + [last(s)] == s
  {
  }

  lemma lemma_LastOfDropIsLast<T>(s:seq<T>, i:int)
    requires 0 <= i < |s|
    ensures  last(s[i..]) == last(s)
  {
  }

  lemma lemma_LastOfAllButLast<T>(s:seq<T>)
    requires |s| > 1
    ensures  last(all_but_last(s)) == s[|s|-2]
  {
  }

  lemma lemma_TakePlusDropIsSeq<T>(s:seq<T>, i:int)
    requires 0 <= i <= |s|
    ensures  s == s[..i] + s[i..]
  {
  }

  lemma lemma_SeqEqualsThreeWayConcatentation<T>(s:seq<T>, i:int, j:int)
    requires 0 <= i <= j <= |s|
    ensures  s == s[..i] + s[i..j] + s[j..]
  {
  }

  lemma lemma_DropMapSeqToSeq<T, U>(s:seq<T>, f:T->U, i:int)
    requires |s| >= i >= 0
    ensures  MapSeqToSeq(s[i..], f) == MapSeqToSeq(s, f)[i..]
    decreases i
  {
    var s1 := MapSeqToSeq(s[i..], f);
    var s2 := MapSeqToSeq(s, f)[i..];
    assert |s1| == |s2|;
    forall j | 0 <= j < |s1|
      ensures s1[j] == s2[j]
    {
      calc {
        s1[j];
        f(s[i..][j]);
          { lemma_IndexIntoDrop(s, i, j); }
        f(s[i+j]);
        MapSeqToSeq(s, f)[i+j];
          { lemma_IndexIntoDrop(MapSeqToSeq(s, f), i, j); }
        MapSeqToSeq(s, f)[i..][j];
        s2[j];
      }
    }
  }

}
