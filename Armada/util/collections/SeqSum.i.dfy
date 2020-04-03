module util_collections_SeqSum_i {

    function SeqSum(s:seq<int>) : int
    {
        if |s| == 0 then
            0
        else
            s[0] + SeqSum(s[1..])
    }

    lemma lemma_SeqSumNonNegativeIfAllElementsNonNegative(s:seq<int>)
        requires forall i :: 0 <= i < |s| ==> s[i] >= 0
        ensures  SeqSum(s) >= 0
    {
    }

    lemma lemma_SeqSumLessIfOneElementLessAndRestSame(s1:seq<int>, s2:seq<int>, pos:int)
        requires |s1| == |s2|
        requires 0 <= pos < |s1|
        requires forall i :: 0 <= i < |s1| && i != pos ==> s1[i] == s2[i]
        requires s1[pos] < s2[pos]
        ensures  SeqSum(s1) < SeqSum(s2)
    {
        if |s1| == 0 {
        }
        else if pos == 0 {
            assert s1[1..] == s2[1..];
        }
        else {
            lemma_SeqSumLessIfOneElementLessAndRestSame(s1[1..], s2[1..], pos-1);
        }
    }
    
}

    
