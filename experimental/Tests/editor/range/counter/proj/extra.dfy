module sets_helpers {

lemma Cardinality<T>(x:set<T>, y:set<T>)
    ensures x<y ==> |x|<|y|;
    ensures x<=y ==> |x|<=|y|;
{
    if (x!={}) {
        var e :| e in x;
        Cardinality(x-{e}, y-{e});
    }
}

}
