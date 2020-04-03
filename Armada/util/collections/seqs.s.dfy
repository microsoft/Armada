module util_collections_seqs_s
{
    function last<T>(s:seq<T>) : T
        requires |s| > 0;
    {
        s[|s|-1]
    }
    
    function all_but_last<T>(s:seq<T>) : seq<T>
        requires |s| > 0;
    {
        s[..|s|-1]
    }
} 
