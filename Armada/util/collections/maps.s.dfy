module util_collections_maps_s
{
    function mapdomain<KT,VT>(m:map<KT,VT>) : set<KT>
    {
        set k | k in m :: k
    }
    
    function mapremove<KT,VT>(m:map<KT,VT>, k:KT) : map<KT,VT>
    {
        map ki | ki in m && ki != k :: m[ki]
    }

    predicate maptotal<KT(!new),VT>(m:map<KT,VT>)
    {
        forall k {:trigger m[k]}{:trigger k in m} :: k in m
    }
    
    predicate imaptotal<KT(!new),VT>(m:imap<KT,VT>)
    {
        forall k {:trigger m[k]}{:trigger k in m} :: k in m
    }
} 
