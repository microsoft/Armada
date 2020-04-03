
module Math__mod_auto_i {

predicate eq_mod(x:int, y:int, n:int)
    requires n > 0;
{
    (x - y) % n == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
}

predicate ModAuto(n:int)
    requires n > 0;
{
    (n % n == (-n) % n == 0)
 && (forall x:int {:trigger (x % n) % n} :: (x % n) % n == x % n)
 && (forall x:int {:trigger x % n} :: 0 <= x < n <==> x % n == x)
 && (forall x:int, y:int {:trigger (x + y) % n} ::
                (var z := (x % n) + (y % n);
                    (  (0 <= z < n     && (x + y) % n == z)
                    || (n <= z < n + n && (x + y) % n == z - n))))
 && (forall x:int, y:int {:trigger (x - y) % n} ::
                (var z := (x % n) - (y % n);
                    (   (0 <= z < n && (x - y) % n == z)
                    || (-n <= z < 0 && (x - y) % n == z + n))))
}

lemma {:verify false} lemma_mod_auto(n:int)
    requires n > 0;
    ensures  ModAuto(n);
{
}

}
