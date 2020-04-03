module util_functions_i {

  predicate RelationSatisfiableAt<T, U(!new)>(relation:(T,U)->bool, x:T)
  {
    exists y:U :: relation(x, y)
  }

  predicate RelationAlwaysSatisfiable<T(!new), U(!new)>(relation:(T,U)->bool)
  {
    forall x:T :: RelationSatisfiableAt(relation, x)
  }

  predicate FunctionSatisfiesRelation<T(!new), U(!new)>(f:T->U, relation:(T,U)->bool)
  {
    forall t:T :: relation(t, f(t))
  }

  function FunctionSatisfyingRelation<T(!new), U(!new)>(relation:(T,U)->bool) : (T->U)
    requires RelationAlwaysSatisfiable(relation)
  {
    (x:T) => var y :| assert RelationSatisfiableAt(relation, x); relation(x, y); y
  }

  /* Example use:
  predicate MyRelation(x:int, y:int)

  lemma SatisfyMyRelation(x:int) returns (y:int)
    ensures MyRelation(x, y)

  lemma ConstructFunctionSatisfyingMyRelation() returns (f:int->int)
    ensures FunctionSatisfiesRelation(f, MyRelation)
  {
    forall x:int
      ensures RelationSatisfiableAt(MyRelation, x)
    {
      var y := SatisfyMyRelation(x);
    }
    f := FunctionSatisfyingRelation(MyRelation);
  }
  */
  
}
