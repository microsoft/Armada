using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  public class ResolutionContext
  {
    private readonly Expression lvalueState;
    private readonly Expression rvalueState;
    public readonly Expression tid;
    public readonly string methodName;
    public readonly ArmadaSymbolTable symbols;
    public readonly IFailureReporter failureReporter;
    public readonly string moduleName;

    public ResolutionContext(Expression i_lvalueState, Expression i_rvalueState, Expression i_tid, string i_methodName,
                             ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter, string i_moduleName = null)
    {
      lvalueState = i_lvalueState;
      rvalueState = i_rvalueState;
      tid = i_tid;
      methodName = i_methodName;
      symbols = i_symbols;
      failureReporter = i_failureReporter;
      moduleName = i_moduleName;
    }

    public virtual Expression GetLValueState()
    {
      if (lvalueState == null) {
        Fail("Can't get an lvalue state for this context");
      }
      return lvalueState;
    }

    public virtual Expression GetRValueState()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
      }
      return rvalueState;
    }

    public virtual Expression GetLValueTopStackFrame()
    {
      if (lvalueState == null) {
        Fail("Can't get an lvalue state for this context");
        return null;
      }
      var threads = AH.MakeExprDotName(lvalueState, "threads", AH.MakeThreadsType(moduleName));
      var thread = AH.MakeSeqSelectExpr(threads, tid, AH.MakeThreadType(moduleName));
      return AH.MakeExprDotName(thread, "top", AH.MakeStackFrameType(moduleName));
    }

    public virtual Expression GetRValueHeap()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      var fnName = AH.AddModuleToIdentifier(moduleName, "Armada_GetThreadLocalView");
      var locv = AH.MakeApply2(fnName, rvalueState, tid, AH.MakeSharedMemoryType(moduleName));
      return AH.MakeExprDotName(locv, "heap", "Armada_Heap");
    }

    public virtual Expression GetRValueGlobals()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      var fnName = AH.AddModuleToIdentifier(moduleName, "Armada_GetThreadLocalView");
      var locv = AH.MakeApply2(fnName, rvalueState, tid, AH.MakeSharedMemoryType(moduleName));
      return AH.MakeExprDotName(locv, "globals", AH.MakeGlobalsType(moduleName));
    }

    public virtual Expression GetRValueGhosts()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      return AH.MakeExprDotName(rvalueState, "ghosts", AH.MakeGhostsType(moduleName));
    }

    public virtual Expression GetRValueTopStackFrame()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      var threads = AH.MakeExprDotName(rvalueState, "threads", AH.MakeThreadsType(moduleName));
      var thread = AH.MakeSeqSelectExpr(threads, tid, AH.MakeThreadType(moduleName));
      return AH.MakeExprDotName(thread, "top", AH.MakeStackFrameType(moduleName));
    }

    public virtual ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      Fail(tok, "Can't use old() expression in this context");
      return null;
    }

    public void Fail(IToken tok, string reason) { failureReporter.Fail(tok, reason); }
    public void Fail(string reason) { failureReporter.Fail(reason); }

    public ArmadaRValue ResolveArmadaBinaryExpr(IToken tok, Type targetType, BinaryExpr.Opcode op,
                                                ArmadaRValue operand1, ArmadaRValue operand2)
    {
      UndefinedBehaviorAvoidanceConstraint crashAvoidance = operand1.UndefinedBehaviorAvoidance + operand2.UndefinedBehaviorAvoidance;

      // If this is a pointer plus or minus an integer, the semantics is that it produces undefined behavior unless
      // it stays within an array.

      if ((op == BinaryExpr.Opcode.Add || op == BinaryExpr.Opcode.Sub) && operand1.Val.Type is PointerType) {
        var pt = (PointerType)operand1.Val.Type;

        // operand1 in h.valid
        var h = GetRValueHeap();
        var valid_set = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());
        var operand1_valid = AH.MakeInExpr(operand1.Val, valid_set);
        crashAvoidance.Add(operand1_valid);

        // tree[operand1].field_of_parent.Armada_FieldArrayIndex?
        // (in other words, operand1 must be a child of its parent via an index field)
        var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
        var operand1_in_tree = AH.MakeInExpr(operand1.Val, tree);
        crashAvoidance.Add(operand1_in_tree);
        var operand1Node = AH.MakeSeqSelectExpr(tree, operand1.Val, "Armada_Node");
        var field_of_parent = AH.MakeExprDotName(operand1Node, "field_of_parent", "Armada_Field");
        crashAvoidance.Add(AH.MakeExprDotName(field_of_parent, "Armada_FieldArrayIndex?", new BoolType()));

        // Armada_FieldArrayIndex(field_of_parent.i <op> operand2) in tree[operand1.parent].children
        var index_of_parent = AH.MakeExprDotName(field_of_parent, "i", new IntType());
        var operand2val = AH.ConvertToIntIfNotInt(operand2.Val);
        var updated_index = AH.MakeBinaryExpr(op, index_of_parent, operand2val, "Armada_Pointer");
        var parent = AH.MakeExprDotName(operand1Node, "parent", "Armada_Pointer");
        crashAvoidance.Add(AH.MakeInExpr(parent, tree));
        var parentNode = AH.MakeSeqSelectExpr(tree, parent, "Armada_Node");
        var children = AH.MakeExprDotName(parentNode, "children", AH.MakeChildrenType());
        var updated_field = AH.MakeApply1("Armada_FieldArrayIndex", updated_index, "Armada_Field");
        crashAvoidance.Add(AH.MakeInExpr(updated_field, children));

        // child := tree[operand1.parent].children[Armada_FieldArrayIndex(field_of_parent.i + operand2)]
        var child = AH.MakeSeqSelectExpr(children, updated_field, operand1.Val.Type);
        return new ArmadaRValue(crashAvoidance, child);
      }

      // Order-based comparison of pointers is only allowed when they're in the same array.  The semantics for such a
      // comparison is that their indices within that array have the given comparison relationship.

      if ((op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge) &&
          (operand1.Val.Type is PointerType || operand2.Val.Type is PointerType))
      {
        if (!AH.TypesMatch(operand1.Val.Type, operand2.Val.Type)) {
          Fail(tok, "Can't compare a pointer to anything except a pointer of the same type");
          return null;
        }

        var h = GetRValueHeap();
        var valid_set = AH.MakeExprDotName(h, "valid", AH.MakePointerSetType());

        // It's undefined behavior if operand 1 or 2 isn't a valid pointer
        var operand1_valid = AH.MakeInExpr(operand1.Val, valid_set);
        crashAvoidance.Add(operand1_valid);
        var operand2_valid = AH.MakeInExpr(operand2.Val, valid_set);
        crashAvoidance.Add(operand2_valid);

        // It's undefined behavior if operand 1 or 2 isn't in the tree
        var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
        var operand1_in_tree = AH.MakeInExpr(operand1.Val, tree);
        crashAvoidance.Add(operand1_in_tree);
        var operand2_in_tree = AH.MakeInExpr(operand2.Val, tree);
        crashAvoidance.Add(operand2_in_tree);

        // It's undefined behavior if operand 1 or 2 isn't an array element
        var operand1Node = AH.MakeSeqSelectExpr(tree, operand1.Val, "Armada_Node");
        var field1_of_parent = AH.MakeExprDotName(operand1Node, "field_of_parent", "Armada_Field");
        crashAvoidance.Add(AH.MakeExprDotName(field1_of_parent, "Armada_FieldArrayIndex?", new BoolType()));
        var operand2Node = AH.MakeSeqSelectExpr(tree, operand2.Val, "Armada_Node");
        var field2_of_parent = AH.MakeExprDotName(operand2Node, "field_of_parent", "Armada_Field");
        crashAvoidance.Add(AH.MakeExprDotName(field2_of_parent, "Armada_FieldArrayIndex?", new BoolType()));

        // It's undefined behavior if operands 1 and 2 don't have the same parent
        var parent1 = AH.MakeExprDotName(operand1Node, "parent", "Armada_Pointer");
        var parent2 = AH.MakeExprDotName(operand2Node, "parent", "Armada_Pointer");
        crashAvoidance.Add(AH.MakeEqExpr(parent1, parent2));

        // The actual comparison is between the field indices of operands 1 and 2
        var idx1 = AH.MakeExprDotName(field1_of_parent, "i", new IntType());
        var idx2 = AH.MakeExprDotName(field2_of_parent, "i", new IntType());
        var result = AH.MakeBinaryExpr(op, idx1, idx2, new BoolType());
        return new ArmadaRValue(crashAvoidance, result);
      }

      if (op == BinaryExpr.Opcode.And) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + AH.MakeImpliesExpr(operand1.Val, operand2.UndefinedBehaviorAvoidance.Expr);
        }
      }
      else if (op == BinaryExpr.Opcode.Or) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + AH.MakeOrExpr(operand1.Val, operand2.UndefinedBehaviorAvoidance.Expr);
        }
      }
      else if (op == BinaryExpr.Opcode.Imp) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + AH.MakeImpliesExpr(operand1.Val, operand2.UndefinedBehaviorAvoidance.Expr);
        }
      }
      else if (op == BinaryExpr.Opcode.Exp) {
        if (operand1.CanCauseUndefinedBehavior) {
          crashAvoidance = operand2.UndefinedBehaviorAvoidance + AH.MakeImpliesExpr(operand2.Val, operand1.UndefinedBehaviorAvoidance.Expr);
        }
      }
      else if (op == BinaryExpr.Opcode.Div) {
        var div_by_zero = AH.MakeNeqExpr(operand2.Val, AH.MakeZero());
        crashAvoidance.Add(div_by_zero);
      }
      else if (op == BinaryExpr.Opcode.Mod) {
        var mod_by_zero = AH.MakeNeqExpr(operand2.Val, AH.MakeZero());
        crashAvoidance.Add(mod_by_zero);
      }

      /*
        It's undefined behavior to compare the value of a freed pointer (even if you don't dereference that value!)
        since our model of pointers doesn't capture the possibility of reusing the same location after it's freed.

        For example, consider the following code:

          void BadNews()
          {
            var p:ptr<int32>, q:ptr<int32>;
            p = malloc(int32);
            free(p);
            q = malloc(int32);
            free(q);
            if (p == q) { // Comparing a freed pointer
              *p := 0;
            }
          }

        If we didn't treat comparing the value of a freed pointer as undefined behavior, we'd model the above code as
        never crashing.  After all, in our model, pointers are never reused after being freed, so the verification would
        find p is always different from q, so the guard on the if is always false and the store to *p never happens.  In
        the compiled code, however, it could happen that the pointer was reused and p is equal to q.  In that case the
        assignment to *p would occur, and potentially crash.  We don't want the code crashing when verification says it
        won't, so we have to disallow looking at the values of freed pointers.
      */

      if (op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le ||
          op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge || op == BinaryExpr.Opcode.In || op == BinaryExpr.Opcode.NotIn)
      {
        var h = GetRValueHeap();

        if (operand1.Val.Type is PointerType) {
          crashAvoidance.Add(AH.MakeApply2("Armada_ComparablePointer", operand1.Val, h, "bool"));
        }
        if (operand2.Val.Type is PointerType) {
          crashAvoidance.Add(AH.MakeApply2("Armada_ComparablePointer", operand2.Val, h, "bool"));
        }
      }

      // Do appropriate conversions

      if (   op == BinaryExpr.Opcode.BitwiseAnd 
          || op == BinaryExpr.Opcode.BitwiseOr 
          || op == BinaryExpr.Opcode.BitwiseXor
          || op == BinaryExpr.Opcode.LeftShift
          || op == BinaryExpr.Opcode.RightShift
          ) {
        var name = "";
        if (op == BinaryExpr.Opcode.BitwiseAnd) {
          name = "bit_and_uint";
        } else if (op == BinaryExpr.Opcode.BitwiseOr) {
          name = "bit_or_uint";
        } else if (op == BinaryExpr.Opcode.BitwiseXor) {
          name = "bit_xor_uint";
        } else if (op == BinaryExpr.Opcode.LeftShift) {
          name = "bit_lshift_uint";
        } else if (op == BinaryExpr.Opcode.RightShift) {
          name = "bit_rshift_uint";
        }

        var bitwidth = AH.GetBitWidth(operand1.Val.Type as UserDefinedType);
        var e = AH.MakeFunctionCallExpr(tok, name + bitwidth,
          new List<Expression>() {operand1.Val, operand2.Val}, targetType);
        return new ArmadaRValue(crashAvoidance, e, targetType);
      }
      // For mathematical expressions, we should treat them as if
      else if (op == BinaryExpr.Opcode.In || op == BinaryExpr.Opcode.NotIn ||
               op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq) {
        var op1val = operand1.Val;
        var op2val = operand2.Val;
        var e = AH.MakeBinaryExpr(op, operand1.Val, operand2.Val, targetType);
        return new ArmadaRValue(crashAvoidance, e);
      }
      else {
        var op1val = AH.IsLimitedSizeIntType(operand1.Val.Type) ? AH.MakeConversionExpr(operand1.Val, new IntType()) : operand1.Val;
        var op2val = AH.IsLimitedSizeIntType(operand2.Val.Type) ? AH.MakeConversionExpr(operand2.Val, new IntType()) : operand2.Val;
        var e = AH.EnsureIntegerFit(new BinaryExpr(tok, op, op1val, op2val), targetType);
        return new ArmadaRValue(crashAvoidance, e);
      }
    }

    public ArmadaLValue ResolveArmadaDereferenceExprAsLValue(IToken tok, ArmadaRValue addr)
    {
      if (addr.Val.Type == null) {
        Fail(tok, "Attempt to dereference a value whose type isn't known");
        return null;
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addr.Val.Type, out subtype, out err)) {
        Fail(tok, err);
        return null;
      }

      return new AddressableArmadaLValue(tok, subtype, addr);
    }

    public ArmadaRValue ResolveArmadaDereferenceExprAsRValue(IToken tok, ArmadaRValue addr)
    {
      if (addr.Val.Type == null) {
        Fail(tok, "Attempt to dereference a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addr.Val.Type, out subtype, out err)) {
        Fail(tok, err);
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, subtype);
      if (valid == null) {
        Fail(tok, "Type {subtype} is not supported on the heap, and thus not for dereference operations");
        return new ArmadaRValue(null);
      }
      var crashAvoidance = addr.UndefinedBehaviorAvoidance + valid;

      var ret = AH.GetInvocationOfDereferencePointer(h, addr.Val, subtype);
      if (ret == null) {
        Fail(tok, "Type {subtype} is not supported on the heap, and thus not for dereference operations");
      }
      return new ArmadaRValue(crashAvoidance, ret);
    }

    public ArmadaRValue ResolveAllocatedExpr(IToken tok, ArmadaRValue addr)
    {
      if (addr.Val.Type == null) {
        Fail(tok, "Attempt to determine the allocated-ness of a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addr.Val.Type, out subtype, out err)) {
        Fail(tok, err);
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, subtype);
      if (valid == null) {
        Fail(tok, "Type {subtype} is not supported on the heap, and thus not for allocated() expressions");
        return new ArmadaRValue(null);
      }

      return new ArmadaRValue(addr.UndefinedBehaviorAvoidance, valid);
    }

    public ArmadaRValue ResolveAllocatedArrayExpr(IToken tok, ArmadaRValue addr)
    {
      if (addr.Val.Type == null) {
        Fail(tok, "Attempt to determine the allocated-array-ness of a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addr.Val.Type, out subtype, out err)) {
        Fail(tok, err);
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, subtype);
      if (valid == null) {
        Fail(tok, "Type {subtype} is not supported on the heap, and thus not for allocated_array() expressions");
        return new ArmadaRValue(null);
      }

      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      var node = AH.MakeSeqSelectExpr(tree, addr.Val, "Armada_Node");
      var field_of_parent = AH.MakeExprDotName(node, "field_of_parent", "Armada_Field");
      var is_array_field = AH.MakeExprDotName(field_of_parent, "Armada_FieldArrayIndex?", new BoolType());

      var parent = AH.MakeExprDotName(node, "parent", "Armada_Pointer");
      var parent_valid = AH.GetInvocationOfValidPointer(h, parent, new SizedArrayType(subtype, null));
      if (parent_valid == null) {
        Fail(tok, "Arrays of type {subtype} aren't supported on the heap, and thus can't be used for allocated_array() expressions");
        return new ArmadaRValue(null);
      }

      var res = AH.MakeAndExpr(valid, is_array_field);
      res = AH.MakeAndExpr(res, parent_valid);

      return new ArmadaRValue(addr.UndefinedBehaviorAvoidance, res);
    }

    private Attributes ResolveAttributes(Attributes attrs)
    {
      if (attrs == null) {
        return null;
      }

      var prev = ResolveAttributes(attrs.Prev);

      if (attrs.Name == "trigger") {
        var args = attrs.Args.Select(arg => ResolveAsRValue(arg).Val).ToList();
        return new Attributes(attrs.Name, args, prev);
      }
      else {
        return new Attributes(attrs.Name, attrs.Args, prev);
      }
    }

    private static Attributes CullAttributesToTriggersOnly(Attributes attrs)
    {
      if (attrs == null) {
        return null;
      }

      var prev = CullAttributesToTriggersOnly(attrs.Prev);
      if (attrs.Name == "trigger") {
        return new Attributes(attrs.Name, attrs.Args, prev);
      }
      else {
        return prev;
      }
    }

    private static UndefinedBehaviorAvoidanceConstraint GetQuantifiedUndefinedBehaviorAvoidanceConstraint(
      ArmadaRValue range,
      ArmadaRValue term,
      List<TypeParameter> typeArgs,
      List<BoundVar> bvars,
      Attributes attrs
      )
    {
      Expression crashExpr = null;
      if (range != null && range.CanCauseUndefinedBehavior) {
        if (term.CanCauseUndefinedBehavior) {
          crashExpr = AH.MakeAndExpr(range.UndefinedBehaviorAvoidance.Expr, AH.MakeImpliesExpr(range.Val, term.UndefinedBehaviorAvoidance.Expr));
        }
        else {
          crashExpr = range.UndefinedBehaviorAvoidance.Expr;
        }
      }
      else if (term.CanCauseUndefinedBehavior) {
        if (range != null && range.Val != null) {
          crashExpr = AH.MakeImpliesExpr(range.Val, term.UndefinedBehaviorAvoidance.Expr);
        }
        else {
          crashExpr = term.UndefinedBehaviorAvoidance.Expr;
        }
      }

      // No matter what kind of quantified expression it is, forall or exists, to avoid crashing it must be true for
      // all elements in the domain.  So we always use a ForallExpr expression, even if the quantifier is an exists.

      if (crashExpr != null) {
        var triggers = CullAttributesToTriggersOnly(attrs);
        crashExpr = new ForallExpr(Token.NoToken, typeArgs, bvars, null /* no range */, crashExpr, triggers);
        crashExpr = AH.SetExprType(crashExpr, new BoolType());
      }
      return new UndefinedBehaviorAvoidanceConstraint(crashExpr);
    }

    public ArmadaLValue ResolveAsLValue(Expression expr)
    {
      if (expr == null) {
        return null;
      }

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return ResolveAsLValue(e.E);
      }

      if (expr is NameSegment) {
        var e = (NameSegment)expr;
        var av = symbols.Lookup(methodName, e.Name);
        if (av == null) {
          return null;
        }
        else {
          return av.GetLValue(e.tok, this);
        }
      }

      if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        var newLhs = ResolveAsLValue(e.Lhs);
        if (newLhs == null) {
          return null;
        }
        return newLhs.ApplyExprDotName(e.tok, this, e.SuffixName, expr.Type);
      }

      if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        var newSeq = ResolveAsLValue(e.Seq);

        if (newSeq == null) {
          return null;
        }

        if (!e.SelectOne) {
          Fail(expr.tok, "Can't resolve a slice as an lvalue");
        }

        var newE0 = ResolveAsRValue(e.E0);
        return newSeq.ApplySeqSelect(e.tok, this, newE0, expr.Type);
      }

      if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Dereference) {
          var newE = ResolveAsRValue(e.E);
          return ResolveArmadaDereferenceExprAsLValue(e.tok, newE);
        }
        else {
          Fail(expr.tok, "Can't resolve unary-operator expression as an lvalue since it's not the dereference operator (*)");
        }
      }

      Fail(expr.tok, $"Can't resolve the following expression as an lvalue since it has an unexpected expression type:  {expr}\n");
      return null;
    }

    public ArmadaRValue ResolveAsRValue(Expression expr)
    {
      if (expr == null) {
        return new ArmadaRValue(null);
      }

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return ResolveAsRValue(e.E);
      }

      if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ArmadaRValueList newOperands = ResolveAsRValueList(e.Operands);
        ArmadaRValueList newPrefixLimits = ResolveAsRValueList(e.PrefixLimits);
        var crashAvoidance = newOperands.UndefinedBehaviorAvoidance + newPrefixLimits.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance,
                                new ChainingExpression(e.tok, newOperands.Vals, e.Operators, e.OperatorLocs, newPrefixLimits.Vals),
                                expr.Type);
      }

      if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        var newE = ResolveAsRValue(e.E);
        var newE_val = AH.ConvertToIntIfLimitedSizeInt(newE.Val);
        var val = AH.EnsureIntegerFit(new NegationExpression(e.tok, newE_val), expr.Type);
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, val);
      }

      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e.Value == null) {
          // If an expression is null, treat it as the null pointer.
          // That is, treat it as 0 with the same type that the resolver already assigned it.
          var null_ptr = new LiteralExpr(e.tok, 0);
          null_ptr.Type = e.Type;
          return new ArmadaRValue(null_ptr);
        }
        else {
          return new ArmadaRValue(expr);
        }
      }

      if (expr is ThisExpr) {
        Fail(expr.tok, "The keyword 'this' isn't supported in Armada");
        return new ArmadaRValue(null);
      }

      if (expr is MeExpr) {
        return new ArmadaRValue(tid);
      }

      if (expr is StoreBufferEmptyExpr) {
        var s = GetRValueState();
        var threads = AH.MakeExprDotName(s, "threads", AH.MakeThreadsType());
        var thread = AH.MakeSeqSelectExpr(threads, tid, "Armada_Thread");
        var storeBuffer = AH.MakeExprDotName(thread, "storeBuffer", "Armada_StoreBuffer");
        var storeBufferCardinality = AH.MakeCardinalityExpr(storeBuffer);
        var storeBufferEmpty = AH.MakeEqExpr(storeBufferCardinality, AH.MakeZero());
        return new ArmadaRValue(storeBufferEmpty);
      }

      if (expr is IdentifierExpr) {
        Fail(expr.tok, "Attempt to resolve IdentifierExpr");
        return new ArmadaRValue(null);
      }

      if (expr is SetDisplayExpr) {
        var e = (SetDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, new SetDisplayExpr(e.tok, e.Finite, newElements.Vals), expr.Type);
      }

      if (expr is MultiSetDisplayExpr) {
        var e = (MultiSetDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, new MultiSetDisplayExpr(e.tok, newElements.Vals), expr.Type);
      }

      if (expr is SeqDisplayExpr) {
        var e = (SeqDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, new SeqDisplayExpr(e.tok, newElements.Vals), expr.Type);
      }

      if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        var newElements = new List<ExpressionPair>();
        var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
        foreach (var pair in e.Elements) {
          var newA = ResolveAsRValue(pair.A);
          var newB = ResolveAsRValue(pair.B);
          newElements.Add(new ExpressionPair(newA.Val, newB.Val));
          crashAvoidance.Add(newA.UndefinedBehaviorAvoidance);
          crashAvoidance.Add(newB.UndefinedBehaviorAvoidance);
        }
        return new ArmadaRValue(crashAvoidance, new MapDisplayExpr(e.tok, e.Finite, newElements), expr.Type);
      }

      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        var newArgs = ResolveAsRValueList(e.Arguments);
        return new ArmadaRValue(newArgs.UndefinedBehaviorAvoidance, new DatatypeValue(e.tok, e.DatatypeName, e.MemberName, newArgs.Vals), expr.Type);
      }

      if (expr is NameSegment) {
        var e = (NameSegment)expr;
        var av = symbols.Lookup(methodName, e.Name);
        if (av == null) {
          return new ArmadaRValue(expr);
        }
        else {
          return av.GetRValue(e.tok, this);
        }
      }

      if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        var newLhs = ResolveAsRValue(e.Lhs);
        return new ArmadaRValue(newLhs.UndefinedBehaviorAvoidance, new ExprDotName(e.tok, newLhs.Val, e.SuffixName, e.OptTypeArguments), expr.Type);
      }

      if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        var newLhs = ResolveAsRValue(e.Lhs);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newLhs.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new ApplySuffix(e.tok, newLhs.Val, newArgs.Vals), expr.Type);
      }

      if (expr is RevealExpr) {
        return new ArmadaRValue(expr);
      }

      if (expr is MemberSelectExpr) {
        Fail("Attempt to resolve a MemberSelectExpr");
        return new ArmadaRValue(null);
      }

      if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        var newSeq = ResolveAsRValue(e.Seq);
        var newE0 = ResolveAsRValue(e.E0);
        var newE1 = ResolveAsRValue(e.E1);
        var type = e.Seq.Type;

        var newE0val = (type is MapType) ? newE0.Val : AH.ConvertToIntIfNotInt(newE0.Val);
        var newE1val = (type is MapType) ? newE1.Val : e.SelectOne ? null : AH.ConvertToIntIfNotInt(newE1.Val);
        var crashAvoidance = newSeq.UndefinedBehaviorAvoidance + newE0.UndefinedBehaviorAvoidance;
        if (!e.SelectOne && e.E1 != null)
        {
          crashAvoidance.Add(newE1.UndefinedBehaviorAvoidance);
        }

        if (type is SeqType || type is SizedArrayType) {
          var cardinality = AH.MakeCardinalityExpr(newSeq.Val);
          crashAvoidance.Add(AH.MakeLeExpr(AH.MakeZero(), newE0val));
          if (e.SelectOne) {
            crashAvoidance.Add(AH.MakeLtExpr(newE0val, cardinality));
          }
          else if (e.E1 == null) {
            crashAvoidance.Add(AH.MakeLeExpr(newE0val, cardinality));
          }
          else {
            crashAvoidance.Add(AH.MakeLeExpr(newE0val, newE1val));
            crashAvoidance.Add(AH.MakeLeExpr(newE1val, cardinality));
          }
          return new ArmadaRValue(crashAvoidance, new SeqSelectExpr(e.tok, e.SelectOne, newSeq.Val, newE0val, newE1val), expr.Type);
        }

        if (type is MapType) {
          if (!e.SelectOne) {
            Fail(e.tok, "Attempt to take range of map");
            return new ArmadaRValue(null);
          }
          crashAvoidance.Add(AH.MakeInExpr(newE0val, newSeq.Val));
          return new ArmadaRValue(crashAvoidance, new SeqSelectExpr(e.tok, e.SelectOne, newSeq.Val, newE0val, newE1val), expr.Type);
        }

        Fail(e.tok, $"Attempt to obtain element of non-array, non-sequence, non-map type {type}");
        return new ArmadaRValue(null);
      }

      if (expr is MultiSelectExpr) {
        Fail(expr.tok, "Multi-select expressions aren't supported in Armada");
        return new ArmadaRValue(null);
      }

      if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        var newSeq = ResolveAsRValue(e.Seq);
        var newIndex = ResolveAsRValue(e.Index);
        var newValue = ResolveAsRValue(e.Value);
        var crashAvoidance = newSeq.UndefinedBehaviorAvoidance + newIndex.UndefinedBehaviorAvoidance + newValue.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new SeqUpdateExpr(e.tok, newSeq.Val, newIndex.Val, newValue.Val), expr.Type);
      }

      if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        var newRoot = ResolveAsRValue(e.Root);
        var newUpdates = new List<Tuple<IToken, string, Expression>>();
        var crashAvoidance = newRoot.UndefinedBehaviorAvoidance;
        foreach (var update in e.Updates) {
          var newItem3 = ResolveAsRValue(update.Item3);
          newUpdates.Add(new Tuple<IToken, string, Expression>(update.Item1, update.Item2, newItem3.Val));
          crashAvoidance.Add(newItem3.UndefinedBehaviorAvoidance);
        }
        return new ArmadaRValue(crashAvoidance, new DatatypeUpdateExpr(e.tok, newRoot.Val, newUpdates), expr.Type);
      }

      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var newReceiver = ResolveAsRValue(e.Receiver);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newReceiver.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new FunctionCallExpr(e.tok, e.Name, newReceiver.Val, e.OpenParen, newArgs.Vals), expr.Type);
      }

      if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        var newFunction = ResolveAsRValue(e.Function);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newFunction.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new ApplyExpr(e.tok, newFunction.Val, newArgs.Vals), expr.Type);
      }

      if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        var newE = ResolveAsRValue(e.E);
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, new MultiSetFormingExpr(e.tok, newE.Val), expr.Type);
      }

      if (expr is OldExpr) {
        var e = (OldExpr)expr;

        if (e.At != null) {
          Fail(expr.tok, "Armada doesn't yet support old() expressions that specify a specific program point");
          return new ArmadaRValue(null);
        }

        return ResolveAsOldRValue(e.tok, e.E);
      }

      if (expr is UnchangedExpr) {
        Fail(expr.tok, "unchanged expressions aren't supported by Armada");
        return new ArmadaRValue(null);
      }

      if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Dereference) {
          var newE = ResolveAsRValue(e.E);
          if (newE == null) {
            return new ArmadaRValue(null);
          }
          return ResolveArmadaDereferenceExprAsRValue(e.tok, newE);
        }
        else if (e.Op == UnaryOpExpr.Opcode.AddressOf) {
          var newE = ResolveAsLValue(e.E);
          if (newE == null) {
            Fail(e.tok, "Attempt to get address of value that isn't an lvalue");
            return new ArmadaRValue(null);
          }
          var addr = newE.GetAddress();
          if (addr == null) {
            Fail(e.tok, "Attempt to get address of value without an address");
            return new ArmadaRValue(null);
          }
          var crashAvoidance = newE.GetUndefinedBehaviorAvoidanceConstraint();
          return new ArmadaRValue(crashAvoidance, addr);
        }
        else if (e.Op == UnaryOpExpr.Opcode.Allocated) {
          var newE = ResolveAsRValue(e.E);
          return ResolveAllocatedExpr(e.tok, newE);
        }
        else if (e.Op == UnaryOpExpr.Opcode.AllocatedArray) {
          var newE = ResolveAsRValue(e.E);
          return ResolveAllocatedArrayExpr(e.tok, newE);
        }
        else if (e.Op == UnaryOpExpr.Opcode.Not && e.Type is PointerType) {
          Fail(e.tok, "Can't do bitwise-not (or any other integer manipulation, for that matter) on a pointer value");
          return new ArmadaRValue(null);
        }
        else {
          var newE = ResolveAsRValue(e.E);
          var newE_val = AH.ConvertToIntIfLimitedSizeInt(newE.Val);
          var val = AH.EnsureIntegerFit(new UnaryOpExpr(e.tok, e.Op, newE_val), expr.Type);
          return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, val);
        }
      }

      if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        var newE = ResolveAsRValue(e.E);
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, new ConversionExpr(e.tok, newE.Val, e.ToType), expr.Type);
      }

      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        var newE0 = ResolveAsRValue(e.E0);
        var newE1 = ResolveAsRValue(e.E1);
        return ResolveArmadaBinaryExpr(e.tok, e.Type, e.Op, newE0, newE1);
      }

      if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        var newE0 = ResolveAsRValue(e.E0);
        var newE1 = ResolveAsRValue(e.E1);
        var newE2 = ResolveAsRValue(e.E2);
        var crashAvoidance = newE0.UndefinedBehaviorAvoidance + newE1.UndefinedBehaviorAvoidance + newE2.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new TernaryExpr(e.tok, e.Op, newE0.Val, newE1.Val, newE2.Val), expr.Type);
      }

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        var newRHSs = ResolveAsRValueList(e.RHSs);
        var newBody = ResolveAsRValue(e.Body);
        var newAttrs = ResolveAttributes(e.Attributes);
        var crashAvoidance = newRHSs.UndefinedBehaviorAvoidance;
        if (newBody.CanCauseUndefinedBehavior) {
          crashAvoidance.Add(new LetExpr(Token.NoToken, e.LHSs, newRHSs.Vals, newBody.UndefinedBehaviorAvoidance.Expr, e.Exact, null));
        }
        return new ArmadaRValue(crashAvoidance, new LetExpr(e.tok, e.LHSs, newRHSs.Vals, newBody.Val, e.Exact, newAttrs), expr.Type);
      }

      if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        var newBody = ResolveAsRValue(e.Body);
        var newContract = ResolveAsRValue(e.Contract);
        var crashAvoidance = newBody.UndefinedBehaviorAvoidance + newContract.UndefinedBehaviorAvoidance;
        return new ArmadaRValue(crashAvoidance, new NamedExpr(e.tok, e.Name, newBody.Val, newContract.Val, e.ReplacerToken), expr.Type);
      }

      if (expr is ForallExpr) {
        var e = (ForallExpr)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var newAttrs = ResolveAttributes(e.Attributes);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, e.TypeArgs, e.BoundVars, newAttrs);
        return new ArmadaRValue(crashAvoidance,
                                new ForallExpr(e.tok, e.TypeArgs, e.BoundVars, newRange.Val, newTerm.Val, newAttrs),
                                expr.Type);
      }

      if (expr is ExistsExpr) {
        var e = (ExistsExpr)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var newAttrs = ResolveAttributes(e.Attributes);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, e.TypeArgs, e.BoundVars, newAttrs);
        return new ArmadaRValue(crashAvoidance,
                                new ExistsExpr(e.tok, e.TypeArgs, e.BoundVars, newRange.Val, newTerm.Val, newAttrs),
                                expr.Type);
      }

      if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var newAttrs = ResolveAttributes(e.Attributes);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, new List<TypeParameter>(), e.BoundVars, newAttrs);
        return new ArmadaRValue(crashAvoidance,
                                new SetComprehension(e.tok, e.Finite, e.BoundVars, newRange.Val, newTerm.Val, newAttrs),
                                expr.Type);
      }

      if (expr is MapComprehension) {
        // FIXME: I have no idea about what the left term is doing,
        //        and this is only minimal fix to make CSharp happy
        var e = (MapComprehension)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newRightTerm = ResolveAsRValue(e.Term);
        var newLeftTerm = ResolveAsRValue(e.TermLeft);
        var newAttrs = ResolveAttributes(e.Attributes);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newRightTerm, new List<TypeParameter>(), e.BoundVars, newAttrs);
        return new ArmadaRValue(crashAvoidance,
                                new MapComprehension(e.tok, e.Finite, e.BoundVars, newRange.Val, newLeftTerm.Val, newRightTerm.Val, newAttrs),
                                expr.Type);
      }

      if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        var newRequires = ResolveAsRValue(e.Range);
        var newBody = ResolveAsRValue(e.Body);
        var newReads = new List<FrameExpression>();
        if (e.Reads != null && e.Reads.Any()) {
          Fail(expr.tok, "Can't resolve a lambda expression with a reads clause");
        }
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRequires, newBody, new List<TypeParameter>(), e.BoundVars,
                                                                   null /* no attributes */);
        return new ArmadaRValue(crashAvoidance,
                                new LambdaExpr(e.tok, e.BoundVars, newRequires.Val, newReads, newBody.Val),
                                expr.Type);
      }

      if (expr is WildcardExpr) {
        Fail("Can't resolve wildcard expression in this context");
        return new ArmadaRValue(expr);
      }

      if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        var newE = ResolveAsRValue(e.E);
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, new StmtExpr(e.tok, e.S, newE.Val), expr.Type);
      }

      if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        var newTest = ResolveAsRValue(e.Test);
        var newThn = ResolveAsRValue(e.Thn);
        var newEls = ResolveAsRValue(e.Els);
        var crashAvoidance = newTest.UndefinedBehaviorAvoidance;
        if (newThn.CanCauseUndefinedBehavior) {
          crashAvoidance.Add(AH.MakeImpliesExpr(newTest.Val, newThn.UndefinedBehaviorAvoidance.Expr));
        }
        if (newEls != null && newEls.CanCauseUndefinedBehavior) {
          crashAvoidance.Add(AH.MakeOrExpr(newTest.Val, newEls.UndefinedBehaviorAvoidance.Expr));
        }
        return new ArmadaRValue(crashAvoidance, new ITEExpr(e.tok, e.IsBindingGuard, newTest.Val, newThn.Val, newEls.Val), expr.Type);
      }

      if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var newSource = ResolveAsRValue(e.Source);
        var newCases = new List<MatchCaseExpr>();

        bool canCrash = false;
        var crashAvoidanceCases = new List<MatchCaseExpr>();
        foreach (var c in e.Cases) {
          var newBody = ResolveAsRValue(c.Body);
          // I believe that it's best to always use CasePatterns, because we can't be sure that it's resolved.
          newCases.Add(new MatchCaseExpr(c.tok, c.Id, c.CasePatterns, newBody.Val));

          // Now, add a case to the list of crash-avoidance cases.  We need to get this case
          // even if it's empty (true) since some of the cases might not be empty.

          var crashExpr = newBody.UndefinedBehaviorAvoidance.Expr;
          crashAvoidanceCases.Add(new MatchCaseExpr(c.tok, c.Id, c.CasePatterns, crashExpr));
          if (newBody.CanCauseUndefinedBehavior) {
            canCrash = true;
          }
        }

        // The crash-avoidance constraint includes the source's crash-avoidance constraint.  And, if any of
        // the cases can crash, we create a match expression to describe the crash-avoidance constraint
        // and add it to the crash-avoidance constraint.

        var crashAvoidance = newSource.UndefinedBehaviorAvoidance;
        if (canCrash) {
          crashAvoidance.Add(new MatchExpr(e.tok, newSource.Val, crashAvoidanceCases, e.UsesOptionalBraces));
        }

        return new ArmadaRValue(crashAvoidance, new MatchExpr(e.tok, newSource.Val, newCases, e.UsesOptionalBraces), expr.Type);
      }

      Fail(expr.tok, $"Can't resolve the following expression as an rvalue since it has an unexpected expression type:  {expr}\n");
      return new ArmadaRValue(expr);
    }

    public ArmadaRValueList ResolveAsRValueList(List<Expression> es)
    {
      if (es == null) {
        return null;
      }

      var ret = new ArmadaRValueList();
      foreach (var e in es) {
        ret.Add(ResolveAsRValue(e));
      }
      return ret;
    }
  }

  public class NormalResolutionContext : ResolutionContext
  {
    private readonly Expression locv;
    private readonly Expression t;

    public NormalResolutionContext(NextRoutine next, ArmadaSymbolTable i_symbols)
      : base(next.s, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      locv = next.locv;
      t = next.t;
    }

    public NormalResolutionContext(Expression i_lvalueState, NextRoutine next, ArmadaSymbolTable i_symbols)
      : base(i_lvalueState, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      locv = next.locv;
      t = next.t;
    }

    public override Expression GetRValueHeap()
    {
      return AH.MakeExprDotName(locv, "heap", "Armada_Heap");
    }

    public override Expression GetRValueGlobals()
    {
      return AH.MakeExprDotName(locv, "globals", AH.MakeGlobalsType(moduleName));
    }

    public override Expression GetRValueTopStackFrame()
    {
      return AH.MakeExprDotName(t, "top", AH.MakeStackFrameType(moduleName));
    }
  }

  public class CustomResolutionContext : ResolutionContext
  {
    private readonly Expression locv;
    private readonly Expression top;
    private readonly Expression ghosts;

    public CustomResolutionContext(Expression i_lvalueState, Expression i_rvalueState, Expression i_locv, Expression i_top,
                                   Expression i_ghosts, Expression i_tid, string i_methodName,
                                   ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter)
      : base(i_lvalueState, i_rvalueState, i_tid, i_methodName, i_symbols, i_failureReporter)
    {
      locv = i_locv;
      top = i_top;
      ghosts = i_ghosts;
    }

    public override Expression GetRValueHeap()
    {
      return AH.MakeExprDotName(locv, "heap", "Armada_Heap");
    }

    public override Expression GetRValueGlobals()
    {
      return AH.MakeExprDotName(locv, "globals", AH.MakeGlobalsType(moduleName));
    }

    public override Expression GetRValueGhosts()
    {
      return ghosts;
    }

    public override Expression GetRValueTopStackFrame()
    {
      return top;
    }
  }

  public class GlobalInvariantResolutionContext : ResolutionContext
  {
    public GlobalInvariantResolutionContext(Expression i_s, ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter,
                                            string i_moduleName)
      : base(i_s, i_s, null, null, i_symbols, i_failureReporter, i_moduleName)
    {
    }

    public override Expression GetRValueHeap()
    {
      var mem = AH.MakeExprDotName(GetRValueState(), "mem", "Armada_SharedMemory");
      return AH.MakeExprDotName(mem, "heap", "Armada_Heap");
    }

    public override Expression GetRValueGlobals()
    {
      var mem = AH.MakeExprDotName(GetRValueState(), "mem", "Armada_SharedMemory");
      return AH.MakeExprDotName(mem, "globals", AH.MakeGlobalsType(moduleName));
    }

    public override Expression GetRValueGhosts()
    {
      return AH.MakeExprDotName(GetRValueState(), "ghosts", AH.MakeGhostsType(moduleName));
    }

    public override Expression GetRValueTopStackFrame()
    {
      Fail("Can't refer to a stack variable in a global invariant");
      return null;
    }
  }

  public class YieldPredicateResolutionContext : ResolutionContext
  {
    private readonly Expression s;

    public YieldPredicateResolutionContext(Expression i_s, Expression s_prime, Expression i_tid,
                                           ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter, string i_moduleName)
      : base(s_prime, s_prime, i_tid, null, i_symbols, i_failureReporter, i_moduleName)
    {
      s = i_s;
    }

    public override Expression GetRValueTopStackFrame()
    {
      Fail("Can't refer to a stack variable in a yield predicate");
      return null;
    }

    public override ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      var yrc = new YieldPredicateResolutionContext(s, s, tid, symbols, failureReporter, moduleName);
      return yrc.ResolveAsRValue(expr);
    }
  }

  public class RequiresResolutionContext : ResolutionContext
  {
    public RequiresResolutionContext(Expression i_s, Expression i_tid, string i_methodName, ArmadaSymbolTable i_symbols,
                                     IFailureReporter i_failureReporter, string i_moduleName = null)
      : base(i_s, i_s, i_tid, i_methodName, i_symbols, i_failureReporter, i_moduleName)
    {
    }
  }

  public class EnsuresResolutionContext : ResolutionContext
  {
    private readonly Expression s;

    public EnsuresResolutionContext(Expression i_s, Expression s_prime, Expression i_tid, string i_methodName,
                                    ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter, string i_moduleName)
      : base(s_prime, s_prime, i_tid, i_methodName, i_symbols, i_failureReporter, i_moduleName)
    {
      s = i_s;
    }

    public override ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      var erc = new EnsuresResolutionContext(s, s, tid, methodName, symbols, failureReporter, moduleName);
      return erc.ResolveAsRValue(expr);
    }
  }

  public class BodylessMethodSnapshotResolutionContext : ResolutionContext
  {
    private List<Expression> oldValues;
    private bool resolving;

    public BodylessMethodSnapshotResolutionContext(Expression i_s, Expression i_tid, string i_methodName, ArmadaSymbolTable i_symbols,
                                                   IFailureReporter i_failureReporter)
      : base(i_s, i_s, i_tid, i_methodName, i_symbols, i_failureReporter, null)
    {
      oldValues = new List<Expression>();
      resolving = false;
    }

    public override ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      if (resolving) {
        Fail(tok, "Nested old() expressions not allowed in the postcondition of a body-less method");
        return null;
      }

      oldValues.Add(expr);

      resolving = true;
      var retval = ResolveAsRValue(expr);
      resolving = false;

      return retval;
    }

    public List<Expression> OldValues { get { return oldValues; } }
  }

  public class BodylessMethodPostconditionResolutionContext : ResolutionContext
  {
    private int numOldResolutions;

    public BodylessMethodPostconditionResolutionContext(NextRoutine next, ArmadaSymbolTable i_symbols)
      : base(next.s, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      numOldResolutions = 0;
    }

    public override ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      var v = symbols.Lookup(methodName, $"Armada_Old{numOldResolutions}");
      ++numOldResolutions;
      return v.GetRValue(tok, this);
    }
  }
}
