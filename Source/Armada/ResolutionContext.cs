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
    private readonly string lvalueState;
    private readonly string rvalueState;
    public readonly string tid;
    public readonly string methodName;
    public readonly ArmadaSymbolTable symbols;
    public readonly IFailureReporter failureReporter;
    public readonly string moduleName;

    public ResolutionContext(string i_lvalueState, string i_rvalueState, string i_tid, string i_methodName,
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

    public virtual string GetLValueState()
    {
      if (lvalueState == null) {
        Fail("Can't get an lvalue state for this context");
      }
      return lvalueState;
    }

    public virtual string GetRValueState()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
      }
      return rvalueState;
    }

    public virtual string GetLValueTopStackFrame()
    {
      if (lvalueState == null) {
        Fail("Can't get an lvalue state for this context");
        return null;
      }
      if (tid == null) {
        Fail("No thread defined in this context, so can't determine top stack frame");
        return null;
      }
      return $"({lvalueState}).threads[{tid}].top";
    }

    public virtual string GetRValueHeap()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      if (tid == null) {
        Fail("No thread defined in this context, so can't determine local view of heap");
        return null;
      }
      var fnName = AH.AddModuleToIdentifier(moduleName, "Armada_GetThreadLocalView");
      return $"{fnName}({rvalueState}, {tid}).heap";
    }

    public virtual string GetRValueGlobals()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      if (tid == null) {
        Fail("No thread defined in this context, so can't determine local view of globals");
        return null;
      }
      var fnName = AH.AddModuleToIdentifier(moduleName, "Armada_GetThreadLocalView");
      return $"{fnName}({rvalueState}, {tid}).globals";
    }

    public virtual string GetRValueGhosts()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      return $"({rvalueState}).ghosts";
    }

    public virtual string GetRValueTopStackFrame()
    {
      if (rvalueState == null) {
        Fail("Can't get an rvalue state for this context");
        return null;
      }
      if (tid == null) {
        Fail("No thread defined in this context, so can't determine top stack frame");
        return null;
      }
      return $"({rvalueState}).threads[{tid}].top";
    }

    public virtual ArmadaRValue ResolveAsOldRValue(IToken tok, Expression expr)
    {
      Fail(tok, "Can't use old() expression in this context");
      return null;
    }

    public virtual ArmadaRValue ResolveAsMemoryRValue(IToken tok, Expression expr)
    {
      var subcontext = new GlobalViewResolutionContext(rvalueState, tid, methodName, symbols, failureReporter, moduleName);
      return subcontext.ResolveAsRValue(expr);
    }

    public void Fail(IToken tok, string reason) { failureReporter.Fail(tok, reason); }
    public void Fail(string reason) { failureReporter.Fail(reason); }

    public ArmadaRValue ResolveArmadaBinaryExpr(IToken tok, Type targetType, BinaryExpr.Opcode op,
                                                ArmadaRValue operand1, ArmadaRValue operand2,
                                                Type operand1Type, Type operand2Type)
    {
      UndefinedBehaviorAvoidanceConstraint crashAvoidance = operand1.UndefinedBehaviorAvoidance + operand2.UndefinedBehaviorAvoidance;

      // If this is a pointer plus or minus an integer, the semantics is that it produces undefined behavior unless
      // it stays within an array.

      if ((op == BinaryExpr.Opcode.Add || op == BinaryExpr.Opcode.Sub) && operand1Type is PointerType) {
        var pt = (PointerType)operand1Type;

        // operand1 in h.valid
        var h = GetRValueHeap();
        var operand1_valid = $"({operand1.Val}) in ({h}).valid";
        crashAvoidance.Add(operand1_valid);

        // operand1 in h.tree
        var tree = $"({h}).tree";
        var operand1_in_tree = $"{operand1.Val} in {tree}";
        crashAvoidance.Add(operand1_in_tree);

        // tree[operand1].child_type.Armada_ChildTypeIndex?
        // (in other words, operand1 must be a child of its parent via an index field)
        var is_field_array_index = $"{tree}[{operand1.Val}].child_type.Armada_ChildTypeIndex?";
        crashAvoidance.Add(is_field_array_index);

        // tree[operand1].parent in h.tree
        var parent = $"{tree}[{operand1.Val}].parent";
        crashAvoidance.Add($"{parent} in {tree}");

        // 0 <= (child_type.i <op> operand2) < |tree[operand1.parent].children|
        var operand2val = AH.ConvertToIntIfNotInt(operand2.Val, operand2Type);
        var updated_index = $"{tree}[{operand1.Val}].child_type.i {BinaryExpr.OpcodeString(op)} {operand2val}";
        crashAvoidance.Add($"0 <= {updated_index} < |{tree}[{parent}].children|");

        // return tree[operand1.parent].children[child_type.i + operand2]
        return new ArmadaRValue(crashAvoidance, $"{tree}[{parent}].children[{updated_index}]");
      }

      // Order-based comparison of pointers is only allowed when they're in the same array.  The semantics for such a
      // comparison is that their indices within that array have the given comparison relationship.

      if ((op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge) &&
          (operand1Type is PointerType || operand2Type is PointerType))
      {
        if (!AH.TypesMatch(operand1Type, operand2Type)) {
          Fail(tok, "Can't compare a pointer to anything except a pointer of the same type");
          return null;
        }

        var h = GetRValueHeap();

        // It's undefined behavior if operand 1 or 2 isn't a valid pointer
        crashAvoidance.Add($"({operand1.Val}) in ({h}).valid");
        crashAvoidance.Add($"({operand2.Val}) in ({h}).valid");

        // It's undefined behavior if operand 1 or 2 isn't in the tree
        var tree = $"({h}).tree";
        crashAvoidance.Add($"({operand1.Val}) in {tree}");
        crashAvoidance.Add($"({operand2.Val}) in {tree}");

        // It's undefined behavior if operand 1 or 2 isn't an array element
        crashAvoidance.Add($"{tree}[{operand1.Val}].child_type.Armada_ChildTypeIndex?");
        crashAvoidance.Add($"{tree}[{operand2.Val}].child_type.Armada_ChildTypeIndex?");

        // It's undefined behavior if operands 1 and 2 don't have the same parent
        crashAvoidance.Add($"{tree}[{operand1.Val}].parent == {tree}[{operand2.Val}].parent");

        // The actual comparison is between the field indices of operands 1 and 2
        var result = $"{tree}[{operand1.Val}].child_type.i {BinaryExpr.OpcodeString(op)} {tree}[{operand2.Val}].child_type.i";
        return new ArmadaRValue(crashAvoidance, result);
      }

      if (op == BinaryExpr.Opcode.And) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + $"({operand1.Val}) ==> ({operand2.UndefinedBehaviorAvoidance.Expr})";
        }
      }
      else if (op == BinaryExpr.Opcode.Or) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + $"({operand1.Val}) || ({operand2.UndefinedBehaviorAvoidance.Expr})";
        }
      }
      else if (op == BinaryExpr.Opcode.Imp) {
        if (operand2.CanCauseUndefinedBehavior) {
          crashAvoidance = operand1.UndefinedBehaviorAvoidance + $"({operand1.Val}) ==> ({operand2.UndefinedBehaviorAvoidance.Expr})";
        }
      }
      else if (op == BinaryExpr.Opcode.Exp) {
        if (operand1.CanCauseUndefinedBehavior) {
          crashAvoidance = operand2.UndefinedBehaviorAvoidance + $"({operand2.Val}) ==> ({operand1.UndefinedBehaviorAvoidance.Expr})";
        }
      }
      else if (op == BinaryExpr.Opcode.Div) {
        crashAvoidance.Add($"({operand2.Val}) != 0");
      }
      else if (op == BinaryExpr.Opcode.Mod) {
        crashAvoidance.Add($"({operand2.Val}) != 0");
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

        if (operand1Type is PointerType) {
          crashAvoidance.Add($"Armada_ComparablePointer({operand1.Val}, {h})");
        }
        if (operand2Type is PointerType) {
          crashAvoidance.Add($"Armada_ComparablePointer({operand2.Val}, {h})");
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
        name += AH.GetBitWidth(operand1Type as UserDefinedType);
        var e = $"{name}({operand1.Val}, {operand2.Val})";
        return new ArmadaRValue(crashAvoidance, e);
      }
      // For mathematical expressions, we should treat them as if
      else if (op == BinaryExpr.Opcode.In || op == BinaryExpr.Opcode.NotIn ||
               op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq) {
        var e = $"({operand1.Val}) {BinaryExpr.OpcodeString(op)} ({operand2.Val})";
        return new ArmadaRValue(crashAvoidance, e);
      }
      else {
        var op1val = AH.ConvertToIntIfLimitedSizeInt(operand1.Val, operand1Type);
        var op2val = AH.ConvertToIntIfLimitedSizeInt(operand2.Val, operand2Type);
        var e = $"({op1val}) {BinaryExpr.OpcodeString(op)} ({op2val})";
        e = AH.EnsureIntegerFit(e, new IntType(), targetType);
        return new ArmadaRValue(crashAvoidance, e);
      }
    }

    public ArmadaLValue ResolveArmadaDereferenceExprAsLValue(IToken tok, ArmadaRValue addr, Type targetType)
    {
      if (targetType == null) {
        Fail(tok, "Attempt to dereference a value whose type isn't known");
        return null;
      }

      return new AddressableArmadaLValue(tok, targetType, addr);
    }

    public ArmadaRValue ResolveArmadaDereferenceExprAsRValue(IToken tok, ArmadaRValue addr, Type targetType)
    {
      if (targetType == null) {
        Fail(tok, "Attempt to dereference a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, targetType);
      if (valid == null) {
        Fail(tok, $"Type {targetType} is not supported on the heap, and thus not for dereference operations");
        return new ArmadaRValue(null);
      }
      var crashAvoidance = addr.UndefinedBehaviorAvoidance + valid;

      var ret = AH.GetInvocationOfDereferencePointer(h, addr.Val, targetType);
      if (ret == null) {
        Fail(tok, $"Type {targetType} is not supported on the heap, and thus not for dereference operations");
      }
      return new ArmadaRValue(crashAvoidance, ret);
    }

    public ArmadaRValue ResolveAllocatedExpr(IToken tok, ArmadaRValue addr, Type addrType)
    {
      if (addrType == null) {
        Fail(tok, "Attempt to determine the allocated-ness of a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addrType, out subtype, out err)) {
        Fail(tok, err);
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, subtype);
      if (valid == null) {
        Fail(tok, $"Type {subtype} is not supported on the heap, and thus not for allocated() expressions");
        return new ArmadaRValue(null);
      }

      return new ArmadaRValue(addr.UndefinedBehaviorAvoidance, valid);
    }

    public ArmadaRValue ResolveAllocatedArrayExpr(IToken tok, ArmadaRValue addr, Type addrType)
    {
      if (addrType == null) {
        Fail(tok, "Attempt to determine the allocated-array-ness of a value whose type isn't known");
        return new ArmadaRValue(null);
      }

      Type subtype;
      string err;
      if (!AH.GetDereferenceType(addrType, out subtype, out err)) {
        Fail(tok, err);
        return new ArmadaRValue(null);
      }

      var h = GetRValueHeap();

      var valid = AH.GetInvocationOfValidPointer(h, addr.Val, subtype);
      if (valid == null) {
        Fail(tok, $"Type {subtype} is not supported on the heap, and thus not for allocated_array() expressions");
        return new ArmadaRValue(null);
      }

      var node = $"({h}).tree[{addr.Val}]";
      var is_array_field = $"{node}.child_type.Armada_ChildTypeIndex?";
      var parent_valid = $"Armada_ValidPointer({h}, {node}.parent)";

      var res = $"({valid}) && ({is_array_field}) && ({parent_valid})";

      return new ArmadaRValue(addr.UndefinedBehaviorAvoidance, res);
    }

    private string ResolveTriggers(Attributes attrs)
    {
      if (attrs == null) {
        return "";
      }

      var prev_triggers = ResolveTriggers(attrs.Prev);

      if (attrs.Name == "trigger") {
        var rs = ResolveAsRValueList(attrs.Args);
        var s = String.Join(", ", rs.Vals);
        return $"{prev_triggers} {{:trigger {s}}}";
      }
      else {
        return prev_triggers;
      }
    }

    private UndefinedBehaviorAvoidanceConstraint GetQuantifiedUndefinedBehaviorAvoidanceConstraint(
      ArmadaRValue range,
      ArmadaRValue term,
      List<TypeParameter> typeArgs,
      List<BoundVar> bvars,
      Attributes attrs
      )
    {
      string body = null;
      if (range != null && range.CanCauseUndefinedBehavior) {
        if (term.CanCauseUndefinedBehavior) {
          body = $"({range.UndefinedBehaviorAvoidance.Expr}) && (({range.Val}) ==> ({term.UndefinedBehaviorAvoidance.Expr}))";
        }
        else {
          body = range.UndefinedBehaviorAvoidance.Expr;
        }
      }
      else if (term.CanCauseUndefinedBehavior) {
        if (range != null && range.Val != null) {
          body = $"({range.Val}) ==> ({term.UndefinedBehaviorAvoidance.Expr})";
        }
        else {
          body = term.UndefinedBehaviorAvoidance.Expr;
        }
      }

      if (body == null) {
        return new UndefinedBehaviorAvoidanceConstraint();
      }

      // No matter what kind of quantified expression it is, forall or exists, to avoid crashing it must be true for
      // all elements in the domain.  So we always use a forall expression, even if the quantifier is an exists.
      // Note that we don't need to put a range on this forall (i.e., we don't need to say | range ::) because
      // the restriction to the range is already talked about in the body.
      
      var avoidanceExpr = "forall "
                          + String.Join(", ", bvars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                          + " "
                          + ResolveTriggers(attrs) // intentionally leave out range, since it's in the body
                          + " :: "
                          + body;
      return new UndefinedBehaviorAvoidanceConstraint(avoidanceExpr);
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
        return newSeq.ApplySeqSelect(e.tok, this, newE0, e.E0.Type, expr.Type);
      }

      if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Dereference) {
          var newE = ResolveAsRValue(e.E);
          return ResolveArmadaDereferenceExprAsLValue(e.tok, newE, expr.Type);
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
        var newOperandStrings = newOperands.Vals;
        var crashAvoidance = newOperands.UndefinedBehaviorAvoidance;
        var val = newOperandStrings[0]
                + String.Concat(Enumerable.Range(0, e.Operands.Count - 1).Select(i => $" {BinaryExpr.OpcodeString(e.Operators[i])} ({newOperandStrings[i + 1]})"));
        return new ArmadaRValue(crashAvoidance, val);
      }

      if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        var newE = ResolveAsRValue(e.E);
        var newEAsInt = AH.ConvertToIntIfLimitedSizeInt(newE.Val, e.E.Type);
        var val = AH.EnsureIntegerFit($"-({newEAsInt})", new IntType(), expr.Type);
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, val);
      }

      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e.Value == null) {
          // If an expression is null, treat it as the null pointer. That is, treat it as 0.
          return new ArmadaRValue("0");
        }
        else {
          return new ArmadaRValue(Printer.ExprToString(expr));
        }
      }

      if (expr is ThisExpr) {
        Fail(expr.tok, "The keyword 'this' isn't supported in Armada");
        return new ArmadaRValue(null);
      }

      if (expr is MeExpr) {
        if (tid == null) {
          Fail(expr.tok, "No thread defined in this context, $me isn't defined");
        }
        return new ArmadaRValue(tid);
      }

      if (expr is StoreBufferEmptyExpr) {
        if (tid == null) {
          Fail("No thread defined in this context, so $sb_empty is undefined");
          return null;
        }
        var storeBufferEmpty = $"|({GetRValueState()}).threads[{tid}].storeBuffer| == 0";
        return new ArmadaRValue(storeBufferEmpty);
      }

      if (expr is TotalStateExpr) {
        return new ArmadaRValue(GetRValueState());
      }

      if (expr is IfUndefinedExpr) {
        var e = (IfUndefinedExpr)expr;
        var potentiallyUnsafe = ResolveAsRValue(e.PotentiallyUnsafe);
        if (!potentiallyUnsafe.CanCauseUndefinedBehavior) {
          return potentiallyUnsafe;
        }
        var safeSubstitution = ResolveAsRValue(e.SafeSubstitution);
        var undefinedBehaviorAvoidance = new UndefinedBehaviorAvoidanceConstraint();
        if (safeSubstitution.CanCauseUndefinedBehavior) {
          undefinedBehaviorAvoidance.Add(
            $"({potentiallyUnsafe.UndefinedBehaviorAvoidance.Expr}) || ({safeSubstitution.UndefinedBehaviorAvoidance.Expr})"
          );
        }
        return new ArmadaRValue(
          undefinedBehaviorAvoidance,
          $"if {potentiallyUnsafe.UndefinedBehaviorAvoidance.Expr} then {potentiallyUnsafe.Val} else {safeSubstitution.Val}"
        );
      }

      if (expr is IdentifierExpr) {
        Fail(expr.tok, "Attempt to resolve IdentifierExpr");
        return new ArmadaRValue(null);
      }

      if (expr is SetDisplayExpr) {
        var e = (SetDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        var v = "{" + String.Join(", ", newElements.Vals) + "}";
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, v);
      }

      if (expr is MultiSetDisplayExpr) {
        var e = (MultiSetDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        var v = "multiset {" + String.Join(", ", newElements.Vals) + "}";
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, v);
      }

      if (expr is SeqDisplayExpr) {
        var e = (SeqDisplayExpr)expr;
        var newElements = ResolveAsRValueList(e.Elements);
        var v = "[" + String.Join(", ", newElements.Vals) + "]";
        return new ArmadaRValue(newElements.UndefinedBehaviorAvoidance, v);
      }

      if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        var mapElements = new List<string>();
        var crashAvoidance = new UndefinedBehaviorAvoidanceConstraint();
        foreach (var pair in e.Elements) {
          var newA = ResolveAsRValue(pair.A);
          var newB = ResolveAsRValue(pair.B);
          mapElements.Add($"({newA.Val}) := ({newB.Val})");
          crashAvoidance.Add(newA.UndefinedBehaviorAvoidance);
          crashAvoidance.Add(newB.UndefinedBehaviorAvoidance);
        }
        var v = "map [" + String.Join(", ", mapElements) + "]";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        var newArgs = ResolveAsRValueList(e.Arguments);
        var v = $"{e.DatatypeName}.{e.MemberName}";
        if (e.Arguments.Any()) {
          v += "(" + String.Join(", ", newArgs.Vals) + ")";
        }
        return new ArmadaRValue(newArgs.UndefinedBehaviorAvoidance, v);
      }

      if (expr is NameSegment) {
        var e = (NameSegment)expr;
        var av = symbols.Lookup(methodName, e.Name);
        if (av == null) {
          return new ArmadaRValue(e.Name);
        }
        else {
          return av.GetRValue(e.tok, this);
        }
      }

      if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        var newLhs = ResolveAsRValue(e.Lhs);
        var newLhsParenthesized = AH.IsJustNames(e.Lhs) ? newLhs.Val : "(" + newLhs.Val + ")";
        var v = $"{newLhsParenthesized}.{e.SuffixName}";
        return new ArmadaRValue(newLhs.UndefinedBehaviorAvoidance, v);
      }

      if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        var newLhs = ResolveAsRValue(e.Lhs);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newLhs.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        var newLhsParenthesized = AH.IsJustNames(e.Lhs) ? newLhs.Val : $"({newLhs.Val})";
        var v = $"{newLhsParenthesized}(" + String.Join(", ", newArgs.Vals) + ")";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is RevealExpr) {
        var e = (RevealExpr) expr;
        var subexpr = ResolveAsRValue(e.Expr);
        return new ArmadaRValue(subexpr.UndefinedBehaviorAvoidance, $"reveal {subexpr.Val}");
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

        var newE0val = (type is MapType) ? newE0.Val : AH.ConvertToIntIfNotInt(newE0.Val, e.E0.Type);
        var newE1val = (type is MapType) ? newE1.Val
                                         : ((e.SelectOne || e.E1 == null) ? null : AH.ConvertToIntIfNotInt(newE1.Val, e.E1.Type));
        var crashAvoidance = newSeq.UndefinedBehaviorAvoidance + newE0.UndefinedBehaviorAvoidance;
        if (!e.SelectOne && e.E1 != null)
        {
          crashAvoidance.Add(newE1.UndefinedBehaviorAvoidance);
        }

        if (type is SeqType || type is SizedArrayType) {
          string v;
          if (e.SelectOne) {
            crashAvoidance.Add($"0 <= {newE0val} < |{newSeq.Val}|");
            v = $"({newSeq.Val})[{newE0val}]";
          }
          else if (e.E1 == null) {
            crashAvoidance.Add($"0 <= {newE0val} <= |{newSeq.Val}|");
            v = $"({newSeq.Val})[{newE0val}..]";
          }
          else {
            crashAvoidance.Add($"0 <= {newE0val} <= {newE1val} <= |{newSeq.Val}|");
            v = $"({newSeq.Val})[{newE0val}..{newE1val}]";
          }
          return new ArmadaRValue(crashAvoidance, v);
        }

        if (type is MapType) {
          if (!e.SelectOne) {
            Fail(e.tok, "Attempt to take range of map");
            return new ArmadaRValue(null);
          }
          crashAvoidance.Add($"({newE0val}) in ({newSeq.Val})");
          var v = $"({newSeq.Val})[{newE0val}]";
          return new ArmadaRValue(crashAvoidance, v);
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
        var v = $"({newSeq.Val})[{newIndex.Val} := {newValue.Val}]";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        var newRoot = ResolveAsRValue(e.Root);
        var newUpdates = new List<string>();
        var crashAvoidance = newRoot.UndefinedBehaviorAvoidance;
        foreach (var update in e.Updates) {
          var newItem3 = ResolveAsRValue(update.Item3);
          newUpdates.Add($"{update.Item2} := {newItem3.Val}");
          crashAvoidance.Add(newItem3.UndefinedBehaviorAvoidance);
        }
        var v = $"({newRoot.Val}).(" + String.Join(", ", newUpdates) + ")";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var newReceiver = ResolveAsRValue(e.Receiver);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newReceiver.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        if (e.Receiver != null) {
          Fail(e.tok, "Receivers not supported in Armada");
          return null;
        }
        var v = $"{e.Name}(" + String.Join(", ", newArgs.Vals) + ")";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        var newFunction = ResolveAsRValue(e.Function);
        var newArgs = ResolveAsRValueList(e.Args);
        var crashAvoidance = newFunction.UndefinedBehaviorAvoidance + newArgs.UndefinedBehaviorAvoidance;
        var newFunctionParenthesized = AH.IsJustNames(e.Function) ? newFunction.Val : $"({newFunction.Val})";
        var v = $"{newFunctionParenthesized}(" + String.Join(", ", newArgs.Vals) + ")";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        var newE = ResolveAsRValue(e.E);
        var v = $"multiset ({newE.Val})";
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, v);
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
        ArmadaRValue newRV;
        string val;
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not :
            if (e.Type is PointerType) {
              Fail(e.tok, "Can't do not (or any other integer manipulation, for that matter) on a pointer value");
              return new ArmadaRValue(null);
            }
            newRV = ResolveAsRValue(e.E);
            val = $"!({newRV.Val})";
            return new ArmadaRValue(newRV.UndefinedBehaviorAvoidance, val);

          case UnaryOpExpr.Opcode.Cardinality :
            newRV = ResolveAsRValue(e.E);
            val = $"|({newRV.Val})|";
            return new ArmadaRValue(newRV.UndefinedBehaviorAvoidance, val);

          case UnaryOpExpr.Opcode.Allocated :
            newRV = ResolveAsRValue(e.E);
            return ResolveAllocatedExpr(e.tok, newRV, e.E.Type);

          case UnaryOpExpr.Opcode.AddressOf :
            var newLV = ResolveAsLValue(e.E);
            if (newLV == null) {
              Fail(e.tok, "Attempt to get address of value that isn't an lvalue");
              return new ArmadaRValue(null);
            }
            var addr = newLV.GetAddress();
            if (addr == null) {
              Fail(e.tok, "Attempt to get address of value without an address");
              return new ArmadaRValue(null);
            }
            var crashAvoidance = newLV.GetUndefinedBehaviorAvoidanceConstraint();
            return new ArmadaRValue(crashAvoidance, addr);

          case UnaryOpExpr.Opcode.Dereference :
            newRV = ResolveAsRValue(e.E);
            if (newRV == null) {
              return new ArmadaRValue(null);
            }
            return ResolveArmadaDereferenceExprAsRValue(e.tok, newRV, expr.Type);

          case UnaryOpExpr.Opcode.AllocatedArray :
            newRV = ResolveAsRValue(e.E);
            return ResolveAllocatedArrayExpr(e.tok, newRV, e.E.Type);

          case UnaryOpExpr.Opcode.GlobalView :
            return ResolveAsMemoryRValue(e.tok, e.E);

          default :
            Fail(e.tok, $"Armada doesn't support the {e.Op.ToString()} operator");
            return new ArmadaRValue(null);
        }
      }

      if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        var newE = ResolveAsRValue(e.E);
        var v = $"({newE.Val}) as {e.ToType.ToString()}";
        return new ArmadaRValue(newE.UndefinedBehaviorAvoidance, v);
      }

      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        var newE0 = ResolveAsRValue(e.E0);
        var newE1 = ResolveAsRValue(e.E1);
        return ResolveArmadaBinaryExpr(e.tok, e.Type, e.Op, newE0, newE1, e.E0.Type, e.E1.Type);
      }

      if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        Fail(expr.tok, "Ternary operators not supported in Armada");
        return new ArmadaRValue(null);
        /*
        var newE0 = ResolveAsRValue(e.E0);
        var newE1 = ResolveAsRValue(e.E1);
        var newE2 = ResolveAsRValue(e.E2);
        var crashAvoidance = newE0.UndefinedBehaviorAvoidance + newE1.UndefinedBehaviorAvoidance + newE2.UndefinedBehaviorAvoidance;
        var v = ...;
        return new ArmadaRValue(crashAvoidance, v);
        */
      }

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        var newRHSs = ResolveAsRValueList(e.RHSs);
        var newBody = ResolveAsRValue(e.Body);
        var crashAvoidance = newRHSs.UndefinedBehaviorAvoidance;
        var defs = String.Concat(Enumerable.Range(0, e.LHSs.Count).Select(i => $"var {e.LHSs[i].Id} := {newRHSs.Vals[i]}; "));
        if (newBody.CanCauseUndefinedBehavior) {
          crashAvoidance.Add($"{defs}{newBody.UndefinedBehaviorAvoidance.Expr}");
        }
        return new ArmadaRValue(crashAvoidance, $"{defs}{newBody.Val}");
      }

      if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        var newBody = ResolveAsRValue(e.Body);
        var crashAvoidance = newBody.UndefinedBehaviorAvoidance;
        var v = $"label {e.Name} : {newBody.Val}";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is ForallExpr) {
        var e = (ForallExpr)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, e.TypeArgs, e.BoundVars, e.Attributes);
        var v = "forall "
                + String.Join(", ", e.BoundVars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                + " "
                + ResolveTriggers(e.Attributes)
                + (e.Range != null ? " | " + newRange.Val : "")
                + " :: "
                + newTerm.Val;
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is ExistsExpr) {
        var e = (ExistsExpr)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, e.TypeArgs, e.BoundVars, e.Attributes);
        var v = "exists "
                + String.Join(", ", e.BoundVars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                + " "
                + ResolveTriggers(e.Attributes)
                + (e.Range != null ? " | " + newRange.Val : "")
                + " :: "
                + newTerm.Val;
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newTerm = ResolveAsRValue(e.Term);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newTerm, new List<TypeParameter>(), e.BoundVars,
                                                                               e.Attributes);
        var v = (e.Finite ? "set " : "iset ")
                + String.Join(", ", e.BoundVars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                + ResolveTriggers(e.Attributes)
                + " | "
                + newRange.Val
                + (e.Term != null ? " :: " + newTerm.Val : "");
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        var newRange = ResolveAsRValue(e.Range);
        var newRightTerm = ResolveAsRValue(e.Term);
        var newLeftTerm = ResolveAsRValue(e.TermLeft);
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newRightTerm, new List<TypeParameter>(),
                                                                               e.BoundVars, e.Attributes);
        if (e.TermLeft != null) {
          crashAvoidance += GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRange, newLeftTerm, new List<TypeParameter>(),
                                                                              e.BoundVars, e.Attributes);
        }
        var v = (e.Finite ? "map " : "imap ")
                + String.Join(", ", e.BoundVars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                + ResolveTriggers(e.Attributes)
                + (e.Range != null ? " | " + newRange.Val : "")
                + " :: "
                + (e.TermLeft != null ? $"{newLeftTerm.Val} := " : "")
                + newRightTerm.Val;
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        var newRequires = ResolveAsRValue(e.Range);
        var newBody = ResolveAsRValue(e.Body);
        if (e.Reads != null && e.Reads.Any()) {
          Fail(expr.tok, "Can't resolve a lambda expression with a reads clause");
          return new ArmadaRValue(null);
        }
        var crashAvoidance = GetQuantifiedUndefinedBehaviorAvoidanceConstraint(newRequires, newBody, new List<TypeParameter>(), e.BoundVars,
                                                                               null /* no attributes */);
        var v = "lambda "
                + String.Join(", ", e.BoundVars.Select(bv => $"{bv.Name}:{bv.Type.ToString()}"))
                + (e.Range != null ? $" requires {newRequires.Val}" : "")
                + " => "
                + newBody.Val;
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is WildcardExpr) {
        Fail("Can't resolve wildcard expression in this context");
        return new ArmadaRValue(null);
      }

      if (expr is StmtExpr) {
        Fail("Can't resolve statement expression in this context");
        return new ArmadaRValue(null);
      }

      if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        var newTest = ResolveAsRValue(e.Test);
        var newThn = ResolveAsRValue(e.Thn);
        var newEls = ResolveAsRValue(e.Els);
        var crashAvoidance = newTest.UndefinedBehaviorAvoidance;
        if (newThn.CanCauseUndefinedBehavior) {
          crashAvoidance.Add($"({newTest.Val}) ==> ({newThn.UndefinedBehaviorAvoidance.Expr})");
        }
        if (newEls != null && newEls.CanCauseUndefinedBehavior) {
          crashAvoidance.Add($"({newTest.Val}) || ({newEls.UndefinedBehaviorAvoidance.Expr})");
        }
        var v = $"if {newTest.Val} then {newThn.Val} else {newEls.Val}";
        return new ArmadaRValue(crashAvoidance, v);
      }

      if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var newSource = ResolveAsRValue(e.Source);
        var newCases = "";

        bool canCrash = false;
        var crashAvoidanceCases = "";
        foreach (var c in e.Cases) {
          var newBody = ResolveAsRValue(c.Body);
          // I believe that it's best to always use CasePatterns, because we can't be sure that it's resolved.
          var cpHeader = $"case {c.Id}";
          if (c.CasePatterns != null) {
            cpHeader += "(" + String.Join(", ", c.CasePatterns.Select(cp => $"{cp.Var.Name}:{cp.Var.Type.ToString()}")) + ")";
          }
          cpHeader += " => ";
          newCases += (cpHeader + newBody.Val + "\n");

          // Now, add a case to the list of crash-avoidance cases.  We need to get this case
          // even if it's empty (true) since some of the cases might not be empty.

          var crashExpr = newBody.UndefinedBehaviorAvoidance.Expr;
          crashAvoidanceCases += (cpHeader + crashExpr + "\n");
          if (newBody.CanCauseUndefinedBehavior) {
            canCrash = true;
          }
        }

        // The crash-avoidance constraint includes the source's crash-avoidance constraint.  And, if any of
        // the cases can crash, we create a match expression to describe the crash-avoidance constraint
        // and add it to the crash-avoidance constraint.

        var crashAvoidance = newSource.UndefinedBehaviorAvoidance;
        if (canCrash) {
          crashAvoidance.Add($"match {newSource.Val}\n{crashAvoidanceCases}");
        }

        return new ArmadaRValue(crashAvoidance, $"match {newSource.Val}\n{newCases}");
      }

      Fail(expr.tok, $"Can't resolve the following expression as an rvalue since it has an unexpected expression type:  {expr}\n");
      return new ArmadaRValue(null);
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
    private readonly string locv;
    private readonly string t;

    public NormalResolutionContext(NextRoutineConstructor next, ArmadaSymbolTable i_symbols)
      : base(next.s, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      locv = next.locv;
      t = next.t;
    }

    public NormalResolutionContext(string i_lvalueState, NextRoutineConstructor next, ArmadaSymbolTable i_symbols)
      : base(i_lvalueState, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      locv = next.locv;
      t = next.t;
    }

    public NormalResolutionContext(string moduleName, string methodName, ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter)
      : base("s", "s", "tid", methodName, i_symbols, i_failureReporter, moduleName)
    {
      locv = "locv";
      t = "t";
    }

    public override string GetRValueHeap()
    {
      return $"({locv}).heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({locv}).globals";
    }

    public override string GetRValueTopStackFrame()
    {
      return $"({t}).top";
    }
  }

  public class CustomResolutionContext : ResolutionContext
  {
    private readonly string locv;
    private readonly string top;
    private readonly string ghosts;

    public CustomResolutionContext(string i_lvalueState, string i_rvalueState, string i_locv, string i_top,
                                   string i_ghosts, string i_tid, string i_methodName,
                                   ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter)
      : base(i_lvalueState, i_rvalueState, i_tid, i_methodName, i_symbols, i_failureReporter)
    {
      locv = i_locv;
      top = i_top;
      ghosts = i_ghosts;
    }

    public override string GetRValueHeap()
    {
      return $"({locv}).heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({locv}).globals";
    }

    public override string GetRValueGhosts()
    {
      return ghosts;
    }

    public override string GetRValueTopStackFrame()
    {
      return top;
    }

    public override ArmadaRValue ResolveAsMemoryRValue(IToken tok, Expression expr)
    {
      Fail(tok, "Can't use mem() in this context");
      return null;
    }
  }

  public class GlobalInvariantResolutionContext : ResolutionContext
  {
    public GlobalInvariantResolutionContext(string i_s, ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter,
                                            string i_moduleName)
      : base(i_s, i_s, null, null, i_symbols, i_failureReporter, i_moduleName)
    {
    }

    public override string GetRValueHeap()
    {
      return $"({GetRValueState()}).mem.heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({GetRValueState()}).mem.globals";
    }

    public override string GetRValueGhosts()
    {
      return $"({GetRValueState()}).ghosts";
    }

    public override string GetRValueTopStackFrame()
    {
      Fail("Can't refer to a stack variable in a global invariant");
      return null;
    }
  }

  public class YieldPredicateResolutionContext : ResolutionContext
  {
    private readonly string s;

    public YieldPredicateResolutionContext(string i_s, string s_prime, string i_tid,
                                           ArmadaSymbolTable i_symbols, IFailureReporter i_failureReporter, string i_moduleName)
      : base(s_prime, s_prime, i_tid, null, i_symbols, i_failureReporter, i_moduleName)
    {
      s = i_s;
    }

    public override string GetRValueTopStackFrame()
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
    public RequiresResolutionContext(string i_s, string i_tid, string i_methodName, ArmadaSymbolTable i_symbols,
                                     IFailureReporter i_failureReporter, string i_moduleName = null)
      : base(i_s, i_s, i_tid, i_methodName, i_symbols, i_failureReporter, i_moduleName)
    {
    }
  }

  public class EnsuresResolutionContext : ResolutionContext
  {
    private readonly string s;

    public EnsuresResolutionContext(string i_s, string s_prime, string i_tid, string i_methodName,
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

    public BodylessMethodSnapshotResolutionContext(string i_s, string i_tid, string i_methodName, ArmadaSymbolTable i_symbols,
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

    public BodylessMethodPostconditionResolutionContext(NextRoutineConstructor next, ArmadaSymbolTable i_symbols)
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

  public class TSOBypassingResolutionContext : ResolutionContext
  {
    private readonly string mem;
    private readonly string t;

    public TSOBypassingResolutionContext(NextRoutineConstructor next, ArmadaSymbolTable i_symbols)
      : base(next.s, next.s, next.tid, next.method.Name, i_symbols, next)
    {
      mem = $"({next.s}).mem";
      t = next.t;
    }

    public override string GetRValueHeap()
    {
      return $"({mem}).heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({mem}).globals";
    }

    public override string GetRValueTopStackFrame()
    {
      return $"({t}).top";
    }

    public override ArmadaRValue ResolveAsMemoryRValue(IToken tok, Expression expr)
    {
      return ResolveAsRValue(expr);
    }
  }

  public class GlobalViewResolutionContext : ResolutionContext
  {
    private readonly string mem;

    public GlobalViewResolutionContext(string s, string i_tid, string i_methodName, ArmadaSymbolTable i_symbols,
                                       IFailureReporter i_failureReporter, string i_moduleName)
      : base(null, s, i_tid, i_methodName, i_symbols, i_failureReporter, i_moduleName)
    {
      mem = $"({s}).mem";
    }

    public override string GetRValueHeap()
    {
      return $"({mem}).heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({mem}).globals";
    }
  }

  public class EnablingConstraintResolutionContext : ResolutionContext
  {
    private readonly string locv;
    private readonly string top;
    private readonly string ghosts;

    public EnablingConstraintResolutionContext(EnablingConstraintCollector ecc, string methodName, ArmadaSymbolTable symbols)
      : base(ecc.s, ecc.s, ecc.tid, methodName, symbols, ecc)
    {
      locv = ecc.locv;
      top = ecc.top;
      ghosts = ecc.ghosts;
    }

    public override string GetRValueHeap()
    {
      return $"({locv}).heap";
    }

    public override string GetRValueGlobals()
    {
      return $"({locv}).globals";
    }

    public override string GetRValueGhosts()
    {
      return ghosts;
    }

    public override string GetRValueTopStackFrame()
    {
      return top;
    }
  }
}
