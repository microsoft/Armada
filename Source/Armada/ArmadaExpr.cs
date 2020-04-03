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

  public abstract class ArmadaLValue
  {
    protected readonly IToken tok;
    protected readonly Type type;

    public ArmadaLValue(IToken i_tok, Type i_type)
    {
      tok = i_tok;
      type = i_type;
    }

    public virtual Type Type { get { return type; } }

    public virtual bool IsHeap() { return false; }
    public virtual bool NoTSO() { return false; }

    public abstract UndefinedBehaviorAvoidanceConstraint GetUndefinedBehaviorAvoidanceConstraint();
    public abstract Expression GetAddress();

    public virtual Expression GetValueInLValueState(ResolutionContext context)
    {
      context.Fail("Internal error:  GetValueInLValueState not supported");
      return null;
    }

    public abstract Expression GetStoreBufferLocation();

    public Expression GetStoreBufferEntry(Expression val_new)
    {
      var loc = GetStoreBufferLocation();
      if (loc == null) {
        return null;
      }
      var primitive_value_constructor = AH.MakeNameSegment(AH.GetPrimitiveValueConstructorName(val_new.Type), "Armada_PrimitiveValue");
      var boxed_val_new = AH.MakeApply1(primitive_value_constructor, val_new, "Armada_PrimitiveValue");
      return AH.MakeApply2("Armada_StoreBufferEntry", loc, boxed_val_new, "Armada_StoreBufferEntry");
    }

    public abstract Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new);

    public Expression UpdateTotalStateBypassingStoreBuffer(ResolutionContext context, IConstraintCollector constraintCollector,
                                                           Expression val_new)
    {
      var s_current = UpdateTotalStateLocationDirectly(context, constraintCollector, val_new);
      return s_current;
    }

    public Expression UpdateTotalStateWithStoreBufferEntry(ResolutionContext context, IConstraintCollector constraintCollector,
                                                           Expression val_new)
    {
      if (NoTSO()) {
        return UpdateTotalStateLocationDirectly(context, constraintCollector, val_new);
      }

      if (!AH.IsPrimitiveType(type)) {
        context.Fail(tok, "Can't do TSO write to non-primitive type; try using ::= instead of :=");
        return null;
      }

      var entry = GetStoreBufferEntry(val_new);
      if (entry == null) {
        context.Fail(tok, "Can't do a TSO write to that location; try using ::= instead of :=");
        return null;
      }

      return AH.MakeApply3("Armada_AppendToThreadStoreBuffer", context.GetLValueState(), context.tid, entry, "Armada_TotalState");
    }

    public abstract ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type ty);
    public abstract ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type ty);
  }

  public class AddressableArmadaLValue : ArmadaLValue
  {
    protected ArmadaRValue address;

    public AddressableArmadaLValue(IToken i_tok, Type i_type, ArmadaRValue i_address)
      : base(i_tok, i_type)
    {
      address = i_address;
    }

    public override bool IsHeap() { return true; }
    public override bool NoTSO() { return false; }

    public override UndefinedBehaviorAvoidanceConstraint GetUndefinedBehaviorAvoidanceConstraint() { return address.UndefinedBehaviorAvoidance; }
    public override Expression GetAddress() { return address.Val; }

    public override Expression GetStoreBufferLocation()
    {
      if (!AH.IsPrimitiveType(type)) {
        return null;
      }

      return AH.MakeApply1("Armada_StoreBufferLocation_Addressable", address.Val, "Armada_StoreBufferLocation");
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      var s = context.GetLValueState();
      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var valid = AH.GetInvocationOfValidPointer(h, address.Val, type);
      if (valid == null) {
        constraintCollector.Fail(tok, $"Type {type} is currently not supported in the heap");
      }
      else {
        constraintCollector.AddUndefinedBehaviorAvoidanceConstraint(valid);
      }

      var h_new = AH.GetInvocationOfUpdatePointer(h, address.Val, val_new);
      if (h_new == null) {
        constraintCollector.Fail(tok, $"Type {type} is currently not supported in the heap");
      }

      var mem_new = AH.MakeDatatypeUpdateExpr(mem, "heap", h_new);
      return AH.MakeDatatypeUpdateExpr(s, "mem", mem_new);
    }

    public override ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type ty)
    {
      if (!(type is UserDefinedType)) {
        context.Fail(i_tok, $"Attempt to take a field ({fieldName}) of non-struct type {type}");
        return null;
      }
      UserDefinedType ut = (UserDefinedType)type;
      if (!context.symbols.DoesStructExist(ut.Name)) {
        context.Fail(i_tok, $"Attempt to take a field ({fieldName}) of non struct type {ut.Name}");
        return null;
      }
      Type fieldType = context.symbols.GetStructFieldType(ut.Name, fieldName);
      if (fieldType == null) {
        context.Fail(i_tok, $"Attempt to take non-existent field ({fieldName}) in struct type {ut.Name}");
        return null;
      }
      if (!AH.TypesMatch(fieldType, ty)) {
        context.Fail(i_tok, $"Field {fieldName} of type {fieldType} used as type {ty}");
        return null;
      }

      var crashAvoidance = address.UndefinedBehaviorAvoidance;

      var s = context.GetLValueState();
      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      crashAvoidance.Add(AH.MakeInExpr(address.Val, tree));

      var node = AH.MakeSeqSelectExpr(tree, address.Val, "Armada_Node");
      var children = AH.MakeExprDotName(node, "children", AH.MakeChildrenType());
      var field = AH.MakeApply1("Armada_FieldStruct",
                                AH.MakeNameSegment($"Armada_FieldType_{ut.Name}'{fieldName}", "Armada_FieldType"),
                                "Armada_Field");
      var child = AH.MakeSeqSelectExpr(children, field, new PointerType(fieldType));
      crashAvoidance.Add(AH.MakeInExpr(field, children));

      return new AddressableArmadaLValue(i_tok, fieldType, new ArmadaRValue(crashAvoidance, child));
    }

    public override ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type ty)
    {
      if (!(type is SizedArrayType)) {
        context.Fail(i_tok, "Attempt to obtain element of non-array type");
        return null;
      }
      SizedArrayType st = (SizedArrayType)type;
      if (!AH.TypesMatch(st.Range, ty)) {
        context.Fail(i_tok, $"Element of type {st.Range} used as type {ty}");
        return null;
      }

      var crashAvoidance = address.UndefinedBehaviorAvoidance + idx1.UndefinedBehaviorAvoidance;

      var s = context.GetLValueState();
      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      var h = AH.MakeExprDotName(mem, "heap", "Armada_Heap");
      var tree = AH.MakeExprDotName(h, "tree", "Armada_Tree");
      crashAvoidance.Add(AH.MakeInExpr(address.Val, tree));

      var node = AH.MakeSeqSelectExpr(tree, address.Val, "Armada_Node");
      var children = AH.MakeExprDotName(node, "children", AH.MakeChildrenType());
      var idx1_as_int = AH.ConvertToIntIfNotInt(idx1.Val);
      var field = AH.MakeApply1("Armada_FieldArrayIndex", idx1_as_int, "Armada_Field");
      var child = AH.MakeSeqSelectExpr(children, field, new PointerType(st.Range));
      crashAvoidance.Add(AH.MakeInExpr(field, children));

      return new AddressableArmadaLValue(i_tok, st.Range, new ArmadaRValue(crashAvoidance, child));
    }
  }

  public abstract class UnaddressableArmadaLValue : ArmadaLValue
  {
    protected UndefinedBehaviorAvoidanceConstraint crashAvoidance;

    public UnaddressableArmadaLValue(IToken i_tok, Type i_type, UndefinedBehaviorAvoidanceConstraint i_crashAvoidance) : base(i_tok, i_type)
    {
      crashAvoidance = i_crashAvoidance;
    }

    public override UndefinedBehaviorAvoidanceConstraint GetUndefinedBehaviorAvoidanceConstraint()
    {
      return crashAvoidance;
    }

    public override Expression GetAddress() { return null; }

    public abstract Expression GetStoreBufferLocationInfo(ref List<Expression> fields);

    public override Expression GetStoreBufferLocation()
    {
      if (!AH.IsPrimitiveType(type)) {
        return null;
      }

      var fields = new List<Expression>();
      var v = GetStoreBufferLocationInfo(ref fields);
      if (v == null) {
        return null;
      }

      var fields_seq = new SeqDisplayExpr(Token.NoToken, fields);
      return AH.MakeApply2("Armada_StoreBufferLocation_Unaddressable", v, fields_seq, "Armada_StoreBufferLocation");
    }

    public override ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type ty)
    {
      if (!(type is UserDefinedType)) {
        context.Fail(i_tok, $"Attempt to take a field ({fieldName}) of non-struct, non-datatype type {type}");
        return null;
      }

      UserDefinedType ut = (UserDefinedType)type;
      if (context.symbols.DoesStructExist(ut.Name)) {
        Type fieldType = context.symbols.GetStructFieldType(ut.Name, fieldName);
        if (fieldType == null) {
          context.Fail(i_tok, $"Attempt to take non-existent field ({fieldName}) in struct type {ut.Name}");
          return null;
        }
        if (!AH.TypesMatch(fieldType, ty)) {
          context.Fail(i_tok, $"Field {fieldName} of type {fieldType} used as type {ty}");
          return null;
        }
      }

      return new UnaddressableFieldArmadaLValue(i_tok, ty, this, crashAvoidance, fieldName, false);
    }

    public override ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type ty)
    {
      var me = GetValueInLValueState(context);
      var sz = AH.MakeCardinalityExpr(me);

      var newUndefinedBehaviorAvoidance = GetUndefinedBehaviorAvoidanceConstraint() + idx1.UndefinedBehaviorAvoidance;

      var idx1val = AH.ConvertToIntIfNotInt(idx1.Val);

      if (type is SizedArrayType) {
        SizedArrayType st = (SizedArrayType)type;
        if (!AH.TypesMatch(st.Range, ty)) {
          context.Fail(i_tok, $"Element of type {st.Range} used as type {ty}");
          return null;
        }

        newUndefinedBehaviorAvoidance.Add(AH.MakeLeExpr(AH.MakeZero(), idx1val));
        newUndefinedBehaviorAvoidance.Add(AH.MakeLtExpr(idx1val, sz));
      }
      else if (type is SeqType) {
        newUndefinedBehaviorAvoidance.Add(AH.MakeLeExpr(AH.MakeZero(), idx1val));
        newUndefinedBehaviorAvoidance.Add(AH.MakeLtExpr(idx1val, sz));
      }
      else if (type is MapType) {
        newUndefinedBehaviorAvoidance.Add(AH.MakeInExpr(idx1val, me));
      }
      else {
        context.Fail(i_tok, $"Attempt to index into something that isn't an array, seq, or map");
        return null;
      }

      return new UnaddressableIndexArmadaLValue(i_tok, ty, this, newUndefinedBehaviorAvoidance, idx1val);
    }
  }

  public class TopStackFrameArmadaLValue : UnaddressableArmadaLValue
  {
    public TopStackFrameArmadaLValue(UndefinedBehaviorAvoidanceConstraint i_crashAvoidance) : base(Token.NoToken, AH.ReferToType("Armada_StackFrame"), i_crashAvoidance)
    {
    }

    public override bool NoTSO() { return true; }

    public override Expression GetValueInLValueState(ResolutionContext context)
    {
      return context.GetLValueTopStackFrame();
    }

    public override Expression GetStoreBufferLocationInfo(ref List<Expression> fields)
    {
      return null;
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      return AH.MakeApply3("Armada_UpdateTSFrame", context.GetLValueState(), context.tid, val_new, "Armada_TotalState");
    }
  }

  public class GlobalsArmadaLValue : UnaddressableArmadaLValue
  {
    public GlobalsArmadaLValue() : base(Token.NoToken, AH.ReferToType("Armada_Globals"), new UndefinedBehaviorAvoidanceConstraint()) { }

    public override bool NoTSO() { return false; }

    public override Expression GetValueInLValueState(ResolutionContext context)
    {
      var s = context.GetLValueState();
      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      return AH.MakeExprDotName(mem, "globals", "Armada_Globals");
    }

    public override Expression GetStoreBufferLocationInfo(ref List<Expression> fields)
    {
      return null;
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      var s = context.GetLValueState();
      var mem = AH.MakeExprDotName(s, "mem", "Armada_SharedMemory");
      var mem_new = AH.MakeDatatypeUpdateExpr(mem, "globals", val_new);
      return AH.MakeDatatypeUpdateExpr(s, "mem", mem_new);
    }
  }

  public class GhostsArmadaLValue : UnaddressableArmadaLValue
  {
    public GhostsArmadaLValue() : base(Token.NoToken, AH.ReferToType("Armada_Ghosts"), new UndefinedBehaviorAvoidanceConstraint()) { }

    public override bool NoTSO() { return true; }

    public override Expression GetValueInLValueState(ResolutionContext context)
    {
      var s = context.GetLValueState();
      return AH.MakeExprDotName(s, "ghosts", "Armada_Ghosts");
    }

    public override Expression GetStoreBufferLocationInfo(ref List<Expression> fields)
    {
      return null;
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      var s = context.GetLValueState();
      return AH.MakeDatatypeUpdateExpr(s, "ghosts", val_new);
    }
  }

  public class UnaddressableFieldArmadaLValue : UnaddressableArmadaLValue
  {
    private readonly UnaddressableArmadaLValue parent;
    private readonly string fieldName;
    public readonly bool noTSO;

    public UnaddressableFieldArmadaLValue(IToken i_tok, Type i_type, UnaddressableArmadaLValue i_parent,
                                          UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, string i_fieldName, bool i_noTSO)
      : base(i_tok, i_type, i_crashAvoidance)
    {
      parent = i_parent;
      fieldName = i_fieldName;
      noTSO = i_noTSO;
    }

    public UnaddressableArmadaLValue GetParent() { return parent; }
    public string GetFieldName() { return fieldName; }

    public override bool NoTSO() { return noTSO || parent.NoTSO(); }

    public override Expression GetValueInLValueState(ResolutionContext context)
    {
      return AH.SetExprType(new ExprDotName(tok, parent.GetValueInLValueState(context), fieldName, null), type);
    }

    public override Expression GetStoreBufferLocationInfo(ref List<Expression> fields) {
      if (parent.NoTSO()) {
        return null;
      }
      if (parent is GlobalsArmadaLValue) {
        return AH.MakeNameSegment($"Armada_GlobalStaticVar_{fieldName}", "Armada_GlobalStaticVar");
      }
      else if (!(parent.Type is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)parent.Type;
        var ret = parent.GetStoreBufferLocationInfo(ref fields);
        if (ret == null) {
          return null;
        }
        var struct_field_type = AH.MakeNameSegment($"Armada_FieldType_{ut.Name}'{fieldName}", "Armada_FieldType");
        var field = AH.MakeApply1("Armada_FieldStruct", struct_field_type, "Armada_Field");
        fields.Add(field);
        return ret;
      }
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      Expression parent_val_old = parent.GetValueInLValueState(context);
      Expression parent_val_new = AH.MakeDatatypeUpdateExpr(tok, parent_val_old, fieldName, val_new);
      return parent.UpdateTotalStateLocationDirectly(context, constraintCollector, parent_val_new);
    }
  }

  public class UnaddressableIndexArmadaLValue : UnaddressableArmadaLValue
  {
    private UnaddressableArmadaLValue parent;
    private Expression index;

    public UnaddressableIndexArmadaLValue(IToken i_tok, Type i_type, UnaddressableArmadaLValue i_parent,
                                          UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, Expression i_index)
      : base(i_tok, i_type, i_crashAvoidance)
    {
      parent = i_parent;
      index = i_index;
    }

    public UnaddressableArmadaLValue GetParent() { return parent; }
    public Expression GetIndex() { return index; }

    public override bool NoTSO() { return parent.NoTSO(); }

    public override Expression GetValueInLValueState(ResolutionContext context)
    {
      return AH.MakeSeqSelectExpr(parent.GetValueInLValueState(context), index, type);
    }

    public override Expression GetStoreBufferLocationInfo(ref List<Expression> fields) {
      if (parent.NoTSO()) {
        return null;
      }

      var ret = parent.GetStoreBufferLocationInfo(ref fields);
      if (ret == null) {
        return null;
      }

      var field = AH.MakeApply1("Armada_FieldArrayIndex", index, "Armada_Field");
      fields.Add(field);
      return ret;
    }

    public override Expression UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                                Expression val_new)
    {
      Expression parent_val_old = parent.GetValueInLValueState(context);
      Expression parent_val_new = AH.MakeSeqUpdateExpr(tok, parent_val_old, index, val_new);
      return parent.UpdateTotalStateLocationDirectly(context, constraintCollector, parent_val_new);
    }
  }
}
