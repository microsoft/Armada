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
    public abstract string GetAddress();

    public virtual string GetValueInLValueState(ResolutionContext context)
    {
      context.Fail("Internal error:  GetValueInLValueState not supported");
      return null;
    }

    public abstract string GetStoreBufferLocation();

    public string GetStoreBufferEntry(string val_new, ArmadaPC pc)
    {
      var loc = GetStoreBufferLocation();
      if (loc == null) {
        return null;
      }
      return $"Armada_StoreBufferEntry({loc}, {AH.GetPrimitiveValueConstructorName(type)}({val_new}), {pc.ToString()})";
    }

    public abstract string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new);

    public string UpdateTotalStateBypassingStoreBuffer(ResolutionContext context, IConstraintCollector constraintCollector,
                                                       string val_new)
    {
      var s_current = UpdateTotalStateLocationDirectly(context, constraintCollector, val_new);
      return s_current;
    }

    public string UpdateTotalStateWithStoreBufferEntry(ResolutionContext context, IConstraintCollector constraintCollector,
                                                       string val_new, ArmadaPC pc)
    {
      if (NoTSO()) {
        return UpdateTotalStateLocationDirectly(context, constraintCollector, val_new);
      }

      if (!AH.IsPrimitiveType(type)) {
        context.Fail(tok, "Can't do TSO write to non-primitive type; try using ::= instead of :=");
        return null;
      }

      var entry = GetStoreBufferEntry(val_new, pc);
      if (entry == null) {
        context.Fail(tok, "Can't do a TSO write to that location; try using ::= instead of :=");
        return null;
      }

      return $"Armada_AppendToThreadStoreBuffer({context.GetLValueState()}, {context.tid}, {entry})";
    }

    public abstract ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type ty);
    public abstract ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type indexType, Type exprType);
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
    public override string GetAddress() { return address.Val; }

    public override string GetStoreBufferLocation()
    {
      if (!AH.IsPrimitiveType(type)) {
        return null;
      }

      return $"Armada_StoreBufferLocation_Addressable({address.Val})";
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      var s = context.GetLValueState();
      var h = $"({s}).mem.heap";
      var valid = AH.GetInvocationOfValidPointer(h, address.Val, type);
      if (valid == null) {
        constraintCollector.Fail(tok, $"Type {type} is currently not supported in the heap");
      }
      else {
        constraintCollector.AddUndefinedBehaviorAvoidanceConstraint(valid);
      }

      var h_new = AH.GetInvocationOfUpdatePointer(h, address.Val, val_new, type);
      if (h_new == null) {
        constraintCollector.Fail(tok, $"Type {type} is currently not supported in the heap");
      }

      return $"{s}.(mem := {s}.mem.(heap := {h_new}))";
    }

    public override ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type targetType)
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
      if (!AH.TypesMatch(fieldType, targetType)) {
        context.Fail(i_tok, $"Field {fieldName} of type {fieldType} used as type {targetType}");
        return null;
      }

      var crashAvoidance = address.UndefinedBehaviorAvoidance;

      var s = context.GetLValueState();
      var h = $"({s}).mem.heap";
      int fieldPos = context.symbols.GetStructFieldPos(ut.Name, fieldName);
      crashAvoidance.Add($"{address.Val} in {h}.tree");
      crashAvoidance.Add($"0 <= {fieldPos} < |{h}.tree[{address.Val}].children|");

      var child = $"{h}.tree[{address.Val}].children[{fieldPos}]";
      return new AddressableArmadaLValue(i_tok, fieldType, new ArmadaRValue(crashAvoidance, child));
    }

    public override ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type indexType, Type exprType)
    {
      if (!(type is SizedArrayType)) {
        context.Fail(i_tok, "Attempt to obtain element of non-array type");
        return null;
      }
      SizedArrayType st = (SizedArrayType)type;
      if (!AH.TypesMatch(st.Range, exprType)) {
        context.Fail(i_tok, $"Element of type {st.Range} used as type {exprType}");
        return null;
      }

      var crashAvoidance = address.UndefinedBehaviorAvoidance + idx1.UndefinedBehaviorAvoidance;

      var s = context.GetLValueState();
      var h = $"({s}).mem.heap";
      var idx1_as_int = AH.ConvertToIntIfNotInt(idx1.Val, indexType);
      crashAvoidance.Add($"{address.Val} in {h}.tree");
      crashAvoidance.Add($"0 <= {idx1_as_int} < |{h}.tree[{address.Val}].children|");

      var child = $"{h}.tree[{address.Val}].children[{idx1_as_int}]";
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

    public override string GetAddress() { return null; }

    public abstract string GetStoreBufferLocationInfo(ref List<string> fields);

    public override string GetStoreBufferLocation()
    {
      if (!AH.IsPrimitiveType(type)) {
        return null;
      }

      var fields = new List<string>();
      var v = GetStoreBufferLocationInfo(ref fields);
      if (v == null) {
        return null;
      }

      var fields_seq = String.Join(", ", fields);
      return $"Armada_StoreBufferLocation_Unaddressable({v}, [{fields_seq}])";
    }

    public override ArmadaLValue ApplyExprDotName(IToken i_tok, ResolutionContext context, string fieldName, Type ty)
    {
      if (!(type is UserDefinedType)) {
        context.Fail(i_tok, $"Attempt to take a field ({fieldName}) of non-struct, non-datatype type {type}");
        return null;
      }

      UserDefinedType ut = (UserDefinedType)type;
      int fieldPos = 0;
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
        fieldPos = context.symbols.GetStructFieldPos(ut.Name, fieldName);
      }

      return new UnaddressableFieldArmadaLValue(i_tok, ty, this, crashAvoidance, fieldName, fieldPos, false);
    }

    public override ArmadaLValue ApplySeqSelect(IToken i_tok, ResolutionContext context, ArmadaRValue idx1, Type indexType, Type exprType)
    {
      var me = GetValueInLValueState(context);
      var sz = $"|{me}|";

      var newUndefinedBehaviorAvoidance = GetUndefinedBehaviorAvoidanceConstraint() + idx1.UndefinedBehaviorAvoidance;

      var idx1val = AH.ConvertToIntIfNotInt(idx1.Val, indexType);

      if (type is SizedArrayType) {
        SizedArrayType st = (SizedArrayType)type;
        if (!AH.TypesMatch(st.Range, exprType)) {
          context.Fail(i_tok, $"Element of type {st.Range} used as type {exprType}");
          return null;
        }

        newUndefinedBehaviorAvoidance.Add($"0 <= {idx1val} < {sz}");
      }
      else if (type is SeqType) {
        newUndefinedBehaviorAvoidance.Add($"0 <= {idx1val} < {sz}");
      }
      else if (type is MapType) {
        // There's no need to consider it undefined behavior if idx1.Val isn't in this map, since we're just
        // using it as an lvalue.  It's fine to update an element of a map that isn't yet in its domain.
        // So we don't need to do:
        //   newUndefinedBehaviorAvoidance.Add($"({idx1.Val}) in ({me})");
        return new UnaddressableIndexArmadaLValue(i_tok, exprType, this, newUndefinedBehaviorAvoidance, idx1.Val);
      }
      else {
        context.Fail(i_tok, $"Attempt to index into something that isn't an array, seq, or map");
        return null;
      }

      return new UnaddressableIndexArmadaLValue(i_tok, exprType, this, newUndefinedBehaviorAvoidance, idx1val);
    }
  }

  public class TopStackVarsArmadaLValue : UnaddressableArmadaLValue
  {
    private string methodName;

    public TopStackVarsArmadaLValue(UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, string i_methodName)
      : base(Token.NoToken, AH.ReferToType($"Armada_StackVars_{i_methodName}"), i_crashAvoidance)
    {
      methodName = i_methodName;
    }

    public override bool NoTSO() { return true; }

    public override string GetValueInLValueState(ResolutionContext context)
    {
      return $"({context.GetLValueTopStackFrame()}).{methodName}";
    }

    public override string GetStoreBufferLocationInfo(ref List<string> fields)
    {
      return null;
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      return $"Armada_UpdateTSFrame({context.GetLValueState()}, {context.tid}, Armada_StackFrame_{methodName}({val_new}))";
    }
  }

  public class GlobalsArmadaLValue : UnaddressableArmadaLValue
  {
    public GlobalsArmadaLValue() : base(Token.NoToken, AH.ReferToType("Armada_Globals"), new UndefinedBehaviorAvoidanceConstraint()) { }

    public override bool NoTSO() { return false; }

    public override string GetValueInLValueState(ResolutionContext context)
    {
      return $"({context.GetLValueState()}).mem.globals";
    }

    public override string GetStoreBufferLocationInfo(ref List<string> fields)
    {
      return null;
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      var s = context.GetLValueState();
      return $"({s}).(mem := ({s}).mem.(globals := {val_new}))";
    }
  }

  public class GhostsArmadaLValue : UnaddressableArmadaLValue
  {
    public GhostsArmadaLValue() : base(Token.NoToken, AH.ReferToType("Armada_Ghosts"), new UndefinedBehaviorAvoidanceConstraint()) { }

    public override bool NoTSO() { return true; }

    public override string GetValueInLValueState(ResolutionContext context)
    {
      return $"({context.GetLValueState()}).ghosts";
    }

    public override string GetStoreBufferLocationInfo(ref List<string> fields)
    {
      return null;
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      return $"({context.GetLValueState()}).(ghosts := {val_new})";
    }
  }

  public class UnaddressableFieldArmadaLValue : UnaddressableArmadaLValue
  {
    private readonly UnaddressableArmadaLValue parent;
    private readonly string fieldName;
    private readonly int fieldPos;
    public readonly bool noTSO;

    public UnaddressableFieldArmadaLValue(IToken i_tok, Type i_type, UnaddressableArmadaLValue i_parent,
                                          UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, string i_fieldName,
                                          int i_fieldPos, bool i_noTSO)
      : base(i_tok, i_type, i_crashAvoidance)
    {
      parent = i_parent;
      fieldName = i_fieldName;
      fieldPos = i_fieldPos;
      noTSO = i_noTSO;
    }

    public UnaddressableArmadaLValue GetParent() { return parent; }
    public string GetFieldName() { return fieldName; }
    public int GetFieldPos() { return fieldPos; }

    public override bool NoTSO() { return noTSO || parent.NoTSO(); }

    public override string GetValueInLValueState(ResolutionContext context)
    {
      return $"({parent.GetValueInLValueState(context)}).{fieldName}";
    }

    public override string GetStoreBufferLocationInfo(ref List<string> fields) {
      if (parent.NoTSO()) {
        return null;
      }
      if (parent is GlobalsArmadaLValue) {
        return $"Armada_GlobalStaticVar_{fieldName}";
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
        fields.Add($"{fieldPos}");
        return ret;
      }
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      string parent_val_old = parent.GetValueInLValueState(context);
      string parent_val_new = $"({parent_val_old}).({fieldName} := {val_new})";
      return parent.UpdateTotalStateLocationDirectly(context, constraintCollector, parent_val_new);
    }
  }

  public class UnaddressableIndexArmadaLValue : UnaddressableArmadaLValue
  {
    private UnaddressableArmadaLValue parent;
    private string index;

    public UnaddressableIndexArmadaLValue(IToken i_tok, Type i_type, UnaddressableArmadaLValue i_parent,
                                          UndefinedBehaviorAvoidanceConstraint i_crashAvoidance, string i_index)
      : base(i_tok, i_type, i_crashAvoidance)
    {
      parent = i_parent;
      index = i_index;
    }

    public UnaddressableArmadaLValue GetParent() { return parent; }
    public string GetIndex() { return index; }

    public override bool NoTSO() { return parent.NoTSO(); }

    public override string GetValueInLValueState(ResolutionContext context)
    {
      return $"({parent.GetValueInLValueState(context)})[{index}]";
    }

    public override string GetStoreBufferLocationInfo(ref List<string> fields) {
      if (parent.NoTSO()) {
        return null;
      }

      var ret = parent.GetStoreBufferLocationInfo(ref fields);
      if (ret == null) {
        return null;
      }

      fields.Add(index);
      return ret;
    }

    public override string UpdateTotalStateLocationDirectly(ResolutionContext context, IConstraintCollector constraintCollector,
                                                            string val_new)
    {
      string parent_val_old = parent.GetValueInLValueState(context);
      string parent_val_new = $"({parent_val_old})[{index} := {val_new}]";
      return parent.UpdateTotalStateLocationDirectly(context, constraintCollector, parent_val_new);
    }
  }
}
