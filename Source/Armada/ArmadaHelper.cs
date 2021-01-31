using System;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using static Microsoft.Armada.Predicate;
using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Armada {

  class AH {

    public static void PrintError(Program prog, IToken tok, string s) {
      prog.reporter.Error(MessageSource.Rewriter, tok, s);
      throw new Exception(s);
    }

    public static void PrintError(Program prog, string s) {
      PrintError(prog, Token.NoToken, s);
    }

    public static void PrintWarning(Program prog, IToken tok, string s) {
      prog.reporter.Warning(MessageSource.Rewriter, tok, s);
    }

    public static void PrintWarning(Program prog, string s) {
      PrintWarning(prog, Token.NoToken, s);
    }

    public static Declaration ParseTopLevelDecl(Program prog, string filename, string s) {
      var e = new Errors(new ErrorReporterWrapper(prog.reporter, s));
      return Parser.ParseTopLevelDecl(s, filename, filename, null, prog.DefaultModule, prog.BuiltIns, e);
    }

    public static Expression ParseExpression(Program prog, string filename, string s) {
      var e = new Errors(new ErrorReporterWrapper(prog.reporter, s));
      return Parser.ParseExpression(s, filename, filename, null, prog.DefaultModule, prog.BuiltIns, e);
    }

    public static string AddModuleToIdentifier(string moduleName, string typeName)
    {
      return moduleName != null ? moduleName + "." + typeName : typeName;
    }

    public static IToken MakeToken(string s) {
      var t = new Token();
      t.val = s;
      return t;
    }

    public static Expression SetExprType(Expression e, Type t) {
      if (t != null) {
        e.Type = t;
      }
      return e;
    }

    public static Expression MakeNameSegment(string name, Type type) {
      return SetExprType(new NameSegment(Token.NoToken, name, null), type);
    }

    public static AliasModuleDecl MakeAliasModuleDecl(string s, ModuleDefinition def, bool opened) {
      var t = MakeToken(s);
      return new AliasModuleDecl(new List<IToken>{t}, t, def, opened, new List<IToken>());
    }

    public static AliasModuleDecl MakeAliasModuleDecl(string alias, string target, ModuleDefinition def, bool opened) {
      var t1 = MakeToken(target);
      var t2 = MakeToken(alias);
      return new AliasModuleDecl(new List<IToken>{t1}, t2, def, opened, new List<IToken>());
    }

    public static Type ReferToType(string name, string moduleName = null) {
      return new UserDefinedType(Token.NoToken, AddModuleToIdentifier(moduleName, name), null);
    }

    public static string GetConcreteThreadHandleTypeName() {
      return "uint64";
    }

    public static string GetConcretePointerTypeName() {
      return "uint64";
    }

    public static Type ConcretizeType(Type t) {
      t = t.NormalizeExpand(true);
      if (t is PointerType) {
        return ReferToType(GetConcretePointerTypeName());
      }
      if (t is UserDefinedType) {
        var udt = (UserDefinedType)t;
        if (udt.Name == "Armada_ThreadHandle") {
          return ReferToType(GetConcreteThreadHandleTypeName());
        }
        if (udt.Name == "Armada_Pointer") {
          return ReferToType(GetConcretePointerTypeName());
        }
      }
      return t;
    }

    public static bool TypesMatch(Type t1, Type t2)
    {
      if (t1 is PointerType) {
        if (!(t2 is PointerType)) {
          return false;
        }
        var pt1 = (PointerType)t1;
        var pt2 = (PointerType)t2;
        return TypesMatch(pt1.Arg, pt2.Arg);
      }

      if (t1 is UserDefinedType && t2 is UserDefinedType) {
        var ut1 = (UserDefinedType)t1;
        var ut2 = (UserDefinedType)t2;
        if (ut1.Name == ut2.Name) {
          return true;
        }
      }

      if (t1 is SizedArrayType) {
        if (!(t2 is SizedArrayType)) {
          return false;
        }
        var st1 = (SizedArrayType)t1;
        var st2 = (SizedArrayType)t2;
        var sz1 = st1.Size;
        var sz2 = st2.Size;
        if (sz1 is LiteralExpr && sz2 is LiteralExpr) {
          var le1 = (LiteralExpr)sz1;
          var le2 = (LiteralExpr)sz2;
          if (!le1.Value.Equals(le2.Value)) {
            return false;
          }
        }
        else {
          if (!sz1.Equals(sz2)) {
            return false;
          }
        }
        return TypesMatch(st1.Range, st2.Range);
      }

      return t1.Equals(t2);
    }

    public static string GetObjectType(Type t)
    {
      t = ConcretizeType(t);
      if (t is PointerType) {
        return $"Armada_ObjectTypePrimitive(Armada_PrimitiveType_{GetConcretePointerTypeName()})";
      }
      else if (t is SizedArrayType at) {
        var subtypeConstructor = GetObjectType(at.Range);
        return $"Armada_ObjectTypeArray({subtypeConstructor}, {Printer.ExprToString(at.Size)})";
      }
      else if (IsPrimitiveType(t)) {
        return $"Armada_ObjectTypePrimitive(Armada_PrimitiveType_{t})";
      }
      else if (t is UserDefinedType ut) {
        return $"Armada_StructType_{ut.Name}()";
      }
      else {
        return null;
      }
    }

    public static string GetInvocationOfValidPointer(string h, string p, Type t)
    {
      return $"Armada_ValidPointerToObjectType({h}, {p}, {GetObjectType(t)})";
    }

    public static string GetInvocationOfValidPointerToDynamicArray(string h, string p, Type t, string sz)
    {
      return $"Armada_ValidPointerToObjectType({h}, {p}, Armada_ObjectTypeArray({GetObjectType(t)}, {sz}))";
    }

    public static string GetInvocationOfDescendants(string h, string p, Type t)
    {
      return $"Armada_DescendantsOfPointerToObjectType(({h}).tree, {p}, {GetObjectType(t)})";
    }

    public static string GetInvocationOfDescendantsOfDynamicArray(string h, string p, Type subtype, string sz)
    {
      return $"Armada_DescendantsOfPointerToObjectType(({h}).tree, {p}, Armada_ObjectTypeArray({GetObjectType(subtype)}, {sz}))";
    }

    public static string GetInvocationOfDereferencePointer(string h, string p, Type t)
    {
      if (t is SizedArrayType at) {
        var subinvocation = GetInvocationOfDereferencePointer(h, $"{h}.tree[{p}].children[i]", at.Range);
        return $"var sz := {h}.tree[{p}].ty.sz; seq(sz, i requires 0 <= i < sz => ({subinvocation}))";
      }
      else {
        t = ConcretizeType(t);
        if (AH.IsPrimitiveType(t)) {
          return $"{h}.values[{p}].n_{t}";
        }
        else if (t is UserDefinedType ut) {
          return $"Armada_DereferenceStructPointer_{ut.Name}({h}, {p})";
        }
        else {
          return null;
        }
      }
    }

    public static string GetInvocationOfUpdateValuesViaPointer(string h, string p, string value, Type valueType)
    {
      if (valueType is SizedArrayType at) {
        var invocation = GetInvocationOfUpdateValuesViaPointer(h, $"{h}.tree[{p}].children[i_]", $"({value})[i_]", at.Range);
        return $@"
          set tup_: (Armada_Pointer, Armada_PrimitiveValue), i_: int
            | 0 <= i_ < |{h}.tree[{p}].children| && i_ < |{value}| && tup_ in ({invocation}) :: tup_
        ";
      }
      else {
        var t = ConcretizeType(valueType);
        if (AH.IsPrimitiveType(t)) {
          return $"{{ ({p}, Armada_PrimitiveValue_{t}({value})) }}";
        }
        else if (t is UserDefinedType ut) {
          return $"Armada_UpdateHeapValuesWithStruct_{ut.Name}({h}, {p}, {value})";
        }
        else {
          return null;
        }
      }
    }

    public static string GetInvocationOfUpdatePointer(string h, string p, string value, Type valueType)
    {
      if (AH.IsPrimitiveType(valueType)) {
        var t = AH.ConcretizeType(valueType);
        return $"{h}.(values := Armada_UpdateHeapValuesWithPrimitiveValue({h}.values, {p}, Armada_PrimitiveValue_{t}({value})))";
      }
      else {
        var subinvocation = GetInvocationOfUpdateValuesViaPointer(h, p, value, valueType);
        return $"{h}.(values := Armada_UpdateHeapValuesSimultaneously({h}.values, {subinvocation}))";
      }
    }

    public static List<string> GetPrimitiveTypeNames()
    {
      return new List<string>{ "uint8", "uint16", "uint32", "uint64", "int8", "int16", "int32", "int64" };
    }

    public static bool IsLimitedSizeIntType(Type type)
    {
      type = ConcretizeType(type);
      if (!(type is UserDefinedType)) {
        return false;
      }
      var ut = (UserDefinedType)type;
      return GetPrimitiveTypeNames().Contains(ut.Name);
    }

    public static bool IsPrimitiveType(Type type)
    {
      type = ConcretizeType(type);
      if (!(type is UserDefinedType)) {
        return false;
      }
      var ut = (UserDefinedType)type;
      return GetPrimitiveTypeNames().Contains(ut.Name);
    }

    public static string GetPrimitiveValueField(Type type)
    {
      type = ConcretizeType(type);
      if (!(type is UserDefinedType)) {
        Debug.Assert(false);
        return null;
      }
      var ut = (UserDefinedType)type;
      var primitiveTypeNames = GetPrimitiveTypeNames();
      foreach (var primitiveTypeName in primitiveTypeNames) {
        if (ut.Name == primitiveTypeName) {
          return "n_" + primitiveTypeName;
        }
      }
      Debug.Assert(false);
      return null;
    }

    public static string GetPrimitiveValueConstructorName(Type type)
    {
      type = ConcretizeType(type);
      if (!(type is UserDefinedType)) {
        Debug.Assert(false);
        return null;
      }
      var ut = (UserDefinedType)type;
      var primitiveTypeNames = GetPrimitiveTypeNames();
      foreach (var primitiveTypeName in primitiveTypeNames) {
        if (ut.Name == primitiveTypeName) {
          return "Armada_PrimitiveValue_" + primitiveTypeName;
        }
      }
      Debug.Assert(false);
      return null;
    }

    public static string GetPrimitiveTypeName(Type type)
    {
      type = ConcretizeType(type);
      if (!(type is UserDefinedType)) {
        Debug.Assert(false);
        return null;
      }
      var ut = (UserDefinedType)type;
      var primitiveTypeNames = GetPrimitiveTypeNames();
      foreach (var primitiveTypeName in primitiveTypeNames) {
        if (ut.Name == primitiveTypeName) {
          return "Armada_PrimitiveType_" + primitiveTypeName;
        }
      }
      Debug.Assert(false);
      return null;
    }

    public static int GetNumArrayDimensions(Type outerType, out Type innerType)
    {
      if (outerType is SizedArrayType at) {
        return GetNumArrayDimensions(at.Range, out innerType) + 1;
      }
      innerType = ConcretizeType(outerType);
      return 0;
    }

    public static string CombineStringsWithOr(IEnumerable<string> es)
    {
      var body = String.Join(" || ", es.Select(e => $"({e})"));
      return body.Length == 0 ? "false" : body;
    }

    public static string CombineStringsWithAnd(IEnumerable<string> es)
    {
      var body = String.Join(" && ", es.Select(e => $"({e})"));
      return body.Length == 0 ? "true" : body;
    }

    public static string CombineStringsWithCommas(IEnumerable<string> strs)
    {
      return String.Join(", ", strs);
    }

    public static string CombineStringsWithSetAddition(IEnumerable<string> es)
    {
      var body = String.Join(" + ", es.Select(e => $"({e})"));
      return body.Length == 0 ? "{}" : body;
    }

    public static string ExpandUnderscores(string s)
    {
      return s.Replace("_", "__");
    }

    public static bool IsJustNames(Expression e)
    {
      if (e is NameSegment) {
        return true;
      }
      else if (e is ExprDotName subexpr) {
        return IsJustNames(subexpr.Lhs);
      }
      else {
        return false;
      }
    }

    public static bool GetDereferenceType(Type t, out Type subtype, out string err) {
      subtype = null;
      err = null;
      if (!(t is PointerType)) {
        err = "Attempt to dereference non-pointer type";
        return false;
      }
      PointerType pt = (PointerType)t;
      subtype = pt.Arg;
      return true;
    }

    public static string EnsureIntegerFit(string e, Type sourceType, Type targetType)
    {
      sourceType = ConcretizeType(sourceType);
      targetType = ConcretizeType(targetType);

      if (!(targetType is UserDefinedType)) {
        return e;
      }

      var ut = (UserDefinedType)targetType;
      var primitiveTypeNames = GetPrimitiveTypeNames();
      foreach (var primitiveTypeName in primitiveTypeNames) {
        if (ut.Name == primitiveTypeName) {
          if (IsLimitedSizeIntType(sourceType)) {
            e = $"({e}) as int";
          }
          return $"Armada_CastTo_{primitiveTypeName}({e})";
        }
      }

      return e;
    }

    public static string ConvertToIntIfNotInt(string e, Type ty)
    {
      if (e == null || ty is IntType) {
        return e;
      }
      return $"({e}) as int";
    }

    public static string ConvertToIntIfLimitedSizeInt(string e, Type ty)
    {
      if (IsLimitedSizeIntType(ty)) {
        return $"({e}) as int";
      }
      else {
        return e;
      }
    }

    public static string GetBitWidth(UserDefinedType uty) {
      Match match = Regex.Match(uty.Name, @"^u?int(\d+)$");
      if (!match.Success) {
        throw new Exception("Failed to find the bit-width of: " + uty);
      }
      return "" + match.Groups[1];
    }

    public static string GetLValueRootVariable(Expression expr)
    {
      if (expr == null) {
        return null;
      }

      if (expr is ParensExpression pe) {
        return GetLValueRootVariable(pe.E);
      }

      if (expr is NameSegment ns) {
        return ns.Name;
      }

      if (expr is ExprDotName edn) {
        return GetLValueRootVariable(edn.Lhs);
      }

      if (expr is SeqSelectExpr sse) {
        return GetLValueRootVariable(sse.Seq);
      }

      if (expr is UnaryOpExpr uoe) {
        return GetLValueRootVariable(uoe.E);
      }

      return null;
    }

    public static string TokenToString(IToken tok)
    {
      return $"line {tok.line}, col {tok.col}";
    }
  }
}
