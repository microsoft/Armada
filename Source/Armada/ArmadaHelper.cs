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

    public static Expression SetExprType(Expression e, Type t) {
      if (t != null) {
        e.Type = t;
      }
      return e;
    }

    public static Expression SetExprType(Expression e1, Expression e2) {
      return SetExprType(e1, e2.Type);
    }

    public static Expression SetExprType(Expression e, string t) {
      return SetExprType(e, ReferToType(t));
    }

    public static Type ReferToType(string name, string moduleName = null) {
      return new UserDefinedType(Token.NoToken, AddModuleToIdentifier(moduleName, name), null);
    }

    public static Expression MakeExprDotName(Expression e, string name, Type type) {
      return SetExprType(new ExprDotName(Token.NoToken, e, name, null), type);
    }

    public static Expression MakeExprDotName(Expression e, string name, string type) {
      return MakeExprDotName(e, name, ReferToType(type));
    }

    public static Expression MakeSeqSelectExpr(Expression s, Expression idx, Type type) {
      return SetExprType(new SeqSelectExpr(Token.NoToken, true, s, idx, null), type);
    }

    public static Expression MakeSeqSelectExpr(Expression s, Expression idx, string type) {
      return MakeSeqSelectExpr(s, idx, ReferToType(type));
    }

    public static Expression MakeSeqSliceExpr(Expression s, Expression idx1, Expression idx2) {
      return SetExprType(new SeqSelectExpr(Token.NoToken, false, s, idx1, idx2), s.Type);
    }

    public static Expression MakeSeqUpdateExpr(Expression s, Expression idx, Expression v) {
      return SetExprType(new SeqUpdateExpr(Token.NoToken, s, idx, v), s.Type);
    }

    public static Expression MakeSeqUpdateExpr(IToken tok, Expression s, Expression idx, Expression v) {
      return SetExprType(new SeqUpdateExpr(tok, s, idx, v), s.Type);
    }

    public static Expression MakeDatatypeUpdateExpr(Expression s, string name, Expression v) {
      return SetExprType(new DatatypeUpdateExpr(Token.NoToken, s,
                                                new List<Tuple<IToken, string, Expression>> { Tuple.Create(Token.NoToken, name, v) }),
                         s);
    }

    public static Expression MakeDatatypeUpdateExpr(IToken tok, Expression s, string name, Expression v) {
      return SetExprType(new DatatypeUpdateExpr(tok, s, new List<Tuple<IToken, string, Expression>> { Tuple.Create(tok, name, v) }),
                         s);
    }

    public static Expression MakeDatatypeUpdate2Expr(Expression s, string name1, Expression v1, string name2, Expression v2) {
      return SetExprType(new DatatypeUpdateExpr(Token.NoToken, s,
                                                new List<Tuple<IToken, string, Expression>> {
                                                  Tuple.Create(Token.NoToken, name1, v1),
                                                  Tuple.Create(Token.NoToken, name2, v2)
                                                }),
                         s);
    }

    public static Expression MakeDatatypeUpdate3Expr(Expression s, string name1, Expression v1, string name2, Expression v2,
                                                     string name3, Expression v3) {
      return SetExprType(new DatatypeUpdateExpr(Token.NoToken, s,
                                                new List<Tuple<IToken, string, Expression>> {
                                                  Tuple.Create(Token.NoToken, name1, v1),
                                                  Tuple.Create(Token.NoToken, name2, v2),
                                                  Tuple.Create(Token.NoToken, name3, v3)
                                                }),
                         s);
    }

    public static Expression MakeDatatypeUpdate4Expr(Expression s, string name1, Expression v1, string name2, Expression v2,
                                                     string name3, Expression v3, string name4, Expression v4) {
      return SetExprType(new DatatypeUpdateExpr(Token.NoToken, s,
                                                new List<Tuple<IToken, string, Expression>> {
                                                  Tuple.Create(Token.NoToken, name1, v1),
                                                  Tuple.Create(Token.NoToken, name2, v2),
                                                  Tuple.Create(Token.NoToken, name3, v3),
                                                  Tuple.Create(Token.NoToken, name4, v4)
                                                }),
                         s);
    }

    public static Expression MakeDatatypeUpdate5Expr(Expression s, string name1, Expression v1, string name2, Expression v2,
                                                     string name3, Expression v3, string name4, Expression v4,
                                                     string name5, Expression v5) {
      return SetExprType(new DatatypeUpdateExpr(Token.NoToken, s,
                                                new List<Tuple<IToken, string, Expression>> {
                                                  Tuple.Create(Token.NoToken, name1, v1),
                                                  Tuple.Create(Token.NoToken, name2, v2),
                                                  Tuple.Create(Token.NoToken, name3, v3),
                                                  Tuple.Create(Token.NoToken, name4, v4),
                                                  Tuple.Create(Token.NoToken, name5, v5)
                                                }),
                         s);
    }

    public static Expression MakeNameSegment(string name, Type type) {
      return SetExprType(new NameSegment(Token.NoToken, name, null), type);
    }

    public static Expression MakeNameSegment(string name, string type) {
      return MakeNameSegment(name, ReferToType(type));
    }

    public static Expression MakeApply1(Expression f, Expression e, Type type) {
      return SetExprType(new ApplySuffix(Token.NoToken, f, new List<Expression> { e }), type);
    }

    public static Expression MakeApply1(Expression f, Expression e, string ty) {
      return MakeApply1(f, e, ReferToType(ty));
    }

    public static Expression MakeApply1(string f, Expression e, Type ty) {
      return MakeApply1(MakeNameSegment(f, (Type)null), e, ty);
    }

    public static Expression MakeApply1(string f, Expression e, string ty) {
      return MakeApply1(f, e, ReferToType(ty));
    }

    public static Expression MakeApply2(string f, Expression e1, Expression e2, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), new List<Expression> { e1, e2 }), ty);
    }

    public static Expression MakeApply2(string f, Expression e1, Expression e2, string ty) {
      return MakeApply2(f, e1, e2, ReferToType(ty));
    }

    public static Expression MakeApply3(string f, Expression e1, Expression e2, Expression e3, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), new List<Expression> { e1, e2, e3 }), ty);
    }

    public static Expression MakeApply3(string f, Expression e1, Expression e2, Expression e3, string ty) {
      return MakeApply3(f, e1, e2, e3, ReferToType(ty));
    }

    public static Expression MakeApply4(string f, Expression e1, Expression e2, Expression e3, Expression e4, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), new List<Expression> { e1, e2, e3, e4 }), ty);
    }

    public static Expression MakeApply4(string f, Expression e1, Expression e2, Expression e3, Expression e4, string ty) {
      return MakeApply4(f, e1, e2, e3, e4, ReferToType(ty));
    }

    public static Expression MakeApply5(string f, Expression e1, Expression e2, Expression e3, Expression e4, Expression e5, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), new List<Expression> { e1, e2, e3, e4, e5 }), ty);
    }

    public static Expression MakeApply5(string f, Expression e1, Expression e2, Expression e3, Expression e4, Expression e5, string ty) {
      return MakeApply5(f, e1, e2, e3, e4, e5, ReferToType(ty));
    }

    public static Expression MakeApply6(string f, Expression e1, Expression e2, Expression e3, Expression e4, Expression e5,
                                        Expression e6, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), new List<Expression> { e1, e2, e3, e4, e5, e6 }),
                         ty);
    }

    public static Expression MakeApply6(string f, Expression e1, Expression e2, Expression e3, Expression e4, Expression e5,
                                        Expression e6, string ty) {
      return MakeApply6(f, e1, e2, e3, e4, e5, e6, ReferToType(ty));
    }

    public static Expression MakeApplyN(string f, List<Expression> es, Type ty) {
      return SetExprType(new ApplySuffix(Token.NoToken, MakeNameSegment(f, (Type)null), es), ty);
    }

    public static Expression MakeApplyN(string f, List<Expression> es, string ty) {
      return MakeApplyN(f, es, ReferToType(ty));
    }

    public static Expression MakeIntLiteral(int i) {
      return new LiteralExpr(Token.NoToken, i);
    }

    public static Expression MakeIntLiteral(BigInteger i) {
      return new LiteralExpr(Token.NoToken, i);
    }

    public static Expression MakeZero() {
      return MakeIntLiteral(0);
    }

    public static Expression MakeOne() {
      return MakeIntLiteral(1);
    }

    public static Expression MakeTwo() {
      return MakeIntLiteral(2);
    }

    public static Expression MakeFalse() {
      return new LiteralExpr(Token.NoToken, false);
    }

    public static Expression MakeTrue() {
      return new LiteralExpr(Token.NoToken, true);
    }

    public static Expression MakeUnaryExpr(UnaryOpExpr.Opcode op, Expression e, Type type) {
      return SetExprType(new UnaryOpExpr(Token.NoToken, op, e), type);
    }

    public static Expression MakeCardinalityExpr(Expression e) {
      return MakeUnaryExpr(UnaryOpExpr.Opcode.Cardinality, e, new IntType());
    }

    public static Expression MakeNotExpr(Expression e) {
      return MakeUnaryExpr(UnaryOpExpr.Opcode.Not, e, new BoolType());
    }

    public static Expression MakeBinaryExpr(BinaryExpr.Opcode op, Expression e1, Expression e2, Type type) {
      return SetExprType(new BinaryExpr(Token.NoToken, op, e1, e2), type);
    }

    public static Expression MakeBinaryExpr(BinaryExpr.Opcode op, Expression e1, Expression e2, string type) {
      return MakeBinaryExpr(op, e1, e2, ReferToType(type));
    }

    public static Expression MakeEqExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Eq, e1, e2, new BoolType());
    }

    public static Expression MakeNeqExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Neq, e1, e2, new BoolType());
    }

    public static Expression MakeAndExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.And, e1, e2, new BoolType());
    }

    public static Expression MakeOrExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Or, e1, e2, new BoolType());
    }

    public static Expression MakeImpliesExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Imp, e1, e2, new BoolType());
    }

    public static Expression MakeLeExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Le, e1, e2, new BoolType());
    }

    public static Expression MakeLtExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Lt, e1, e2, new BoolType());
    }

    public static Expression MakeGeExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Ge, e1, e2, new BoolType());
    }

    public static Expression MakeGtExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Gt, e1, e2, new BoolType());
    }

    public static Expression MakeInExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.In, e1, e2, new BoolType());
    }

    public static Expression MakeNotInExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.NotIn, e1, e2, new BoolType());
    }

    public static Expression MakeDisjointExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Disjoint, e1, e2, new BoolType());
    }

    public static Expression MakeAddExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Add, e1, e2, e1.Type);
    }

    public static Expression MakeSubExpr(Expression e1, Expression e2) {
      return MakeBinaryExpr(BinaryExpr.Opcode.Sub, e1, e2, e1.Type);
    }

    public static Expression MakeIfExpr(Expression e_cond, Expression e_true, Expression e_false) {
      return SetExprType(new ITEExpr(Token.NoToken, false /* isExistentialGuard */, e_cond, e_true, e_false), e_true);
    }

    public static Expression MakeForallExpr(BoundVar bvar, Expression term) {
      return SetExprType(new ForallExpr(Token.NoToken, new List<BoundVar> { bvar }, null, term, null), new BoolType());
    }

    public static Expression MakeConversionExpr(Expression e, Type t) {
      return SetExprType(new ConversionExpr(Token.NoToken, e, t), t);
    }

    public static Expression MakeConversionExpr(Expression e, string typeName) {
      return MakeConversionExpr(e, ReferToType(typeName));
    }

    public static Expression MakeEmptySeqDisplayExpr(Type t) {
      return SetExprType(new SeqDisplayExpr(Token.NoToken, new List<Expression>()), new SeqType(t));
    }

    public static Expression MakeEmptySeqDisplayExpr(string typeName) {
      return MakeEmptySeqDisplayExpr(ReferToType(typeName));
    }

    public static Expression MakeSeqDisplayExpr(List<Expression> es) {
      var e = es.ElementAt(0);
      return SetExprType(new SeqDisplayExpr(Token.NoToken, es), MakeSeqType(e.Type));
    }

    public static Expression MakeSeqDisplayExpr(List<Expression> es, Type ty) {
      return SetExprType(new SeqDisplayExpr(Token.NoToken, es), MakeSeqType(ty));
    }

    public static Expression MakeSeqDisplayExpr(List<Expression> es, string typeName) {
      return SetExprType(new SeqDisplayExpr(Token.NoToken, es), MakeSeqType(ReferToType(typeName)));
    }

    public static Expression MakeSetComprehension(List<BoundVar> bvars, Expression range, Expression term) {
      return new SetComprehension(Token.NoToken, true, bvars, range, term, null);
    }

    public static Expression MakeIsetComprehension(List<BoundVar> bvars, Expression range, Expression term) {
      return new SetComprehension(Token.NoToken, false, bvars, range, term, null);
    }

    public static Expression MakeMapComprehension(List<BoundVar> bvars, Expression range, Expression term) {
      return new MapComprehension(Token.NoToken, true, bvars, range, null, term, null);
    }

    public static Expression MakeImapComprehension(List<BoundVar> bvars, Expression range, Expression term) {
      return new MapComprehension(Token.NoToken, false, bvars, range, null, term, null);
    }

    public static Formal MakeFormal(string name, string t) {
      return new Formal(Token.NoToken, name, ReferToType(t), true, false);
    }

    public static Formal MakeFormal(string name, Type t) {
      return new Formal(Token.NoToken, name, t, true, false);
    }

    public static BoundVar MakeBoundVar(string name, Type t) {
      return new BoundVar(Token.NoToken, name, t);
    }

    public static BoundVar MakeBoundVar(string name, string t) {
      return new BoundVar(Token.NoToken, name, ReferToType(t));
    }

    public static Expression MakeLet1Expr(string v, Expression val, Expression body) {
      var bv = MakeBoundVar(v, val.Type);
      var cp = new CasePattern<BoundVar>(Token.NoToken, bv);
      return SetExprType(new LetExpr(Token.NoToken, new List<CasePattern<BoundVar>> { cp }, new List<Expression> { val }, body, true),
                         body);
    }

    public static Expression MakeAssignSuchThatExpr(string v, Expression val, Expression body, string t) {
      var bv = MakeBoundVar(v, ReferToType(t));
      var cp = new CasePattern<BoundVar>(Token.NoToken, bv);
      return SetExprType(new LetExpr(Token.NoToken, new List<CasePattern<BoundVar>> { cp }, new List<Expression> { val }, body, false),
                         body);
    }

    public static Expression MakeLet2Expr(string v1, Expression val1, string v2, Expression val2, Expression body) {
      var bv1 = MakeBoundVar(v1, val1.Type);
      var bv2 = MakeBoundVar(v2, val2.Type);
      var cp1 = new CasePattern<BoundVar>(Token.NoToken, bv1);
      var cp2 = new CasePattern<BoundVar>(Token.NoToken, bv2);
      return SetExprType(new LetExpr(Token.NoToken, new List<CasePattern<BoundVar>> { cp1, cp2 }, new List<Expression> { val1, val2 }, body, true),
                         body);
    }

    public static MatchCaseExpr MakeMatchCaseExpr(string caseString, List<BoundVar> bvs, Expression body)
    {
      return new MatchCaseExpr(Token.NoToken, caseString, bvs, body);
    }

    public static MatchCaseExpr MakeMatchCaseExpr(string caseString, BoundVar bv, Expression body)
    {
      return new MatchCaseExpr(Token.NoToken, caseString, new List<BoundVar> {bv}, body);
    }

    public static MatchCaseExpr MakeMatchCaseExpr(string caseString, Expression body)
    {
      return new MatchCaseExpr(Token.NoToken, caseString, new List<BoundVar>(), body);
    }

    public static Expression MakeMatchExpr(Expression source, List<MatchCaseExpr> cases, Type ty)
    {
      return SetExprType(new MatchExpr(Token.NoToken, source, cases, false), ty);
    }

    public static Expression MakeMatchExpr(Expression source, List<MatchCaseExpr> cases, string typeName)
    {
      return MakeMatchExpr(source, cases, ReferToType(typeName));
    }

    public static DatatypeCtor MakeDatatypeCtor(string name, List<Formal> formals) {
      return new DatatypeCtor(Token.NoToken, name, formals, null);
    }

    public static IndDatatypeDecl MakeDatatypeDecl(ModuleDefinition m, string name, List<DatatypeCtor> ctors) {
      return new IndDatatypeDecl(Token.NoToken, name, m, new List<TypeParameter>(), ctors, new List<MemberDecl>(), null);
    }

    public static TypeSynonymDecl MakeTypeSynonymDecl(ModuleDefinition m, string name, Type ty) {
      return new TypeSynonymDecl(Token.NoToken, name, new TypeParameter.TypeParameterCharacteristics(false), new List<TypeParameter>(), m,
                                 ty, null);
    }

    public static Predicate MakePredicate(string name, List<Formal> formals, Expression body) {
      return new Predicate(Token.NoToken, name, false, false, true, new List<TypeParameter>(), formals,
                           new List<MaybeFreeExpression>(), new List<FrameExpression>(), new List<MaybeFreeExpression>(),
                           new Specification<Expression>(new List<Expression>(), null), body,
                           BodyOriginKind.OriginalOrInherited, null, null);
    }

    public static Predicate MakePredicateWithReq(string name, List<Formal> formals, Expression req, Expression body) {
      return new Predicate(Token.NoToken, name, false, false, true, new List<TypeParameter>(), formals,
                           new List<MaybeFreeExpression> { new MaybeFreeExpression(req) },
                           new List<FrameExpression>(), new List<MaybeFreeExpression>(),
                           new Specification<Expression>(new List<Expression>(), null), body,
                           BodyOriginKind.OriginalOrInherited, null, null);
    }

    public static Function MakeFunction(string name, List<Formal> formals, Expression body) {
      return new Function(Token.NoToken, name, false, false, true, new List<TypeParameter>(), formals, null, body.Type,
                          new List<MaybeFreeExpression>(), new List<FrameExpression>(), new List<MaybeFreeExpression>(),
                          new Specification<Expression>(new List<Expression>(), null), body, null, null);
    }

    public static Function MakeFunctionWithReq(string name, List<Formal> formals, Expression req, Expression body) {
      return new Function(Token.NoToken, name, false, false, true, new List<TypeParameter>(), formals, null, body.Type,
                          new List<MaybeFreeExpression> { new MaybeFreeExpression(req) },
                          new List<FrameExpression>(), new List<MaybeFreeExpression>(),
                          new Specification<Expression>(new List<Expression>(), null), body, null, null);
    }

    public static Function MakeFunctionWithEns(string name, List<Formal> formals, Formal result, Expression ens, Expression body) {
      return new Function(Token.NoToken, name, false, false, true, new List<TypeParameter>(), formals, result, body.Type,
                          new List<MaybeFreeExpression>(), new List<FrameExpression>(),
                          new List<MaybeFreeExpression>() { new MaybeFreeExpression(ens) },
                          new Specification<Expression>(new List<Expression>(), null), body, null, null);
    }

    public static Type MakeFunctionType(Type d, Type r) {
      return new UserDefinedType(Token.NoToken, ArrowType.TotalArrowTypeName(1), new List<Type> { d, r });
    }

    public static Type MakeFunctionType(string d, string r) {
      return MakeFunctionType(ReferToType(d), ReferToType(r));
    }

    public static Type MakeFunctionType(string d, Type r) {
      return MakeFunctionType(ReferToType(d), r);
    }

    public static Type MakeFunctionType(Type d, string r) {
      return MakeFunctionType(d, ReferToType(r));
    }

    public static TypeParameter MakeTypeParameter(string name)
    {
      return new TypeParameter(Token.NoToken, name, TypeParameter.TPVarianceSyntax.NonVariant_Strict,
                               new TypeParameter.TypeParameterCharacteristics(false));
    }

    public static Type MakeMapType(Type d, Type r) {
      return new MapType(true, d, r);
    }

    public static Type MakeMapType(string d, string r) {
      return MakeMapType(ReferToType(d), ReferToType(r));
    }

    public static Type MakeMapType(string d, Type r) {
      return MakeMapType(ReferToType(d), r);
    }

    public static Type MakeMapType(Type d, string r) {
      return MakeMapType(d, ReferToType(r));
    }

    public static Type MakeImapType(Type d, Type r) {
      return new MapType(false, d, r);
    }

    public static Type MakeImapType(string d, string r) {
      return MakeImapType(ReferToType(d), ReferToType(r));
    }

    public static Type MakeImapType(string d, Type r) {
      return MakeImapType(ReferToType(d), r);
    }

    public static Type MakeSeqType(Type t) {
      return new SeqType(t);
    }

    public static Type MakeSeqType(string t) {
      return MakeSeqType(ReferToType(t));
    }

    public static Type MakeSetType(Type t) {
      return new SetType(true, t);
    }

    public static Type MakeSetType(string t) {
      return MakeSetType(ReferToType(t));
    }

    public static Type MakeGenericTypeSpecific(string g, List<Type> ts)
    {
      return new UserDefinedType(Token.NoToken, g, ts);
    }

    public static Type MakeGenericTypeSpecific(string g, Type t)
    {
      return MakeGenericTypeSpecific(g, new List<Type>{t});
    }

    public static Type MakeGenericTypeSpecific(string g, string s)
    {
      return MakeGenericTypeSpecific(g, ReferToType(s));
    }

    public static Type MakeOptionType(Type t) {
      return MakeGenericTypeSpecific("util_option_s.Option", t);
    }

    public static Type MakeOptionType(string t) {
      return MakeOptionType(ReferToType(t));
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

    public static Type MakeGlobalsType(string moduleName = null) {
      return ReferToType(AddModuleToIdentifier(moduleName, "Armada_Globals"));
    }

    public static Type MakeGhostsType(string moduleName = null) {
      return ReferToType(AddModuleToIdentifier(moduleName, "Armada_Ghosts"));
    }

    public static Type MakeStackFrameType(string moduleName = null) {
      return ReferToType(AddModuleToIdentifier(moduleName, "Armada_StackFrame"));
    }

    public static Type MakeThreadType(string moduleName = null) {
      return ReferToType(AddModuleToIdentifier(moduleName, "Armada_Thread"));
    }

    public static Type MakeSharedMemoryType(string moduleName = null) {
      return ReferToType(AddModuleToIdentifier(moduleName, "Armada_SharedMemory"));
    }

    public static Type MakeStackType(string moduleName = null) {
      return MakeSeqType(AddModuleToIdentifier(moduleName, "Armada_ExtendedFrame"));
    }

    public static Type MakeStoreBufferType(string moduleName = null) {
      return MakeSeqType(AddModuleToIdentifier(moduleName, "Armada_StoreBufferEntry"));
    }

    public static Type MakeThreadsType(string moduleName = null) {
      return MakeMapType("Armada_ThreadHandle", AddModuleToIdentifier(moduleName, "Armada_Thread"));
    }

    public static Type MakePointerSetType() {
      return MakeSetType("Armada_Pointer");
    }

    public static Type MakeValuesType() {
      return MakeMapType("Armada_Pointer", "Armada_PrimitiveValue");
    }

    public static Type MakeChildrenType(string moduleName = null) {
      return MakeMapType(AddModuleToIdentifier(moduleName, "Armada_Field"), "Armada_Pointer");
    }

    public static Type MakeLogType() {
      return MakeSeqType("Armada_LogEntry");
    }

    public static Type MakeNextThreadType() {
      return MakeOptionType("Armada_ThreadHandle");
    }

    public static IToken MakeToken(string s) {
      var t = new Token();
      t.val = s;
      return t;
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

    public static Expression GetInvocationOfValidPointer(Expression h, Expression p, Type t)
    {
      t = ConcretizeType(t);
      if (IsPrimitiveType(t)) {
          var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{t}", "Armada_PrimitiveType");
          return MakeApply3("Armada_ValidPointerToPrimitive", h, p, pty, new BoolType());
      }
      else if (t is SizedArrayType) {
        var at = (SizedArrayType)t;
        var sz = at.Size;
        if (at.Range is PointerType) {
          var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{GetConcretePointerTypeName()}", "Armada_PrimitiveType");
          if (sz != null) {
            return MakeApply4($"Armada_ValidPointerToPrimitiveSizedArray", h, p, pty, sz, new BoolType());
          }
          else {
            return MakeApply3($"Armada_ValidPointerToPrimitiveArray", h, p, pty, new BoolType());
          }
        }
        else if (IsPrimitiveType(at.Range)) {
          var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{at.Range}", "Armada_PrimitiveType");
          if (sz != null) {
            return MakeApply4($"Armada_ValidPointerToPrimitiveSizedArray", h, p, pty, sz, new BoolType());
          }
          else {
            return MakeApply3($"Armada_ValidPointerToPrimitiveArray", h, p, pty, new BoolType());
          }
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        else {
          var ut = (UserDefinedType)at.Range;
          if (sz != null) {
            return MakeApply3($"Armada_ValidPointerToStructSizedArray_{ut.Name}", h, p, sz, new BoolType());
          }
          else {
            return MakeApply2($"Armada_ValidPointerToStructArray_{ut.Name}", h, p, new BoolType());
          }
        }
      }
      else if (!(t is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)t;
        return MakeApply2($"Armada_ValidPointerToStruct_{ut.Name}", h, p, new BoolType());
      }
    }

    public static Expression GetInvocationOfAllocatedBy(Expression h, Expression p, Type t)
    {
      t = ConcretizeType(t);
      if (IsPrimitiveType(t)) {
        var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{t}", "Armada_PrimitiveType");
        return MakeApply3($"Armada_AllocatedByPrimitive", h, p, pty, t);
      }
      else if (t is SizedArrayType) {
        var at = (SizedArrayType)t;
        var sz = at.Size;
        if (sz == null) {
          return null;
        }
        if (at.Range is PointerType) {
          var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{GetConcretePointerTypeName()}", "Armada_PrimitiveType");
          return MakeApply3($"Armada_AllocatedByPrimitiveArray", h, p, pty, t);
        }
        else if (IsPrimitiveType(at.Range)) {
          var pty = AH.MakeNameSegment($"Armada_PrimitiveType_{at.Range}", "Armada_PrimitiveType");
          return MakeApply3($"Armada_AllocatedByPrimitiveArray", h, p, pty, t);
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        else {
          var ut = (UserDefinedType)at.Range;
          return MakeApply2($"Armada_AllocatedByStructArray_{ut.Name}", h, p, t);
        }
      }
      else if (!(t is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)t;
        return MakeApply2($"Armada_AllocatedByStruct_{ut.Name}", h, p, t);
      }
    }

    public static Expression GetInvocationOfDereferencePointer(Expression h, Expression p, Type t)
    {
      var ct = ConcretizeType(t);
      if (IsPrimitiveType(ct)) {
        return MakeApply2($"Armada_DereferencePointerToPrimitive_{ct}", h, p, t);
      }
      else if (ct is SizedArrayType) {
        var at = (SizedArrayType)ct;
        if (at.Range is PointerType) {
          return MakeApply2($"Armada_DereferencePointerToPrimitiveArray_{GetConcretePointerTypeName()}", h, p, t);
        }
        else if (IsPrimitiveType(at.Range)) {
          return MakeApply2($"Armada_DereferencePointerToPrimitiveArray_{at.Range}", h, p, t);
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        else {
          var ut = (UserDefinedType)at.Range;
          return MakeApply2($"Armada_DereferencePointerToStructArray_{ut.Name}", h, p, t);
        }
      }
      else if (!(ct is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)ct;
        return MakeApply2($"Armada_DereferencePointerToStruct_{ut.Name}", h, p, t);
      }
    }

    public static Expression GetInvocationOfUpdatePointer(Expression h, Expression p, Expression value)
    {
      var t = ConcretizeType(value.Type);
      if (IsPrimitiveType(t)) {
        return MakeApply3($"Armada_UpdatePointerToPrimitive_{t}", h, p, value, "Armada_Heap");
      }
      else if (t is SizedArrayType) {
        var at = (SizedArrayType)t;
        if (at.Range is PointerType) {
          return MakeApply3($"Armada_UpdatePointerToPrimitiveArray_{GetConcretePointerTypeName()}", h, p, value, "Armada_Heap");
        }
        else if (IsPrimitiveType(at.Range)) {
          return MakeApply3($"Armada_UpdatePointerToPrimitiveArray_{at.Range}", h, p, value, "Armada_Heap");
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        var ut = (UserDefinedType)at.Range;
        return MakeApply3($"Armada_UpdatePointerToStructArray_{ut.Name}", h, p, value, "Armada_Heap");
      }
      else if (!(t is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)t;
        return MakeApply3($"Armada_UpdatePointerToStruct_{ut.Name}", h, p, value, "Armada_Heap");
      }
    }

    public static Expression GetInvocationOfUpdateChild(Expression h, Expression p, Expression field, Expression value, Type t)
    {
      t = ConcretizeType(t);
      if (IsPrimitiveType(t)) {
        return MakeApply4($"Armada_UpdateChildToPrimitive_{t}", h, p, field, value, "Armada_Heap");
      }
      else if (t is SizedArrayType) {
        var at = (SizedArrayType)t;
        if (at.Range is PointerType) {
          return MakeApply4($"Armada_UpdateChildToPrimitiveArray_{GetConcretePointerTypeName()}", h, p, field, value, "Armada_Heap");
        }
        else if (IsPrimitiveType(at.Range)) {
          return MakeApply4($"Armada_UpdateChildToPrimitiveArray_{at.Range}", h, p, field, value, "Armada_Heap");
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        var ut = (UserDefinedType)at.Range;
        return MakeApply4($"Armada_UpdateChildToStructArray_{ut.Name}", h, p, field, value, "Armada_Heap");
      }
      else if (!(t is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)t;
        return MakeApply4($"Armada_UpdateChildToStruct_{ut.Name}", h, p, field, value, "Armada_Heap");
      }
    }

    public static Expression GetInvocationOfPerformFieldUpdate(Expression v, Expression fields, Expression value)
    {
      var t = ConcretizeType(v.Type);
      if (IsPrimitiveType(t)) {
        return MakeApply3($"Armada_PerformFieldUpdateForPrimitive_{t}", v, fields, value, v.Type);
      }
      else if (t is SizedArrayType) {
        var at = (SizedArrayType)t;
        if (at.Range is PointerType) {
          return MakeApply3($"Armada_PerformFieldUpdateForPrimitiveArray_{GetConcretePointerTypeName()}", v, fields, value, v.Type);
        }
        else if (IsPrimitiveType(at.Range)) {
          return MakeApply3($"Armada_PerformFieldUpdateForPrimitiveArray_{at.Range}", v, fields, value, v.Type);
        }
        else if (!(at.Range is UserDefinedType)) {
          return null;
        }
        var ut = (UserDefinedType)at.Range;
        return MakeApply3($"Armada_PerformFieldUpdateForStructArray_{ut.Name}", v, fields, value, v.Type);
      }
      else if (!(t is UserDefinedType)) {
        return null;
      }
      else {
        var ut = (UserDefinedType)t;
        return MakeApply3($"Armada_PerformFieldUpdateForStruct_{ut.Name}", v, fields, value, v.Type);
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

    public static Expression MakePrimitiveValue(Expression e)
    {
      string constructorName = GetPrimitiveValueConstructorName(e.Type);
      return MakeApply1(constructorName, e, "Armada_PrimitiveValue");
    }

    public static Expression CombineExpressionsWithAnd(List<Expression> es)
    {
      Expression all = null;

      foreach (var e in es) {
        if (all == null) {
          all = e;
        }
        else {
          all = MakeAndExpr(all, e);
        }
      }

      if (all == null) {
        return new LiteralExpr(Token.NoToken, true);
      }
      else {
        return all;
      }
    }

    public static Expression CombineExpressionsWithOr(List<Expression> es)
    {
      Expression all = null;

      foreach (var e in es) {
        if (all == null) {
          all = e;
        }
        else {
          all = MakeOrExpr(all, e);
        }
      }

      if (all == null) {
        return new LiteralExpr(Token.NoToken, false);
      }
      else {
        return all;
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

    public static Expression EnsureIntegerFit(Expression e, Type type) {
      e.Type = type;

      type = ConcretizeType(type);

      if (!(type is UserDefinedType)) {
        return e;
      }

      var e_as_int = IsLimitedSizeIntType(type) ? MakeConversionExpr(e, new IntType()) : e;

      var ut = (UserDefinedType)type;
      var primitiveTypeNames = GetPrimitiveTypeNames();
      foreach (var primitiveTypeName in primitiveTypeNames) {
        if (ut.Name == primitiveTypeName) {
          return MakeApply1("Armada_CastTo_" + primitiveTypeName, e_as_int, type);
        }
      }
      return e;
    }

    public static Expression ConvertToIntIfNotInt(Expression e)
    {
      if (e == null || e.Type is IntType) {
        return e;
      }
      return AH.MakeConversionExpr(e, new IntType());
    }

    public static Expression ConvertToIntIfLimitedSizeInt(Expression e)
    {
      if (IsLimitedSizeIntType(e.Type)) {
        return AH.MakeConversionExpr(e, new IntType());
      }
      else {
        return e;
      }
    }

    public static Expression MakeFunctionCallExpr(IToken tok, string name, List<Expression> args, Type targetType) {
      var funcCall = new FunctionCallExpr(tok, name, new ImplicitThisExpr(tok), tok, args);
      var e = SetExprType(funcCall, targetType);
      return e;
    }

    public static string GetBitWidth(UserDefinedType uty) {
      Match match = Regex.Match(uty.Name, @"^u?int(\d+)$");
      if (!match.Success) {
        throw new Exception("Failed to find the bit-width of: " + uty);
      }
      return "" + match.Groups[1];
    }

    public static Expression ConvertToBitVector(Expression e)
    {
      var ty = e.Type;
      if (!(ty is UserDefinedType)) {
        return e;
      }
      var uty = (UserDefinedType)ty;
      Match match = Regex.Match(uty.Name, @"^u?int(\d+)$");
      if (!match.Success) {
        return e;
      }
      var bvTypeName = "bv" + match.Groups[1];

      return MakeFunctionCallExpr(e.tok, "B" + match.Groups[1], new List<Expression>() {e}, ReferToType(bvTypeName));
    }
  }
}
