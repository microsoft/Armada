//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.CodeDom;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Reflection;
using System.Security.Principal;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Armada {
  public class ClightTsoCompiler : Compiler {
    public ClightTsoCompiler(ErrorReporter reporter, ReadOnlyCollection<string> otherHeaders)
    : base(reporter) {
      this.headers = otherHeaders;
      this.datatypeDecls = new List<DatatypeDecl>();
      this.armadaMethodParams = new Dictionary<string, List<string>>();
    }

    private ReadOnlyCollection<string> headers;
    private List<DatatypeDecl> datatypeDecls;

    private Dictionary<string, List<string>> armadaMethodParams;

    // Shadowing variables in Compiler.cs
    //new string DafnySetClass = "DafnySet";
    //new string DafnyMultiSetClass = "DafnyMultiset";
    //new string DafnySeqClass = "DafnySequence";
    //new string DafnyMapClass = "DafnyMap";

    public override string TargetLanguage => "ClightTSO";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into ClightTSO", program.Name);
      wr.WriteLine("#include \"DafnyRuntime.h\"");
      foreach (var header in this.headers) {
        wr.WriteLine("#include \"{0}\"", header);
      }
      // TODO: Include appropriate .h file here
      //ReadRuntimeSystem("DafnyRuntime.h", wr);
    }

    protected override void EmitFooter(Program program, TargetWriter wr) {
      /*foreach (var dt in this.datatypeDecls) {
        var wd = wr.NewBlock(String.Format("{0} {1}::{2}{3} get_default({1}::{2}{3}* ignored)",
          DeclareTemplate(dt.TypeArgs),
          dt.Module.CompileName,
          dt.CompileName,
          TemplateMethod(dt.TypeArgs)));
          wd.WriteLine("return {0}::{1}{2}();", dt.Module.CompileName, dt.CompileName, TemplateMethod(dt.TypeArgs));
      }*/
    }

    public override void EmitCallToMain(Method mainMethod, TargetWriter wr) {
      var w = wr.NewBlock("int main()");
      w.WriteLine("_main();");
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = (cw as ClightTsoCompiler.ClassWriter).MethodWriter;
      return wr.NewBlock("int main()");
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, TargetWriter wr)
    {

      var s = string.Format("// namespace {0} ", IdProtect(moduleName));
      wr.WriteLine(s);
      return wr;
    }



    private string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => "typename " + IdName(tp));
    }

    private string DeclareTemplate(List<TypeParameter> typeArgs) {
      var targs = "";
      if (typeArgs.Count > 0) {
        targs = String.Format("template <{0}>", TypeParameters(typeArgs));
      }
      return targs;
    }

    private string DeclareTemplate(List<Type> typeArgs) {
      var targs = "";
      if (typeArgs.Count > 0) {
        targs = String.Format("template <{0}>", Util.Comma(typeArgs, t => "typename " + TypeName(t, null, null)));
      }
      return targs;
    }

    private string TemplateMethod(List<TypeParameter> typeArgs) {
      var targs = "";
      if (typeArgs.Count > 0) {
        targs = String.Format("<{0}>", Util.Comma(typeArgs, ta => ta.CompileName));
      }
      return targs;
    }

    private string TemplateMethod(List<Type> typeArgs) {
      var targs = "";
      if (typeArgs.Count > 0) {
        targs = String.Format("<{0}>", Util.Comma(typeArgs, ta => TypeName(ta, null, null)));
      }
      return targs;
    }

    protected override string GetHelperModuleName() => "_dafny";

    protected Exception NotSupported(String msg) {
      return new Exception(String.Format("{0} is not yet supported", msg));
    }

    protected Exception NotSupported(String msg, Bpl.IToken tok) {
      return new Exception(String.Format("{0} is not yet supported (at {1}:{2}:{3})", msg, tok.filename, tok.line, tok.col));
    }


    protected override IClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      if (isExtern || (superClasses != null && superClasses.Count > 0)) {
        throw NotSupported(String.Format("extern and/or traits in class {0}", name), tok);
      }

      if (typeParameters != null && typeParameters.Count > 0) {
        wr.WriteLine(DeclareTemplate(typeParameters));
      }

      var w = wr.NewBlock(string.Format("struct {0}", name), ";");

      //w.Write("// Constructor\n");
      //w2.Write(string.Format("{0}(", name));
      //var fieldWriter = w.NewBlock(")");
      var fieldWriter = w;
      /*
      if (fullPrintName != null) {
        fieldWriter.WriteLine("this._tname = \"{0}\";", fullPrintName);
      }
      */
      var methodWriter = w;
      return new ClassWriter(name, this, methodWriter, fieldWriter, wr);
    }

    protected override bool SupportsProperties { get => false; }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      throw NotSupported(String.Format("traits in class {0}", name), tok);
      /*
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", IdProtect(name)), ";");
      var fieldWriter = w.NewBlock("constructor ()");
      var methodWriter = w;
      return new ClassWriter(this, methodWriter, fieldWriter);
      */
    }

    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr) {
      // An iterator is compiled as follows:
      //   public class MyIteratorExample
      //   {
      //     public T q;  // in-parameter
      //     public T x;  // yield-parameter
      //     public int y;  // yield-parameter
      //     IEnumerator<object> _iter;
      //
      //     public void _MyIteratorExample(T q) {
      //       this.q = q;
      //       _iter = TheIterator();
      //     }
      //
      //     public void MoveNext(out bool more) {
      //       more =_iter.MoveNext();
      //     }
      //
      //     private IEnumerator<object> TheIterator() {
      //       // the translation of the body of the iterator, with each "yield" turning into a "yield return null;"
      //       yield break;
      //     }
      //   }
      throw NotSupported(String.Format("iterator {0}", iter));

     /*  var cw = CreateClass(IdName(iter), iter.TypeArgs, wr) as ClightTsoCompiler.ClassWriter;
      var w = cw.MethodWriter;
      var instanceFieldsWriter = cw.FieldWriter;
      // here come the fields
      Constructor ct = null;
      foreach (var member in iter.Members) {
        var f = member as Field;
        if (f != null && !f.IsGhost) {
          DeclareField(IdName(f), false, false, f.Type, f.tok, DefaultValue(f.Type, instanceFieldsWriter, f.tok), instanceFieldsWriter);
        } else if (member is Constructor) {
          Contract.Assert(ct == null);  // we're expecting just one constructor
          ct = (Constructor)member;
        }
      }
      Contract.Assert(ct != null);  // we do expect a constructor
      instanceFieldsWriter.WriteLine("this._iter = undefined;");

      // here's the initializer method
      w.Write("{0}(", IdName(ct));
      string sep = "";
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          // here we rely on the parameters and the corresponding fields having the same names
          w.Write("{0}{1}", sep, IdName(p));
          sep = ", ";
        }
      }
      using (var wBody = w.NewBlock(")")) {
        foreach (var p in ct.Ins) {
          if (!p.IsGhost) {
            wBody.WriteLine("this.{0} = {0};", IdName(p));
          }
        }
        wBody.WriteLine("this.__iter = this.TheIterator();");
      }
      // here are the enumerator methods
      using (var wBody = w.NewBlock("MoveNext()")) {
        wBody.WriteLine("let r = this.__iter.next();");
        wBody.WriteLine("return !r.done;");
      }
      var wIter = w.NewBlock("*TheIterator()");
      wIter.WriteLine("let _this = this;");
      return wIter; */
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {

      throw NotSupported("DeclareDatatype");
      // Given:
      // datatype Example1 = Example1(u:uint32, b:bool)
      // datatype Example2 = Ex2a(u:uint32) | Ex2b(b:bool)
      //
      // Produce:
      // struct Example1 {
      //   uint32 u;
      //   bool b;
      //   Example1(uint32 u, bool b) : u (u), b (b) {}
      // };
      // bool is_Example1(struct Example1 d) { return true; }
      //
      // struct Example2_2a {
      //   uint32 u;
      // };
      //
      // struct Example2_2b {
      //   bool b;
      // };
      //
      // struct Example2 {
      //   enum {TAG_2a, TAG_2b} tag;
      //   union {
      //     struct Example2_2a v2a;
      //     struct Example2_2b v2b;
      //   };
      //   static Example2 create_Ex2a(uint32 u) {
      //      Example2 result;
      //      result.tag = TAG_Ex2a;
      //      result.v_Ex2a.u = u;
      //      return result;
      //    }
      //    bool is_Example2_2a() { return tag == Example2::TAG_2a; }
      //    bool is_Example2_2b() { return tag == Example2::TAG_2b; }
      // };
      // bool is_Example2_2a(struct Example2 d) { return d.tag == Example2::TAG_2a; }
      // bool is_Example2_2b(struct Example2 d) { return d.tag == Example2::TAG_2b; }
/*
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.h
        return;
      }

      this.datatypeDecls.Add(dt);

      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);

      // Optimize a not-uncommon case
      if (dt.Ctors.Count == 1) {
        var ctor = dt.Ctors[0];
        var ws = wr.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), DtT_protected), ";");

        // Declare the struct members
        var i = 0;
        var argNames = new List<string>();
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            ws.WriteLine("{0} {1};", TypeName(arg.Type, wr, arg.tok), FormalName(arg, i));
            argNames.Add(FormalName(arg, i));
            i++;
          }
        }

        if (argNames.Count > 0) {
          // Create a constructor with arguments
          ws.Write("{0}(", DtT_protected);
          WriteFormals("", ctor.Formals, ws);
          ws.Write(")");
          if (argNames.Count > 0) {
            // Add initializers
            ws.Write(" :");
            ws.Write(Util.Comma(argNames, nm => String.Format(" {0} ({0})", IdProtect(nm))));
          }

          ws.WriteLine(" {}");
        }

        // Create a constructor with no arguments
        var wc = ws.NewNamedBlock("{0}()", DtT_protected);
        foreach (var arg in ctor.Formals) {
          wc.WriteLine("{0} = {1};", arg.CompileName, DefaultValue(arg.Type, wc, arg.tok));
        }

        // Overload the comparison operator
        ws.WriteLine("friend bool operator==(const {0} &left, const {0} &right) {{ ", DtT_protected);
        ws.Write("\treturn true ");
        foreach (var arg in argNames) {
            ws.WriteLine("\t\t&& left.{0} == right.{0}", arg);
        }
        ws.WriteLine(";\n}");

        // Overload the not-comparison operator
        ws.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", DtT_protected);

        wr.WriteLine("{0}\nbool is_{1}(const struct {2}{3} d) {{ return true; }}", DeclareTemplate(dt.TypeArgs), ctor.CompileName, DtT_protected, TemplateMethod(dt.TypeArgs));
      } else {

        // Create one struct for each constructor
        foreach (var ctor in dt.Ctors) {
          string structName = string.Format("{0}_{1}", DtT_protected, ctor.CompileName);
          var wstruct = wr.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), structName), ";");
          // Declare the struct members
          var i = 0;
          var argNames = new List<string>();
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              wstruct.WriteLine("{0} {1};", TypeName(arg.Type, wr, arg.tok), FormalName(arg, i));
              argNames.Add(FormalName(arg, i));
              i++;
            }
          }

          // Overload the comparison operator
          wstruct.WriteLine("friend bool operator==(const {0} &left, const {0} &right) {{ ", structName);
          wstruct.Write("\treturn true ");
          foreach (var arg in argNames) {
            wstruct.WriteLine("\t\t&& left.{0} == right.{0}", arg);
          }
          wstruct.WriteLine(";\n}");

          // Overload the not-comparison operator
          wstruct.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", structName);
        }

        // Declare the overall tagged union
        var ws = wr.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), DtT_protected), ";");
        ws.Write("enum {");
        ws.Write(Util.Comma(dt.Ctors, nm => String.Format(" TAG_{0}", nm.CompileName)));
        ws.Write("} tag;\n");
        var wu = ws.NewBlock("union ", ";");
        foreach (var ctor in dt.Ctors) {
          wu.WriteLine("struct {2}_{0}{1} v_{0};", ctor.CompileName, TemplateMethod(dt.TypeArgs), DtT_protected);
        }

        // Declare static "constructors" for each Dafny constructor
        foreach (var ctor in dt.Ctors)
        {
          var argNames = new List<string>();
          foreach (Formal arg in ctor.Formals)
          {
            if (!arg.IsGhost)
            {
              argNames.Add(arg.CompileName);
            }
          }

          using (var wc = ws.NewNamedBlock("static {0} create_{1}({2})",
                                           DtT_protected, ctor.CompileName,
                                           DeclareFormals(ctor.Formals))) {
            wc.WriteLine("{0}{1} result;", DtT_protected, TemplateMethod(dt.TypeArgs));
            wc.WriteLine("result.tag = {0}::TAG_{1};", DtT_protected, ctor.CompileName);
            foreach (Formal arg in ctor.Formals)
            {
              wc.WriteLine("result.v_{0}.{1} = {1};", ctor.CompileName, arg.CompileName);
            }
            wc.WriteLine("return result;");
          }
        }

        // Declare a default constructor
        using (var wd = ws.NewNamedBlock(String.Format("{0}()", DtT_protected))) {
          var default_ctor = dt.Ctors[0];   // Arbitrarily choose the first one
          wd.WriteLine("tag = {0}::TAG_{1};", DtT_protected, default_ctor.CompileName);
          foreach (Formal arg in default_ctor.Formals)
          {
            wd.WriteLine("v_{0}.{1} = {2};", default_ctor.CompileName, arg.CompileName, DefaultValue(arg.Type, wd, arg.tok));
          }
        }

        // Declare a default destructor
        ws.WriteLine("~{0}() {{}}", DtT_protected);

        // Declare a default copy constructor (just in case any of our components are non-trivial, i.e., contain smart_ptr)
        using (var wcc = ws.NewNamedBlock(String.Format("{0}(const {0} &other)", DtT_protected))) {
          wcc.WriteLine("tag = other.tag;");
          foreach (var ctor in dt.Ctors) {
            wcc.WriteLine("if (tag == {0}::TAG_{1}) {{ v_{1} = other.v_{1}; }}", DtT_protected, ctor.CompileName);
          }
        }

        // Declare a default copy assignment operator (just in case any of our components are non-trivial, i.e., contain smart_ptr)
        using (var wcc = ws.NewNamedBlock(String.Format("{0}& operator=(const {0} other)", DtT_protected))) {
          wcc.WriteLine("tag = other.tag;");
          foreach (var ctor in dt.Ctors) {
            wcc.WriteLine("if (tag == {0}::TAG_{1}) {{ v_{1} = other.v_{1}; }}", DtT_protected, ctor.CompileName);
          }
          wcc.WriteLine("return *this;");
        }

        // Declare type queries, both as members and general-purpose functions
        foreach (var ctor in dt.Ctors) {
          ws.WriteLine("bool is_{0}() const {{ return tag == {1}{2}::TAG_{0}; }}", ctor.CompileName, DtT_protected, TemplateMethod(dt.TypeArgs));
          wr.WriteLine("{0}\nbool is_{1}(const struct {2}{3} d) {{ return d.tag == {2}{3}::TAG_{1}; }}", DeclareTemplate(dt.TypeArgs), ctor.CompileName, DtT_protected, TemplateMethod(dt.TypeArgs));
        }

        // Overload the comparison operator
        ws.WriteLine("friend bool operator==(const {0} &left, const {0} &right) {{ ", DtT_protected);
        ws.Write("\treturn false");
        foreach (var ctor in dt.Ctors) {
          ws.WriteLine("\t\t|| (left.is_{0}() && right.is_{0}() && left.v_{0} == right.v_{0})", ctor.CompileName);
        }
        ws.WriteLine(";\n}");

        // Overload the not-comparison operator
        ws.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", DtT_protected);

      }
      */
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr)
    {
      throw NotSupported("DeclareNewtype");
//      if (nt.NativeType != null) {
//        if (nt.NativeType.Name != nt.Name) {
//          string nt_name_def, literalSuffice_def;
//          bool needsCastAfterArithmetic_def;
//          GetNativeInfo(nt.NativeType.Sel, out nt_name_def, out literalSuffice_def, out needsCastAfterArithmetic_def);
//          wr.WriteLine("typedef {0} {1};", nt_name_def, nt.Name);
//        }
//        /*
//        var wIntegerRangeBody = w.NewBlock("static *IntegerRange(lo, hi)");
//        var wLoopBody = wIntegerRangeBody.NewBlock("while (lo.isLessThan(hi))");
//        wLoopBody.WriteLine("yield lo.toNumber();");
//        EmitIncrementVar("lo", wLoopBody);
//        */
//      } else {
//        throw NotSupported(String.Format("non-native newtype {0}", nt));
//      }
//      var className = "class_" + IdName(nt);
//      var cw = CreateClass(className, null, wr) as ClightTsoCompiler.ClassWriter;
//      var w = cw.MethodWriter;
//      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
//        var witness = new TargetWriter(w.IndentLevel, true);
//        if (nt.NativeType == null) {
//          TrExpr(nt.Witness, witness, false);
//        } else {
//          TrParenExpr(nt.Witness, witness, false);
//          witness.Write(".toNumber()");
//        }
//
//        DeclareField(className, nt.TypeArgs, "Witness", true, true, nt.BaseType, nt.tok, witness.ToString(), w, wr);
//      }
//
//      string nt_name, literalSuffice;
//      bool needsCastAfterArithmetic;
//      GetNativeInfo(nt.NativeType.Sel, out nt_name, out literalSuffice, out needsCastAfterArithmetic);
//      using (var wDefault = w.NewBlock(string.Format("static {0} get_Default()", nt_name))) {
//        var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
//        var d = TypeInitializationValue(udt, wr, nt.tok, false);
//        wDefault.WriteLine("return {0};", d);
//      }
//      // TODO(xueyuanz): make it compile, probably not correct.
//      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr)
    {
      throw NotSupported("DeclareSubsetType");
      /*if (sst.Name == "nat") {
        return;  // C++ does not support Nats
      }

      string templateDecl = "";
      if (sst.Var.Type is SeqType s) {
        templateDecl = DeclareTemplate(s.TypeArgs[0].TypeArgs);  // We want the type args (if any) for the seq-elt type, not the seq
      } else {
        templateDecl = DeclareTemplate(sst.Var.Type.TypeArgs);
      }
      wr.WriteLine("{2} using {1} = {0};", TypeName(sst.Var.Type, wr, sst.tok), IdName(sst), templateDecl);

      var className = "class_" + IdName(sst);
      var cw = CreateClass(className, sst.TypeArgs, wr) as ClightTsoCompiler.ClassWriter;
      var w = cw.MethodWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(sst.Witness, witness, false);
        DeclareField(className, sst.TypeArgs, "Witness", true, true, sst.Rhs, sst.tok, witness.ToString(), w, wr);
      }

      using (var wDefault = w.NewBlock(String.Format("static {0}{1} get_Default()", IdName(sst), TemplateMethod(sst.TypeArgs)))) {
        var udt = new UserDefinedType(sst.tok, sst.Name, sst, sst.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp)));
        var d = TypeInitializationValue(udt, wr, sst.tok, false);
        wDefault.WriteLine("return {0};", d);
      }*/

    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "uint8";
          break;
        case NativeType.Selection.SByte:
          name = "int8";
          break;
        case NativeType.Selection.UShort:
          name = "uint16";
          break;
        case NativeType.Selection.Short:
          name = "int16";
          break;
        case NativeType.Selection.UInt:
          name = "uint32";
          break;
        case NativeType.Selection.Int:
          name = "int32";
          break;
        case NativeType.Selection.ULong:
          name = "uint64";
          break;
        case NativeType.Selection.Number:
        case NativeType.Selection.Long:
          name = "int64";
          break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter {
      public string ClassName;
      public readonly ClightTsoCompiler Compiler;
      public readonly BlockTargetWriter MethodWriter;
      public readonly BlockTargetWriter FieldWriter;
      public readonly TargetWriter Finisher;

      public ClassWriter(string className, ClightTsoCompiler compiler, BlockTargetWriter methodWriter, BlockTargetWriter fieldWriter, TargetWriter finisher) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(fieldWriter != null);
        this.ClassName = className;
        this.Compiler = compiler;
        this.MethodWriter = methodWriter;
        this.FieldWriter = fieldWriter;
        this.Finisher = finisher;
      }

      public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
        return Compiler.CreateMethod(m, createBody, MethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, MethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, MethodWriter);
      }
      public void DeclareField(string name, List<TypeParameter> targs, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
        Compiler.DeclareField(ClassName, targs, name, isStatic, isConst, type, tok, rhs, FieldWriter, Finisher);
      }
      public TextWriter/*?*/ ErrorWriter() => MethodWriter;
      public void Finish() { }
    }

    protected BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, TargetWriter wr) {
      string targetReturnTypeReplacement = null;
      foreach (var p in m.Outs) {
        if (!p.IsGhost) {
          if (targetReturnTypeReplacement == null) {
            targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
          } else if (targetReturnTypeReplacement != null) {
            // there's more than one out-parameter, so bail
            targetReturnTypeReplacement = null;
            break;
          }
        }
      }

      if (!createBody) {
        return null;
      }

      if (m.TypeArgs.Count != 0) {
        wr.WriteLine(DeclareTemplate(m.TypeArgs));
      }

      wr.Write("{0}{1} {2}",
      m.IsStatic ? "static " : "",
      targetReturnTypeReplacement ?? "void",
      IdName(m));

      wr.Write("(");
      int nIns = WriteFormals("", m.Ins, wr);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wr);
      }

      var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);

      if (targetReturnTypeReplacement != null) {
        var r = new TargetWriter(w.IndentLevel);
        EmitReturn(m.Outs, r);
        w.BodySuffix = r.ToString();
      }
      return w;
    }

    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr) {
      wr.Write("{0}{1} {2}", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (typeArgs != null && typeArgs.Count != 0) {
        throw NotSupported(String.Format("type parameters in function {0}", name), tok);
        //wr.Write("<{0}>", TypeParameters(typeArgs));
      }
      wr.Write("(");
      WriteFormals("", formals, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null;
      } else {
        if (formals.Count > 1) {
          var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
          return w;
        } else {
          var w = wr.NewBlock(")");
          return w;
        }
      }
    }

    new List<TypeParameter> UsedTypeParameters(DatatypeDecl dt) {
      Contract.Requires(dt != null);

      var idt = dt as IndDatatypeDecl;
      if (idt == null) {
        return dt.TypeArgs;
      } else {
        Contract.Assert(idt.TypeArgs.Count == idt.TypeParametersUsedInConstructionByDefaultCtor.Length);
        var tps = new List<TypeParameter>();
        for (int i = 0; i < idt.TypeArgs.Count; i++) {
          if (idt.TypeParametersUsedInConstructionByDefaultCtor[i]) {
            tps.Add(idt.TypeArgs[i]);
          }
        }
        return tps;
      }
    }

    List<Type> UsedTypeParameters(DatatypeDecl dt, List<Type> typeArgs) {
      Contract.Requires(dt != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(dt.TypeArgs.Count == typeArgs.Count);

      var idt = dt as IndDatatypeDecl;
      if (idt == null) {
        return typeArgs;
      } else {
        Contract.Assert(typeArgs.Count == idt.TypeParametersUsedInConstructionByDefaultCtor.Length);
        var ts = new List<Type>();
        for (int i = 0; i < typeArgs.Count; i++) {
          if (idt.TypeParametersUsedInConstructionByDefaultCtor[i]) {
            ts.Add(typeArgs[i]);
          }
        }
        return ts;
      }
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      if (typeParams.Count == 0) {
        return 0;
      } else {
        throw NotSupported("WriteRuntimeTypeDescriptorsFormals");
      }
/*
      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write("{0}{1}", prefix, "rtd$_" + tp.CompileName);
          prefix = ", ";
          c++;
        }
      }
      return c; */
    }

    protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals, Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr) {
      var sep = "";
      var c = 0;
      for (int i = 0; i < typeArgs.Count; i++) {
        var actual = typeArgs[i];
        var formal = formals[i];
        if (useAllTypeArgs || formal.Characteristics.MustSupportZeroInitialization) {
          wr.Write("{0}{1}", sep, RuntimeTypeDescriptor(actual, tok, wr));
          sep = ", ";
          c++;
        }
      }
      return c;
    }

    string RuntimeTypeDescriptor(Type type, Bpl.IToken tok, TextWriter wr) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);
      throw NotSupported(string.Format("RuntimeTypeDescriptor {0} not yet supported", type), tok);
/*
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as bool, since no particular type information is apparently needed for this type
        return "_dafny.Rtd_bool";
      }

      if (xType is BoolType) {
        return "_dafny.Rtd_bool";
      } else if (xType is CharType) {
        return "_dafny.Rtd_char";
      } else if (xType is IntType) {
        return "_dafny.Rtd_int";
      } else if (xType is BigOrdinalType) {
        return "_dafny.BigOrdinal";
      } else if (xType is RealType) {
        return "_dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        if (t.NativeType != null) {
          return "_dafny.Rtd_bv_Native";
        } else {
          return "_dafny.Rtd_bv_NonNative";
        }
      } else if (xType is SetType) {
        return "_dafny.Set";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSet";
      } else if (xType is SeqType) {
        return "_dafny.Seq";
      } else if (xType is MapType) {
        return "_dafny.Map";
      } else if (xType.IsBuiltinArrowType) {
        return "_dafny.Rtd_ref";  // null suffices as a default value, since the function will never be called
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        var tp = udt.ResolvedParam;
        if (tp != null) {
          return string.Format("{0}rtd$_{1}", tp.Parent is ClassDecl ? "this." : "", tp.CompileName);
        }
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "_dafny.Rtd_ref";
        } else if (cl is ClassDecl) {
          return "_dafny.Rtd_ref";
        } else if (cl is DatatypeDecl) {
          var dt = (DatatypeDecl)cl;
          var w = new TargetWriter();
          w.Write("{0}.Rtd(", dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt));
          EmitRuntimeTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), cl.TypeArgs, udt.tok, true, w);
          w.Write(")");
          return w.ToString();
        } else if (xType.IsNonNullRefType) {
          // this initializer shouldn't ever be needed; the compiler is expected to generate an error
          // sooner or later, , but it could be that the the compiler needs to
          // lay down some bits to please the C#'s compiler's different definite-assignment rules.
          return "_dafny.Rtd_ref/";
        } else {
          Contract.Assert(cl is NewtypeDecl || cl is SubsetTypeDecl);
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      } */
    }

    protected BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr) {
      // We don't use getters
      return createBody ? new TargetWriter().NewBlock("") : null;
    }

    protected BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      // We don't use getter/setter pairs; we just embed the trait's fields.
      if (createBody) {
        var abyss = new TargetWriter();
        setterWriter = abyss;
        return abyss.NewBlock("");
      } else {
        setterWriter = null;
        return null;
      }
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      //wr.WriteLine("continue TAIL_CALL_START;");
    }

    protected void Warn(string msg, Bpl.IToken tok) {
      Console.Error.WriteLine("WARNING: {3} ({0}:{1}:{2})", tok.filename, tok.line, tok.col, msg);
    }

    // Use class_name = true if you want the actual name of the class, not the type used when declaring variables/arguments/etc.
    protected string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null, bool class_name=false) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      if (type is SizedArrayType)
      {
        return ((SizedArrayType) type).Arg.ToString();
      } else if (type is PointerType)
      {
        var arg = ((PointerType) type).Arg;
        var arg_name = (arg is SizedArrayType) ? TypeName(arg, wr, null) + "*" : TypeName(arg, wr, null) ;
        return arg_name +  "*";
      } else if (type is UserDefinedType)
      {
        var ty = ((UserDefinedType) type);
        var primitiveTypes = new List<string>
          {"int", "uint8", "uint16", "uint32", "uint64", "int8", "int16", "int32", "int64", "bool", "_default"};
        if (primitiveTypes.Contains(ty.ToString()))
        {
          return ty.ToString();
        }
        else
        {
          return "struct " + (((UserDefinedType) type).ToString());
        }
      }
      else
      {
        throw NotSupported(String.Format("Unknown Type: {0}", type.ToString()));
      }

//      var xType = type.NormalizeExpand();
//      Console.WriteLine("Handling TypeName {0}",xType.ToString());
//
//      if (xType is TypeProxy) {
//        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
//        return "object";
//      }
//
//      if (xType is BoolType) {
//        return "bool";
//      } else if (xType is CharType) {
//        return "char";
//      } else if (xType is IntType || xType is BigOrdinalType) {
//        Warn("BigInteger used", tok);
//        return "BigNumber";
//      } else if (xType is RealType) {
//        Warn("BigRational used", tok);
//        return "Dafny.BigRational";
//      } else if (xType is BitvectorType) {
//        var t = (BitvectorType)xType;
//        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigNumber";
//      } else if (xType.AsNewtype != null) {
//        NativeType nativeType = xType.AsNewtype.NativeType;
//        if (nativeType != null) {
//          return GetNativeTypeName(nativeType);
//        }
//        return TypeName(xType.AsNewtype.BaseType, wr, tok);
//      } else if (xType.IsObjectQ) {
//        return "object";
//      } else if (xType.IsArrayType) {
//        ArrayClassDecl at = xType.AsArrayType;
//        Contract.Assert(at != null);  // follows from type.IsArrayType
//        Type elType = UserDefinedType.ArrayElementType(xType);
//        string typeNameSansBrackets, brackets;
//        //TypeName_SplitArrayName(elType, wr, tok, out typeNameSansBrackets, out brackets);
//        //return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets;
//        if (at.Dims == 1) {
//          return "shared_ptr<vector<" + TypeName(elType, wr, tok, null, false) + ">>";
//        } else {
//          throw NotSupported("Multi-dimensional arrays");
//        }
//      } else if (xType is UserDefinedType) {
//        var udt = (UserDefinedType)xType;
//        var s = FullTypeName(udt, member);
//        var cl = udt.ResolvedClass;
//        bool isHandle = true;
//        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
//          return "ulong";
//        } else if (DafnyOptions.O.IronDafny &&
//            !(xType is ArrowType) &&
//            cl != null &&
//            cl.Module != null &&
//            !cl.Module.IsDefaultModule) {
//          s = cl.FullCompileName;
//        }
//        if (class_name || xType.IsTypeParameter || xType.IsDatatype) {  // Don't add pointer decorations to class names or type parameters
//          return IdProtect(s) + ActualTypeArgs(xType.TypeArgs);
//        } else {
//          return TypeName_UDT(s, udt.TypeArgs, wr, udt.tok);
//        }
//      } else if (xType is SetType) {
//        Type argType = ((SetType)xType).Arg;
//        if (ComplicatedTypeParameterForCompilation(argType)) {
//          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
//        }
//        return DafnySetClass + "<" + TypeName(argType, wr, tok) + ">";
//      } else if (xType is SeqType) {
//        Type argType = ((SeqType)xType).Arg;
//        if (ComplicatedTypeParameterForCompilation(argType)) {
//          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
//        }
//        return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">";
//      } else if (xType is MultiSetType) {
//        Type argType = ((MultiSetType)xType).Arg;
//        if (ComplicatedTypeParameterForCompilation(argType)) {
//          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
//        }
//        return DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">";
//      } else if (xType is MapType) {
//        Type domType = ((MapType)xType).Domain;
//        Type ranType = ((MapType)xType).Range;
//        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
//          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
//        }
//        return DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">";
//      } else if (xType is SizedArrayType) {
//        //TODO(xueyuanz): Handle sized array type
//        return "TODO:SizedArrayType";
//      } else if (xType is PointerType) {
//        return "TODO:PointerType";
//      } else {
//        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
//      }
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass
      return TypeName(type, wr, tok, member, false);
    }

    protected string ClassName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass
      return TypeName(type, wr, tok, member, true);
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok, bool inAutoInitContext)
    {
      var xType = type.NormalizeExpandKeepConstraints();
      Console.WriteLine("Handling Type {0}",xType.ToString());

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
      } else if (xType is IntType || xType is BigOrdinalType) {
        Warn("BigInteger used", tok);
        return "new BigNumber(0)";
      } else if (xType is RealType) {
        Warn("BigRational used", tok);
        return "_dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "new BigNumber(0)";
      } else if (xType is SetType) {
        return "_dafny.Set.Empty";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSet.Empty";
      } else if (xType is SeqType) {
        return string.Format("DafnySequence<{0}>()", TypeName(xType.AsSeqType.Arg, wr, tok, null, true));
      } else if (xType is MapType) {
        return "_dafny.Map.Empty";
      } else if (xType is SizedArrayType) {
        return "{0}";
      } else if (xType is PointerType)
      {
        return "NULL";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        if (udt.ResolvedClass != null && Attributes.Contains(udt.ResolvedClass.Attributes, "extern")) {
          // Assume the external definition includes a default value
          return String.Format("{1}::get_{0}_default()", IdProtect(udt.Name), udt.ResolvedClass.Module.CompileName);
        } else if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization) {
          return String.Format("get_default<{0}>(NULL)", IdProtect(udt.Name));
        } else {
          return null;
          //return string.Format("{0}.Default", RuntimeTypeDescriptor(udt, udt.tok, wr));
        }
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return td.Module.CompileName + "::class_" + td.CompileName + "::Witness";
          //return TypeName(udt, wr, udt.tok, null, true) + "::Witness";
          //return TypeName(udt, wr, udt.tok, null, true) + "()";
          //return "Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return td.Module.CompileName + "::class_" + td.CompileName + "::Witness";
          //return TypeName(udt, wr, udt.tok, null, true) + "::Witness";
          //return TypeName(udt, wr, udt.tok, null, true) + "()";
          //return "Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return null;
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            if (arrayClass.Dims == 1) {
              return "NULL";
            } else {
              return string.Format("_dafny.newArray(nullptr, {0})", Util.Comma(arrayClass.Dims, _ => "0"));
            }
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return null;
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return null;
        }
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var s = dt is TupleTypeDecl ? "Tuple" + (dt as TupleTypeDecl).Dims : FullTypeName(udt);
        var w = new TargetWriter();
        w.Write("{0}{1}()", s, TemplateMethod(udt.TypeArgs));
        /*
        w.Write("{0}.Rtd(", s);
        EmitRuntimeTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), dt.TypeArgs, udt.tok, true, w);
        w.Write(").Default");
        */
        return w.ToString();
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    private string ActualTypeArgs(List<Type> typeArgs) {
      return typeArgs.Count > 0
        ? String.Format(" <{0}> ", Util.Comma(typeArgs, tp => TypeName(tp, null, null))) : "";
    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      return String.Format("std::shared_ptr<{0}{1}>", s, ActualTypeArgs(typeArgs));
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member) {
      // There are no companion classes for Cpp
      var t = TypeName(type, wr, tok, member, true);
      return t;
    }

    // ----- Declarations -------------------------------------------------------------
    protected override void DeclareExternType(OpaqueTypeDecl d, Expression compileTypeHint, TargetWriter wr) {
      if (compileTypeHint.AsStringLiteral() == "struct") {
        wr.WriteLine("// Extern declaration of {1}\n{0} struct {1} {2};", DeclareTemplate(d.TypeArgs), d.Name, TemplateMethod(d.TypeArgs));
      } else {
        Error(d.tok, "Opaque type ('{0}') with unrecognized extern attribute {1} cannot be compiled.  Expected {{:extern compile_type_hint}} ", wr, d.FullName, compileTypeHint.AsStringLiteral());
      }
    }

    protected void DeclareField(string className, List<TypeParameter> targs, string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr, TargetWriter finisher) {

      var t = TypeName(type, wr, tok);
      var pref = "";
      if (isStatic)
      {
        pref = "static ";
        //throw NotSupported("Static field");
      }
      if (type is SizedArrayType)
      {
        var size = ((SizedArrayType) type).Size;
        wr.WriteLine("{0}{1} {2}[{3}];",pref, t, name,((LiteralExpr) size).Value.ToString() );
      }
      else
      {
        wr.WriteLine("{0}{1} {2};", pref, t, name);
      }
    }

    private  void CompileArmadaStruct(ArmadaStruct s,TargetWriter wr) {

      var fieldWriter = wr.NewBlock(string.Format("struct {0};\n" +
                                                  "typedef struct {0} {0};\n" +
                                                  "struct {0}", s.Name),
        ";");
      var isParam = s.Name.StartsWith("_params_of_");
      foreach (string name in s.FieldNames)
      {
        var type = s.GetFieldType(name);
        var t = TypeName(type, fieldWriter, null);

        if (type is SizedArrayType)
        {
          fieldWriter.Write(DeclareSizedArray(name, (SizedArrayType) type, wr, null) + ";");
        }
        else if (isParam) {
          fieldWriter.WriteLine("{0} {1};", t, name);
        }
        else
        {
          fieldWriter.WriteLine("volatile {0} {1};", t, name);
        }
      }
    }
    public override void CompileArmadaStructs(ArmadaStructs structs, TargetWriter wr)
    {
      foreach (string name in structs.StructNames)
      {
        var s = structs.GetStruct(name);
        CompileArmadaStruct(s, wr);
      }
    }

    protected BlockTargetWriter/*?*/ CreateArmadaMethod(Method m, bool createBody, TargetWriter wr) {
      var method_name = m.Name;
      if (IsMain(m)) method_name = "_main";

      string targetReturnTypeReplacement = null;
      foreach (var p in m.Outs) {
        if (!p.IsGhost) {
          if (targetReturnTypeReplacement == null) {
            targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
          } else if (targetReturnTypeReplacement != null) {
            // there's more than one out-parameter, so bail
            targetReturnTypeReplacement = null;
            break;
          }
        }
      }



      if (m.TypeArgs.Count != 0) {
        wr.WriteLine(DeclareTemplate(m.TypeArgs));
      }

      wr.Write("{0} {1}",
        targetReturnTypeReplacement ?? "void",
        method_name);

      wr.Write("(");
      int nIns = WriteFormals("", m.Ins, wr);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wr);
      }

      if (!createBody) {
        wr.WriteLine(");");
        return null;
      }

      var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);

      if (targetReturnTypeReplacement != null) {
        var r = new TargetWriter(w.IndentLevel);
        EmitReturn(m.Outs, r);
        w.BodySuffix = r.ToString();
      }
      return w;
    }

    protected void CreateParamStruct(Method m, TargetWriter wr)
    {
      var method_name = m.Name;
      if (IsMain(m)) method_name = "_main";
      var struct_name = "_params_of_" + method_name;
      var fields = new Dictionary<string, Type>();
      foreach (var formal in m.Ins)
      {
        var name = formal.Name;
        var type = formal.Type;
        fields.Add(name, type);
      }

      var param_struct = new ArmadaStruct(struct_name, fields);
      CompileArmadaStruct(param_struct, wr);
    }

    protected void CreateThreadWrpper (Method m, bool createBody, TargetWriter wr)
    {
      var method_name = m.Name;
      if (IsMain(m)) method_name = "_main";
      var wrapper_name = "_thread_of_" + method_name;
      var struct_name = "_params_of_" + method_name;

      wr.Write("void* {0} (void* vargs)", wrapper_name);
      if (!createBody)
      {
        wr.WriteLine(";");
        return;
      }
      var body_wr = wr.NewBlock("","");
      body_wr.WriteLine("{0} args = *(({0} *) vargs);",struct_name);
      body_wr.Write("{0} (", method_name);
      var sep = "";
      foreach (var formal in m.Ins)
      {
        var name = sep + "args." + formal.Name;
        sep = ",";
        body_wr.Write(name);
      }
      body_wr.WriteLine(");");
      body_wr.WriteLine("return NULL;");
    }
    protected void CompileArmadaMethod(Method m, TargetWriter wr)
    {
      var method_name = m.Name;
      if (IsMain(m))
        method_name = "_main";

      if (m.IsExtern(out _, out _))
      {
        Console.WriteLine("Method {0} is extern",method_name);
        wr.WriteLine("// Skipped extern method {0}", method_name);
        CreateThreadWrpper(m, true, wr);
        return;
      }

      wr.WriteLine("// Beginning of method {0}", method_name);

      // create the writer for the method
      var w = CreateArmadaMethod(m, true, wr);
      if (w != null) {
        int nonGhostOutsCount = 0;
        foreach (var p in m.Outs) {
          if (!p.IsGhost) {
            nonGhostOutsCount++;
          }
        }

        var useReturnStyleOuts = UseReturnStyleOuts(m, nonGhostOutsCount);
        foreach (var p in m.Outs) {
          if (!p.IsGhost) {
            DeclareLocalOutVar(IdName(p), p.Type, p.tok, DefaultValue(p.Type, w, p.tok, true), useReturnStyleOuts, w);
          }
        }

        w = EmitMethodReturns(m, w);

        if (m.Body == null) {
          Error(m.tok, "Method {0} has no body", w, m.FullName);
        } else {
          Contract.Assert(enclosingMethod == null);
          enclosingMethod = m;
          // translate the body of method.
          TrStmtList(m.Body.Body, w);
          Contract.Assert(enclosingMethod == m);
          enclosingMethod = null;
        }

        // create thread wrapper for the method.
        CreateThreadWrpper(m, true, wr);

        wr.WriteLine("// End of method {0}\n",method_name);
      }

      // allow the Main method to be an instance method
      /*if (IsMain(m) && (!m.IsStatic || m.CompileName != "Main")) {
        w = CreateStaticMain(cw);
        if (!m.IsStatic) {
          var c = m.EnclosingClass;
          var typeArgs = c.TypeArgs.ConvertAll(tp => (Type)Type.Bool);
          var ty = new UserDefinedType(m.tok, c.Name, c, typeArgs);
          var wRhs = DeclareLocalVar("b", ty, m.tok, w);
          EmitNew(ty, m.tok, null, wRhs);
          w.WriteLine("b.{0}();", IdName(m));
        } else {
          w.WriteLine("{0}();", IdName(m));
        }
      }*/

    }

    protected void DeclareArmadaGlobalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr) {
      if (type != null) {
        if (type is SizedArrayType)
          wr.Write(DeclareSizedArray(name, (SizedArrayType) type, wr, tok));
        else
          wr.Write("volatile {0} {1}", TypeName(type, wr, tok), name);
      } else {
        throw NotSupported("auto type");
      }
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }


    public void CompileArmadaGlobalVariables(ArmadaGlobalVariableSymbolTable table, TargetWriter wr)
    {
      foreach (var name in table.VariableNames)
      {
        var variable = table.Lookup(name);
        if (variable is GlobalGhostArmadaVariable)
        {
          continue;
        }
        var type = variable.ty;
        if (variable.initialValue == null)
        {
          DeclareArmadaGlobalVar(name, type, null, false,  DefaultValue(type, wr, null), wr);
        }
        else
        {
          var wrhs = new TargetWriter();
          variable.initialValue.Type = variable.ty;
          // xueyuanz: May throw error when rhs is not constant, while this should not be allowed.
          TrExpr(variable.initialValue, wrhs, false);
          var rhs = wrhs.ToString();
          DeclareArmadaGlobalVar(name, type, null, false,  rhs, wr);
        }
      }
    }

    public void UpdateArmadaMethodParams(AllMethodsInfo methods)
    {
      foreach (var methodName in methods.AllMethodNames)
      {
        var methodInfo = methods.LookupMethod(methodName);
        var method = methodInfo.method;
        var param_list = new List<string>();
        foreach (var param in method.Ins)
        {
          param_list.Add(param.Name);
        }
        this.armadaMethodParams.Add(methodName, param_list);
      }
    }

    void CreateParamStructs(AllMethodsInfo methods, TargetWriter wr)
    {
      foreach (var methodName in methods.AllMethodNames)
      {
        var methodInfo = methods.LookupMethod(methodName);
        var method = methodInfo.method;
        // create param struct for the method.
        CreateParamStruct(method, wr);
      }
    }

    void DeclareArmadaMethods(AllMethodsInfo methods, TargetWriter wr)
    {
      foreach (var methodName in methods.AllMethodNames)
      {
        var methodInfo = methods.LookupMethod(methodName);
        var method = methodInfo.method;

        // Skip the method decl if it is extern
        if (!method.IsExtern(out _, out _))
        {
          CreateArmadaMethod(method, false, wr);
        }
        CreateThreadWrpper(method, false, wr);
      }
    }
    void CompileArmadaMethods(AllMethodsInfo methods, TargetWriter wr)
    {
      foreach (var methodName in methods.AllMethodNames)
      {
        var methodInfo = methods.LookupMethod(methodName);
        var method = methodInfo.method;
        CompileArmadaMethod(method, wr);
        if (IsMain(method))
        {
          EmitCallToMain(method, wr);
        }
      }
    }

    public override void CompileArmadaLayer(ModuleDefinition layer, TargetWriter wr)
    {
      var symbols = layer.ArmadaSymbols;
      var globals = symbols.Globals;
      var methods = symbols.AllMethods;
      // Compile the global varibales
      wr.WriteLine("// Global Variables");
      CompileArmadaGlobalVariables(globals, wr);

      // Create the Param structs for each method
      wr.WriteLine("// Param Stucts");
      CreateParamStructs(methods, wr);

      // Update the info about method params for the use of create thread
      UpdateArmadaMethodParams(methods);

      // Declare all methods and their wrappers
      wr.WriteLine("// Method Decls");
      DeclareArmadaMethods(methods, wr);

      // Compile the methods together with their wrappers
      wr.WriteLine("// Methods Defns");
      CompileArmadaMethods(methods, wr);



    }

    public override void CompileArmadaCreateThread(ArmadaCreateThreadStatement stmt, TargetWriter wr)
    {
      Contract.Assert(stmt.Stmt is UpdateStmt);
      var s = (UpdateStmt) stmt.Stmt;
      var bw = wr.NewBlock("//Begin Create Thread\n", "\n//End Create Thread\n" );
      var lhs_name = "_temp_thread_id";

      if (s.Lhss.Count == 0)
      {
        // create a temp tid if there is no LHS
        bw.WriteLine("pthread_t {0};",lhs_name);
      }
      else
      {
        // get the lhs name
        Contract.Assert(s.Lhss.Count == 1);
        var lhs_wr = new TargetWriter();
        TrExpr(s.Lhss[0], lhs_wr, false);
        lhs_name = lhs_wr.ToString();
      }


      Contract.Assert(s.Rhss.Count == 1);
      Contract.Assert(s.Rhss[0] is CreateThreadRhs);

      var rhs = (CreateThreadRhs) s.Rhss[0];
      var method_name = rhs.MethodName.val;
      Contract.Assert(this.armadaMethodParams.ContainsKey(method_name));
      var param_names = this.armadaMethodParams[method_name];

      // create and init param struct
      bw.WriteLine("_params_of_{0}* args = malloc(sizeof(_params_of_{0}));", method_name);
      var index = 0;
      foreach (var arg in rhs.Args)
      {
        var arg_wr = new TargetWriter();
        TrExpr(arg, arg_wr, false);
        var arg_val = arg_wr.ToString();
        var arg_name = param_names[index];
        bw.WriteLine("args->{0} = {1};",arg_name,arg_val);
        index += 1;
      }
      // call pthread_create
      bw.WriteLine("pthread_create((pthread_t*) &({0}), NULL, _thread_of_{1}, (void *) args);",lhs_name,method_name);
    }

    public override void CompileArmadaCompareAndSwap(ArmadaCompareAndSwapStatement stmt, TargetWriter wr)
    {
      var us = (UpdateStmt)stmt.Stmt;
      var crhs = (CompareAndSwapRhs)us.Rhss[0];
      if (us.Lhss.Count > 0) {
        TrExpr(us.Lhss[0], wr, false);
        wr.Write(" = ");
      }
      wr.Write("__sync_val_compare_and_swap(&");
      TrParenExpr(crhs.Target, wr, false);
      wr.Write(", ");
      TrExpr(crhs.OldVal, wr, false);
      wr.Write(", ");
      TrExpr(crhs.NewVal, wr, false);
      wr.WriteLine(");");
    }

    public override void CompileArmadaAtomicExchange(ArmadaAtomicExchangeStatement stmt, TargetWriter wr)
    {
      var us = (UpdateStmt)stmt.Stmt;
      var crhs = (CompareAndSwapRhs)us.Rhss[0];
      if (us.Lhss.Count > 0) {
        TrExpr(us.Lhss[0], wr, false);
        wr.Write(" = ");
      }
      wr.Write("__armada_atomic_exchange(&");
      TrParenExpr(crhs.Target, wr, false);
      wr.Write(", ");
      TrExpr(crhs.NewVal, wr, false);
      wr.WriteLine(");");
    }

    private string DeclareFormalString(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam) {
      if (isInParam) {
        return String.Format("{0}{2} {1}", prefix, name, TypeName(type, null, tok));
      } else {
        return null;
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      var formal_str = DeclareFormalString(prefix, name, type, tok, isInParam);
      if (formal_str != null) {
        wr.Write(formal_str);
        return true;
      } else {
        return false;
      }
    }

    private string DeclareFormals(List<Formal> formals) {
      var i = 0;
      var ret = "";
      var sep = "";
      foreach (Formal arg in formals) {
        if (!arg.IsGhost) {
          string name = FormalName(arg, i);
          string decl = DeclareFormalString(sep, name, arg.Type, arg.tok, arg.InParam);
          if (decl != null) {
            ret += decl;
            sep = ", ";
          }
          i++;
        }
      }
      return ret;
    }

    private string DeclareSizedArray(string name, SizedArrayType type, TargetWriter wr, Bpl.IToken/*?*/ tok)
    {
      var size = type.Size;
      return String.Format("{0} {1}[{2}]", TypeName(type.Arg, wr, tok), name,((LiteralExpr) size).Value.ToString() );
    }
    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr) {
      if (type != null) {
        if (type is SizedArrayType)
          wr.Write(DeclareSizedArray(name, (SizedArrayType) type, wr, tok));
        else
          wr.Write("{0} {1}", TypeName(type, wr, tok), name);
      } else {
        throw NotSupported("auto type");
      }
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }


    protected override TargetWriter DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, TargetWriter wr) {
      if (type != null) {
        wr.Write("{0} ", TypeName(type, wr, tok));
      } else {
        wr.Write("auto ");
      }
      wr.Write("{0} = ", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("auto {0} = ", collectorVarName);
    }
    protected override void DeclareSpecificOutCollector(string collectorVarName, TargetWriter wr, int outCount, List<Type> types, Method m) {
      for (int i = 0; i < types.Count; i++) {
        Formal p = m.Outs[i];
        if (!p.IsGhost) {
          wr.Write($"{TypeName(types[i], wr, p.tok)} {collectorVarName} = ");
          return;
        }
      }
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      wr.Write(ActualTypeArgs(typeArgs));
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return "auto " + target;
    }

    protected override void EmitNull(Type type, TargetWriter wr) {
      wr.Write("NULL");
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitJoinStmt(TargetWriter wr, Expression thread_id)
    {
      var thread_id_wr = new TargetWriter();
      TrExpr(thread_id, thread_id_wr, false);
      var thread_id_val = thread_id_wr.ToString();
      wr.WriteLine("pthread_join((pthread_t){0},NULL);",thread_id_val);
    }

    protected override void EmitFenceStmt(TargetWriter wr)
    {
      wr.WriteLine("asm volatile (\"mfence\" ::: \"memory\");");
    }

    protected override void EmitGotoStmt(TargetWriter wr, string target)
    {
      wr.WriteLine($"goto after_{target};");
    }

    protected override void EmitDeallocStmt(TargetWriter wr, Expression addr)
    {
      var addr_wr = new TargetWriter();
      TrExpr(addr, addr_wr, false);
      var addr_val = addr_wr.ToString();
      wr.WriteLine("free({0});",addr_val);
    }

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      //wr.Write("_dafny::Print(");
      //TrExpr(arg, wr, false);
      //wr.WriteLine(");");
      wr.Write("cout << (");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (!outParams.Any()) {
        wr.WriteLine("return;");
      } else {
        wr.WriteLine("return {0};", Util.Comma(outParams, IdName));
      }
    }

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      var w = wr.ForkSection();
      wr.IndentLess();
      wr.WriteLine("after_{0}: ;", label);
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, TargetWriter wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("goto after_{0};", label);
      }
    }

    protected override void EmitContinue( TargetWriter wr)
    {
      wr.WriteLine("continue;");
    }

    protected override void EmitYield(TargetWriter wr) {
      throw NotSupported("EmitYield");
      //wr.WriteLine("yield null;");
    }

    protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw \"{0}\";", message);
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock("for (auto {0} = 0; {0} < {1}; {0}++)", indexVar, bound);
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock("for (unsigned long long {0} = 1; ; {0} = {0} * 2)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0} += 1;", varName);
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0} = {0} -= 1;", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return string.Format("_dafny.Quantifier");
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type/*?*/ boundVarType, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null) {
      wr.Write("for ({0} {1} : ", boundVarType, boundVar);
      collectionWriter = wr.Fork();
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      } else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", "{0} = {1};", altBoundVarName, boundVar);
      } else {
        return wr.NewBlockWithPrefix(")", "auto {0} = {1};", altBoundVarName, boundVar);
      }
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
      if (cl != null && cl.Name == "object") {
        wr.Write("_dafny.NewObject()");
      } else {
        //string targs = type.TypeArgs.Count > 0
        //  ? String.Format(" <{0}> ", Util.Comma(type.TypeArgs, tp => TypeName(tp, wr, tok))) : "";
        //wr.Write("std::make_shared<{0}{1}> (", TypeName(type, wr, tok, null, true), targs);
        wr.Write("std::make_shared<{0}> (", TypeName(type, wr, tok, null, true));
        EmitRuntimeTypeDescriptorsActuals(type.TypeArgs, cl.TypeArgs, tok, false, wr);
        wr.Write(")");
      }
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      var initValue = mustInitialize ? DefaultValue(elmtType, wr, tok) : null;
      // TODO: Handle initValue
      if (dimensions.Count == 1) {
        // handle the common case of 1-dimensional arrays separately
        wr.Write("make_shared<vector<{0}>>(", TypeName(elmtType, wr, tok));
        TrExpr(dimensions[0], wr, false);
        wr.Write(")");
      } else {
        throw NotSupported("Multi-dimensional arrays", tok);
        // the general case
        /* wr.Write("_dafny.newArray({0}", initValue ?? "undefined");
        foreach (var dim in dimensions) {
          wr.Write(", ");
          TrParenExpr(dim, wr, false);
          wr.Write(".toNumber()");
        }
        wr.Write(")"); */
      }
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("NULL");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("'{0}'", v);
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        // TODO: the string should be converted to a Dafny seq<char>
        TrStringLiteral(str, wr);
      } else if (AsNativeType(e.Type) is NativeType nt) {
        wr.Write("({0}){1}", GetNativeTypeName(nt), (BigInteger)e.Value);
      } else if (e.Value is BigInteger i) {
        EmitIntegerLiteral(i, wr);
      } else if (e.Value is BaseTypes.BigDec) {
        throw NotSupported("EmitLiteralExpr of BaseTypes.BigDec");
        /*
        var n = (BaseTypes.BigDec)e.Value;
        if (0 <= n.Exponent) {
          wr.Write("new _dafny.BigRational(new BigNumber(\"{0}", n.Mantissa);
          for (int i = 0; i < n.Exponent; i++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        } else {
          wr.Write("new _dafny.BigRational(");
          EmitIntegerLiteral(n.Mantissa, wr);
          wr.Write(", new BigNumber(\"1");
          for (int i = n.Exponent; i < 0; i++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        } */
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
    void EmitIntegerLiteral(BigInteger i, TextWriter wr) {
      Contract.Requires(wr != null);
      wr.Write(i);
      /*
      if (i == 0) {
        wr.Write("_dafny.Zero");
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write("_dafny.IntOfInt64({0})", i);
      } else {
        wr.Write("_dafny.IntOfString(\"{0}\")", i);
      }
       */
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      var n = str.Length;
      wr.Write("DafnySequence<char>(");
      if (!isVerbatim) {
        wr.Write("\"{0}\"", str);
      } else {
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i+1 < n && str[i+1] == '\"') {
            wr.Write("\\\"");
            i++;
          } else if (str[i] == '\\') {
            wr.Write("\\\\");
          } else if (str[i] == '\n') {
            wr.Write("\\n");
          } else if (str[i] == '\r') {
            wr.Write("\\r");
          } else {
            wr.Write(str[i]);
          }
        }
        wr.Write("\"");
      }
      wr.Write(")");
    }

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr) {
      throw NotSupported("EmitBitvectorTruncation");
      /*string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      if (bvType.NativeType == null) {
        wr.Write("(");
        var middle = wr.Fork();
        wr.Write(").mod(new BigNumber(2).exponentiatedBy({0}))", bvType.Width);
        return middle;
      } else if (bvType.NativeType.Bitwidth != bvType.Width) {
        // no truncation needed
        return wr;
      } else {
        wr.Write("((");
        var middle = wr.Fork();
        // print in hex, because that looks nice
        wr.Write(") & 0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix);
        return middle;
      }*/
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      throw NotSupported("EmitRotate");
      /*string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      var bv = e0.Type.AsBitVectorType;
      if (bv.Width == 0) {
        tr(e0, wr, inLetExprBody);
      } else {
        wr.Write("_dafny.{0}(", isRotateLeft ? "RotateLeft" : "RotateRight");
        tr(e0, wr, inLetExprBody);
        wr.Write(", (");
        tr(e1, wr, inLetExprBody);
        wr.Write(").toNumber(), {0})", bv.Width);
        if (needsCast) {
          wr.Write(".toNumber()");
        }
      }*/
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr) {
      throw NotSupported("EmitEmptyTupleList");
      //wr.Write("[]", tupleTypeArgs);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      throw NotSupported("EmitAddTupleToList");
      /*wr.Write("{0}.push(_dafny.Tuple.of(", ingredients, tupleTypeArgs);
      var wrTuple = wr.Fork();
      wr.WriteLine("));");
      return wrTuple;*/
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      throw NotSupported("EmitTupleSelect");
      //wr.Write("{0}[{1}]", prefix, i);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public static string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      switch (name) {
        // Taken from: https://www.w3schools.in/cplusplus-tutorial/keywords/
        // Keywords
        case "asm":
        case "auto":
        case "bool":
        case "break":
        case "case":
        case "catch":
        case "char":
        case "class":
        case "const":
        case "const_cast":
        case "continue":
        case "default":
        case "delete":
        case "do":
        case "double":
        case "dynamic_cast":
        case "else":
        case "enum":
        case "explicit":
        case "export":
        case "extern":
        case "false":
        case "float":
        case "for":
        case "friend":
        case "goto":
        case "if":
        case "inline":
        case "int":
        case "long":
        case "mutable":
        case "namespace":
        case "new":
        case "operator":
        case "private":
        case "protected":
        case "public":
        case "register":
        case "reinterpret_cast":
        case "return":
        case "short":
        case "signed":
        case "sizeof":
        case "static":
        case "static_cast":
        case "struct":
        case "switch":
        case "template":
        case "this":
        case "throw":
        case "true":
        case "try":
        case "typedef":
        case "typeid":
        case "typename":
        case "union":
        case "unsigned":
        case "using":
        case "virtual":
        case "void":
        case "volatile":
        case "wchar_t":
        case "while":

        // Also reserved
        case "And":
        case "and_eq":
        case "bitand":
        case "bitor":
        case "compl":
        case "not":
        case "not_eq":
        case "or":
        case "or_eq":
        case "xor":
        case "xor_eq":
          return name + "_";
        default:
          return name;
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        throw NotSupported(string.Format("UserDefinedTypeName {0}", udt.Name));
        //return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      } else if (cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cl.Module.Attributes, "extern") &&
                 member != null && Attributes.Contains(member.Attributes, "extern")) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.Module.IsDefaultModule); // default module is not marked ":extern"
        return IdProtect(cl.Module.CompileName);
      } else if (Attributes.Contains(cl.Attributes, "extern")) {
        return IdProtect(cl.Module.CompileName) + "::" + IdProtect(cl.Name);
      } else if (cl is TupleTypeDecl) {
        var tuple = cl as TupleTypeDecl;
        return "Tuple" + tuple.Dims;
      } else {
        return IdProtect(cl.Module.CompileName) + "::" + IdProtect(cl.CompileName);
      }
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      EmitDatatypeValue(dtv, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeValue dtv, DatatypeCtor ctor, bool isCoCall, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.CompileName;
      var ctorName = ctor.CompileName;

      if (dt is TupleTypeDecl) {
        var tuple = dt as TupleTypeDecl;
        var types = new List<Type>();
        foreach (var arg in dtv.Arguments) {
          types.Add(arg.Type);
        }
        wr.Write("Tuple{0}{1}({2})", tuple.Dims, TemplateMethod(types), arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate:  Dt.create_Ctor(arguments)
        if (dt.Ctors.Count == 1) {
          wr.Write("{3}::{0}{1}({2})",
            dtName,
            TemplateMethod(dt.TypeArgs),
            arguments,
            dt.Module.CompileName);
        } else {
          wr.Write("{4}::{0}{1}::create_{2}({3})",
            dtName, ActualTypeArgs(dtv.InferredTypeArgs), ctorName,
            arguments, dt.Module.CompileName);
        }

      } else {
        // Co-recursive call
        // Generate:  Dt.lazy_Ctor(($dt) => Dt.create_Ctor($dt, args))
        wr.Write("{0}.lazy_{1}(($dt) => ", dtName, ctorName);
        wr.Write("{0}.create_{1}($dt{2}{3})", dtName, ctorName, arguments.Length == 0 ? "" : ", ", arguments);
        wr.Write(")");
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          throw NotSupported("taking an array's length");
          //break;
        case SpecialField.ID.Floor:
          compiledName = "int()";
          break;
        case SpecialField.ID.IsLimit:
          throw NotSupported("IsLimit");
        case SpecialField.ID.IsSucc:
          throw NotSupported("IsSucc");
        case SpecialField.ID.Offset:
          throw NotSupported("Offset");
        case SpecialField.ID.IsNat:
          throw NotSupported("IsNat");
        case SpecialField.ID.Keys:
          compiledName = "dafnyKeySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "dafnyValues()";
          break;
        case SpecialField.ID.Items:
          compiledName = "Items()";
          break;
        case SpecialField.ID.Reads:
          compiledName = "_reads";
          break;
        case SpecialField.ID.Modifies:
          compiledName = "_modifies";
          break;
        case SpecialField.ID.New:
          compiledName = "_new";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr) {
      var wSource = wr.Fork();
      if (isLValue && member is ConstantField) {
        wr.Write(".{0}", member.Name);
      } else if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl)
      {
        throw NotSupported("datatype");
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        throw NotSupported("datatype special field");
      } else if (!isLValue && member is SpecialField sf) {
        throw NotSupported("special field");
        /*
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        if (sf is ConstantField && !member.IsStatic && compiledName.Length != 0) {
          wr.Write(".{0}", compiledName);
        } else if (sf.SpecialId == SpecialField.ID.Keys || sf.SpecialId == SpecialField.ID.Values) {
          wr.Write(".{0}", compiledName);
        } else if (sf is DatatypeDestructor dtor2) {
          if (dtor2.EnclosingCtors.Count > 1) {
            NotSupported(String.Format("Using the same destructor {0} with multiple constructors is ambiguous", member.Name), dtor2.tok);
          }
          if (!(dtor2.EnclosingClass is IndDatatypeDecl)) {
            NotSupported(String.Format("Unexpected use of a destructor {0} that isn't for an inductive datatype.  Panic!", member.Name), dtor2.tok);
          }
          var dt = dtor2.EnclosingClass as IndDatatypeDecl;
          if (dt.Ctors.Count > 1) {
            wr.Write(".v_{0}.{1}", dtor2.EnclosingCtors[0].CompileName, sf.CompileName);
          } else {
            wr.Write(".{0}", sf.CompileName);
          }
        } else if (compiledName.Length != 0) {
          wr.Write("::{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
        }*/
      } else {
        wr.Write(".{0}", member.Name);
      }
      return wSource;
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      var w = wr.Fork();
      foreach (var index in indices) {
        wr.Write("[{0}]", index);
      }
      return w;
    }

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      foreach (var index in indices) {
        wr.Write("[");
        TrExpr(index, wr, inLetExprBody);
        wr.Write("]");
      }
      return w;
    }

    protected override string ArrayIndexToInt(string arrayIndex) {
      //return string.Format("new BigNumber({0})", arrayIndex);
      return arrayIndex;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(expr, wr, inLetExprBody);
      if (AsNativeType(expr.Type) == null) {
        wr.Write(".toNumber()");
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      if (source.Type.NormalizeExpand() is SeqType) {
        // seq
        wr.Write(".select(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(")");
      } else {
        // map or imap
        wr.Write("[");
        TrExpr(index, wr, inLetExprBody);
        wr.Write("]");
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr, bool nativeIndex = false) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".update(");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        string typeName = "";
        if (source.Type is UserDefinedType udt && udt.ResolvedClass != null &&
            udt.ResolvedClass is TypeSynonymDecl tsd) {
          // Hack to workaround type synonyms wrapped around the actual array type
          // TODO: Come up with a more systematic way of resolving this!
          typeName = TypeName(tsd.Rhs.TypeArgs[0], wr, source.tok, null, true);
        } else {
          typeName = TypeName(source.Type.TypeArgs[0], wr, source.tok, null, true);
        }
        wr.Write("DafnySequence<{0}>::SeqFromArray", typeName);
        //var arr = source.Type.AsArrayType;
        // wr.Write("DafnySequence<{0}>::SeqFromArray", TypeName(arr., wr, source.tok, null, true));
        //wr.Write("DafnySequence<{0}>::SeqFromArray", IdName(source.GetType().AsArrayType.TypeArgs[0]));
      }
      TrParenExpr(source, wr, inLetExprBody);

      if (hi != null) {
        TrParenExpr(".take", hi, wr, inLetExprBody);
      }
      if (lo != null) {
        TrParenExpr(".drop", lo, wr, inLetExprBody);
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr) {
      wr.Write("DafnySequence<{0}>::Create(", TypeName(expr.Type, wr, expr.tok, null, true));
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr("_dafny.MultiSet.FromArray", expr.E, wr, inLetExprBody);
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(function, wr, inLetExprBody);
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs, List<Type> boundTypes, Type resultType, Bpl.IToken tok, bool inLetExprBody, TargetWriter wr) {
      wr.Write("(({0}) => ", Util.Comma(boundVars));
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr) {
      wr.Write("is_{1}({0})", source, ctor.CompileName);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("({0})[{1}]", source, formalNonGhostIndex);
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        wr.Write("({0}){1}.v_{3}.{2}", source, ctor.EnclosingDatatype is CoDatatypeDecl ? "._D()" : "", dtorName, ctor.CompileName);
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      wr.Write("function (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1}", i == 0 ? "" : ", ", inNames[i]);
      }
      var w = wr.NewExprBlock(")");
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      throw NotSupported("CreateIIFE_ExprBody-A", sourceTok);
      /*var w = wr.NewExprBlock("function ({0})", bvName);
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;
      TrParenExpr(source, wr, inLetExprBody);
      return w;*/
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      throw NotSupported("CreateIIFE_ExprBody-B", sourceTok);
      /*var w = wr.NewExprBlock("function ({0})", bvName);
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;
      wr.Write("({0})", source);
      return w;*/
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      //throw NotSupported("CreateIIFE0", resultTok);
      var w = wr.NewBigExprBlock("[&] ", " ()");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      throw NotSupported("CreateIIFE1", resultTok);
      /*var w = wr.NewExprBlock("function ({0})", bvName);
      wr.Write("({0})", source);
      return w;*/
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            wr.Write("~ ");
            TrParenExpr(expr, wr, inLetExprBody);
          } else {
            TrParenExpr(expr, wr, inLetExprBody);
            wr.Write(".Not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr(expr, wr, inLetExprBody);
          wr.Write(".size()");
          break;
        case ResolvedUnaryOp.Dereference:
          TrParenExpr("*" ,expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.AddressOf:
          TrParenExpr("&" ,expr, wr, inLetExprBody);
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null;
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, Bpl.IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      TextWriter errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "=="; break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!"; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          if (AsNativeType(resultType) != null) {
            opString = "&";
          } else {
            callString = "And";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          if (AsNativeType(resultType) != null) {
            opString = "|";
          } else {
            callString = "Or";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          if (AsNativeType(resultType) != null) {
            opString = "^";
          } else {
            callString = "Xor";
          }
          break;

        case BinaryExpr.ResolvedOpcode.EqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "==";
            } else if (e0.Type.IsRefType) {
              opString = "==";
            } else {
              //staticCallString = "==";
              opString = "==";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
              postOpString = "/* handle */";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "!=";
            } else if (e0.Type.IsRefType) {
              opString = "!=";
            } else {
              opString = "!=";
              //preOpString = "!";
              //staticCallString = "_dafny.AreEqual";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">=";
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">";
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "<<";
          } else {
            if (AsNativeType(e1.Type) != null) {
              callString = "Lsh(_dafny.IntOfUint64(uint64";
              postOpString = "))";
            } else {
              callString = "Lsh";
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (AsNativeType(resultType) != null) {
            opString = ">>";
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            if (AsNativeType(e1.Type) != null) {
              callString = "Rsh(_dafny.IntOfUint64(uint64";
              postOpString = "))";
            } else {
              callString = "Rsh";
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null || resultType is PointerType) {
            opString = "+";
          } else {
            callString = "Plus";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null) {
            opString = "-";
          } else {
            callString = "Minus";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "*";
          } else {
            callString = "Times";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              //staticCallString =  "_dafny.Div" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
              //TODO(xueyuanz): using native division for all types
              opString = "/";
            } else {
              // Native division is fine for unsigned
              opString = "/";
            }
          } else {
            callString = "DivBy";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              //staticCallString = "_dafny.Mod" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
              //TODO(xueyuanz): using native mod for all types
              opString = "%";
            } else {
              // Native division is fine for unsigned
              opString = "%";
            }
          } else {
            callString = "Modulo";
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
          callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          preOpString = "!"; callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "IsProperSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "IsSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          callString = "IsSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          callString = "IsProperSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
        case BinaryExpr.ResolvedOpcode.MapDisjoint:
          callString = "IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersection"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "concatenate"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
      }
    }

    protected override void EmitIsZero(string varName, TargetWriter wr) {
      wr.Write("{0}.Cmp(_dafny.Zero) == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("_dafny.RealOfFrac(");
          TargetWriter w;
          if (AsNativeType(e.E.Type) is NativeType nt) {
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(nt)));
            w = wr.Fork();
            wr.Write(")");
          } else {
            w = wr;
          }
          TrParenExpr(e.E, w, inLetExprBody);
          wr.Write(", _dafny.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write("_dafny.Char(");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int32())");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            wr.Write(GetNativeTypeName(toNative));
            TrParenExpr(e.E, wr, inLetExprBody);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("_dafny.IntOfInt32(rune(");
              TrExpr(e.E, wr, inLetExprBody);
              wr.Write("))");
            } else {
              // char -> native
              wr.Write(GetNativeTypeName(toNative));
              TrParenExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            TrExpr(e.E, wr, inLetExprBody);
          } else if (fromNative != null) {
            Contract.Assert(toNative == null); // follows from other checks

            // native (int or bv) -> big-integer (int or bv)
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(fromNative)));
            TrExpr(e.E, wr, inLetExprBody);
            wr.Write(')');
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("{0}({1})", GetNativeTypeName(toNative), literal);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(u.E, wr, inLetExprBody);
              wr.Write(".CardinalityInt())");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(m.Obj, wr, inLetExprBody);
              wr.Write(".LenInt(0))");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody);
              wr.Write(".{0}()", Capitalize(GetNativeTypeName(toNative)));
            }

          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int()");
          if (AsNativeType(e.ToType) is NativeType nt) {
            wr.Write(".{0}()", Capitalize(GetNativeTypeName(nt)));
          }
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
        // identity will do
        TrExpr(e.E, wr, inLetExprBody);
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr)
    {
      throw NotSupported("Collection");
      /*if (ct is SetType) {
        wr.Write("DafnySet<{0}>::Create({{", TypeName(ct.TypeArgs[0], wr, tok, null, false));
        for (var i = 0; i < elements.Count; i++) {
          TrExpr(elements[i], wr, inLetExprBody);
          if (i < elements.Count - 1)  {
            wr.Write(",");
          }
        }
        wr.Write("})");
      } else if (ct is MultiSetType) {
        throw NotSupported("EmitCollectionDisplay/multiset", tok);
        wr.Write("_dafny.MultiSet.fromElements");
        TrExprList(elements, wr, inLetExprBody);
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        TargetWriter wrElements;
        if (ct.Arg.IsCharType) {
          throw NotSupported("EmitCollectionDisplay/string", tok);
          // We're really constructing a string.
          // TODO: It may be that ct.Arg is a type parameter that may stand for char. We currently don't catch that case here.
          wr.Write("[");
          wrElements = wr.Fork();
          wr.Write("].join(\"\")");
        } else
        {
          wr.Write("DafnySequence<{0}>::Create({{", TypeName(ct.TypeArgs[0], wr, tok, null, false));
          for (var i = 0; i < elements.Count; i++) {
            TrExpr(elements[i], wr, inLetExprBody);
            if (i < elements.Count - 1)  {
              wr.Write(",");
            }
          }
          wr.Write("})");
        }



        string sep = "";
        foreach (var e in elements) {
          wrElements.Write(sep);
          TrExpr(e, wrElements, inLetExprBody);
          sep = ", ";
        }
      }*/
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("DafnyMap<{0},{1}>::Create({{",
               TypeName(mt.TypeArgs[0], wr, tok, null, false),
               TypeName(mt.TypeArgs[1], wr, tok, null, false));
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("{");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(",");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write("}");
        sep = ", ";
      }
      wr.Write("})");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {

      if (ct is SetType) {
        wr.Write("DafnySet<{0}>()", TypeName(ct.TypeArgs[0], wr, tok, null, false));
      } else {
        throw NotSupported("EmitCollectionBuilder_New/non_set", tok);
      }

      /*
      else if (ct is MultiSetType) {
        wr.Write("new _dafny.MultiSet()");
      } else if (ct is MapType) {
        wr.Write("new _dafny.Map()");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
      */
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      if (ct is MultiSetType) {
        throw NotSupported("EmitCollectionBuilder_Add/MultiSetType");
      }
      wr.Write("{0}.set.emplace(", collName);
      TrExpr(elmt, wr, inLetExprBody);
      wr.WriteLine(");");
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr) {
      throw NotSupported("EmitMapBuilder_Add", tok);
      /*wr.Write("{0}.push([", collName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine("]);");
      return termLeftWriter;*/
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      // collections are built in place
      return collName;
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody);
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      throw NotSupported("Compilation of C++ files is not yet supported");
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {
        throw NotSupported("Running C++ programs is not yet supported");
    }
  }


}
