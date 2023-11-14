using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Starmada
{
    /*
     * For now, using Token class from Scanner.frame
    public class Token {
        public int kind;
        public string str;

        public string filename;
        public int startLine;
        public int startCh;
        public int endLine;
        public int endCh;
    }
    */

    // All AST node classes should be subclasses of this.
    // Can put helper functions (e.g. ToString) in this for convenience.
    //
    // Might decide to get rid of this entirely later.
    public abstract class AstNode
    {
        public Token FirstTok;
        public Token LastTok;
        public Scope Sc;
        public string PC;
        public string NextPC;
        // labelOn stands for label_enable
        public abstract string ToString(int indentation, bool labelOn);
        public abstract string ToCProgram(int indentation);
        public abstract string ToFStarLang(int indentation);

        /// <summary>This function looks at the children nodes of this AST node
        // and try to type resolve this AST node (Bottom-up resolution).</summary>
        /// <param name="currentScope">includes all variables defined until now.</param>
        /// <param name="enforcingType">In case of top-down resolution,
        // this parameters indicates the enforcing type.</param>
        public abstract void TypeResolve(Type enforcingType, ref Errors errors);

        /// <summary>This function sets the program counter of each AST Node
        // based on its definition and its parent PC.</summary>
        /// <param name="parentPC">The program counter of the parent.</param>
        /// <param name="index">The index of this AST node in parent.</param>
        public abstract void SetProgramCounter(string parentPC, int index);
        /// <summary>This function sets the program counter of the statement after this
        // statement.</summary>
        /// <param name="nextPC">The next program counter of this statement.</param>
        public abstract void SetNextProgramCounter(string nextPC);
        /// <summary>This function returns all the child AstNode of this AstNode.</summary>
        public abstract IEnumerable<AstNode> AllChildren();
        // FIXME: add clone()?

        public AstNode(Token firstTok)
        {
            this.FirstTok = firstTok;
        }
    }

    // A complete Starmada program, with all the levels and proof steps.
    public class StarmadaProgram : AstNode
    {
        public List<string> Includes;
        public string Name;
        public List<StructDecl> StructDecls;
        public List<DatatypeDecl> DatatypeDecls;
        public List<LevelDecl> Levels;
        public List<ProofDecl> Proofs;
        public Errors errors;
        public ErrorReporter reporter;

        public StarmadaProgram(Token tok, string name, Errors errors, ErrorReporter reporter) : base(tok)
        {
            this.Name = name;
            this.errors = errors;
            this.reporter = reporter;
            Includes = new List<string>();
            StructDecls = new List<StructDecl>();
            DatatypeDecls = new List<DatatypeDecl>();
            Levels = new List<LevelDecl>();
            Proofs = new List<ProofDecl>();
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + this.Name + "\n";
            foreach (var inc in this.Includes)
            {
                str = str + indentationStr + $"include {inc}\n";
            }
            foreach (var structDecl in this.StructDecls)
            {
                str = str + structDecl.ToString(indentation, labelOn) + "\n";
            }
            foreach (var dataTypeDecl in this.DatatypeDecls)
            {
                str = str + dataTypeDecl.ToString(indentation, labelOn) + "\n";
            }
            foreach (var level in this.Levels)
            {
                str = str + level.ToString(indentation, labelOn) + "\n";
            }
            foreach (var proof in this.Proofs)
            {
                str = str + proof.ToString(indentation, labelOn) + "\n";
            }
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);

            // TODO: Make a single runtime header which includes all necessary files + definitions
            str = str + "#include <stdint.h>\n";
            str = str + "#include <pthread.h>\n";
            str = str + "#include <assert.h>\n";
            str = str + "#include <stdio.h>\n";
            str = str + "#include <stdlib.h>\n";
            str = str + "#include <stdatomic.h>\n";

            foreach (var structDecl in this.StructDecls)
            {
                str = str + structDecl.ToCProgram(indentation) + "\n";
            }
            foreach (var dataTypeDecl in this.DatatypeDecls)
            {
                str = str + dataTypeDecl.ToCProgram(indentation) + "\n";
            }
            foreach (var level in this.Levels)
            {
                str = str + level.ToCProgram(indentation) + "\n";
            }

            // Add main method
            str = str + "int main() {\n";
            str = str + "  _main();\n";
            str = str + "  pthread_exit(NULL);\n}\n";
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            var moduleName = Path.GetFileNameWithoutExtension(this.Name);
            moduleName = char.ToUpper(moduleName[0]) + moduleName.Substring(1);
            str += Printer.GetFStarHeaderForModule(moduleName) + '\n';
            str += "let finite_map_insert (#a: eqtype) (#b: Type u#b) (m: FStar.FiniteMap.Base.map a b) (k: a) (v: b) = ComputationProduces (FStar.FiniteMap.Base.insert #a #b k v m)\n";
            str += "let map_insert #key #value m k v = ComputationProduces (FStar.Map.upd #key #value m k v)\n";
            str += "let set_singleton #a x = ComputationProduces (FStar.Set.singleton #a x)\n";
            str += "let set_union #a s1 s2 = ComputationProduces (FStar.Set.union #a s1 s2)\n";
            str += "let finite_set_insert (#a: eqtype) (x: a) (s: FStar.FiniteSet.Base.set a) = ComputationProduces (FStar.FiniteSet.Base.insert #a x s)\n";
            str += "let seq_build (#ty: Type) (s: seq ty) (v: ty) = ComputationProduces (build #ty s v)\n";
            str += "let seq_index (#ty: Type) (s: seq ty) (i: nat): conditional_computation_t ty = if i < length s then ComputationProduces (index #ty s i) else ComputationUndefined\n";
            str += "let seq_range (#ty: Type) (s: seq ty) (startIndex: nat) (endIndex: nat): conditional_computation_t (seq ty) = if startIndex <= endIndex && endIndex <= length s then ComputationProduces (drop #ty (take #ty s endIndex) startIndex) else ComputationUndefined\n";
            str += "let map_select #key #value m k = ComputationProduces (FStar.Map.sel #key #value m k)\n";
            str += "let finite_map_select (#a: eqtype) (#b: Type u#b) (m: FStar.FiniteMap.Base.map a b) (k: a) = match (FStar.FiniteMap.Base.elements m) k with | None -> ComputationUndefined | Some v -> ComputationProduces v\n";
            str += "let seq_update (#ty: Type) (s: seq ty) (i: nat) (v: ty): conditional_computation_t (seq ty) = if i < length s then ComputationProduces (update #ty s i v) else ComputationUndefined\n";
            str += "let map_update #key #value m k v = ComputationProduces (FStar.Map.upd #key #value m k v)\n";
            str += "let finite_map_update (#a: eqtype) (#b: Type u#b) (m: FStar.FiniteMap.Base.map a b) (k: a) (v: b) = ComputationProduces (FStar.FiniteMap.Base.insert #a #b k v m)\n";
            str += "let seq_contains (#ty: Type) (v: ty) (s: seq ty) = ComputationProduces (u2b (contains #ty s v))\n";
            str += "let set_contains #a x s = ComputationProduces (FStar.Set.mem #a x s)\n";
            str += "let finite_set_contains (#a: eqtype) (x: a) (s: FStar.FiniteSet.Base.set a) = ComputationProduces (FStar.FiniteSet.Base.mem #a x s)\n";
            str += "let map_contains #key #value k m = ComputationProduces (FStar.Map.contains #key #value m k)\n";
            str += "let finite_map_contains #key #value k m = ComputationProduces (FStar.FiniteMap.Base.mem #key #value k m)\n";
            str += "let not_seq_contains (#ty: Type) (v: ty) (s: seq ty) = ComputationProduces (not (u2b (contains #ty s v)))\n";
            str += "let not_set_contains #a x s = ComputationProduces (not (FStar.Set.mem #a x s))\n";
            str += "let not_finite_set_contains (#a: eqtype) (x: a) (s: FStar.FiniteSet.Base.set a) = ComputationProduces (not (FStar.FiniteSet.Base.mem #a x s))\n";
            str += "let not_map_contains #key #value k m = ComputationProduces (not (FStar.Map.contains #key #value m k))\n";
            str += "let not_finite_map_contains #key #value k m = ComputationProduces (not (FStar.FiniteMap.Base.mem #key #value k m))\n";
            str += "let set_disjoint (#a:eqtype) (s1: FStar.Set.set a) (s2: FStar.Set.set a) = ComputationProduces (u2b (FStar.Set.disjoint #a s1 s2))\n";
            str += "let finiteset_disjoint (#a: eqtype) (s1: FStar.FiniteSet.Base.set a) (s2: FStar.FiniteSet.Base.set a) = ComputationProduces (u2b (FStar.FiniteSet.Base.disjoint #a s1 s2))\n";
            str += "let seq_cardinality (#ty: Type) (s: seq ty) = ComputationProduces (length s)\n";
            str += "let finiteset_cardinality (#a: eqtype) (s: FStar.FiniteSet.Base.set a) = ComputationProduces (FStar.FiniteSet.Base.cardinality #a s)\n";
            str += "let finitemap_cardinality #key #value  m = ComputationProduces (FStar.FiniteMap.Base.cardinality #key #value m)\n";
            str += "\n";

            foreach (var structDecl in this.StructDecls)
            {
                str += structDecl.ToFStarLang(indentation) + "\n";
            }
            foreach (var dataTypeDecl in this.DatatypeDecls)
            {
                str += dataTypeDecl.ToFStarLang(indentation) + "\n";
            }
            foreach (var dataTypeDecl in this.DatatypeDecls)
            {
                str += indentationStr + dataTypeDecl.GenerateFstarFunctions() + "\n";
            }
            foreach (var level in Levels) {
                foreach (var node in level.AllChildren()) {
                    if (node is MethodDecl) {
                        var methodDecl = node as MethodDecl;
                        str += methodDecl.GetStackInitializer(indentation) + "\n";
                    }
                }
            }
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            var structDatatypeNamesToTokenDict = new Dictionary<string, Token>();
            foreach (var structDecl in this.StructDecls) {
                var structName = structDecl.Name.Name.ToLower();
                if (structDatatypeNamesToTokenDict.ContainsKey(structName)) {
                    errors.SemErr(structDecl.FirstTok, $"{structName} is already defined at line {structDatatypeNamesToTokenDict[structName].line}:{structDatatypeNamesToTokenDict[structName].col} (uppercase neglected)!");
                }
                structDatatypeNamesToTokenDict[structName] = structDecl.Name.FirstTok;
            }
            foreach (var datatypeDecl in this.DatatypeDecls) {
                var datatypeName = datatypeDecl.Ty.Name.Name.ToLower();
                if (structDatatypeNamesToTokenDict.ContainsKey(datatypeName)) {
                    errors.SemErr(datatypeDecl.FirstTok, $"{datatypeName} is already defined at line {structDatatypeNamesToTokenDict[datatypeName].line}:{structDatatypeNamesToTokenDict[datatypeName].col} (uppercase neglected)!");
                }
                structDatatypeNamesToTokenDict[datatypeName] = datatypeDecl.FirstTok;
            }
            
            // Add all defined structs and datatypes to the current scope
            foreach (var structDecl in this.StructDecls)
            {
                Sc.Push(structDecl);
            }
            foreach (var datatypeDecl in this.DatatypeDecls)
            {
                Sc.Push(datatypeDecl);
            }

            foreach (var structDecl in this.StructDecls)
            {
                structDecl.Sc = new Scope(Sc);
                structDecl.Sc.EnclosingNode = structDecl;
                structDecl.TypeResolve(null, ref errors);
            }
            foreach (var datatypeDecl in this.DatatypeDecls)
            {
                datatypeDecl.Sc = Sc;
                datatypeDecl.TypeResolve(null, ref errors);
            }
            foreach (var levelDecl in this.Levels)
            {
                levelDecl.Sc = new Scope(Sc);
                levelDecl.Sc.EnclosingNode = levelDecl;
                levelDecl.TypeResolve(null, ref errors);
            }
            foreach (var proofDecl in this.Proofs)
            {
                proofDecl.Sc = new Scope(Sc);
                proofDecl.Sc.EnclosingNode = proofDecl;
                proofDecl.TypeResolve(null, ref errors);
            }
            // TODO: Implement this function
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            foreach (var levelDecl in this.Levels)
            {
                levelDecl.SetProgramCounter("", 0);
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var structDecl in StructDecls)
            {
                foreach (var node in structDecl.AllChildren())
                    yield return node;
                yield return structDecl;
            }
            foreach (var datatypeDecl in DatatypeDecls)
            {
                foreach (var node in datatypeDecl.AllChildren())
                    yield return node;
                yield return datatypeDecl;
            }
            foreach (var level in Levels)
            {
                foreach (var node in level.AllChildren())
                    yield return node;
                yield return level;
            }
            foreach (var proof in Proofs)
            {
                foreach (var node in proof.AllChildren())
                    yield return node;
                yield return proof;
            }
        }
    }

    public class StructDecl : AstNode
    {
        public Ident Name;
        public List<VarDecl> Decls; // must have at least one entry
        public StructDecl(Token tok, Ident name) : base(tok)
        {
            this.Name = name;
            this.Decls = new List<VarDecl>();
        }
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "struct " + this.Name.ToString(0, labelOn) + " {\n";
            foreach (var decl in this.Decls)
            {
                str = str + decl.ToString(indentation + 2, labelOn) + "\n";
            }
            str = str + indentationStr + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var decl in this.Decls)
            {
                decl.Sc = Sc;
                decl.TypeResolve(null, ref errors);
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotImplementedException();
        }
        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "struct " + this.Name.ToString(0, false) + " {\n";
            foreach (var decl in this.Decls)
            {
                str = str + decl.ToCProgram(indentation + 2) + "\n";
            }
            str = str + indentationStr + "};";
            return str;
        }
        public VarDecl GetField(string name)
        {
            foreach (var decl in this.Decls)
            {
                if (decl.Name.Name == name)
                {
                    return decl;
                }
            }
            return null;
        }
        public string GetFieldAccessInFStar(string fieldName, string firstOp)
        {
            int fieldId = -1;
            for (int i = 0; i < Decls.Count; i++)
            {
                if (Decls[i].Name.Name == fieldName) {
                    fieldId = i;
                    break;
                }
            }
            if (fieldId == -1) {
                throw new ArgumentException($"Field {fieldName} doesn't exist in {Name} struct declaration");
            }
            string str = $"(ExpressionFieldOf (_user_defined_struct__{this.Name.ToString(0, false).ToLower()}) ({firstOp}) {fieldId})";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "type _user_defined_struct__" + Name.ToString(0, false).ToLower() + " = (ObjectTDStruct (singleton \n";
            string sep = indentationStr + "  ";
            foreach (var field in this.Decls) {
                str += sep + "( " + field.Ty.ToFStarLang(0, true) + " )";
                sep = " $::\n" + indentationStr + "  ";
            }
            str += "\n" + indentationStr + "))";
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            foreach (var vardecl in Decls)
            {
                foreach (var node in vardecl.AllChildren())
                    yield return node;
                yield return vardecl;
            }
        }
    }

    public class DatatypeDecl : AstNode
    {
        public UserDefinedType Ty;
        public List<DatatypeMemberDecl> MemberDeclList = new List<DatatypeMemberDecl>();

        private Dictionary<string, int> GenericTypeDict = new Dictionary<string, int>(); // filled in during type resolution
        private Dictionary<string, int> MatchDict = new Dictionary<string, int>(); // filled in during type resolution

        class Fn
        {
            public Type astType; // return type
            public string ty; // function return type
            public string parameterTy; // function parameter type
            public List<DatatypeMemberDecl> members;
            public string name; // function name
            public string definition; // function definition
            public string invocation; // string format for function invocation
        }

        // For resolution of D.x, generating F* functions
        private Dictionary<string, Fn> name2fn = new Dictionary<string, Fn>();

        public DatatypeDecl(Token tok, UserDefinedType ty) : base(tok)
        {
            this.Ty = ty;
        }

        // FIXME: unsupported; seems not fully supported by grammar
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "datatype " + Ty.ToString(0) + " = ";
            var sep = "";
            foreach (var member in this.MemberDeclList)
            {
                str += sep + member.ToString(0, false);
                sep = " | ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (Ty.ArgumentList != null)
            {
                for (int i = 0; i < Ty.ArgumentList.Count; i++)
                {
                    var genericType = Ty.ArgumentList[i] as UserDefinedType;
                    if (genericType == null)
                    {
                        errors.SemErr(Ty.Name.FirstTok, "Invalid generic type list!");
                    }
                    GenericTypeDict.Add(genericType.Name.Name, i);
                }
            }
            foreach (var datatypeMemberDecl in MemberDeclList)
            {
                foreach (Parameter parameter in datatypeMemberDecl.Arguments)
                {
                    bool isDefinedType = Sc.IsDefinedType(parameter.Ty);
                    bool isGenericType = false;
                    if (!isDefinedType && Ty.ArgumentList != null && parameter.Ty is UserDefinedType)
                    {
                        var ut = parameter.Ty as UserDefinedType;
                        int index = -1;
                        isGenericType = GenericTypeDict.TryGetValue(ut.Name.Name, out index);
                        parameter.Ty = new GenericType(ut.Name.Name, index);
                    }
                    if (!isDefinedType && !isGenericType)
                    {
                        errors.SemErr(parameter.FirstTok, parameter.Ty.ToString(0) + "'s type is not defined.");
                    }
                    string name = parameter.Name.Name;
                    if (name2fn.ContainsKey(name))
                    {
                        if (name2fn[name].ty != parameter.Ty.ToString(0))
                        {
                            errors.SemErr(parameter.FirstTok, "Parameter with the same name must has the same type.");
                        }
                    }
                    else
                    {
                        name2fn[name] = new Fn();
                        name2fn[name].astType = parameter.Ty;
                        name2fn[name].ty = parameter.Ty.ToString(0);
                        name2fn[name].members = new List<DatatypeMemberDecl>();
                    }
                    name2fn[name].members.Add(datatypeMemberDecl);
                }
                var datatypeMember = Sc.GetDatatypeMemberDecl(datatypeMemberDecl.Name.Name);
                if (datatypeMember != null)
                {
                    errors.SemErr(FirstTok, $"{Ty.Name.ToString(0, false).ToLower()} is already defined at line {datatypeMember.FirstTok.line}:{datatypeMember.FirstTok.col}!");
                }
                Sc.Push(datatypeMemberDecl);
            }
            // Prepare for generating fstar functions
            foreach (KeyValuePair<string, Fn> entry in name2fn)
            {
                string indentation = new string(' ', 4);
                string name = entry.Key;
                Fn fn = entry.Value;
                string baseName = Ty.Name.Name.ToLower();
                fn.name = $"_{baseName}_{name}";
                List<string> typesStr = fn.members.ConvertAll(member => $"{member.Name.Name}?gt");
                fn.parameterTy = $"gt: {baseName}{{{String.Join(" \\/ ", typesStr)}}}";
                string body = $"let {fn.name} (base: ({fn.parameterTy})): conditional_computation_t {fn.ty} = ";
                if (fn.members.Count == 1)
                {
                    DatatypeMemberDecl member = fn.members[0];
                    body += $"ComputationProduces ({member.Name.Name}?.{name} base)\n";
                }
                else
                {
                    body += '\n' + "ComputationProduces (\n";
                    body += indentation + $"match base with\n";
                    foreach (DatatypeMemberDecl member in fn.members)
                    {
                        body += indentation + $"| {member.Name.Name} {String.Join(' ', member.Arguments.ConvertAll(arg => arg.Name.Name))} -> {name}\n";
                    }
                    body += ")\n";
                }
                fn.definition = body;
                fn.invocation = $"ExpressionApplyFunction ({fn.astType.ToFStarLang(0, true)}) [!!] {fn.ty} [{fn.parameterTy}] {fn.name}";
            }
            // Set the match list
            for (int i = 0; i < MemberDeclList.Count; i++)
            {
                MatchDict.Add(MemberDeclList[i].Name.Name, i);
            }
            Sc.Push(this);
        }
        public int GetMemberDeclIndex(string name)
        {
            int index = -1;
            MatchDict.TryGetValue(name, out index);
            return index;
        }
        public List<DatatypeMemberDecl> GetDefinedMemberList(List<Type> definedTypes)
        {
            if (Ty.ArgumentList == null || Ty.ArgumentList.Count == 0)
            {
                return MemberDeclList;
            }
            var definedMemberList = new List<DatatypeMemberDecl>();
            foreach (var datatypeMemberDecl in MemberDeclList)
            {
                var newParameters = new List<Parameter>();
                foreach (var parameter in datatypeMemberDecl.Arguments)
                {
                    if (parameter.Ty is GenericType)
                    {
                        newParameters.Add(new Parameter(parameter.FirstTok, parameter.Name, definedTypes[(parameter.Ty as GenericType).Index]));
                    }
                    else
                    {
                        newParameters.Add(parameter);
                    }
                }
                definedMemberList.Add(new DatatypeMemberDecl(datatypeMemberDecl.Name, newParameters));
            }
            return definedMemberList;
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            return;
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            return;
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotImplementedException();
        }

        public string GenerateFstarFunctions()
        {
            List<string> fnStr = new List<string>();
            foreach (Fn fn in name2fn.Values)
            {
                fnStr.Add(fn.definition);
            }
            return String.Join('\n', fnStr);
        }

        public string GetFunctionInvocation(string name, string fstarExpr)
        {
            if (!name2fn.ContainsKey(name))
            {
                return null;
            }
            string[] s = name2fn[name].invocation.Split("!!");
            return s[0] + fstarExpr + s[1];
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "type " + Ty.ToFStarLang(0, false) + " = \n";
            foreach (var member in MemberDeclList)
            {
                str += member.ToFStarLang(indentation + 4) + Ty.ToFStarLang(0, false) + "\n";
            }
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var member in MemberDeclList)
            {
                foreach (var node in member.AllChildren())
                    yield return node;
                yield return member;
            }
        }
    }

    public class DatatypeMemberDecl : AstNode
    {
        public Ident Name;
        public List<Parameter> Arguments;
        public DatatypeDecl parent;
        public DatatypeMemberDecl(Ident name, List<Parameter> args) : base(name.FirstTok)
        {
            this.Name = name;
            this.Arguments = args;
        }
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Name.ToString(0, false);
            if (Arguments != null && Arguments.Count > 0)
            {
                str = str + "(";
                var sep = "";
                foreach (Parameter p in Arguments)
                {
                    str += sep + p.ToString(0, false);
                    sep = ", ";
                }
                str += ")";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            throw new NotImplementedException();
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotImplementedException();
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "| " + Name.ToString(0, false) + ": ";
            foreach (Parameter arg in Arguments)
            {
                str += $"({arg.ToFStarLang(0)})";
                str += " -> ";
            }
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            foreach (Parameter arg in Arguments)
            {
                foreach (var node in arg.AllChildren())
                    yield return node;
                yield return arg;
            }
        }
    }

    public class LevelDecl : AstNode
    {
        public Ident Name;
        public List<VarDecl> Globals;
        public List<MemberDecl> Members;
        public List<InvariantDecl> Invariants;
        public Ident SharedStructName;
        private int FunctionCount = 0;
        // FIXME: want to use option type, perhaps impl ourselves
        // TODO: ref to shared structs

        public string MainStartPC = "main.1";

        public LevelDecl(Token tok, Ident name) : base(tok)
        {
            this.Name = name;
            Globals = new List<VarDecl>();
            Members = new List<MemberDecl>();
            Invariants = new List<InvariantDecl>();
        }
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "level " + Name.ToString(0, labelOn) + " {\n";
            foreach (var decl in Globals)
            {
                str = str + decl.ToString(indentation + 2, labelOn) + "\n";
            }
            foreach (var member in Members)
            {
                str = str + member.ToString(indentation + 2, labelOn) + "\n";
            }
            foreach (var inv in Invariants)
            {
                str = str + inv.ToString(indentation + 2, labelOn) + "\n";
            }
            str = str + indentationStr + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function, now it is just for test
            foreach (var global in Globals)
            {
                global.Sc = Sc;
                global.TypeResolve(null, ref errors);
            }
            foreach (var member in Members)
            {
                Sc.Push(member);
            }
            foreach (var inv in Invariants)
            {
                Sc.Push(inv);
            }
            foreach (var member in Members)
            {
                member.Sc = new Scope(Sc);
                member.Sc.EnclosingNode = member;
                if (member is MethodDecl methodDecl) {
                    methodDecl.EnclosingLevel = this;
                }
                foreach (var node in member.AllChildren())
                {
                    if (node is not Statement)
                    {
                        continue;
                    }
                    Statement stmt = node as Statement;
                    if (stmt.PC != null)
                    {
                        member.Sc.PC2Stmt[stmt.PC] = stmt;
                    }
                }
                member.TypeResolve(null, ref errors);
            }
            foreach (var inv in Invariants)
            {
                inv.Sc = new Scope(Sc);
                inv.Sc.EnclosingNode = inv;
                inv.TypeResolve(null, ref errors);
            }
            // TODO: deal with SharedStructName
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            foreach (var member in Members)
            {
                member.SetProgramCounter("", 0);
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotSupportedException();
        }
        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            foreach (var decl in Globals)
            {
                str = str + decl.ToCProgram(indentation) + "\n";
            }
            foreach (var member in Members)
            {
                str = str + member.ToCProgram(indentation) + "\n";
            }
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            foreach (var node in AllChildren())
            {
                if (node is MatchExpr)
                {
                    MatchExpr matchExpr = node as MatchExpr;
                    str += matchExpr.ToFStarFunction(indentation, $"func_{FunctionCount}") + '\n';
                    FunctionCount++;
                }
                if (node is QuantifierExpr)
                {
                    QuantifierExpr quantifierExpr = node as QuantifierExpr;
                    str += quantifierExpr.ToFStarFunction(indentation, $"func_{FunctionCount}") + '\n';
                    FunctionCount++;
                }
                if (node is ComprehensionExpr)
                {
                    ComprehensionExpr comprehensionExpr = node as ComprehensionExpr;
                    str += comprehensionExpr.ToFStarMapFunction(indentation, $"func_{FunctionCount}") + '\n';
                    FunctionCount++;
                }
            }
            str += indentationStr + $"let global_initializers: list initializer_t =\n";
            str += indentationStr + "  [\n";
            var sep = "";
            foreach (var global in Globals)
            {
                if (global.Ty is TypeSuffix)
                {
                    string arrayName = global.Name.ToString(0, false);
                    if (global.Value != null && global.Value is SeqDisplayExpr)
                    {
                        SeqDisplayExpr seqInit = global.Value as SeqDisplayExpr;
                        str += sep + new string(' ', indentation + 4) + $"{{ var_id = \"_{arrayName}_array\"; iv = InitializerSpecific ({seqInit.ToFStarObjectValue()}); weakly_consistent = false; }}";
                        global.Value = new ArrayPointer(global.FirstTok, arrayName);
                    }
                    else if (global.Value == null)
                    {
                        str += sep + new string(' ', indentation + 4) + $"{{ var_id = \"_{arrayName}_array\"; iv = InitializerArbitrary ({(global.Ty as TypeSuffix).ToArrayFStarLang()}); weakly_consistent = false; }}";
                        global.Value = new ArrayPointer(global.FirstTok, arrayName);
                    }
                    else
                    {
                        throw new NotSupportedException();
                    }
                    sep = " ;\n";
                }
                str += sep + global.ToFStarLang(indentation + 4);
                sep = " ;\n";
            }
            str += indentationStr + "\n  ]\n";
            foreach (var member in Members)
            {
                str = str + member.ToFStarLang(indentation) + "\n";
            }
            str += indentationStr + "let propagate_statement = { start_pc = None; end_pc = None; starts_atomic_block = true; ends_atomic_block = true; statement = PropagateWriteMessageStatement }\n";
            str += indentationStr + $"let program_statements = \n  [\n";
            sep = "";
            foreach (var member in Members)
            {
                if (member is MethodDecl method) {
                    if (method.Name.Name == "main")
                    {
                        if (method.FStarStmts.Count == 0)
                        {
                            throw new Exception("no actual statements in main function");
                        }
                        MainStartPC = method.FStarStmts[0].StartPC;
                    }
                }
                str += sep + indentationStr + "    " + member.Name.ToString(0, false).ToLower() + "_func_statements";
                sep = ";\n";
            }
            str += "\n  ]\n";
            str += indentationStr + "let prog: Armada.Program.t = {\n";
            str += indentationStr + "  main_method_id = \"main\";\n";
            str += indentationStr + $"  main_start_pc = \"{MainStartPC}\";\n";
            str += indentationStr + "  global_initializers = global_initializers;\n";
            str += indentationStr + $"  main_stack_initializers = level_{Name.Name}_main_stack_initializers;\n";
            str += indentationStr + "  program_statements = propagate_statement :: flatten program_statements;\n";
            str += indentationStr + "}\n";
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            foreach (var global in Globals)
            {
                foreach (var node in global.AllChildren())
                    yield return node;
                yield return global;
            }
            foreach (var member in Members)
            {
                foreach (var node in member.AllChildren())
                    yield return node;
                yield return member;
            }
            foreach (var inv in Invariants)
            {
                foreach (var node in inv.AllChildren())
                    yield return node;
                yield return inv;
            }
        }
    }

    public abstract class MemberDecl : AstNode
    {
        public Ident Name;
        public MemberDecl(Token tok) : base(tok) { }
    }

    public class MethodDecl : MemberDecl
    {
        public List<Parameter> Args;
        public List<MethodSpec> Specs;
        public Parameter Ret;
        // FIXME: impl method spec
        public List<VarDecl> VarDeclList; // filled in during type resolution
        public List<Statement> Stmts;
        // For each caller, there would be an element in this list.
        public List<FunctionCallStatement> CallerStmtList;
        private bool IsCalledWithThread = false;
        private bool IsExternal = false;
        public bool IsAtomic = false;
        public List<Attribute> Attrs;
        public LevelDecl EnclosingLevel = null;

        public List<FStarStmt> FStarStmts;

        public MethodDecl(Token tok) : base(tok)
        {
            Args = new List<Parameter>();
            Specs = new List<MethodSpec>();
            VarDeclList = new List<VarDecl>();
            Stmts = new List<Statement>();
            CallerStmtList = new List<FunctionCallStatement>();
            Attrs = new List<Attribute>();
            FStarStmts = new();
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "method ";
            foreach (var attr in Attrs)
            {
                str += $"{{:{attr.Name.Name}}} ";
            }
            str += Name.ToString(0, labelOn) + " (";
            for (int i = 0; i < Args.Count; i++)
            {
                str = str + Args[i].ToString(0, labelOn);
                if (i != Args.Count - 1)
                {
                    str = str + ", ";
                }
            }
            str = str + ")";
            if (Ret != null)
            {
                str = str + " returns (" + Ret.ToString(0, labelOn) + ")";
            }
            foreach (var spec in Specs)
            {
                str += "\n" + spec.ToString(indentation + 2, labelOn);
            }
            str = str + "\n" + indentationStr + "{\n";
            foreach (var stmt in VarDeclList)
            {
                str = str + stmt.ToString(indentation + 2, labelOn) + "\n";
            }
            foreach (var stmt in Stmts)
            {
                str = str + stmt.ToString(indentation + 2, labelOn) + "\n";
            }
            str = str + indentationStr + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function, now it is just for test
            foreach (var attr in Attrs)
            {
                if (attr.Name.Name == "extern")
                {
                    IsExternal = true;
                }
                else if (attr.Name.Name == "atomic_method")
                {
                    IsAtomic = true;
                }
            }
            foreach (var arg in Args)
            {
                arg.Sc = Sc;
                arg.TypeResolve(null, ref errors);
                Sc.Push(arg);
            }
            if (Ret != null)
            {
                Ret.Sc = Sc;
                Ret.TypeResolve(null, ref errors);
                Sc.Push(Ret);
            }
            foreach (var spec in Specs)
            {
                spec.Sc = Sc;
                spec.TypeResolve(null, ref errors);
            }
            if (IsAtomic)
            {
                foreach (var stmt in Stmts)
                {
                    stmt.InAtomicBlock = true;
                    stmt.StartsAtomicBlock = false;
                    stmt.EndsAtomicBlock = false;
                }
            }
            // Add label statement to scope
            foreach (Statement stmt in Stmts)
            {
                if (stmt.Label != null)
                {
                    Sc.Push(stmt);
                }
            }
            foreach (Statement stmt in Stmts)
            {
                stmt.Sc = Sc;
                stmt.TypeResolve(enforcingType, ref errors);
            }

            // Seperate VarDecls and other statements
            bool endVarDecl = false;
            foreach (Statement stmt in Stmts)
            {
                if (stmt is VarDecl)
                {
                    if (endVarDecl)
                    {
                        errors.SemErr(stmt.FirstTok, "Variable declaration should be at the top of the method declaration!");
                    }
                    VarDeclList.Add(stmt as VarDecl);
                }
                else
                {
                    endVarDecl = true;
                }
            }
            Stmts.RemoveRange(0, VarDeclList.Count);

            List<Statement> generatedAssigns = new List<Statement>();
            string prefix = Name.ToString(0, false).ToLower();
            int count = 1;
            foreach (VarDecl vardecl in VarDeclList)
            {
                if (vardecl.Value != null && vardecl.Value is not FStarExpressionConstant)
                {
                    var assignStatement = new AssignStatement(vardecl.FirstTok, vardecl.Name, vardecl.Value, false);
                    assignStatement.PC = $"{prefix}.{count}";
                    count += 1;
                    assignStatement.NextPC = $"{prefix}.{count}";
                    assignStatement.Sc = Sc;
                    assignStatement.TypeResolve(null, ref errors);
                    generatedAssigns.Add(assignStatement);
                    vardecl.Value = null;
                }
            }
            if (generatedAssigns.Count > 0)
            {
                if (Stmts.Count > 0)
                {
                    generatedAssigns[generatedAssigns.Count - 1].NextPC = Stmts[0].PC;
                }
                else
                {
                    generatedAssigns[generatedAssigns.Count - 1].NextPC = $"{prefix}.End";
                }
            }
            else if (Stmts.Count > 0)
            {
                Stmts[0].PC = $"{prefix}.1";
            }
            Stmts.InsertRange(0, generatedAssigns);
        }
        public void AddCaller(Expr destination, bool isSequential, string nextPC)
        {
            var funcCallStmt = new FunctionCallStatement(this, destination,
              Ret == null ? null : Ret.Name,
              isSequential, Name.ToString(0, false).ToLower() + ".End", nextPC);
            if (IsAtomic)
            {
                funcCallStmt.InAtomicBlock = true;
                funcCallStmt.StartsAtomicBlock = false;
                funcCallStmt.EndsAtomicBlock = false;
            }
            CallerStmtList.Add(funcCallStmt);
        }
        public void AddThreadCaller()
        {
            IsCalledWithThread = true;
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            for (int i = 0; i < Stmts.Count; i++)
            {
                Stmts[i].SetProgramCounter(Name.ToString(0, false).ToLower(), i + 1);
            }
            // TODO: implement SetNextProgramCounter
            if (Stmts.Count > 0)
            {
                for (int i = 0; i < Stmts.Count - 1; i++)
                {
                    Stmts[i].SetNextProgramCounter(Stmts[i + 1].PC);
                }
                Stmts[Stmts.Count - 1].SetNextProgramCounter(Name.ToString(0, false).ToLower() + ".End");
                this.PC = Stmts[0].PC;
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotSupportedException();
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr;

            if (Ret != null)
            {
                str = str + Ret.ToCProgram(0) + " ";
            }
            else
            {
                str = str + "void ";
            }

            if (Name.ToCProgram(0) == "main")
            {
                str = str + "_main" + "(";
            }
            else
            {
                str = str + Name.ToCProgram(0) + "(";
            }

            for (int i = 0; i < Args.Count; i++)
            {
                str = str + Args[i].ToCProgram(0);
                if (i != Args.Count - 1)
                {
                    str = str + ", ";
                }
            }
            str = str + ")";
            str = str + " {\n";
            foreach (var stmt in Stmts)
            {
                str = str + stmt.ToCProgram(indentation + 2) + "\n";
            }
            str = str + indentationStr + "}\n";

            // Create an arg struct and function wrapper for thread invocations of this method
            if (Name.ToCProgram(0) != "main")
            {
                if (Args.Count > 0)
                {
                    str = str + indentationStr + createArgStruct();
                }
                str = str + indentationStr + getThreadWrapper();
            }

            return str;
        }

        private string createArgStruct()
        {
            string structType = "struct _" + Name.ToCProgram(0) + "Args";
            string indentationStr = new string(' ', 2);
            string structStr = structType + "{\n";
            for (int i = 0; i < Args.Count; i++)
            {
                structStr = structStr + indentationStr + Args[i].ToCProgram(0) + ";\n";
            }
            structStr = structStr + "};\n";
            return structStr;
        }

        private string getThreadWrapper()
        {
            string structType = "struct _" + Name.ToCProgram(0) + "Args";
            string indentationStr = new string(' ', 2);

            string str = "void _" + Name.ToCProgram(0) + "Wrapper";

            if (Args.Count > 0)
            {
                str = str + "(void * args) {\n";
                str = str + indentationStr + structType + "* func_args = (" + structType + "*) args;\n";
            }
            else
            {
                str = str + "() {\n";
            }

            str = str + indentationStr + Name.ToCProgram(0) + "(";
            if (Args.Count > 0)
            {
                for (int i = 0; i < Args.Count; i++)
                {
                    str = str + "func_args->" + Args[i].Name.ToCProgram(0);
                    if (i != Args.Count - 1)
                    {
                        str = str + ", ";
                    }
                }
            }
            str = str + ");\n";
            if (Args.Count > 0)
            {
                str = str + indentationStr + "free(args);\n";
            }
            str = str + "}\n";
            return str;
        }

        public string GetStackInitializer(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            // define stack variables
            str += indentationStr + $"let level_{EnclosingLevel.Name.Name}_{Name.ToString(0, false).ToLower()}_stack_initializers: list initializer_t = \n  [";
            if (VarDeclList.Count == 0 && !IsExternal) {
                str += " ]\n";
                return str;
            }
            var sep = "\n";
            foreach (var vardecl in VarDeclList)
            {
                str += sep + vardecl.ToFStarLang(indentation + 4);
                sep = " ;\n";
            }
            if (IsExternal)
            {
                foreach (var spec in Specs)
                {
                    if (spec is MethodSpecReads)
                    {
                        var msr = spec as MethodSpecReads;
                        str += sep + msr.ToFStarLang(indentation + 4);
                        sep = " ;\n";
                    }
                }
            }
            str += indentationStr + "\n  ]\n";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);

            // define function statements
            str += indentationStr + $"let {Name.ToString(0, false).ToLower()}_func_statements = \n  [\n";
            var sep = "";
            if (IsExternal)
            {
                Expr awaitsSpec = null;
                Expr undefinedUnlessSpec = null;
                Expr ensuresSpec = null;
                List<Expr> modifiesSpec = new List<Expr>();
                List<Expr> readsSpec = new List<Expr>();
                List<Expr> logsSpec = new List<Expr>();
                foreach (var spec in Specs)
                {
                    if (spec is MethodSpecReads)
                    {
                        readsSpec.AddRange(spec.Elements);
                    }
                    else if (spec is MethodSpecAwaits)
                    {
                        awaitsSpec = awaitsSpec == null ? spec.overallExpr : new BinaryExpr(awaitsSpec.FirstTok, awaitsSpec, spec.overallExpr, Opcode.And);
                    }
                    else if (spec is MethodSpecUndefinedUnless)
                    {
                        undefinedUnlessSpec = undefinedUnlessSpec == null ? spec.overallExpr : new BinaryExpr(undefinedUnlessSpec.FirstTok, undefinedUnlessSpec, spec.overallExpr, Opcode.And);
                    }
                    else if (spec is MethodSpecModifies)
                    {
                        modifiesSpec.Add(spec.overallExpr);
                    }
                    else if (spec is MethodSpecEnsures)
                    {
                        ensuresSpec = ensuresSpec == null ? spec.overallExpr : new BinaryExpr(ensuresSpec.FirstTok, ensuresSpec, spec.overallExpr, Opcode.And);
                    }
                    else if (spec is MethodSpecLogs)
                    {
                        logsSpec.AddRange(spec.Elements);
                    }
                }
                string awaitsSpecStr = awaitsSpec != null ? awaitsSpec.ToFStarLang(0) : "ExpressionConstant (ObjectValueAbstract bool true)";
                string undefinedUnlessSpecStr = undefinedUnlessSpec != null ? undefinedUnlessSpec.ToFStarLang(0) : "ExpressionConstant (ObjectValueAbstract bool true)";
                string ensuresSpecStr = ensuresSpec != null ? ensuresSpec.ToFStarLang(0) : "ExpressionConstant (ObjectValueAbstract bool true)";
                string modifiesSpecStr = "[ " + string.Join("; ", modifiesSpec.Select(x => x.ToFStarLang(0)).ToArray()) + " ]";
                string readsSpecStr = "[ " + string.Join("; ", readsSpec.Select((x, index) => $"(\"_snapshot_var_{index}\", {x.ToFStarLang(0)})").ToArray()) + " ]";
                string logsSpecStr = "[ " + string.Join("; ", logsSpec.Select(x => $"({x.ToFStarLang(0)})").ToArray()) + " ]";
                // TODO set bypassing write buffer from attributes
                // TODO set read clauses
                str += sep + (new FStarStmt($"{Name.ToString(0, false)}.End", null, false, false,
                  $"ExternalMethodStartStatement\n{indentationStr}        " +
                  $"({awaitsSpecStr})\n{indentationStr}        " +
                  $"({undefinedUnlessSpecStr})\n{indentationStr}        " +
                  $"false\n{indentationStr}        " +
                  $"{modifiesSpecStr}\n{indentationStr}        " +
                  $"{readsSpecStr}")).GetFStarCodeOfStatement(indentation + 4);
                sep = ";\n";

                str += sep + (new FStarStmt($"{Name.ToString(0, false)}.End", null, false, false,
                  $"ExternalMethodMiddleStatement\n{indentationStr}        " +
                  $"false\n{indentationStr}        " +
                  $"{modifiesSpecStr}\n{indentationStr}        " +
                  $"{readsSpecStr}")).GetFStarCodeOfStatement(indentation + 4);
                sep = ";\n";

                str += sep + (new FStarStmt($"{Name.ToString(0, false)}.End", null, false, false,
                  $"ExternalMethodEndStatement\n{indentationStr}        " + 
                  $"({ensuresSpecStr})\n{indentationStr}        " +
                  $"{logsSpecStr}")).GetFStarCodeOfStatement(indentation + 4);
                sep = ";\n";
            }
            foreach (var statement in Stmts)
            {
                statement.ToFStarLang(indentation + 4);
                FStarStmts.AddRange(statement.FStarStmts);
            }
            foreach (var callerStmt in CallerStmtList)
            {
                callerStmt.ToFStarLang(indentation + 4);
                FStarStmts.AddRange(callerStmt.FStarStmts);
            }
            if (IsCalledWithThread)
            {
                FStarStmts.Add(new FStarStmt($"{Name.ToString(0, false)}.End", null, false, false, 
                    $"TerminateThreadStatement \"{Name.ToString(0, false)}\""));
            }
            str += sep + String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation + 4)));
            str += indentationStr + "\n  ]";
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            foreach (var arg in Args)
            {
                foreach (var node in arg.AllChildren())
                    yield return node;
                yield return arg;
            }
            if (Ret != null)
            {
                foreach (var node in Ret.AllChildren())
                    yield return node;
                yield return Ret;
            }
            foreach (var spec in Specs)
            {
                foreach (var node in spec.AllChildren())
                    yield return node;
                yield return spec;
            }
            foreach (var varDecl in VarDeclList)
            {
                foreach (var node in varDecl.AllChildren())
                    yield return node;
                yield return varDecl;
            }
            foreach (var stmt in Stmts)
            {
                foreach (var node in stmt.AllChildren())
                    yield return node;
                yield return stmt;
            }
            foreach (var attr in Attrs)
            {
                foreach (var node in attr.AllChildren())
                    yield return node;
                yield return attr;
            }
        }
    }

    public abstract class MethodSpec : AstNode
    {
        public List<Expr> Elements;
        public Expr overallExpr = null;
        public List<Attribute> Attrs = null;
        public MethodSpec(Token firstTok, List<Expr> elements) : base(firstTok)
        {
            this.Elements = elements;
        }

        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotSupportedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotSupportedException();
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var e in Attrs)
            {
                foreach (var node in e.AllChildren())
                    yield return node;
                yield return e;
            }
            foreach (var e in Elements)
            {
                foreach (var node in e.AllChildren())
                    yield return node;
                yield return e;
            }
        }
        public override string ToFStarLang(int indentation)
        {
            if (overallExpr != null)
            {
                return overallExpr.ToFStarLang(indentation);
            }
            else
            {
                throw new NotImplementedException();
            }
        }
    }

    public class MethodSpecAwaits : MethodSpec
    {
        public MethodSpecAwaits(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "awaits ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public class MethodSpecUndefinedUnless : MethodSpec
    {
        public MethodSpecUndefinedUnless(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "undefined_unless ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public class MethodSpecEnsures : MethodSpec
    {
        public MethodSpecEnsures(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "ensures ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public class MethodSpecModifies : MethodSpec
    {
        public MethodSpecModifies(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "modifies ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(null, ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public class MethodSpecReads : MethodSpec
    {
        public List<Ident> Variables = new List<Ident>();
        public MethodSpecReads(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "reads ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(null, ref errors);
                Contract.Assert(e is Ident);
                Variables.Add(e as Ident);
            }
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            var sep = "";
            foreach (var v in Variables)
            {
                str += sep + indentationStr + $"{{ var_id = \"{v.ToString(0, false)}\"; ";
                str += $"iv = ";
                str += "InitializerArbitrary";
                str += $" ({v.Ty.ToFStarLang(0, true)});";
                str += " weakly_consistent = false; }";
                sep = " ;\n";
            }
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
            {
                yield return node;
            }
            foreach (var e in Variables)
            {
                foreach (var node in e.AllChildren())
                    yield return node;
                yield return e;
            }
        }
    }

    public class MethodSpecRequires : MethodSpec
    {
        public MethodSpecRequires(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "requires ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public class MethodSpecLogs : MethodSpec
    {
        public MethodSpecLogs(Token firstTok, List<Expr> elements) : base(firstTok, elements)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "logs ";
            var sep = "";
            foreach (var element in Elements)
            {
                str += sep + element.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (var e in Elements)
            {
                e.Sc = Sc;
                e.TypeResolve(null, ref errors);
            }
            overallExpr = Elements[0];
            for (int i = 1; i < Elements.Count; i++)
            {
                overallExpr = new BinaryExpr(overallExpr.FirstTok, overallExpr, Elements[i], Opcode.And, false);
            }
        }
    }

    public enum InvariantType {
        MAINTAINED_IF_STATEMENT_SATISFIES = 1,
        MAINTAINED_IF_VARS_UNCHANGED = 2
    }

    public class InvariantDecl : MemberDecl
    {
        public Expr Body;
        public InvariantType InvType;
        public List<Ident> UnchangedVars;

        public InvariantDecl(Token tok, Ident name, Expr body, InvariantType invType, List<Ident> unchangedVars) : base(tok)
        {
            this.Name = name;
            this.Body = body;
            this.InvType = invType;
            this.UnchangedVars = unchangedVars;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "invariant " + this.Name.ToString(0, labelOn) + " {\n";
            str = str + this.Body.ToString(indentation + 2, labelOn) + "\n";
            str = str + indentationStr + "} by ";
            if (InvType == InvariantType.MAINTAINED_IF_STATEMENT_SATISFIES) {
                str += "maintained_if_statement_satisfies";
            } else if (InvType == InvariantType.MAINTAINED_IF_VARS_UNCHANGED) {
                str += "maintained_if_vars_unchanged";
            } else {
                throw new NotSupportedException();
            }
            var sep = " ";
            foreach (var id in UnchangedVars) {
                str += sep + id.ToString(0, false);
                sep = ", ";
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Body.Sc = Sc;
            Body.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotSupportedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotSupportedException();
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotSupportedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var child in Body.AllChildren()) {
                yield return child;
            }
            yield return Body;
            foreach (var id in UnchangedVars) {
                yield return id;
            }
        }
    }

    public class YieldPredicateDecl : MemberDecl
    {
        public Expr Body;

        public YieldPredicateDecl(Token tok, Ident name, Expr body) : base(tok)
        {
            this.Name = name;
            this.Body = body;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "yield predicate " + this.Name.ToString(0, labelOn) + " {\n";
            str = str + indentationStr + this.Body.ToString(0, labelOn) + "\n";
            str = str + indentationStr + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            throw new NotImplementedException();
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotImplementedException();
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            throw new NotImplementedException();
        }
    }


    public class Parameter : VarDecl
    {
        public Parameter(Token tok, Ident name, Type ty) : base(tok, name, ty)
        {
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Name.ToString(0, labelOn) + ":" + Ty.ToString(0);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            base.TypeResolve(enforcingType, ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }
        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Ty.ToCProgram(0) + " " + Name.ToCProgram(0);
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Name.ToString(0, false) + ":" + Ty.ToFStarLang(0, false);
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
        }
    }

    public class ProofDecl : AstNode
    {
        public Ident Name;
        public Ident LLevelName;
        public Ident HLevelName;
        public ProofStrategy Strategy;
        public ProofDecl(Token tok, Ident name, Ident LName, Ident HName, ProofStrategy strategy) : base(tok)
        {
            this.Name = name;
            this.LLevelName = LName;
            this.HLevelName = HName;
            this.Strategy = strategy;
        }
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "proof " + Name.ToString(0, labelOn) + " {\n";
            str = str + indentationStr + "  refinement " + LLevelName.ToString(0, labelOn) + " " + HLevelName.ToString(0, labelOn) + "\n";
            str = str + Strategy.ToString(indentation + 2, labelOn) + "\n";
            str = str + indentationStr + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // throw new NotImplementedException();
            // TODO: implement it
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            throw new NotImplementedException();
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            yield return LLevelName;
            yield return HLevelName;
            foreach (var node in Strategy.AllChildren())
                yield return node;
            yield return Strategy;
        }
    }

    public class Ident : Expr
    {
        public string Name;
        public VarDecl Declaration;

        public Ident(Token tok, string name)
        : base(tok)
        {
            this.Name = name;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string indentationStr = new string(' ', indentation);
            string str = indentationStr + Name;
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            VarDecl varDeclaration = Sc.GetVariableDecl(this, false);
            if (varDeclaration != null)
            {
                this.Ty = varDeclaration.Ty;
            }
            else
            {
                errors.SemErr(FirstTok, $"{Name} is not defined!");
                return;
            }
            this.Declaration = varDeclaration;
            this.Ty = varDeclaration.Ty;
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public bool FitsInInt8()
        {
            sbyte value;
            return sbyte.TryParse(Name, out value);
        }
        public bool FitsInInt16()
        {
            Int16 value;
            return Int16.TryParse(Name, out value);
        }
        public bool FitsInInt32()
        {
            Int32 value;
            return Int32.TryParse(Name, out value);
        }
        public bool FitsInInt64()
        {
            Int64 value;
            return Int64.TryParse(Name, out value);
        }
        public bool FitsInUInt8()
        {
            byte value;
            return byte.TryParse(Name, out value);
        }
        public bool FitsInUInt16()
        {
            UInt16 value;
            return UInt16.TryParse(Name, out value);
        }
        public bool FitsInUInt32()
        {
            UInt32 value;
            return UInt32.TryParse(Name, out value);
        }
        public bool FitsInUInt64()
        {
            UInt64 value;
            return UInt64.TryParse(Name, out value);
        }
        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }
        public override string ToFStarLang(int indentation)
        {
            var declInLocalScope = Sc.GetVariableDecl(this, true);
            if (declInLocalScope == Declaration)
            {
                // local variable
                return $"ExpressionLocalVariable ({this.Ty.ToFStarLang(0, true)}) \"{this.ToString(0, false)}\"";
            }
            else
            {
                // global variable
                return $"ExpressionGlobalVariable ({this.Ty.ToFStarLang(0, true)}) \"{this.ToString(0, false)}\"";
            }
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            if (armadaStateName == "") {
                return Name;
            } else {
                return $"{armadaStateName}.mem (RootIdGlobal \"{Name}\")";
            }
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }
}
