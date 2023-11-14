using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Starmada
{
    public class FStarStmt
    {
        public string StartPC;
        public string EndPC;
        public bool StartsAtomicBlock;
        public bool EndsAtomicBlock;
        public string Statement;
        public string Comment;

        public FStarStmt(string startPC, string endPC, bool startsAtomicBlock, bool endsAtomicBlock, string statement, string comment = null)
        {
            Contract.Requires(startPC != null);
            Contract.Requires(statement != null);
            this.StartPC = startPC;
            this.EndPC = endPC;
            this.StartsAtomicBlock = startsAtomicBlock;
            this.EndsAtomicBlock = endsAtomicBlock;
            this.Statement = statement;
            this.Comment = comment;
        }

        public override bool Equals(object o)
        {
            if (o == null)
                return false;
            var second = o as FStarStmt;
            return StartPC == second.StartPC && EndPC == second.EndPC && StartsAtomicBlock == second.StartsAtomicBlock && EndsAtomicBlock == second.EndsAtomicBlock && Statement == second.Statement;
        }

        public override int GetHashCode()
        {
            return (StartPC + EndPC + $"{StartsAtomicBlock}{EndsAtomicBlock}" + Statement).GetHashCode();
        }

        public static bool operator==(FStarStmt a, FStarStmt b){
            return a.Equals(b);
        }   
        public static bool operator!=(FStarStmt a, FStarStmt b){
            return !a.Equals(b);
        }

        public string GetFStarCodeOfStatement(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (Comment != null && Comment.Length > 0)
                str += indentationStr + $"(* {Comment} *)\n";
            str += indentationStr + "{\n";
            str += indentationStr + $"  start_pc = {(StartPC != null ? $"Some \"{StartPC}\"" : "None")};\n";
            str += indentationStr + $"  end_pc = {(EndPC != null ? $"Some \"{EndPC}\"" : "None")};\n";
            str += indentationStr + $"  starts_atomic_block = ";
            str += StartsAtomicBlock ? "true;\n" : "false;\n";
            str += indentationStr + $"  ends_atomic_block = ";
            str += EndsAtomicBlock ? "true;\n" : "false;\n";
            str += indentationStr + $"  statement = {Statement};\n";
            str += indentationStr + "}";
            return str;
        }
    }

    public abstract class Statement : AstNode
    {
        public Ident Label;
        public bool StartsAtomicBlock = true;
        public bool EndsAtomicBlock = true;
        public bool InAtomicBlock = false;
        public List<FStarStmt> FStarStmts;

        public Statement(Token tok) : base(tok)
        {
            FStarStmts = new List<FStarStmt>();
        }

        // Translate? Pretty printing?
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (Label != null && labelOn)
            {
                str = str + indentationStr + "label " + Label.ToString(0, true) + ":";
            }
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Label;
        }
    }

    public class VarDecl : Statement
    {
        public Ident Name;
        public Type Ty;
        public Expr Value; // Want option
        public bool IsGhost;
        public bool IsNoaddr;
        public bool IsConst;
        public bool IsStronglyConsistent;

        public VarDecl(Token tok, Ident name, Type type = null, Expr expr = null, bool isGhost = false, bool isNoaddr = false, bool isConst = false, bool isStronglyConsistent = false) : base(tok)
        {
            this.Name = name;
            this.Ty = type;
            this.Value = expr;
            this.IsGhost = isGhost;
            this.IsNoaddr = isNoaddr;
            this.IsConst = isConst;
            this.IsStronglyConsistent = isStronglyConsistent;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string preStr = "";
            if (IsGhost)
            {
                preStr += "ghost ";
            }
            if (IsNoaddr)
            {
                preStr += "noaddr ";
            }
            if (IsConst)
            {
                preStr += "const ";
            }
            if (IsStronglyConsistent)
            {
                preStr += "sc ";
            }
            if (Ty == null)
            {
                str = str + indentationStr + base.ToString(0, labelOn) +
                  preStr + "var " + Name.ToString(0, labelOn);
            }
            else
            {
                str = str + indentationStr + base.ToString(0, labelOn) +
                  preStr + "var " + Name.ToString(0, labelOn) + ":" + Ty.ToString(0); // TODO: Fix it: T could be null, it will cause System.NullReferenceException:
            }
            if (Value != null)
            {
                str = str + " := " + Value.ToString(0, labelOn);
            }
            str = str + ";";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // Variable declaration type cannot be enforced
            Contract.Requires(enforcingType == null);
            // Variable declaration's type should be specified
            if (Ty == null)
            {
                // During err output labels are always printed
                // FIXME: fixed Name.Tok to make it compile
                errors.SemErr(Name.FirstTok, Name.ToString(0, true) + "'s type is not defined.");
            }
            VarDecl varDeclaration = Sc.GetVariableDecl(Name, true);
            if (varDeclaration != null)
            {
                errors.SemErr(FirstTok, $"{Name.ToString(0, false)} is already defined at line {varDeclaration.FirstTok.line}:{varDeclaration.FirstTok.col}!");
            }
            // TODO check if Ty is inside the scope as a user-defined type or not.
            bool isDefinedType = Sc.IsDefinedType(Ty);
            if (!isDefinedType)
            {
                errors.SemErr(FirstTok, Ty.ToString(0) + "'s type is not defined.");
            }
            Sc.Push(this);
            if (Value != null)
            {
                Value.Sc = Sc;
                Value.TypeResolve(Ty, ref errors);
                if (Ty == null)
                {
                    Ty = Value.Ty;
                }
            }
            Name.Sc = Sc;
            Name.Ty = Ty;
            // currentScope.Pop();
            // if (Ty != null)
            //     Console.WriteLine($"{Name.ToString(0, true)} : {Ty.ToString(0)}");
            // else
            //     Console.WriteLine($"{Name.ToString(0, true)} : undefined");
            // TODO: Check for incompatibility
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            // TODO: Implement this function
            this.PC = $"{parentPC}.{index}";
            if (Value != null)
            {
                Value.SetProgramCounter(this.PC, 0);
            }
        }

        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            if (Value != null)
            {
                Value.SetNextProgramCounter(this.NextPC);
            }
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string preStr = "";
            if (IsGhost || Ty == null)
            {
                return "";
            }
            if (IsConst)
            {
                preStr += "const ";
            }

            if (Ty is PointerType)
            {
                PointerType pt = (PointerType)Ty;
                str = str + indentationStr + //base.ToCProgram(0) +
                    preStr + pt.EntityType.ToCProgram(0) + "* " + Name.ToCProgram(0);
            }
            else if (Ty is TypeSuffix)
            {
                // Array case
                str = str + indentationStr + preStr + ((TypeSuffix)Ty).EntityType.ToCProgram(0)
                    + " " + Name.ToCProgram(0) + Ty.ToCProgram(0);
            }
            else
            {
                str = str + indentationStr + preStr
                    + Ty.ToCProgram(0) + " " + Name.ToCProgram(0);
            }

            if (Value != null)
            {
                str = str + " = " + Value.ToCProgram(0);
            }
            str = str + ";";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"{{ var_id = \"{Name.ToString(0, false)}\"; ";
            str += $"iv = ";
            if (Value == null)
            {
                str += "InitializerArbitrary";
                str += $" ({Ty.ToFStarLang(0, true)});";
            }
            else
            {
                str += "InitializerSpecific";
                var constantValue = Value as FStarExpressionConstant;
                str += $" ({constantValue.ToFStarObjectValue()});";
            }
            str += $" weakly_consistent = ";
            if (IsGhost | IsStronglyConsistent) {
                str += "false";
            }
            else {
                str += "true";
            }
            str += "; }";
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Name;
            if (Value != null)
            {
                yield return Value;
            }
        }
    }

    public class BoundVarDecl : VarDecl
    {
        public BoundVarDecl(Token tok, Ident name, Type type = null)
        : base(tok, name, type, null, false, false, false) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + Name.ToString(0, labelOn) + ':' + Ty.ToString(0);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // Variable declaration type cannot be enforced
            Contract.Requires(enforcingType == null);
            // Variable declaration's type should be specified
            if (Ty == null)
            {
                // During err output labels are always printed
                // FIXME: fixed Name.Tok to make it compile
                errors.SemErr(Name.FirstTok, Name.ToString(0, true) + "'s type is not defined.");
            }
            // We allow variable shadowing in BoundVarDecl
            // TODO check if Ty is inside the scope as a user-defined type or not.
            bool isDefinedType = Sc.IsDefinedType(Ty);
            if (!isDefinedType)
            {
                errors.SemErr(FirstTok, Ty.ToString(0) + "'s type is not defined.");
            }
            Sc.Push(this);
            // currentScope.Pop();
            // if (Ty != null)
            //     Console.WriteLine($"{Name.ToString(0, true)} : {Ty.ToString(0)}");
            // else
            //     Console.WriteLine($"{Name.ToString(0, true)} : undefined");
            // TODO: Check for incompatibility
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            if (index == 0)
                this.PC = $"{parentPC}";
            else
                this.PC = $"{parentPC}.{index}";
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
        }
    }

    public class BlockStatement : Statement
    {
        public List<Statement> Stmts;

        public BlockStatement(Token tok) : base(tok)
        {
            Stmts = new List<Statement>();
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "{\n";
            foreach (var stmt in Stmts)
            {
                str = str + stmt.ToString(indentation + 2, labelOn) + "\n";
            }
            str = str + indentationStr + "}";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "{\n";
            foreach (var stmt in Stmts)
            {
                str = str + stmt.ToCProgram(indentation + 2) + "\n";
            }
            str = str + indentationStr + "}";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (Stmts.Count == 0)
            {
                errors.SemErr(this.FirstTok, "Empty block statement is not allowed!");
            }

            // Set StartsAtomicBlock and EndsAtomicBlock
            Contract.Requires(InAtomicBlock || (!InAtomicBlock && StartsAtomicBlock && EndsAtomicBlock));
            if (InAtomicBlock)
            {
                // Remove nested atomic blocks
                for (int i = 0; i < Stmts.Count; i++)
                {
                    if (Stmts[i] is AtomicStatement)
                    {
                        var removedBlock = (Stmts[i] as AtomicStatement).BlockStmt;
                        Stmts.RemoveAt(i);
                        Stmts.InsertRange(i, removedBlock.Stmts);
                        i--;
                    }
                }
                foreach (var stmt in Stmts)
                {
                    stmt.StartsAtomicBlock = false;
                    stmt.EndsAtomicBlock = false;
                    stmt.InAtomicBlock = true;
                }
                if (Stmts.Count != 0)
                {
                    Stmts[0].StartsAtomicBlock = StartsAtomicBlock;
                    Stmts[Stmts.Count - 1].EndsAtomicBlock = Stmts[Stmts.Count - 1].EndsAtomicBlock || EndsAtomicBlock;
                }
            }

            for (int i = 0; i < Stmts.Count; i++)
            {
                var stmt = Stmts[i];
                stmt.Sc = Sc;
                stmt.TypeResolve(null, ref errors);
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            if (index != 0)
                this.PC = $"{parentPC}.{index}";
            else
                this.PC = parentPC;
            for (int i = 0; i < Stmts.Count; i++)
            {
                Stmts[i].SetProgramCounter(this.PC, i + 1);
            }
            for (int i = 0; i < Stmts.Count - 1; i++)
            {
                Stmts[i].SetNextProgramCounter(Stmts[i + 1].PC);
            }
            if (Stmts.Count > 0)
                this.PC = Stmts[0].PC;
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            if (Stmts.Count > 0)
            {
                Stmts[Stmts.Count - 1].SetNextProgramCounter(nextPC);
                this.NextPC = Stmts[Stmts.Count - 1].NextPC;
            }
            else
            {
                this.NextPC = nextPC;
            }
        }
        public override string ToFStarLang(int indentation)
        {
            foreach (var stmt in Stmts)
            {
                stmt.ToFStarLang(indentation);
                FStarStmts.AddRange(stmt.FStarStmts);
            }
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var stmt in Stmts)
            {
                foreach (var node in stmt.AllChildren())
                    yield return node;
                yield return stmt;
            }
        }
    }

    public class FunctionCallStatement : Statement
    {
        Expr Destination;
        Expr Source;
        bool IsSequential;
        MethodDecl Caller;
        public FunctionCallStatement(MethodDecl caller,
            Expr destination, Expr source, bool isSequential, string PC, string nextPC)
          : base(caller.FirstTok)
        {
            this.Caller = caller;
            this.Destination = destination;
            this.IsSequential = isSequential;
            this.Source = source;
            this.PC = PC;
            this.NextPC = nextPC;
        }
        public override string ToString(int indentation, bool labelOn)
        {
            return "";
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotImplementedException();
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
        public override string ToFStarLang(int indentation)
        {
            string statement = $"ReturnStatement \"{Caller.Name.ToString(0, false).ToLower()}\" ";
            if (IsSequential)
                statement += "true";
            else
                statement += "false";
            if (Destination != null)
            {
                statement += $" ([{Destination.ToFStarLang(0)}]) ([{Source.ToFStarLang(0)}])";
            }
            else
            {
                Contract.Assert(Source == null);
                statement += $" [] []";
            }
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, 
                (NextPC.EndsWith(".R") ? false : EndsAtomicBlock),
                statement, $"return from {PC} to {NextPC}"));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Destination.AllChildren())
                yield return node;
            yield return Destination;
            foreach (var node in Source.AllChildren())
                yield return node;
            yield return Source;
            foreach (var node in Caller.AllChildren())
                yield return node;
            yield return Caller;
        }
    }

    public class ApplySuffixStatement : Statement
    {
        ApplySuffix FunctionCall;
        public ApplySuffixStatement(ApplySuffix functionCall) : base(functionCall.FirstTok)
        {
            this.FunctionCall = functionCall;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            return FunctionCall.ToString(indentation, labelOn);
        }

        public override string ToCProgram(int indentation)
        {
            return FunctionCall.ToCProgram(indentation);
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            FunctionCall.Sc = Sc;
            FunctionCall.TypeResolve(enforcingType, ref errors);
            if (FunctionCall.Callee == null)
            {
                errors.SemErr(FunctionCall.FirstTok, "datatype member constructor can't be called without an lhs.");
            }
            var callee = FunctionCall.Callee;
            if (callee.Ret != null)
            {
                errors.SemErr(FirstTok, "returned value is ignored!");
            }
            callee.AddCaller(null, false, PC + ".R");
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            this.FunctionCall.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            this.FunctionCall.SetNextProgramCounter(this.NextPC);
        }

        public override string ToFStarLang(int indentation)
        {
            string endPC = $"{FunctionCall.Callee.Name.ToString(0, false).ToLower()}.1";
            bool atomicMethod = FunctionCall.Callee.IsAtomic;
            var functionCall = new FunctionCall(FunctionCall.FirstTok, FunctionCall.BaseExpr, FunctionCall.Args, FunctionCall.Callee);
            functionCall.NextPC = PC + ".R";
            FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, !atomicMethod, 
              functionCall.ToFStarLang(0, false /* no stack overflow */), this.ToString(0, false)));
            FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, true /* stack overflow always ends atomic block */,
              functionCall.ToFStarLang(0, true /* stack overflow */), this.ToString(0, false)));
            FStarStmts.Add(new FStarStmt(PC + ".R", this.NextPC, false, EndsAtomicBlock, "UnconditionalJumpStatement", "return from method"));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in FunctionCall.AllChildren())
                yield return node;
            yield return FunctionCall;
        }
    }

    public class AssignStatement : Statement
    {
        public Expr Lhs;
        public Expr Rhs;
        public bool IsSequential;

        public AssignStatement(Token tok, Expr lhs, Expr rhs, bool isSequential) : base(tok)
        {
            this.Lhs = lhs;
            this.Rhs = rhs;
            this.IsSequential = isSequential;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (base.ToString(0, labelOn) != "")
            {
                str = str + indentationStr + base.ToString(0, labelOn) + "\n";
            }
            str = str + indentationStr + Lhs.ToString(0, labelOn);
            if (Rhs != null)
            {
                str = str + (IsSequential ? " ::= " : " := ") + Rhs.ToString(0, labelOn);
            }
            str = str + ";";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            if (IsSequential)
            {
                throw new NotSupportedException();
            }
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (Rhs != null)
            {
                // Special case for create thread call
                if (Rhs is CreateThreadRhs)
                {
                    ((CreateThreadRhs)Rhs).SetThreadIDName(Lhs.ToCProgram(0));
                    str = str + Rhs.ToCProgram(indentation);
                }
                else
                {
                    str = str + indentationStr + Lhs.ToCProgram(0);
                    str = str + " = " + Rhs.ToCProgram(0);
                }
            }
            else
            {
                str = str + indentationStr + Lhs.ToCProgram(0);
            }
            str = str + ";";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Lhs.Sc = Sc;
            Lhs.TypeResolve(enforcingType, ref errors);
            if (Lhs is SeqSelectExpr && (Lhs as SeqSelectExpr).BaseExpr.Ty is not TypeSuffix)
            {
                errors.SemErr(Lhs.FirstTok, "Update a sequence or map using sequence assign expression (eg. new_s := s[0:=1];).");
            }
            if (Rhs != null)
            {
                Rhs.Sc = Sc;
                Rhs.TypeResolve(Lhs.Ty, ref errors);
                // Convert Rhs to function call
                if (Rhs is ApplySuffix && (Rhs as ApplySuffix).Callee != null)
                {
                    var funcCallExpr = Rhs as ApplySuffix;
                    Rhs = new FunctionCall(funcCallExpr.FirstTok, funcCallExpr.BaseExpr, funcCallExpr.Args, funcCallExpr.Callee);
                }
                foreach (var node in Rhs.AllChildren())
                {
                    if (node is ApplySuffix && (node as ApplySuffix).Callee != null)
                    {
                        errors.SemErr(node.FirstTok, "Function call must be in an assign statement! Example: a := f(x)");
                    }
                }
                if (Rhs is FunctionCall)
                {
                    var funcCallExpr = Rhs as FunctionCall;
                    var callee = funcCallExpr.Callee;
                    callee.AddCaller(Lhs, IsSequential, PC + ".R");
                }
                else if (Rhs is CreateThreadRhs)
                {
                    var funcCallExpr = Rhs as CreateThreadRhs;
                    var callee = funcCallExpr.Callee;
                    funcCallExpr.IsSequential = IsSequential;
                    funcCallExpr.OptionalResult = Lhs;
                    callee.AddThreadCaller();
                }
                else if (Rhs is AtomicExchangeRhs)
                {
                    var atomicExchangeExpr = Rhs as AtomicExchangeRhs;
                    atomicExchangeExpr.Lhs = Lhs;
                }
                else if (Rhs is AllocRhs)
                {
                    var allocRhs = Rhs as AllocRhs;
                    allocRhs.IsSequential = IsSequential;
                    allocRhs.Lhs = Lhs;
                }
                else if (Rhs is CompareAndSwapRhs)
                {
                    var compareAndSwapRhs = Rhs as CompareAndSwapRhs;
                    compareAndSwapRhs.IsSequential = IsSequential;
                    compareAndSwapRhs.OptionalResult = Lhs;
                }
            }
            // TODO: check compatibility
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            // TODO: Implement this function
            // Console.WriteLine($"Setting program counter to {parentPC}_{index} for {this.ToString(0, false)}");
            this.PC = $"{parentPC}.{index}";
            this.Lhs.SetProgramCounter(this.PC, 0);
            if (this.Rhs != null)
            {
                this.Rhs.SetProgramCounter(this.PC, 0);
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            this.Lhs.SetNextProgramCounter(this.NextPC);
            if (Rhs != null)
            {
                this.Rhs.SetNextProgramCounter(this.NextPC);
            }
        }

        public override string ToFStarLang(int indentation)
        {
            string endPC = NextPC;
            string statement;
            if (Rhs is FunctionCall)
            {
                var funcCallExpr = Rhs as FunctionCall;
                funcCallExpr.NextPC = PC + ".R";
                endPC = $"{funcCallExpr.Callee.Name.ToString(0, false).ToLower()}.1";
                bool atomicMethod = funcCallExpr.Callee.IsAtomic;
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, !atomicMethod, 
                  funcCallExpr.ToFStarLang(0, false /* no stack overflow */), this.ToString(0, false)));
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, true /* stack overflow always ends atomic block */, 
                  funcCallExpr.ToFStarLang(0, true /* stack overflow */), this.ToString(0, false)));
                FStarStmts.Add(new FStarStmt(PC + ".R", this.NextPC, false, EndsAtomicBlock, "UnconditionalJumpStatement", "return from method"));
            }
            else if (Rhs is CreateThreadRhs)
            {
                var createThreadExpr = Rhs as CreateThreadRhs;
                statement = createThreadExpr.ToFStarLang(0);
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
            }
            else if (Rhs is AtomicExchangeRhs)
            {
                var atomicExchangeExpr = Rhs as AtomicExchangeRhs;
                statement = atomicExchangeExpr.ToFStarLang(0);
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
            }
            else if (Rhs is AllocRhs)
            {
                var allocRhs = Rhs as AllocRhs;
                var statements = allocRhs.ToFStarLang(0).Split('\n');                
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statements[0], this.ToString(0, false)));
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statements[1], this.ToString(0, false)));
            }
            else if (Rhs is CompareAndSwapRhs)
            {
                var compareAndSwapRhs = Rhs as CompareAndSwapRhs;
                statement = compareAndSwapRhs.ToFStarLang(0);
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
            }
            else if (Rhs is WildcardExpr)
            {
                statement = "NondeterministicUpdateStatement ";
                statement += IsSequential ? "true" : "false";
                statement += $" ({Lhs.ToFStarLang(0)})";
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
            }
            else
            {
                statement = "UpdateStatement ";
                if (IsSequential)
                    statement += "true";
                else
                    statement += "false";
                statement += $" ({Lhs.ToFStarLang(0)}) ({Rhs.ToFStarLang(0)})";
                FStarStmts.Add(new FStarStmt(PC, endPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
            }
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Lhs.AllChildren())
                yield return node;
            yield return Lhs;
            if (Rhs != null)
            {
                foreach (var node in Rhs.AllChildren())
                    yield return node;
            }
            yield return Rhs;
        }
    }

    public class AtomicStatement : Statement
    {
        public BlockStatement BlockStmt;

        public AtomicStatement(Token tok, BlockStatement block) : base(tok)
        {
            this.BlockStmt = block;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (base.ToString(0, labelOn) != "")
            {
                str = str + indentationStr + base.ToString(0, labelOn) + "\n";
            }
            str = str + indentationStr + FirstTok.val + "\n" + BlockStmt.ToString(indentation, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // Set StartsAtomicBlock and EndsAtomicBlock
            Contract.Requires(InAtomicBlock || (!InAtomicBlock && StartsAtomicBlock && EndsAtomicBlock));
            BlockStmt.StartsAtomicBlock = !InAtomicBlock || StartsAtomicBlock;
            BlockStmt.EndsAtomicBlock = !InAtomicBlock || EndsAtomicBlock;
            BlockStmt.InAtomicBlock = true;

            BlockStmt.Sc = Sc;
            BlockStmt.TypeResolve(enforcingType, ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            BlockStmt.SetProgramCounter($"{parentPC}.{index}", 0);
            this.PC = BlockStmt.PC;
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            BlockStmt.SetNextProgramCounter(nextPC);
            this.NextPC = BlockStmt.NextPC;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            BlockStmt.ToFStarLang(indentation);
            this.FStarStmts = BlockStmt.FStarStmts;
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in BlockStmt.AllChildren())
                yield return node;
            yield return BlockStmt;
        }
    }

    public class AssertStatement : Statement
    {
        public Expr Cond;

        public AssertStatement(Token tok, Expr cond) : base(tok)
        {
            this.Cond = cond;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "assert " + Cond.ToString(0, labelOn) + ";";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Cond.Sc = Sc;
            Cond.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            // TODO: Implement this function
            this.PC = $"{parentPC}.{index}";
            Cond.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            this.Cond.SetNextProgramCounter(this.NextPC);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "assert(" + Cond.ToCProgram(0) + ");";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string assertTrueStatement = "AssertTrueStatement (" + Cond.ToFStarLang(0) + ")";
            string assertFalseStatement = "AssertFalseStatement (" + Cond.ToFStarLang(0) + ")";
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, assertTrueStatement, ToString(0, false) + " true"));
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, assertFalseStatement, ToString(0, false) + " false"));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Cond.AllChildren())
                yield return node;
            yield return Cond;
        }
    }

    public class AssumeStatement : Statement
    {
        public Expr Cond;

        public AssumeStatement(Token tok, Expr cond) : base(tok)
        {
            this.Cond = cond;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + FirstTok.val + " " + Cond.ToString(0, labelOn) + ";";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Cond.Sc = Sc;
            Cond.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            this.Cond.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            this.Cond.SetNextProgramCounter(this.NextPC);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string assumeStatement = "AssumeExpressionStatement (" + Cond.ToFStarLang(0) + ")";
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, assumeStatement, ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Cond.AllChildren())
                yield return node;
            yield return Cond;
        }
    }

    public class JoinStatement : Statement
    {
        public Expr threadId;

        public JoinStatement(Token tok, Expr tid) : base(tok)
        {
            this.threadId = tid;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "join " + threadId.ToString(0, labelOn) + ";";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            threadId.Sc = Sc;
            threadId.TypeResolve(new PredefinedType(PredefinedTypeEnum.ThreadId), ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            this.threadId.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
            this.threadId.SetNextProgramCounter(this.NextPC);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "pthread_join(" + threadId.ToCProgram(0) + ", NULL);";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string statement = $"JoinStatement ({threadId.ToFStarLang(0)})";
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, statement, ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in threadId.AllChildren())
                yield return node;
            yield return threadId;
        }
    }

    public class WhileBlock : Statement
    {
        public Expr Cond;
        // FIXME: method/invariant spec
        public BlockStatement BlockStmt;

        public WhileBlock(Token tok, Expr cond, BlockStatement block) : base(tok)
        {
            this.Cond = cond;
            this.BlockStmt = block;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "while " + Cond.ToString(0, labelOn) + "\n" + BlockStmt.ToString(indentation, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // Set StartsAtomicBlock and EndsAtomicBlock
            if (InAtomicBlock)
            {
                BlockStmt.StartsAtomicBlock = false;
                BlockStmt.EndsAtomicBlock = this.EndsAtomicBlock;
                BlockStmt.InAtomicBlock = true;
            }
            this.EndsAtomicBlock = false;

            Cond.Sc = Sc;
            Cond.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            BlockStmt.Sc = Sc;
            BlockStmt.TypeResolve(null, ref errors);
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            Cond.SetProgramCounter(this.PC + ".C", 0);
            BlockStmt.SetProgramCounter(this.PC + ".Loop", 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            BlockStmt.SetNextProgramCounter(Cond.PC);
            Cond.SetNextProgramCounter(BlockStmt.PC);
            this.NextPC = nextPC;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "while (" + Cond.ToCProgram(0) + ")\n" + BlockStmt.ToCProgram(indentation);
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            // unconditional jump
            FStarStmt jump = new FStarStmt(this.PC, Cond.PC, StartsAtomicBlock, false, "UnconditionalJumpStatement", "UnconditionalJumpStatement");
            FStarStmts.Add(jump);
            if (Cond is WildcardExpr)
            {
                FStarStmts.Add(new FStarStmt(Cond.PC, Cond.NextPC, false, EndsAtomicBlock, "UnconditionalJumpStatement", "while * --taken"));
                FStarStmts.Add(new FStarStmt(Cond.PC, this.NextPC, false, BlockStmt.EndsAtomicBlock, "UnconditionalJumpStatement", "while * --not taken"));
            }
            else
            {
                // cond -> loop
                string thenStatement = $"ConditionalJumpStatement ({Cond.ToFStarLang(0)})";
                FStarStmts.Add(new FStarStmt(Cond.PC, Cond.NextPC, false, EndsAtomicBlock, thenStatement, $"while {Cond.ToString(0, false)}"));
                // cond -> out loop
                string elseStatement = $"ConditionalJumpStatement ";
                elseStatement += $"(ExpressionUnaryOperator (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool) Armada.UnaryOp.UnaryOpNot ({Cond.ToFStarLang(0)}))";
                FStarStmts.Add(new FStarStmt(Cond.PC, this.NextPC, false, BlockStmt.EndsAtomicBlock, elseStatement, $"!({Cond.ToString(0, false)})"));
            }
            // loop
            BlockStmt.ToFStarLang(indentation);
            FStarStmts.AddRange(BlockStmt.FStarStmts);
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Cond.AllChildren())
                yield return node;
            yield return Cond;
            foreach (var node in BlockStmt.AllChildren())
                yield return node;
            yield return BlockStmt;
        }
    }

    public class IfStatement : Statement
    {
        public Expr Cond;
        public BlockStatement Then;
        public Statement Else; // FIXME: Optional

        public string IfElseNextPC;
        public bool IfElseEndsAtomicBlock = false;

        public IfStatement(Token tok, Expr condition, BlockStatement thenPath, Statement elsePath = null) : base(tok)
        {
            Contract.Requires(condition != null);
            Contract.Requires(thenPath != null);
            Cond = condition;
            Then = thenPath;
            Else = elsePath;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "if " + Cond.ToString(0, labelOn) + "\n" + Then.ToString(indentation, labelOn);
            if (Else != null)
            {
                str = str + "\n" + indentationStr + "else\n" + Else.ToString(indentation, labelOn);
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // Set StartsAtomicBlock and EndsAtomicBlock
            if (InAtomicBlock)
            {
                Then.StartsAtomicBlock = false;
                Then.EndsAtomicBlock = this.EndsAtomicBlock;
                Then.InAtomicBlock = true;
                if (Else != null)
                {
                    Else.StartsAtomicBlock = false;
                    Else.EndsAtomicBlock = this.EndsAtomicBlock;
                    Else.InAtomicBlock = true;
                    this.IfElseEndsAtomicBlock = false;
                }
                else
                {
                    this.IfElseEndsAtomicBlock = this.EndsAtomicBlock;
                }
                this.EndsAtomicBlock = false;
            }

            Cond.Sc = Sc;
            Cond.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            Then.Sc = Sc;
            Then.TypeResolve(null, ref errors);

            if (Else != null)
            {
                Else.Sc = Sc;
                Else.TypeResolve(null, ref errors);
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            Cond.SetProgramCounter(this.PC, 0);
            Then.SetProgramCounter(this.PC + ".T", 0);
            if (Else != null)
            {
                Else.SetProgramCounter(this.PC + ".F", 0);
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            Then.SetNextProgramCounter(nextPC);
            if (Else != null)
            {
                Else.SetNextProgramCounter(nextPC);
                IfElseNextPC = Else.PC;
            }
            else
            {
                IfElseNextPC = nextPC;
            }
            Cond.SetNextProgramCounter(Then.PC);
            this.NextPC = nextPC;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "if (" + Cond.ToCProgram(0) + ")\n" + Then.ToCProgram(indentation);
            if (Else != null)
            {
                str = str + "\n" + indentationStr + "else\n" + Else.ToCProgram(indentation);
            }
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            if (Cond is WildcardExpr)
            {
                FStarStmts.Add(new FStarStmt(PC, Cond.NextPC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", "if * --taken"));
                FStarStmts.Add(new FStarStmt(PC, IfElseNextPC, StartsAtomicBlock, IfElseEndsAtomicBlock, "UnconditionalJumpStatement", "if * --not taken"));
            }
            else
            {
                // cond -> then
                string thenStatement = $"ConditionalJumpStatement ({Cond.ToFStarLang(0)})";
                FStarStmts.Add(new FStarStmt(PC, Cond.NextPC, StartsAtomicBlock, EndsAtomicBlock, thenStatement, $"if {Cond.ToString(0, false)}"));
                // cond -> else
                string elseStatement = $"ConditionalJumpStatement ";
                elseStatement += $"(ExpressionUnaryOperator (ObjectTDPrimitive PrimitiveTDBool) (ObjectTDPrimitive PrimitiveTDBool) Armada.UnaryOp.UnaryOpNot ({Cond.ToFStarLang(0)}))";
                FStarStmts.Add(new FStarStmt(PC, IfElseNextPC, StartsAtomicBlock, IfElseEndsAtomicBlock, elseStatement, $"!({Cond.ToString(0, false)})"));
            }
            // then
            Then.ToFStarLang(indentation);
            FStarStmts.AddRange(Then.FStarStmts);
            // optinal else
            if (Else != null)
            {
                Else.ToFStarLang(indentation);
                FStarStmts.AddRange(Else.FStarStmts);
            }
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Cond.AllChildren())
                yield return node;
            yield return Cond;
            foreach (var node in Then.AllChildren())
                yield return node;
            yield return Then;
            if (Else != null)
            {
                foreach (var node in Else.AllChildren())
                    yield return node;
                yield return Else;
            }
        }
    }

    public class SomehowStatement : Statement
    {
        public readonly Expr UndefinedUnless;
        public readonly List<Ident> Mod;
        public readonly Expr Ens;
        public readonly List<Attribute> Attrs;
        public bool IsSequential = false;

        public SomehowStatement(Token tok, List<Expr> undefinedUnless, List<Ident> mod, List<Expr> ens, List<Attribute> attrs) : base(tok)
        {
            Contract.Requires(undefinedUnless != null);
            Contract.Requires(mod != null);
            Contract.Requires(ens != null);

            if (undefinedUnless.Count == 0)
            {
                UndefinedUnless = null;
            }
            else
            {
                UndefinedUnless = undefinedUnless[0];
                for (int i = 1; i < undefinedUnless.Count; i++)
                {
                    UndefinedUnless = new BinaryExpr(UndefinedUnless.FirstTok,
                      UndefinedUnless, undefinedUnless[i], Opcode.And);
                }
                UndefinedUnless.LastTok = undefinedUnless[undefinedUnless.Count - 1].LastTok;
            }
            this.Mod = mod;
            if (ens.Count == 0)
            {
                Ens = null;
            }
            else
            {
                Ens = ens[0];
                for (int i = 1; i < ens.Count; i++)
                {
                    Ens = new BinaryExpr(Ens.FirstTok,
                      Ens, ens[i], Opcode.And);
                }
                Ens.LastTok = ens[ens.Count - 1].LastTok;
            }
            this.Attrs = attrs;
            foreach (var attr in Attrs)
            {
                // check for bypass write buffer (bwb) attribute
                if (attr.Name.Name == "bwb")
                {
                    IsSequential = true;
                }
            }
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "somehow";
            if (Mod.Count != 0)
            {
                str += "\n" + indentationStr + "  modifies ";
                var sep = "";
                foreach (var m in Mod)
                {
                    str += sep + m.ToString(0, labelOn);
                    sep = ", ";
                }
            }
            if (Ens != null)
            {
                str += "\n" + indentationStr + "  ensures " + Ens.ToString(0, labelOn);
            }
            if (UndefinedUnless != null)
            {
                str += "\n" + indentationStr + "  undefined_unless " + UndefinedUnless.ToString(0, labelOn);
            }
            str += ";";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (UndefinedUnless != null)
            {
                UndefinedUnless.Sc = Sc;
                UndefinedUnless.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            foreach (var e in Mod)
            {
                e.Sc = Sc;
                e.TypeResolve(null, ref errors);
            }
            if (Ens != null)
            {
                Ens.Sc = Sc;
                Ens.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            // TODO: Implement this function
            this.PC = $"{parentPC}.{index}";
            if (UndefinedUnless != null)
                UndefinedUnless.SetProgramCounter(this.PC, 0);
            foreach (var expr in Mod)
            {
                expr.SetProgramCounter(this.PC, 0);
            }
            if (Ens != null)
                Ens.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string indentationStr = new string(' ', indentation);
            string statement = "SomehowStatement ";
            if (UndefinedUnless == null)
            {
                statement += "(ExpressionConstant (ObjectValueAbstract bool true)) ";
            }
            else
            {
                statement += "( " + UndefinedUnless.ToFStarLang(0) + ") ";
            }
            statement += (IsSequential ? "true\n" : "false\n");
            statement += indentationStr + "    [ ";
            var sep = "";
            foreach (var id in Mod)
            {
                statement += sep + "(" + id.ToFStarLang(0) + ")";
                sep = "; ";
            }
            statement += " ]\n";
            if (Ens == null)
            {
                statement += indentationStr + "    (ExpressionConstant (ObjectValueAbstract bool true)) ";
            }
            else
            {
                statement += indentationStr + "    (" + Ens.ToFStarLang(0) + ") ";
            }
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(indentation, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return UndefinedUnless;
            foreach (var expr in Mod)
            {
                foreach (var node in expr.AllChildren())
                    yield return node;
                yield return expr;
            }
            yield return Ens;
        }
    }

    public class MatchCaseStmt : MatchCase
    {
        public List<Statement> Stmts;

        public MatchCaseStmt(Token tok, string id, List<CasePattern> cps, List<Statement> stmts)
          : base(tok, id, cps)
        {
            Contract.Requires(id != null);
            // Contract.Requires(cce.NonNullElements(cps));
            Contract.Requires(stmts != null);
            this.Stmts = stmts;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = base.ToString(indentation, labelOn);
            List<string> stmtsStr = new List<string>();
            foreach (Statement stmt in Stmts)
            {
                stmtsStr.Add(stmt.ToString(0, labelOn));
            }
            str += string.Join("; ", stmtsStr);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            base.TypeResolve(null, ref errors);
            foreach (Statement stmt in Stmts)
            {
                stmt.Sc = Sc;
                stmt.TypeResolve(null, ref errors);
            }
            // no need to set this.Ty because this class is not an expression
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            throw new NotImplementedException();
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            List<string> stmtsStr = new List<string>();
            foreach (Statement stmt in Stmts)
            {
                stmtsStr.Add(stmt.ToCProgram(0));
            }
            str += string.Join("; ", stmtsStr);
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            foreach (var stmt in Stmts)
            {
                foreach (var node in stmt.AllChildren())
                    yield return node;
                yield return stmt;
            }
        }
    }

    public class MatchStatement : Statement
    {
        private Expr source;
        private List<MatchCaseStmt> cases;
        public readonly bool UsesOptionalBraces;

        public MatchStatement(Token tok, Expr source, List<MatchCaseStmt> cases, bool usesOptionalBraces)
        : base(tok)
        {
            Contract.Requires(source != null);
            // Contract.Requires(cce.NonNullElements(cases));
            this.source = source;
            this.cases = cases;
            this.UsesOptionalBraces = usesOptionalBraces;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            List<string> elementsStr = new List<string>();
            foreach (MatchCaseStmt stmt in cases)
            {
                elementsStr.Add(stmt.ToString(0, labelOn));
            }
            string CasesStr = string.Join(" ", elementsStr);
            if (UsesOptionalBraces)
            {
                CasesStr = "{" + CasesStr + "}";
            }
            str = str + indentationStr + "match " + source.ToString(0, labelOn) + " " + CasesStr;
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            source.Sc = Sc;
            source.TypeResolve(null, ref errors);
            foreach (MatchCaseStmt matchCase in cases)
            {
                matchCase.Sc = Sc;
                matchCase.TypeResolve(null, ref errors);
            }
        }

        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            for (int i = 0; i < cases.Count; i++)
            {
                cases[i].SetProgramCounter(this.PC, i);
            }
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            foreach (MatchCaseStmt matchCase in cases)
            {
                matchCase.SetNextProgramCounter(nextPC);
            }
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in source.AllChildren())
                yield return node;
            yield return source;
            foreach (var caseStmt in cases)
            {
                foreach (var node in caseStmt.AllChildren())
                    yield return node;
                yield return caseStmt;
            }
        }
    }

    public class ExprStatement : Statement
    {
        public Expr Expression;

        public ExprStatement(Token tok, Expr expr)
        : base(tok)
        {
            Contract.Requires(expr != null);
            Contract.Requires(expr is CreateThreadRhs || expr is CompareAndSwapRhs);
            Expression = expr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Expression.ToString(0, labelOn) + ';';
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Expression.Sc = Sc;
            Expression.TypeResolve(null, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Expression.ToCProgram(0) + ';';
            return str;
        }

        // TODO: programCounter may change
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            if (Expression is CreateThreadRhs)
            {
                CreateThreadRhs createThreadExpr = Expression as CreateThreadRhs;
                FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, createThreadExpr.ToFStarLang(0), ToString(0, false)));
            }
            else if (Expression is CompareAndSwapRhs)
            {
                CompareAndSwapRhs exprStmt = Expression as CompareAndSwapRhs;
                string compareStatement = exprStmt.ToFStarLang(0);
                FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, compareStatement, ToString(0, false)));
            }
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Expression.AllChildren())
                yield return node;
            yield return Expression;
        }
    }

    public class ContinueStatement : Statement
    {

        public ContinueStatement(Token tok)
        : base(tok)
        {
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "continue;";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "continue;";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (PC.LastIndexOf(".Loop") == -1) {
                errors.SemErr(this.FirstTok, $"continue is not used inside a while loop!");
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            if (PC.LastIndexOf(".Loop") != -1) {
                var startOfLatestLoopPC = this.PC.Substring(0, this.PC.LastIndexOf(".Loop"));
                var splitted = startOfLatestLoopPC.Split('.');
                this.NextPC = $"{String.Join('.', splitted.SkipLast(1))}.{Int32.Parse(splitted.Last())}.C";
            }
        }
        public override string ToFStarLang(int indentation)
        {
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", this.ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class BreakStatement : Statement
    {

        public BreakStatement(Token tok)
        : base(tok)
        {
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "break;";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "break;";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (PC.LastIndexOf(".Loop") == -1) {
                errors.SemErr(this.FirstTok, $"break is not used inside a while loop!");
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            if (PC.LastIndexOf(".Loop") != -1) {
                var startOfLatestLoopPC = this.PC.Substring(0, this.PC.LastIndexOf(".Loop"));
                var splitted = startOfLatestLoopPC.Split('.');
                this.NextPC = $"{String.Join('.', splitted.SkipLast(1))}.{Int32.Parse(splitted.Last()) + 1}";
            }
        }
        public override string ToFStarLang(int indentation)
        {
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", this.ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class ReturnStatement : Statement
    {
        public Expr Val;

        public ReturnStatement(Token tok, Expr val)
        : base(tok)
        {
            Val = val;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "return";
            str += (Val != null) ? " " + Val.ToString(0, labelOn) : "";
            str += ';';
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "return";
            str += (Val != null) ? " " + Val.ToCProgram(0) : "";
            str += ';';
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (Val != null)
            {
                Val.Sc = Sc;
                // TODO: set enforcingtype?
                Val.TypeResolve(enforcingType, ref errors);
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
            if (this.Val != null)
                this.Val.SetProgramCounter(this.PC, 0);
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = $"{this.PC.Split('.')[0]}.End";
            if (this.Val != null)
                this.Val.SetNextProgramCounter(this.NextPC);
        }
        public override string ToFStarLang(int indentation)
        {
            if (Val != null)
            {
                string statement = "UpdateStatement ";
                // TODO: What is the semantics of return statement with regards to sequential
                // if (IsSequential)
                statement += "true";
                // else
                // str += "false";
                var func = Sc.EnclosingNode as MethodDecl;
                statement += $" ({func.Ret.Name.ToFStarLang(0)}) ({Val.ToFStarLang(0)})";
                FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, statement, this.ToString(0, false)));
                return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
            }
            else {
                FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", this.ToString(0, false)));
                return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
            }
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            if (Val != null)
            {
                foreach (var node in Val.AllChildren())
                    yield return node;
                yield return Val;
            }
        }
    }

    public class YieldStatement : Statement
    {
        public YieldStatement(Token tok)
        : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "yield;";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            if (!InAtomicBlock) {
                FStarStmts.Add(new FStarStmt(PC, NextPC, true, true, "UnconditionalJumpStatement", this.ToString(0, false)));
            } else {
                // split the yield statement into two unconditional jump to handle atomic
                FStarStmts.Add(new FStarStmt(PC, PC + ".Y", false, true, "UnconditionalJumpStatement", this.ToString(0, false)));
                FStarStmts.Add(new FStarStmt(PC + ".Y", NextPC, true, false, "UnconditionalJumpStatement", this.ToString(0, false)));
            }
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class GotoStatement : Statement
    {
        public Ident Id;
        public Statement stmt; // filled in resolution

        public GotoStatement(Token tok, Ident id)
        : base(tok)
        {
            Contract.Requires(id != null);
            Id = id;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "goto " + Id.ToString(0, labelOn) + ';';
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            stmt = Sc.GetLabelStatement(Id);
            if (stmt == null)
            {
                errors.SemErr(Id.FirstTok, $"Label {Id.Name} not found!");
            }
            if (stmt.InAtomicBlock ^ InAtomicBlock)
            {
                errors.SemErr(FirstTok, "Goto cannot cross atomic block!");
            }
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            FStarStmts.Add(new FStarStmt(PC, stmt.PC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", this.ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Id;
        }
    }

    public class FenceStatement : Statement
    {
        public FenceStatement(Token tok)
        : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "fence;";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotImplementedException();
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        { }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, "FenceStatement", this.ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class DeallocStatement : Statement
    {
        Expr Addr;

        public DeallocStatement(Token tok, Expr addr)
        : base(tok)
        {
            Contract.Requires(addr != null);
            Addr = addr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "free(" + Addr.ToString(0, labelOn) + ");";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "free(" + Addr.ToCProgram(0) + ");";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Addr.Sc = Sc;
            Addr.TypeResolve(null, ref errors); // TODO: change to pointer type?
        }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            string deallocStatement = $"DeallocStatement ({Addr.ToFStarLang(0)})";
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, deallocStatement, ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Addr.AllChildren())
                yield return node;
            yield return Addr;
        }
    }

    // This node is not in grammar, but generated during resolution to better handle corner cases
    public class UnconditionalJumpStatement : Statement
    {
        public UnconditionalJumpStatement(Token tok, string nextPC)
        : base(tok)
        {
            SetNextProgramCounter(nextPC);
        }

        public override string ToString(int indentation, bool labelOn)
        {
            return new string(' ', indentation) + "UnconditionalJump";
        }

        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        { }
        public override void SetProgramCounter(string parentPC, int index)
        {
            this.PC = $"{parentPC}.{index}";
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }
        public override string ToFStarLang(int indentation)
        {
            FStarStmts.Add(new FStarStmt(PC, NextPC, StartsAtomicBlock, EndsAtomicBlock, "UnconditionalJumpStatement", this.ToString(0, false)));
            return String.Join(";\n", FStarStmts.ConvertAll(stmt => stmt.GetFStarCodeOfStatement(indentation)));
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }
}
