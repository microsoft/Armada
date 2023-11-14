using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Starmada
{
    public abstract class Expr : AstNode
    {
        // TODO: Token class variable
        public Expr(Token tok) : base(tok)
        {
            Contract.Requires(tok != null);
        }

        public Type Ty;

        // public override string ToString(int indentation, bool labelOn) {
        //     string str = "";
        //     string indentationStr = new string(' ', indentation);
        //     str = str + indentationStr + "undefined expr";
        //     return str;
        // }

        // Setting Program Counter for Expressions is generic
        public override void SetProgramCounter(string parentPC, int index)
        {
            // TODO: Implement this function
            this.PC = parentPC;
        }
        public override void SetNextProgramCounter(string nextPC)
        {
            this.NextPC = nextPC;
        }

        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }

        public abstract string ToFStarExpr(string armadaStateName);

        public void CheckCompatiblity(Type enforcingType, ref Errors errors) {
            if (enforcingType != null)
            {   
                if (!(this.Ty.CompatibleType(enforcingType))) {
                    errors.SemErr(FirstTok, $"Type checking fails: expected: {enforcingType.ToString(0)}, got: {this.Ty.ToString(0)}.");
                }
                this.Ty = enforcingType;
            }
        }
    }

    public interface FStarExpressionConstant
    {
        string ToFStarObjectValue();
    }

    public class ConstantExpr : Expr, FStarExpressionConstant
    {
        Ident Value;
        public ConstantExpr(Token tok, Ident value)
        : base(tok)
        {
            this.Value = value;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Value.ToString(0, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Contract.Requires(this.Ty != null);
            Contract.Requires(Value.Ty is PredefinedType);
            Contract.Requires(enforcingType == null || enforcingType is PredefinedType);

            var pdt = Value.Ty as PredefinedType;
            if (enforcingType == null)
            {
                this.Ty = Value.Ty;
                if (Value.FirstTok.val.StartsWith("-") && pdt.IsBoundedInt())
                {
                    if ((pdt.Kind == PredefinedTypeEnum.UInt64) ||
                        (pdt.Kind == PredefinedTypeEnum.UInt32))
                    {
                        errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} is both negative and unsigned! " +
                                    $"It will be casted to {this.Ty.ToString(0)}");
                    }
                }
            }
            else
            {
                var enforcingPred = enforcingType as PredefinedType;
                if (enforcingPred.IsBoundedInt())
                {
                    this.Ty = enforcingType;
                    switch (enforcingPred.Kind)
                    {
                        case PredefinedTypeEnum.Int8:
                            if (!Value.FitsInInt8())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in int8!");
                            }
                            break;
                        case PredefinedTypeEnum.Int16:
                            if (!Value.FitsInInt16())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in int16!");
                            }
                            break;
                        case PredefinedTypeEnum.Int32:
                            if (!Value.FitsInInt32())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in int32!");
                            }
                            break;
                        case PredefinedTypeEnum.Int64:
                            if (!Value.FitsInInt64())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in int64!");
                            }
                            break;
                        case PredefinedTypeEnum.UInt8:
                            if (!Value.FitsInUInt8())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in uint8!");
                            }
                            if (Value.FirstTok.val.StartsWith("-"))
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} is both negative and unsigned! " +
                                    $"It will be casted to {this.Ty.ToString(0)}");
                            }
                            break;
                        case PredefinedTypeEnum.UInt16:
                            if (!Value.FitsInUInt16())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in uint16!");
                            }
                            if (Value.FirstTok.val.StartsWith("-"))
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} is both negative and unsigned! " +
                                    $"It will be casted to {this.Ty.ToString(0)}");
                            }
                            break;
                        case PredefinedTypeEnum.UInt32:
                            if (!Value.FitsInUInt32())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in uint32!");
                            }
                            if (Value.FirstTok.val.StartsWith("-"))
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} is both negative and unsigned! " +
                                    $"It will be casted to {this.Ty.ToString(0)}");
                            }
                            break;
                        case PredefinedTypeEnum.UInt64:
                            if (!Value.FitsInUInt64())
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} doesn't fit in uint64!");
                            }
                            if (Value.FirstTok.val.StartsWith("-"))
                            {
                                errors.Warning(Value.FirstTok,
                                    $"{Value.FirstTok.val} is both negative and unsigned! " +
                                    $"It will be casted to {this.Ty.ToString(0)}");
                            }
                            break;
                        default:
                            errors.SemErr(Value.FirstTok, "unsupported type!");
                            break;
                    }
                }
                else if (enforcingPred.Kind == PredefinedTypeEnum.Int || enforcingPred.Kind == PredefinedTypeEnum.Nat) {
                    this.Ty = enforcingType;
                }
                else if (enforcingPred.Kind == PredefinedTypeEnum.ThreadId) {
                    if (!Value.FitsInUInt32())
                    {
                        errors.SemErr(Value.FirstTok,
                            $"{Value.FirstTok.val} is not a valid thread id!");
                    }
                    this.Ty = enforcingType;
                }
                else {
                    errors.SemErr(Value.FirstTok, $"Unsupported type {enforcingType.ToString(0)}");
                }
            }
        }

        public string ToFStarObjectValue()
        {
            string str = "";
            if (this.Ty is PredefinedType)
            {
                var pt = this.Ty as PredefinedType;
                if (pt.IsBoundedInt())
                {
                    str += $"ObjectValuePrimitive (PrimitiveBoxBoundedInt {Ty.ToFStarLang(0, false)} ({Value.ToString(0, false)}))";
                }
                else
                {
                    str += "ObjectValueAbstract " + Ty.ToFStarLang(0, false) + " (" + Value.ToString(0, false) + ")";
                }
            }
            else
            {
                throw new NotImplementedException();
            }
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "ExpressionConstant (" + ToFStarObjectValue() + ")";
            return str;
        }

        public override string ToFStarExpr(string armadaStateName)
        {
            if (armadaStateName == "") {
                return ToString(0, false);
            } else {
                return $"RootGlobal (ObjectStorageAbstract {Ty.ToFStarLang(0, false)} ( {Value.ToString(0, false)} ))";
            }
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Value;
        }
    }

    public class Attribute : AstNode
    {
        public Ident Name;
        public List<Expr> Exprs;

        public Attribute(Token tok, Ident name, List<Expr> exprs)
        : base(tok)
        {
            Contract.Requires(name != null);
            Contract.Requires(exprs != null);
            Name = name;
            Exprs = exprs;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + "{: " + Name.ToString(0, labelOn) + " " + Util.ListExprsToString(Exprs, labelOn) + "}";
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
            yield return Name;
            foreach (var expr in Exprs)
            {
                foreach (var node in expr.AllChildren())
                    yield return node;
                yield return expr;
            }
        }
    }

    public class WildcardExpr : Expr
    {
        public WildcardExpr(Token tok) : base(tok)
        {
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string indentationStr = new string(' ', indentation);
            return indentationStr + "*";
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotImplementedException();
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = enforcingType;
            return;
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class UnaryExpr : Expr
    {
        public Expr operand;
        public Opcode opcode;
        public bool lvalue;
        public UnaryExpr(Token tok, Expr operand, Opcode op, bool lvalue = false)
        : base(tok)
        {
            this.operand = operand;
            this.opcode = op;
            this.lvalue = lvalue;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (opcode == Opcode.Cardinality)
            {
                str = str + indentationStr + "|" + this.operand.ToString(0, labelOn) + "|";
            }
            else
            {
                str = str + indentationStr + OpcodeToString.OpToStr(opcode) + this.operand.ToString(0, labelOn);
            }
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            if (opcode == Opcode.Cardinality)
            {
                throw new NotSupportedException();
            }
            return ToString(indentation, false);
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: check compatibility according to opcode and deal with enforcing type.
            operand.Sc = Sc;
            switch (opcode)
            {
                case Opcode.Neg:
                case Opcode.BitwiseNot:
                    // TODO: operand should be numbers
                    operand.TypeResolve(enforcingType, ref errors);
                    this.Ty = operand.Ty;
                    if (Ty is PredefinedType)
                    {
                        var pt = (Ty as PredefinedType);
                        if (pt.Kind == PredefinedTypeEnum.Bool 
                            || pt.Kind == PredefinedTypeEnum.ThreadId
                            || pt.Kind == PredefinedTypeEnum.Char
                            || pt.Kind == PredefinedTypeEnum.String)
                        {
                            errors.SemErr(operand.FirstTok, $"{operand.FirstTok.val} cannot be negated.");
                            return;
                        }
                    }
                    break;
                case Opcode.Not:
                    operand.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
                    this.Ty = operand.Ty;
                    break;
                case Opcode.AddressOf:
                    operand.TypeResolve(null, ref errors);
                    this.Ty = new PointerType(operand.Ty);
                    break;
                case Opcode.Dereference:
                    operand.TypeResolve(null, ref errors);
                    PointerType ty = (PointerType)operand.Ty;
                    if (ty == null)
                    {
                        errors.SemErr(operand.FirstTok, $"{operand.FirstTok.val} is not a pointer.");
                        return;
                    }
                    this.Ty = ty.EntityType;
                    break;
                case Opcode.Allocated:
                case Opcode.AllocatedArray:
                    operand.TypeResolve(null, ref errors);
                    ty = (PointerType)operand.Ty;
                    if (ty == null)
                    {
                        errors.SemErr(operand.FirstTok, $"{operand.FirstTok.val} is not a pointer.");
                    }
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                case Opcode.GlobalView:
                    operand.TypeResolve(enforcingType, ref errors);
                    this.Ty = operand.Ty;
                    break;
                case Opcode.Cardinality:
                    operand.TypeResolve(null, ref errors);
                    if (!(operand.Ty is CollectionType))
                    {
                        errors.SemErr(operand.FirstTok, $"{operand.FirstTok.val} is not of a collection type.");
                    }
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Nat);
                    // TODO: check compatibility
                    break;
                default: throw new NotImplementedException();
            }
            CheckCompatiblity(enforcingType, ref errors);
        }
        public override string ToFStarLang(int indentation)
        {
            string opcodeFStar = "";
            string prefix = "Armada.UnaryOp.UnaryOp";
            bool bounded = false;
            if (operand.Ty is PredefinedType && (operand.Ty as PredefinedType).IsBoundedInt())
            {
                bounded = true;
            }
            switch (opcode)
            {
                case Opcode.Neg: opcodeFStar = prefix + (bounded ? $"BoundedNeg {operand.Ty.ToFStarLang(0, false)}" : "Neg"); break;
                case Opcode.BitwiseNot: 
                    if (!bounded) {
                        throw new NotSupportedException("bitwise operation for unbounded values not supported");
                    }
                    opcodeFStar = prefix + $"BitwiseNot {operand.Ty.ToFStarLang(0, false)}";
                    break;
                case Opcode.Not: opcodeFStar = prefix + (bounded ? $"BoundedNot {operand.Ty.ToFStarLang(0, false)}" : "Not"); break;
                case Opcode.AddressOf: return new string(' ', indentation) + $"ExpressionAddressOf ({operand.ToFStarLang(0)})";
                case Opcode.Dereference: return new string(' ', indentation) + $"ExpressionDereference ({operand.Ty.ToFStarLang(0, true)}) ({operand.ToFStarLang(0)})";
                // case Opcode.Allocated: opcodeFStar = prefix + (bounded ? $"BoundedMod {firstOp.Ty.ToFStarLang(0, false)}" : "ModInt"); break;
                // case Opcode.AllocatedArray: opcodeFStar = prefix + "LeftShift"; break;
                // case Opcode.GlobalView: opcodeFStar = prefix + "RightShift"; break;
                case Opcode.Cardinality:
                    string fn = "";
                    if (operand.Ty is SeqType)
                    {
                        fn += "seq_cardinality";
                    }
                    else if (operand.Ty is SetType)
                    {
                        fn += (operand.Ty as SetType).IsInfinite ? "set_cardinality" : "finiteset_cardinality";
                    }
                    else if (operand.Ty is MapType)
                    {
                        fn += (operand.Ty as MapType).IsInfinite ? "map_cardinality" : "finitemap_cardinality";
                    }
                    else
                    {
                        throw new NotImplementedException();
                    }
                    return new string(' ', indentation) + $"ExpressionApplyFunction (ObjectTDAbstract nat) [{operand.ToFStarLang(0)}] nat [{operand.Ty.ToFStarLang(0, false)}] {fn}";
                default: throw new NotImplementedException();
            }
            // return "";
            return new string(' ', indentation) + $"ExpressionUnaryOperator ({operand.Ty.ToFStarLang(0, true)}) ({Ty.ToFStarLang(0, true)}) ({opcodeFStar}) ({operand.ToFStarLang(0)})";

        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in operand.AllChildren())
                yield return node;
            yield return operand;
        }
    }


    public class BinaryExpr : Expr
    {
        public Expr firstOp;
        public Expr secondOp;
        public Opcode opcode;
        public bool lvalue;
        public BinaryExpr(Token tok, Expr firstOp, Expr secondOp = null, Opcode op = Opcode.Add, bool lvalue = false)
        : base(tok)
        {
            this.firstOp = firstOp;
            this.secondOp = secondOp;
            this.opcode = op;
            this.lvalue = lvalue;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + this.firstOp.ToString(0, labelOn); ;
            if (opcode == Opcode.Dot)
            {
                str = str + OpcodeToString.OpToStr(opcode);
            }
            else
            {
                str = str + " " + OpcodeToString.OpToStr(opcode) + " ";
            }
            str = str + this.secondOp.ToString(0, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            firstOp.Sc = Sc;
            secondOp.Sc = Sc;
            switch (opcode)
            {
                case Opcode.Add:
                    firstOp.TypeResolve(enforcingType, ref errors);
                    if (firstOp.Ty is PointerType) {
                        secondOp.TypeResolve(new PredefinedType(PredefinedTypeEnum.Int), ref errors);
                    }
                    else {
                        secondOp.TypeResolve(firstOp.Ty, ref errors);
                    }
                    this.Ty = firstOp.Ty;
                    break;
                case Opcode.Sub:
                case Opcode.Div:
                    firstOp.TypeResolve(enforcingType, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = enforcingType;
                    break;
                case Opcode.Mul: // TODO: first bouned multiplication type checking
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    if (enforcingType != null) {
                        this.Ty = enforcingType;
                    }
                    else {
                        this.Ty = firstOp.Ty;
                    }
                    return;
                case Opcode.Mod:
                    firstOp.TypeResolve(enforcingType, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = firstOp.Ty;
                    break;
                case Opcode.LeftShift:
                case Opcode.RightShift:
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
                    this.Ty = firstOp.Ty;
                    break;
                case Opcode.Equal:
                case Opcode.NotEqual:
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                case Opcode.Lt:
                case Opcode.Le:
                case Opcode.Gt:
                case Opcode.Ge:
                    // Lt, Le, Gt, Ge support Int, BoundedInt, Pointer
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                case Opcode.In:
                case Opcode.NotIn:
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(null, ref errors);
                    if (!(secondOp.Ty is CollectionType))
                    {
                        errors.SemErr(secondOp.FirstTok, $"{secondOp.FirstTok.val} is not of a collection type.");
                    }
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                case Opcode.Disjoint:
                    firstOp.TypeResolve(null, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    if (!(secondOp.Ty is SetType))
                    {
                        errors.SemErr(secondOp.FirstTok, $"{secondOp.FirstTok.val} is not of a set type.");
                    }
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                case Opcode.And:
                case Opcode.Or:
                    firstOp.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = secondOp.Ty;
                    break;
                case Opcode.BitwiseAnd:
                case Opcode.BitwiseOr:
                case Opcode.BitwiseXor:
                    firstOp.TypeResolve(enforcingType, ref errors);
                    secondOp.TypeResolve(firstOp.Ty, ref errors);
                    this.Ty = secondOp.Ty;
                    break;
                case Opcode.Dot:
                    firstOp.TypeResolve(null, ref errors);
                    if (firstOp.Ty is not UserDefinedType)
                    {
                        errors.SemErr(firstOp.FirstTok, $"Datatype {firstOp.ToString(0, false)} not found.");
                    }
                    string name = (firstOp.Ty as UserDefinedType).Name.Name;
                    StructDecl structDecl = Sc.GetStructDecl(name);
                    DatatypeDecl datatypeDecl = Sc.GetDatatypeDecl(name);
                    if (structDecl == null && datatypeDecl == null)
                    {
                        errors.SemErr(firstOp.FirstTok, $"Datatype {name} not found.");
                    }
                    if (secondOp is not Ident)
                    {
                        errors.SemErr(secondOp.FirstTok, $"{secondOp.FirstTok.val} is not a valid field.");
                    }
                    string fieldName = (secondOp as Ident).Name;
                    if (datatypeDecl != null && datatypeDecl.GetFunctionInvocation(fieldName, "") == null)
                    {
                        errors.SemErr(secondOp.FirstTok, $"{fieldName} is not a valid field.");
                    }
                    if (structDecl != null)
                    {
                        var fieldDecl = structDecl.GetField(fieldName);
                        if (fieldDecl == null)
                        {
                            errors.SemErr(secondOp.FirstTok, $"{fieldName} is not a valid field.");
                        }
                        this.Ty = fieldDecl.Ty;
                    }
                    // TODO: check secondOp is valid?
                    break;
                case Opcode.Equiv:
                case Opcode.Imply:
                case Opcode.Exply:
                    firstOp.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
                    secondOp.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
                    this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
                    break;
                default: break;
            }
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            switch (opcode)
            {
                case Opcode.Equiv:
                case Opcode.Imply:
                case Opcode.Exply:
                case Opcode.Disjoint:
                case Opcode.In:
                case Opcode.NotIn:
                    throw new NotSupportedException();
                default:
                    break;
            }
            return ToString(indentation, false);
        }
        public override string ToFStarLang(int indentation)
        {
            string opcodeFStar = "";
            string prefix = "Armada.BinaryOp.BinaryOp";
            bool bounded = false;
            bool pointer = false;
            if (firstOp.Ty is PredefinedType && (firstOp.Ty as PredefinedType).IsBoundedInt() &&
                secondOp.Ty is PredefinedType && (secondOp.Ty as PredefinedType).IsBoundedInt())
            {
                bounded = true;
            }
            if (firstOp.Ty is PointerType && secondOp.Ty is PointerType)
            {
                pointer = true;
            }
            switch (opcode)
            {
                case Opcode.Add:
                    if (firstOp.Ty is PointerType) {
                        return $"(ExpressionPointerOffset ({firstOp.ToFStarLang(0)}) ({secondOp.ToFStarLang(0)}))";
                    }
                    else {
                        opcodeFStar = prefix + (bounded ? $"BoundedAdd {firstOp.Ty.ToFStarLang(0, false)}" : "AddInt");
                    }
                    break;
                case Opcode.Sub: opcodeFStar = prefix + (bounded ? $"BoundedSub {firstOp.Ty.ToFStarLang(0, false)}" : "SubInt"); break;
                case Opcode.Mul: opcodeFStar = prefix + (bounded ? $"BoundedMul {firstOp.Ty.ToFStarLang(0, false)}" : "MulInt"); break;
                case Opcode.Div: opcodeFStar = prefix + (bounded ? $"BoundedDiv {firstOp.Ty.ToFStarLang(0, false)}" : "DivInt"); break;
                case Opcode.Mod: opcodeFStar = prefix + (bounded ? $"BoundedMod {firstOp.Ty.ToFStarLang(0, false)}" : "ModInt"); break;
                case Opcode.LeftShift: 
                    if (firstOp.Ty is PredefinedType && (firstOp.Ty as PredefinedType).IsBoundedInt()) {
                        opcodeFStar = prefix + $"BitwiseLeftShift {firstOp.Ty.ToFStarLang(0, false)}";
                    }
                    else {
                        opcodeFStar = prefix + $"LeftShift";
                    }
                    break;
                case Opcode.RightShift: 
                if (firstOp.Ty is PredefinedType && (firstOp.Ty as PredefinedType).IsBoundedInt()) {
                        opcodeFStar = prefix + $"BitwiseRightShift {firstOp.Ty.ToFStarLang(0, false)}";
                    }
                    else {
                        opcodeFStar = prefix + $"RightShift";
                    }
                break;
                case Opcode.Equal:
                    opcodeFStar = $"{prefix}Eq ({firstOp.Ty.ToFStarLang(0, true)})";
                    break;
                case Opcode.NotEqual:
                    opcodeFStar = $"{prefix}Neq ({firstOp.Ty.ToFStarLang(0, true)})";
                    break;
                case Opcode.Lt: opcodeFStar = prefix + (pointer ? "PtrLt" : (bounded ? $"BoundedLt {firstOp.Ty.ToFStarLang(0, false)}" : "LtInt")); break;
                case Opcode.Le: opcodeFStar = prefix + (pointer ? "PtrLe" : (bounded ? $"BoundedLe {firstOp.Ty.ToFStarLang(0, false)}" : "LeInt")); break;
                case Opcode.Gt: opcodeFStar = prefix + (pointer ? "PtrGt" : (bounded ? $"BoundedGt {firstOp.Ty.ToFStarLang(0, false)}" : "GtInt")); break;
                case Opcode.Ge: opcodeFStar = prefix + (pointer ? "PtrGe" : (bounded ? $"BoundedGe {firstOp.Ty.ToFStarLang(0, false)}" : "GeInt")); break;
                case Opcode.In:
                case Opcode.NotIn:
                    string fn = (opcode == Opcode.NotIn) ? "not_" : "";
                    if (secondOp.Ty is SeqType)
                    {
                        fn += "seq_contains";
                    }
                    else if (secondOp.Ty is SetType)
                    {
                        fn += (secondOp.Ty as SetType).IsInfinite ? "set_contains" : "finite_set_contains";
                    }
                    else if (secondOp.Ty is MapType)
                    {
                        fn += (secondOp.Ty as MapType).IsInfinite ? "map_contains" : "finite_map_contains";
                    }
                    else
                    {
                        throw new NotImplementedException();
                    }
                    return new string(' ', indentation) + $"ExpressionApplyFunction (ObjectTDPrimitive PrimitiveTDBool) [{firstOp.ToFStarLang(0)}; {secondOp.ToFStarLang(0)}] bool [{firstOp.Ty.ToFStarLang(0, false)}; {secondOp.Ty.ToFStarLang(0, false)}] {fn}";
                case Opcode.Disjoint:
                    string disjoint_fn = (firstOp.Ty as SetType).IsInfinite ? "set_disjoint" : "finiteset_disjoint";
                    return new string(' ', indentation) + $"ExpressionApplyFunction (ObjectTDPrimitive PrimitiveTDBool) [{firstOp.ToFStarLang(0)}; {secondOp.ToFStarLang(0)}] bool [{firstOp.Ty.ToFStarLang(0, false)}; {secondOp.Ty.ToFStarLang(0, false)}] {disjoint_fn}";
                case Opcode.And: opcodeFStar = prefix + "And"; break;
                case Opcode.Or: opcodeFStar = prefix + "Or"; break;
                // The Bitwise operators are not supported
                case Opcode.BitwiseAnd: 
                    if (!bounded) {
                        throw new NotSupportedException("bitwise operation for unbounded values not supported");
                    }
                    opcodeFStar = prefix + $"BitwiseAnd {firstOp.Ty.ToFStarLang(0, false)}";
                    break;
                case Opcode.BitwiseOr: 
                    if (!bounded) {
                        throw new NotSupportedException("bitwise operation for unbounded values not supported");
                    }
                    opcodeFStar = prefix + $"BitwiseOr {firstOp.Ty.ToFStarLang(0, false)}";
                    break;
                case Opcode.BitwiseXor: 
                    if (!bounded) {
                        throw new NotSupportedException("bitwise operation for unbounded values not supported");
                    }
                    opcodeFStar = prefix + $"BitwiseXor {firstOp.Ty.ToFStarLang(0, false)}";
                    break;
                case Opcode.Dot:
                    string name = (firstOp.Ty as UserDefinedType).Name.Name;
                    StructDecl structDecl = Sc.GetStructDecl(name);
                    DatatypeDecl datatypeDecl = Sc.GetDatatypeDecl(name);
                    string fieldName = (secondOp as Ident).Name;
                    if (datatypeDecl != null)
                    {
                        return datatypeDecl.GetFunctionInvocation(fieldName, firstOp.ToFStarLang(0));
                    }
                    else if (structDecl != null)
                    {
                        if (firstOp.ToString(0, false) == "$state")
                        {
                            if (secondOp.ToString(0, false) == "initial_tid")
                            {
                                return "ExpressionInitialTid";
                            }
                            else if (secondOp.ToString(0, false) == "uniqs_used")
                            {
                                return "ExpressionUniqsUsed";
                            }
                            else if (secondOp.ToString(0, false) == "stop_reason")
                            {
                                return "ExpressionStopReason";
                            }
                            else
                            {
                                throw new NotSupportedException();
                            }
                        }
                        return structDecl.GetFieldAccessInFStar(fieldName, firstOp.ToFStarLang(0));
                    }
                    break;
                case Opcode.Equiv: opcodeFStar = prefix + "Equiv"; break;
                case Opcode.Imply: opcodeFStar = prefix + "Imply"; break;
                case Opcode.Exply: opcodeFStar = prefix + "Exply"; break;
                default: throw new NotImplementedException();
            }
            return new string(' ', indentation) + $"ExpressionBinaryOperator ({firstOp.Ty.ToFStarLang(0, true)}) ({secondOp.Ty.ToFStarLang(0, true)}) ({Ty.ToFStarLang(0, true)}) ({opcodeFStar}) ({firstOp.ToFStarLang(0)}) ({secondOp.ToFStarLang(0)})";
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            string op1 = $"{firstOp.ToFStarExpr(armadaStateName)}";
            string op2 = $"{secondOp.ToFStarExpr(armadaStateName)}";
            switch (opcode)
            {
                case Opcode.Add:
                    return $"({op1}) + ({op2})";
                case Opcode.Sub:
                    return $"({op1}) - ({op2})";
                case Opcode.Mul:
                    return $"op_Multiply ({op1}) ({op2})";
                case Opcode.Div: throw new NotImplementedException();
                case Opcode.Mod: throw new NotImplementedException();
                case Opcode.LeftShift: throw new NotImplementedException();
                case Opcode.RightShift: throw new NotImplementedException();
                case Opcode.Equal:
                    return $"({op1}) == ({op2})";
                case Opcode.NotEqual: throw new NotImplementedException();
                case Opcode.Lt: throw new NotImplementedException();
                case Opcode.Le: throw new NotImplementedException();
                case Opcode.Gt: throw new NotImplementedException();
                case Opcode.Ge: throw new NotImplementedException();
                case Opcode.In:
                    if (secondOp.Ty is SeqType)
                    {
                        return $"contains ({op2}) ({op1})";
                    }
                    else if (secondOp.Ty is SetType)
                    {
                        return (secondOp.Ty as SetType).IsInfinite ? $"FStar.Set.mem ({op1}) ({op2})" : $"FStar.FiniteSet.Base.mem ({op1}) ({op2})";
                    }
                    else if (secondOp.Ty is MapType)
                    {
                        return (secondOp.Ty as MapType).IsInfinite ? $"FStar.Map.contains ({op2}) ({op1})" : $"FStar.FiniteMap.Base.mem ({op1}) ({op2})";
                    }
                    else
                    {
                        throw new NotImplementedException();
                    }
                case Opcode.NotIn: throw new NotImplementedException();
                case Opcode.Disjoint: throw new NotImplementedException();
                case Opcode.And: throw new NotImplementedException();
                case Opcode.Or: throw new NotImplementedException();
                case Opcode.BitwiseAnd: throw new NotImplementedException();
                case Opcode.BitwiseOr: throw new NotImplementedException();
                case Opcode.BitwiseXor: throw new NotImplementedException();
                case Opcode.Dot: throw new NotImplementedException();
                case Opcode.Equiv: throw new NotImplementedException();
                case Opcode.Imply: throw new NotImplementedException();
                case Opcode.Exply: throw new NotImplementedException();
                default: throw new NotImplementedException();
            }
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in firstOp.AllChildren())
                yield return node;
            yield return firstOp;
            foreach (var node in secondOp.AllChildren())
                yield return node;
            yield return secondOp;
        }
    }

    public class IfExpr : Expr
    {
        public Expr Cond;
        public Expr ThenExpr;
        public Expr ElseExpr;
        public IfExpr(Token tok, Expr cond, Expr thenExpr, Expr elseExpr)
        : base(tok)
        {
            Contract.Requires(cond != null);
            Contract.Requires(thenExpr != null);
            Contract.Requires(elseExpr != null);
            this.Cond = cond;
            this.ThenExpr = thenExpr;
            this.ElseExpr = elseExpr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "if " + Cond.ToString(0, labelOn) +
                  " then " + ThenExpr.ToString(0, labelOn) + " else " + ElseExpr.ToString(0, labelOn);
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "(" + Cond.ToCProgram(0) + ") ? "
                  + ThenExpr.ToCProgram(indentation + 2) + " : "
                  + ElseExpr.ToCProgram(indentation + 2);
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Cond.Sc = Sc;
            ThenExpr.Sc = Sc;
            ElseExpr.Sc = Sc;
            Cond.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            ThenExpr.TypeResolve(enforcingType, ref errors);
            ElseExpr.TypeResolve(ThenExpr.Ty, ref errors);
            this.Ty = ElseExpr.Ty;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += $"ExpressionIf ({ThenExpr.Ty.ToFStarLang(0, true)}) ({Cond.ToFStarLang(0)}) ({ThenExpr.ToFStarLang(0)}) ({ElseExpr.ToFStarLang(0)})";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Cond.AllChildren())
                yield return node;
            yield return Cond;
            foreach (var node in ThenExpr.AllChildren())
                yield return node;
            yield return ThenExpr;
            foreach (var node in ElseExpr.AllChildren())
                yield return node;
            yield return ElseExpr;
        }
    }

    public class LiteralExpr : Expr, FStarExpressionConstant
    {
        public readonly object Value;

        public LiteralExpr(Token tok)
        : base(tok)
        {
            this.Value = null;
        }

        public LiteralExpr(Token tok, bool b)
        : base(tok)
        {
            this.Value = b;
        }

        public LiteralExpr(Token tok, int n)
        : base(tok)
        {
            this.Value = n;
        }

        // This constructor is used by CharLiteralExpr and StringLiteralExpr
        protected LiteralExpr(Token tok, string s)
        : base(tok)
        {
            Contract.Requires(s != null);
            this.Value = s;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (Value == null) {
                str = str + indentationStr + "null";
            }
            else {
                string valueStr = (Value is bool) ? Value.ToString().ToLower() : Value.ToString();
                str = str + indentationStr + valueStr;
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (Value == null)
            {
                Contract.Assert(enforcingType is PointerType);
                this.Ty = enforcingType;
            }
            else if (Value is int)
            {
                this.Ty = new PredefinedType(PredefinedTypeEnum.Int);
            }
            else if (Value is bool)
            {
                this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
            }
            CheckCompatiblity(enforcingType, ref errors);
        }
        public string ToFStarObjectValue()
        {
            if (Value is bool)
            {
                return $"ObjectValuePrimitive (PrimitiveBoxBool {ToString(0, false)})";
            }
            return "ObjectValueAbstract " + Ty.ToString(0) + " " + ToString(0, false);
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "ExpressionConstant (" + ToFStarObjectValue() + ")";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            return ToString(0, false);
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class CharLiteralExpr : LiteralExpr
    {
        public CharLiteralExpr(Token tok, string s)
        : base(tok, s)
        { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "'" + this.Value.ToString() + "'";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = new PredefinedType(PredefinedTypeEnum.Char);
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class StringLiteralExpr : LiteralExpr
    {
        public readonly bool IsVerbatim;

        public StringLiteralExpr(Token tok, string s, bool isVerbatim)
        : base(tok, s)
        {
            this.IsVerbatim = isVerbatim;
        }
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "\"" + this.Value.ToString() + "\"";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = new PredefinedType(PredefinedTypeEnum.String);
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class NullPointerExpr : Expr
    {
        public NullPointerExpr(Token tok)
        : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "null";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = enforcingType;
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            return ToString(indentation, false);
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"ExpressionConstant (ObjectValuePrimitive (PrimitiveBoxPointer PointerNull))";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class MeExpr : Expr
    {
        public MeExpr(Token tok)
        : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "$me";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = new PredefinedType(PredefinedTypeEnum.ThreadId);
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class StoreBufferEmptyExpr : Expr
    {
        public StoreBufferEmptyExpr(Token tok)
        : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "$sb_empty";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class IfUndefinedExpr : Expr
    {
        public Expr PotentiallyUnsafe, SafeSubstitution;

        public IfUndefinedExpr(Token tok, Expr potentiallyUnsafe, Expr safeSubstitution)
        : base(tok)
        {
            this.PotentiallyUnsafe = potentiallyUnsafe;
            this.SafeSubstitution = safeSubstitution;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "if_undefined (" +
                  PotentiallyUnsafe.ToString(0, labelOn) + ", " + SafeSubstitution.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // The type for PotentiallyUnsafe and SafeSubstitution should be the same
            PotentiallyUnsafe.Sc = Sc;
            SafeSubstitution.Sc = Sc;
            PotentiallyUnsafe.TypeResolve(enforcingType, ref errors);
            SafeSubstitution.TypeResolve(enforcingType, ref errors);
            this.Ty = SafeSubstitution.Ty;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"ExpressionIfUndefined ({this.Ty.ToFStarLang(0, true)}) ({PotentiallyUnsafe.ToFStarLang(0)}) ({SafeSubstitution.ToFStarLang(0)})";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in PotentiallyUnsafe.AllChildren())
                yield return node;
            yield return PotentiallyUnsafe;
            foreach (var node in SafeSubstitution.AllChildren())
                yield return node;
            yield return SafeSubstitution;
        }
    }

    public class MapDisplayExpr : Expr
    {
        public bool Finite;
        public Dictionary<Expr, Expr> Elements;

        public MapDisplayExpr(Token tok, bool finite, Dictionary<Expr, Expr> elements)
        : base(tok)
        {
            // Contract.Requires(cce.NonNullElements(elements));
            Finite = finite;
            Elements = elements;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            List<string> elementsStr = new List<string>();
            foreach (var kv in Elements)
            {
                elementsStr.Add(kv.Key.ToString(0, labelOn) + ":=" + kv.Value.ToString(0, labelOn));
            }
            str = str + indentationStr + FirstTok.val + " [" + string.Join(", ", elementsStr) + "]";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type prevElementKeyType = null;
            Type prevElementValueType = null;
            if (enforcingType != null)
            {
                if (enforcingType is not MapType)
                {
                    errors.SemErr(FirstTok, $"Cannot convert {this.ToString(0, false)} to non-map type.");
                }
                MapType enforcingMapType = (enforcingType as MapType);
                if (enforcingMapType.IsInfinite == Finite)
                {
                    errors.SemErr(FirstTok, $"The finite of map does not match.");
                }
                prevElementKeyType = enforcingMapType.KeyType;
                prevElementValueType = enforcingMapType.EntityType;
            }
            foreach (var kv in Elements)
            {
                kv.Key.Sc = Sc;
                kv.Value.Sc = Sc;
                kv.Key.TypeResolve(prevElementKeyType, ref errors);
                prevElementKeyType = kv.Key.Ty;
                kv.Value.TypeResolve(prevElementValueType, ref errors);
                prevElementValueType = kv.Value.Ty;
            }
            this.Ty = new MapType(prevElementKeyType, prevElementValueType, !Finite);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            string emptyStr = Finite ? "FStar.FiniteMap.Base.emptymap" : "(FStar.Map.const 0)";
            string expressionStr = $"ExpressionConstant (ObjectValueAbstract ({this.Ty.ToFStarLang(0, false)}) {emptyStr})";
            Type keyTy = (this.Ty as MapType).KeyType;
            Type valueTy = (this.Ty as MapType).EntityType;
            if (Elements.Count > 0)
            {
                foreach (var kv in Elements)
                {
                    var key = kv.Key;
                    var value = kv.Value;
                    string insertStr = Finite ? "finite_map_insert" : "map_insert";
                    expressionStr = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{expressionStr}; {key.ToFStarLang(0)}; {value.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{this.Ty.ToFStarLang(0, false)}; {keyTy.ToFStarLang(0, false)}; {valueTy.ToFStarLang(0, false)}] {insertStr}";
                }
            }
            str += expressionStr;
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (KeyValuePair<Expr, Expr> entry in Elements)
            {
                foreach (var node in entry.Key.AllChildren())
                    yield return node;
                yield return entry.Key;
                foreach (var node in entry.Value.AllChildren())
                    yield return node;
                yield return entry.Value;
            }
        }
    }

    public abstract class DisplayExpr : Expr
    {
        public readonly List<Expr> Elements;

        public DisplayExpr(Token tok, List<Expr> elements)
        : base(tok)
        {
            // Contract.Requires(cce.NonNullElements(elements));
            Elements = elements;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            List<string> elementsStr = new List<string>();
            foreach (Expr expr in Elements)
            {
                elementsStr.Add(expr.ToString(0, labelOn));
            }
            str = str + indentationStr + string.Join(", ", elementsStr);
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var element in Elements)
            {
                foreach (var node in element.AllChildren())
                    yield return node;
                yield return element;
            }
        }
    }

    public class SetDisplayExpr : DisplayExpr
    {
        public bool Finite;

        public SetDisplayExpr(Token tok, bool finite, List<Expr> elements)
        : base(tok, elements)
        {
            Finite = finite;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "{" + base.ToString(0, labelOn) + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type prevElementType = null;
            if (enforcingType != null)
            {
                if (enforcingType is not SetType)
                {
                    errors.SemErr(FirstTok, $"Cannot convert {this.ToString(0, false)} to non-set type.");
                }
                SetType enforcingSetType = (enforcingType as SetType);
                if (enforcingSetType.IsInfinite == Finite)
                {
                    errors.SemErr(FirstTok, $"The finite of set does not match.");
                }
                prevElementType = enforcingSetType.EntityType;
            }
            foreach (var element in Elements)
            {
                element.Sc = Sc;
                element.TypeResolve(prevElementType, ref errors);
                prevElementType = element.Ty;
            }
            this.Ty = new SetType(prevElementType, !Finite);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            Type elementTy = (this.Ty as SetType).EntityType;
            string emptyStr = Finite ? "FStar.FiniteSet.Base.emptyset" : "FStar.Set.empty";
            string expressionStr = $"ExpressionConstant (ObjectValueAbstract ({this.Ty.ToFStarLang(0, false)}) {emptyStr})";
            if (!Finite)
            {
                if (Elements.Count > 0)
                {
                    List<string> exprStrs = new List<string>();
                    foreach (var expr in Elements)
                    {
                        exprStrs.Add($"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{expr.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{elementTy.ToFStarLang(0, false)}] set_singleton");
                    }
                    expressionStr = exprStrs[0];
                    for (int i = 1; i < Elements.Count; i++)
                    {
                        expressionStr = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{expressionStr}; {exprStrs[i]}] ({this.Ty.ToFStarLang(0, false)}) [{this.Ty.ToFStarLang(0, false)}; {this.Ty.ToFStarLang(0, false)}] set_union";
                    }
                }
            }
            else
            {
                if (Elements.Count > 0)
                {
                    foreach (var expr in Elements)
                    {
                        expressionStr = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{expr.ToFStarLang(0)}; {expressionStr}] ({this.Ty.ToFStarLang(0, false)}) [{elementTy.ToFStarLang(0, false)}; {this.Ty.ToFStarLang(0, false)}] finite_set_insert";
                    }
                }
            }
            str += expressionStr;
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
        }
    }

    public class SeqDisplayExpr : DisplayExpr
    {
        public SeqDisplayExpr(Token tok, List<Expr> elements)
        : base(tok, elements) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "[" + base.ToString(0, labelOn) + "]";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type prevElementType = null;
            bool checkConstant = false;
            if (enforcingType != null)
            {
                if (enforcingType is SeqType)
                {
                    prevElementType = (enforcingType as SeqType).EntityType;
                    this.Ty = new SeqType(prevElementType);
                }
                else if (enforcingType is TypeSuffix)
                {
                    prevElementType = (enforcingType as TypeSuffix).EntityType;
                    var size = (enforcingType as TypeSuffix).Size;
                    int count = Int32.Parse(size.ToString(0, false));
                    if (count != Elements.Count)
                    {
                        errors.SemErr(FirstTok, $"Array Size mismatch, expected: {count}, got {Elements.Count}.");
                    }
                    this.Ty = new TypeSuffix(prevElementType, size);
                    checkConstant = true;
                }
                else
                {
                    errors.SemErr(FirstTok, $"Cannot convert {this.ToString(0, false)} to non-seq type.");
                }
            }
            foreach (var element in Elements)
            {
                if (checkConstant)
                {
                    if (element is not FStarExpressionConstant)
                    {
                        errors.SemErr(element.FirstTok, $"You must initialize an array with constant values.");
                    }
                }
                element.Sc = Sc;
                element.TypeResolve(prevElementType, ref errors);
                prevElementType = element.Ty;
            }
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }

        public string ToFStarObjectValue()
        {
            if (this.Ty is TypeSuffix)
            {
                Type elementTy = (this.Ty as TypeSuffix).EntityType;
                string expressionStr = "empty";
                if (Elements.Count > 0)
                {
                    foreach (var expr in Elements)
                    {
                        expressionStr = $"build ({expressionStr}) ({(expr as FStarExpressionConstant).ToFStarObjectValue()})";
                    }
                }
                return $"ObjectValueArray ({elementTy.ToFStarLang(0, true)}) ({expressionStr})";
            }
            else
            {
                throw new NotSupportedException();
            }
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            if (this.Ty is SeqType)
            {
                Type elementTy = (this.Ty as SeqType).EntityType;
                string expressionStr = $"ExpressionConstant (ObjectValueAbstract ({this.Ty.ToFStarLang(0, false)}) empty)";
                if (Elements.Count > 0)
                {
                    foreach (var expr in Elements)
                    {
                        expressionStr = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{expressionStr}; {expr.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{this.Ty.ToFStarLang(0, false)}; {elementTy.ToFStarLang(0, false)}] seq_build";
                    }
                }
                str += expressionStr;
            }
            else if (this.Ty is TypeSuffix)
            {
                str += $"ExpressionConstant ({ToFStarObjectValue()})";
            }
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
        }
    }

    // To be deleted
    public class MultiSetDisplayExpr : DisplayExpr
    {
        public MultiSetDisplayExpr(Token tok, List<Expr> elements)
        : base(tok, elements) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "multiset" + "{" + base.ToString(0, labelOn) + "}";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
            Type prevElementType = null;
            foreach (var element in Elements)
            {
                element.Sc = Sc;
                element.TypeResolve(prevElementType, ref errors);
                prevElementType = element.Ty;
            }
            this.Ty = new SetType(prevElementType, false);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
        }
    }

    // To be deleted
    public class MultiSetFormingExpr : Expr
    {
        public readonly Expr Expression;

        public MultiSetFormingExpr(Token tok, Expr expr)
        : base(tok)
        {
            Contract.Requires(expr != null);
            // cce.Owner.AssignSame(this, expr);
            Expression = expr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "multiset" + "(" + Expression.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Expression.Sc = Sc;
            Expression.TypeResolve(null, ref errors);
            if (!(Expression.Ty is CollectionType))
            {
                errors.SemErr(Expression.FirstTok, $"{Expression.FirstTok.val} is not of a collection type.");
            }
            CollectionType ty = (CollectionType)Expression.Ty;
            this.Ty = new SetType(ty.EntityType, false);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Expression.AllChildren())
                yield return node;
            yield return Expression;
        }
    }

    // To be deleted
    public class SeqConstructionExpr : Expr
    {
        public Expr N;
        public Expr Initializer;
        public SeqConstructionExpr(Token tok, Expr length, Expr initializer)
        : base(tok)
        {
            Contract.Requires(length != null);
            Contract.Requires(initializer != null);
            N = length;
            Initializer = initializer;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "seq" + "(" + N.ToString(0, labelOn) + ", " + Initializer.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            N.Sc = Sc;
            Initializer.Sc = Sc;
            N.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
            // TODO: Initializer's type should be enforced to boolean, right?
            // In seq(k, n => n+1), n => n+1 should be boolean.
            // We may need to enforce the type of Initializer to be ImpliesExpression, and
            // set the type of Set to be the same as the type of second operand in ImpliesExpression.
            // potential BUG here.
            Initializer.TypeResolve(null, ref errors);
            this.Ty = new SetType(Initializer.Ty, false);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in N.AllChildren())
                yield return node;
            yield return N;
            foreach (var node in Initializer.AllChildren())
                yield return node;
            yield return Initializer;
        }
    }

    public class ConversionExpr : Expr
    {
        public readonly Expr Expression;
        public readonly Type ToType;

        public ConversionExpr(Token tok, Expr expr, Type toType)
        : base(tok)
        {
            Contract.Requires(expr != null);
            Contract.Requires(toType != null);
            this.Expression = expr;
            this.ToType = toType;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + ToType.ToString(0) + "(" + Expression.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Expression.Sc = Sc;
            Expression.TypeResolve(null, ref errors);
            if (ToType is not PredefinedType || !(ToType as PredefinedType).IsBoundedInt())
            {
                errors.SemErr(FirstTok, "The type should be bounded int type.");
            }
            this.Ty = ToType;
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "(" + ToType.ToString(0) + ")" + Expression.ToCProgram(0);
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"ExpressionUnaryOperator ({Expression.Ty.ToFStarLang(0, true)}) ({Ty.ToFStarLang(0, true)}) (Armada.UnaryOp.UnaryOpCast {Expression.Ty.ToFStarLang(0, false)} {Ty.ToFStarLang(0, false)}) ({Expression.ToFStarLang(0)})";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Expression.AllChildren())
                yield return node;
            yield return Expression;
        }
    }

    // To be deleted
    public class LabelExpr : Expr
    {
        public readonly string Name;
        public readonly Expr Body;

        public LabelExpr(Token tok, string p, Expr body)
        : base(tok)
        {
            Name = p;
            Body = body;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "label " + Name + ": " + Body.ToString(0, labelOn);
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            // TODO: Implement this
            string str = "";
            string indentationStr = new string(' ', indentation);
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Body.Sc = Sc;
            Body.TypeResolve(null, ref errors);
            // TODO: set this.ty
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Body.AllChildren())
                yield return node;
            yield return Body;
        }
    }

    public abstract class QuantifierExpr : Expr
    {
        public List<Ident> Idents;
        public Expr Range;
        public Expr Body;
        public Attribute Attrs;

        public string fnInvocation;

        public QuantifierExpr(Token tok, List<Ident> idents, Expr range, Expr body, Attribute attrs)
        : base(tok)
        {
            Idents = idents;
            Range = range;
            Body = body;
            Attrs = attrs;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string indentsStr = Util.ListIdentsToString(Idents, labelOn) + " ";
            string attrsStr = (Attrs == null) ? "" : Attrs.ToString(0, labelOn) + " ";
            string rangeStr = (Range == null) ? "" : "| " + Range.ToString(0, labelOn) + " ";
            string quantifierDomainStr = indentsStr + attrsStr + rangeStr;
            str = str + indentationStr + FirstTok.val + " " + quantifierDomainStr + ":: " + Body.ToString(0, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (Ident ident in Idents)
            {
                BoundVarDecl bv = new BoundVarDecl(ident.FirstTok, ident, ident.Ty);
                bv.Sc = Sc;
                bv.TypeResolve(null, ref errors); // bv will be pushed into scope in TypeResolve
            }
            if (Attrs != null)
            {
                Attrs.Sc = Sc;
                Attrs.TypeResolve(null, ref errors);
            }
            if (Range != null)
            {
                Range.Sc = Sc;
                Range.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            if (Body != null)
            {
                Body.Sc = Sc;
                Body.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            foreach (Ident ident in Idents)
            {
                Sc.Pop();
            }
            this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }

        private List<Ident> getFnParameters()
        {
            List<Ident> idents = new List<Ident>();
            HashSet<string> names = new HashSet<string>();
            foreach (Ident bv in this.Idents)
            {
                names.Add(bv.Name);
            }
            foreach (AstNode node in AllChildren())
            {
                Ident ident = node as Ident;
                if (ident == null || ident.Declaration == null)
                {
                    continue;
                }
                if (names.Contains(ident.Name))
                {
                    continue;
                }
                idents.Add(ident);
                names.Add(ident.Name);
            }
            return idents;
        }

        public string ToFStarFunction(int indentation, string name)
        {
            // TODO: add attributes
            string fnStr = $"let {name} ";
            List<string> fstarStrs = new List<string>();
            List<string> typeStrs = new List<string>();
            foreach (Ident ident in getFnParameters())
            {
                fnStr += $"({ident.Name}: {ident.Ty.ToFStarLang(0, false)}) ";
                fstarStrs.Add(ident.ToFStarLang(0));
                typeStrs.Add(ident.Ty.ToFStarLang(0, false));
            }
            List<string> bvStrs = new List<string>();
            foreach (Ident bv in this.Idents)
            {
                bvStrs.Add($"({bv.Name}: {bv.Ty.ToFStarLang(0, false)})");
            }
            fnStr += $"= ComputationProduces (u2b (forall {string.Join(' ', bvStrs)}. {Range.ToFStarExpr("")} ==> {Body.ToFStarExpr("")}))";
            fnInvocation = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{string.Join(';', fstarStrs)}] ({this.Ty.ToFStarLang(0, false)}) [{string.Join(';', typeStrs)}] {name}";

            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnStr;
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnInvocation;
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var ident in Idents)
            {
                foreach (var node in ident.AllChildren())
                    yield return node;
                yield return ident;
            }
            if (Range != null)
            {
                foreach (var node in Range.AllChildren())
                    yield return node;
                yield return Range;
            }
            if (Body != null)
            {
                foreach (var node in Body.AllChildren())
                    yield return node;
                yield return Body;
            }
            if (Attrs != null)
            {
                foreach (var node in Attrs.AllChildren())
                    yield return node;
                yield return Attrs;
            }
        }
    }

    public class ForallExpr : QuantifierExpr
    {
        public ForallExpr(Token tok, List<Ident> idents, Expr range, Expr body, Attribute attrs)
        : base(tok, idents, range, body, attrs) { }
        public override string ToFStarLang(int indentation)
        {
            return base.ToFStarLang(0);
        }
    }

    public class ExistsExpr : QuantifierExpr
    {
        public ExistsExpr(Token tok, List<Ident> idents, Expr range, Expr body, Attribute attrs)
        : base(tok, idents, range, body, attrs) { }
        public override string ToFStarLang(int indentation)
        {
            return base.ToFStarLang(0);
        }
    }

    public abstract class ComprehensionExpr : Expr
    {
        public readonly List<Ident> Idents;
        public readonly Expr Range;
        public Expr Term;
        public Attribute Attributes;
        public string fnInvocation;

        public ComprehensionExpr(Token tok, List<Ident> idents, Expr range, Expr term, Attribute attrs)
        : base(tok)
        {
            // Contract.Requires(cce.NonNullElements(idents));
            Contract.Requires(term != null);

            this.Idents = idents;
            this.Range = range;
            this.Term = term;
            this.Attributes = attrs;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string idensStr = Util.ListIdentsToString(Idents, labelOn) + " ";
            string attrsStr = (Attributes == null) ? "" : Attributes.ToString(0, labelOn) + " ";
            string rangeStr = (Range == null) ? "" : "| " + Range.ToString(0, labelOn) + " ";
            string bodyStr = (Term == null) ? "" : ":: " + Term.ToString(0, labelOn);
            str = str + indentationStr + FirstTok.val + " " + idensStr + attrsStr + rangeStr + bodyStr;
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            foreach (Ident ident in Idents)
            {
                BoundVarDecl bv = new BoundVarDecl(ident.FirstTok, ident, ident.Ty);
                bv.Sc = Sc;
                bv.TypeResolve(null, ref errors); // bv will be pushed into scope in TypeResolve
            }
            if (Attributes != null)
            {
                Attributes.Sc = Sc;
                Attributes.TypeResolve(null, ref errors);
            }
            if (Range != null)
            {
                Range.Sc = Sc;
                Range.TypeResolve(new PredefinedType(PredefinedTypeEnum.Bool), ref errors);
            }
            if (Term != null)
            {
                Term.Sc = Sc;
                Term.TypeResolve(enforcingType, ref errors);
            }
            if (Range is not BinaryExpr || (Range as BinaryExpr).opcode != Opcode.In)
            {
                errors.SemErr(Range.FirstTok, $"Comprehension expression only supports container range expressions like \"x in s\"");
            }
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public List<Ident> getFnParameters(Expr boundedExpr)
        {
            List<Ident> idents = new List<Ident>();
            HashSet<string> names = new HashSet<string>();
            foreach (Ident bv in this.Idents)
            {
                names.Add(bv.Name);
            }
            foreach (AstNode node in boundedExpr.AllChildren())
            {
                Ident ident = node as Ident;
                if (ident == null || ident.Declaration == null)
                {
                    continue;
                }
                if (names.Contains(ident.Name))
                {
                    continue;
                }
                idents.Add(ident);
                names.Add(ident.Name);
            }
            return idents;
        }

        public string ToFStarMapFunction(int indentation, string name)
        {
            string mapFn = name + "_fn";
            string fnStr = $"let {mapFn} ";
            List<string> fstarStrs = new List<string>();
            foreach (Ident ident in getFnParameters(Term))
            {
                fnStr += $"({ident.Name}: {ident.Ty.ToFStarLang(0, false)}) ";
                fstarStrs.Add(ident.ToFStarLang(0));
            }
            foreach (Ident bv in this.Idents)
            {
                fnStr += $"({bv.Name}: {bv.Ty.ToFStarLang(0, false)}) ";
            }
            fnStr += $"= {Term.ToFStarExpr("")}\n";

            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnStr;
            str += ToFStarFunction(indentation, name);
            return str;
        }
        abstract public string ToFStarFunction(int indentation, string name);

        public override string ToFStarLang(int indentation)
        {            
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnInvocation;
            return str;
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var ident in Idents)
            {
                foreach (var node in ident.AllChildren())
                    yield return node;
                yield return ident;
            }
            if (Attributes != null)
            {
                foreach (var node in Attributes.AllChildren())
                    yield return node;
                yield return Attributes;
            }
            if (Range != null)
            {
                foreach (var node in Range.AllChildren())
                    yield return node;
                yield return Range;
            }
            if (Term != null)
            {
                foreach (var node in Term.AllChildren())
                    yield return node;
                yield return Term;
            }
        }
    }

    public class SetComprehension : ComprehensionExpr
    {
        public readonly bool Finite;
        public readonly bool TermIsImplicit;  // records the given syntactic form

        public SetComprehension(Token tok, bool finite, List<Ident> idents, Expr range, Expr term, Attribute attrs)
        : base(tok, idents, range, term ?? new Ident(tok, idents[0].Name), attrs)
        {
            Contract.Requires(tok != null);
            // Contract.Requires(cce.NonNullElements(idents));
            Contract.Requires(1 <= idents.Count);
            Contract.Requires(range != null);
            Contract.Requires(term != null || idents.Count == 1);

            TermIsImplicit = term == null;
            Finite = finite;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            return base.ToString(indentation, labelOn);
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type elementType = null;
            if (enforcingType != null)
            {
                if (enforcingType is not SetType)
                {
                    errors.SemErr(FirstTok, $"Cannot convert {this.ToString(0, false)} to non-set type.");
                }
                SetType enforcingSetType = (enforcingType as SetType);
                if (enforcingSetType.IsInfinite == Finite)
                {
                    errors.SemErr(FirstTok, $"The finite of set does not match.");
                }
                elementType = enforcingSetType.EntityType;
            }
            base.TypeResolve(elementType, ref errors);
            if (Finite)
            {
                Expr collection = (Range as BinaryExpr).secondOp;
                if ((collection.Ty is SetType && (collection.Ty as SetType).IsInfinite) ||
                    (collection.Ty is MapType && (collection.Ty as MapType).IsInfinite))
                {
                    errors.SemErr(FirstTok, "Cannot build a finite set from comprehension of infinite collection.");
                }
            }
            foreach (Ident ident in Idents)
            {
                Sc.Pop();
            }
            this.Ty = new SetType(elementType, !Finite);
        }
        public override string ToFStarFunction(int indentation, string name)
        {
            // TODO: add attributes
            string fnStr = $"let rec {name}_map ";
            BinaryExpr range = Range as BinaryExpr;
            if (range.secondOp.Ty is not SeqType)
            {
                throw new NotImplementedException();
            }
            Type typeA = range.firstOp.Ty;
            Type typeB = Term.Ty;
            Type collectionType = range.secondOp.Ty;
            List<string> fstarStrs = new List<string>();
            List<string> nameStrs = new List<string>();
            List<string> typeStrs = new List<string>();
            string extraParameters = "";
            foreach (Ident ident in getFnParameters(Term))
            {
                extraParameters += $"({ident.Name}: {ident.Ty.ToFStarLang(0, false)}) ";
                fstarStrs.Add(ident.ToFStarLang(0));
                nameStrs.Add(ident.Name);
                typeStrs.Add(ident.Ty.ToFStarLang(0, false));
            }
            fstarStrs.Add(range.secondOp.ToFStarLang(0));
            typeStrs.Add(collectionType.ToFStarLang(0, false));
            fnStr += extraParameters;
            fnStr += $"(s: {collectionType.ToFStarLang(0, false)})";
            fnStr += $": GTot ({this.Ty.ToFStarLang(0, false)}) (decreases rank s) =\n";
            string oneIndentStr = new string(' ', indentation + 2);
            string twoIndentStr = new string(' ', indentation + 4);
            fnStr += oneIndentStr + "if length s = 0 then\n";
            fnStr += twoIndentStr + (Finite ? "FStar.FiniteSet.Base.emptyset" : "FStar.Set.empty") + '\n';
            fnStr += oneIndentStr + "else\n" + twoIndentStr;
            if (Finite)
            {
                fnStr += $"FStar.FiniteSet.Base.insert ({name}_fn {string.Join(' ', nameStrs)} (index s 0)) ({name}_map {string.Join(' ', nameStrs)} (drop s 1))";
            }
            else
            {
                fnStr += $"FStar.Set.union (FStar.Set.singleton ({name}_fn {string.Join(' ', nameStrs)} (index s 0))) ({name}_map {string.Join(' ', nameStrs)} (drop s 1))";
            }

            fnStr += '\n';
            fnStr += $"let {name} {extraParameters}(s: {collectionType.ToFStarLang(0, false)}) = ComputationProduces ({name}_map {string.Join(' ', nameStrs)} s)";
            fnInvocation = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{string.Join(';', fstarStrs)}] ({this.Ty.ToFStarLang(0, false)}) [{string.Join(';', typeStrs)}] {name}";

            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnStr;
            return str;
        }
    }

    public class MapComprehension : ComprehensionExpr
    {
        public readonly bool Finite;
        public readonly Expr ValueExpr;

        public MapComprehension(Token tok, bool finite, List<Ident> idents, Expr range, Expr keyExpr, Expr valueExpr, Attribute attrs)
          : base(tok, idents, range, keyExpr, attrs)
        {
            Contract.Requires(tok != null);
            // Contract.Requires(cce.NonNullElements(idents));
            Contract.Requires(1 <= idents.Count);
            Contract.Requires(keyExpr != null);
            Contract.Requires(valueExpr != null || idents.Count == 1);

            Finite = finite;
            ValueExpr = valueExpr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string valueStr = (ValueExpr == null) ? "" : " := " + ValueExpr.ToString(0, labelOn);
            return base.ToString(indentation, labelOn) + valueStr;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type prevElementKeyType = null;
            Type prevElementValueType = null;
            if (enforcingType != null)
            {
                if (enforcingType is not MapType)
                {
                    errors.SemErr(FirstTok, $"Cannot convert {this.ToString(0, false)} to non-map type.");
                }
                MapType enforcingMapType = (enforcingType as MapType);
                if (enforcingMapType.IsInfinite == Finite)
                {
                    errors.SemErr(FirstTok, $"The finite of map does not match.");
                }
                prevElementKeyType = enforcingMapType.KeyType;
                prevElementValueType = enforcingMapType.EntityType;
            }
            if (Finite)
            {
                Expr collection = (Range as BinaryExpr).secondOp;
                if ((collection.Ty is SetType && (collection.Ty as SetType).IsInfinite) ||
                    (collection.Ty is MapType && (collection.Ty as MapType).IsInfinite))
                {
                    errors.SemErr(FirstTok, "Cannot build a finite map from comprehension of infinite collection.");
                }
            }
            base.TypeResolve(prevElementKeyType, ref errors);
            ValueExpr.Sc = Sc;
            ValueExpr.TypeResolve(prevElementValueType, ref errors);
            foreach (Ident ident in Idents) // pop the boundvardecl after all exprs are resolved
            {
                Sc.Pop();
            }
            this.Ty = new MapType(prevElementKeyType, prevElementValueType, !Finite);
        }
        public override string ToFStarFunction(int indentation, string name)
        {
            // TODO: add attributes
            // Value mapping function
            string valueFn = name + "_value";
            string fnStr = new string(' ', indentation) + $"let {valueFn} ";
            string extraParameters = "";
            List<string> fstarStrs = new List<string>();
            List<string> nameStrs = new List<string>();
            List<string> keyParaStrs = new List<string>();
            List<string> valueParaStrs = new List<string>();
            List<string> typeStrs = new List<string>();
            foreach (Ident ident in getFnParameters(ValueExpr))
            {
                extraParameters += $"({ident.Name}: {ident.Ty.ToFStarLang(0, false)}) "; 
                fstarStrs.Add(ident.ToFStarLang(0));
                valueParaStrs.Add(ident.Name);
                nameStrs.Add(ident.Name);
                typeStrs.Add(ident.Ty.ToFStarLang(0, false));
            }
            fnStr += extraParameters;
            foreach (Ident bv in this.Idents)
            {
                fnStr += $"({bv.Name}: {bv.Ty.ToFStarLang(0, false)}) ";
            }
            fnStr += $"= {ValueExpr.ToFStarExpr("")}\n";
            // Recursive function
            fnStr += $"let rec {name}_map ";
            BinaryExpr range = Range as BinaryExpr;
            if (range.secondOp.Ty is not SeqType)
            {
                throw new NotImplementedException();
            }
            Type typeA = range.firstOp.Ty;
            Type typeB = Term.Ty;
            Type collectionType = range.secondOp.Ty;
            foreach (Ident ident in getFnParameters(Term))
            {
                extraParameters += $"({ident.Name}: {ident.Ty.ToFStarLang(0, false)}) ";
                fstarStrs.Add(ident.ToFStarLang(0));
                keyParaStrs.Add(ident.Name);
                nameStrs.Add(ident.Name);
                typeStrs.Add(ident.Ty.ToFStarLang(0, false));
            }
            fstarStrs.Add(range.secondOp.ToFStarLang(0));
            typeStrs.Add(collectionType.ToFStarLang(0, false));
            fnStr += extraParameters;
            fnStr += $"(s: {collectionType.ToFStarLang(0, false)})";
            fnStr += $": GTot ({this.Ty.ToFStarLang(0, false)}) (decreases rank s) =\n";
            string oneIndentStr = new string(' ', indentation + 2);
            string twoIndentStr = new string(' ', indentation + 4);
            fnStr += oneIndentStr + "if length s = 0 then\n";
            fnStr += twoIndentStr + (Finite ? "FStar.FiniteMap.Base.emptymap" : "(FStar.Map.const 0)") + '\n';
            fnStr += oneIndentStr + "else\n" + twoIndentStr;
            // FStar.Map.upd m k v
            string m = $"({name}_map {string.Join(' ', nameStrs)} (drop s 1))";
            string k = $"({name}_fn {string.Join(' ', keyParaStrs)} (index s 0))";
            string v = $"({name}_value {string.Join(' ', valueParaStrs)} (index s 0))";
            if (Finite)
            {
                fnStr += $"FStar.FiniteMap.Base.insert {k} {v} {m}";
            }
            else
            {
                fnStr += $"FStar.Map.upd {m} {k} {v}";
            }

            fnStr += '\n';
            fnStr += $"let {name} {extraParameters}(s: {collectionType.ToFStarLang(0, false)}) = ComputationProduces ({name}_map {string.Join(' ', nameStrs)} s)";
            fnInvocation = $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{string.Join(';', fstarStrs)}] ({this.Ty.ToFStarLang(0, false)}) [{string.Join(';', typeStrs)}] {name}";

            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + fnStr;
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            foreach (var node in ValueExpr.AllChildren())
                yield return node;
            yield return ValueExpr;
        }
    }

    public abstract class SuffixExpr : Expr
    {
        // BaseExpr could be seq or map, index could be natural number or key
        public Expr BaseExpr;

        public SuffixExpr(Token tok, Expr baseExpr)
        : base(tok)
        {
            Contract.Requires(baseExpr != null);
            BaseExpr = baseExpr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + BaseExpr.ToString(0, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            BaseExpr.Sc = Sc;
            BaseExpr.TypeResolve(null, ref errors);
            if (!(BaseExpr.Ty is SeqType || BaseExpr.Ty is MapType || BaseExpr.Ty is TypeSuffix))
            {
                errors.SemErr(BaseExpr.FirstTok, $"{BaseExpr.FirstTok.val} is not a sequence, array or map.");
            }
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + BaseExpr.ToCProgram(0);
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in BaseExpr.AllChildren())
                yield return node;
            yield return BaseExpr;
        }
    }

    public class SeqSelectExpr : SuffixExpr
    {
        public Expr IndexExpr;

        public SeqSelectExpr(Token tok, Expr baseExpr, Expr indexExpr)
        : base(tok, baseExpr)
        {
            Contract.Requires(indexExpr != null);
            IndexExpr = indexExpr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = base.ToString(indentation, labelOn) + "[" + IndexExpr.ToString(0, labelOn) + "]";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = base.ToCProgram(indentation) + "[" + IndexExpr.ToCProgram(0) + "]";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            base.TypeResolve(enforcingType, ref errors);
            IndexExpr.Sc = Sc;
            if (BaseExpr.Ty is SeqType)
            {
                IndexExpr.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
                this.Ty = ((CollectionType)BaseExpr.Ty).EntityType;
            }
            else if (BaseExpr.Ty is MapType)
            {
                IndexExpr.TypeResolve(((MapType)BaseExpr.Ty).KeyType, ref errors);
                this.Ty = ((CollectionType)BaseExpr.Ty).EntityType;
            }
            else if (BaseExpr.Ty is TypeSuffix)
            {
                IndexExpr.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
                this.Ty = ((TypeSuffix)BaseExpr.Ty).EntityType;
            }
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            if (BaseExpr.Ty is SeqType)
            {
                str += $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{BaseExpr.ToFStarLang(0)}; {IndexExpr.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{BaseExpr.Ty.ToFStarLang(0, false)}; nat] seq_index";
            }
            else if (BaseExpr.Ty is MapType)
            {
                MapType baseTy = BaseExpr.Ty as MapType;
                string selectFn = (baseTy.IsInfinite) ? "map_select" : "finite_map_select";
                str += $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{BaseExpr.ToFStarLang(0)}; {IndexExpr.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{BaseExpr.Ty.ToFStarLang(0, false)}; {IndexExpr.Ty.ToFStarLang(0, false)}] {selectFn}";
            }
            else if (BaseExpr.Ty is TypeSuffix)
            {
                TypeSuffix baseTy = BaseExpr.Ty as TypeSuffix;
                str += $"ExpressionDereference ({baseTy.EntityType.ToFStarLang(0, true)}) (ExpressionPointerOffset ({BaseExpr.ToFStarLang(0)}) ({IndexExpr.ToFStarLang(0)}))";
            }
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            foreach (var node in IndexExpr.AllChildren())
                yield return node;
            yield return IndexExpr;
        }
    }

    public class SeqRangeExpr : SuffixExpr
    {
        public Expr StartIndex;
        public Expr EndIndex;

        public SeqRangeExpr(Token tok, Expr baseExpr, Expr startIndex, Expr endIndex)
        : base(tok, baseExpr)
        {
            // both StartIndex and EndIndex can be null
            StartIndex = startIndex;
            EndIndex = endIndex;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string startStr = (StartIndex == null) ? "" : StartIndex.ToString(0, labelOn);
            string endStr = (EndIndex == null) ? "" : EndIndex.ToString(0, labelOn);
            string str = base.ToString(indentation, labelOn) + "[" + startStr + ".." + endStr + "]";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Type entityType = null;
            BaseExpr.Sc = Sc;
            BaseExpr.TypeResolve(null, ref errors);
            if (BaseExpr.Ty is SeqType)
            {
                entityType = ((SeqType)BaseExpr.Ty).EntityType;
            }
            else if (BaseExpr.Ty is TypeSuffix)
            {
                entityType = ((TypeSuffix)BaseExpr.Ty).EntityType;
            }
            else
            {
                errors.SemErr(BaseExpr.FirstTok, $"{BaseExpr.FirstTok.val} is not a sequence or array.");
            }
            if (StartIndex != null)
            {
                StartIndex.Sc = Sc;
                StartIndex.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
            }
            if (EndIndex != null)
            {
                EndIndex.Sc = Sc;
                EndIndex.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
            }
            this.Ty = new SeqType(entityType);
            CheckCompatiblity(enforcingType, ref errors);
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            if (BaseExpr.Ty is SeqType)
            {
                str += $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{BaseExpr.ToFStarLang(0)}; {StartIndex.ToFStarLang(0)}; {EndIndex.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{BaseExpr.Ty.ToFStarLang(0, false)}; nat; nat] seq_range";
            }
            else
            {
                throw new NotImplementedException();
            }
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            if (StartIndex != null)
            {
                foreach (var node in StartIndex.AllChildren())
                    yield return node;
                yield return StartIndex;
            }
            if (EndIndex != null)
            {
                foreach (var node in EndIndex.AllChildren())
                    yield return node;
                yield return EndIndex;
            }
        }
    }

    public class SeqAssignExpr : SuffixExpr
    {
        public Expr IndexExpr;
        public Expr ValExpr;

        public SeqAssignExpr(Token tok, Expr baseExpr, Expr indexExpr, Expr valExpr)
        : base(tok, baseExpr)
        {
            Contract.Requires(indexExpr != null);
            Contract.Requires(valExpr != null);
            IndexExpr = indexExpr;
            ValExpr = valExpr;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = base.ToString(indentation, labelOn) + "[" +
                         IndexExpr.ToString(0, labelOn) + ":= " + ValExpr.ToString(0, labelOn) + "]";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            base.TypeResolve(enforcingType, ref errors);
            IndexExpr.Sc = Sc;
            if (BaseExpr.Ty is SeqType)
            {
                IndexExpr.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
            }
            else if (BaseExpr.Ty is MapType)
            {
                IndexExpr.TypeResolve(((MapType)BaseExpr.Ty).KeyType, ref errors);
            }
            else
            {
                errors.SemErr(BaseExpr.FirstTok, "Invalid base type for SeqAssignExpr.");
            }
            CollectionType baseType = (CollectionType)BaseExpr.Ty;
            ValExpr.Sc = Sc;
            ValExpr.TypeResolve(baseType.EntityType, ref errors);
            this.Ty = BaseExpr.Ty;
            CheckCompatiblity(enforcingType, ref errors);
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            string updateFn = "";
            if (BaseExpr.Ty is SeqType)
            {
                updateFn = "seq_update";
            }
            else if (BaseExpr.Ty is MapType)
            {
                updateFn = ((BaseExpr.Ty as MapType).IsInfinite) ? "map_update" : "finite_map_update";
            }
            str += $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{BaseExpr.ToFStarLang(0)}; {IndexExpr.ToFStarLang(0)}; {ValExpr.ToFStarLang(0)}] ({this.Ty.ToFStarLang(0, false)}) [{BaseExpr.Ty.ToFStarLang(0, false)}; {IndexExpr.Ty.ToFStarLang(0, false)}; {ValExpr.Ty.ToFStarLang(0, false)}] {updateFn}";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            foreach (var node in IndexExpr.AllChildren())
                yield return node;
            yield return IndexExpr;
            foreach (var node in ValExpr.AllChildren())
                yield return node;
            yield return ValExpr;
        }
    }

    public class ApplySuffix : SuffixExpr
    {
        public List<Expr> Args;

        // Filled in during resolution, then FunctionCall will be changed to another class
        public DatatypeMemberDecl datatypeMember;
        public MethodDecl Callee;


        public ApplySuffix(Token tok, Expr baseExpr, List<Expr> args)
        : base(tok, baseExpr)
        {
            Contract.Requires(args != null);
            Args = args;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = base.ToString(indentation, labelOn) + "(" + Util.ListExprsToString(Args, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            if (this.BaseExpr is not Ident)
            {
                errors.SemErr(this.BaseExpr.FirstTok, $"{this.BaseExpr.ToString(0, false)} is not a memberDecl.");
            }
            Ident memberId = this.BaseExpr as Ident;
            List<Type> argTypes = new List<Type>();
            foreach (Expr arg in Args)
            {
                arg.Sc = Sc;
                arg.TypeResolve(null, ref errors);
                argTypes.Add(arg.Ty);
            }
            List<string> typesStr = new List<string>();
            foreach (Type ty in argTypes)
            {
                typesStr.Add(ty.ToString(0));
            }
            MemberDecl memberDecl = Sc.GetMemberDecl(memberId, false, argTypes);
            datatypeMember = Sc.GetDatatypeMemberDecl(memberId.Name);
            if (memberDecl == null && datatypeMember == null)
            {
                errors.SemErr(memberId.FirstTok, $"{memberId.FirstTok.val} with arg types ({string.Join(", ", typesStr)}) is not found!");
            }
            if (memberDecl is MethodDecl) // function call
            {
                Callee = memberDecl as MethodDecl;
                if (Callee.Ret != null)
                {
                    this.Ty = Callee.Ret.Ty;
                }
            }
            else if (datatypeMember != null) // datatypemember constructor
            {
                if (datatypeMember.Arguments.Count != argTypes.Count)
                {
                    errors.SemErr(datatypeMember.FirstTok, $"datatype member {memberId.FirstTok.val} with arg types ({string.Join(", ", typesStr)}) is not found!");
                }
                for (int i = 0; i < argTypes.Count; i++)
                {
                    // check generic type
                    // TODO: change to compatible type
                    if (datatypeMember.Arguments[i].Ty is not GenericType &&
                        datatypeMember.Arguments[i].Ty.ToString(0) != argTypes[i].ToString(0))
                    {
                        errors.SemErr(datatypeMember.FirstTok, $"datatype member {memberId.FirstTok.val} with arg types ({string.Join(", ", typesStr)}) is not found!");
                    }
                }
                this.Ty = datatypeMember.parent.Ty;
            }
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = base.ToCProgram(indentation) + "(" + Util.ListExprsToString(Args, false) + ")";
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            str += $"ExpressionConstant (ObjectValueAbstract ({Ty.ToFStarLang(0, false)}) ({datatypeMember.Name.Name} ";
            str += $"{string.Join(' ', Args.ConvertAll(arg => arg.ToString(0, false)))}))";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var arg in Args)
            {
                foreach (var node in arg.AllChildren())
                    yield return node;
                yield return arg;
            }
        }
    }

    public class FunctionCall : ApplySuffix
    {
        public FunctionCall(Token tok, Expr baseExpr, List<Expr> args, MethodDecl callee)
        : base(tok, baseExpr, args)
        {
            this.Callee = callee;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            throw new NotSupportedException();
        }

        public string ToFStarLang(int indentation, bool stackOverflow)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            str = "MethodCallStatement ";
            str += $"\"{Callee.Name.ToString(0, false).ToLower()}\" ";
            str += $"\"{NextPC}\" ";
            str += "[";
            var sep = "";
            foreach (var arg in Callee.Args)
            {
                str += sep + $"\"{arg.Name.ToString(0, false)}\"";
                sep = "; ";
            }
            str += "] [";
            sep = "";
            foreach (var arg in Args)
            {
                str += sep + arg.ToFStarLang(0);
                sep = "; ";
            }
            str += "]";
            str += $" level_{Callee.EnclosingLevel.Name.Name}_{Callee.Name.ToString(0, false).ToLower()}_stack_initializers";
            str += stackOverflow ? " true" : " false";
            return str;
        }
    }

    public class CasePattern : AstNode
    {
        public Ident Id;
        public List<CasePattern> Arguments;

        public CasePattern(Token tok, Ident id, List<CasePattern> arguments = null)
        : base(tok)
        {
            Contract.Requires(id != null);
            Id = id;
            Arguments = arguments;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string identifierStr = (Id == null) ? "" : Id.ToString(0, labelOn);
            string argumentsStr = "";
            if (Arguments != null)
            {
                List<string> elementsStr = new List<string>();
                foreach (CasePattern casePattern in Arguments)
                {
                    elementsStr.Add(casePattern.ToString(0, labelOn));
                }
                argumentsStr = "(" + string.Join(", ", elementsStr) + ")";
            }
            str = str + indentationStr + identifierStr + argumentsStr;
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: It might be better to change Ident to VarDecl here
            // no need to set this.Ty because this class is not an expression
            if (Arguments == null)
            {
                BoundVarDecl bv = new BoundVarDecl(FirstTok, Id, enforcingType);
                bv.Sc = Sc;
                bv.TypeResolve(null, ref errors); // bv will be pushed into scope in TypeResolve
                return;
            }
            if (enforcingType is not UserDefinedType)
            {
                errors.SemErr(Id.FirstTok, "Datatype mismatch!");
                return;
            }
            UserDefinedType ut = enforcingType as UserDefinedType;
            DatatypeDecl datatypeDecl = Sc.GetDatatypeDecl(ut.Name.Name);
            var datatypeMemberDecls = datatypeDecl.GetDefinedMemberList(ut.ArgumentList);
            int datatypeIndex = datatypeDecl.GetMemberDeclIndex(Id.Name);
            if (datatypeIndex == -1)
            {
                errors.SemErr(Id.FirstTok, $"This match case '{Id.Name}' does not match any datatype member!");
                return;
            }
            List<Parameter> parameters = datatypeMemberDecls[datatypeIndex].Arguments;
            if (Arguments.Count != parameters.Count)
            {
                errors.SemErr(Id.FirstTok, $"The datatype member {Id.Name} has {parameters.Count} parameters but this match case has {Arguments.Count} parameters!");
                return;
            }
            for (int i = 0; i < Arguments.Count; i++)
            {
                CasePattern cp = Arguments[i];
                cp.Sc = Sc;
                cp.TypeResolve(parameters[i].Ty, ref errors);
            }
            // no need to set this.Ty because this class is not an expression
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
            if (Arguments == null)
            {
                return str + indentationStr + Id.Name;
            }
            str += indentationStr + "(" + Id.Name;
            foreach (CasePattern cp in Arguments)
            {
                str += " " + cp.ToFStarLang(0);
            }
            str += ")";
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Id;
            if (Arguments != null)
            {
                foreach (var cp in Arguments)
                {
                    foreach (var node in cp.AllChildren())
                        yield return node;
                    yield return cp;
                }
            }
        }
    }

    public abstract class MatchCase : AstNode
    {
        public readonly string Id;
        public List<CasePattern> CasePatterns;
        public DatatypeMemberDecl datatypeMember;  // filled in during resolution

        public MatchCase(Token tok, string id, List<CasePattern> cps)
        : base(tok)
        {
            Contract.Requires(id != null);
            // Contract.Requires(cce.NonNullElements(cps));
            this.Id = id;
            this.CasePatterns = cps;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string casePatternsStr = "";
            if (CasePatterns.Count != 0)
            {
                List<string> elementsStr = new List<string>();
                foreach (CasePattern casePattern in CasePatterns)
                {
                    elementsStr.Add(casePattern.ToString(0, labelOn));
                }
                casePatternsStr = " (" + string.Join(", ", elementsStr) + ")";
            }
            str = str + indentationStr + "case " + Id + casePatternsStr + " => ";
            return str;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // check mismatch string
            if (CasePatterns.Count != datatypeMember.Arguments.Count)
            {
                errors.SemErr(this.FirstTok, $"The datatype member {Id} has {datatypeMember.Arguments.Count} parameters but this match case has {CasePatterns.Count} parameters!");
                return;
            }
            for (int i = 0; i < CasePatterns.Count; i++)
            {
                var casePattern = CasePatterns[i];
                if (casePattern.Id.Name == "_")
                {
                    continue; // no need to add bounded variable _
                }
                var parameter = datatypeMember.Arguments[i];
                casePattern.Sc = Sc;
                casePattern.TypeResolve(parameter.Ty, ref errors);
            }
            // no need to set this.Ty because this class is not an expression
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
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + Id;
            foreach (CasePattern cp in CasePatterns)
            {
                str += " " + cp.ToFStarLang(0);
            }
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var cp in CasePatterns)
            {
                foreach (var node in cp.AllChildren())
                    yield return node;
                yield return cp;
            }
        }
    }

    public class MatchCaseExpr : MatchCase
    {
        public Expr Body;

        public MatchCaseExpr(Token tok, string id, List<CasePattern> cps, Expr body)
          : base(tok, id, cps)
        {
            Contract.Requires(id != null);
            // Contract.Requires(cce.NonNullElements(cps));
            Contract.Requires(body != null);
            this.Body = body;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            return base.ToString(indentation, labelOn) + Body.ToString(0, labelOn);
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            int originCount = Sc.DefinedEntities.Count;
            base.TypeResolve(null, ref errors);
            Body.Sc = Sc;
            Body.TypeResolve(enforcingType, ref errors);
            int scopePopCount = Sc.DefinedEntities.Count - originCount;
            for (int i = 0; i < scopePopCount; i++)
            {
                Sc.Pop();
            }
            // no need to set this.Ty because this class is not an expression
        }
        public override string ToCProgram(int indentation)
        {
            throw new NotImplementedException();
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + " | " + base.ToFStarLang(0) + " -> " + Body.ToFStarExpr("");
            return str;
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in base.AllChildren())
                yield return node;
            foreach (var node in Body.AllChildren())
                yield return node;
            yield return Body;
        }
    }

    public class MatchExpr : Expr
    {  // a MatchExpr is an "extended expression" and is only allowed in certain places
        private Expr source;
        private List<MatchCaseExpr> cases;
        private DatatypeDecl datatypeDecl; // filled in during resolution
        private string FunctionName; // filled in during F* generation
        public readonly bool UsesOptionalBraces;

        public MatchExpr(Token tok, Expr source, List<MatchCaseExpr> cases, bool usesOptionalBraces)
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
            foreach (MatchCaseExpr expr in cases)
            {
                elementsStr.Add(expr.ToString(0, labelOn));
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
            if (source.Ty is not UserDefinedType)
            {
                errors.SemErr(source.FirstTok, "The source of match expression should be user defined datatype!");
            }
            UserDefinedType t = source.Ty as UserDefinedType;
            datatypeDecl = Sc.GetDatatypeDecl(t.Name.Name);
            var datatypeMemberDeclList = datatypeDecl.GetDefinedMemberList(t.ArgumentList);
            Type preType = enforcingType;
            foreach (MatchCaseExpr matchCase in cases)
            {
                matchCase.Sc = Sc;
                int datatypeIndex = datatypeDecl.GetMemberDeclIndex(matchCase.Id);
                if (datatypeIndex < 0)
                {
                    errors.SemErr(matchCase.FirstTok, $"This match case '{matchCase.Id}' does not match any datatype member!");
                    return;
                }
                matchCase.datatypeMember = datatypeMemberDeclList[datatypeIndex];
                matchCase.TypeResolve(preType, ref errors);
                preType = matchCase.Body.Ty;
            }
            this.Ty = preType;
        }

        public string ToFStarFunction(int indentation, string functionName)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            this.FunctionName = functionName;
            str += indentationStr + $"let {functionName}({source.ToString(0, false)}: {source.Ty.ToFStarLang(0, false)}): conditional_computation_t ({this.Ty.ToFStarLang(0, false)}) =\n";
            str += indentationStr + "ComputationProduces (\n";
            str += indentationStr + "match " + source.ToString(0, false) + " with \n";
            foreach (MatchCaseExpr oneCase in cases)
            {
                str += oneCase.ToFStarLang(indentation + 4) + '\n';
            }
            str += indentationStr + ")\n";
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"ExpressionApplyFunction ({this.Ty.ToFStarLang(0, true)}) [{source.ToFStarLang(0)}] {this.Ty.ToString(0)} [{source.Ty.ToFStarLang(0, false)}] {FunctionName}";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in source.AllChildren())
                yield return node;
            yield return source;
            foreach (var matchCase in cases)
            {
                foreach (var node in matchCase.AllChildren())
                    yield return node;
                yield return matchCase;
            }
        }
    }

    public class AllocRhs : Expr
    {
        public Type AllocType;
        public Expr Count;
        public bool IsCalloc;
        public bool IsSequential = false; // filled in during resolution
        public Expr Lhs; // filled in during resolution

        public AllocRhs(Token tok, Type allocType, Expr count, bool isCalloc)
        : base(tok)
        {
            Contract.Requires(allocType != null);
            Contract.Requires(count != null);
            AllocType = allocType;
            Count = count;
            IsCalloc = isCalloc;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + (IsCalloc ? "calloc" : "malloc") + "(" + AllocType.ToString(0) + ", " + Count.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Count.Sc = Sc;
            Count.TypeResolve(new PredefinedType(PredefinedTypeEnum.Nat), ref errors);
            bool isDefinedType = Sc.IsDefinedType(AllocType);
            if (!isDefinedType)
            {
                errors.SemErr(FirstTok, AllocType.ToString(0) + "'s type is not defined.");
            }
            this.Ty = new PointerType(AllocType);
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (IsCalloc)
            {
                str = str + indentationStr + "(" + AllocType.ToCProgram(0) + "*) calloc(sizeof(" + AllocType.ToCProgram(0) + "), " + Count.ToCProgram(0) + ")";
            }
            else
            {
                str = str + indentationStr + "(" + AllocType.ToCProgram(0) + "*) malloc(sizeof(" + AllocType.ToCProgram(0) + ") * " + Count.ToCProgram(0) + ")";
            }
            return str;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            str += IsCalloc ? "CallocSuccessfulStatement " : "MallocSuccessfulStatement ";
            str += IsSequential ? "true " : "false ";
            str += $"({Lhs.ToFStarLang(0)}) ({AllocType.ToFStarLang(0, true)}) ({Count.ToFStarLang(0)}) \n";
            str += IsCalloc ? "CallocReturningNullStatement " : "MallocReturningNullStatement ";
            str += IsSequential ? "true " : "false ";
            str += $"({Lhs.ToFStarLang(0)}) ({Count.ToFStarLang(0)}) \n";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Count.AllChildren())
                yield return node;
            yield return Count;
        }
    }

    public class CreateThreadRhs : Expr
    {
        public Ident Id;
        public List<Expr> Exprs;
        public string threadIDName;
        private bool threadIDChanged;
        public MethodDecl Callee;
        public bool IsSequential = false; // filled in during resolution
        public Expr OptionalResult = null; // filled in during resolution

        public CreateThreadRhs(Token tok, Ident id, List<Expr> exprs)
        : base(tok)
        {
            Contract.Requires(id != null);
            Contract.Requires(exprs != null);
            Id = id;
            Exprs = exprs;
            threadIDName = "_" + Id.ToCProgram(0) + "ID";
            threadIDChanged = false;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "create_thread " + Id.ToString(0, labelOn) +
                  "(" + Util.ListExprsToString(Exprs, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Id.Sc = Sc;
            List<Type> argTypes = new List<Type>();
            foreach (Expr expr in Exprs)
            {
                expr.Sc = Sc;
                expr.TypeResolve(null, ref errors);
                argTypes.Add(expr.Ty);
            }
            MemberDecl memberDecl = Sc.GetMemberDecl(Id, false, argTypes);

            if (memberDecl == null || memberDecl is not MethodDecl)
            {
                List<string> typesStr = new List<string>();
                foreach (Type ty in argTypes)
                {
                    typesStr.Add(ty.ToString(0));
                }
                errors.SemErr(Id.FirstTok, $"MethodDecl {Id.FirstTok.val} with arg types ({string.Join(", ", typesStr)}) is not found!");
            }
            else
            {
                Callee = memberDecl as MethodDecl;
                if (Callee.Ret != null)
                {
                    errors.SemErr(Id.FirstTok, $"{Id.FirstTok.val} must be void!");
                }
            }
            this.Ty = new PredefinedType(PredefinedTypeEnum.ThreadId);
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);

            string threadWrapperName = "_" + Id.ToCProgram(0) + "Wrapper";
            string structType = "struct _" + Id.ToCProgram(0) + "Args";
            string argsVar = "_" + Id.ToCProgram(0) + "WrapperArgs";

            // Create thread ID if necessary
            if (!threadIDChanged)
            {
                str = str + indentationStr + "pthread_t " + threadIDName + ";\n";
            }

            if (Exprs.Count > 0)
            {
                // Create args struct
                str = str + indentationStr + structType + " temp" + argsVar + " = {" + Util.ListExprsToString(Exprs, false) + "};\n";
                str = str + indentationStr + structType + "* " + argsVar + " = malloc(sizeof(" + structType + "));\n";
                str = str + indentationStr + "*" + argsVar + " = temp" + argsVar + ";\n";
            }

            // Spin up new thread
            str = str + indentationStr + "pthread_create((pthread_t *) &" + threadIDName +
                    ", NULL, (void *) &" + threadWrapperName + ", ";
            if (Exprs.Count > 0)
            {
                str = str + "(void *)" + argsVar + ")";
            }
            else
            {
                str = str + "NULL)";
            }
            return str;
        }

        public void SetThreadIDName(string threadIDName)
        {
            this.threadIDName = threadIDName;
            threadIDChanged = true;
        }
        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            str += "CreateThreadStatement ";
            str += $"\"{Callee.Name.ToString(0, false)}\" ";
            str += $"\"{Callee.PC}\" ";
            str += IsSequential ? "true " : "false ";
            str += (OptionalResult == null) ? "None " : $"(Some ({OptionalResult.ToFStarLang(0)})) ";
            str += "[";
            var sep = "";
            foreach (var arg in Callee.Args)
            {
                str += sep + $"\"{arg.Name.ToString(0, false)}\"";
                sep = "; ";
            }
            str += "] [";
            sep = "";
            foreach (var arg in Exprs)
            {
                str += sep + arg.ToFStarLang(0);
                sep = "; ";
            }
            str += "]";
            str += $" level_{Callee.EnclosingLevel.Name.Name}_{Callee.Name.ToString(0, false)}_stack_initializers";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Id;
            foreach (var expr in Exprs)
            {
                foreach (var node in expr.AllChildren())
                    yield return node;
                yield return expr;
            }
        }
    }

    public class CompareAndSwapRhs : Expr
    {
        public Expr Target;
        public Expr Oldval;
        public Expr Newval;

        public bool IsSequential;
        public Expr OptionalResult;

        public CompareAndSwapRhs(Token tok, Expr target, Expr oldval, Expr newval)
        : base(tok)
        {
            Contract.Requires(target != null);
            Contract.Requires(oldval != null);
            Contract.Requires(newval != null);
            Target = target;
            Oldval = oldval;
            Newval = newval;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "compare_and_swap(" + Target.ToString(0, labelOn) + ", " +
                  Oldval.ToString(0, labelOn) + ", " + Newval.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Target.Sc = Sc;
            Target.TypeResolve(null, ref errors);
            Oldval.Sc = Sc;
            Oldval.TypeResolve(null, ref errors);
            Newval.Sc = Sc;
            Newval.TypeResolve(null, ref errors);
            this.Ty = new PredefinedType(PredefinedTypeEnum.Bool);
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "compare_and_swap(&" + Target.ToCProgram(0) + ", " +
                  Oldval.ToCProgram(0) + ", " + Newval.ToCProgram(0) + ")";
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            string compareStatement = $"CompareAndSwapStatement ({Target.ToFStarLang(0)}) ({Oldval.ToFStarLang(0)}) ({Newval.ToFStarLang(0)}) {IsSequential.ToString().ToLower()} ";
            compareStatement += (OptionalResult == null) ? "None" : $"(Some ({OptionalResult.ToFStarLang(0)}))";
            return str + indentationStr + compareStatement;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Target.AllChildren())
                yield return node;
            yield return Target;
            foreach (var node in Oldval.AllChildren())
                yield return node;
            yield return Oldval;
            foreach (var node in Newval.AllChildren())
                yield return node;
            yield return Newval;
        }
    }

    public class AtomicExchangeRhs : Expr
    {
        public Expr Target;
        public Expr Newval;
        public Expr Lhs = null; // filled in during resolution

        public AtomicExchangeRhs(Token tok, Expr target, Expr newval)
        : base(tok)
        {
            Contract.Requires(target != null);
            Contract.Requires(newval != null);
            Target = target;
            Newval = newval;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "atomic_exchange(" + Target.ToString(0, labelOn) + ", " + Newval.ToString(0, labelOn) + ")";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            Target.Sc = Sc;
            Target.TypeResolve(null, ref errors);
            Newval.Sc = Sc;
            Newval.TypeResolve(Target.Ty, ref errors);
            this.Ty = Target.Ty;
            CheckCompatiblity(enforcingType, ref errors);
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "atomic_exchange(&" + Target.ToCProgram(0) + ", " + Newval.ToCProgram(0) + ")";
            return str;
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + $"AtomicExchangeStatement ({Lhs.ToFStarLang(0)}) ({Target.ToFStarLang(0)}) ({Newval.ToFStarLang(0)})";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var node in Target.AllChildren())
                yield return node;
            yield return Target;
            foreach (var node in Newval.AllChildren())
                yield return node;
            yield return Newval;
        }
    }

    public class ArrayPointer : Expr, FStarExpressionConstant
    {
        public string ArrayName;
        public ArrayPointer(Token tok, string arrayName)
        : base(tok)
        {
            ArrayName = arrayName;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            return new string(' ', indentation) + ArrayName;
        }

        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            this.Ty = enforcingType;
        }

        public string ToFStarObjectValue()
        {
            return $"ObjectValuePrimitive (PrimitiveBoxPointer (PointerIndex (PointerRoot (RootIdGlobal \"_{ArrayName}_array\")) 0))";
        }

        public override string ToFStarLang(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += $"ExpressionConstant ({ToFStarObjectValue()})";
            return str;
        }
        public override string ToFStarExpr(string armadaStateName)
        {
            throw new NotImplementedException();
        }

        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public enum Opcode
    {
        Nop,
        LeftShift,
        RightShift, // Arithmatic right shift
        Add,
        Sub,
        Mul,
        Div,
        Neg,
        Mod,
        Equal,
        NotEqual,
        Lt,
        Le,
        Gt,
        Ge,
        In,
        NotIn,
        Not,
        Disjoint,
        And,
        Or,
        BitwiseAnd,
        BitwiseOr,
        BitwiseXor,
        BitwiseNot,
        AddressOf,
        Dereference,
        Dot,
        Equiv,
        Imply,
        Exply,
        Allocated,
        AllocatedArray,
        GlobalView,
        Cardinality,
    }

    public class OpcodeToString
    {
        public static string OpToStr(Opcode opcode)
        {
            switch (opcode)
            {
                case Opcode.Add:
                    return "+";
                case Opcode.AddressOf:
                    return "&";
                case Opcode.Allocated:
                    return "allocated";
                case Opcode.AllocatedArray:
                    return "allocated_array";
                case Opcode.And:
                    return "&&";
                case Opcode.BitwiseAnd:
                    return "&";
                case Opcode.BitwiseNot:
                    return "~";
                case Opcode.BitwiseOr:
                    return "|";
                case Opcode.BitwiseXor:
                    return "^";
                case Opcode.Cardinality:
                    return "| |";
                case Opcode.Dereference:
                    return " *";
                case Opcode.Disjoint:
                    return "!! ";
                case Opcode.Div:
                    return "/ ";
                case Opcode.Dot:
                    return ".";
                case Opcode.Equal:
                    return "==";
                case Opcode.Equiv:
                    return "<==>";
                case Opcode.Exply:
                    return "<==";
                case Opcode.Ge:
                    return ">=";
                case Opcode.GlobalView:
                    return "global_view";
                case Opcode.Gt:
                    return ">";
                case Opcode.Imply:
                    return "==>";
                case Opcode.In:
                    return "in";
                case Opcode.Le:
                    return "<=";
                case Opcode.LeftShift:
                    return "<<";
                case Opcode.Lt:
                    return "<";
                case Opcode.Mod:
                    return "%";
                case Opcode.Mul:
                    return "*";
                case Opcode.Neg:
                    return "-";
                case Opcode.Nop:
                    return "nop";
                case Opcode.Not:
                    return "!";
                case Opcode.NotEqual:
                    return "!=";
                case Opcode.NotIn:
                    return "notIn";
                case Opcode.Or:
                    return "||";
                case Opcode.RightShift:
                    return ">>";
                case Opcode.Sub:
                    return "-";
                default:
                    return " undefined opcode ";
            }
        }
    }
}
