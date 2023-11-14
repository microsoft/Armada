using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System;

namespace Microsoft.Starmada
{
    public abstract class Type
    {
        public abstract string ToString(int indentation);
        public abstract string ToCProgram(int indentation);
        public abstract string ToFStarLang(int indentation, bool includeObjectTD);

        public abstract bool EqualType(Type other);
        // The direction is this can be converted to other.
        public abstract bool CompatibleType(Type other);
    }

    public enum PredefinedTypeEnum
    {
        Int8 = 0,
        Int16,
        Int32,
        Int64,
        UInt8,
        UInt16,
        UInt32,
        UInt64,
        Int,
        Nat,
        Bool,
        Real,
        ThreadId,
        Char,
        String
    }

    public class PredefinedType : Type
    {
        public PredefinedTypeEnum Kind;
        public PredefinedType(PredefinedTypeEnum kind)
        {
            this.Kind = kind;
        }

        public bool IsBoundedInt()
        {
            switch (Kind)
            {
                case PredefinedTypeEnum.Int8:
                case PredefinedTypeEnum.Int16:
                case PredefinedTypeEnum.Int32:
                case PredefinedTypeEnum.Int64:
                case PredefinedTypeEnum.UInt8:
                case PredefinedTypeEnum.UInt16:
                case PredefinedTypeEnum.UInt32:
                case PredefinedTypeEnum.UInt64:
                    return true;
                default: return false;
            }
        }

        public override string ToString(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr;
            switch (Kind)
            {
                case PredefinedTypeEnum.Int8: str += "int8"; break;
                case PredefinedTypeEnum.Int16: str += "int16"; break;
                case PredefinedTypeEnum.Int32: str += "int32"; break;
                case PredefinedTypeEnum.Int64: str += "int64"; break;
                case PredefinedTypeEnum.UInt8: str += "uint8"; break;
                case PredefinedTypeEnum.UInt16: str += "uint16"; break;
                case PredefinedTypeEnum.UInt32: str += "uint32"; break;
                case PredefinedTypeEnum.UInt64: str += "uint64"; break;
                case PredefinedTypeEnum.Int: str += "int"; break;
                case PredefinedTypeEnum.Nat: str += "nat"; break;
                case PredefinedTypeEnum.Bool: str += "bool"; break;
                case PredefinedTypeEnum.Real: str += "real"; break;
                case PredefinedTypeEnum.ThreadId: str += "tid_t"; break;
                case PredefinedTypeEnum.Char: str += "char"; break;
                case PredefinedTypeEnum.String: str += "string"; break;
                default: throw new ArgumentException("Unknown type");
            }
            return str;
        }

        public override string ToCProgram(int indentation)
        {
                        string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr;
            switch (Kind)
            {
                case PredefinedTypeEnum.Int8: str += "int8_t"; break;
                case PredefinedTypeEnum.Int16: str += "int16_t"; break;
                case PredefinedTypeEnum.Int32: str += "int32_t"; break;
                case PredefinedTypeEnum.Int64: str += "int64_t"; break;
                case PredefinedTypeEnum.UInt8: str += "uint8_t"; break;
                case PredefinedTypeEnum.UInt16: str += "uint16_t"; break;
                case PredefinedTypeEnum.UInt32: str += "uint32_t"; break;
                case PredefinedTypeEnum.UInt64: str += "uint64_t"; break;
                case PredefinedTypeEnum.Int: str += "int"; break;
                case PredefinedTypeEnum.Nat: str += "nat"; break;
                case PredefinedTypeEnum.Bool: str += "bool"; break;
                case PredefinedTypeEnum.Real: str += "real"; break;
                case PredefinedTypeEnum.ThreadId: str += "tid_t"; break;
                case PredefinedTypeEnum.Char: str += "char"; break;
                case PredefinedTypeEnum.String: str += "string"; break;
                default: throw new ArgumentException("Unknown type");
            }
            return str;
        }

        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr;
            switch (Kind)
            {
                case PredefinedTypeEnum.Int8:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineInt8)" : "Armada.BoundedInt.MachineInt8";
                  break;
                case PredefinedTypeEnum.Int16:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineInt16)" : "Armada.BoundedInt.MachineInt16";
                  break;
                case PredefinedTypeEnum.Int32:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineInt32)" : "Armada.BoundedInt.MachineInt32";
                  break;
                case PredefinedTypeEnum.Int64:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineInt64)" : "Armada.BoundedInt.MachineInt64";
                  break;
                case PredefinedTypeEnum.UInt8:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineUint8)" : "Armada.BoundedInt.MachineUint8";
                  break;
                case PredefinedTypeEnum.UInt16:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineUint16)" : "Armada.BoundedInt.MachineUint16";
                  break;
                case PredefinedTypeEnum.UInt32:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineUint32)" : "Armada.BoundedInt.MachineUint32";
                  break;
                case PredefinedTypeEnum.UInt64:
                  str += includeObjectTD ? "ObjectTDPrimitive (PrimitiveTDBoundedInt Armada.BoundedInt.MachineUint64)" : "Armada.BoundedInt.MachineUint64";
                  break;
                case PredefinedTypeEnum.Int:
                  str += includeObjectTD ? "ObjectTDAbstract int" : "int";
                  break;
                case PredefinedTypeEnum.Nat:
                  str += includeObjectTD ? "ObjectTDAbstract nat" : "nat";
                  break;
                case PredefinedTypeEnum.Bool:
                  str += includeObjectTD ? "ObjectTDPrimitive PrimitiveTDBool" : "bool";
                  break;
                case PredefinedTypeEnum.Real:
                  str += includeObjectTD ? "ObjectTDAbstract real" : "real";
                  break;
                case PredefinedTypeEnum.ThreadId:
                  str += includeObjectTD ? "ObjectTDPrimitive PrimitiveTDThreadId" : "tid_t";
                  break;
                case PredefinedTypeEnum.Char:
                  str += includeObjectTD ? "ObjectTDAbstract char" : "char";
                  break;
                case PredefinedTypeEnum.String:
                  str += includeObjectTD ? "ObjectTDAbstract string" : "string";
                  break;
                default: throw new ArgumentException("Unknown type");
            }
            return str;
        }
        public override bool EqualType(Type other)
        {
            if (other is PredefinedType otherT)
            {
                return Kind == otherT.Kind;
            }
            return false;
        }
        public override bool CompatibleType(Type other)
        {
            // TODO (yuchen): ok this is nasty; let's check it carefully
            if (other is PredefinedType otherT)
            {
                return Kind == otherT.Kind || (Kind, otherT.Kind) switch {
                    (PredefinedTypeEnum.Nat, PredefinedTypeEnum.Int) => true,
                    (PredefinedTypeEnum a, PredefinedTypeEnum.Int) =>
                        // Bounded signed int types are compatible with unbounded int
                        IsBoundedSigned(a) || IsBoundedUnsigned(a),
                    (PredefinedTypeEnum a, PredefinedTypeEnum.Nat) =>
                        // Bounded unsigned int types are compatible with unbounded nat
                        IsBoundedUnsigned(a),
                    (PredefinedTypeEnum a, PredefinedTypeEnum b) =>
                        // Only bounded int types may be compatible to each other
                        CompatibleBoundedInt(a, b),
                };
            }
            return false;
        }
        static bool IsBoundedSigned(PredefinedTypeEnum kind) {
            return PredefinedTypeEnum.Int8 <= kind && kind <= PredefinedTypeEnum.Int64;
        }
        static bool IsBoundedUnsigned(PredefinedTypeEnum kind) {
            return PredefinedTypeEnum.UInt8 <= kind && kind <= PredefinedTypeEnum.UInt64;
        }
        static bool CompatibleBoundedInt(PredefinedTypeEnum a, PredefinedTypeEnum b) {
            return (IsBoundedSigned(a) && IsBoundedSigned(b) && a <= b)
                || (IsBoundedUnsigned(a) && IsBoundedUnsigned(b) && a <= b);
        }
    }

    public class PointerType : Type
    {
        public Type EntityType;
        public PointerType(Type entityType)
        {
            this.EntityType = entityType;
        }
        public override string ToString(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "ptr<";
            str = str + EntityType.ToString(0) + ">";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + EntityType.ToString(0) + "*";
            return str;
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            if (!includeObjectTD)
            {
                throw new NotImplementedException();
            }
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr + "ObjectTDPrimitive PrimitiveTDPointer";
            return str;
        }
        public override bool EqualType(Type other)
        {
            return other switch {
                PointerType otherT => EntityType.EqualType(otherT.EntityType),
                _ => false,
            };
        }
        public override bool CompatibleType(Type other)
        {
            // TODO (yuchen): Check assumption
            // Pointer types don't have the C-like compatibility.
            return other switch {
                PointerType otherT => EntityType.CompatibleType(otherT.EntityType),
                _ => false,
            };
        }
    }

    // This type is only used in datatypeDecl TypeResolve
    public class GenericType : Type
    {
        public string Name;
        public int Index;

        public GenericType(string name, int index)
        {
            Name = name;
            Index = index;
        }

        public override string ToString(int indentation)
        {
            return new string(' ', indentation) + Name;
        }
        public override string ToCProgram(int indentation)
        {
            return ToString(indentation);
        }
        public override string ToFStarLang(int indentation,  bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + (includeObjectTD ? "ObjectTDAbstract " : "");
            str += Name;
            return str;
        }
        public override bool EqualType(Type other)
        {
            // TODO (yuchen): Check assumption.
            // Index is a local tag and should imply Name.
            return other switch {
                GenericType otherT => Index == otherT.Index,
                _ => false,
            };
        }
        public override bool CompatibleType(Type other)
        {
            // TODO (yuchen): Check assumption.
            // Abstractors should only be compatible with themselves.
            return other switch {
                GenericType otherT => Index == otherT.Index,
                _ => false,
            };
        }
    }

    public class UserDefinedType : Type
    {
        public Ident Name;
        public List<Type> ArgumentList;
        public AstNode TypeDeclaration = null;
        public UserDefinedType(Ident name)
        {
            this.Name = name;
            this.ArgumentList = new List<Type>();
        }
        public UserDefinedType(Ident name, List<Type> argumentList)
        {
            this.Name = name;
            this.ArgumentList = argumentList;
        }
        public UserDefinedType(Ident name, List<Ident> argumentList)
        {
            Contract.Requires(argumentList != null);
            this.Name = name;
            this.ArgumentList = argumentList.ConvertAll(id => (Type)new UserDefinedType(id));
        }
        public override string ToString(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Name.ToString(0, false);
            if (ArgumentList != null && ArgumentList.Count > 0)
            {
                str += "<";
                var sep = "";
                foreach (var p in ArgumentList)
                {
                    str = str + sep + p.ToString(0);
                    sep = ", ";
                }
                str += ">";
            }
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + Name.ToString(0, false);
            if (ArgumentList != null && ArgumentList.Count > 0)
            {
                str += "(";
                var sep = "";
                foreach (var p in ArgumentList)
                {
                    str = str + sep + p.ToString(0);
                    sep = ", ";
                }
                str += ")";
            }
            return str;
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            if (TypeDeclaration is StructDecl) {
                str = indentationStr + "_user_defined_struct__";
                str += Name.ToString(0, false).ToLower();
                return str;
            }
            str += indentationStr + (includeObjectTD ? "ObjectTDAbstract (" : "");
            str += Name.ToString(0, false);
            if (ArgumentList.Count > 0)
            {
                str += " " + String.Join(" ", ArgumentList.ConvertAll(p => p.ToString(0)));
            }
            str += (includeObjectTD ? ")" : "");
            return str;
        }
        public override bool EqualType(Type other)
        {
            // TODO (yuchen): Is our type system nominal or structural?
            // For now, we assume nominal.
            return other switch {
                UserDefinedType otherT => Name.Name == otherT.Name.Name
                    && CompatibleType(other),
                _ => false,
            };
        }
        public override bool CompatibleType(Type other)
        {
            // TODO (yuchen): Same.
            // For now, we assume nominal.
            return other switch {
                UserDefinedType otherT => ArgumentList.Count == otherT.ArgumentList.Count
                    && ArgumentList
                        .Zip(otherT.ArgumentList, (a, b) => a.EqualType(b))
                        .All(x => x),
                _ => false,
            };
        }
    }

    public abstract class CollectionType : Type
    {
        public Type EntityType;

        public CollectionType(Type entityType)
        {
            this.EntityType = entityType;
        }

        public virtual string GetCollectionName()
        {
            return "";
        }

        public override string ToString(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + GetCollectionName() + "<";
            str += EntityType.ToString(0);
            str += ">";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            throw new NotSupportedException();
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            throw new NotImplementedException();
        }
    }

    public class SeqType : CollectionType
    {
        public SeqType(Type entityType)
        : base(entityType) { }

        public override string GetCollectionName()
        {
            return "seq";
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            if (includeObjectTD)
            {
                str += $"ObjectTDAbstract (seq {EntityType.ToFStarLang(0, false)})"; 
            }
            else
            {
                str = $"seq {EntityType.ToFStarLang(0, false)}";
            }
            return str;
        }
        public override bool EqualType(Type other)
        {
            return other switch {
                SeqType otherT => EntityType.EqualType(otherT.EntityType),
                _ => false,
            };
        }
        public override bool CompatibleType(Type other)
        {
            return other switch {
                SeqType otherT => EntityType.CompatibleType(otherT.EntityType),
                _ => false,
            };
        }
    }

    public class SetType : CollectionType
    {
        public bool IsInfinite;

        public SetType(Type entityType, bool isInfinite)
        : base(entityType)
        {
            this.IsInfinite = isInfinite;
        }

        public override string GetCollectionName()
        {
            return IsInfinite ? "iset" : "set";
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            string setStr = "";
            if (IsInfinite)
            {
                setStr = $"FStar.Set.set {EntityType.ToFStarLang(0, false)}";
            }
            else
            {
                setStr = $"FStar.FiniteSet.Base.set {EntityType.ToFStarLang(0, false)}";
            }
            if (includeObjectTD)
            {
                setStr = $"ObjectTDAbstract ({setStr})"; 
            }
            str += setStr;
            return str;
        }
        public override bool EqualType(Type other)
        {
            return other switch {
                SetType otherT => IsInfinite == otherT.IsInfinite
                    && EntityType.EqualType(otherT.EntityType),
                _ => false,
            };
        }
        public override bool CompatibleType(Type other)
        {
            return other switch {
                SetType otherT => (!IsInfinite || otherT.IsInfinite)
                    && EntityType.CompatibleType(otherT.EntityType),
                _ => false,
            };
        }
    }

    public class MapType : CollectionType
    {
        // For MapType, the inherited Entity is Value.
        public bool IsInfinite;
        public Type KeyType;

        public MapType(Type keyType, Type valueType, bool isInfinite)
        : base(valueType)
        {
            this.IsInfinite = isInfinite;
            this.KeyType = keyType;
        }

        public override string GetCollectionName()
        {
            return IsInfinite ? "imap" : "map";
        }

        public override string ToString(int indentation)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + GetCollectionName() + "<";
            str += KeyType.ToString(0) + ", " + EntityType.ToString(0);
            str += ">";
            return str;
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            string typePrefix = IsInfinite ? "FStar.Map.t" : "FStar.FiniteMap.Base.map";
            string typeStr = $"{typePrefix} {KeyType.ToFStarLang(0, false)} {EntityType.ToFStarLang(0, false)}";
            if (includeObjectTD)
            {
                str += $"ObjectTDAbstract ({typeStr})"; 
            }
            else
            {
                str += typeStr;
            }
            return str;
        }
        public override bool EqualType(Type other)
        {
            if (other is MapType mapT)
            {
                return IsInfinite == mapT.IsInfinite
                    && KeyType.EqualType(mapT.KeyType)
                    && EntityType.EqualType(mapT.EntityType);
            }
            return false;
        }
        public override bool CompatibleType(Type other)
        {
            if (other is MapType mapT)
            {
                return (!IsInfinite || mapT.IsInfinite)
                    && KeyType.CompatibleType(mapT.KeyType)
                    && EntityType.CompatibleType(mapT.EntityType);
            }
            return false;
        }
    }

    public class TypeSuffix : PointerType
    {
        public Ident Size;

        public TypeSuffix(Type baseType, Ident size)
        : base(baseType)
        {
            this.Size = size;
        }

        public override string ToString(int indentation)
        {
            string str = EntityType.ToString(indentation) + "[" + Size.ToString(0, false) + "]";
            return str;
        }

        public override string ToCProgram(int indentation)
        {
            string str = "[" + Size.ToCProgram(0) + "]";
            return str;
        }
        public string ToArrayFStarLang()
        {
            return $"ObjectTDArray ({EntityType.ToFStarLang(0, true)}) ({Size.ToString(0, false)})";
        }
        public override string ToFStarLang(int indentation, bool includeObjectTD)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str += indentationStr;
            if (!includeObjectTD)
            {
                throw new NotImplementedException();
            }
            str += ToArrayFStarLang();
            return str;
        }
        public override bool EqualType(Type other)
        {
            if (other is TypeSuffix arrT)
            {
                return base.EqualType(arrT) && Size.Name == arrT.Size.Name;
            }
            return false;
        }
        public override bool CompatibleType(Type other)
        {
            if (other is TypeSuffix arrT)
            {
                return base.CompatibleType(arrT) && Size.Name == arrT.Size.Name;
            }
            return false;
        }
    }
}
