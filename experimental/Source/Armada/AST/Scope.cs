using System.Diagnostics.Contracts;
using System.Collections.Generic;
using System;

namespace Microsoft.Starmada
{
    public class Scope
    {
        public List<AstNode> DefinedEntities = new List<AstNode>();
        public Scope Parent;
        public AstNode EnclosingNode;
        public Dictionary<string, Statement> PC2Stmt = new Dictionary<string, Statement>();

        public Scope(Scope parent = null)
        {
            this.Parent = parent;
        }

        public void Push(AstNode node)
        {
            DefinedEntities.Add(node);
            // if (Parent != null)
            // {
            //     Parent.Push(node);
            // }
        }
        public void Pop()
        {
            DefinedEntities.RemoveAt(DefinedEntities.Count - 1);
        }

        public bool IsDefinedType(Type type)
        {
            Contract.Requires(type != null);
            bool foundMatch = false;
            if (type is UserDefinedType)
            {
                var udt = (UserDefinedType)type;
                for (int i = DefinedEntities.Count - 1; i >= 0; i--)
                {
                    var entity = DefinedEntities[i];
                    if (entity is DatatypeDecl)
                    {
                        var typeDecl = (DatatypeDecl)entity;
                        if (typeDecl.Ty.Name.Name.ToLower() == udt.Name.Name.ToLower())
                        {
                            if (typeDecl.Ty.ArgumentList.Count != udt.ArgumentList.Count)
                                continue;
                            foundMatch = true;
                            foreach (var arg in udt.ArgumentList)
                            {
                                if (!IsDefinedType(arg))
                                {
                                    foundMatch = false;
                                }
                            }
                            if (!foundMatch)
                            {
                                continue;
                            }
                            udt.TypeDeclaration = typeDecl;
                            break;
                        }
                    }
                    if (entity is StructDecl)
                    {
                        var structDecl = (StructDecl)entity;
                        if (structDecl.Name.Name.ToLower() == udt.Name.Name.ToLower())
                        {
                            foundMatch = true;
                            udt.TypeDeclaration = structDecl;
                            break;
                        }
                    }
                }
                if (!foundMatch && Parent != null)
                {
                    return Parent.IsDefinedType(type);
                }
                else
                {
                    return foundMatch;
                }
            }
            else if (type is PredefinedType)
            {
                return true;
            }
            else if (type is PointerType)
            {
                return IsDefinedType((type as PointerType).EntityType);
            }
            else if (type is SeqType)
            {
                return IsDefinedType((type as SeqType).EntityType);
            }
            else if (type is SetType)
            {
                return IsDefinedType((type as SetType).EntityType);
            }
            else if (type is MapType)
            {
                return IsDefinedType((type as MapType).KeyType) && IsDefinedType((type as MapType).EntityType);
            }
            else if (type is TypeSuffix)
            {
                return IsDefinedType((type as TypeSuffix).EntityType);
            }
            else
            {
                throw new ArgumentException($"Unknown type {type.ToString(0)}");
            }
        }

        /// <summary>This function returns the variable declaration of the given identifier.</summary>
        /// <param name="ident">The name of the identifier to be looked up.</param>
        /// <param name="shallowLookup">If true, it will only look up at the declarations in this scope.
        /// Otherwise, it will look up all the way to parent(s).</param>
        public VarDecl GetVariableDecl(Ident ident, bool shallowLookup)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is BoundVarDecl)
                {
                    var bv = entity as BoundVarDecl;
                    if (bv.Name.Name == ident.Name)
                    {
                        return bv;
                    }
                }
                else if (entity is VarDecl)
                {
                    var vd = entity as VarDecl;
                    if (vd.Name.Name == ident.Name)
                    {
                        return vd;
                    }
                }
                else if (entity is Parameter)
                {
                    var pr = entity as Parameter;
                    if (pr.Name.Name == ident.Name)
                    {
                        return pr;
                    }
                }
            }
            if (shallowLookup == false && Parent != null)
            {
                return Parent.GetVariableDecl(ident, shallowLookup);
            }
            return null;
        }

        public StructDecl GetStructDecl(string name)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is StructDecl)
                {
                    var structDecl = entity as StructDecl;
                    if (structDecl.Name.Name.ToLower() == name.ToLower())
                    {
                        return structDecl;
                    }
                }
            }
            if (Parent != null)
            {
                return Parent.GetStructDecl(name);
            }
            return null;
        }

        public DatatypeDecl GetDatatypeDecl(string name)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is DatatypeDecl)
                {
                    var datatypeDecl = entity as DatatypeDecl;
                    if (datatypeDecl.Ty.Name.Name.ToLower() == name.ToLower())
                    {
                        return datatypeDecl;
                    }
                }
            }
            if (Parent != null)
            {
                return Parent.GetDatatypeDecl(name);
            }
            return null;
        }

        public DatatypeMemberDecl GetDatatypeMemberDecl(string name)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is DatatypeMemberDecl)
                {
                    var datatypeMemberDecl = entity as DatatypeMemberDecl;
                    if (datatypeMemberDecl.Name.Name == name)
                    {
                        return datatypeMemberDecl;
                    }
                }
            }
            if (Parent != null)
            {
                return Parent.GetDatatypeMemberDecl(name);
            }
            return null;
        }

        public MemberDecl GetMemberDecl(Ident ident, bool shallowLookup, List<Type> argTypes)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is MemberDecl)
                {
                    var md = entity as MemberDecl;
                    if (md.Name.Name == ident.Name)
                    {
                        if (md is MethodDecl)
                        {
                            var methodDecl = md as MethodDecl;
                            if (methodDecl.Args.Count == argTypes.Count)
                            {
                                bool match = true;
                                for (int j = 0; j < methodDecl.Args.Count; j++)
                                {
                                    // TODO: change to compatible type
                                    if (methodDecl.Args[j].Ty.ToString(0) != argTypes[j].ToString(0))
                                    {
                                        match = false;
                                        break;
                                    }
                                }
                                if (match)
                                {
                                    return methodDecl;
                                }
                            }
                        }
                        else if (md is InvariantDecl || md is YieldPredicateDecl)
                        {
                            if (argTypes.Count == 1 && argTypes[0].ToString(0) == "bool")
                            {
                                return md;
                            }
                        }
                    }
                }
            }
            if (shallowLookup == false && Parent != null)
            {
                return Parent.GetMemberDecl(ident, shallowLookup, argTypes);
            }
            return null;
        }

        public Statement GetLabelStatement(Ident ident)
        {
            for (int i = DefinedEntities.Count - 1; i >= 0; i--)
            {
                var entity = DefinedEntities[i];
                if (entity is Statement)
                {
                    var stmt = entity as Statement;
                    if (stmt.Label.Name == ident.Name)
                    {
                        return stmt;
                    }
                }
            }
            return null;
        }
    }
}
