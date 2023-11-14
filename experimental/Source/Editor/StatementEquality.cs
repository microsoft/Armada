using System.Collections.Generic;
using Microsoft.Starmada;

namespace Editor
{
    public class SyntacticEq : EqualityComparer<Statement>
    {
        public SyntacticEq() { }
        public override bool Equals(Statement x, Statement y)
        {
            return x.ToString(0, false) == y.ToString(0, false);
        }
        public override int GetHashCode(Statement s)
        {
            return s.GetHashCode();
        }
    }

    public class FallbackEq : SyntacticEq { }

    public class VarIntroEq : EqualityComparer<Statement>
    {
        public List<Ident> Variables;
        public VarIntroEq(VarIntroStrategy vis)
        {
            Variables = vis.Variables;
        }
        public override bool Equals(Statement x, Statement y)
        {
            if (y is VarDecl && Variables.Contains(((VarDecl)y).Name))
            {
                return false;
            }
            return new SyntacticEq().Equals(x, y);
        }
        public override int GetHashCode(Statement s)
        {
            return s.GetHashCode();
        }
    }

    public class VarHidingEq : EqualityComparer<Statement>
    {
        public List<Ident> Variables;
        public VarHidingEq(VarHidingStrategy vis)
        {
            Variables = vis.Variables;
        }
        public override bool Equals(Statement x, Statement y)
        {
            if (x is VarDecl && Variables.Contains(((VarDecl)x).Name))
            {
                return false;
            }
            return new SyntacticEq().Equals(x, y);
        }
        public override int GetHashCode(Statement s)
        {
            return s.GetHashCode();
        }
    }

    public class TSOElimEq : EqualityComparer<Statement>
    {
        public TSOElimEq() { }
        public override bool Equals(Statement x, Statement y)
        {
            if (x is AssignStatement && y is AssignStatement)
            {
                AssignStatement x_ = x as AssignStatement;
                AssignStatement y_ = y as AssignStatement;
                if (!x_.IsSequential && y_.IsSequential)
                {
                    if (new ExprEq().Equals(x_.Lhs, y_.Lhs) &&
                        new ExprEq().Equals(x_.Rhs, y_.Rhs))
                    {
                        return true;
                    }
                }
            }
            return new SyntacticEq().Equals(x, y);
        }

        public override int GetHashCode(Statement s)
        {
            return s.GetHashCode();
        }
    }

    public class AssumeIntroEq : SyntacticEq { }
    // public class ReductionEq : SyntacticEq { }
    public class WeakeningEq : SyntacticEq { }
    public class CombiningEq : SyntacticEq { }
    // public class StarWeakeningEq : SyntacticEq { }
}
