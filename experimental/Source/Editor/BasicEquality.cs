using System.Collections.Generic;
using Microsoft.Starmada;

namespace Editor
{
    public class IdentEq : IEqualityComparer<Ident>
    {
        public bool Equals(Ident x, Ident y)
        {
            return x.Name == y.Name;
        }

        public int GetHashCode(Ident obj)
        {
            return obj.Name.GetHashCode();
        }
    }
    public class IdentStrEq : IEqualityComparer<IdentStr>
    {
        public bool Equals(IdentStr x, IdentStr y)
        {
            return x.Str == y.Str;
        }

        public int GetHashCode(IdentStr obj)
        {
            return obj.Str.GetHashCode();
        }
    }
    public class ExprEq : IEqualityComparer<Expr>
    {
        public bool Equals(Expr x, Expr y)
        {
            return x.ToString(0, false) == y.ToString(0, false);
        }

        public int GetHashCode(Expr obj)
        {
            return obj.GetHashCode();
        }
    }
}
