using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Starmada
{
    public class Util
    {
        /// <summary>
        /// For "S" returns S and false.
        /// For @"S" return S and true.
        /// Assumes that s has one of these forms.
        /// </summary>
        public static string RemoveParsedStringQuotes(string s, out bool isVerbatimString)
        {
            Contract.Requires(s != null);
            var len = s.Length;
            if (s[0] == '@') {
                isVerbatimString = true;
                return s.Substring(2, len - 3);
            } else {
                isVerbatimString = false;
                return s.Substring(1, len - 2);
            }
        }

        public static string ListExprsToString(List<Expr> elements, bool labelOn, string sperator = ", ")
        {
            List<string> elementsStr = new List<string>();
            foreach (Expr expr in elements)
            {
                elementsStr.Add(expr.ToString(0, labelOn));
            }
            return string.Join(sperator, elementsStr);
        }

        public static string ListIdentsToString(List<Ident> idents, bool labelOn, string sperator = ", ")
        {
            List<string> elementsStr = new List<string>();
            foreach (Ident ident in idents)
            {
                elementsStr.Add(ident.ToString(0, labelOn));
            }
            return string.Join(sperator, elementsStr);
        }

        public static void CheckLowerCase(Ident ident, ref Errors errors)
        {
            if (ident.Name.ToLower() != ident.Name)
            {
                errors.SynErr(ident.FirstTok.line, ident.FirstTok.col, "type must be lower case!");
            }
        }
    }
}

