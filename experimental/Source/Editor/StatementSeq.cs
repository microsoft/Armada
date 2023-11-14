using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Starmada;
using Type = Microsoft.Starmada.Type;

namespace Editor
{
    public class StatementSeq : IList<Statement>
    {
        public abstract class DelimiterStatement : Statement
        {
            public DelimiterStatement(Token tok) : base(tok) { }
            public override void TypeResolve(Type type, ref Errors errors) { throw new NotImplementedException(); }
            public override void SetProgramCounter(string parentPC, int index) { throw new NotImplementedException(); }
            public override void SetNextProgramCounter(string nextPC) { throw new NotImplementedException(); }
            public override string ToFStarLang(int indentation) { throw new NotImplementedException(); }
        }
        public class AtomicBegin : DelimiterStatement
        {
            public AtomicBegin(AtomicStatement stmt) : base(stmt.FirstTok)
            {
                LastTok = stmt.BlockStmt.FirstTok;
                Label = stmt.Label;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                if (Label != null && labelOn)
                {
                    str = str + indentationStr + base.ToString(0, labelOn) + "\n";
                }
                str = str + indentationStr + "atomic" + "\n";
                str = str + indentationStr + "{";
                return str;
            }
        }
        public class AtomicEnd : DelimiterStatement
        {
            public AtomicEnd(AtomicStatement stmt) : base(stmt.FirstTok)
            {
                FirstTok = stmt.LastTok;
                LastTok = FirstTok;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                str = str + indentationStr + "}";
                return str;
            }
        }
        public List<Statement> FlattenAtomic(AtomicStatement atomicStatement)
        {
            List<Statement> res = new List<Statement>();
            res.Add(new AtomicBegin(atomicStatement));
            res.AddRange(FlattenBlock(atomicStatement.BlockStmt));
            res.Add(new AtomicEnd(atomicStatement));
            return res;
        }
        public class IfBegin : DelimiterStatement
        {
            public Expr Cond;
            public IfBegin(IfStatement stmt) : base(stmt.FirstTok)
            {
                Cond = stmt.Cond;
                LastTok = stmt.Then.FirstTok;
                Label = stmt.Label;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                if (Label != null && labelOn)
                {
                    str = str + indentationStr + base.ToString(0, labelOn) + "\n";
                }
                str = str + indentationStr + "if " + Cond.ToString(0, labelOn) + "\n";
                str = str + indentationStr + "{";
                return str;
            }
        }
        public class Else : DelimiterStatement
        {
            public Else(IfStatement stmt) : base(stmt.FirstTok)
            {
                FirstTok = stmt.Then.LastTok;
                LastTok = stmt.Else.FirstTok;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                str = str + indentationStr + "}" + "\n";
                str = str + indentationStr + "else" + "\n";
                str = str + indentationStr + "{";
                return str;
            }
        }
        public class IfEnd : DelimiterStatement
        {
            public IfEnd(IfStatement stmt) : base(stmt.FirstTok)
            {
                FirstTok = stmt.LastTok;
                LastTok = FirstTok;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                str = str + indentationStr + "}";
                return str;
            }
        }
        public List<Statement> FlattenIf(IfStatement ifStatement)
        {
            List<Statement> res = new List<Statement>();
            res.Add(new IfBegin(ifStatement));
            res.AddRange(FlattenBlock(ifStatement.Then));
            if (ifStatement.Else is not null)
            {
                res.Add(new Else(ifStatement));
                res.AddRange(Flatten(ifStatement.Else));
            }
            res.Add(new IfEnd(ifStatement));
            return res;
        }
        public class WhileBegin : DelimiterStatement
        {
            public Expr Cond;
            public WhileBegin(WhileBlock stmt) : base(stmt.FirstTok)
            {
                Cond = stmt.Cond;
                LastTok = stmt.BlockStmt.FirstTok;
                Label = stmt.Label;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                if (Label != null && labelOn)
                {
                    str = str + indentationStr + base.ToString(0, labelOn) + "\n";
                }
                str = str + indentationStr + "while " + Cond.ToString(0, labelOn) + "\n";
                str = str + indentationStr + "{";
                return str;
            }
        }
        public class WhileEnd : DelimiterStatement
        {
            public WhileEnd(WhileBlock stmt) : base(stmt.FirstTok)
            {
                FirstTok = stmt.BlockStmt.LastTok;
                LastTok = FirstTok;
            }
            public override string ToString(int indentation, bool labelOn)
            {
                string str = "";
                string indentationStr = new string(' ', indentation);
                str = str + indentationStr + "}";
                return str;
            }
        }
        public List<Statement> FlattenWhile(WhileBlock whileBlock)
        {
            List<Statement> res = new List<Statement>();
            res.Add(new WhileBegin(whileBlock));
            res.AddRange(FlattenBlock(whileBlock.BlockStmt));
            res.Add(new WhileEnd(whileBlock));
            return res;
        }
        public List<Statement> FlattenBlock(BlockStatement blockStatement)
        {
            List<Statement> res = blockStatement.Stmts.SelectMany(stmt => Flatten(stmt)).ToList();
            return res;
        }
        public List<Statement> Flatten(Statement stmt)
        {
            List<Statement> res = new List<Statement>();
            if (stmt is BlockStatement s1)
            {
                res.AddRange(FlattenBlock(s1));
            }
            else if (stmt is IfStatement s2)
            {
                res.AddRange(FlattenIf(s2));
            }
            else if (stmt is WhileBlock s3)
            {
                res.AddRange(FlattenWhile(s3));
            }
            else if (stmt is AtomicStatement s4)
            {
                res.AddRange(FlattenAtomic(s4));
            }
            else
            {
                res.Add(stmt);
            }
            return res;
        }

        public int IndexOf(Statement item)
        {
            return ((IList<Statement>)Sequence).IndexOf(item);
        }

        public void Insert(int index, Statement item)
        {
            ((IList<Statement>)Sequence).Insert(index, item);
        }

        public void RemoveAt(int index)
        {
            ((IList<Statement>)Sequence).RemoveAt(index);
        }

        public void Add(Statement item)
        {
            ((ICollection<Statement>)Sequence).Add(item);
        }

        public void Clear()
        {
            ((ICollection<Statement>)Sequence).Clear();
        }

        public bool Contains(Statement item)
        {
            return ((ICollection<Statement>)Sequence).Contains(item);
        }

        public void CopyTo(Statement[] array, int arrayIndex)
        {
            ((ICollection<Statement>)Sequence).CopyTo(array, arrayIndex);
        }

        public bool Remove(Statement item)
        {
            return ((ICollection<Statement>)Sequence).Remove(item);
        }

        public IEnumerator<Statement> GetEnumerator()
        {
            return ((IEnumerable<Statement>)Sequence).GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return ((IEnumerable)Sequence).GetEnumerator();
        }

        // SeqStatement
        public List<Statement> Sequence;

        public int Count => ((ICollection<Statement>)Sequence).Count;

        public bool IsReadOnly => ((ICollection<Statement>)Sequence).IsReadOnly;

        public Statement this[int index] { get => ((IList<Statement>)Sequence)[index]; set => ((IList<Statement>)Sequence)[index] = value; }

        public StatementSeq(List<Statement> seq)
        {
            Sequence = seq.SelectMany(stmt => Flatten(stmt)).ToList();
        }
    }
}
