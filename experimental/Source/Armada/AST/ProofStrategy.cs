using System;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    public abstract class ProofStrategy : AstNode
    {
        public ProofStrategy(Token tok) : base(tok) { }
        
        // Proof strategies don't have program counter.
        public override void SetProgramCounter(string parentPC, int index) {
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
    }

    public class TSOElimStrategy : ProofStrategy
    {
        public Ident Id;

        public TSOElimStrategy(Token tok, Ident id) : base(tok)
        {
            this.Id = id;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "tso_elim " + Id.ToString(0, labelOn) + "\n";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return Id;
        }
    }

    public class WeakeningStrategy : ProofStrategy
    {
        public WeakeningStrategy(Token tok) : base(tok) { }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "weakening \n";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield break;
        }
    }

    public class CombiningStrategy : ProofStrategy
    {
        public Ident startLabel;
        public Ident endLabel;
        public Ident newLabel;
        public CombiningStrategy(Token tok, Ident startLabel, Ident endLabel, Ident newLabel) : base(tok)
        {
            this.startLabel = startLabel;
            this.endLabel = endLabel;
            this.newLabel = newLabel;
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "combining " +
              startLabel.ToString(0, labelOn) + " " +
              endLabel.ToString(0, labelOn) + " " +
              newLabel.ToString(0, labelOn);
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            yield return startLabel;
            yield return endLabel;
            yield return newLabel;
        }
    }

    public class AssumeIntroStrategy : ProofStrategy
    {
        public AssumeIntroStrategy(Token tok) : base(tok) { }
        
        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "assume_intro \n";
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
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

    public class VarIntroStrategy : ProofStrategy
    {
        public List<Ident> Variables;

        public VarIntroStrategy(Token tok) : base(tok)
        {
            Variables = new List<Ident>();
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "var_intro ";
            for (int i = 0; i < Variables.Count; i++)
            {
                str = str + Variables[i].ToString(0, labelOn);
                if (i != Variables.Count - 1)
                {
                    str = str + ", ";
                }
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var variable in Variables)
            {
                yield return variable;
            }
        }
    }

    public class VarHidingStrategy : ProofStrategy
    {
        public List<Ident> Variables;

        public VarHidingStrategy(Token tok) : base(tok)
        {
            Variables = new List<Ident>();
        }

        public override string ToString(int indentation, bool labelOn)
        {
            string str = "";
            string indentationStr = new string(' ', indentation);
            str = str + indentationStr + "var_hiding ";
            for (int i = 0; i < Variables.Count; i++)
            {
                str = str + Variables[i].ToString(0, labelOn);
                if (i != Variables.Count - 1)
                {
                    str = str + ", ";
                }
            }
            return str;
        }
        public override void TypeResolve(Type enforcingType, ref Errors errors)
        {
            // TODO: Implement this function
        }
        public override string ToFStarLang(int indentation)
        {
            throw new NotImplementedException();
        }
        public override IEnumerable<AstNode> AllChildren()
        {
            foreach (var variable in Variables)
            {
                yield return variable;
            }
        }
    }
}
