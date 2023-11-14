using System.Collections.Generic;
using Microsoft.Starmada;

namespace Editor
{
    public class ProjectSummary
    {
        // Stores LevelInfo
        public Dictionary<IdentStr, LevelInfo> LevelInfoDict { get; set; }

        // Stores the result StatementSeqs
        public List<LevelSummary> LevelSummaryChain { get; set; }

        // Stores the Proof
        public List<ProofSummary> ProofSummaryChain { get; set; }


        public ProjectSummary()
        {
            LevelInfoDict = new(new IdentStrEq());
            LevelSummaryChain = new();
            ProofSummaryChain = new();
        }

        public LevelSummary GetLevelSummary(IdentStr levelName)
        {
            return LevelSummaryChain[LevelInfoDict[levelName].ChainIdx];
        }

        public StmtToken GetStmtToken(StmtLoc loc)
        {
            LevelInfo lvInfo = LevelInfoDict[loc.Level];
            Statement stmt = LevelSummaryChain[lvInfo.ChainIdx].MethodCollection[loc.Method][loc.StmtIdx];
            return new StmtToken(lvInfo.File, stmt.FirstTok, stmt.LastTok);
        }
    }

    public class LevelSummary
    {
        public IdentStr Name;
        public Dictionary<IdentStr, StatementSeq> MethodCollection;
        public LevelSummary(LevelDecl level)
        {
            Name = new(level.Name);
            MethodCollection = new Dictionary<IdentStr, StatementSeq>(new IdentStrEq());
            foreach (var member in level.Members)
            {
                if (member is MethodDecl method)
                {
                    MethodCollection.Add(new(method.Name), new StatementSeq(method.Stmts));
                }
            }
        }
    }

    public class ProofSummary
    {
        public IdentStr Name;
        public ProofStrategy Strategy;
        public ProofSummary(ProofDecl proof)
        {
            Name = new(proof.Name);
            Strategy = proof.Strategy;
        }
    }
}