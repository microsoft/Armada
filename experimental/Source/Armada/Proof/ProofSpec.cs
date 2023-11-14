using System;
using System.Collections.Generic;
using System.Linq;


namespace Microsoft.Starmada
{
    public class ProofSpec
    {
        public AtomicSpec LS;
        public AtomicSpec HS;
        
        public ProofSpec(LevelDecl L, LevelDecl H)
        {
            LS = new AtomicSpec(L);
            HS = new AtomicSpec(H);
        }
    }

    public class WeakeningProofSpec : ProofSpec
    {
        public List<string> WeakeningTrans;
        public List<int> WeakeningUpdateIndices;

        public WeakeningProofSpec(LevelDecl L, LevelDecl H)
        : base(L, H)
        {
            WeakeningUpdateIndices = new();
            WeakeningTrans = GetWeakeningTrans();
        }

        public List<string> GetWeakeningTrans()
        {
            List<string> trans = new();
            List<ExecutionPathScheme> Lseqs = LS.Sequences;
            List<ExecutionPathScheme> Hseqs = HS.Sequences;
            // assert Lseqs.Count == Hseqs.Count
            int Nseqs = Lseqs.Count;
            for (int i = 0; i < Nseqs; i++) {
                List<FStarStmt> LAtomicBlock = Lseqs[i].Stmts;
                List<FStarStmt> HAtomicBlock = Hseqs[i].Stmts;
                // assert LAtomicBlock.Count == HAtomicBlock.Count
                int Nstmts = LAtomicBlock.Count;
                int firstdiff = -1;
                for (int j = 0; j < Nstmts; j++) {
                    if (LAtomicBlock[j] != HAtomicBlock[j]) {
                        firstdiff = j;
                        break;
                    }
                }
                string same = "ArmadaWeakeningTransformerSameStep {0}";
                string update = "ArmadaWeakeningTransformerUpdatedStep my_special_case_action_{0} my_special_case_steps_updater_{0} my_special_case_steps_updater_works_{0}";
                if (firstdiff == -1) { // The same atomic sequences
                    for (int k = 0; k <= Nstmts; k++) {
                        trans.Add(string.Format(same, trans.Count));
                    }
                } else {
                    WeakeningUpdateIndices.Add(trans.Count);
                    trans.Add(string.Format(update, trans.Count));
                    for (int k = 0; k < Nstmts; k++) {
                        if (k < firstdiff) {
                            trans.Add(string.Format(same, trans.Count));
                        } else {
                            WeakeningUpdateIndices.Add(trans.Count);
                            trans.Add(string.Format(update, trans.Count));
                        }
                    }
                }
            }
            return trans;
        }
    }

    public class VarIntroProofSpec: ProofSpec
    {
        public List<FStarStmt> VarIntroStmts;
        public Dictionary<FStarStmt, FStarStmt> FstmtMap; // L statement to H statement
        public Dictionary<string, string> PCMap; // Map from hpc to lpc
        public Dictionary<string, List<string>> ReversePCMap; // Map from lpc to hpc
        public Dictionary<ExecutionPathScheme, ExecutionPathScheme> SequenceMap; // H sequence to L sequence
        public Dictionary<ExecutionPathScheme, ExecutionPathScheme> ReverseSequenceMap; // L sequence to H sequence
        public Dictionary<string, ExecutionPathScheme> IntroPCs; // PC in a introduced atomic block
        public Dictionary<ExecutionPath, ExecutionPath> ActionMap; // L Action to H Action

        public VarIntroProofSpec(LevelDecl L, LevelDecl H)
        : base(L, H)
        {
            VarIntroStmts = GetVarIntroStmts();
            InitMaps();
            InitAtomicSequenceMap();
            InitActionMap();
        }

        private void InitMaps()
        {
            FstmtMap = new();
            PCMap = new();
            ReversePCMap = new();
            int i = 0, j = 0;
            while (i < LS.Fstmts.Count && j < HS.Fstmts.Count)
            {
                FStarStmt lfstmt = LS.Fstmts[i];
                FStarStmt hfstmt = HS.Fstmts[j];
                if (VarIntroStmts.Contains(hfstmt))
                {
                    j++;
                    continue;
                }
                // TODO: Error checking, whether these two statement matches
                FstmtMap[lfstmt] = hfstmt;
                if (hfstmt.StartPC != null && hfstmt.EndPC != null) {
                    PCMap[hfstmt.StartPC] = lfstmt.StartPC;
                    PCMap[hfstmt.EndPC] = lfstmt.EndPC;
                }
                i++;
                j++;
            }
            foreach (FStarStmt introStmt in VarIntroStmts)
            {
                if (!PCMap.ContainsKey(introStmt.EndPC)) {
                    if (PCMap.ContainsKey(introStmt.StartPC)) {
                        PCMap[introStmt.EndPC] = PCMap[introStmt.StartPC];
                    }
                }
                if (!PCMap.ContainsKey(introStmt.StartPC)) {
                    if (PCMap.ContainsKey(introStmt.EndPC)) {
                        PCMap[introStmt.StartPC] = PCMap[introStmt.EndPC];
                    }
                }
            }
            foreach (var kv in PCMap)
            {
                string lpc = kv.Value;
                string hpc = kv.Key;
                if (!ReversePCMap.ContainsKey(lpc)) {
                    ReversePCMap[lpc] = new();
                }
                ReversePCMap[lpc].Add(hpc);
            }
        }

        private void InitAtomicSequenceMap()
        {
            SequenceMap = new();
            ReverseSequenceMap = new();
            Dictionary<(string, string), List<ExecutionPathScheme>> patternMap = new(); // atomic sequence pattern for level L
            IntroPCs = new();
            foreach (var sequence in LS.Sequences)
            {
                var fstmts = sequence.Stmts;
                if (fstmts[0].StartPC == null) continue;
                var pattern = (fstmts[0].StartPC, fstmts[fstmts.Count - 1].EndPC);
                if (!patternMap.ContainsKey(pattern))
                    patternMap[pattern] = new();
                patternMap[pattern].Add(sequence);
            }
            foreach (var sequence in HS.Sequences)
            {
                var fstmts = sequence.Stmts;
                if (fstmts[0].StartPC == null) continue;
                var pattern = (PCMap[fstmts[0].StartPC], PCMap[fstmts[fstmts.Count - 1].EndPC]);
                if (patternMap.ContainsKey(pattern) && patternMap[pattern].Count > 0)
                {
                    var lseq = patternMap[pattern][0];
                    SequenceMap[sequence] = lseq;
                    ReverseSequenceMap[lseq] = sequence;
                    patternMap[pattern].Remove(lseq);
                }
                else // Introduced atomic block, add the first PC
                {
                    IntroPCs[fstmts[0].StartPC] = sequence;
                }
            }
        }

        private void InitActionMap()
        {
            ActionMap = new();
            // Add the PropagateWriteMessageStatement
            ActionMap[LS.Actions[0]] = HS.Actions[0];
            ActionMap[LS.Actions[1]] = HS.Actions[1];
            foreach (var kv in ReverseSequenceMap)
            {
                var lseq = kv.Key;
                var hseq = kv.Value;
                foreach (var laction in lseq.Paths)
                {
                    // All success to all success
                    if (!laction.FailAtTheEnd)
                    {
                        ActionMap[laction] = hseq.Paths[0];
                    }
                    else
                    {
                        FStarStmt llast = laction.Stmts[laction.Stmts.Count - 1];
                        FStarStmt hlast = FstmtMap[llast];
                        ActionMap[laction] = hseq.Paths[hseq.Stmts.IndexOf(hlast) + 1];
                    }
                }
            }
            // foreach (var kv in ActionMap)
            // {
            //     var laction = kv.Key;
            //     var haction = kv.Value;
            //     AtomicPrinter ap = new();
            //     Console.Write("Action Map:\n");
            //     Console.Write(ap.ToFStarAtomic(laction, 0) + '\n');
            //     Console.Write(ap.ToFStarAtomic(haction, 0) + '\n');
            // }
        }

        public List<FStarStmt> GetVarIntroStmts()
        {
            List<FStarStmt> varIntroStmts = new();
            HashSet<string> lupdates = new();
            foreach (var fstmt in LS.Fstmts)
            {
                string actualstmt = fstmt.Statement;
                if (!actualstmt.StartsWith("UpdateStatement"))
                    continue;
                lupdates.Add(actualstmt);
            }
            foreach (var fstmt in HS.Fstmts)
            {
                string actualstmt = fstmt.Statement;
                if (!actualstmt.StartsWith("UpdateStatement"))
                    continue;
                if (!lupdates.Contains(actualstmt))
                {
                    varIntroStmts.Add(fstmt);
                }
            }
            return varIntroStmts;
        }

        public List<FStarStmt> GetNonConstStmts()
        {
            List<FStarStmt> nonConstStmts = new();
            foreach (FStarStmt fstmt in VarIntroStmts)
            {
                string actualstmt = fstmt.Statement;
                int startIdx = actualstmt.IndexOf("(ExpressionConstant");
                int endIdx = actualstmt.LastIndexOf(')');
                if (startIdx == -1)
                {
                    nonConstStmts.Add(fstmt);
                    continue;
                }
                string rhs = actualstmt.Substring(startIdx, endIdx - startIdx + 1);
                int left = actualstmt.Count(c => c == '(');
                int right = actualstmt.Count(c => c == ')');
                if (left != right)
                {
                    nonConstStmts.Add(fstmt);
                }
            }
            return nonConstStmts;
        }
    }
}