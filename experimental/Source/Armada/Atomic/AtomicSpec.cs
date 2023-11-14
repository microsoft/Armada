using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Starmada
{
    public class ExecutionPath
    {
        public bool FailAtTheEnd;
        public List<FStarStmt> Stmts;

        public ExecutionPath(bool failAtEnd, List<FStarStmt> stmts)
        {
            FailAtTheEnd = failAtEnd;
            Stmts = stmts;
        }
    }
    public class ExecutionPathScheme
    {
        public List<FStarStmt> Stmts;
        public List<ExecutionPath> Paths;
        public ExecutionPathScheme(List<FStarStmt> stmts)
        {
            Stmts = new List<FStarStmt>(stmts);
            Debug.Assert(Stmts.Count != 0);
        }
        public ExecutionPathScheme(FStarStmt stmt)
        {
            Stmts = new List<FStarStmt>();
            Stmts.Add(stmt);
        }
        public List<ExecutionPath> IterateStatements()
        {
            if (Paths == null)
            {
                Paths = new List<ExecutionPath>();
                Paths.Add(new ExecutionPath(false, Stmts));
                for (int i = 1; i <= Stmts.Count; i++)
                {
                    List<FStarStmt> fstmts = Stmts.Take(i).ToList();
                    Paths.Add(new ExecutionPath(true, fstmts));
                }
            }
            return Paths;
        }
    }

    public class AtomicSpec
    {
        public string MainStartPC;
        public List<FStarStmt> Fstmts { get; set; } = null;
        public Dictionary<FStarStmt, int> StmtIndex { get; set; } = null;
        public List<ExecutionPathScheme> Sequences { get; set; } = null;
        public List<List<int>> AtomicToRegularMap { get; set; } = null;
        public List<List<int>> AtomicPathInfo { get; set; } = null;
        public Dictionary<string, List<FStarStmt>> PC2Stmt { get; set; } = null;
        public List<string> PCs { get; set; } = null;
        public Dictionary<string, int> PC2Index { get; set; } = null;
        public List<ExecutionPath> Actions { get; set; } = null;
        public HashSet<string> NormalBreakPoints { get; set; } = null;
        public HashSet<string> LoopBreakPoints { get; set; } = null;


        public AtomicSpec(LevelDecl level)
        {
            MainStartPC = level.MainStartPC;
            // Initialize Fstmts, Sequences, NormalBreakPoints
            if (Fstmts is null)
            {
                Fstmts = new();
                Fstmts.Add(new FStarStmt(null, null, true, true, "PropagateWriteMessageStatement"));
                foreach (MemberDecl member in level.Members)
                {
                    if (member is MethodDecl method)
                    {
                        Fstmts.AddRange(method.FStarStmts);
                    }
                }
            }
            if (StmtIndex is null)
            {
                StmtIndex = new();
                for (int i = 0; i < Fstmts.Count; i++)
                {
                    StmtIndex[Fstmts[i]] = i * 2;
                }
            }
            if (Sequences is null)
            {
                Sequences = new();
                Sequences.Add(new ExecutionPathScheme(Fstmts[0]));
                Sequences.AddRange(StatementsToPathSchemes(Fstmts));
            }
            if (Actions is null)
            {
                Actions = new();
                foreach (ExecutionPathScheme sequence in Sequences)
                {
                    Actions.AddRange(sequence.IterateStatements());
                }
            }
            if (PCs is null)
            {
                PCs = new();
                PC2Index = new();
                int i = 0;
                foreach (var kv in PC2Stmt)
                {
                    PCs.Add(kv.Key);
                    PC2Index[kv.Key] = i++;
                }
            }
        }

        public IEnumerable<ExecutionPathScheme> GetExecutionPathSchemes()
        {
            return Sequences;
        }

        public IEnumerable<ExecutionPathScheme> StatementsToPathSchemes(List<FStarStmt> fstmts)
        {
            List<ExecutionPathScheme> sequences = new();
            PC2Stmt = new();
            List<FStarStmt> path = new List<FStarStmt>();
            LoopBreakPoints = new();
            NormalBreakPoints = new();
            NormalBreakPoints.Add(MainStartPC);
            HashSet<string> discoveredPCs = new();
            foreach (FStarStmt fstmt in fstmts)
            {
                string PC = fstmt.StartPC;
                if (PC == null)
                    continue;
                if (!PC2Stmt.ContainsKey(PC))
                {
                    PC2Stmt[PC] = new List<FStarStmt>();
                }
                if (fstmt.EndPC != null && !PC2Stmt.ContainsKey(fstmt.EndPC))
                {
                    PC2Stmt[fstmt.EndPC] = new List<FStarStmt>();
                }
                PC2Stmt[PC].Add(fstmt);
            }
            // First traversal, finding the break points
            discoveredPCs.Add(MainStartPC);
            foreach (FStarStmt fstmt in PC2Stmt[MainStartPC])
            {
                path.Clear();
                findBreakPoints(fstmt);
            }
            discoveredPCs.Clear();
            discoveredPCs.Add(MainStartPC);
            // Second traversal, generate atomic sequences according to additional break points
            foreach (FStarStmt fstmt in PC2Stmt[MainStartPC])
            {
                path.Clear();
                dfs(fstmt);
            }
            return sequences;

            void findBreakPoints(FStarStmt fstmt)
            {
                if (fstmt.EndsAtomicBlock)
                {
                    if (discoveredPCs.Contains(fstmt.EndPC))
                        return;
                    discoveredPCs.Add(fstmt.EndPC);
                    List<FStarStmt> savedPath = new(path);
                    foreach (FStarStmt nextStmt in PC2Stmt[fstmt.EndPC])
                    {
                        // Deal with MethodCallStatement with stack_overflow true
                        if (nextStmt.StartsAtomicBlock) {
                            path.Clear();
                            findBreakPoints(nextStmt);
                        }
                    }
                    path = savedPath;
                }
                path.Add(fstmt);
                if (path.ConvertAll(fstmt => fstmt.StartPC).Contains(fstmt.EndPC)) // find backedge
                {
                    LoopBreakPoints.Add(fstmt.EndPC);
                }
                else
                {
                    List<FStarStmt> nextStmts = PC2Stmt[fstmt.EndPC];
                    Contract.Requires(nextStmts.Count > 0);
                    foreach (FStarStmt nextStmt in nextStmts)
                    {
                        findBreakPoints(nextStmt);
                    }
                }
                path.RemoveAt(path.Count - 1);
                return;
            }

            void dfs(FStarStmt fstmt)
            {
                path.Add(fstmt);
                if (fstmt.EndsAtomicBlock)
                {
                    sequences.Add(new ExecutionPathScheme(path));
                    if (discoveredPCs.Contains(fstmt.EndPC))
                        return;
                    discoveredPCs.Add(fstmt.EndPC);
                    NormalBreakPoints.Add(fstmt.EndPC);
                    List<FStarStmt> savedPath = new(path);
                    foreach (FStarStmt nextStmt in PC2Stmt[fstmt.EndPC])
                    {
                        if (nextStmt.StartsAtomicBlock) {
                            path.Clear();
                            dfs(nextStmt);
                        }
                    }
                    path = savedPath;
                }
                else if (LoopBreakPoints.Contains(fstmt.EndPC))
                {
                    if (path.ConvertAll(fstmt => fstmt.StartPC).Contains(fstmt.EndPC)) // loop backedge
                    {
                        sequences.Add(new ExecutionPathScheme(path));
                    }
                    else
                    {
                        List<FStarStmt> savedPath = new List<FStarStmt>(path);
                        sequences.Add(new ExecutionPathScheme(path));
                        foreach (FStarStmt nextStmt in PC2Stmt[fstmt.EndPC])
                        {
                            path.Clear();
                            dfs(nextStmt);
                        }
                        path = savedPath;
                    }
                }
                else
                {
                    List<FStarStmt> nextStmts = PC2Stmt[fstmt.EndPC];
                    Contract.Requires(nextStmts.Count > 0);
                    foreach (FStarStmt nextStmt in nextStmts)
                    {
                        dfs(nextStmt);
                    }
                }
                path.RemoveAt(path.Count - 1);
                return;
            }
        }

        public int GetFstmtIndex(FStarStmt fstmt, bool ok)
        {
            return StmtIndex[fstmt] + (ok ? 0 : 1);
        }
        public List<int> GetActionIndices(ExecutionPath action)
        {
            List<int> indices = new();
            foreach (FStarStmt fstmt in action.Stmts)
            {
                indices.Add(GetFstmtIndex(fstmt, true));
            }
            if (action.FailAtTheEnd)
            {
                indices[indices.Count - 1]  += 1;
            }
            return indices;
        }

        public List<List<int>> GetAtomicToRegularMap()
        {
            // [[0]; [1]; [2; 4; 6]; [3]; [2; 5]; [2; 4; 7]; [8]; [9]]
            List<List<int>> atomicToRegularMap = new();
            foreach (var action in Actions)
            {
                atomicToRegularMap.Add(GetActionIndices(action));
            }
            return atomicToRegularMap;
        }

        public int GetMapIndex(List<int> indices)
        {
            if (AtomicToRegularMap is null)
            {
                AtomicToRegularMap = GetAtomicToRegularMap();
            }
            for (int i = 0; i < AtomicToRegularMap.Count; i++)
            {
                if (indices.SequenceEqual(AtomicToRegularMap[i]))
                {
                    return i;
                }
            }
            return -1;
        }

        public List<string> GetAtomicPathInfo()
        {
            List<string> pathInfos = new();
            AtomicPathInfo = new();
            foreach (var sequence in Sequences)
            {
                var allfstmts = sequence.Stmts;
                for (int i = 1; i <= allfstmts.Count; i++)
                {
                    List<FStarStmt> fstmts = allfstmts.Take(i).ToList();
                    var okPath = new ExecutionPath(false, fstmts);
                    var failPath = new ExecutionPath(true, fstmts);

                    // ok == true
                    var okIndices = GetActionIndices(okPath);
                    AtomicPathInfo.Add(okIndices);
                    if (i == allfstmts.Count)
                    {
                        pathInfos.Add($"make_breaking_atomic_path_info [{String.Join("; ", okIndices)}] {GetMapIndex(okIndices)};");
                    }
                    else
                    {
                        var nextStmt = allfstmts[i];
                        int k = pathInfos.Count;
                        pathInfos.Add($"make_incomplete_atomic_path_info [{String.Join("; ", okIndices)}] [make_successor_info {GetFstmtIndex(nextStmt, true)} {k + 2}; make_successor_info {GetFstmtIndex(nextStmt, false)} {k + 3}];");
                    }
                    // ok == false
                    var indices = GetActionIndices(failPath);
                    AtomicPathInfo.Add(indices);
                    pathInfos.Add($"make_breaking_atomic_path_info [{String.Join("; ", indices)}] {GetMapIndex(indices)};");
                }
            }
            return pathInfos;
        }

        public List<int> GetSingletonPathIndices()
        {
            List<int> singleton = new();
            for (int i = 0; i < Fstmts.Count * 2; i++)
            {
                bool found = false;
                for (int j = 0; j < AtomicPathInfo.Count; j++)
                {
                    if (AtomicPathInfo[j].Count == 1 && AtomicPathInfo[j][0] == i)
                    {
                        found = true;
                        singleton.Add(j);
                        break;
                    }
                }
                if (!found)
                {
                    singleton.Add(-1);
                }
            }
            return singleton;
        }

        public int GetStartIndex()
        {
            return PC2Index[MainStartPC];
        }

        public string GetNonYieldingPCList()
        {
            return $"[{String.Join("; ", PCs.ConvertAll(pc => (!NormalBreakPoints.Contains(pc)).ToString().ToLower()))}]";
        }
        public string GetBreakPCList()
        {
            return $"[{String.Join("; ", PCs.ConvertAll(pc => (NormalBreakPoints.Contains(pc) || LoopBreakPoints.Contains(pc)).ToString().ToLower()))}]";
        }
        public delegate string StmtToString<Stmt>(Stmt stmt, int index, int indentation);
        public static string BinarySearchGen<Stmt>(List<Stmt> seq, StmtToString<Stmt> fmt, int indentation = 0)
        {
            return BinarySearchGen<Stmt>(seq, fmt, indentation, 0, seq.Count);
        }
        public static string BinarySearchGen<Stmt>(List<Stmt> seq, StmtToString<Stmt> fmt, int indentation, int a, int b)
        {
            string indent = new string(' ', indentation);
            string str = "";
            Debug.Assert(a <= b);
            if (a == b) { }
            else if (a + 1 == b)
            {
                str += $"{fmt(seq[a], a, indentation)}";
            }
            else
            {
                var l = BinarySearchGen(seq, fmt, indentation + 2, a, (a + b + 1) / 2);
                var r = BinarySearchGen(seq, fmt, indentation + 2, (a + b + 1) / 2, b);
                str += $"{indent}if n < {(a + b + 1) / 2} then (\n{l}\n{indent}) else (\n{r}\n{indent})";
            }
            return str;
        }
    }
}