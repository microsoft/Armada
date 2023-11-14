using System.Collections.Generic;
using System.Linq;
using Microsoft.Starmada;

namespace Editor
{
    class Mapper
    {
        public ProjectSummary Project;
        public LevelRange Range;
        private Dictionary<IdentStr, Diff<StatementSeq, Statement>>[] diffs;

        public Mapper(ProjectSummary proj, LevelRange range)
        {
            Project = proj;
            Range = range;
            diffs = new Dictionary<IdentStr, Diff<StatementSeq, Statement>>[Project.LevelSummaryChain.Count - 1];
        }

        protected EqualityComparer<Statement> EqualityPicker(ProofSummary proof)
        {
            ProofStrategy ps = proof.Strategy;
            if (ps is TSOElimStrategy) return new TSOElimEq();
            if (ps is WeakeningStrategy) return new WeakeningEq();
            // Starweakening - currently not in parser
            if (ps is CombiningStrategy) return new CombiningEq();
            if (ps is AssumeIntroStrategy) return new AssumeIntroEq();
            // Reduction - currently not in parser
            if (ps is VarIntroStrategy vi_ps) return new VarIntroEq(vi_ps);
            if (ps is VarHidingStrategy vh_ps) return new VarHidingEq(vh_ps);
            return new FallbackEq();
        }

        private Diff<StatementSeq, Statement> getDiff(int lower_idx, IdentStr method)
        {
            Dictionary<IdentStr, Diff<StatementSeq, Statement>> diff_lv = diffs[lower_idx];
            if (diff_lv is null)
            {
                diff_lv = new();
            }
            if (!diff_lv.TryGetValue(method, out Diff<StatementSeq, Statement> diff_method))
            {
                diff_method = null;
                diff_lv.Add(method, diff_method);
            }
            if (diff_method is null)
            {
                int i = lower_idx;
                StatementSeq curSeq = Project.LevelSummaryChain[i].MethodCollection[method];
                StatementSeq nextSeq = Project.LevelSummaryChain[i + 1].MethodCollection[method];
                ProofSummary proof = Project.ProofSummaryChain[i];
                Diff<StatementSeq, Statement> diff = new(
                    curSeq,
                    nextSeq,
                    EqualityPicker(proof)
                );
                diff_method = diff;
            }
            return diff_method;
        }

        private List<StmtLoc> IdentifyByStatement(StmtLoc loc)
        {
            LevelInfo llv = Project.LevelInfoDict[Range.LLevel];
            LevelInfo hlv = Project.LevelInfoDict[Range.HLevel];
            LevelInfo lv = Project.LevelInfoDict[loc.Level];
            bool valid = llv.ChainIdx <= lv.ChainIdx && lv.ChainIdx <= hlv.ChainIdx;
            if (!valid)
            {
                throw new FatalError(
                    $"Incorrect level dependency: requiring {Range.LLevel} <= {loc.Level} <= {Range.HLevel}"
                );
            }
            // Check if method appears in all levels
            for (int i = llv.ChainIdx; i <= hlv.ChainIdx; i++)
            {
                LevelSummary lvSummary = Project.LevelSummaryChain[i];
                if (!lvSummary.MethodCollection.ContainsKey(loc.Method))
                {
                    throw new FatalError(
                        $"Method {loc.Method} not found in {lvSummary.Name}"
                    );
                }
            }

            List<int> mapping = new List<int>();
            if (Project.LevelSummaryChain[lv.ChainIdx].MethodCollection[loc.Method].Count <= loc.StmtIdx)
            {
                throw new FatalError(
                    $"Statement index {loc.StmtIdx} in level {loc.Level} method {loc.Method} out of bound."
                );
            }
            mapping.Add(loc.StmtIdx);

            // Lower level propagation
            for (int i = lv.ChainIdx; i > llv.ChainIdx; i--)
            {
                Diff<StatementSeq, Statement> diff = getDiff(i - 1, loc.Method);
                int prevIdx = diff.MapExactBackward(mapping.Last());
                // Invalid idx
                if (prevIdx < 0)
                {
                    IdentStr levelName = Project.LevelSummaryChain[i - 1].Name;
                    throw new FatalError(
                        $"Propagation failed in level {levelName} method {loc.Method}."
                    );
                }
                mapping.Add(prevIdx);
            }

            // Reverse indexChain to perform forward propagation
            mapping.Reverse();

            // Higher level propagation
            for (int i = lv.ChainIdx; i < hlv.ChainIdx; i++)
            {
                Diff<StatementSeq, Statement> diff = getDiff(i, loc.Method);
                int nextIdx = diff.MapExactForward(mapping.Last());
                // Invalid idx
                if (nextIdx < 0)
                {
                    IdentStr levelName = Project.LevelSummaryChain[i + 1].Name;
                    throw new FatalError(
                        $"Propagation failed in level {levelName} method {loc.Method}."
                    );
                }
                mapping.Add(nextIdx);
            }

            List<StmtLoc> res = new List<StmtLoc>();
            for (int i = llv.ChainIdx, j = 0; i <= hlv.ChainIdx; i++, j++)
            {
                res.Add(new StmtLoc(Project.LevelSummaryChain[i].Name, loc.Method, mapping[j]));
            }

            return res;
        }

        private static List<List<T>> transpose<T>(List<List<T>> source, int arity)
        {
            // init
            List<List<T>> res = new();
            // transpose
            for (int i = 0; i < arity; i++)
            {
                List<T> l = new();
                for (int j = 0; j < source.Count; j++)
                {
                    l.Add(source[j][i]);
                }
                res.Add(l);
            }
            return res;
        }

        public List<StmtGroupLoc> IdentifyByStatementSelection(StmtRangeLoc rangeLoc)
        {
            List<List<StmtLoc>> locMat = new();
            int arity = -1;
            for (int idx = rangeLoc.StmtIdx; idx <= rangeLoc.StmtEndIdx; idx++)
            {
                var locs = IdentifyByStatement(new StmtLoc(rangeLoc.Level, rangeLoc.Method, idx));
                if (arity == -1)
                {
                    arity = locs.Count;
                }
                else if (arity != locs.Count)
                {
                    throw new FatalError("Arity mismatch between levels.");
                }
                locMat.Add(locs);
            }
            // transpose
            List<List<StmtLoc>> locTrans = (List<List<StmtLoc>>)transpose(locMat, arity);

            List<StmtGroupLoc> groups = locTrans.Select(
                locs => new StmtGroupLoc(locs)
            ).ToList();
            return groups;
        }
    }
}
