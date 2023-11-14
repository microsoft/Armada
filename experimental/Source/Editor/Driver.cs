using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Starmada;

using StarmadaParser = Microsoft.Starmada.Parser;

namespace Editor
{
    public class Driver
    {
        // Project Root
        public string InputRoot;
        // Source files
        public List<string> InputFiles;

        // Caret with selection
        public StmtRangeLoc CaretRangeLoc;

        // Level range
        public LevelRange LevelRange;

        // ProjectSummary
        public ProjectSummary Project;

        public static bool PositionBetweenTokens(Token firstTok, Token lastTok, (int, int) position)
        {
            var (line, col) = position;
            bool afterFirstTok = (firstTok.line == line && firstTok.col < col) || firstTok.line < line;
            bool beforeLastTok = line < lastTok.line || (line == lastTok.line && col <= lastTok.col + lastTok.val.Length);
            return afterFirstTok && beforeLastTok;
        }

        private IEnumerable<string> inputFilesFromTarget(string target)
        {
            List<string> inputFiles = new();
            System.IO.DirectoryInfo info = new(target);
            foreach (var f in info.GetFiles("*.arm"))
            {
                inputFiles.Add(f.FullName);
            }
            foreach (var d in info.GetDirectories("*.*"))
            {
                if (d.Name != ".build")
                {
                    inputFiles.AddRange(inputFilesFromTarget(d.ToString()));
                }
            }
            return inputFiles;
        }

        public Driver(string target)
        {
            InputRoot = target;
            InputFiles = new(inputFilesFromTarget(target));
            CaretRangeLoc = null;
            LevelRange = null;
            Project = null;
        }

        public Driver Run(PositionSelection ps, (IdentStr LLevel, IdentStr HLevel) lvRange)
        {
            ProjectSummary proj = new();

            Dictionary<IdentStr, LevelDecl> levels = new(new IdentStrEq());
            Dictionary<IdentStr, ProofDecl> proofs = new(new IdentStrEq());
            Dictionary<IdentStr, IdentStr> proofMap = new(new IdentStrEq());
            HashSet<IdentStr> proofTails = new(new IdentStrEq());

            List<LevelDecl> levelChain = new();
            List<ProofDecl> proofChain = new();

            CaretLevelMethod caretLevelMethod = null;

            foreach (var inputFile in InputFiles)
            {
                Console.WriteLine(
                    $"Scanning {InputRoot}{inputFile.Remove(0, System.IO.Path.GetFullPath(InputRoot).Length)}."
                );
                Scanner scanner = new Scanner(inputFile);
                StarmadaParser parser = new StarmadaParser(scanner, inputFile);
                parser.Parse();

                // set StatementLocs
                if (inputFile.Equals(ps.File))
                {
                    caretLevelMethod = new(parser.program, ps.Start);
                    if (ps.Selection)
                    {
                        CaretLevelMethod caretLevelMethodEnd = new(parser.program, ps.End);
                        if (!caretLevelMethod.Equals(caretLevelMethodEnd))
                        {
                            throw new FatalError("Invalid Selection across methods");
                        }
                    }
                }
                // init levels and proofs
                foreach (var level in parser.program.Levels)
                {
                    levels.Add(new(level.Name), level);
                    proj.LevelInfoDict.Add(new(level.Name), new LevelInfo(inputFile));
                }
                foreach (var proof in parser.program.Proofs)
                {
                    proofs.Add(new(proof.LLevelName), proof);
                    proofMap.Add(new(proof.LLevelName), new(proof.HLevelName));
                    proofTails.Add(new(proof.HLevelName));
                }
            }

            if (caretLevelMethod is null)
            {
                throw new FatalError("CaretLevelMethod not set");
            }

            List<IdentStr> proofHead = new List<IdentStr>();
            foreach (var (low, _) in proofMap)
            {
                if (!proofTails.Contains(low))
                {
                    proofHead.Add(low);
                }
            }
            if (proofHead.Count > 1)
            {
                throw new FatalError("Multiple lowest levels found");
            }
            if (proofHead.Count == 0)
            {
                throw new FatalError("No lowest level found");
            }
            IdentStr cur = proofHead[0];

            int chainCnt = 0;
            while (true)
            {
                if (!levels.ContainsKey(cur))
                {
                    throw new FatalError("Level mentioned is not found");
                }
                levelChain.Add(levels[cur]);
                proj.LevelInfoDict[new(levels[cur].Name)].ChainIdx = chainCnt;

                if (!proofMap.ContainsKey(cur))
                {
                    break;
                }

                if (!proofs.ContainsKey(cur))
                {
                    throw new FatalError("Proof mentioned is not found");
                }
                proofChain.Add(proofs[cur]);

                // Iterate
                cur = proofMap[cur];
                chainCnt += 1;
            }

            LevelRange = new(
                lvRange.LLevel is null ? new(levelChain.First().Name) : lvRange.LLevel,
                lvRange.HLevel is null ? new(levelChain.Last().Name) : lvRange.HLevel
            );

            // generate LevelStmtSeqChain
            foreach (var level in levelChain)
            {
                proj.LevelSummaryChain.Add(new LevelSummary(level));
            }

            // generate ProofChain
            foreach (var proof in proofChain)
            {
                proj.ProofSummaryChain.Add(new ProofSummary(proof));
            }

            Project = proj;

            // Set the CaretRangeLoc
            caretLevelMethod.SetStmtSeq(Project);
            StmtLoc start = caretLevelMethod.GetStmtLoc(ps.Start);
            if (ps.Selection)
            {
                StmtLoc end = caretLevelMethod.GetStmtLoc(ps.End);
                CaretRangeLoc = new(start, end);
            }
            else
            {
                CaretRangeLoc = new(start);
            }

            return this;
        }

        public List<StmtGroupToken> StmtGroupLocToToken(List<StmtGroupLoc> groupLocs)
        {
            List<StmtGroupToken> groupToks = new(groupLocs.Select(glo => glo.ToStmtGroupToken(Project)));
            return groupToks;
        }

        public void DumpCaretCandidates(string file)
        {
            StatementSeq seq = Project
                .GetLevelSummary(CaretRangeLoc.Level)
                .MethodCollection[CaretRangeLoc.Method];

            string buffer = "";
            for (int i = CaretRangeLoc.StmtIdx; i <= CaretRangeLoc.StmtEndIdx; i++)
            {
                Statement s = seq[i];
                buffer += s.ToString(0, true) + '\n';
            }

            System.IO.File.WriteAllText(file, buffer);
        }
    }

    class CaretLevelMethod
    {
        IdentStr level;
        IdentStr method;
        public CaretLevelMethod(StarmadaProgram program, (int, int) position)
        {
            foreach (var lv in program.Levels)
            {
                if (Driver.PositionBetweenTokens(lv.FirstTok, lv.LastTok, position))
                {
                    foreach (var member in lv.Members)
                    {
                        if (Driver.PositionBetweenTokens(member.FirstTok, member.LastTok, position))
                        {
                            if (member is MethodDecl)
                            {
                                MethodDecl me = (MethodDecl)member;
                                level = new(lv.Name);
                                method = new(me.Name);
                                return;
                            }
                            else
                            {
                                throw new FatalError("Refactor is performed outside method");
                            }
                        }
                    }
                    throw new FatalError("Refactor is performed in invalid region in a level");
                }
            }
            throw new FatalError("Refactor is performed outside levels");
        }
        public bool Equals(CaretLevelMethod other)
        {
            return level.Equals(other.level) && method.Equals(other.method);
        }

        private StatementSeq stmts;
        public void SetStmtSeq(ProjectSummary pc)
        {
            stmts = pc.LevelSummaryChain[pc.LevelInfoDict[level].ChainIdx].MethodCollection[method];
        }
        public StmtLoc GetStmtLoc((int, int) position)
        {
            for (int i = 0; i < stmts.Count; i++)
            {
                Statement stmt = stmts[i];
                if (Driver.PositionBetweenTokens(stmt.FirstTok, stmt.LastTok, position))
                {
                    return new StmtLoc(level, method, i);
                }
            }
            throw new FatalError("Refactor is performed outside the statements");
        }
    }
}