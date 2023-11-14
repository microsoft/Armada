using System.Collections.Generic;
using System.Linq;
using System.Text.Json.Serialization;
using Microsoft.Starmada;

namespace Editor
{
    public class IdentStr
    {
        public string Str;
        public IdentStr(string s)
        {
            Str = s;
        }
        public IdentStr(Ident id)
        {
            Str = id.Name;
        }
        public override bool Equals(object obj)
        {
            //Check for null and compare run-time types.
            if ((obj == null) || !this.GetType().Equals(obj.GetType()))
            {
                return false;
            }
            else
            {
                IdentStr p = (IdentStr)obj;
                return Str == p.Str;
            }
        }
        public override int GetHashCode()
        {
            return base.GetHashCode();
        }
        public override string ToString()
        {
            return Str;
        }
    }

    public class LevelInfo
    {
        public string File;
        public int ChainIdx;
        public LevelInfo(string file)
        {
            File = file;
            ChainIdx = -1;
        }
        public string ToString(IdentStr name)
        {
            return $"{name.ToString()}.{ChainIdx} @ {File}";
        }
    }

    public class MethodInfo
    {
        public IdentStr Method;
        public MethodInfo(IdentStr method)
        {
            Method = method;
        }
    }

    public class StmtLoc
    {
        public IdentStr Level;
        public IdentStr Method;
        public int StmtIdx;
        public StmtLoc(IdentStr level, IdentStr method, int stmtIdx)
        {
            if (level is null || method is null)
            {
                throw new FatalError("StmtLoc arguments can't be null.");
            }
            Level = level;
            Method = method;
            StmtIdx = stmtIdx;
        }
    }

    public class StmtRangeLoc : StmtLoc
    {
        // StmtEndIdx == StatementIdx if a point, >= 0 if a valid selection; works as [start, end], so be careful of off by 1.
        public int StmtEndIdx;
        public StmtRangeLoc(StmtLoc start) : base(start.Level, start.Method, start.StmtIdx)
        {
            StmtEndIdx = start.StmtIdx;
        }
        public StmtRangeLoc(StmtLoc start, int endIdx) : base(start.Level, start.Method, start.StmtIdx)
        {
            StmtEndIdx = endIdx;
        }
        public StmtRangeLoc(StmtLoc start, StmtLoc end) : base(start.Level, start.Method, start.StmtIdx)
        {
            if (!start.Level.Equals(end.Level) || !start.Method.Equals(end.Method))
            {
                throw new FatalError("StmtRangeLoc must locate in the same level in the same method.");
            }
            if (!(start.StmtIdx <= end.StmtIdx))
            {
                throw new FatalError("StmtRangeLoc must take end located after start.");
            }
            StmtEndIdx = end.StmtIdx;
        }
        public StmtLoc GetEndLoc()
        {
            return new StmtLoc(Level, Method, StmtEndIdx);
        }
    }

    public class StmtGroupLoc
    {
        public List<StmtLoc> Locs;
        public StmtRangeLoc Selection;
        private void tryCluster()
        {
            Selection = null;
            if (Locs.Count == 0)
            {
                return;
            }
            StmtLoc head = Locs[0];
            int end = head.StmtIdx;
            for (int i = 1; i < Locs.Count; i++)
            {
                if (!(Locs[i].StmtIdx == ++end))
                {
                    return;
                }
            }
            Selection = new(head, end);
        }
        public StmtGroupLoc(IEnumerable<StmtLoc> iter)
        {
            Locs = new List<StmtLoc>(iter);
            tryCluster();
        }
        public StmtGroupToken ToStmtGroupToken(ProjectSummary proj)
        {
            StmtGroupToken groupTok;
            groupTok = new(Locs.Select(lo => proj.GetStmtToken(lo)));
            if (Selection is not null)
            {
                StmtToken start = proj.GetStmtToken(Selection);
                StmtToken end = proj.GetStmtToken(Selection.GetEndLoc());
                groupTok.Clustered = new(start.File, start.FirstTok, end.LastTok);
            }
            return groupTok;
        }
    }

    public class StmtToken
    {
        public string File { get; set; }
        public Token FirstTok { get; set; }
        public Token LastTok { get; set; }

        [JsonConstructor]
        public StmtToken(string file, Token firstTok, Token lastTok)
        {
            File = file;
            FirstTok = firstTok;
            LastTok = lastTok;
        }
        // exclusive
        public ((int, int), (int, int)) GetPosRange()
        {
            return ((FirstTok.line, FirstTok.col), (LastTok.line, LastTok.col + LastTok.val.Length));
        }
        // exclusive
        public (int, int) GetCharPosRange()
        {
            return (FirstTok.charPos, LastTok.charPos + LastTok.val.Length);
        }
        public string GetStringFromBuffer(string buf)
        {
            var (a, b) = GetCharPosRange();
            return buf.Substring(a, b - a);
        }

    }

    public class StmtGroupToken
    {
        public List<StmtToken> Tokens { get; set; }
        public StmtToken Clustered { get; set; }
        public StmtGroupToken(IEnumerable<StmtToken> iter)
        {
            Tokens = new(iter);
            Clustered = null;
        }
        [JsonConstructor]
        public StmtGroupToken(List<StmtToken> tokens, StmtToken clustered)
        {
            Tokens = tokens;
            Clustered = clustered;
        }
    }

    public class LevelRange
    {
        public IdentStr LLevel;
        public IdentStr HLevel;
        public LevelRange(IdentStr low, IdentStr high)
        {
            if (low is null || high is null)
            {
                throw new FatalError("LevelRange can't be null.");
            }
            LLevel = low;
            HLevel = high;
        }
    }
}