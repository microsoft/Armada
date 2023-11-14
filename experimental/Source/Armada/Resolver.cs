using System.Collections.Generic;

namespace Microsoft.Starmada
{
    public class Resolver
    {
        public DatatypeDecl GetStopReasonDatatypeDecl()
        {
            DatatypeDecl StopReasonDatatype = new DatatypeDecl(new Token(),
                new UserDefinedType(new Ident(new Token(), "stop_reason_t")));
            return StopReasonDatatype;
        }
        public StructDecl GetArmadaStateStructDecl()
        {
            StructDecl ArmadaStateStructure = new StructDecl(new Token(), new Ident(new Token(), "Armada.State.t"));
            ArmadaStateStructure.Decls.Add(
                new VarDecl(new Token(), new Ident(new Token(), "initial_tid"),
                            new PredefinedType(PredefinedTypeEnum.ThreadId),
                            null, true, true, true, true));
            ArmadaStateStructure.Decls.Add(
                new VarDecl(new Token(), new Ident(new Token(), "uniqs_used"),
                            new SeqType(new PredefinedType(PredefinedTypeEnum.Nat)),
                            null, true, true, true, true));
            ArmadaStateStructure.Decls.Add(
                new VarDecl(new Token(), new Ident(new Token(), "stop_reason"),
                            new UserDefinedType(new Ident(new Token(), "stop_reason_t")),
                            null, true, true, true, true));
            return ArmadaStateStructure;
        }
        public void Resolve(StarmadaProgram program)
        {
            program.Sc = new Scope(null);
            program.Sc.EnclosingNode = program;
            program.Sc.Push(GetStopReasonDatatypeDecl());
            program.Sc.Push(GetArmadaStateStructDecl());
            program.Sc.Push(new VarDecl(new Token(), new Ident(new Token(), "$state"), new UserDefinedType(new Ident(new Token(), "Armada.State.t")), null, true, true, true));
            program.TypeResolve(null, ref program.errors);
        }
    }

    public class ProofResolver
    {
        // Proofs ordered from lower to upper
        public List<ProofDecl> ProofRefinements;
        public Dictionary<string, LevelDecl> Levels;
        // Proofs indexed by lower level name
        Dictionary<string, ProofDecl> Proofs;
        Dictionary<string, string> Refinement;
        HashSet<string> RefinementL;
        HashSet<string> RefinementH;
        string L = null;
        string H = null;
        public void Resolve(StarmadaProgram program)
        {
            ProofRefinements = new();
            Levels = new();
            Proofs = new();
            Refinement = new();
            RefinementL = new();
            RefinementH = new();
            foreach (var level in program.Levels)
            {
                Levels[level.Name.Name] = level;
            }
            foreach (var proof in program.Proofs)
            {
                string l = proof.LLevelName.Name;
                string h = proof.HLevelName.Name;
                if (!Levels.ContainsKey(l))
                {
                    program.errors.SemErr(new Token(), "Cannot find level: " + l);
                    return;
                }
                if (!Levels.ContainsKey(h))
                {
                    program.errors.SemErr(new Token(), "Cannot find level: " + h);
                    return;
                }
                if (Refinement.ContainsKey(l))
                {
                    program.errors.SemErr(new Token(), "Refinement on the same level for multiple times: " + l);
                    return;
                }
                Refinement[l] = h;
                RefinementL.Add(l);
                RefinementH.Add(h);
                Proofs[l] = proof;
            }
            HashSet<string> Ls = new(RefinementL);
            Ls.ExceptWith(RefinementH);
            if (Ls.Count > 1)
            {
                program.errors.SemErr(new Token(), "There are multiple refinement levels that are lowerest levels: " + string.Join(", ", Ls));
                return;
            }
            if (Ls.Count == 0)
            {
                if (RefinementL.Count > 0)
                {
                    program.errors.SemErr(new Token(), "There are no refinement levels that are lowest levels");
                }
                return;
            }

            foreach (var lowest in Ls)
            {
                L = lowest;
            }
            string next = L;
            while (Refinement.ContainsKey(next))
            {
                ProofRefinements.Add(Proofs[next]);
                next = Refinement[next];
            }
            H = next;
        }

        public LevelDecl GetLLevel()
        {
            if (L == null || !Levels.ContainsKey(L))
                return null;
            return Levels[L];
        }

        public LevelDecl GetHLevel()
        {
            if (H == null || !Levels.ContainsKey(H))
                return null;
            return Levels[H];
        }
    }
}
