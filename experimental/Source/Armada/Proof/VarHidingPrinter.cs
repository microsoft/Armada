using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class VarHidingPrinter : StrategyPrinter
    {
        public string GetProof(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LName = L.Name.ToString(0, false);
            var LAtomicName = "Atomic" + LName;
            var HName = H.Name.ToString(0, false);
            var HAtomicName = "Atomic" + HName;
            var HAtomicInvariantName = LAtomicName + "Invariant"; // Actually LAtomic Invariant Name
            AtomicPrinter atomicPrinter = new AtomicPrinter();
            Scope sc = L.Sc;
            VarHidingStrategy vs = proof.Strategy as VarHidingStrategy;
            HashSet<string> hidingVarNameSet = new();
            foreach (Ident introvar in vs.Variables)
            {
                hidingVarNameSet.Add(introvar.Name);
            }
            VarIntroProofSpec proofSpec = new VarIntroProofSpec(H, L);

            str += indent(0) + "let vs: list var_id_t =\n";
            str += indent(1) + "[\n";
            foreach (Ident introvar in vs.Variables)
            {
                str += indent(2) + $"\"{introvar.Name}\";\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let tds: list object_td_t =\n";
            str += indent(1) + "[\n";
            foreach (Ident introvar in vs.Variables)
            {
                VarDecl vardecl = sc.GetVariableDecl(introvar, false);
                str += indent(2) + $"({vardecl.Ty.ToFStarLang(0, true)});\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let which_initializers_are_hidings: list bool =\n";
            str += indent(1) + "[\n";
            foreach (var globalvar in L.Globals)
            {
                str += indent(2) + $"{hidingVarNameSet.Contains(globalvar.Name.Name).ToString().ToLower()};\n";
            }
            str += indent(1) + "]\n\n";

            string lpcList = $"[{String.Join("; ", proofSpec.HS.PCs.ConvertAll(pc => $"\"{pc}\""))}]";
            str += indent(0) + $"let lpcs: array_t pc_t = list_to_array {lpcList}\n\n";

            string hpcList = $"[{String.Join("; ", proofSpec.LS.PCs.ConvertAll(pc => $"\"{pc}\""))}]";
            str += indent(0) + $"let hpcs: array_t pc_t = list_to_array {hpcList}\n\n";

            List<string> lpc2hpc = new();
            foreach (string lpc in proofSpec.HS.PCs)
            {
                string hpc = proofSpec.PCMap[lpc];
                lpc2hpc.Add($"{proofSpec.LS.PC2Index[hpc]}");
            }
            str += indent(0) + $"let lpc_to_hpc: array_t nat = list_to_array [{String.Join("; ", lpc2hpc)}]\n\n";

            string lpcReturnList = $"[{String.Join("; ", proofSpec.HS.PCs.ConvertAll(pc => $"{pc.EndsWith(".R").ToString().ToLower()}"))}]";
            str += indent(0) + $"let is_return_lpc: array_t bool = list_to_array {lpcReturnList}\n\n";

            str += indent(0) + $"let is_nonyielding_lpc : array_t bool = list_to_array {proofSpec.HS.GetNonYieldingPCList()}\n\n";
            str += indent(0) + $"let is_nonyielding_hpc : array_t bool = list_to_array {proofSpec.LS.GetNonYieldingPCList()}\n\n";

            List<FStarStmt> nonconstStmts = proofSpec.GetNonConstStmts();
            for (int i = 0; i < nonconstStmts.Count; i++)
            {
                str += indent(0) + $"let statement_subroutine_{i}: program_statement_t =\n";
                str += nonconstStmts[i].GetFStarCodeOfStatement(indentation + 2) + "\n\n";

                str += indent(0) + "#push-options \"--z3rlimit 20 --z3cliopt smt.qi.eager_threshold=100\"\n";

                str += indent(0) + $"let lemma_cant_crash_subroutine_{i}\n";
                str += indent(1) + "(actor: tid_t)\n";
                str += indent(1) + "(nd: nondeterminism_t)\n";
                str += indent(1) + "(s: Armada.State.t{\n";
                str += indent(3) + $"{HAtomicInvariantName}.inv s\n";
                str += indent(2) + "/\\ all_gvars_have_types s.mem vs tds\n";
                str += indent(2) + "/\\ NotStopped? s.stop_reason\n";
                str += indent(2) + "/\\ ThreadStatusRunning? (s.threads actor).status\n";
                str += indent(2) + $"/\\ statement_subroutine_{i}.start_pc = Some (s.threads actor).pc}})\n";
                str += indent(1) + $": squash (let ps = statement_subroutine_{i} in\n";
                str += indent(5) + "not (ComputationUndefined? (statement_computation actor nd (Some?.v ps.start_pc) ps.end_pc ps.statement s))) = \n";
                str += indent(1) + "()\n";
                str += indent(0) + "#pop-options\n\n";
            }

            str += indent(0) + $"let corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds {HAtomicInvariantName}.inv) = list_to_array\n";
            str += indent(1) + "[\n";
            Dictionary<ExecutionPath, ExecutionPath> actionMap = new();
            foreach (var kv in proofSpec.ActionMap)
            {
                actionMap[kv.Value] = kv.Key;
            }
            foreach (var laction in proofSpec.HS.Actions)
            {
                if (actionMap.ContainsKey(laction))
                {
                    var haction = actionMap[laction];
                    int hactionIndex= proofSpec.LS.Actions.IndexOf(haction);
                    if (laction.Stmts.Count == 1 && laction.Stmts[0].Statement == "PropagateWriteMessageStatement")
                    {
                        str += indent(2) + $"CorrespondencePropagate {hactionIndex};\n";
                        continue;
                    }
                    List<string> lactionMaps = new();
                    foreach (FStarStmt lstmt in laction.Stmts)
                    {
                        if (proofSpec.VarIntroStmts.Contains(lstmt))
                        {
                            lactionMaps.Add("true");
                        }
                        else
                        {
                            lactionMaps.Add("false");
                        }
                    }
                    str += indent(2) + $"CorrespondenceNormal {hactionIndex} [{String.Join("; ", lactionMaps)}];\n";
                }
                else if (!laction.FailAtTheEnd)
                {
                    str += indent(2) + "CorrespondenceHidden;\n";
                }
                else
                {
                    string correspond = "CorrespondenceImpossibleConstantAssignmentFailure";
                    foreach (FStarStmt lstmt in laction.Stmts)
                    {
                        if (proofSpec.VarIntroStmts.Contains(lstmt))
                        {
                            if (nonconstStmts.Contains(lstmt))
                            {
                                int nonconstIndex = nonconstStmts.IndexOf(lstmt);
                                correspond = $"CorrespondenceImpossibleStatementFailure statement_subroutine_{nonconstIndex} lemma_cant_crash_subroutine_{nonconstIndex}";
                            }
                        }
                    }
                    str += indent(2) + correspond + ";\n";
                }
            }
            str += indent(1) + "]\n\n";

            str += $"let lprog_main_start_pc_index = {proofSpec.HS.GetStartIndex()}\n\n";
            str += $"let hprog_main_start_pc_index = {proofSpec.LS.GetStartIndex()}\n\n";
            
            str += atomicPrinter.MakePCIndexStarter(0);

            str += indent(0) + "let lpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var laction in proofSpec.HS.Actions)
            {
                str += indent(2) + $"[{String.Join("; ", laction.Stmts.ConvertAll(fstmt => atomicPrinter.MakePCIndex(proofSpec.HS, fstmt)))}];\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let hpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var haction in proofSpec.LS.Actions)
            {
                str += indent(2) + $"[{String.Join("; ", haction.Stmts.ConvertAll(fstmt => atomicPrinter.MakePCIndex(proofSpec.LS, fstmt)))}];\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let vw: efficient_var_hiding_witness_t = {\n";
            str += indent(1) + $"lprog = {LName}.prog;\n";
            str += indent(1) + $"hprog = {HName}.prog;\n";
            str += indent(1) + $"lprog_actions_array = list_to_array {LAtomicName}.prog.actions;\n";
            str += indent(1) + $"hprog_actions_array = list_to_array {HAtomicName}.prog.actions;\n";
            str += indent(1) + "vs = vs;\n";
            str += indent(1) + "tds = tds;\n";
            str += indent(1) + $"inv = {HAtomicInvariantName}.inv;\n";
            str += indent(1) + "which_initializers_are_hidings = which_initializers_are_hidings;\n";
            str += indent(1) + "lpcs = lpcs;\n";
            str += indent(1) + "hpcs = hpcs;\n";
            str += indent(1) + "lpc_to_hpc = lpc_to_hpc;\n";
            str += indent(1) + "is_return_lpc = is_return_lpc;\n";
            str += indent(1) + "is_nonyielding_lpc = is_nonyielding_lpc;\n";
            str += indent(1) + "is_nonyielding_hpc = is_nonyielding_hpc;\n";
            str += indent(1) + "corresponding_hactions_info = corresponding_hactions_info;\n";
            str += indent(1) + "lprog_main_start_pc_index = lprog_main_start_pc_index;\n";
            str += indent(1) + "hprog_main_start_pc_index = hprog_main_start_pc_index;\n";
            str += indent(1) + "lpc_indices_array = lpc_indices_array;\n";
            str += indent(1) + "hpc_indices_array = hpc_indices_array;\n";
            str += indent(0) + "}\n\n";

            str += indent(0) + $"let lemma_{LAtomicName}Refines{HAtomicName}()\n";
            str += indent(1) + ": Lemma (spec_refines_spec\n";
            str += indent(5) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {LAtomicName}.prog)\n";
            str += indent(5) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {HAtomicName}.prog)\n";
            str += indent(5) + $"refinement_requirement) =\n";
            str += indent(1) + $"let latomic_prog = {LAtomicName}.prog in\n";
            str += indent(1) + $"let hatomic_prog = {HAtomicName}.prog in\n";
            str += indent(1) + "let pc_relation = efficient_lh_pc_relation lpc_to_hpc in\n";
            str += indent(1) + "let pc_return_relation = efficient_lh_pc_return_relation lpc_to_hpc is_return_lpc in\n";
            str += indent(1) + "assert (efficient_var_hiding_witness_valid latomic_prog hatomic_prog vw)\n";
            str += indent(2) + "by (FStar.Tactics.compute (); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"{HAtomicInvariantName}.inv_is_stepwise_invariant ();\n";
            str += indent(1) + "efficient_var_hiding_witness_valid_implies_refinement latomic_prog hatomic_prog vw\n\n";

            return str;
        }

        public string GetInvariant(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            VarIntroPrinter vp = new();
            // Exactly the same as varIntro
            return vp.GetInvariant(proof, H, L, indentation);
        }
    }
}
