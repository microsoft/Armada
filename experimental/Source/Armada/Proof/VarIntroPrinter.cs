using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class VarIntroPrinter : StrategyPrinter
    {
        public string GetProof(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LName = L.Name.ToString(0, false);
            var LAtomicName = "Atomic" + LName;
            var HName = H.Name.ToString(0, false);
            var HAtomicName = "Atomic" + HName;
            var HAtomicInvariantName = HAtomicName + "Invariant";
            AtomicPrinter atomicPrinter = new AtomicPrinter();
            Scope sc = H.Sc;
            VarIntroStrategy vs = proof.Strategy as VarIntroStrategy;
            HashSet<string> introvarNameSet = new();
            foreach (Ident introvar in vs.Variables)
            {
                introvarNameSet.Add(introvar.Name);
            }
            VarIntroProofSpec proofSpec = new VarIntroProofSpec(L, H);
            
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

            str += indent(0) + "let which_initializers_are_intros: list bool =\n";
            str += indent(1) + "[\n";
            foreach (var globalvar in H.Globals)
            {
                str += indent(2) + $"{introvarNameSet.Contains(globalvar.Name.Name).ToString().ToLower()};\n";
            }
            str += indent(1) + "]\n\n";

            string lpcList = $"[{String.Join("; ", proofSpec.LS.PCs.ConvertAll(pc => $"\"{pc}\""))}]";
            str += indent(0) + $"let lpcs: array_t pc_t = list_to_array {lpcList}\n\n";

            string hpcList = $"[{String.Join("; ", proofSpec.HS.PCs.ConvertAll(pc => $"\"{pc}\""))}]";
            str += indent(0) + $"let hpcs: array_t pc_t = list_to_array {hpcList}\n\n";

            List<string> hpc2lpc = new();
            foreach (string hpc in proofSpec.HS.PCs)
            {
                string lpc = proofSpec.PCMap[hpc];
                hpc2lpc.Add($"{proofSpec.LS.PC2Index[lpc]}");
            }
            str += indent(0) + $"let hpc_to_lpc: array_t nat = list_to_array [{String.Join("; ", hpc2lpc)}]\n\n";
            
            List<string> lpc2hpcs = new();
            foreach (string lpc in proofSpec.LS.PCs)
            {
                List<string> hpcs = proofSpec.ReversePCMap[lpc];
                List<int> hpcIndices = hpcs.ConvertAll(hpc => proofSpec.HS.PC2Index[hpc]);
                hpcIndices.Sort();
                lpc2hpcs.Add($"[{String.Join("; ", hpcIndices.ConvertAll(id => id.ToString()))}]");
            }
            str += indent(0) + $"let lpc_to_hpcs: array_t (list nat) = list_to_array [{String.Join("; ", lpc2hpcs)}]\n\n";

            string hpcReturnList = $"[{String.Join("; ", proofSpec.HS.PCs.ConvertAll(pc => $"{pc.EndsWith(".R").ToString().ToLower()}"))}]";
            str += indent(0) + $"let is_return_hpc: array_t bool = list_to_array {hpcReturnList}\n\n";

            str += indent(0) + $"let is_nonyielding_lpc : array_t bool = list_to_array {proofSpec.LS.GetNonYieldingPCList()}\n\n";
            str += indent(0) + $"let is_nonyielding_hpc : array_t bool = list_to_array {proofSpec.HS.GetNonYieldingPCList()}\n\n";

            str += indent(0) + $"let is_breaking_hpc : array_t bool = list_to_array {proofSpec.HS.GetBreakPCList()}\n\n";
            
            List<FStarStmt> nonconstStmts = proofSpec.GetNonConstStmts();
            for (int i = 0; i < nonconstStmts.Count; i++)
            {
                str += indent(0) + $"let statement_subroutine_{i}: program_statement_t =\n";
                str += nonconstStmts[i].GetFStarCodeOfStatement(indentation + 2) + "\n\n";

                str += indent(0) + "#push-options \"--z3rlimit 20 --z3cliopt smt.qi.eager_threshold=100\"\n";

                str += indent(0) + $"let lemma_cant_crash_subroutine_{i}\n";
                str += indent(1) + "(actor: tid_t)\n";
                str += indent(1) + "(s: Armada.State.t{\n";
                str += indent(3) + $"{HAtomicInvariantName}.inv s\n";
                str += indent(2) + "/\\ all_gvars_have_types s.mem vs tds\n";
                str += indent(2) + "/\\ NotStopped? s.stop_reason\n";
                str += indent(2) + "/\\ ThreadStatusRunning? (s.threads actor).status\n";
                str += indent(2) + $"/\\ statement_subroutine_{i}.start_pc = Some (s.threads actor).pc}})\n";
                str += indent(1) + $": squash (let ps = statement_subroutine_{i} in\n";
                str += indent(5) + "ComputationProduces? (statement_computation actor [] (Some?.v ps.start_pc) ps.end_pc ps.statement s)) =\n";
                str += indent(1) + "()\n";
                str += indent(0) + "#pop-options\n\n";

                str += indent(0) + $"let introduction_succeeds_witness_subroutine_{i}: introduction_succeeds_witness_t vs tds {HAtomicInvariantName}.inv =\n";
                str += indent(1) + $"IntroductionSucceedsProof statement_subroutine_{i} lemma_cant_crash_subroutine_{i}\n\n";
            }

            str += indent(0) + $"let hpc_info: array_t (efficient_hpc_info_t vs tds {HAtomicInvariantName}.inv) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var hpc in proofSpec.HS.PCs)
            {
                string info = "EfficientHPCInfoNormal";
                if (proofSpec.IntroPCs.ContainsKey(hpc))
                {
                    var sequence = proofSpec.IntroPCs[hpc];
                    int successPathIndex = proofSpec.HS.Actions.IndexOf(sequence.Paths[0]);
                    string endPC = sequence.Stmts[sequence.Stmts.Count - 1].EndPC;
                    string successReasons = String.Join("; ", sequence.Stmts.ConvertAll(stmt => nonconstStmts.Contains(stmt) ? $"introduction_succeeds_witness_subroutine_{nonconstStmts.IndexOf(stmt)}" : "IntroductionSucceedsBecauseItAssignsConstant"));
                    int progress = 1;
                    string nextPC = endPC;
                    while (proofSpec.IntroPCs.ContainsKey(nextPC))
                    {
                        progress += 1;
                        var nextSeq = proofSpec.IntroPCs[nextPC];
                        nextPC = nextSeq.Stmts[nextSeq.Stmts.Count - 1].EndPC;
                    }
                    // Console.WriteLine(hpc);
                    // Console.WriteLine(atomicPrinter.ToFStarAtomic(proofSpec.HS.Actions[successPathIndex], 0));
                    // Console.WriteLine(endPC);
                    info = $"EfficientHPCInfoIntroduced {successPathIndex} {proofSpec.HS.PC2Index[endPC]} [{successReasons}] {progress}";
                }
                str += indent(2) + $"{info};\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + $"let corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds {HAtomicInvariantName}.inv) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var laction in proofSpec.LS.Actions)
            {
                var haction = proofSpec.ActionMap[laction];
                int hactionIndex= proofSpec.HS.Actions.IndexOf(haction);
                if (laction.Stmts.Count == 1 && laction.Stmts[0].Statement == "PropagateWriteMessageStatement")
                {
                    str += indent(2) + $"CorrespondencePropagate {hactionIndex};\n";
                    continue;
                }
                List<string> hactionMaps = new();
                foreach (FStarStmt hstmt in haction.Stmts)
                {
                    if (proofSpec.VarIntroStmts.Contains(hstmt))
                    {
                        string hactionMap = "MapperIntroduced ";
                        if (nonconstStmts.Contains(hstmt))
                        {
                            hactionMap += $"introduction_succeeds_witness_subroutine_{nonconstStmts.IndexOf(hstmt)}";
                        }
                        else
                        {
                            hactionMap += "IntroductionSucceedsBecauseItAssignsConstant";
                        }
                        hactionMaps.Add(hactionMap);
                    }
                    else
                    {
                        hactionMaps.Add("MapperMatching");
                    }
                }
                str += indent(2) + $"CorrespondenceNormal {hactionIndex} [{String.Join("; ", hactionMaps)}];\n";
            }
            str += indent(1) + "]\n\n";

            str += $"let lprog_main_start_pc_index = {proofSpec.LS.GetStartIndex()}\n\n";
            str += $"let hprog_main_start_pc_index = {proofSpec.HS.GetStartIndex()}\n\n";

            str += atomicPrinter.MakePCIndexStarter(0);

            str += indent(0) + "let lpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var laction in proofSpec.LS.Actions)
            {
                str += indent(2) + $"[{String.Join("; ", laction.Stmts.ConvertAll(fstmt => atomicPrinter.MakePCIndex(proofSpec.LS, fstmt)))}];\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let hpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var haction in proofSpec.HS.Actions)
            {
                str += indent(2) + $"[{String.Join("; ", haction.Stmts.ConvertAll(fstmt => atomicPrinter.MakePCIndex(proofSpec.HS, fstmt)))}];\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "let vw: efficient_var_intro_witness_t = {\n";
            str += indent(1) + $"lprog = {LName}.prog;\n";
            str += indent(1) + $"hprog = {HName}.prog;\n";
            str += indent(1) + $"lprog_actions_array = list_to_array {LAtomicName}.prog.actions;\n";
            str += indent(1) + $"hprog_actions_array = list_to_array {HAtomicName}.prog.actions;\n";
            str += indent(1) + "vs = vs;\n";
            str += indent(1) + "tds = tds;\n";
            str += indent(1) + $"inv = {HAtomicInvariantName}.inv;\n";
            str += indent(1) + "which_initializers_are_intros = which_initializers_are_intros;\n";
            str += indent(1) + "lpcs = lpcs;\n";
            str += indent(1) + "hpcs = hpcs;\n";
            str += indent(1) + "hpc_to_lpc = hpc_to_lpc;\n";
            str += indent(1) + "lpc_to_hpcs = lpc_to_hpcs;\n";
            str += indent(1) + "is_return_hpc = is_return_hpc;\n";
            str += indent(1) + "is_nonyielding_lpc = is_nonyielding_lpc;\n";
            str += indent(1) + "is_nonyielding_hpc = is_nonyielding_hpc;\n";
            str += indent(1) + "is_breaking_hpc = is_breaking_hpc;\n";
            str += indent(1) + "hpc_info = hpc_info;\n";
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
            str += indent(1) + "assert (efficient_var_intro_witness_valid latomic_prog hatomic_prog vw)\n";
            str += indent(2) + "by (FStar.Tactics.compute (); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"{HAtomicInvariantName}.inv_is_stepwise_invariant ();\n";
            str += indent(1) + "efficient_var_intro_witness_valid_implies_refinement latomic_prog hatomic_prog vw\n\n";

            return str;
        }

        public string GetInvariant(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var HName = H.Name.ToString(0, false);
            var HAtomicName = "Atomic" + HName;
            Scope sc = H.Sc;
            List<Ident> vars = new();
            if (proof.Strategy is VarIntroStrategy varIntroStrategy) {
                vars = varIntroStrategy.Variables;
            } else if (proof.Strategy is VarHidingStrategy varHidingStrategy) {
                vars = varHidingStrategy.Variables;
            } else {
                throw new NotSupportedException();
            }
            var HSpec = new AtomicSpec(H);

            List<VarDecl> introVars = new();
            List<VarDecl> invariantVars = new();
            foreach (Ident introvar in vars)
            {
                VarDecl vardecl = sc.GetVariableDecl(introvar, false);
                introVars.Add(vardecl);
            }
            foreach (var entity in sc.DefinedEntities)
            {
                if (entity is VarDecl vardecl && !introVars.Contains(vardecl))
                {
                    invariantVars.Add(vardecl);
                }
            }

            str += indent(0) + "let inv (s: Armada.State.t) : GTot ubool = true\n";
            foreach (var invvar in invariantVars)
            {
                str += indent(1) + $"/\\ gvar_has_type s.mem \"{invvar.Name.Name}\" ({invvar.Ty.ToFStarLang(0, true)})\n";
            }
            str += '\n';

            str += indent(0) + "private let action_pred (action: Armada.Action.t) : GTot ubool = True\n\n";

            str += indent(0) + "#push-options \"--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100\"\n\n";

            str += indent(0) + "private let atomic_bprog_init_establishes_inv\n";
            str += indent(1) + $"(s: Armada.State.t{{(semantics_to_spec (make_atomic_semantics armada_semantics) {HAtomicName}.prog).init s}})\n";
            str += indent(1) + ": squash (inv s) =\n";
            str += indent(1) + "()\n\n";

            str += indent(0) + "private let action_pred_preserves_inv\n";
            str += indent(1) + "(actor: tid_t)\n";
            str += indent(1) + "(starts_atomic_block: bool)\n";
            str += indent(1) + "(ends_atomic_block: bool)\n";
            str += indent(1) + "(step: Armada.Step.t)\n";
            str += indent(1) + "(s: Armada.State.t{\n";
            str += indent(2) + "Some? (step_computation actor starts_atomic_block ends_atomic_block step s)\n";
            str += indent(2) + "/\\ action_pred step.action\n";
            str += indent(2) + "/\\ inv s})\n";
            str += indent(1) + ": squash (inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) =\n";
            str += indent(1) + "step_computation_maintains_all_gvars_have_types\n";
            str += indent(2) + $"[{String.Join("; ", invariantVars.ConvertAll(vardecl => "\"" + vardecl.Name.Name + "\""))}]\n";
            str += indent(2) + $"[{String.Join("; ", invariantVars.ConvertAll(vardecl => vardecl.Ty.ToFStarLang(0, true)))}]\n";
            str += indent(2) + "actor starts_atomic_block ends_atomic_block step s\n\n";

            str += indent(0) + "#pop-options\n\n";

            str += indent(0) + "private let my_special_case_proofs\n";
            str += indent(1) + ": list (list (option (armada_action_special_case_invariant_proof_t inv))) =\n";
            str += indent(1) + "[\n";
            foreach (var action in HSpec.Actions)
            {
                str += indent(2) + $"[{String.Join("; ", action.Stmts.ConvertAll(stmt => "None"))}];\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + $"let inv_witness () : armada_atomic_substep_invariant_witness_t {HAtomicName}.prog inv =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "action_pred = action_pred;\n";
            str += indent(2) + "special_case_proofs = my_special_case_proofs;\n";
            str += indent(2) + "init_implies_inv_proof = atomic_bprog_init_establishes_inv;\n";
            str += indent(2) + "action_proof = action_pred_preserves_inv;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let inv_is_stepwise_invariant ()\n";
            str += indent(1) + $": Lemma (is_armada_substep_invariant {HAtomicName}.prog inv) =\n";
            str += indent(1) + "let aiw = inv_witness () in\n";
            str += indent(1) + $"assert (armada_atomic_substep_invariant_witness_valid {HAtomicName}.prog inv aiw)\n";
            str += indent(2) + "by (FStar.Tactics.compute(); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"armada_atomic_substep_invariant_witness_valid_implies_is_substep_invariant {HAtomicName}.prog inv aiw\n\n";
            return str;
        }
    }
}
