using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class WeakeningPrinter : StrategyPrinter
    {
        public string GetProof(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LName = L.Name.ToString(0, false);
            var LAtomicName = "Atomic" + LName;
            var HName = H.Name.ToString(0, false);
            var HAtomicName = "Atomic" + HName;
            AtomicPrinter atomicPrinter = new AtomicPrinter();
            WeakeningProofSpec proofSpec = new WeakeningProofSpec(L, H);

            var updateIndices = proofSpec.WeakeningUpdateIndices;
            foreach (int index in updateIndices)
            {
                str += indent(0) + $"private let my_special_case_action_{index} : list Armada.Action.t =\n";
                str += atomicPrinter.ToFStarAtomic(proofSpec.LS.Actions[index], 2) + "\n\n";
            }
            foreach (int index in updateIndices)
            {
                str += indent(0) + $"private let my_special_case_steps_updater_{index}\n";
                str += indent(1) + "(actor: tid_t) (steps: list Armada.Step.t) (s: Armada.State.t)\n";
                str += indent(1) + ": nat * (list Armada.Step.t) =\n";
                var action = proofSpec.HS.Actions[index];
                List<string> steps = new();
                for (int i = 0; i < action.Stmts.Count; i++)
                {
                    steps.Add($"step{i}");
                    str += indent(1) + $"let step{i}: Armada.Step.t = \n";
                    str += indent(2) + "{\n";
                    str += indent(3) + "nd = [];\n";
                    str += indent(3) + "action =\n";
                    str += atomicPrinter.ToFStarAtomic(
                        action.Stmts[i], indentation + 6,
                        !(action.FailAtTheEnd && i + 1 == action.Stmts.Count)
                    ) + '\n';
                    str += indent(2) + "}";
                    str += ((i + 1 == action.Stmts.Count) ? "" : ";") + "\n";
                    str += indent(1) + "in\n";
                }
                str += indent(1) + $"({index}, [{string.Join(';', steps)}])\n\n";
            }

            str += indent(0) + "#push-options \"--z3rlimit 20 --fuel 4\"\n\n";

            foreach (int index in updateIndices)
            {
                str += indent(0) + $"private let my_special_case_steps_updater_satisfies_weakening_{index}\n";
                str += indent(1) + "(actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: list Armada.Step.t) (haction_index: nat) (hsteps: list Armada.Step.t) (s: Armada.State.t)\n";
                str += indent(1) + $": Lemma (requires   (FStar.List.Tot.map armada_step_to_action lsteps == my_special_case_action_{index})\n";
                str += indent(8) + "/\\ (my_inv s)\n";
                str += indent(8) + "/\\ (Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s))\n";
                str += indent(8) + $"/\\ ((haction_index, hsteps) == my_special_case_steps_updater_{index} actor lsteps s))\n";
                str += indent(5) + "(ensures  (  (Some? (steps_computation actor starts_atomic_block ends_atomic_block hsteps s))\n";
                str += indent(8) + "/\\ (steps_computation actor starts_atomic_block ends_atomic_block lsteps s ==\n";
                str += indent(10) + "steps_computation actor starts_atomic_block ends_atomic_block hsteps s)\n";
                str += indent(8) + $"/\\ nth {HAtomicName}.prog.actions haction_index ==\n";
                str += indent(8) + "Some (map_ghost armada_step_to_action hsteps))) =\n";
                str += indent(1) + "()\n\n";
            }

            str += indent(0) + "#pop-options\n\n";

            foreach (int index in updateIndices)
            {
                str += indent(0) + $"private let my_special_case_steps_updater_works_{index} ()\n";
                str += indent(1) + $": squash (armada_steps_updater_works (list_to_array {HAtomicName}.prog.actions) my_inv my_special_case_action_{index}\n";
                str += indent(6) + $"my_special_case_steps_updater_{index}) =\n";
                str += indent(1) + $"let hatomic_action_array = list_to_array {HAtomicName}.prog.actions in\n";
                str += indent(1) + "introduce forall (actor: tid_t) (starts_atomic_block: bool) (ends_atomic_block: bool) (lsteps: list Armada.Step.t) (s: Armada.State.t).\n";
                str += indent(3) + $"map_ghost armada_step_to_action lsteps == my_special_case_action_{index}\n";
                str += indent(2) + "/\\ my_inv s\n";
                str += indent(2) + "/\\ Some? (steps_computation actor starts_atomic_block ends_atomic_block lsteps s)\n";
                str += indent(2) + "==>\n";
                str += indent(2) + $"( let hatomic_action_idx, hsteps = my_special_case_steps_updater_{index} actor lsteps s in\n";
                str += indent(3) + "let haction = map_ghost armada_step_to_action hsteps in\n";
                str += indent(4) + "hatomic_action_idx < array_len hatomic_action_array\n";
                str += indent(3) + "/\\ array_index hatomic_action_array hatomic_action_idx == haction\n";
                str += indent(3) + "/\\ (steps_computation actor starts_atomic_block ends_atomic_block hsteps s ==\n";
                str += indent(5) + "steps_computation actor starts_atomic_block ends_atomic_block lsteps s))\n";
                str += indent(1) + "with introduce _ ==> _\n";
                str += indent(1) + "with _.\n";
                str += indent(2) + $"let hatomic_action_idx, hsteps = my_special_case_steps_updater_{index} actor lsteps s in\n";
                str += indent(2) + $"list_to_array_implies_nth_equivalent hatomic_action_array {HAtomicName}.prog.actions hatomic_action_idx;\n";
                str += indent(2) + $"my_special_case_steps_updater_satisfies_weakening_{index} actor starts_atomic_block ends_atomic_block\n";
                str += indent(3) + "lsteps hatomic_action_idx hsteps s\n\n";
            }
            
            str += indent(0) + "private let my_weakening_transformers\n";
            str += indent(1) + $": list (armada_weakening_transformer_t (list_to_array {HAtomicName}.prog.actions) my_inv) =\n";
            str += indent(1) + "[\n";
            var Transformers = proofSpec.WeakeningTrans;
            for (int i = 0; i < Transformers.Count; i++)
            {
                str += indent(2) + Transformers[i] + ((i == Transformers.Count - 1) ? "": ";") + "\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + $"let lemma_{LAtomicName}_refines_{HAtomicName} ()\n";
            str += indent(1) + $": Lemma (spec_refines_spec\n";
            str += indent(5) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {LAtomicName}.prog)\n";
            str += indent(5) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {HAtomicName}.prog)\n";
            str += indent(5) + $"eq2) =\n";
            str += indent(2) + $"let ww: armada_weakening_witness_t {LAtomicName}.prog {HAtomicName}.prog = {{\n";
            str += indent(3) + $"inv = my_inv;\n";
            str += indent(3) + $"hatomic_action_array = list_to_array {HAtomicName}.prog.actions;\n";
            str += indent(3) + $"weakening_transformers = my_weakening_transformers;\n";
            str += indent(3) + $"init_implies_init_proof = (fun _ -> ());\n";
            str += indent(2) + $"}} in\n";
            str += indent(2) + $"assert (armada_weakening_witness_valid {LAtomicName}.prog {HAtomicName}.prog ww)\n";
            str += indent(3) + $"by (compute (); trivial ());\n";
            str += indent(2) + "my_inv_is_stepwise_invariant ();\n";
            str += indent(2) + $"armada_weakening_witness_valid_implies_refinement {LAtomicName}.prog {HAtomicName}.prog ww\n\n";

            str += indent(0) + $"let lemma_{LName}_refines_{HName} ()\n";
            str += indent(1) + $": Lemma (spec_refines_spec\n";
            str += indent(5) + $"(program_to_spec {LName}.prog)\n";
            str += indent(5) + $"(program_to_spec {HName}.prog)\n";
            str += indent(5) + $"eq2) =\n";
            str += indent(1) + $"lemma_{LName}_refines_{LAtomicName} ();\n";
            str += indent(1) + $"lemma_{LAtomicName}_refines_{HAtomicName} ();\n";
            str += indent(1) + $"lemma_{HAtomicName}_refines_{HName} ();\n";
            str += indent(1) + $"spec_refinement_transitivity_4\n";
            str += indent(2) + $"(program_to_spec {LName}.prog)\n";
            str += indent(2) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {LAtomicName}.prog)\n";
            str += indent(2) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {HAtomicName}.prog)\n";
            str += indent(2) + $"(program_to_spec {HName}.prog)\n";
            str += indent(2) + $"eq2\n";
            str += indent(2) + $"eq2\n";
            str += indent(2) + $"eq2\n";
            str += indent(2) + $"eq2\n";
            str += indent(2) + $"eq2\n";
            return str;
        }

        public string GetInvariant(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LName = L.Name.ToString(0, false);
            var LAtomicName = "Atomic" + LName;
            var HName = H.Name.ToString(0, false);
            var HAtomicName = "Atomic" + HName;
            AtomicSpec atomicSpecL = new AtomicSpec(L);

            str += indent(0) + "let my_inv (s: Armada.State.t) : GTot ubool = true\n\n";

            str += indent(0) + "private let my_action_pred (action: Armada.Action.t) : GTot ubool = true\n\n";

            str += indent(0) + "private let my_special_case_proofs\n";
            str += indent(1) + ": list (option (armada_atomic_special_case_invariant_proof_t my_inv)) =\n";
            str += indent(1) + "[\n";
            for (int i = 0; i < atomicSpecL.Actions.Count; i++)
            {
                str += indent(2) + "None" + (i + 1 == atomicSpecL.Actions.Count ? "" : ";") + '\n';
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + "private let atomic_lprog_init_establishes_my_inv\n";
            str += indent(1) + $"(s: Armada.State.t{{(semantics_to_spec (make_atomic_semantics armada_semantics) {LAtomicName}.prog).init s}})\n";
            str += indent(1) + ": squash (my_inv s) = ()\n\n";

            str += indent(0) + "private let my_action_pred_preserves_my_inv\n";
            str += indent(1) + "(actor: tid_t)\n";
            str += indent(1) + "(starts_atomic_block: bool)\n";
            str += indent(1) + "(ends_atomic_block: bool)\n";
            str += indent(1) + "(step: Armada.Step.t)\n";
            str += indent(1) + "(s: Armada.State.t{\n";
            str += indent(3) + "Some? (step_computation actor starts_atomic_block ends_atomic_block step s)\n";
            str += indent(2) + "/\\ my_action_pred step.action\n";
            str += indent(2) + "/\\ my_inv s})\n";
            str += indent(1) + ": squash (my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) = ()\n\n";

            str += indent(0) + $"let my_inv_witness () : armada_atomic_semantics_invariant_witness_t {LAtomicName}.prog my_inv =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "action_pred = my_action_pred;\n";
            str += indent(2) + "special_case_proofs = my_special_case_proofs;\n";
            str += indent(2) + "init_implies_inv_proof = atomic_lprog_init_establishes_my_inv;\n";
            str += indent(2) + "action_proof = my_action_pred_preserves_my_inv;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let my_inv_is_stepwise_invariant ()\n";
            str += indent(1) + ": Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)\n";
            str += indent(5) + $"{LAtomicName}.prog my_inv) =\n";
            str += indent(1) + "let aiw = my_inv_witness () in\n";
            str += indent(1) + $"assert (armada_atomic_semantics_invariant_witness_valid {LAtomicName}.prog my_inv aiw)\n";
            str += indent(2) + "by (FStar.Tactics.compute (); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant {LAtomicName}.prog my_inv aiw\n";
            return str;
        }
    }
}
