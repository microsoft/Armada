using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class InvariantPrinter
    {
        public static string GetProof(LevelDecl Level, InvariantDecl Inv, int indentation) {
            switch (Inv.InvType) {
                case InvariantType.MAINTAINED_IF_STATEMENT_SATISFIES:
                    return GetInvMaintainedIfStatementSatistiesProof(Level, Inv.Body, indentation);
                case InvariantType.MAINTAINED_IF_VARS_UNCHANGED:
                    return GetInvMaintainedIfVariablesUnchangedProof(Level, Inv.UnchangedVars, Inv.Body, indentation);
                default:
                    throw new NotSupportedException();
            }
        }
        public static string GetInvMaintainedIfStatementSatistiesProof(
            LevelDecl Level, Expr invariant, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LevelName = Level.Name.ToString(0, false);
            var LevelAtomicName = "Atomic" + LevelName;
            Scope sc = Level.Sc;
            var LevelSpec = new AtomicSpec(Level);

            str += indent(0) + $"let my_inv (s: Armada.State.t) : GTot ubool = {invariant.ToFStarExpr("s")}\n\n";

            str += indent(0) + $"private let my_action_pred (action: Armada.Action.t) : GTot ubool = True\n\n";

            str += indent(0) + "#push-options \"--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100\"\n\n";

            str += indent(0) + "private let atomic_lprog_init_establishes_my_inv\n";
            str += indent(1) + $"(s: Armada.State.t{{(semantics_to_spec (make_atomic_semantics armada_semantics) {LevelAtomicName}.prog).init s}})\n";
            str += indent(1) + ": squash (my_inv s) =\n";
            str += indent(1) + "()\n\n";

            str += indent(0) + "private let my_action_pred_preserves_my_inv\n";
            str += indent(1) + "(actor: tid_t)\n";
            str += indent(1) + "(starts_atomic_block: bool)\n";
            str += indent(1) + "(ends_atomic_block: bool)\n";
            str += indent(1) + "(step: Armada.Step.t)\n";
            str += indent(1) + "(s: Armada.State.t{\n";
            str += indent(2) + "Some? (step_computation actor starts_atomic_block ends_atomic_block step s)\n";
            str += indent(2) + "/\\ my_action_pred step.action\n";
            str += indent(2) + "/\\ my_inv s})\n";
            str += indent(1) + ": squash (my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) =\n";
            str += indent(1) + "()\n\n";

            str += indent(0) + "#pop-options\n\n";

            str += indent(0) + "private let my_special_case_proofs\n";
            str += indent(1) + ": list (option (armada_atomic_special_case_invariant_proof_t my_inv)) =\n";
            str += indent(1) + "[\n";
            foreach (var action in LevelSpec.Actions)
            {
                str += indent(2) + $"{String.Join("; ", action.Stmts.ConvertAll(stmt => "None"))};\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + $"let my_inv_witness () : armada_atomic_semantics_invariant_witness_t {LevelAtomicName}.prog my_inv =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "action_pred = my_action_pred;\n";
            str += indent(2) + "special_case_proofs = my_special_case_proofs;\n";
            str += indent(2) + "init_implies_inv_proof = atomic_lprog_init_establishes_my_inv;\n";
            str += indent(2) + "action_proof = my_action_pred_preserves_my_inv;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let inv_is_stepwise_invariant ()\n";
            str += indent(1) + $": Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics)\n";
            str += indent(6) + $"{LevelAtomicName}.prog my_inv) =\n";
            str += indent(1) + "let aiw = my_inv_witness () in\n";
            str += indent(1) + $"assert (armada_atomic_semantics_invariant_witness_valid {LevelAtomicName}.prog my_inv aiw)\n";
            str += indent(2) + "by (FStar.Tactics.compute(); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant {LevelAtomicName}.prog my_inv aiw\n\n";
            return str;
        }

        public static string GetInvMaintainedIfVariablesUnchangedProof(
            LevelDecl Level, List<Ident> Variables, Expr invariant, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var LevelName = Level.Name.ToString(0, false);
            var LevelAtomicName = "Atomic" + LevelName;
            Scope sc = Level.Sc;
            var LevelSpec = new AtomicSpec(Level);

            str += indent(0) + "let vs = [\n";
            var sep = "";
            foreach (var v in Variables)
            {
                str += sep + indent(1) + $"\"{v.Name}\"";
                sep = ";\n";
            }
            str += "\n]\n\n";

            str += indent(0) + $"private let my_inv (s: Armada.State.t) : GTot ubool =";
            str += indent(1) + $"{invariant.ToFStarExpr("s")}\n\n";

            str += indent(0) + $"private let my_action_pred (action: Armada.Action.t) : GTot ubool =\n";
            str += indent(2) + "(not action.ok)\n";
            str += indent(1) + "\\/ ( global_variables_unmodifiable_by_statement vs action.program_statement.statement\n";
            str += indent(2) + "/\\ global_variables_unaddressable_in_statement vs action.program_statement.statement\n";
            str += indent(1) + ")\n\n";

            str += indent(0) + $"private let inductive_inv (s: Armada.State.t) : GTot ubool =\n";
            str += indent(2) + $"roots_match s.mem\n";
            str += indent(1) + $"/\\ positions_valid_in_state s\n";
            str += indent(1) + $"/\\ global_variables_unaddressed_in_memory vs s.mem\n\n";

            str += indent(0) + $"private let inductive_my_inv (s: Armada.State.t) : GTot ubool =\n";
            str += indent(1) + $"inductive_inv s /\\ my_inv s\n\n";

            str += indent(0) + $"private let step_relation (s s': Armada.State.t): GTot ubool =\n";
            str += indent(1) + $"states_match_on_global_variables vs s s'\n\n";

            str += indent(0) + $"private let step_relation_preserves_my_inv (s s': Armada.State.t)\n";
            str += indent(1) + $": Lemma (requires my_inv s /\\ step_relation s s')\n";
            str += indent(5) + $"(ensures  my_inv s') =\n";
            str += indent(1) + $"()\n\n";

            str += indent(0) + "#push-options \"--z3rlimit 10 --z3cliopt smt.qi.eager_threshold=100\"\n\n";

            str += indent(0) + "private let atomic_lprog_init_establishes_inductive_my_inv\n";
            str += indent(1) + $"(s: Armada.State.t{{(semantics_to_spec (make_atomic_semantics armada_semantics) {LevelAtomicName}.prog).init s}})\n";
            str += indent(1) + ": squash (inductive_my_inv s) =\n";
            str += indent(1) + $"init_implies_global_variables_unaddressed_in_memory vs {LevelName}.prog s\n\n";

            str += indent(0) + "private let my_action_pred_preserves_inductive_my_inv_proof\n";
            str += indent(1) + "(actor: tid_t)\n";
            str += indent(1) + "(starts_atomic_block ends_atomic_block: bool)\n";
            str += indent(1) + "(step: Armada.Step.t)\n";
            str += indent(1) + "(s: Armada.State.t)\n";
            str += indent(1) + ": Lemma (requires   Some? (step_computation actor starts_atomic_block ends_atomic_block step s)\n";
            str += indent(10) + "/\\ my_action_pred step.action\n";
            str += indent(10) + "/\\ inductive_my_inv s)\n";
            str += indent(5) + "(ensures    inductive_my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s)))\n";
            str += indent(1) + "= executing_statement_maintains_roots_match actor step.nd ((s.threads actor).pc) step.action.program_statement.end_pc step.action.program_statement.statement s;\n";
            str += indent(2) + "executing_statement_maintains_positions_valid_in_state actor step.nd ((s.threads actor).pc) step.action.program_statement.end_pc step.action.program_statement.statement s;\n";
            str += indent(2) + "if (step.action.ok) then begin\n";
            str += indent(3) + "global_variables_unaddressable_by_statement_global_vars_unaddressed_in_state vs actor step starts_atomic_block ends_atomic_block s;\n";
            str += indent(3) + "global_variables_unmodifiable_by_statement_memories_matches_on_global_variables vs actor step starts_atomic_block ends_atomic_block s;\n";
            str += indent(3) + "step_relation_preserves_my_inv s (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))\n";
            str += indent(2) + "end\n\n";

            str += indent(0) + "private let my_action_pred_preserves_inductive_my_inv\n";
            str += indent(1) + "(actor: tid_t)\n";
            str += indent(1) + "(starts_atomic_block: bool)\n";
            str += indent(1) + "(ends_atomic_block: bool)\n";
            str += indent(1) + "(step: Armada.Step.t)\n";
            str += indent(1) + "(s: Armada.State.t{\n";
            str += indent(2) + "Some? (step_computation actor starts_atomic_block ends_atomic_block step s)\n";
            str += indent(2) + "/\\ my_action_pred step.action\n";
            str += indent(2) + "/\\ my_inv s})\n";
            str += indent(1) + ": squash (inductive_my_inv (Some?.v (step_computation actor starts_atomic_block ends_atomic_block step s))) =\n";
            str += indent(1) + "my_action_pred_preserves_inductive_my_inv_proof actor starts_atomic_block ends_atomic_block step s\n\n";

            str += indent(0) + "#pop-options\n\n";

            str += indent(0) + "private let my_special_case_proofs\n";
            str += indent(1) + ": list (option (armada_action_special_case_invariant_proof_t my_inv)) =\n";
            str += indent(1) + "[\n";
            foreach (var action in LevelSpec.Actions)
            {
                str += indent(2) + $"{String.Join("; ", action.Stmts.ConvertAll(stmt => "None"))};\n";
            }
            str += indent(1) + "]\n\n";

            str += indent(0) + $"let inductive_my_inv_witness () : armada_atomic_semantics_invariant_witness_t {LevelAtomicName}.prog inductive_my_inv =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "action_pred = my_action_pred;\n";
            str += indent(2) + "special_case_proofs = my_special_case_proofs;\n";
            str += indent(2) + "init_implies_inv_proof = atomic_lprog_init_establishes_inductive_my_inv;\n";
            str += indent(2) + "action_proof = my_action_pred_preserves_inductive_my_inv;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let my_inv_is_stepwise_invariant ()\n";
            str += indent(1) + $": Lemma (semantics_has_stepwise_inductive_invariant (make_atomic_semantics armada_semantics) {LevelAtomicName}.prog inductive_my_inv) =\n";
            str += indent(1) + "let aiw = inductive_my_inv_witness () in\n";
            str += indent(1) + $"assert (armada_atomic_semantics_invariant_witness_valid {LevelAtomicName}.prog inductive_my_inv aiw)\n";
            str += indent(2) + "by (FStar.Tactics.compute(); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"armada_atomic_semantics_invariant_witness_valid_implies_stepwise_invariant {LevelAtomicName}.prog inductive_my_inv aiw\n\n";
            return str;
        }
    }
}
