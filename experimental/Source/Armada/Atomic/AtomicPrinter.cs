using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class AtomicPrinter
    {
        public string ToFStarAtomic(LevelDecl level, int indentation, string moduleName)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";

            str += indent(0) + $"let atomic_actions: list (list Armada.Action.t) =\n";
            str += indent(1) + "[\n";
            AtomicSpec atomicSpec = new AtomicSpec(level);
            str += String.Join(";\n", atomicSpec.Actions.ConvertAll(action => ToFStarAtomic(action, indentation + 4))) + '\n';
            str += indent(1) + "]\n\n";
            str += indent(0) + "let prog: (program_t (make_atomic_semantics armada_semantics)) =\n";
            str += indent(1) + "{\n";
            str += indent(2) + $"init_f = init_program {moduleName}.prog;\n";
            str += indent(2) + "actions = atomic_actions;\n";
            str += indent(1) + "}\n";
            return str;
        }

        public string ToFStarAtomic(ExecutionPath action, int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";

            str += indent(0) + "[\n";
            for (int i = 0; i < action.Stmts.Count; i++)
            {
                str += ToFStarAtomic(
                    action.Stmts[i], indentation + 2,
                    !(action.FailAtTheEnd && i + 1 == action.Stmts.Count)
                );
                str += ((i + 1 == action.Stmts.Count) ? "" : ";") + "\n";
            }
            str += indent(0) + "]";
            return str;
        }

        public string ToFStarAtomic(FStarStmt fstmt, int indentation, bool ok)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);

            string str = "";
            string ok_str = ok ? "true" : "false";
            str += indent(0) + "{\n";
            str += indent(1) + $"ok = {ok_str};\n";
            str += indent(1) + "program_statement = \n";
            str += fstmt.GetFStarCodeOfStatement(indentation + 4) + '\n';
            str += indent(0) + "}";
            return str;
        }

        public string AtomicToRegular(LevelDecl level, int indentation)
        {
            AtomicSpec atomicSpec = new AtomicSpec(level);

            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var moduleName = level.Name.ToString(0, false);
            var moduleAtomicName = "Atomic" + moduleName;

            str += "let my_atomic_to_regular_map: (list (list nat)) =\n";
            List<List<int>> atomicToRegularMap = atomicSpec.GetAtomicToRegularMap();
            str += indent(1) + $"[{String.Join("; ", atomicToRegularMap.ConvertAll(indices => $"[{String.Join("; ", indices)}]"))}]" + "\n\n";

            str += $"let lemma_{moduleAtomicName}_refines_{moduleName} ()\n";
            str += indent(1) + ": Lemma (ensures spec_refines_spec\n";
            str += indent(10) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {moduleAtomicName}.prog)\n";
            str += indent(10) + $"(program_to_spec {moduleName}.prog)\n";
            str += indent(10) + "eq2) =\n";
            str += indent(1) + "let aw: atomic_refines_armada_witness_t = {\n";
            str += indent(2) + "atomic_to_regular_map = my_atomic_to_regular_map;\n";
            str += indent(2) + $"actions_array = list_to_array (all_actions {moduleName}.prog.program_statements)\n";
            str += indent(1) + "} in\n";
            str += indent(1) + $"assert (atomic_refines_armada_witness_valid {moduleAtomicName}.prog {moduleName}.prog aw)\n";
            str += indent(2) + "by (FStar.Tactics.compute (); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"atomic_refines_armada_witness_valid_implies_refinement {moduleAtomicName}.prog {moduleName}.prog aw\n";

            return str;
        }

        public string MakePCIndexStarter(int indentation)
        {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            str += indent(0) + "let make_none_pc_indices: statement_pc_indices_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "start_pc_index = None;\n";
            str += indent(2) + "end_pc_index = None;\n";
            str += indent(2) + "create_thread_initial_pc_index = None;\n";
            str += indent(2) + "method_call_return_pc_index = None;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let make_pc_indices (start_pc_index: nat) (end_pc_index: nat) : statement_pc_indices_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "start_pc_index = Some start_pc_index;\n";
            str += indent(2) + "end_pc_index = Some end_pc_index;\n";
            str += indent(2) + "create_thread_initial_pc_index = None;\n";
            str += indent(2) + "method_call_return_pc_index = None;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let make_terminating_pc_indices (start_pc_index: nat) : statement_pc_indices_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "start_pc_index = Some start_pc_index;\n";
            str += indent(2) + "end_pc_index = None;\n";
            str += indent(2) + "create_thread_initial_pc_index = None;\n";
            str += indent(2) + "method_call_return_pc_index = None;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let make_method_call_pc_indices (start_pc_index: nat) (end_pc_index: nat) (method_call_return_pc_index: nat) : statement_pc_indices_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "start_pc_index = Some start_pc_index;\n";
            str += indent(2) + "end_pc_index = Some end_pc_index;\n";
            str += indent(2) + "create_thread_initial_pc_index = None;\n";
            str += indent(2) + "method_call_return_pc_index = Some method_call_return_pc_index;\n";
            str += indent(1) + "}\n\n";

            str += indent(0) + "let make_create_thread_pc_indices (start_pc_index: nat) (end_pc_index: nat) (create_thread_pc_index: nat) : statement_pc_indices_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "start_pc_index = Some start_pc_index;\n";
            str += indent(2) + "end_pc_index = Some end_pc_index;\n";
            str += indent(2) + "create_thread_initial_pc_index = Some create_thread_pc_index;\n";
            str += indent(2) + "method_call_return_pc_index = None;\n";
            str += indent(1) + "}\n\n";
            return str;
        }

        public string MakePCIndex(AtomicSpec atomicSpec, FStarStmt fstmt)
        {
            string str = "";
            if (fstmt.StartPC == null && fstmt.EndPC == null)
            {
                str += $"make_none_pc_indices"; 
                return str;
            }
            int startPCIndex = atomicSpec.PC2Index[fstmt.StartPC];
            if (fstmt.EndPC == null) {
                str += $"make_terminating_pc_indices {startPCIndex}";
                return str;
            }
            int endPCIndex = atomicSpec.PC2Index[fstmt.EndPC];
            if (fstmt.Statement.StartsWith("MethodCallStatement"))
            {
                string returnPC = fstmt.Statement.Split(' ')[2];
                returnPC = returnPC.TrimEnd('"').TrimStart('"');
                int methodCallReturnPCIndex = atomicSpec.PC2Index[returnPC];
                str += $"make_method_call_pc_indices {startPCIndex} {endPCIndex} {methodCallReturnPCIndex}";
            }
            else if (fstmt.Statement.StartsWith("CreateThreadStatement"))
            {
                string initPC = fstmt.Statement.Split(' ')[2];
                initPC = initPC.TrimEnd('"').TrimStart('"');
                int createThreadPCIndex = atomicSpec.PC2Index[initPC];
                str += $"make_create_thread_pc_indices {startPCIndex} {endPCIndex} {createThreadPCIndex}";
            }
            else
            {
                str += $"make_pc_indices {startPCIndex} {endPCIndex}";
            }
            return str;
        }

        public string RegularToAtomic(LevelDecl level, int indentation)
        {
            AtomicSpec atomicSpec = new AtomicSpec(level);

            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            string str = "";
            var moduleName = level.Name.ToString(0, false);
            var moduleAtomicName = "Atomic" + moduleName;

            string pcList = $"[{String.Join("; ", atomicSpec.PCs.ConvertAll(pc => $"\"{pc}\""))}]";
            str += $"let my_lpcs: array_t pc_t = list_to_array {pcList}\n\n";

            str += $"let my_lprog_main_start_pc_index = {atomicSpec.GetStartIndex()}\n\n";

            str += $"let my_pc_index_breaking : array_t bool = list_to_array {atomicSpec.GetBreakPCList()}\n\n";

            str += MakePCIndexStarter(0);

            str += $"let my_pc_indices_array: array_t statement_pc_indices_t = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var fstmt in atomicSpec.Fstmts)
            {
                string pcIndex = MakePCIndex(atomicSpec, fstmt);
                str += indent(2) + pcIndex + ";\n";
                str += indent(2) + pcIndex + ";\n";
            }
            str += indent(1) + "]\n\n";

            List<string> actionIndicesNoPC = new();
            for (int i = 0; i < atomicSpec.Actions.Count; i++)
            {
                var action = atomicSpec.Actions[i];
                if (action.Stmts[0].StartPC == null)
                {
                    actionIndicesNoPC.Add($"{i}");
                }
            }
            str += $"let my_action_indices_starting_at_no_pc: list nat = [{string.Join("; ", actionIndicesNoPC)}]\n\n";

            str += $"let my_action_indices_starting_at_pc_index: array_t (list nat) = list_to_array\n";
            str += indent(1) + "[\n";
            foreach (var kv in atomicSpec.PC2Stmt)
            {
                var fstmts = kv.Value;
                List<int> indices = new();
                foreach (var fstmt in fstmts)
                {
                    indices.Add(atomicSpec.GetFstmtIndex(fstmt, true));
                    indices.Add(atomicSpec.GetFstmtIndex(fstmt, false));
                }
                str += indent(2) + $"[{String.Join("; ", indices)}];\n";
                
            }
            str += indent(1) + "]\n\n";

            str += "let make_successor_info (action_index: nat) (path_index: nat) : armada_successor_info_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "action_index = action_index;\n";
            str += indent(2) + "path_index = path_index;\n";
            str += indent(1) + "}\n\n";

            str += "let make_breaking_atomic_path_info (path: list nat) (atomic_action_index: nat) : armada_atomic_path_info_t =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "path = path;\n";
            str += indent(2) + "atomic_action_index_or_successors = Inl atomic_action_index;\n";
            str += indent(1) + "}\n\n";

            str += "let make_incomplete_atomic_path_info (path: list nat) (successors: list armada_successor_info_t) =\n";
            str += indent(1) + "{\n";
            str += indent(2) + "path = path;\n";
            str += indent(2) + "atomic_action_index_or_successors = Inr successors;\n";
            str += indent(1) + "}\n\n";

            str += $"let my_atomic_path_infos: array_t armada_atomic_path_info_t = list_to_array\n";
            str += indent(1) + "[\n";
            List<string> pathInfos = atomicSpec.GetAtomicPathInfo();
            foreach (string pathInfo in pathInfos)
            {
                str += indent(2) + pathInfo + '\n';
            }
            str += indent(1) + "]\n\n";

            str += $"let my_singleton_path_indices: array_t (option nat) = list_to_array\n";
            str += indent(1) + "[\n";
            List<int> singleton = atomicSpec.GetSingletonPathIndices();
            foreach (var index in singleton)
            {
                str += indent(2) + (index == -1 ? "None" : $"Some {index}") + ";\n";
            }
            str += indent(1) + "]\n\n";

            str += $"let lemma_{moduleName}_refines_{moduleAtomicName} ()\n";
            str += indent(1) + ": Lemma (ensures spec_refines_spec\n";
            str += indent(10) + $"(program_to_spec {moduleName}.prog)\n";
            str += indent(10) + $"(semantics_to_spec (make_atomic_semantics armada_semantics) {moduleAtomicName}.prog)\n";
            str += indent(10) + "eq2) =\n";
            str += indent(1) + $"let lprog = {moduleName}.prog in\n";
            str += indent(1) + $"let hprog = {moduleAtomicName}.prog in\n";
            str += indent(1) + "let aw: armada_refines_atomic_witness_t = {\n";
            str += indent(2) + "pc_index_breaking = my_pc_index_breaking;\n";
            str += indent(2) + "pc_indices_array = my_pc_indices_array;\n";
            str += indent(2) + "action_indices_starting_at_no_pc = my_action_indices_starting_at_no_pc;\n";
            str += indent(2) + "action_indices_starting_at_pc_index = my_action_indices_starting_at_pc_index;\n";
            str += indent(2) + "atomic_path_infos = my_atomic_path_infos;\n";
            str += indent(2) + "singleton_path_indices = my_singleton_path_indices;\n";
            str += indent(2) + "lpcs = my_lpcs;\n";
            str += indent(2) + "lprog_main_start_pc_index = my_lprog_main_start_pc_index;\n";
            str += indent(2) + "lprog_actions_array = list_to_array (all_actions lprog.program_statements);\n";
            str += indent(2) + "hprog_actions_array = list_to_array hprog.actions;\n";
            str += indent(1) + "} in\n";
            str += indent(1) + $"assert (armada_refines_atomic_witness_valid {moduleName}.prog {moduleAtomicName}.prog aw)\n";
            str += indent(2) + "by (FStar.Tactics.compute (); FStar.Tactics.trivial ());\n";
            str += indent(1) + $"armada_refines_atomic_witness_valid_implies_refinement {moduleName}.prog {moduleAtomicName}.prog aw";

            return str;
        }
    }
}
