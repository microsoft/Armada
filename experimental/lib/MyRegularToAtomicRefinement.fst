module MyRegularToAtomicRefinement

open Armada.Action
open Armada.Base
open Armada.BinaryOp
open Armada.Expression
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open FStar.Tactics
open MyAtomicLProg
open MyLProg
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.Atomic
open Strategies.PCIndices
open Strategies.RegularToAtomic
open Strategies.RegularToAtomic.Armada
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.ImmutableArray
open Util.Nth
open Util.Range

// This is all the PCs in the program.

let my_lpcs: array_t pc_t = list_to_array [ "main.0"; "main.1"; "main.2"; "main.3"; "main.4"; "main.5" ]

// The start PC is "main.0", which is the 0th element of the my_lpcs array.

let my_lprog_main_start_pc_index = 0

// Every PC is breaking except "main.2" and "main.3":

let my_pc_index_breaking : array_t bool = list_to_array [ true; true; false; false; true; true ]

// The ten actions are:
// 0 - ok = true, start_pc = "main.0", end_pc = "main.1"
// 1 - ok = false, start_pc = "main.0", end_pc = "main.1"
// 2 - ok = true, start_pc = "main.1", end_pc = "main.2"
// 3 - ok = false, start_pc = "main.1", end_pc = "main.2"
// 4 - ok = true, start_pc = "main.2", end_pc = "main.3"
// 5 - ok = false, start_pc = "main.2", end_pc = "main.3"
// 6 - ok = true, start_pc = "main.3", end_pc = "main.4"
// 7 - ok = false, start_pc = "main.3", end_pc = "main.4"
// 8 - ok = true, start_pc = "main.4", end_pc = "main.5"
// 9 - ok = false, start_pc = "main.4", end_pc = "main.5"

let make_pc_indices (start_pc_index: nat) (end_pc_index: nat) : statement_pc_indices_t =
  {
    start_pc_index = Some start_pc_index;
    end_pc_index = Some end_pc_index;
    create_thread_initial_pc_index = None;
    method_call_return_pc_index = None;
  }

// This array gives the indices of the PCs mentioned in the ten actions.
// None of them are create-thread or method-call instructions, so they
// always use None for the last two fields of each statement_pc_indices_t.

let my_pc_indices_array: array_t statement_pc_indices_t = list_to_array
  [
    make_pc_indices 0 1; // Action 0 goes from "main.0" to "main.1"
    make_pc_indices 0 1; // Action 1 goes from "main.0" to "main.1"
    make_pc_indices 1 2; // Action 2 goes from "main.1" to "main.2"
    make_pc_indices 1 2; // Action 3 goes from "main.1" to "main.2"
    make_pc_indices 2 3; // Action 4 goes from "main.2" to "main.3"
    make_pc_indices 2 3; // Action 5 goes from "main.2" to "main.3"
    make_pc_indices 3 4; // Action 6 goes from "main.3" to "main.4"
    make_pc_indices 3 4; // Action 7 goes from "main.3" to "main.4"
    make_pc_indices 4 5; // Action 8 goes from "main.4" to "main.5"
    make_pc_indices 4 5  // Action 9 goes from "main.4" to "main.5"
  ]

// This is the list of action indices with a start_pc of None.  We don't have
// any in this program because we don't include tau.

let my_action_indices_starting_at_no_pc: list nat = []

// This is a list of, for each PC, the list of actions that start at that PC.

let my_action_indices_starting_at_pc_index: array_t (list nat) = list_to_array
  [
    [0; 1]; // The actions starting at "main.0" are actions 0 and 1
    [2; 3]; // The actions starting at "main.1" are actions 2 and 3
    [4; 5]; // The actions starting at "main.2" are actions 4 and 5
    [6; 7]; // The actions starting at "main.3" are actions 6 and 7
    [8; 9]; // The actions starting at "main.4" are actions 8 and 9
    []      // The actions starting at "main.5" are <empty set>
  ]

let make_successor_info (action_index: nat) (path_index: nat) : armada_successor_info_t =
  {
    action_index = action_index;
    path_index = path_index;
  }

let make_breaking_atomic_path_info
  (path: list nat)
  (atomic_action_index: nat)
  : armada_atomic_path_info_t =
  {
    path = path;
    atomic_action_index_or_successors = Inl atomic_action_index;
  }

let make_incomplete_atomic_path_info
  (path: list nat)
  (successors: list armada_successor_info_t) =
  {
    path = path;
    atomic_action_index_or_successors = Inr successors;
  }

// The following are all the paths, i.e., all the prefixes of atomic actions:

let my_atomic_path_infos: array_t armada_atomic_path_info_t = list_to_array
  [
    // Path 0:  Action 0 by itself is a full atomic action (#0)
    make_breaking_atomic_path_info [0] 0;
    // Path 1:  Action 1 by itself is a full atomic action (#1)
    make_breaking_atomic_path_info [1] 1;
    // Path 2:  Action 2 by itself doesn't break and can be succeeded by action 4 or 5,
    //          producing path 6 or 7 respectively
    make_incomplete_atomic_path_info [2] [make_successor_info 4 6; make_successor_info 5 7];
    // Path 3:  Action 3 by itself is a full atomic action (#3)
    make_breaking_atomic_path_info [3] 3;
    // Path 4:  Action 8 by itself is a full atomic action (#6)
    make_breaking_atomic_path_info [8] 6;
    // Path 5:  Action 9 by itself is a full atomic action (#7)
    make_breaking_atomic_path_info [9] 7;
    // Path 6:  Actions 2 and 4 in succession don't break and can be succeeded by action 6 or 7,
    //          producing path 8 or 9 respectively
    make_incomplete_atomic_path_info [2; 4] [make_successor_info 6 8; make_successor_info 7 9];
    // Path 7:  Actions 2 and 5 in succession constitute a full atomic action (#4)
    make_breaking_atomic_path_info [2; 5] 4;
    // Path 8:  Actions 2, 4, and 6 in succession constitute a full atomic action (#2)
    make_breaking_atomic_path_info [2; 4; 6] 2;
    // Path 9:  Actions 2, 4, and 7 in succession constitute a full atomic action (#5)
    make_breaking_atomic_path_info [2; 4; 7] 5;
  ]

// This is a list of, for each action, which path consists only of that action.

let my_singleton_path_indices: array_t (option nat) = list_to_array
  [
    Some 0; // Action 0 by itself is path 0
    Some 1; // Action 1 by itself is path 1
    Some 2; // Action 2 by itself is path 2
    Some 3; // Action 3 by itself is path 3
    None;   // Action 4 by itself isn't among the paths
    None;   // Action 5 by itself isn't among the paths
    None;   // Action 6 by itself isn't among the paths
    None;   // Action 7 by itself isn't among the paths
    Some 4; // Action 8 by itself is path 4
    Some 5  // Action 9 by itself is path 5
  ]

let lemma_MyLProg_refines_MyAtomicLProg ()
  : Lemma (ensures spec_refines_spec
                     (program_to_spec MyLProg.prog)
                     (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicLProg.prog)
                     eq2) =
  let lprog = MyLProg.prog in
  let hprog = MyAtomicLProg.prog in
  let aw: armada_refines_atomic_witness_t = {
    pc_index_breaking = my_pc_index_breaking;
    pc_indices_array = my_pc_indices_array;
    action_indices_starting_at_no_pc = my_action_indices_starting_at_no_pc;
    action_indices_starting_at_pc_index = my_action_indices_starting_at_pc_index;
    atomic_path_infos = my_atomic_path_infos;
    singleton_path_indices = my_singleton_path_indices;
    lpcs = my_lpcs;
    lprog_main_start_pc_index = my_lprog_main_start_pc_index;
    lprog_actions_array = list_to_array (all_actions lprog.program_statements);
    hprog_actions_array = list_to_array hprog.actions;
  } in
  assert (armada_refines_atomic_witness_valid MyLProg.prog MyAtomicLProg.prog aw)
    by (compute (); trivial ());
  armada_refines_atomic_witness_valid_implies_refinement MyLProg.prog MyAtomicLProg.prog aw
