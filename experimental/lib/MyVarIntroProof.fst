module MyVarIntroProof

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open Spec.Behavior
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.GlobalVars.Types
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.PCIndices
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Efficient
open Util.ImmutableArray

let vs: list var_id_t = // introduced variables in no particular order
  [
    "b";
    "d";
  ]

let tds: list object_td_t = // object type descriptors for the introduced variables in the order corresponding to `vs`
  [
    (ObjectTDAbstract int); // "b" is an abstract int
    (ObjectTDAbstract int); // "d" is an abstract int
  ]

let which_initializers_are_intros: list bool =
  [
    false; // The first initializer in B.global_initializers is a, which is not being introduced
    true;  // b *is* being introduced
    false; // c is not being introduced
    true;  // d is being introduced
    false; // e is not being introduced
  ]

let lpcs: array_t pc_t = list_to_array
  [
    "main.1";         // by index, known as A.PC #0
    "main.2.1";       // by index, known as A.PC #1
    "main.2.2";       // by index, known as A.PC #2
    "main.3";         // by index, known as A.PC #3
    "main.3.R";       // by index, known as A.PC #4
    "main.End";       // by index, known as A.PC #5
    "subroutine.1";   // by index, known as A.PC #6
    "subroutine.End"; // by index, known as A.PC #7
  ]

let hpcs: array_t pc_t = list_to_array
  [
    "main.1.1";       // by index, known as B.PC #0
    "main.1.2";       // by index, known as B.PC #1
    "main.1.3";       // by index, known as B.PC #2
    "main.2.1";       // by index, known as B.PC #3
    "main.2.2";       // by index, known as B.PC #4
    "main.2.3";       // by index, known as B.PC #5
    "main.3";         // by index, known as B.PC #6
    "main.3.R";       // by index, known as B.PC #7
    "main.4.1";       // by index, known as B.PC #8
    "main.4.2";       // by index, known as B.PC #9
    "main.End";       // by index, known as B.PC #10
    "subroutine.1";   // by index, known as B.PC #11
    "subroutine.2";   // by index, known as B.PC #12
    "subroutine.3";   // by index, known as B.PC #13
    "subroutine.End"; // by index, known as B.PC #14
  ]

let hpc_to_lpc: array_t nat = list_to_array
  [
    0; // B.main.1.1 (which is B.PC #0) maps to A.main.1 (which is A.PC #0)
    0; // B.main.1.2 (which is B.PC #1) maps to A.main.1 (which is A.PC #0)
    1; // B.main.1.3 (which is B.PC #2) maps to A.main.2.1 (which is A.PC #1)
    1; // B.main.2.1 (which is B.PC #3) maps to A.main.2.1 (which is A.PC #1)
    2; // B.main.2.2 (which is B.PC #4) maps to A.main.2.2 (which is A.PC #2)
    2; // B.main.2.3 (which is B.PC #5) maps to A.main.2.2 (which is A.PC #2)
    3; // B.main.3 (which is B.PC #6) maps to A.main.3 (which is A.PC #3)
    4; // B.main.3.R (which is B.PC #7) maps to A.main.3.R (which is A.PC #4)
    5; // B.main.4.1 (which is B.PC #8) maps to A.main.End (which is A.PC #5)
    5; // B.main.4.2 (which is B.PC #9) maps to A.main.End (which is A.PC #5)
    5; // B.main.End (which is B.PC #10) maps to A.main.End (which is A.PC #5)
    6; // B.subroutine.1 (which is B.PC #11) maps to A.subroutine.1 (which is A.PC #6)
    7; // B.subroutine.2 (which is B.PC #12) maps to A.subroutine.End (which is A.PC #7)
    7; // B.subroutine.3 (which is B.PC #13) maps to A.subroutine.End (which is A.PC #7)
    7; // B.subroutine.End (which is B.PC #14) maps to A.subroutine.End (which is A.PC #7)
  ]

let lpc_to_hpcs: array_t (list nat) = list_to_array
  [
    [0; 1];     // A.main.1 (which is A.PC #0) maps to B.PCs #0, #1
    [2; 3];     // A.main.2.1 (which is A.PC #1) maps to B.PCs #2, #3
    [4; 5];     // A.main.2.2 (which is A.PC #2) maps to B.PCs #4, #5
    [6];        // A.main.3 (which is A.PC #3) maps to B.PC #6
    [7];        // A.main.3.R (which is A.PC #4) maps to B.PC #7
    [8; 9; 10]; // A.main.End (which is A.PC #5) maps to B.PCs #8, #9, #10
    [11];       // A.subroutine.1 (which is A.PC #6) maps to B.PC #11
    [12; 13; 14];  // A.subroutine.End (which is A.PC #7) maps to B.PCs #12, #13, #14
  ]

let is_return_hpc: array_t bool = list_to_array
  [
    false; // B.PC #0 isn't a return PC
    false; // B.PC #1 isn't a return PC
    false; // ...
    false;
    false;
    false;
    false;
    true;  // only B.main.3.R (which is B.PC #7) is a return PC (one that's pushed on the stack to be returned to)
    false;
    false;
    false;
    false;
    false;
    false;
    false;
  ]

let is_nonyielding_lpc: array_t bool = list_to_array
  [
    false; // A.main.1 is not nonyielding
    false; // A.main.2.1 is not nonyielding
    true;  // A.main.2.2 is nonyielding
    false; // A.main.3 is not nonyielding
    false; // A.main.3.R is not nonyielding
    false; // A.main.End is not nonyielding
    false; // A.subroutine.1 is not nonyielding
    false; // A.subroutine.End is not nonyielding
  ]

let is_nonyielding_hpc: array_t bool = list_to_array
  [
    false; // B.main.1.1 is not nonyielding
    true;  // B.main.1.2 is nonyielding
    true;  // B.main.1.3 is nonyielding
    false; // B.main.2.1 is not nonyielding
    true;  // B.main.2.2 is nonyielding
    true;  // B.main.2.3 is nonyielding
    false; // B.main.3 is not nonyielding
    false; // B.main.3.R is not nonyielding
    false; // B.main.4.1 is not nonyielding
    true;  // B.main.4.2 is nonyielding
    false; // B.main.End is not nonyielding
    false; // B.subroutine.1 is not nonyielding
    false; // B.subroutine.2 is not nonyielding
    false; // B.subroutine.3 is not nonyielding
    false; // B.subroutine.End is not nonyielding
  ]

// The is_breaking_hpc array describes which high-level PCs are PCs at
// which atomic actions are broken up. Generally, this is the opposite
// of nonyielding PCs, since yielding PCs are break points. However,
// sometimes other PCs are break points (entry points of atomic
// recursive functions and heads of atomic loops).

let is_breaking_hpc: array_t bool = list_to_array
  [
    true; // B.main.1.1 is a break point
    false;  // B.main.1.2 is not a break point
    false;  // B.main.1.3 is not a break point
    true; // B.main.2.1 is a break point
    false;  // B.main.2.2 is not a break point
    false;  // B.main.2.3 is not a break point
    true; // B.main.3 is a break point
    true; // B.main.3.R is a break point
    true; // B.main.4.1 is a break point
    false;  // B.main.4.2 is not a break point
    true; // B.main.End is a break point
    true; // B.subroutine.1 is a break point
    true; // B.subroutine.2 is a break point
    true; // B.subroutine.3 is a break point
    true; // B.subroutine.End is a break point
  ]

/// For each introduced statement in the high-level program, if it
/// doesn't just assign a constant that's a primitive or abstract
/// value, we have to provide a witness that it can't crash.

// The subroutine_2 statement is `b := a`

let statement_subroutine_2: program_statement_t =
  (* b := a; *)
  {
    start_pc = Some "subroutine.2";
    end_pc = Some "subroutine.3";
    starts_atomic_block = true;
    ends_atomic_block = true;
    statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "b") (ExpressionGlobalVariable (ObjectTDAbstract int) "a");
  }

// We need to write a proof that the statement `b := a` can't crash,
// because it doesn't just assign a constant.  It depends on the
// invariant that the global variable `a` exists and has the same type
// as `b`.

let lemma_cant_crash_subroutine_2
  (actor: tid_t)
  (s: Armada.State.t{
      MyAtomicBInvariant.inv s
    /\ all_gvars_have_types s.mem vs tds
    /\ NotStopped? s.stop_reason
    /\ ThreadStatusRunning? (s.threads actor).status
    /\ statement_subroutine_2.start_pc = Some (s.threads actor).pc})
  : squash (let ps = statement_subroutine_2 in
            ComputationProduces? (statement_computation actor [] (Some?.v ps.start_pc) ps.end_pc ps.statement s)) =
  ()

// This is the witness for the uncrashability of the subroutine_2 statement.

let introduction_succeeds_witness_subroutine_2: introduction_succeeds_witness_t vs tds MyAtomicBInvariant.inv =
  IntroductionSucceedsProof statement_subroutine_2 lemma_cant_crash_subroutine_2

// In hpc_info, we describe any atomic blocks (including single
// statements outside of atomic blocks) that are completely newly
// introduced.  This doesn't count assignment statements that are
// introduced into existing atomic blocks.  So, for instance, where A
// has `a := 10;` and B has `atomic { d := 5; a := 10; e := 15; }`,
// this doesn't count as an introduced assignment.  That's a
// correspondence between an A atomic block and a B atomic block,
// which will be described later.

let hpc_info: array_t (efficient_hpc_info_t vs tds MyAtomicBInvariant.inv) = list_to_array
  [
    EfficientHPCInfoNormal; // B.main.1.1 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.1.2 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.1.3 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.2.1 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.2.2 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.2.3 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.3 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.3.R isn't a PC with an introduced atomic block
    EfficientHPCInfoIntroduced 22 10 [IntroductionSucceedsBecauseItAssignsConstant;
                                      IntroductionSucceedsBecauseItAssignsConstant] 1;
      // B.main.4.1 is a PC with an introduced atomic block. It's B's atomic action #22,
      // which ends at PC B.main.End (B.PC #10). We assign it progress value 1 because
      // when B is at main.4.1, it has 1 more atomic block to execute (#22) before it
      // doesn't have to introduce any more atomic blocks.
    EfficientHPCInfoNormal; // B.main.4.2 isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.main.End isn't a PC with an introduced atomic block
    EfficientHPCInfoNormal; // B.subroutine.1 isn't a PC with an introduced atomic block
    EfficientHPCInfoIntroduced 14 13 [introduction_succeeds_witness_subroutine_2] 2;
      // B.subroutine.2 is a PC with an introduced atomic block. It's B's atomic action #14,
      // which ends at PC B.subroutine.3 (B.PC #13). We assign it progress value 2
      // because when B is at subroutine.1, it has 2 more atomic block to execute (#14, #16)
      // before it doesn't have to introduce any more atomic blocks.
    EfficientHPCInfoIntroduced 16 14 [IntroductionSucceedsBecauseItAssignsConstant] 1;
      // B.subroutine.3 is a PC with an introduced atomic block. It's B's atomic action #16,
      // which ends at PC B.subroutine.End (B.PC #14). We assign it progress value 1
      // because when B is at subroutine.2, it has 1 more atomic block to execute (#16)
      // before it doesn't have to introduce any more atomic blocks.
    EfficientHPCInfoNormal; // B.subroutine.End isn't a PC with an introduced atomic block
  ]

// In corresponding_hactions_info, we describe, for each low-level
// atomic action, what the corresponding high-level atomic action is.
// In most cases, it'll be the identical one. But in some, it'll be
// one that adds one or more introduced assignments. Correspondences
// are usually CorrespondenceNormal, but for the propagate action we
// use CorrespondencePropagate. For each of the CorrespondenceNormal
// entries, we need to provide a "mapper" that maps the list of
// high-level actions to the list of low-level actions.

let corresponding_hactions_info: array_t (ltoh_correspondence_t vs tds MyAtomicBInvariant.inv) = list_to_array
  [
    // Low-level action #A.0 is a := 10 with ok = true.
    CorrespondenceNormal
      0 // It corresponds to high-level action #B.0, which is atomic { d := 5; a := 10; e := 15 } (ok=true)
      [
        MapperIntroduced IntroductionSucceedsBecauseItAssignsConstant; // The action d := 5 is introduced
        MapperMatching;                                // The action a := 10 is the same as at the low level
        MapperIntroduced IntroductionSucceedsBecauseItAssignsConstant; // The action e := 15 is introduced
      ];
    // Low-level action #A.1 is a := 10 with ok = false.
    CorrespondenceNormal
      2 // It corresponds to high-level action #B.2, which is atomic { d := 5 (ok=true); a := 10 (ok=false) }
      [
        MapperIntroduced IntroductionSucceedsBecauseItAssignsConstant; // The action d := 5 is introduced
        MapperMatching;                                // The action a := 10 is the same as at the low level
      ];
    // Low-level action #A.2 is c := 20; e := 30 with ok = true, true
    CorrespondenceNormal
      4 // It corresponds to high-level action #B.4, which is atomic { c := 20; b := 25; e := 20 } (all ok)
      [
        MapperMatching;                                // The action c := 20 is the same as at the low level
        MapperIntroduced IntroductionSucceedsBecauseItAssignsConstant; // The action b := 25 is introduced
        MapperMatching;                                // The action e := 30 is the same as at the low level
      ];
    // Low-level action #A.3 is c := 20 with ok = false
    CorrespondenceNormal
      5 // It corresponds to high-level action #B.5, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.4 is c := 20; e := 30 with ok = true, false
    CorrespondenceNormal
      7 // It corresponds to high-level action #B.7, which is atomic { c := 20; b := 25; e := 20 (ok=false) }
      [
        MapperMatching;                           // The action c := 20 is the same as at the low level
        MapperIntroduced IntroductionSucceedsBecauseItAssignsConstant; // The action b := 25 is introduced
        MapperMatching;                           // The action e := 30 is the same as at the low level
      ];
    // Low-level action #A.5 is MethodCall subroutine with ok = true
    CorrespondenceNormal
      8 // It corresponds to high-level action #B.8, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.6 is MethodCall subroutine with ok = false
    CorrespondenceNormal
      9 // It corresponds to high-level action #B.9, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.7 is MethodCall subroutine with stack overflow with ok = true
    CorrespondenceNormal
      10 // It corresponds to high-level action #B.10, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.8 is MethodCall subroutine with stack overflow with ok = false
    CorrespondenceNormal
      11 // It corresponds to high-level action #B.11, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.9 is a := 0 with ok = true
    CorrespondenceNormal
      12 // It corresponds to high-level action #B.12, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.10 is a := 0 with ok = false
    CorrespondenceNormal
      13 // It corresponds to high-level action #B.13, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.11 is Return with ok = true
    CorrespondenceNormal
      18 // It corresponds to high-level action #B.18, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.12 is Return with ok = false
    CorrespondenceNormal
      19 // It corresponds to high-level action #B.19, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.13 is UnconditionalJump from "main.3.R" to "main.End" with ok = true
    CorrespondenceNormal
      20 // It corresponds to high-level action #B.20, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.14 is UnconditionalJump from "main.3.R" to "main.End" with ok = false
    CorrespondenceNormal
      21 // It corresponds to high-level action #B.21, which matches
      [ MapperMatching ];                              // The only action is the same as at the low level
    // Low-level action #A.15 is PropagateWriteMessageStatement with ok = true
    CorrespondencePropagate
      25; // It corresponds to high-level action #B.25, which matches
    // Low-level action #A.16 is PropagateWriteMessageStatement with ok = false
    CorrespondencePropagate
      26 // It corresponds to high-level action #B.26, which matches
  ]

// The start PC for the low-level program is "main.1", which is A.PC #0
let lprog_main_start_pc_index: nat = 0

// The start PC for the high-level program is "main.1.1", which is B.PC #0
let hprog_main_start_pc_index: nat = 0

let make_pc_indices (start_pc_index: nat) (end_pc_index: nat) : statement_pc_indices_t =
  {
    start_pc_index = Some start_pc_index;
    end_pc_index = Some end_pc_index;
    create_thread_initial_pc_index = None;
    method_call_return_pc_index = None;
  }

let make_empty_pc_indices : statement_pc_indices_t =
  {
    start_pc_index = None;
    end_pc_index = None;
    create_thread_initial_pc_index = None;
    method_call_return_pc_index = None;
  }

// The lpc_indices_array contains, for each atomic action in the low-level program,
// a list of PC index summaries, one for each action in that atomic action.

let lpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array
  [
    // Low-level action #A.0 is a := 10 with ok = true. It goes from "main.1" (A.PC #0) to "main.2.1" (A.PC #1).
    [ make_pc_indices 0 1 ];
    // Low-level action #A.1 is a := 10 with ok = false. It goes from "main.1" (A.PC #0) to "main.2.1" (A.PC #1).
    [ make_pc_indices 0 1 ];
    // Low-level action #A.2 is c := 20; e := 30 with ok = true, true
    [ make_pc_indices 1 2; make_pc_indices 2 3 ];
    // Low-level action #A.3 is c := 20 with ok = false
    [ make_pc_indices 1 2 ];
    // Low-level action #A.4 is c := 20; e := 30 with ok = true, false
    [ make_pc_indices 1 2; make_pc_indices 2 3 ];
    // Low-level action #A.5 is MethodCall subroutine with ok = true. It goes from "main.3" to "subroutine.1".
    // But, since it does so with a method call, we need to set the method_call_return_pc_index field as well.
    [
      {
        start_pc_index = Some 3;
        end_pc_index = Some 6;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 4; // The return PC is "main.3.R" (A.PC #4)
      }
    ];
    // Low-level action #A.6 is MethodCall subroutine with ok = false. It goes from "main.3" to "subroutine.1".
    [
      {
        start_pc_index = Some 3;
        end_pc_index = Some 6;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 4; // The return PC is "main.3.R" (A.PC #4)
      }
    ];
    // Low-level action #A.7 is MethodCall subroutine with ok = true. It goes from "main.3" to "subroutine.1".
    // But, since it does so with a method call, we need to set the method_call_return_pc_index field as well.
    [
      {
        start_pc_index = Some 3;
        end_pc_index = Some 6;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 4; // The return PC is "main.3.R" (A.PC #4)
      }
    ];
    // Low-level action #A.8 is MethodCall subroutine with ok = false. It goes from "main.3" to "subroutine.1".
    [
      {
        start_pc_index = Some 3;
        end_pc_index = Some 6;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 4; // The return PC is "main.3.R" (A.PC #4)
      }
    ];
    // Low-level action #A.9 is a := 0 with ok = true
    [ make_pc_indices 6 7 ];
    // Low-level action #A.10 is a := 0 with ok = false
    [ make_pc_indices 6 7 ];
    // Low-level action #A.11 is Return with ok = true
    [ make_pc_indices 7 4 ];
    // Low-level action #A.12 is Return with ok = false
    [ make_pc_indices 7 4 ];
    // Low-level action #A.13 is UnconditionalJump from "main.3.R" to "main.End" with ok = true
    [ make_pc_indices 4 5 ];
    // Low-level action #A.14 is UnconditionalJump from "main.3.R" to "main.End" with ok = false
    [ make_pc_indices 4 5 ];
    // Low-level action #A.15 is PropagateWriteMessageStatement with ok = true
    [ make_empty_pc_indices ];
    // Low-level action #A.16 is PropagateWriteMessageStatement with ok = false
    [ make_empty_pc_indices ];
  ]

// The hpc_indices_array contains, for each atomic action in the high-level program,
// a list of PC index summaries, one for each action in that atomic action.

let hpc_indices_array: array_t (list statement_pc_indices_t) = list_to_array
  [
    // Atomic action #0
    [ make_pc_indices 0 1; make_pc_indices 1 2; make_pc_indices 2 3 ];
    // Atomic action #1
    [ make_pc_indices 0 1 ];
    // Atomic action #2
    [ make_pc_indices 0 1; make_pc_indices 1 2 ];
    // Atomic action #3
    [ make_pc_indices 0 1; make_pc_indices 1 2; make_pc_indices 2 3 ];
    // Atomic action #4
    [ make_pc_indices 3 4; make_pc_indices 4 5; make_pc_indices 5 6 ];
    // Atomic action #5
    [ make_pc_indices 3 4 ];
    // Atomic action #6
    [ make_pc_indices 3 4; make_pc_indices 4 5 ];
    // Atomic action #7
    [ make_pc_indices 3 4; make_pc_indices 4 5; make_pc_indices 5 6 ];
    // Atomic action #8
    [
      {
        start_pc_index = Some 6;
        end_pc_index = Some 11;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 7; // The return PC is "main.3.R" (B.PC #7)
      }
    ];
    // Atomic action #9
    [
      {
        start_pc_index = Some 6;
        end_pc_index = Some 11;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 7; // The return PC is "main.3.R" (B.PC #7)
      }
    ];
    // Atomic action #10
    [
      {
        start_pc_index = Some 6;
        end_pc_index = Some 11;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 7; // The return PC is "main.3.R" (B.PC #7)
      }
    ];
    // Atomic action #11
    [
      {
        start_pc_index = Some 6;
        end_pc_index = Some 11;
        create_thread_initial_pc_index = None;
        method_call_return_pc_index = Some 7; // The return PC is "main.3.R" (B.PC #7)
      }
    ];
    // Atomic action #12
    [ make_pc_indices 11 12 ];
    // Atomic action #13
    [ make_pc_indices 11 12 ];
    // Atomic action #14
    [ make_pc_indices 12 13 ];
    // Atomic action #15
    [ make_pc_indices 12 13 ];
    // Atomic action #16
    [ make_pc_indices 13 14 ];
    // Atomic action #17
    [ make_pc_indices 13 14 ];
    // Atomic action #18
    [ make_pc_indices 14 7 ];
    // Atomic action #19
    [ make_pc_indices 14 7 ];
    // Atomic action #20
    [ make_pc_indices 7 8 ];
    // Atomic action #21
    [ make_pc_indices 7 8 ];
    // Atomic action #22
    [ make_pc_indices 8 9; make_pc_indices 9 10 ];
    // Atomic action #23
    [ make_pc_indices 8 9 ];
    // Atomic action #24
    [ make_pc_indices 8 9; make_pc_indices 9 10 ];
    // Atomic action #25
    [ make_empty_pc_indices ];
    // Atomic action #26
    [ make_empty_pc_indices ];
  ]

let vw: efficient_var_intro_witness_t = {
  lprog = MyAProg.prog;
  hprog = MyBProg.prog;
  lprog_actions_array = list_to_array MyAtomicAProg.prog.actions;
  hprog_actions_array = list_to_array MyAtomicBProg.prog.actions;
  vs = vs;
  tds = tds;
  inv = MyAtomicBInvariant.inv;
  which_initializers_are_intros = which_initializers_are_intros;
  lpcs = lpcs;
  hpcs = hpcs;
  hpc_to_lpc = hpc_to_lpc;
  lpc_to_hpcs = lpc_to_hpcs;
  is_return_hpc = is_return_hpc;
  is_nonyielding_lpc = is_nonyielding_lpc;
  is_nonyielding_hpc = is_nonyielding_hpc;
  is_breaking_hpc = is_breaking_hpc;
  hpc_info = hpc_info;
  corresponding_hactions_info = corresponding_hactions_info;
  lprog_main_start_pc_index = lprog_main_start_pc_index;
  hprog_main_start_pc_index = hprog_main_start_pc_index;
  lpc_indices_array = lpc_indices_array;
  hpc_indices_array = hpc_indices_array;
}

let lemma_MyAtomicAProgRefinesMyAtomicBProg ()
  : Lemma (spec_refines_spec
           (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicAProg.prog)
           (semantics_to_spec (make_atomic_semantics armada_semantics) MyAtomicBProg.prog)
           refinement_requirement) =
  let latomic_prog = MyAtomicAProg.prog in
  let hatomic_prog = MyAtomicBProg.prog in
  assert (efficient_var_intro_witness_valid latomic_prog hatomic_prog vw)
    by (FStar.Tactics.V2.compute (); FStar.Tactics.V2.trivial ());
  MyAtomicBInvariant.inv_is_stepwise_invariant ();
  efficient_var_intro_witness_valid_implies_refinement latomic_prog hatomic_prog vw
