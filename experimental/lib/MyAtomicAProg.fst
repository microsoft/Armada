module MyAtomicAProg

open Armada.Action
open Armada.Base
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Type
open Armada.Pointer
open Armada.Computation
open FStar.List.Tot
open FStar.Char
open FStar.Mul
open FStar.Sequence.Base
open Spec.Behavior
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.AtomicToRegular.Armada
open Strategies.RegularToAtomic.Armada
open Strategies.PCIndices
open Util.ImmutableArray
open Util.Nth
open MyAProg

let atomic_actions: list (list Armada.Action.t) =
  [
    // Atomic action #0
    [
      {
        ok = true;
        program_statement = 
          (* a := 10; *)
          {
            start_pc = Some "main.1";
            end_pc = Some "main.2.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 10));
          }
      }
    ];
    // Atomic action #1
    [
      {
        ok = false;
        program_statement = 
          (* a := 10; *)
          {
            start_pc = Some "main.1";
            end_pc = Some "main.2.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 10));
          }
      }
    ];
    // Atomic action #2
    [
      {
        ok = true;
        program_statement = 
          (* c := 20; *)
          {
            start_pc = Some "main.2.1";
            end_pc = Some "main.2.2";
            starts_atomic_block = true;
            ends_atomic_block = false;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "c") (ExpressionConstant (ObjectValueAbstract int 20));
          }
      };
      {
        ok = true;
        program_statement = 
          (* e := 30; *)
          {
            start_pc = Some "main.2.2";
            end_pc = Some "main.3";
            starts_atomic_block = false;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e") (ExpressionConstant (ObjectValueAbstract int 30));
          }
      }
    ];
    // Atomic action #3
    [
      {
        ok = false;
        program_statement = 
          (* c := 20; *)
          {
            start_pc = Some "main.2.1";
            end_pc = Some "main.2.2";
            starts_atomic_block = true;
            ends_atomic_block = false;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "c") (ExpressionConstant (ObjectValueAbstract int 20));
          }
      }
    ];
    // Atomic action #4
    [
      {
        ok = true;
        program_statement = 
          (* c := 20; *)
          {
            start_pc = Some "main.2.1";
            end_pc = Some "main.2.2";
            starts_atomic_block = true;
            ends_atomic_block = false;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "c") (ExpressionConstant (ObjectValueAbstract int 20));
          }
      };
      {
        ok = false;
        program_statement = 
          (* e := 30; *)
          {
            start_pc = Some "main.2.2";
            end_pc = Some "main.3";
            starts_atomic_block = false;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e") (ExpressionConstant (ObjectValueAbstract int 30));
          }
      }
    ];
    // Atomic action #5
    [
      {
        ok = true;
        program_statement = 
          (* subroutine() *)
          {
            start_pc = Some "main.3";
            end_pc = Some "subroutine.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers false;
          }
      }
    ];
    // Atomic action #6
    [
      {
        ok = false;
        program_statement = 
          (* subroutine() *)
          {
            start_pc = Some "main.3";
            end_pc = Some "subroutine.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers false;
          }
      }
    ];
    // Atomic action #7
    [
      {
        ok = true;
        program_statement = 
          (* subroutine() stack overflow *)
          {
            start_pc = Some "main.3";
            end_pc = Some "subroutine.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers true;
          }
      }
    ];
    // Atomic action #8
    [
      {
        ok = false;
        program_statement = 
          (* subroutine() stack overflow *)
          {
            start_pc = Some "main.3";
            end_pc = Some "subroutine.1";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers true;
          }
      }
    ];
    // Atomic action #9
    [
      {
        ok = true;
        program_statement = 
          (* a := 0; *)
          {
            start_pc = Some "subroutine.1";
            end_pc = Some "subroutine.End";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 0));
          }
      }
    ];
    // Atomic action #10
    [
      {
        ok = false;
        program_statement = 
          (* a := 0; *)
          {
            start_pc = Some "subroutine.1";
            end_pc = Some "subroutine.End";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 0));
          }
      }
    ];
    // Atomic action #11
    [
      {
        ok = true;
        program_statement = 
          (* return from subroutine.End to main.3.R *)
          {
            start_pc = Some "subroutine.End";
            end_pc = Some "main.3.R";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = ReturnStatement "subroutine" false [] [];
          }
      }
    ];
    // Atomic action #12
    [
      {
        ok = false;
        program_statement = 
          (* return from subroutine.End to main.3.R *)
          {
            start_pc = Some "subroutine.End";
            end_pc = Some "main.3.R";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = ReturnStatement "subroutine" false [] [];
          }
      }
    ];
    // Atomic action #13
    [
      {
        ok = true;
        program_statement = 
          (* return from method *)
          {
            start_pc = Some "main.3.R";
            end_pc = Some "main.End";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UnconditionalJumpStatement;
          }
      }
    ];
    // Atomic action #14
    [
      {
        ok = false;
        program_statement = 
          (* return from method *)
          {
            start_pc = Some "main.3.R";
            end_pc = Some "main.End";
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = UnconditionalJumpStatement;
          }
      }
    ];
    // Atomic action #15
    [
      {
        ok = true;
        program_statement =
          (* propagate *)
          {
            start_pc = None;
            end_pc = None;
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = PropagateWriteMessageStatement;
          }
      }
    ];
    // Atomic action #16
    [
      {
        ok = false;
        program_statement =
          (* propagate *)
          {
            start_pc = None;
            end_pc = None;
            starts_atomic_block = true;
            ends_atomic_block = true;
            statement = PropagateWriteMessageStatement;
          }
      }
    ];
  ]

let prog: (program_t (make_atomic_semantics armada_semantics)) =
  {
    init_f = init_program MyAProg.prog;
    actions = atomic_actions;
  }

