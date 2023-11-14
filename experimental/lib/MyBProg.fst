/// level B
/// {
///   ghost var a: int := 1;
///   ghost var b: int := 2;
///   ghost var c: int := 3;
///   ghost var d: int := 4;
///   ghost var e: int := 5;
/// 
///   method subroutine ()
///   {
///     a := 0;
///     b := a;
///     d := 2;
///   }
/// 
///   method main ()
///   {
///     atomic {
///       d := 5;
///       a := 10;
///       b := 15;
///     }
///     atomic {
///       c := 20;
///       b := 25;
///       e := 30;
///     }
///     subroutine();
///     atomic {
///       b := 35;
///       d := 40;
///     }
///   }
/// }

module MyBProg

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

let global_initializers: list initializer_t =
  [
    { var_id = "a"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } ;
    { var_id = "b"; iv = InitializerSpecific (ObjectValueAbstract int 2); weakly_consistent = false; } ;
    { var_id = "c"; iv = InitializerSpecific (ObjectValueAbstract int 3); weakly_consistent = false; } ;
    { var_id = "d"; iv = InitializerSpecific (ObjectValueAbstract int 4); weakly_consistent = false; } ;
    { var_id = "e"; iv = InitializerSpecific (ObjectValueAbstract int 5); weakly_consistent = false; }
  ]
let subroutine_stack_initializers: list initializer_t = 
  [

  ]
let subroutine_func_statements = 
  [
    (* a := 0; *)
    {
      start_pc = Some "subroutine.1";
      end_pc = Some "subroutine.2";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 0));
    };
    (* b := a; *)
    {
      start_pc = Some "subroutine.2";
      end_pc = Some "subroutine.3";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "b") (ExpressionGlobalVariable (ObjectTDAbstract int) "a");
    };
    (* d := 2; *)
    {
      start_pc = Some "subroutine.3";
      end_pc = Some "subroutine.End";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "d") (ExpressionConstant (ObjectValueAbstract int 2));
    };
    (* return from subroutine.End to main.3.R *)
    {
      start_pc = Some "subroutine.End";
      end_pc = Some "main.3.R";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = ReturnStatement "subroutine" false [] [];
    }
  ]
let main_stack_initializers: list initializer_t = 
  [

  ]
let main_func_statements = 
  [
    (* d := 5; *)
    {
      start_pc = Some "main.1.1";
      end_pc = Some "main.1.2";
      starts_atomic_block = true;
      ends_atomic_block = false;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "d") (ExpressionConstant (ObjectValueAbstract int 5));
    };
    (* a := 10; *)
    {
      start_pc = Some "main.1.2";
      end_pc = Some "main.1.3";
      starts_atomic_block = false;
      ends_atomic_block = false;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "a") (ExpressionConstant (ObjectValueAbstract int 10));
    };
    (* b := 15; *)
    {
      start_pc = Some "main.1.3";
      end_pc = Some "main.2.1";
      starts_atomic_block = false;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "b") (ExpressionConstant (ObjectValueAbstract int 15));
    };
    (* c := 20; *)
    {
      start_pc = Some "main.2.1";
      end_pc = Some "main.2.2";
      starts_atomic_block = true;
      ends_atomic_block = false;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "c") (ExpressionConstant (ObjectValueAbstract int 20));
    };
    (* b := 25; *)
    {
      start_pc = Some "main.2.2";
      end_pc = Some "main.2.3";
      starts_atomic_block = false;
      ends_atomic_block = false;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "b") (ExpressionConstant (ObjectValueAbstract int 25));
    };
    (* e := 30; *)
    {
      start_pc = Some "main.2.3";
      end_pc = Some "main.3";
      starts_atomic_block = false;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "e") (ExpressionConstant (ObjectValueAbstract int 30));
    };
    (* subroutine() *)
    {
      start_pc = Some "main.3";
      end_pc = Some "subroutine.1";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers false;
    };
    (* subroutine() stack overflow *)
    {
      start_pc = Some "main.3";
      end_pc = Some "subroutine.1";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = MethodCallStatement "subroutine" "main.3.R" [] [] subroutine_stack_initializers true;
    };
    (* return from method *)
    {
      start_pc = Some "main.3.R";
      end_pc = Some "main.4.1";
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = UnconditionalJumpStatement;
    };
    (* b := 35; *)
    {
      start_pc = Some "main.4.1";
      end_pc = Some "main.4.2";
      starts_atomic_block = true;
      ends_atomic_block = false;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "b") (ExpressionConstant (ObjectValueAbstract int 35));
    };
    (* d := 40; *)
    {
      start_pc = Some "main.4.2";
      end_pc = Some "main.End";
      starts_atomic_block = false;
      ends_atomic_block = true;
      statement = UpdateStatement false (ExpressionGlobalVariable (ObjectTDAbstract int) "d") (ExpressionConstant (ObjectValueAbstract int 40));
    }
  ]
let propagate_statements =
  [
    {
      start_pc = None;
      end_pc = None;
      starts_atomic_block = true;
      ends_atomic_block = true;
      statement = PropagateWriteMessageStatement;
    }
  ]
let program_statements = 
  [
    subroutine_func_statements;
    main_func_statements;
    propagate_statements
  ]
let prog: Armada.Program.t = {
  main_method_id = "main";
  main_start_pc = "main.1.1";
  global_initializers = global_initializers;
  main_stack_initializers = main_stack_initializers;
  program_statements = flatten program_statements;
}

