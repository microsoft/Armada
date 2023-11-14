module MyHProg

open Armada.Action
open Armada.Base
open Armada.BinaryOp
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Type
open Spec.Behavior
open Spec.Ubool

/// level MyHProg
/// {
///   ghost var a: int := 0;
///   ghost var b: int := 1;
///   ghost var c: int := 2;
///   ghost var d: int := 3;
///   ghost var e: int;
///   ghost var f: int := 1;
///   ghost var g: int := 1;
///   ghost var h: int := 0;
///
///   method main ()
///   {
///     ghost var x: int := 0;
///
///     e := g;  // This is the only statement differing from level MyLProg
///     atomic {
///       a := c;
///       d := b;
///       e := e;
///     }
///     f := f / f;
///   }
/// }

let global_initializers: list initializer_t =
  [
    { var_id = "a"; iv = InitializerSpecific (ObjectValueAbstract int 0); weakly_consistent = false; } ;
    { var_id = "b"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } ;
    { var_id = "c"; iv = InitializerSpecific (ObjectValueAbstract int 2); weakly_consistent = false; } ;
    { var_id = "d"; iv = InitializerSpecific (ObjectValueAbstract int 3); weakly_consistent = false; } ;
    { var_id = "e"; iv = InitializerArbitrary (ObjectTDAbstract int); weakly_consistent = false; } ;
    { var_id = "f"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } ;
    { var_id = "g"; iv = InitializerSpecific (ObjectValueAbstract int 1); weakly_consistent = false; } ;
    { var_id = "h"; iv = InitializerSpecific (ObjectValueAbstract int 0); weakly_consistent = false; }
  ]

let program_statements = [
  { start_pc = Some "main.0"; end_pc = Some "main.1"; starts_atomic_block = true; ends_atomic_block = true;
    statement = UpdateStatement false
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "g"); };
  { start_pc = Some "main.1"; end_pc = Some "main.2"; starts_atomic_block = true; ends_atomic_block = false;
    statement = UpdateStatement false
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "a")
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "c"); };
  { start_pc = Some "main.2"; end_pc = Some "main.3";  starts_atomic_block = false; ends_atomic_block = false;
    statement = UpdateStatement false
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "d")
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "b"); };
  { start_pc = Some "main.3"; end_pc = Some "main.4"; starts_atomic_block = false; ends_atomic_block = true;
    statement = UpdateStatement false
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "e"); };
  { start_pc = Some "main.4"; end_pc = Some "main.5"; starts_atomic_block = true; ends_atomic_block = true;
    statement = UpdateStatement false
                  (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                  (ExpressionBinaryOperator
                    (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int) BinaryOpDivInt
                    (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                    (ExpressionGlobalVariable (ObjectTDAbstract int) "f")); };
]

let prog: Armada.Program.t = {
  main_method_id = "main";
  main_start_pc = "main.0";
  global_initializers = global_initializers;
  main_stack_initializers = [ { var_id = "x"; iv = InitializerSpecific (ObjectValueAbstract int 0); weakly_consistent = false } ];
  program_statements = program_statements;
}
