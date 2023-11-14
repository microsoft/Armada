module MyAtomicHProg

open Armada.Action
open Armada.BinaryOp
open Armada.Expression
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Type
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.Atomic
open Strategies.Semantics
open Strategies.Semantics.Armada

let atomic_actions: list (list Armada.Action.t) =
  [
    // Statement at PC 0 succeeds
    [
      {
        ok = true;
        program_statement = { start_pc = Some "main.0";
                              end_pc = Some "main.1";
                              starts_atomic_block = true;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "g"); }
      }
    ];

    // Statement at PC 0 exhibits undefined behavior
    [
      {
        ok = false;
        program_statement = { start_pc = Some "main.0";
                              end_pc = Some "main.1";
                              starts_atomic_block = true;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "g"); }
      }
    ];

    // Statements at PCs 1-3 run successfully
    [
      {
        ok = true;
        program_statement = { start_pc = Some "main.1";
                              end_pc = Some "main.2";
                              starts_atomic_block = true;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "a")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "c"); };
      };
      {
        ok = true;
        program_statement = { start_pc = Some "main.2";
                              end_pc = Some "main.3";
                              starts_atomic_block = false;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "d")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "b"); }
      };
      {
        ok = true;
        program_statement = { start_pc = Some "main.3";
                              end_pc = Some "main.4";
                              starts_atomic_block = false;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e"); }
      }
    ];

    // Statement at PC 1 exhibits undefined behavior
    [
      {
        ok = false;
        program_statement = { start_pc = Some "main.1";
                              end_pc = Some "main.2";
                              starts_atomic_block = true;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "a")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "c"); }
      }
    ];

    // Statement at PC 1 runs normally then statement at PC 2 exhibits undefined behavior
    [
      {
        ok = true;
        program_statement = { start_pc = Some "main.1";
                              end_pc = Some "main.2";
                              starts_atomic_block = true;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "a")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "c"); }
      };
      {
        ok = false;
        program_statement = { start_pc = Some "main.2";
                              end_pc = Some "main.3";
                              starts_atomic_block = false;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "d")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "b"); }
      }
    ];

    // Statements at PCs 1-2 run successfully then statement at PC 3 exhibits undefined behavior
    [
      {
        ok = true;
        program_statement = { start_pc = Some "main.1";
                              end_pc = Some "main.2";
                              starts_atomic_block = true;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "a")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "c"); }
      };
      {
        ok = true;
        program_statement = { start_pc = Some "main.2";
                              end_pc = Some "main.3";
                              starts_atomic_block = false;
                              ends_atomic_block = false;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "d")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "b"); }
      };
      {
        ok = false;
        program_statement = { start_pc = Some "main.3";
                              end_pc = Some "main.4";
                              starts_atomic_block = false;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e")
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "e"); }
      }
    ];

    // Statement at PC 4 runs normally
    [
      {
        ok = true;
        program_statement = { start_pc = Some "main.4";
                              end_pc = Some "main.5";
                              starts_atomic_block = true;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                                (ExpressionBinaryOperator (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
                                  BinaryOpDivInt
                                  (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                                  (ExpressionGlobalVariable (ObjectTDAbstract int) "f")); }
      }
    ];

    // Statement at PC 4 exhibits undefined behavior
    [
      {
        ok = false;
        program_statement = { start_pc = Some "main.4";
                              end_pc = Some "main.5";
                              starts_atomic_block = true;
                              ends_atomic_block = true;
                              statement = UpdateStatement false
                                (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                                (ExpressionBinaryOperator (ObjectTDAbstract int) (ObjectTDAbstract int) (ObjectTDAbstract int)
                                  BinaryOpDivInt
                                  (ExpressionGlobalVariable (ObjectTDAbstract int) "f")
                                  (ExpressionGlobalVariable (ObjectTDAbstract int) "f")); }
      }
    ]
  ]

let atomic_semantics : semantics_t =
  make_atomic_semantics armada_semantics

let prog: (program_t atomic_semantics) =
  {
    init_f = init_program MyHProg.prog;
    actions = atomic_actions;
  }
