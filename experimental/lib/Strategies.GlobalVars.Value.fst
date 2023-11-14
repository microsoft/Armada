module Strategies.GlobalVars.Value

open Armada.Base
open Armada.BinaryOp
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open Armada.UnaryOp
open FStar.Sequence.Ambient
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.GlobalVars
open Strategies.GlobalVars.Unaddressed
open Strategies.PCRelation
open Util.List
open Util.Nth
open Util.Seq
open Util.Trigger

#push-options "--z3rlimit 30"

let rec dereference_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_pointer vs p
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  dereference_computation p mem1 == dereference_computation p mem2
                    /\ (match dereference_computation p mem1 with
                       | ComputationProduces storage -> global_variables_unaddressed_in_storage vs storage
                       | _ -> True)) =
  match p with
  | PointerUninitialized -> ()
  | PointerNull -> ()
  | PointerRoot root_id -> ()
  | PointerField struct_ptr field_id ->
      dereference_computation_doesnt_depend_on_global_variables vs struct_ptr mem1 mem2
  | PointerIndex array_ptr idx ->
      dereference_computation_doesnt_depend_on_global_variables vs array_ptr mem1 mem2

let dereference_as_td_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (p: Armada.Pointer.t)
  (td: object_td_t)
  (actor: tid_t)
  (mem1: Armada.Memory.t)
  (mem2: Armada.Memory.t)
  : Lemma (requires   memories_match_except_global_variables vs mem1 mem2
                    /\ global_variables_unaddressed_in_pointer vs p
                    /\ global_variables_unaddressed_in_memory vs mem1
                    /\ global_variables_unaddressed_in_memory vs mem2
                    /\ roots_match mem1
                    /\ roots_match mem2)
          (ensures  dereference_as_td_computation p td actor mem1 == dereference_as_td_computation p td actor mem2
                    /\ (match dereference_as_td_computation p td actor mem1 with
                       | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                       | _ -> True)) =
  dereference_computation_doesnt_depend_on_global_variables vs p mem1 mem2;
  match dereference_computation p mem1 with
  | ComputationProduces storage ->
      global_variables_unaddressed_in_storage_implies_unaddressed_in_object_value vs actor storage
  | _ -> ()

#pop-options
#push-options "--z3rlimit 80"

let rec rvalue_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expression vs exp
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures  rvalue_computation exp actor s1 == rvalue_computation exp actor s2
                    /\ (match rvalue_computation exp actor s1 with
                       | ComputationProduces value -> global_variables_unaddressed_in_object_value vs value
                       | _ -> True))
          (decreases exp) =
  if not (expression_valid exp) then
    ()
  else
    match exp with
    | ExpressionConstant value -> ()
    | ExpressionGlobalVariable td var_id ->
        dereference_as_td_computation_doesnt_depend_on_global_variables vs (PointerRoot (RootIdGlobal var_id)) td actor
          s1.mem s2.mem
    | ExpressionLocalVariable td var_id ->
        let thread = s1.threads actor in
        if list_contains var_id thread.top.local_variables then
          dereference_as_td_computation_doesnt_depend_on_global_variables vs
            (PointerRoot (RootIdStack actor thread.top.method_id thread.top.frame_uniq var_id)) td actor s1.mem s2.mem
        else
          ()
    | ExpressionUnaryOperator _ _ operator operand ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand actor s1 s2
    | ExpressionBinaryOperator _ _ _ operator operand1 operand2 ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand1 actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand2 actor s1 s2
    | ExpressionIf _ cond operand_then operand_else ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation cond actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand_then actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation operand_else actor s1 s2
    | ExpressionDereference td ptr ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2;
        (match rvalue_computation ptr actor s1 with
         | ComputationUndefined | ComputationImpossible -> ()
         | ComputationProduces ptr_value ->
             let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
             dereference_as_td_computation_doesnt_depend_on_global_variables vs p td actor s1.mem s2.mem)
    | ExpressionAddressOf obj ->
        lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2
    | ExpressionPointerOffset ptr offset ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation offset actor s1 s2;
        (match rvalue_computation ptr actor s1 with
         | ComputationUndefined | ComputationImpossible -> ()
         | ComputationProduces ptr_value ->
             (match rvalue_computation offset actor s1 with
              | ComputationUndefined | ComputationImpossible -> ()
              | ComputationProduces offset_value ->
                  let p = PrimitiveBoxPointer?.ptr (ObjectValuePrimitive?.value ptr_value) in
                  (match p with
                   | PointerIndex array_ptr idx ->
                       let offset_int = ObjectValueAbstract?.value offset_value in
                       dereference_computation_doesnt_depend_on_global_variables vs array_ptr s1.mem s2.mem
                   | _ -> ())))
    | ExpressionFieldOf td obj field_id ->
        lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2;
        (match lvalue_computation obj actor s1 with
         | ComputationProduces obj_ptr ->
             dereference_as_td_computation_doesnt_depend_on_global_variables vs (PointerField obj_ptr field_id)
               td actor s1.mem s2.mem
         | _ -> ())
    | ExpressionAllocated ptr ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2
    | ExpressionApplyFunction td operands return_type operand_types fn ->
        rvalues_computation_doesnt_depend_on_global_variables vs pc_relation operands actor s1 s2
    | ExpressionIfUndefined td potentially_unsafe safe_substitution ->
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation potentially_unsafe actor s1 s2;
        rvalue_computation_doesnt_depend_on_global_variables vs pc_relation safe_substitution actor s1 s2
    | ExpressionInitialTid -> ()
    | ExpressionUniqsUsed -> ()
    | ExpressionStopReason -> ()

and lvalue_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exp: expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expression vs exp
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures    lvalue_computation exp actor s1 == lvalue_computation exp actor s2
                    /\ (match lvalue_computation exp actor s1 with
                       | ComputationProduces p -> global_variables_unaddressed_in_pointer vs p
                       | _ -> True))
          (decreases exp) =
  match exp with
  | ExpressionGlobalVariable _ var_id -> ()
  | ExpressionLocalVariable _ var_id -> ()
  | ExpressionDereference _ ptr ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation ptr actor s1 s2
  | ExpressionFieldOf td obj field_id ->
      lvalue_computation_doesnt_depend_on_global_variables vs pc_relation obj actor s1 s2
  | _ -> ()
  
and rvalues_computation_doesnt_depend_on_global_variables
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (exps: list expression_t)
  (actor: tid_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   global_variables_unmentioned_in_expressions vs exps
                    /\ states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ ThreadStatusRunning? (s1.threads actor).status)
          (ensures  rvalues_computation exps actor s1 == rvalues_computation exps actor s2
                    /\ (match rvalues_computation exps actor s1 with
                       | ComputationProduces values -> global_variables_unaddressed_in_object_values vs values
                       | _ -> True))
          (decreases exps) =
  match exps with
  | [] -> ()
  | exp :: exps' ->
      rvalue_computation_doesnt_depend_on_global_variables vs pc_relation exp actor s1 s2;
      rvalues_computation_doesnt_depend_on_global_variables vs pc_relation exps' actor s1 s2

#pop-options
