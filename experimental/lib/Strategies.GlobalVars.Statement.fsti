module Strategies.GlobalVars.Statement

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Type
open Spec.Ubool
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.GlobalVars
open Strategies.PCIndices
open Strategies.PCRelation
open Util.ImmutableArray
open Util.Relation

let statements_match_per_pc_relation
  (relation: relation_t pc_t pc_t)
  (return_relation: relation_t pc_t pc_t)
  (statement1: Armada.Statement.t)
  (statement2: Armada.Statement.t)
  : GTot ubool =
  match statement1 with
  | CreateThreadStatement method_id1 initial_pc1 bypassing_write_buffer1 optional_result1 parameter_var_ids1
                          parameter_expressions1 local_variable_initializers1 ->
      (match statement2 with
       | CreateThreadStatement method_id2 initial_pc2 bypassing_write_buffer2 optional_result2 parameter_var_ids2
                               parameter_expressions2 local_variable_initializers2 ->
              method_id1 = method_id2
           /\ relation initial_pc1 initial_pc2
           /\ bypassing_write_buffer1 = bypassing_write_buffer2
           /\ optional_result1 == optional_result2
           /\ parameter_var_ids1 = parameter_var_ids2
           /\ parameter_expressions1 == parameter_expressions2
           /\ local_variable_initializers1 == local_variable_initializers2
       | _ -> False)
  | MethodCallStatement method_id1 return_pc1 parameter_var_ids1 parameter_expressions1 local_variable_initializers1
                          stack_overflow1 ->
      (match statement2 with
       | MethodCallStatement method_id2 return_pc2 parameter_var_ids2 parameter_expressions2
                             local_variable_initializers2 stack_overflow2 ->
              method_id1 = method_id2
           /\ relation return_pc1 return_pc2
           /\ return_relation return_pc1 return_pc2
           /\ parameter_var_ids1 = parameter_var_ids2
           /\ parameter_expressions1 == parameter_expressions2
           /\ local_variable_initializers1 == local_variable_initializers2
           /\ stack_overflow1 = stack_overflow2
       | _ -> False)
  | _ -> statement2 == statement1

let efficient_statements_match_per_pc_relation
  (relation: relation_t nat nat)
  (return_relation: relation_t nat nat)
  (statement1: Armada.Statement.t)
  (statement2: Armada.Statement.t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : GTot ubool =
  match statement1 with
  | CreateThreadStatement method_id1 initial_pc1 bypassing_write_buffer1 optional_result1 parameter_var_ids1
                          parameter_expressions1 local_variable_initializers1 ->
      (match statement2 with
       | CreateThreadStatement method_id2 initial_pc2 bypassing_write_buffer2 optional_result2 parameter_var_ids2
                               parameter_expressions2 local_variable_initializers2 ->
              method_id1 = method_id2
           /\ bypassing_write_buffer1 = bypassing_write_buffer2
           /\ optional_result1 == optional_result2
           /\ parameter_var_ids1 = parameter_var_ids2
           /\ parameter_expressions1 == parameter_expressions2
           /\ local_variable_initializers1 == local_variable_initializers2
           /\ (match pc_indices1.create_thread_initial_pc_index, pc_indices2.create_thread_initial_pc_index with
              | Some idx1, Some idx2 -> relation idx1 idx2
              | _, _ -> False)
       | _ -> False)
  | MethodCallStatement method_id1 return_pc1 parameter_var_ids1 parameter_expressions1 local_variable_initializers1
                          stack_overflow1 ->
      (match statement2 with
       | MethodCallStatement method_id2 return_pc2 parameter_var_ids2 parameter_expressions2
                             local_variable_initializers2 stack_overflow2 ->
              method_id1 = method_id2
           /\ parameter_var_ids1 = parameter_var_ids2
           /\ parameter_expressions1 == parameter_expressions2
           /\ local_variable_initializers1 == local_variable_initializers2
           /\ stack_overflow1 = stack_overflow2
           /\ (match pc_indices1.method_call_return_pc_index, pc_indices2.method_call_return_pc_index with
              | Some idx1, Some idx2 -> relation idx1 idx2 /\ return_relation idx1 idx2
              | _, _ -> False)
       | _ -> False)
  | _ -> statement2 == statement1

let efficient_statements_match_per_pc_relation_implies_statements_match_per_pc_relation
  (pcs1: array_t pc_t)
  (pcs2: array_t pc_t)
  (idx_relation: relation_t nat nat)
  (idx_return_relation: relation_t nat nat)
  (pc_relation: relation_t pc_t pc_t)
  (pc_return_relation: relation_t pc_t pc_t)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : Lemma (requires   program_statement_corresponds_to_statement_pc_indices pcs1 ps1 pc_indices1
                    /\ program_statement_corresponds_to_statement_pc_indices pcs2 ps2 pc_indices2
                    /\ efficient_statements_match_per_pc_relation idx_relation idx_return_relation
                        ps1.statement ps2.statement pc_indices1 pc_indices2
                    /\ (forall (idx1: nat) (idx2: nat). idx1 < array_len pcs1 /\ idx2 < array_len pcs2 ==>
                         (let pc1 = array_index pcs1 idx1 in
                          let pc2 = array_index pcs2 idx2 in
                            (idx_relation idx1 idx2 ==> pc_relation pc1 pc2)
                          /\ (idx_return_relation idx1 idx2 ==> pc_return_relation pc1 pc2))))
          (ensures statements_match_per_pc_relation pc_relation pc_return_relation ps1.statement ps2.statement) =
  ()

let program_statement_end_pcs_match_per_pc_relation
  (relation: relation_t pc_t pc_t)
  (return_relation: relation_t pc_t pc_t)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  : GTot ubool =
  match ps1.end_pc, ps2.end_pc with
  | Some pc1, Some pc2 -> relation pc1 pc2 /\ (ReturnStatement? ps1.statement ==> return_relation pc1 pc2)
  | None, None -> True
  | _, _ -> False

let efficient_program_statement_end_pcs_match_per_pc_relation
  (relation: relation_t nat nat)
  (return_relation: relation_t nat nat)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : GTot ubool =
  match pc_indices1.end_pc_index, pc_indices2.end_pc_index with
  | Some pc1, Some pc2 -> relation pc1 pc2 /\ (ReturnStatement? ps1.statement ==> return_relation pc1 pc2)
  | None, None -> True
  | _, _ -> False

let efficient_statement_end_pcs_match_per_pc_relation_implies_program_statement_end_pcs_match_per_pc_relation
  (pcs1: array_t pc_t)
  (pcs2: array_t pc_t)
  (idx_relation: relation_t nat nat)
  (idx_return_relation: relation_t nat nat)
  (pc_relation: relation_t pc_t pc_t)
  (pc_return_relation: relation_t pc_t pc_t)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : Lemma (requires   program_statement_corresponds_to_statement_pc_indices pcs1 ps1 pc_indices1
                    /\ program_statement_corresponds_to_statement_pc_indices pcs2 ps2 pc_indices2
                    /\ efficient_program_statement_end_pcs_match_per_pc_relation idx_relation idx_return_relation
                        ps1 ps2 pc_indices1 pc_indices2
                    /\ (forall (idx1: nat) (idx2: nat). idx1 < array_len pcs1 /\ idx2 < array_len pcs2 ==>
                         (let pc1 = array_index pcs1 idx1 in
                          let pc2 = array_index pcs2 idx2 in
                            (idx_relation idx1 idx2 ==> pc_relation pc1 pc2)
                          /\ (idx_return_relation idx1 idx2 ==> pc_return_relation pc1 pc2))))
          (ensures program_statement_end_pcs_match_per_pc_relation pc_relation pc_return_relation ps1 ps2) =
  ()

let program_statements_match_per_pc_relation
  (relation: relation_t pc_t pc_t)
  (return_relation: relation_t pc_t pc_t)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  : GTot ubool =
     statements_match_per_pc_relation relation return_relation ps1.statement ps2.statement
   /\ program_statement_end_pcs_match_per_pc_relation relation return_relation ps1 ps2

let efficient_program_statements_match_per_pc_relation
  (relation: relation_t nat nat)
  (return_relation: relation_t nat nat)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : GTot ubool =
     efficient_statements_match_per_pc_relation relation return_relation ps1.statement ps2.statement pc_indices1
       pc_indices2
   /\ efficient_program_statement_end_pcs_match_per_pc_relation relation return_relation ps1 ps2 pc_indices1 pc_indices2

let efficient_program_statements_match_per_pc_relation_implies_program_statements_match_per_pc_relation
  (pcs1: array_t pc_t)
  (pcs2: array_t pc_t)
  (idx_relation: relation_t nat nat)
  (idx_return_relation: relation_t nat nat)
  (pc_relation: relation_t pc_t pc_t)
  (pc_return_relation: relation_t pc_t pc_t)
  (ps1: program_statement_t)
  (ps2: program_statement_t)
  (pc_indices1: statement_pc_indices_t)
  (pc_indices2: statement_pc_indices_t)
  : Lemma (requires   program_statement_corresponds_to_statement_pc_indices pcs1 ps1 pc_indices1
                    /\ program_statement_corresponds_to_statement_pc_indices pcs2 ps2 pc_indices2
                    /\ efficient_program_statements_match_per_pc_relation idx_relation idx_return_relation
                        ps1 ps2 pc_indices1 pc_indices2
                    /\ (forall (idx1: nat) (idx2: nat). idx1 < array_len pcs1 /\ idx2 < array_len pcs2 ==>
                         (let pc1 = array_index pcs1 idx1 in
                          let pc2 = array_index pcs2 idx2 in
                            (idx_relation idx1 idx2 ==> pc_relation pc1 pc2)
                          /\ (idx_return_relation idx1 idx2 ==> pc_return_relation pc1 pc2))))
          (ensures program_statements_match_per_pc_relation pc_relation pc_return_relation ps1 ps2) =
  efficient_statement_end_pcs_match_per_pc_relation_implies_program_statement_end_pcs_match_per_pc_relation
    pcs1 pcs2 idx_relation idx_return_relation pc_relation pc_return_relation ps1 ps2 pc_indices1 pc_indices2;
  efficient_statements_match_per_pc_relation_implies_statements_match_per_pc_relation pcs1 pcs2 idx_relation
    idx_return_relation pc_relation pc_return_relation ps1 ps2 pc_indices1 pc_indices2

let statement_effect_independent_of_global_variables
  (vs: list var_id_t)
  (statement: Armada.Statement.t)
  : GTot bool =
  match statement with
  | AssumeExpressionStatement exp ->
      global_variables_unmentioned_in_expression vs exp
  | AssumePredicateStatement pred ->
      false
  | AssertTrueStatement exp ->
      global_variables_unmentioned_in_expression vs exp
  | AssertFalseStatement exp ->
      global_variables_unmentioned_in_expression vs exp
  | ConditionalJumpStatement cond ->
      global_variables_unmentioned_in_expression vs cond
  | UnconditionalJumpStatement ->
      true
  | UpdateStatement _ dst src ->
         global_variables_unmentioned_in_expression vs dst
      && global_variables_unmentioned_in_expression vs src
  | NondeterministicUpdateStatement _ dst ->
      global_variables_unmentioned_in_expression vs dst
  | PropagateWriteMessageStatement ->
      false
  | CompareAndSwapStatement target old_val new_val bypassing_write_buffer optional_result ->
         global_variables_unmentioned_in_expression vs target
      && global_variables_unmentioned_in_expression vs old_val
      && global_variables_unmentioned_in_expression vs new_val
      && global_variables_unmentioned_in_optional_expression vs optional_result
  | AtomicExchangeStatement old_val target new_val ->
         global_variables_unmentioned_in_expression vs old_val
      && global_variables_unmentioned_in_expression vs target
      && global_variables_unmentioned_in_expression vs new_val
  | CreateThreadStatement _ _ _ option_result _ parameter_expressions local_variable_initializers ->
         global_variables_unmentioned_in_optional_expression vs option_result
      && global_variables_unmentioned_in_expressions vs parameter_expressions
      && global_variables_unaddressed_in_initializers vs local_variable_initializers
  | MethodCallStatement _ _ parameter_var_ids parameter_expressions local_variable_initializers stack_overflow ->
         global_variables_unmentioned_in_expressions vs parameter_expressions
      && global_variables_unaddressed_in_initializers vs local_variable_initializers
  | ReturnStatement _ _ output_dsts output_srcs ->
         global_variables_unmentioned_in_expressions vs output_dsts
      && global_variables_unmentioned_in_expressions vs output_srcs
  | TerminateThreadStatement _ ->
      true
  | TerminateProcessStatement _ ->
      true
  | JoinStatement join_tid ->
      global_variables_unmentioned_in_expression vs join_tid
  | MallocSuccessfulStatement _ result _ count ->
         global_variables_unmentioned_in_expression vs result
      && global_variables_unmentioned_in_expression vs count
  | MallocReturningNullStatement _ result count ->
         global_variables_unmentioned_in_expression vs result
      && global_variables_unmentioned_in_expression vs count
  | CallocSuccessfulStatement _ result _ count ->
         global_variables_unmentioned_in_expression vs result
      && global_variables_unmentioned_in_expression vs count
  | CallocReturningNullStatement _ result count ->
         global_variables_unmentioned_in_expression vs result
      && global_variables_unmentioned_in_expression vs count
  | DeallocStatement ptr ->
      global_variables_unmentioned_in_expression vs ptr

  // For SomehowStatement, we have no idea what's put into the
  // destinations specified in modifies clauses.  So all we can do is
  // make sure that none of those destinations has any pointer fields.
  
  | SomehowStatement undefined_unless_cond _ modifies_clauses ensures_cond ->
         global_variables_unmentioned_in_expression vs undefined_unless_cond
      && global_variables_unmentioned_in_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
      && global_variables_unmentioned_in_expression vs ensures_cond

  | FenceStatement ->
      true

  // For ExternalMethodStartStatement and
  // ExternalMethodMiddleStatement, we have no idea what's put into
  // the destinations specified in modifies clauses.  So all we can do
  // is make sure that none of those destinations has any pointer
  // fields.

  | ExternalMethodStartStatement await_cond undefined_unless_cond _ modifies_clauses reads_clauses ->
         global_variables_unmentioned_in_expression vs await_cond
      && global_variables_unmentioned_in_expression vs undefined_unless_cond
      && global_variables_unmentioned_in_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
      && global_variables_unmentioned_in_reads_clauses vs reads_clauses
  | ExternalMethodMiddleStatement _ modifies_clauses reads_clauses ->
         global_variables_unmentioned_in_expressions vs modifies_clauses
      && expressions_lack_pointer_field modifies_clauses
      && global_variables_unmentioned_in_reads_clauses vs reads_clauses

  | ExternalMethodEndStatement ensures_cond logs_clauses ->
         global_variables_unmentioned_in_expression vs ensures_cond
      && global_variables_unmentioned_in_expressions vs logs_clauses

val statement_effect_independent_implications
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc1: pc_t)
  (start_pc2: pc_t)
  (end_pc1: option pc_t)
  (end_pc2: option pc_t)
  (statement1: Armada.Statement.t)
  (statement2: Armada.Statement.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ unstarted_threads_have_empty_write_buffers s1
                    /\ unstarted_threads_have_empty_write_buffers s2
                    /\ statement_effect_independent_of_global_variables vs statement1
                    /\ statements_match_per_pc_relation pc_relation.relation pc_relation.return_relation
                        statement1 statement2
                    /\ pc_relation.relation start_pc1 start_pc2
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ (match end_pc1, end_pc2 with
                       | Some pc1, Some pc2 ->
                              pc_relation.relation pc1 pc2
                           /\ (ReturnStatement? statement1 ==> pc_relation.return_relation pc1 pc2)
                       | None, None -> True
                       | _, _ -> False))
          (ensures  (match statement_computation actor nd start_pc1 end_pc1 statement1 s1,
                           statement_computation actor nd start_pc2 end_pc2 statement2 s2 with
                     | ComputationProduces s1', ComputationProduces s2' ->
                           states_match_except_global_variables vs pc_relation s1' s2'
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ global_variables_unaddressed_in_memory vs s2'.mem
                         /\ roots_match s1'.mem
                         /\ roots_match s2'.mem
                     | ComputationImpossible, ComputationImpossible -> True
                     | ComputationUndefined, ComputationUndefined -> True
                     | _ -> False))
