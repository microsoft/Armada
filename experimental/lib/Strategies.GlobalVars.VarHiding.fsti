module Strategies.GlobalVars.VarHiding

open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.GlobalVars
open Strategies.GlobalVars.VarIntro
open Strategies.PCRelation
open Util.List

val statement_that_updates_gvars_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (start_pc: pc_t)
  (end_pc: option pc_t)
  (statement: Armada.Statement.t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ statement_updates_gvars vs statement)
          (ensures  (match statement_computation actor nd start_pc end_pc statement s1 with
                     | ComputationProduces s1' ->
                           states_match_except_global_variables vs pc_relation s1' s2
                         /\ global_variables_unaddressed_in_memory vs s1'.mem
                         /\ roots_match s1'.mem
                     | _ -> True))

val propagate_write_message_statement_computation_s1_only_maintains_states_match
  (vs: list var_id_t)
  (pc_relation: pc_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (s1: Armada.State.t)
  (s2: Armada.State.t)
  : Lemma (requires   states_match_except_global_variables vs pc_relation s1 s2
                    /\ global_variables_unaddressed_in_memory vs s1.mem
                    /\ global_variables_unaddressed_in_memory vs s2.mem
                    /\ roots_match s1.mem
                    /\ roots_match s2.mem
                    /\ unstarted_threads_have_empty_write_buffers s1
                    /\ unstarted_threads_have_empty_write_buffers s2
                    /\ ThreadStatusRunning? (s1.threads actor).status
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ (let receiver_tid = ObjectValueAbstract?.value (Cons?.hd nd) in
                       let thread1 = s1.threads actor in
                       let write_buffer1 = thread1.write_buffer in
                       let position1 = (s1.threads receiver_tid).position_in_other_write_buffers actor in
                         length write_buffer1 > position1
                       /\ (let write_message1 = index write_buffer1 position1 in
                          not (global_variables_unaddressed_in_write_message vs write_message1))))
          (ensures  (match propagate_write_message_statement_computation actor nd s1 with
                     | ComputationProduces s1' ->
                           states_match_except_global_variables vs pc_relation s1' s2
                         /\ global_variables_unaddressed_in_memory vs s1.mem
                         /\ roots_match s1.mem
                         /\ unstarted_threads_have_empty_write_buffers s1'
                     | ComputationImpossible -> True
                     | ComputationUndefined -> True))
