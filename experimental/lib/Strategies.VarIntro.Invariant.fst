module Strategies.VarIntro.Invariant

open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Ubool
open Strategies.ArmadaStatement.Breaking
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.GlobalVars
open Strategies.GlobalVars.Types
open Strategies.Invariant
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Helpers
open Strategies.VarIntro.Initialization

let var_intro_invariant
  (ls: Armada.State.t)
  : GTot ubool =
  True

let var_intro_lh_relation_between_steps
  (vr: var_intro_relation_t)
  (u: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  : GTot ubool =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
    states_match_except_global_variables vr.vs pc_relation ls hs
  /\ all_running_threads_have_pcs_in_list vr.hpcs hs
  /\ global_variables_unaddressed_in_memory vr.vs ls.mem
  /\ global_variables_unaddressed_in_memory vr.vs hs.mem
  /\ roots_match ls.mem
  /\ roots_match hs.mem
  /\ all_gvars_have_types hs.mem vr.vs vr.tds
  /\ unstarted_threads_have_empty_write_buffers ls
  /\ unstarted_threads_have_empty_write_buffers hs
  /\ (NotStopped? hs.stop_reason ==> vr.inv hs)

let var_intro_lh_relation
  (vr: var_intro_relation_t)
  (u: unit)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  : GTot ubool =
    var_intro_lh_relation_between_steps vr u ls hs
  /\ all_threads_breaking vr.is_breaking_hpc hs
  
let var_intro_pc_progress_measure
  (vr: var_intro_relation_t)
  (hs: Armada.State.t)
  (actor: tid_t)
  : GTot nat =
  let hthread = hs.threads actor in
  match (vr.hpc_info hthread.pc) with
  | HPCInfoNormal -> 0
  | HPCInfoIntroduced _ _ _ progress -> progress + 1

let var_intro_unread_write_buffer_len_measure
  (vr: var_intro_relation_t)
  (hs: Armada.State.t)
  (latomic_step: list Armada.Step.t)
  (actor: tid_t)
  : GTot nat =
  let hthread = hs.threads actor in
  match latomic_step with
  | [lstep] ->
      (match lstep.action.program_statement.statement with
       | PropagateWriteMessageStatement ->
           let nd = lstep.nd in
           if   list_len nd <> 1
              || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
             0
           else
             let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
             let position_in_write_buffer = (hs.threads receiver_tid).position_in_other_write_buffers actor in
             let write_buffer_len = length hthread.write_buffer in
             if position_in_write_buffer <= write_buffer_len then
               write_buffer_len - position_in_write_buffer
             else
               0
       | _ -> 0)
  | _ -> 0

let var_intro_progress_measure
  (vr: var_intro_relation_t)
  (hs: Armada.State.t)
  (latomic_step: list Armada.Step.t)
  (actor: tid_t)
  : GTot (nat * nat) =
  (var_intro_pc_progress_measure vr hs actor, var_intro_unread_write_buffer_len_measure vr hs latomic_step actor)
