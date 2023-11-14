module Strategies.VarIntro.Propagate

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Step
open Armada.Statement
open Armada.Thread
open Armada.Threads
open Armada.Transition
open Armada.Type
open FStar.Sequence.Ambient
open FStar.Sequence.Base
open FStar.WellFoundedRelation
open Spec.Behavior
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaStatement.Propagate
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.ArmadaStatement.Status
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.GlobalVars
open Strategies.GlobalVars.Init
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.PCRelation
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Helpers
open Strategies.VarIntro.Initialization
open Strategies.VarIntro.Invariant
open Util.List
open Util.Nth
open Util.Seq

let propagate_action: Armada.Action.t =
  { ok = true; program_statement = propagate_program_statement }

#push-options "--z3rlimit 20"

let get_propagate_lifter_case_skip_helper
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  : Lemma (requires   var_intro_lh_relation vr () ls hs
                    /\ NotStopped? hs.stop_reason
                    /\ ThreadStatusRunning? (hs.threads actor).status
                    /\ step == { nd = nd; action = propagate_action }
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
                    /\ receiver_tid <> actor
                    /\ ComputationProduces? (propagate_write_message_statement_computation actor nd ls)
                    /\ (let lthread = ls.threads actor in
                       let lwrite_buffer = lthread.write_buffer in
                       let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
                       let lwrite_message = index lwrite_buffer lposition in
                       let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
                         ThreadStatusRunning? lthread.status
                       /\ not (global_variables_unaddressed_in_write_message vr.vs lwrite_message)))
          (ensures  (match propagate_write_message_statement_computation actor nd ls with
                     | ComputationProduces ls' -> var_intro_lh_relation vr () ls' hs)) =
  let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
  let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
    false_elim ()
  else
    let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    if receiver_tid = actor then // can't propagate to the same thread
      false_elim ()
    else
      let propagator_thread = ls.threads actor in
      let receiver_thread = ls.threads receiver_tid in
      let which_message = receiver_thread.position_in_other_write_buffers actor in
      if which_message >= length propagator_thread.write_buffer then
        false_elim ()
      else (
        let write_message = index propagator_thread.write_buffer which_message in
        let position_in_other_write_buffers' =
          Spec.Map.upd receiver_thread.position_in_other_write_buffers actor (which_message + 1) in
        let receiver_thread' =
          { receiver_thread with position_in_other_write_buffers = position_in_other_write_buffers' } in
        let threads' = Spec.Map.upd ls.threads receiver_tid receiver_thread' in
        assert (positions_valid_in_threads threads');
        let lem () : Lemma (positions_in_write_buffers_match_except_global_variables vr.vs threads' hs.threads) =
        (
          introduce forall sender_tid' receiver_tid'. sender_receiver_trigger sender_tid' receiver_tid' ==>
                        write_buffers_match_except_global_variables vr.vs
                          (unread_write_buffer threads' sender_tid' receiver_tid')
                          (unread_write_buffer hs.threads sender_tid' receiver_tid')
          with introduce _ ==> _
          with _. (
            assert (position_valid ls.threads sender_tid' receiver_tid');
            assert (write_buffers_match_except_global_variables vr.vs
                      (unread_write_buffer ls.threads sender_tid' receiver_tid')
                      (unread_write_buffer hs.threads sender_tid' receiver_tid'));
            if receiver_tid <> receiver_tid' then
              ()
            else if actor <> sender_tid' then
              ()
            else (
              assert (unread_write_buffer hs.threads sender_tid' receiver_tid' == hunread_write_buffer);
              assert (unread_write_buffer threads' sender_tid' receiver_tid' == drop lunread_write_buffer 1);
              seq_to_list_drop_equals_tail lunread_write_buffer
            )
          )
        ) in
        lem ();
        assert (positions_in_write_buffers_match_except_global_variables vr.vs threads' hs.threads);
        match propagate_write_message write_message receiver_tid ls.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            // If propagate would trigger undefined behavior (e.g., by propagating to freed memory),
            // it just leaves memory unchanged.
            let ls' = { ls with threads = threads'; } in
            assert (states_match_except_global_variables vr.vs pc_relation ls' hs);
            assert (unstarted_threads_have_empty_write_buffers ls');
            assert (global_variables_unaddressed_in_memory vr.vs ls'.mem);
            assert (roots_match ls'.mem);
            assert (var_intro_lh_relation vr () ls' hs)
        | ComputationProduces mem' ->
            let ls' = { ls with mem = mem'; threads = threads'; } in
            propagate_write_message_statement_computation_s1_only_maintains_states_match vr.vs pc_relation actor nd
              ls hs;
            assert (unstarted_threads_have_empty_write_buffers ls');
            propagate_write_message_maintains_gvars_unaddressed vr.vs write_message receiver_tid ls.mem;
            assert (global_variables_unaddressed_in_memory vr.vs ls'.mem);
            assert (roots_match ls'.mem);
            assert (var_intro_lh_relation vr () ls' hs)
      )

#pop-options

let get_propagate_lifter_case_skip
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (nd: nondeterminism_t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  (lifter: step_lifter_t (list Armada.Step.t) unit)
  : Lemma
    (requires (  var_intro_lh_relation vr () ls hs
               /\ ComputationProduces? (propagate_write_message_statement_computation actor nd ls)
               /\ NotStopped? ls.stop_reason
               /\ list_len nd = 1
               /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
               /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
               /\ lifter == StepLifterSkip ()
               /\ step == { nd = nd; action = propagate_action }
               /\ (let lthread = ls.threads actor in
                  let lwrite_buffer = lthread.write_buffer in
                  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
                    lposition < length lwrite_buffer
                  /\ (let lwrite_message = index lwrite_buffer lposition in
                       ThreadStatusRunning? lthread.status
                     /\ not (global_variables_unaddressed_in_write_message vr.vs lwrite_message)))))
    (ensures  step_lifter_works
                (make_atomic_semantics armada_semantics)
                (make_atomic_semantics armada_semantics)
                vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                (var_intro_progress_measure vr) actor true true [step] ls hs lifter) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  let lthread = ls.threads actor in
  let lwrite_buffer = lthread.write_buffer in
  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
  let lwrite_message = index lwrite_buffer lposition in
  assert_norm (map_ghost armada_step_to_action [step] == propagate_action_list);
  get_propagate_lifter_case_skip_helper vr actor nd ls hs receiver_tid step;
  step_computation_is_propagate_computation actor nd ls step

#push-options "--z3rlimit 20"

let get_propagate_lifter_case_match
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (nd: nondeterminism_t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  (lifter: step_lifter_t (list Armada.Step.t) unit)
  : Lemma
    (requires (  var_intro_lh_relation vr () ls hs
               /\ ComputationProduces? (propagate_write_message_statement_computation actor nd ls)
               /\ NotStopped? ls.stop_reason
               /\ list_len nd = 1
               /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
               /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
               /\ (let lthread = ls.threads actor in
                  let hthread = hs.threads actor in
                  let lwrite_buffer = lthread.write_buffer in
                  let hwrite_buffer = hthread.write_buffer in
                  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
                  let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
                    ThreadStatusRunning? lthread.status
                  /\ length hwrite_buffer > hposition
                  /\ (let lwrite_message = index lwrite_buffer lposition in
                     let hwrite_message = index hwrite_buffer hposition in
                     let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
                     let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
                     let hstep = [step] in
                       step == { nd = nd; action = propagate_action }
                     /\ program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
                         vr.hatomic_prog [step]
                     /\ lifter == StepLifterLift hstep ()
                     /\ global_variables_unaddressed_in_write_message vr.vs lwrite_message
                     /\ global_variables_unaddressed_in_write_message vr.vs hwrite_message
                     /\ write_messages_match lwrite_message hwrite_message))))
    (ensures  step_lifter_works
                (make_atomic_semantics armada_semantics)
                (make_atomic_semantics armada_semantics)
                vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                (var_intro_progress_measure vr) actor true true [step] ls hs lifter) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let lwrite_buffer = lthread.write_buffer in
  let hwrite_buffer = hthread.write_buffer in
  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
  let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
  let lwrite_message = index lwrite_buffer lposition in
  let hwrite_message = index hwrite_buffer hposition in
  let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
  let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
  assert (map_ghost armada_step_to_action [step] == propagate_action_list);
  propagate_write_message_statement_computation_maintains_states_match vr.vs pc_relation actor nd ls hs;
  match propagate_write_message_statement_computation actor nd ls,
        propagate_write_message_statement_computation actor nd hs with
  | ComputationProduces ls', ComputationProduces hs' ->
      assert (states_match_except_global_variables vr.vs pc_relation ls' hs');
      assert (global_variables_unaddressed_in_memory vr.vs ls'.mem);
      assert (global_variables_unaddressed_in_memory vr.vs hs'.mem);
      assert (roots_match ls'.mem);
      assert (roots_match hs'.mem);
      propagate_maintains_all_running_threads_have_pcs_in_list actor nd vr.hpcs hs;
      propagate_maintains_all_gvars_have_types vr.vs vr.tds actor nd hs;
      step_computation_is_propagate_computation actor nd ls step;
      step_computation_is_propagate_computation actor nd hs step;
      introduce NotStopped? hs'.stop_reason ==> vr.inv hs'
      with _. (
        vr.inv_is_substep_invariant_proof ();
        assert (vr.inv hs);
        assert (contains_ubool step.action propagate_action_list);
        assert (contains_ubool propagate_action_list vr.hatomic_prog.actions);
        assert (Some hs' == step_computation actor true true step hs)
      );
      assert (var_intro_lh_relation vr () ls' hs')

#pop-options
#push-options "--z3rlimit 40"

let get_propagate_lifter_case_introduce_helper1
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  : Lemma (requires   var_intro_lh_relation vr () ls hs
                    /\ NotStopped? hs.stop_reason
                    /\ ThreadStatusRunning? (hs.threads actor).status
                    /\ step == { nd = nd; action = propagate_action }
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
                    /\ receiver_tid <> actor
                    /\ (let lthread = ls.threads actor in
                       let hthread = hs.threads actor in
                       let lwrite_buffer = lthread.write_buffer in
                       let hwrite_buffer = hthread.write_buffer in
                       let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
                          length hwrite_buffer > hposition
                       /\ (let hwrite_message = index hwrite_buffer hposition in
                          let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
                          let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
                            step == { nd = nd; action = propagate_action }
                          /\ program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
                              vr.hatomic_prog [step]
                          /\ not (global_variables_unaddressed_in_write_message vr.vs hwrite_message))))
          (ensures  (match propagate_write_message_statement_computation actor nd hs with
                     | ComputationProduces hs' -> var_intro_lh_relation vr () ls hs'
                     | _ -> False)) =
  let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
  let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
    false_elim ()
  else
    let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    if receiver_tid = actor then // can't propagate to the same thread
      false_elim ()
    else
      let propagator_thread = hs.threads actor in
      let receiver_thread = hs.threads receiver_tid in
      let which_message = receiver_thread.position_in_other_write_buffers actor in
      if which_message >= length propagator_thread.write_buffer then
        false_elim ()
      else
        let write_message = index propagator_thread.write_buffer which_message in
        let position_in_other_write_buffers' =
          Spec.Map.upd receiver_thread.position_in_other_write_buffers actor (which_message + 1) in
        let receiver_thread' =
          { receiver_thread with position_in_other_write_buffers = position_in_other_write_buffers' } in
        let threads' = Spec.Map.upd hs.threads receiver_tid receiver_thread' in
        let lem () : Lemma (  positions_valid_in_threads threads'
                            /\ positions_in_write_buffers_match_except_global_variables vr.vs ls.threads threads') =
        (
          introduce forall sender_tid' receiver_tid'. sender_receiver_trigger sender_tid' receiver_tid' ==>
                          position_valid threads' sender_tid' receiver_tid'
                        /\ write_buffers_match_except_global_variables vr.vs
                            (unread_write_buffer ls.threads sender_tid' receiver_tid')
                            (unread_write_buffer threads' sender_tid' receiver_tid')
          with introduce _ ==> _
          with _. (
            assert (position_valid hs.threads sender_tid' receiver_tid');
            assert (write_buffers_match_except_global_variables vr.vs
                      (unread_write_buffer ls.threads sender_tid' receiver_tid')
                      (unread_write_buffer hs.threads sender_tid' receiver_tid'));
            if receiver_tid <> receiver_tid' then
              ()
            else if actor <> sender_tid' then
              ()
            else (
              assert (unread_write_buffer ls.threads sender_tid' receiver_tid' == lunread_write_buffer);
              assert (unread_write_buffer threads' sender_tid' receiver_tid' == drop hunread_write_buffer 1);
              seq_to_list_drop_equals_tail hunread_write_buffer
            )
          )
        ) in
        lem ();
        assert (positions_valid_in_threads threads');
        assert (positions_in_write_buffers_match_except_global_variables vr.vs ls.threads threads');
        propagate_maintains_all_running_threads_have_pcs_in_list actor nd vr.hpcs hs;
        propagate_maintains_all_gvars_have_types vr.vs vr.tds actor nd hs;
        step_computation_is_propagate_computation actor nd hs step;
        match propagate_write_message write_message receiver_tid hs.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            // If propagate would trigger undefined behavior (e.g., by propagating to freed memory),
            // it just leaves memory unchanged.
            let hs' = { hs with threads = threads'; } in
            assert (states_match_except_global_variables vr.vs pc_relation ls hs');
            assert (all_running_threads_have_pcs_in_list vr.hpcs hs');
            assert (unstarted_threads_have_empty_write_buffers hs');
            assert (global_variables_unaddressed_in_memory vr.vs hs'.mem);
            assert (roots_match hs'.mem);
            assert (all_gvars_have_types hs'.mem vr.vs vr.tds);
            introduce NotStopped? hs'.stop_reason ==> vr.inv hs'
            with _. (
              vr.inv_is_substep_invariant_proof ();
              assert (vr.inv hs);
              assert (contains_ubool step.action propagate_action_list);
              assert (contains_ubool propagate_action_list vr.hatomic_prog.actions);
              assert (Some hs' == step_computation actor true true step hs)
            );
            assert (var_intro_lh_relation vr () ls hs')
        | ComputationProduces mem' ->
            let hs' = { hs with mem = mem'; threads = threads'; } in
            propagate_write_message_statement_computation_s2_only_maintains_states_match vr.vs pc_relation actor nd
              ls hs;
            assert (all_running_threads_have_pcs_in_list vr.hpcs hs');
            assert (unstarted_threads_have_empty_write_buffers hs');
            propagate_write_message_maintains_gvars_unaddressed vr.vs write_message receiver_tid hs.mem;
            assert (global_variables_unaddressed_in_memory vr.vs hs'.mem);
            assert (roots_match hs'.mem);
            assert (all_gvars_have_types hs'.mem vr.vs vr.tds);
            introduce NotStopped? hs'.stop_reason ==> vr.inv hs'
            with _. (
              vr.inv_is_substep_invariant_proof ();
              assert (vr.inv hs);
              assert (contains_ubool step.action propagate_action_list);
              assert (contains_ubool propagate_action_list vr.hatomic_prog.actions);
              assert (Some hs' == step_computation actor true true step hs)
            );
            assert (var_intro_lh_relation vr () ls hs')

let get_propagate_lifter_case_introduce_helper2
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (nd: nondeterminism_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  : Lemma (requires   var_intro_lh_relation vr () ls hs
                    /\ NotStopped? hs.stop_reason
                    /\ ThreadStatusRunning? (hs.threads actor).status
                    /\ step == { nd = nd; action = propagate_action }
                    /\ list_len nd = 1
                    /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
                    /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
                    /\ receiver_tid <> actor
                    /\ (let lthread = ls.threads actor in
                       let hthread = hs.threads actor in
                       let lwrite_buffer = lthread.write_buffer in
                       let hwrite_buffer = hthread.write_buffer in
                       let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
                          length hwrite_buffer > hposition
                       /\ (let hwrite_message = index hwrite_buffer hposition in
                          let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
                          let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
                            step == { nd = nd; action = propagate_action }
                          /\ program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
                              vr.hatomic_prog [step]
                          /\ not (global_variables_unaddressed_in_write_message vr.vs hwrite_message))))
          (ensures  (match propagate_write_message_statement_computation actor nd hs with
                     | ComputationProduces hs' ->
                           (hs'.threads actor).pc = (hs.threads actor).pc
                         /\ var_intro_unread_write_buffer_len_measure vr hs' [step] actor <
                             var_intro_unread_write_buffer_len_measure vr hs [step] actor
                     | _ -> False)) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  if   list_len nd <> 1
     || neqb (object_value_to_td (Cons?.hd nd)) (ObjectTDAbstract tid_t) then
    false_elim ()
  else
    let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
    if receiver_tid = actor then // can't propagate to the same thread
      false_elim ()
    else
      let propagator_thread = hs.threads actor in
      let receiver_thread = hs.threads receiver_tid in
      let which_message = receiver_thread.position_in_other_write_buffers actor in
      if which_message >= length propagator_thread.write_buffer then
        false_elim ()
      else
        let write_message = index propagator_thread.write_buffer which_message in
        let position_in_other_write_buffers' =
          Spec.Map.upd receiver_thread.position_in_other_write_buffers actor (which_message + 1) in
        let receiver_thread' =
          { receiver_thread with position_in_other_write_buffers = position_in_other_write_buffers' } in
        let threads' = Spec.Map.upd hs.threads receiver_tid receiver_thread' in
        assert ((threads' actor).write_buffer == (hs.threads actor).write_buffer);
        assert (which_message + 1 <= length (threads' actor).write_buffer);
        assert (position_in_other_write_buffers' actor == which_message + 1);
        assert (threads' receiver_tid == receiver_thread');
        assert ((threads' receiver_tid).position_in_other_write_buffers == position_in_other_write_buffers');
        assert ((threads' receiver_tid).position_in_other_write_buffers actor == which_message + 1);
        match propagate_write_message write_message receiver_tid hs.mem with
        | ComputationImpossible
        | ComputationUndefined ->
            // If propagate would trigger undefined behavior (e.g., by propagating to freed memory),
            // it just leaves memory unchanged.
            let hs' = { hs with threads = threads'; } in
            assert (var_intro_unread_write_buffer_len_measure vr hs [step] actor ==
                      length propagator_thread.write_buffer - which_message);
            assert (var_intro_unread_write_buffer_len_measure vr hs' [step] actor ==
                      length (hs'.threads actor).write_buffer - (which_message + 1));
            assert (var_intro_unread_write_buffer_len_measure vr hs' [step] actor <
                      var_intro_unread_write_buffer_len_measure vr hs [step] actor)
        | ComputationProduces mem' ->
            let hs' = { hs with mem = mem'; threads = threads'; } in
            assert (var_intro_unread_write_buffer_len_measure vr hs [step] actor ==
                      length propagator_thread.write_buffer - which_message);
            assert (var_intro_unread_write_buffer_len_measure vr hs' [step] actor ==
                      length (hs'.threads actor).write_buffer - (which_message + 1));
            assert (var_intro_unread_write_buffer_len_measure vr hs' [step] actor <
                      var_intro_unread_write_buffer_len_measure vr hs [step] actor)

let get_propagate_lifter_case_introduce
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (nd: nondeterminism_t)
  (receiver_tid: tid_t)
  (step: Armada.Step.t)
  (lifter: step_lifter_t (list Armada.Step.t) unit)
  : Lemma
    (requires (  var_intro_lh_relation vr () ls hs
               /\ ComputationProduces? (propagate_write_message_statement_computation actor nd ls)
               /\ NotStopped? ls.stop_reason
               /\ list_len nd = 1
               /\ object_value_to_td (Cons?.hd nd) == ObjectTDAbstract tid_t
               /\ receiver_tid == ObjectValueAbstract?.value (Cons?.hd nd)
               /\ step == { nd = nd; action = propagate_action }
               /\ (let lthread = ls.threads actor in
                  let hthread = hs.threads actor in
                  let lwrite_buffer = lthread.write_buffer in
                  let hwrite_buffer = hthread.write_buffer in
                  let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
                    ThreadStatusRunning? lthread.status
                  /\ length hwrite_buffer > hposition
                  /\ (let hwrite_message = index hwrite_buffer hposition in
                     let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
                     let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
                       program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
                         vr.hatomic_prog [step]
                     /\ lifter == StepLifterIntroduce [step] ()
                     /\ not (global_variables_unaddressed_in_write_message vr.vs hwrite_message)))))
    (ensures  step_lifter_works
                (make_atomic_semantics armada_semantics)
                (make_atomic_semantics armada_semantics)
                vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                (var_intro_progress_measure vr) actor true true [step] ls hs lifter) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let lwrite_buffer = lthread.write_buffer in
  let hwrite_buffer = hthread.write_buffer in
  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
  let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
  let lwrite_message = index lwrite_buffer lposition in
  let hwrite_message = index hwrite_buffer hposition in
  let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
  let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
  assert_norm (map_ghost armada_step_to_action [step] == propagate_action_list);
  get_propagate_lifter_case_introduce_helper1 vr actor nd ls hs receiver_tid step;
  get_propagate_lifter_case_introduce_helper2 vr actor nd ls hs receiver_tid step;
  step_computation_is_propagate_computation actor nd hs step;
  let hs' = Some?.v (step_computation_generic (make_atomic_semantics armada_semantics) actor true true [step] hs) in
  let progress_wfr = lex_nondep_wfr (default_wfr nat) (default_wfr nat) in
  let progress_measure = var_intro_progress_measure vr in
  assert (progress_wfr.relation (progress_measure hs' [step] actor) (progress_measure hs [step] actor))

let correspondence_for_propagate_implies_propagate_among_hactions
  (vr: var_intro_relation_t)
  (correspondence: ltoh_correspondence_t vr.vs vr.tds vr.inv)
  : Lemma (requires lactions_correspond_to_hactions_per_correspondence vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.lpc_to_hpcs
                      vr.return_hpcs vr.is_breaking_hpc vr.hpc_info vr.hatomic_prog.actions propagate_action_list
                      correspondence)
          (ensures  contains_ubool propagate_action_list vr.hatomic_prog.actions) =
  let pc_relation = var_intro_pc_relation vr.hpc_to_lpc vr.return_hpcs vr.return_pcs_unique_proof in
  vr.corresponding_hactions_correspond_proof ();
  match correspondence with
  | CorrespondencePropagate hidx ->
      nth_implies_contains_ubool vr.hatomic_prog.actions hidx propagate_action_list
  | CorrespondenceNormal hidx mapper ->
      let hactions = list_index vr.hatomic_prog.actions hidx in
      lactions_correspond_to_hactions_implies_not_propagate vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.return_hpcs
        ThreadStateRunning ThreadStateRunning ThreadStateRunning ThreadStateRunning
        mapper propagate_action_list hactions

let get_propagate_lifter_helper
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (nd: nondeterminism_t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_intro_lh_relation vr () ls hs
              /\ NotStopped? ls.stop_reason
              /\ ThreadStatusRunning? (ls.threads actor).status
              /\ contains_ubool propagate_action_list vr.latomic_prog.actions
              /\ ComputationProduces? (propagate_write_message_statement_computation actor nd ls))
    (ensures  fun lifter ->
                let step = { nd = nd; action = propagate_action } in
                step_lifter_works
                  (make_atomic_semantics armada_semantics)
                  (make_atomic_semantics armada_semantics)
                  vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                  (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                  (var_intro_progress_measure vr) actor true true [step] ls hs lifter) =
  let lthread = ls.threads actor in
  let hthread = hs.threads actor in
  let receiver_tid: tid_t = ObjectValueAbstract?.value (Cons?.hd nd) in
  assert (positions_in_write_buffers_match_except_global_variables vr.vs ls.threads hs.threads);
  assert (sender_receiver_trigger actor receiver_tid);
  let lunread_write_buffer = unread_write_buffer ls.threads actor receiver_tid in
  let hunread_write_buffer = unread_write_buffer hs.threads actor receiver_tid in
  let lwrite_buffer = lthread.write_buffer in
  let hwrite_buffer = hthread.write_buffer in
  let lposition = (ls.threads receiver_tid).position_in_other_write_buffers actor in
  let hposition = (hs.threads receiver_tid).position_in_other_write_buffers actor in
  assert (lunread_write_buffer == drop lwrite_buffer lposition);
  assert (hunread_write_buffer == drop hwrite_buffer hposition);
  assert (length lunread_write_buffer > 0);
  let lwrite_message = index lunread_write_buffer 0 in
  assert (lwrite_message == index lwrite_buffer lposition);
  let step = { nd = nd; action = propagate_action } in
  let lem () : Lemma (program_contains_action_of_step_generic (make_atomic_semantics armada_semantics)
                        vr.hatomic_prog [step]) =
  (
    vr.corresponding_hactions_correspond_proof ();
    assert (map_ghost armada_step_to_action [step] == propagate_action_list);
    let correspondence = get_correspondent_from_lists_correspond_ubool
      (lactions_correspond_to_hactions_per_correspondence vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.lpc_to_hpcs
         vr.return_hpcs vr.is_breaking_hpc vr.hpc_info vr.hatomic_prog.actions)
      vr.latomic_prog.actions vr.corresponding_hactions_info propagate_action_list
    in
    correspondence_for_propagate_implies_propagate_among_hactions vr correspondence
  ) in
  lem ();
  if global_variables_unaddressed_in_write_message vr.vs lwrite_message then
    let hwrite_message = index hunread_write_buffer 0 in
    assert (hwrite_message == index hwrite_buffer hposition);
    if global_variables_unaddressed_in_write_message vr.vs hwrite_message then (
      let lifter = StepLifterLift [step] () in
      get_propagate_lifter_case_match vr actor ls hs nd receiver_tid step lifter;
      lifter
    )
    else (
      let lifter = StepLifterIntroduce [step] () in
      get_propagate_lifter_case_introduce vr actor ls hs nd receiver_tid step lifter;
      lifter
    )
  else (
    let lifter = StepLifterSkip () in
    get_propagate_lifter_case_skip vr actor ls hs nd receiver_tid step lifter;
    lifter
  )

let get_propagate_lifter
  (vr: var_intro_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (ls: Armada.State.t)
  (hs: Armada.State.t)
  (lsteps: list Armada.Step.t)
  : Ghost (step_lifter_t (list Armada.Step.t) unit)
    (requires   var_intro_lh_relation vr () ls hs
              /\ Some? (steps_computation_generic armada_semantics actor starts_atomic_block ends_atomic_block
                         lsteps ls)
              /\ contains_ubool (map_ghost armada_step_to_action lsteps) vr.latomic_prog.actions
              /\ (Cons?.hd lsteps).action.program_statement.statement == PropagateWriteMessageStatement)
    (ensures  fun lifter ->
                step_lifter_works
                  (make_atomic_semantics armada_semantics)
                  (make_atomic_semantics armada_semantics)
                  vr.latomic_prog vr.hatomic_prog unit (var_intro_lh_relation vr)
                  (nat * nat) (lex_nondep_wfr (default_wfr nat) (default_wfr nat))
                  (var_intro_progress_measure vr) actor starts_atomic_block ends_atomic_block lsteps ls hs lifter) =
  let step = Cons?.hd lsteps in
  let nd = step.nd in
  let lactions = map_ghost armada_step_to_action lsteps in
  vr.corresponding_hactions_correspond_proof ();
  let correspondence = get_correspondent_from_lists_correspond_ubool
    (lactions_correspond_to_hactions_per_correspondence vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.lpc_to_hpcs vr.return_hpcs
       vr.is_breaking_hpc vr.hpc_info vr.hatomic_prog.actions)
    vr.latomic_prog.actions vr.corresponding_hactions_info lactions
  in
  match correspondence with
  | CorrespondencePropagate hidx ->
      possible_propagate_action_ok actor starts_atomic_block ends_atomic_block ls lsteps;
      get_propagate_lifter_helper vr actor ls hs nd
  | CorrespondenceNormal hidx mapper ->
      (match list_nth vr.hatomic_prog.actions hidx with
       | Some hactions ->
           let lstart_state = action_to_starting_thread_state (Cons?.hd lactions) in
           let lend_state = actions_to_ending_thread_state lactions in
           let hstart_state = action_to_starting_thread_state (Cons?.hd hactions) in
           let hend_state = actions_to_ending_thread_state hactions in
           lactions_correspond_to_hactions_implies_not_propagate vr.vs vr.tds vr.inv vr.hpc_to_lpc vr.return_hpcs
             lstart_state hstart_state lend_state hend_state mapper lactions hactions;
           false_elim ()
       | None -> false_elim ())

#pop-options
