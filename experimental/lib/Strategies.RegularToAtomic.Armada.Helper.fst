module Strategies.RegularToAtomic.Armada.Helper

open Armada.Action
open Armada.Base
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open FStar.List.Tot
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Map
open Spec.Ubool
open Strategies.ArmadaStatement.Status
open Strategies.Atomic
open Strategies.RegularToAtomic
open Strategies.Semantics
open Strategies.Semantics.Armada
open Util.Behavior
open Util.List
open Util.Nth

let is_breaking_optional_pc
  (pc_breaking: pc_t -> GTot bool)
  (optional_pc: option pc_t)
  : GTot bool =
  match optional_pc with
  | Some pc -> pc_breaking pc
  | None -> true

let pc_breaking_correct_specific
  (pc_breaking: pc_t -> GTot bool)
  (ps: program_statement_t)
  : GTot bool =
     is_breaking_optional_pc pc_breaking ps.start_pc = ps.starts_atomic_block
  && is_breaking_optional_pc pc_breaking ps.end_pc = ps.ends_atomic_block
  && (implies (None? ps.end_pc) (is_breaking_optional_pc pc_breaking ps.start_pc))

let pc_breaking_correct
  (lprog: Armada.Program.t)
  (pc_breaking: pc_t -> GTot bool)
  : GTot bool =
  for_all_ghost (pc_breaking_correct_specific pc_breaking) lprog.program_statements

let created_threads_initially_breaking_specific
  (pc_breaking: pc_t -> GTot bool)
  (ps: program_statement_t)
  : GTot bool =
  match ps.statement with
  | CreateThreadStatement _ initial_pc _ _ _ _ _ -> pc_breaking initial_pc
  | _ -> true

let created_threads_initially_breaking
  (lprog: Armada.Program.t)
  (pc_breaking: pc_t -> GTot bool)
  : GTot bool =
  for_all_ghost (created_threads_initially_breaking_specific pc_breaking) lprog.program_statements

let actions_starting_at_pc_correct_specific
  (actions_starting_at_pc: option pc_t -> GTot (list Armada.Action.t))
  (action: Armada.Action.t)
  : GTot ubool =
  contains_ubool action (actions_starting_at_pc action.program_statement.start_pc)

let actions_starting_at_pc_correct
  (lprog: Armada.Program.t)
  (actions_starting_at_pc: option pc_t -> GTot (list Armada.Action.t))
  : GTot ubool =
  for_all_ubool (actions_starting_at_pc_correct_specific actions_starting_at_pc) (all_actions lprog.program_statements)

let starting_successors_match_path_infos_specific
  (starting_successors: list (successor_info_t armada_semantics))
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  (successor: successor_info_t armada_semantics)
  : GTot ubool =
    successor.path_index < length atomic_path_infos
  /\ (index atomic_path_infos successor.path_index).path == [successor.action]

let starting_successors_match_path_infos
  (starting_successors: list (successor_info_t armada_semantics))
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool
    (starting_successors_match_path_infos_specific starting_successors atomic_path_infos)
    starting_successors

let path_successor_matches_path_info
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  (atomic_path_info: atomic_path_info_t armada_semantics)
  (successor: successor_info_t armada_semantics)
  : GTot ubool =
     successor.path_index < length atomic_path_infos
  /\ (index atomic_path_infos successor.path_index).path == append atomic_path_info.path [successor.action]

let path_successors_match_path_infos_specific
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  (atomic_path_info: atomic_path_info_t armada_semantics)
  : GTot ubool =
  for_all_ubool (path_successor_matches_path_info atomic_path_infos atomic_path_info) atomic_path_info.successors

let path_successors_match_path_infos
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool (path_successors_match_path_infos_specific atomic_path_infos) atomic_path_infos

let is_breaking_armada_action (pc_breaking: pc_t -> GTot bool) (action: Armada.Action.t) : GTot bool =
    not action.ok
  || is_breaking_optional_pc pc_breaking action.program_statement.end_pc
  || (match action.program_statement.statement with
     | AssertFalseStatement _
     | TerminateProcessStatement _
     | TerminateThreadStatement _
     | MethodCallStatement _ _ _ _ _ true -> true
     | _ -> false)

let path_breaking_correct_specific
  (pc_breaking: pc_t -> GTot bool)
  (atomic_path_info: atomic_path_info_t armada_semantics)
  : GTot bool =
     Cons? atomic_path_info.path
  && atomic_path_info.breaking = is_breaking_armada_action pc_breaking (last atomic_path_info.path)

let path_breaking_correct
  (pc_breaking: pc_t -> GTot bool)
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot bool =
  for_all_ghost (path_breaking_correct_specific pc_breaking) atomic_path_infos

let path_atomic_index_correct
  (hprog_actions: list (list Armada.Action.t))
  (atomic_path_info: atomic_path_info_t armada_semantics)
  : GTot ubool =
  atomic_path_info.breaking ==>
      atomic_path_info.atomic_action_index < length hprog_actions
    /\ atomic_path_info.path == index hprog_actions atomic_path_info.atomic_action_index

let path_atomic_indices_correct
  (hprog_actions: list (list Armada.Action.t))
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool (path_atomic_index_correct hprog_actions) atomic_path_infos

let path_action_in_lprog
  (lprog: Armada.Program.t)
  (action: Armada.Action.t)
  : GTot ubool =
  contains_ubool action.program_statement lprog.program_statements

let path_actions_in_lprog_specific
  (lprog: Armada.Program.t)
  (atomic_path_info: atomic_path_info_t armada_semantics)
  : GTot ubool =
  for_all_ubool (path_action_in_lprog lprog) atomic_path_info.path

let path_actions_in_lprog
  (lprog: Armada.Program.t)
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool (path_actions_in_lprog_specific lprog) atomic_path_infos

let action_matches_successor
  (action: Armada.Action.t)
  (successor: successor_info_t armada_semantics)
  : GTot ubool =
  action == successor.action

let successors_include_action
  (successors: list (successor_info_t armada_semantics))
  (action: Armada.Action.t)
  : GTot ubool =
  exists_ubool (action_matches_successor action) successors

let starting_successors_reflect_action
  (pc_breaking: pc_t -> GTot bool)
  (starting_successors: list (successor_info_t armada_semantics))
  (action: Armada.Action.t)
  : GTot ubool =
  is_breaking_optional_pc pc_breaking action.program_statement.start_pc ==>
    successors_include_action starting_successors action

let starting_successors_complete
  (lprog: Armada.Program.t)
  (pc_breaking: pc_t -> GTot bool)
  (starting_successors: list (successor_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool (starting_successors_reflect_action pc_breaking starting_successors)
    (all_actions lprog.program_statements)

let path_successors_complete_specific
  (actions_starting_at_pc: option pc_t -> GTot (list Armada.Action.t))
  (atomic_path_info: atomic_path_info_t armada_semantics)
  : GTot ubool =
  not atomic_path_info.breaking ==>
       length atomic_path_info.path > 0
    /\ (let final_action = last atomic_path_info.path in
       let actions = actions_starting_at_pc (final_action.program_statement.end_pc) in
       for_all_ubool (successors_include_action atomic_path_info.successors) actions)

let path_successors_complete
  (actions_starting_at_pc: option pc_t -> GTot (list Armada.Action.t))
  (atomic_path_infos: list (atomic_path_info_t armada_semantics))
  : GTot ubool =
  for_all_ubool (path_successors_complete_specific actions_starting_at_pc) atomic_path_infos

noeq type regular_refines_atomic_params_t = {
  sem: semantics_t;
  lprog: program_t sem;
  hprog: program_t (make_atomic_semantics sem);
  is_breaking_state: sem.state_t -> sem.actor_t -> GTot bool;
  starting_successors: list (successor_info_t sem);
  atomic_path_infos: list (atomic_path_info_t sem);
}

noeq type armada_refines_atomic_relation_t = {
  lprog: Armada.Program.t;
  hprog: program_t (make_atomic_semantics armada_semantics);
  pc_breaking: pc_t -> GTot bool;
  actions_starting_at_pc: option pc_t -> GTot (list Armada.Action.t);
  starting_successors: list (successor_info_t armada_semantics);
  atomic_path_infos: list (atomic_path_info_t armada_semantics);

  actions_starting_at_pc_correct_proof: unit ->
    squash (actions_starting_at_pc_correct lprog actions_starting_at_pc);

  starting_successors_match_path_infos_proof: unit ->
    squash (starting_successors_match_path_infos starting_successors atomic_path_infos);

  path_successors_match_path_infos_proof: unit ->
    squash (path_successors_match_path_infos atomic_path_infos);

  path_breaking_correct_proof: unit ->
    squash (path_breaking_correct pc_breaking atomic_path_infos);

  path_atomic_indices_correct_proof: unit ->
    squash (path_atomic_indices_correct hprog.actions atomic_path_infos);

  path_actions_in_lprog_proof: unit ->
    squash (path_actions_in_lprog lprog atomic_path_infos);

  starting_successors_complete_proof: unit ->
    squash (starting_successors_complete lprog pc_breaking starting_successors);

  path_successors_complete_proof: unit ->
    squash (path_successors_complete actions_starting_at_pc atomic_path_infos);

  created_threads_initially_breaking_proof: unit ->
    squash (created_threads_initially_breaking lprog pc_breaking);

  pc_breaking_correct_proof: unit ->
    squash (pc_breaking_correct lprog pc_breaking);

  main_start_pc_breaking_proof: unit ->
    squash (pc_breaking lprog.main_start_pc);

  inits_identical_proof: unit ->
    squash (Armada.Program.init_program lprog == hprog.init_f);
}

let my_is_breaking_state
  (pc_breaking: pc_t -> GTot bool)
  (s: Armada.State.t)
  (tid: tid_t)
  : GTot bool =
  if NotStopped? s.stop_reason then
    let thread = s.threads tid in
    if ThreadStatusRunning? thread.status then
      pc_breaking thread.pc
    else
      true
  else
    true

let aa_to_ra_params (aa: armada_refines_atomic_relation_t) : GTot regular_refines_atomic_params_t =
  {
    sem = armada_semantics;
    lprog = armada_program_to_generic aa.lprog;
    hprog = aa.hprog;
    is_breaking_state = my_is_breaking_state aa.pc_breaking;
    starting_successors = aa.starting_successors;
    atomic_path_infos = aa.atomic_path_infos;
  }

let step_not_ending_atomic_block_ends_at_pc
  (aa: armada_refines_atomic_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires (  contains_ubool step.action.program_statement aa.lprog.program_statements
                     /\ Some? (step_computation actor starts_atomic_block false step s)))
          (ensures  (  Some? step.action.program_statement.end_pc
                     /\ (let s' = Some?.v (step_computation actor starts_atomic_block false step s) in
                        let pc' = Some?.v step.action.program_statement.end_pc in
                        (s'.threads actor).pc = pc'))) =
  aa.pc_breaking_correct_proof ()

let rec steps_not_ending_atomic_block_end_at_pc
  (aa: armada_refines_atomic_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires (  Cons? steps
                     /\ (let step = last steps in
                        contains_ubool step.action.program_statement aa.lprog.program_statements)
                     /\ Some? (steps_computation_generic armada_semantics actor starts_atomic_block
                                false steps s)))
          (ensures  (let step = last steps in
                       Some? step.action.program_statement.end_pc
                     /\ (let s' = Some?.v (steps_computation_generic armada_semantics actor
                                            starts_atomic_block false steps s) in
                        let pc' = Some?.v step.action.program_statement.end_pc in
                        (s'.threads actor).pc = pc')))
          (decreases steps) =
  match steps with
  | [last_step] -> step_not_ending_atomic_block_ends_at_pc aa actor starts_atomic_block last_step s
  | first_step :: remaining_steps ->
      let s_mid = Some?.v (step_computation actor starts_atomic_block false first_step s) in
      steps_not_ending_atomic_block_end_at_pc aa actor false remaining_steps s_mid

let lemma_starting_successors_match_path_infos
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (successor: successor_info_t armada_semantics{
       rap == aa_to_ra_params aa
     /\ contains_ubool successor rap.starting_successors})
  : squash (   successor.path_index < length rap.atomic_path_infos
            /\ (index rap.atomic_path_infos successor.path_index).path == [successor.action]) =
  aa.starting_successors_match_path_infos_proof ()

#push-options "--z3rlimit 10"

let lemma_path_successors_match_path_infos
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (atomic_path_info: atomic_path_info_t armada_semantics)
  (successor: successor_info_t armada_semantics{
       rap == aa_to_ra_params aa
     /\ contains_ubool atomic_path_info rap.atomic_path_infos
     /\ contains_ubool successor atomic_path_info.successors})
  : squash (   successor.path_index < length rap.atomic_path_infos
            /\ (index rap.atomic_path_infos successor.path_index).path ==
                 append atomic_path_info.path [successor.action]) =
  aa.path_successors_match_path_infos_proof ()

#pop-options

let executing_step_leads_to_breaking
  (aa: armada_refines_atomic_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  (s': Armada.State.t)
  : Lemma (requires Some s' == step_computation_generic armada_semantics actor starts_atomic_block
                                 ends_atomic_block step s
                    /\ contains_ubool step.action.program_statement aa.lprog.program_statements
                    /\ (starts_atomic_block ==> my_is_breaking_state aa.pc_breaking s actor))
          (ensures (let action = armada_semantics.step_to_action_f step in
                    my_is_breaking_state aa.pc_breaking s' actor = is_breaking_armada_action aa.pc_breaking action)) =
  let action = armada_semantics.step_to_action_f step in
  let program_statement = action.program_statement in
  let statement = program_statement.statement in
  aa.pc_breaking_correct_proof ();
  executing_step_changes_status_depending_on_statement actor starts_atomic_block ends_atomic_block step s

let rec executing_steps_on_path_leads_to_breaking
  (aa: armada_refines_atomic_relation_t)
  (path: list Armada.Action.t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t)
  (s': Armada.State.t)
  : Lemma (requires   map_ghost armada_semantics.step_to_action_f steps == path
                    /\ Cons? path
                    /\ Some s' == steps_computation_generic armada_semantics actor starts_atomic_block
                                   ends_atomic_block steps s
                    /\ for_all_ubool (fun action -> contains_ubool action.program_statement aa.lprog.program_statements)
                        path
                    /\ (starts_atomic_block ==> my_is_breaking_state aa.pc_breaking s actor))
           (ensures  my_is_breaking_state aa.pc_breaking s' actor =
                       is_breaking_armada_action aa.pc_breaking (last path)) =
  match steps with
  | [last_step] -> executing_step_leads_to_breaking aa actor starts_atomic_block ends_atomic_block last_step s s'
  | first_step :: remaining_steps ->
      let s_mid = Some?.v (step_computation_generic armada_semantics actor starts_atomic_block false
                             first_step s) in
      executing_steps_on_path_leads_to_breaking aa (Cons?.tl path) actor false ends_atomic_block remaining_steps
        s_mid s'

let executing_step_starts_at_pc
  (aa: armada_refines_atomic_relation_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t)
  : Lemma (requires   Some? (step_computation_generic armada_semantics actor starts_atomic_block
                               ends_atomic_block step s)
                    /\ contains_ubool step.action.program_statement aa.lprog.program_statements)
          (ensures (match step.action.program_statement.start_pc with
                    | None -> starts_atomic_block
                    | Some pc -> pc = (s.threads actor).pc)) =
  aa.pc_breaking_correct_proof ()

let lemma_path_breaking_correct
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (atomic_path_info: atomic_path_info_t armada_semantics)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (s: Armada.State.t{
      rap == aa_to_ra_params aa
    /\ contains_ubool atomic_path_info rap.atomic_path_infos
    /\ (map_ghost armada_semantics.step_to_action_f steps) == atomic_path_info.path
    /\ Some? (steps_computation_generic armada_semantics actor starts_atomic_block
               ends_atomic_block steps s)
    /\ (starts_atomic_block ==> rap.is_breaking_state s actor)})
  : squash (let s' = Some?.v (steps_computation_generic armada_semantics actor
                                starts_atomic_block ends_atomic_block steps s) in
            (atomic_path_info.breaking = rap.is_breaking_state s' actor)) =
  aa.path_breaking_correct_proof ();
  let s' = Some?.v (steps_computation_generic armada_semantics actor starts_atomic_block
                      ends_atomic_block steps s) in
  aa.path_actions_in_lprog_proof ();
  executing_steps_on_path_leads_to_breaking aa atomic_path_info.path actor starts_atomic_block ends_atomic_block
    steps s s'

let lemma_path_atomic_indices_correct
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (atomic_path_info: atomic_path_info_t rap.sem{
       rap == aa_to_ra_params aa
     /\ contains_ubool atomic_path_info rap.atomic_path_infos
     /\ atomic_path_info.breaking})
  : squash (   atomic_path_info.atomic_action_index < length rap.hprog.actions
            /\ index rap.hprog.actions atomic_path_info.atomic_action_index == atomic_path_info.path) =
  aa.path_atomic_indices_correct_proof ()

#push-options "--z3cliopt smt.qi.eager_threshold=100"

let lemma_starting_successors_complete
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      rap == aa_to_ra_params aa
    /\ contains_ubool step.action rap.lprog.actions
    /\ rap.is_breaking_state s actor
    /\ Some? (step_computation_generic armada_semantics actor starts_atomic_block
               ends_atomic_block step s)})
  : squash (action_among_successors armada_semantics step.action rap.starting_successors) =
  aa.starting_successors_complete_proof ()

let lemma_path_successors_complete
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (atomic_path_info: atomic_path_info_t armada_semantics)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (steps: list Armada.Step.t)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      rap == aa_to_ra_params aa
    /\ contains_ubool atomic_path_info rap.atomic_path_infos
    /\ map_ghost armada_step_to_action steps == atomic_path_info.path
    /\ contains_ubool step.action rap.lprog.actions
    /\ not atomic_path_info.breaking
    /\ (match steps_computation_generic armada_semantics actor starts_atomic_block
               false steps s with
       | None -> False
       | Some s' -> Some? (step_computation_generic armada_semantics actor false
                            ends_atomic_block step s'))})
  : squash (action_among_successors armada_semantics step.action atomic_path_info.successors) =
  let s' = Some?.v (steps_computation_generic armada_semantics actor starts_atomic_block false
                      steps s) in
  aa.path_actions_in_lprog_proof ();
  list_contains_last atomic_path_info.path;
  map_ghost_maps_last armada_step_to_action steps;
  steps_not_ending_atomic_block_end_at_pc aa actor starts_atomic_block steps s;
  all_actions_has_all_actions step.action aa.lprog.program_statements;
  executing_step_starts_at_pc aa actor false ends_atomic_block step s';
  aa.path_successors_complete_proof ();
  aa.actions_starting_at_pc_correct_proof ()

#pop-options

let lemma_actions_dont_unbreak_other_actors
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (ends_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
    let action = step.action in
      rap == aa_to_ra_params aa
    /\ contains_ubool action rap.lprog.actions
    /\ Some? (step_computation_generic armada_semantics actor starts_atomic_block
               ends_atomic_block step s)})
  : squash (let s' = Some?.v (step_computation_generic armada_semantics actor
                                starts_atomic_block ends_atomic_block step s) in
            forall other_actor. rap.is_breaking_state s other_actor /\ actor <> other_actor ==>
                             rap.is_breaking_state s' other_actor) =
  step_effects_on_other_threads actor starts_atomic_block ends_atomic_block step s;
  if not step.action.ok then
    ()
  else (
    match step.action.program_statement.statement with
    | CreateThreadStatement _ _ _ _ _ _ _ ->
        all_actions_has_all_actions step.action aa.lprog.program_statements;
        aa.created_threads_initially_breaking_proof ()
    | JoinStatement _ -> ()
    | PropagateWriteMessageStatement -> ()
    | _ -> ()
  )

let lemma_actions_break_if_last_in_transition
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (actor: tid_t)
  (starts_atomic_block: bool)
  (step: Armada.Step.t)
  (s: Armada.State.t{
      rap == aa_to_ra_params aa
    /\ contains_ubool step.action rap.lprog.actions
    /\ Some? (step_computation_generic armada_semantics actor starts_atomic_block true step s)
    /\ (starts_atomic_block ==> rap.is_breaking_state s actor)})
  : squash (let s' = Some?.v (step_computation_generic armada_semantics actor
                               starts_atomic_block true step s) in
            rap.is_breaking_state s' actor) =
  if not step.action.ok then
    ()
  else (
    let s' = Some?.v (step_computation_generic armada_semantics actor starts_atomic_block true step s) in
    aa.pc_breaking_correct_proof ();
    all_actions_has_all_actions step.action aa.lprog.program_statements;
    assert (is_breaking_optional_pc aa.pc_breaking step.action.program_statement.end_pc);
    executing_step_changes_status_depending_on_statement actor starts_atomic_block true step s;
    executing_step_starts_at_pc aa actor starts_atomic_block true step s
  )

let lemma_init_breaks_all_actors
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (s: Armada.State.t{rap == aa_to_ra_params aa /\ rap.lprog.init_f s})
  : squash (forall actor. rap.is_breaking_state s actor) =
  aa.main_start_pc_breaking_proof ()

let lemma_init_implies_init
  (aa: armada_refines_atomic_relation_t)
  (rap: regular_refines_atomic_params_t)
  (s: Armada.State.t{rap == aa_to_ra_params aa /\ rap.lprog.init_f s})
  : squash (rap.hprog.init_f s) =
  aa.inits_identical_proof ()

let aa_to_ra (aa: armada_refines_atomic_relation_t)
  : GTot (ra: regular_refines_atomic_relation_t{
              ra.sem == armada_semantics
            /\ ra.lprog == armada_program_to_generic aa.lprog
            /\ ra.hprog == aa.hprog}) =
  let rap = aa_to_ra_params aa in
  let ra: regular_refines_atomic_relation_t =
  {
     sem = rap.sem;
     lprog = rap.lprog;
     hprog = rap.hprog;
     is_breaking_state = rap.is_breaking_state;
     starting_successors = rap.starting_successors;
     atomic_path_infos = rap.atomic_path_infos;
     starting_successors_match_path_infos_proof = lemma_starting_successors_match_path_infos aa rap;
     path_successors_match_path_infos_proof = lemma_path_successors_match_path_infos aa rap;
     path_breaking_correct_proof = lemma_path_breaking_correct aa rap;
     path_atomic_indices_correct_proof = lemma_path_atomic_indices_correct aa rap;
     starting_successors_complete_proof = lemma_starting_successors_complete aa rap;
     path_successors_complete_proof = lemma_path_successors_complete aa rap;
     actions_dont_unbreak_other_actors_proof = lemma_actions_dont_unbreak_other_actors aa rap;
     actions_break_if_last_in_transition_proof = lemma_actions_break_if_last_in_transition aa rap;
     init_breaks_all_actors_proof = lemma_init_breaks_all_actors aa rap;
     init_implies_init_proof = lemma_init_implies_init aa rap;
   } in
   ra

let armada_refines_atomic_relation_implies_refinement (aa: armada_refines_atomic_relation_t)
  : Lemma (ensures (spec_refines_spec
                    (program_to_spec aa.lprog)
                    (semantics_to_spec (make_atomic_semantics armada_semantics) aa.hprog)
                    eq2)) =
  let ra: regular_refines_atomic_relation_t = aa_to_ra aa in
  regular_refines_atomic_relation_implies_refinement ra;
  armada_spec_refines_generic aa.lprog;
  spec_refinement_transitivity
    (program_to_spec aa.lprog)
    (semantics_to_spec ra.sem ra.lprog)
    (semantics_to_spec (make_atomic_semantics ra.sem) ra.hprog)
    eq2
    eq2
    eq2
