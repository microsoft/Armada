module Strategies.VarHiding.Initialization

open Armada.Base
open Armada.Computation
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Type
open Spec.List
open Spec.Ubool
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.ArmadaInvariant.PositionsValid
open Strategies.ArmadaInvariant.UnstartedThreads
open Strategies.GlobalVars
open Strategies.GlobalVars.Init
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarHiding
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.VarHiding.Defs
open Util.List

let rec remove_hidden_initializers_ensures_memories_match_except_gvars
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires initializers_match_except_global_variables vs which_are_hidings linits hinits)
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                     memories_match_except_global_variables vs lmem hmem)) =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      remove_hidden_initializers_ensures_memories_match_except_gvars vs remaining_which_are_hidings remaining_linits
        hinits lmem
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      remove_hidden_initializers_ensures_memories_match_except_gvars vs remaining_which_are_hidings remaining_linits
        remaining_hinits lmem
  | _, _, _ -> ()

let rec initializers_match_except_global_variables_ensures_inclusion
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (init: initializer_t)
  : Lemma (requires   contains_ubool init hinits
                    /\ initializers_match_except_global_variables vs which_are_hidings linits hinits)
          (ensures  contains_ubool init linits) =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      initializers_match_except_global_variables_ensures_inclusion vs remaining_which_are_hidings
        remaining_linits hinits init
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      if eqb init first_hinit then
        ()
      else
        initializers_match_except_global_variables_ensures_inclusion vs remaining_which_are_hidings
          remaining_linits remaining_hinits init
  | _, _, _ -> ()

let initializers_match_except_global_variables_ensures_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_hidings linits hinits
                    /\ memory_satisfies_global_initializers mem linits)
          (ensures  memory_satisfies_global_initializers mem hinits) =
  introduce forall init. contains_ubool init hinits ==> memory_satisfies_global_initializer mem init
  with introduce _ ==> _
  with _. (
    initializers_match_except_global_variables_ensures_inclusion vs which_are_hidings linits hinits init
  )

let rec initializers_match_except_global_variables_ensures_no_gvars_in_hinits
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  : Lemma (requires initializers_match_except_global_variables vs which_are_hidings linits hinits)
          (ensures  forall init. contains_ubool init hinits ==> not (list_contains init.var_id vs)) =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      initializers_match_except_global_variables_ensures_no_gvars_in_hinits vs remaining_which_are_hidings
        remaining_linits hinits
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      initializers_match_except_global_variables_ensures_no_gvars_in_hinits vs remaining_which_are_hidings
        remaining_linits remaining_hinits
  | _, _, _ -> ()
  
let rec remove_hidden_initializers_maintains_memory_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (all_hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_hidings linits hinits
                    /\ memory_satisfies_global_initializers lmem all_hinits
                    /\ (forall init. contains_ubool init hinits ==> contains_ubool init all_hinits)
                    /\ (forall init. contains_ubool init all_hinits ==> not (list_contains init.var_id vs)))
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                     memory_satisfies_global_initializers hmem all_hinits)) =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      remove_hidden_initializers_maintains_memory_satisfies_global_initializers vs remaining_which_are_hidings
        remaining_linits hinits all_hinits lmem
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      remove_hidden_initializers_maintains_memory_satisfies_global_initializers vs remaining_which_are_hidings
        remaining_linits remaining_hinits all_hinits lmem
  | _, _, _ -> ()

let remove_hidden_initializers_ensures_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  initializers_match_except_global_variables_ensures_satisfies_global_initializers vs which_are_hidings
    linits hinits lmem;
  initializers_match_except_global_variables_ensures_no_gvars_in_hinits vs which_are_hidings linits hinits;
  remove_hidden_initializers_maintains_memory_satisfies_global_initializers vs which_are_hidings linits
    hinits hinits lmem;
  remove_hidden_initializers_ensures_memories_match_except_gvars vs which_are_hidings linits hinits lmem

let rec remove_hidden_initializers_maintains_nonglobal_root
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (lmem: Armada.Memory.t)
  (root_id: root_id_t)
  : Lemma (requires not (RootIdGlobal? root_id))
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings inits lmem in
                     hmem root_id == lmem root_id)) =
  match which_are_hidings, inits with
  | [], _ -> ()
  | true :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_nonglobal_root remaining_which_are_hidings remaining_inits lmem root_id
  | false :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_nonglobal_root remaining_which_are_hidings remaining_inits lmem root_id
  | _, _ -> ()

let rec remove_hidden_initializers_ensures_satisfies_main_stack_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (main_stack_initializers: list initializer_t)
  (lmem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  match local_variables, main_stack_initializers with
  | [], [] -> ()
  | var_id :: remaining_var_ids, initializer :: remaining_initializers ->
      let root_id = RootIdStack initial_tid main_method_id initial_frame_uniq var_id in
      remove_hidden_initializers_maintains_nonglobal_root which_are_hidings linits lmem root_id;
      remove_hidden_initializers_ensures_satisfies_main_stack_initializers vs which_are_hidings linits
        initial_tid main_method_id initial_frame_uniq remaining_var_ids remaining_initializers lmem
  | _ -> ()

let rec matching_hinits_are_present
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : GTot bool =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> true
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      matching_hinits_are_present remaining_which_are_hidings remaining_linits hinits lmem
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      (match lmem (RootIdGlobal first_hinit.var_id) with
       | RootGlobal _ -> exists_ghost (var_id_in_initializer first_hinit.var_id) hinits
       | _ -> false)
  | _, _, _ -> false

let rec remove_hidden_initializers_maintains_roots_match
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires roots_match mem)
          (ensures  roots_match (remove_hidden_initializers which_are_hidings inits mem)) =
  match which_are_hidings, inits with
  | [], _ -> ()
  | true :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_roots_match remaining_which_are_hidings remaining_inits mem
  | false :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_roots_match remaining_which_are_hidings remaining_inits mem
  | _, _ -> ()

let rec remove_hidden_initializers_doesnt_change_nonglobal
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  (root_id: root_id_t)
  : Lemma (requires not (RootIdGlobal? root_id))
          (ensures  mem root_id == (remove_hidden_initializers which_are_hidings inits mem) root_id) =
  match which_are_hidings, inits with
  | [], _ -> ()
  | true :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_doesnt_change_nonglobal remaining_which_are_hidings remaining_inits mem root_id
  | false :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_doesnt_change_nonglobal remaining_which_are_hidings remaining_inits mem root_id
  | _, _ -> ()

let rec remove_hidden_initializers_maintains_root_invalid_outside_initializations
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  (root_id: root_id_t)
  : Lemma (requires not (RootIdGlobal? root_id))
          (ensures  mem root_id == (remove_hidden_initializers which_are_hidings inits mem) root_id) =
  match which_are_hidings, inits with
  | [], _ -> ()
  | true :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_root_invalid_outside_initializations remaining_which_are_hidings
        remaining_inits mem root_id
  | false :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_maintains_root_invalid_outside_initializations remaining_which_are_hidings
        remaining_inits mem root_id
  | _, _ -> ()

let rec remove_hidden_initializers_doesnt_add_global
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  (root_id: root_id_t)
  : Lemma (requires (let mem' = remove_hidden_initializers which_are_hidings inits mem in
                     RootGlobal? (mem' root_id)))
          (ensures  RootGlobal? (mem root_id)) =
  match which_are_hidings, inits with
  | [], _ -> ()
  | true :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_doesnt_add_global remaining_which_are_hidings
        remaining_inits mem root_id
  | false :: remaining_which_are_hidings, first_hinit :: remaining_inits ->
      remove_hidden_initializers_doesnt_add_global remaining_which_are_hidings
        remaining_inits mem root_id
  | _, _ -> ()

let rec remove_hidden_initializers_removes_extra_inits
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  (var_id: var_id_t)
  : Lemma (requires   exists_ghost (var_id_in_initializer var_id) linits
                    /\ ~(exists_ghost (var_id_in_initializer var_id) hinits)
                    /\ initializers_match_except_global_variables vs which_are_hidings linits hinits)
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                     RootInvalid? (hmem (RootIdGlobal var_id)))) =
  match which_are_hidings, linits, hinits with
  | [], [], [] -> false_elim ()
  | true :: remaining_which_are_hidings, first_linit :: remaining_linits, _ ->
      if first_linit.var_id = var_id then
        ()
      else
        remove_hidden_initializers_removes_extra_inits vs remaining_which_are_hidings remaining_linits
          hinits lmem var_id
  | false :: remaining_which_are_hidings, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      remove_hidden_initializers_removes_extra_inits vs remaining_which_are_hidings remaining_linits
        remaining_hinits lmem var_id
  | _, _, _ -> false_elim ()

let remove_hidden_initializers_ensures_memory_invalid_outside_initializations
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (lmem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  let hmem = remove_hidden_initializers which_are_hidings linits lmem in
  remove_hidden_initializers_maintains_roots_match which_are_hidings linits lmem;
  introduce forall root_id. root_invalid_outside_initializations hmem hinits initial_tid
                       main_method_id initial_frame_uniq local_variables root_id
  with (
    match hmem root_id with
    | RootGlobal _ ->
        (match root_id with
         | RootIdGlobal var_id ->
             if exists_ghost (var_id_in_initializer var_id) hinits then
               ()
             else (
               remove_hidden_initializers_doesnt_add_global which_are_hidings linits lmem root_id;
               assert (exists_ghost (var_id_in_initializer var_id) linits);
               remove_hidden_initializers_removes_extra_inits vs which_are_hidings linits hinits lmem var_id
             )
         | _ -> ())
    | RootInvalid -> ()
    | _ -> remove_hidden_initializers_doesnt_change_nonglobal which_are_hidings linits lmem root_id
  )

let initialization_ensures_gvar_has_type
  (v: var_id_t)
  (td: object_td_t)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   memory_satisfies_global_initializers mem inits
                    /\ exists_ubool (initializer_matches_variable_and_td v td) inits)
          (ensures  gvar_has_type mem v td) =
  ()

let rec initialization_ensures_all_gvars_have_types_helper
  (vs: list var_id_t)
  (tds: list object_td_t)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   memory_satisfies_global_initializers mem inits
                    /\ every_variable_appears_among_initializers inits vs tds)
          (ensures  all_gvars_have_types mem vs tds) =
  match vs, tds with
  | [], [] -> ()
  | first_v :: remaining_vs, first_td :: remaining_tds ->
      initialization_ensures_gvar_has_type first_v first_td inits mem;
      initialization_ensures_all_gvars_have_types_helper remaining_vs remaining_tds inits mem

let initialization_ensures_all_gvars_have_types
  (vs: list var_id_t)
  (tds: list object_td_t)
  (linits: list initializer_t)
  (lmem: Armada.Memory.t)
  (* see .fst file for spec *) =
  initialization_ensures_all_gvars_have_types_helper vs tds linits lmem
