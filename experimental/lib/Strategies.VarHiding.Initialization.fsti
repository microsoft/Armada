module Strategies.VarHiding.Initialization

open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Type
open Spec.List
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.GlobalVars
open Strategies.GlobalVars.Types
open Strategies.VarHiding.Defs

let remove_hidden_initializer
  (init: initializer_t)
  (mem: Armada.Memory.t)
  : GTot Armada.Memory.t =
  let root_id = RootIdGlobal init.var_id in
  Spec.Map.upd mem root_id RootInvalid

let rec remove_hidden_initializers
  (which_are_hidings: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  : GTot Armada.Memory.t =
  match which_are_hidings, inits with
  | [], _ -> mem
  | true :: remaining_which_are_hidings, first_init :: remaining_inits ->
      let mem' = remove_hidden_initializers remaining_which_are_hidings remaining_inits mem in
      remove_hidden_initializer first_init mem'
  | false :: remaining_which_are_hidings, first_init :: remaining_inits ->
      remove_hidden_initializers remaining_which_are_hidings remaining_inits mem
  | _, _ -> mem

val remove_hidden_initializers_ensures_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_hidings linits hinits
                    /\ memory_satisfies_global_initializers lmem linits)
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                       memory_satisfies_global_initializers hmem hinits
                     /\ memories_match_except_global_variables vs lmem hmem))

val remove_hidden_initializers_ensures_satisfies_main_stack_initializers
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (main_stack_initializers: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires memory_satisfies_main_stack_initializers lmem initial_tid main_method_id initial_frame_uniq
                      local_variables main_stack_initializers)
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                     memory_satisfies_main_stack_initializers hmem initial_tid main_method_id initial_frame_uniq
                       local_variables main_stack_initializers))

val remove_hidden_initializers_ensures_memory_invalid_outside_initializations
  (vs: list var_id_t)
  (which_are_hidings: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   memory_invalid_outside_initializations lmem linits initial_tid main_method_id
                        initial_frame_uniq local_variables
                    /\ initializers_match_except_global_variables vs which_are_hidings linits hinits
                    /\ roots_match lmem)
          (ensures  (let hmem = remove_hidden_initializers which_are_hidings linits lmem in
                     memory_invalid_outside_initializations hmem hinits initial_tid main_method_id
                       initial_frame_uniq local_variables))

val initialization_ensures_all_gvars_have_types
  (vs: list var_id_t)
  (tds: list object_td_t)
  (linits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   memory_satisfies_global_initializers lmem linits
                    /\ every_variable_appears_among_initializers linits vs tds)
          (ensures  all_gvars_have_types lmem vs tds)
