module Strategies.VarIntro.Initialization

open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Type
open Spec.List
open Strategies.ArmadaInvariant.RootsMatch
open Strategies.GlobalVars
open Strategies.GlobalVars.Types
open Strategies.VarIntro.Defs

let apply_introduced_initializer
  (init: initializer_t)
  (mem: Armada.Memory.t)
  : GTot Armada.Memory.t =
  match init.iv with
  | InitializerSpecific value ->
      (match value with
       | ObjectValuePrimitive _
       | ObjectValueAbstract _ _ ->
           let root_id = RootIdGlobal init.var_id in
           let storage = object_value_to_storage value in
           let root = RootGlobal storage in
           Spec.Map.upd mem root_id root
       | _ -> mem)
  | _ -> mem

let rec apply_introduced_initializers
  (which_are_intros: list bool)
  (inits: list initializer_t)
  (mem: Armada.Memory.t)
  : GTot Armada.Memory.t =
  match which_are_intros, inits with
  | [], _ -> mem
  | true :: remaining_which_are_intros, first_hinit :: remaining_inits ->
      let mem' = apply_introduced_initializers remaining_which_are_intros remaining_inits mem in
      apply_introduced_initializer first_hinit mem'
  | false :: remaining_which_are_intros, first_hinit :: remaining_inits ->
      apply_introduced_initializers remaining_which_are_intros remaining_inits mem
  | _, _ -> mem

val initializers_with_same_variable_id_match_equivalent_to_forall
  (inits: list initializer_t)
  : Lemma (ensures initializers_with_same_variable_id_match inits <==>
                   (forall init1 init2. contains_ubool init1 inits /\ contains_ubool init2 inits ==>
                      initializers_match_if_same_variable_id init1 init2))

val apply_introduced_initializers_ensures_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires    initializers_match_except_global_variables vs which_are_intros linits hinits
                    /\ initializers_with_same_variable_id_match hinits
                    /\ memory_satisfies_global_initializers lmem linits)
          (ensures  (let hmem = apply_introduced_initializers which_are_intros hinits lmem in
                       memory_satisfies_global_initializers hmem hinits
                     /\ memories_match_except_global_variables vs lmem hmem))

val apply_introduced_initializers_ensures_satisfies_main_stack_initializers
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (hinits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (main_stack_initializers: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires memory_satisfies_main_stack_initializers lmem initial_tid main_method_id initial_frame_uniq
                      local_variables main_stack_initializers)
          (ensures  (let hmem = apply_introduced_initializers which_are_intros hinits lmem in
                     memory_satisfies_main_stack_initializers hmem initial_tid main_method_id initial_frame_uniq
                        local_variables main_stack_initializers))

val apply_introduced_initializers_ensures_memory_invalid_outside_initializations
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   memory_invalid_outside_initializations lmem linits initial_tid main_method_id
                        initial_frame_uniq local_variables
                    /\ initializers_match_except_global_variables vs which_are_intros linits hinits
                    /\ roots_match lmem)
          (ensures  (let hmem = apply_introduced_initializers which_are_intros hinits lmem in
                     memory_invalid_outside_initializations hmem hinits initial_tid main_method_id
                       initial_frame_uniq local_variables))

val apply_introduced_initializer_ensures_gvar_has_type
  (init: initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires initializer_ok_for_var_intro init)
          (ensures (let mem' = apply_introduced_initializer init mem in
                      gvar_has_type mem' init.var_id (initializer_value_to_td init.iv)
                    /\ (forall v td. gvar_has_type mem v td /\ v <> init.var_id ==> gvar_has_type mem' v td)))
