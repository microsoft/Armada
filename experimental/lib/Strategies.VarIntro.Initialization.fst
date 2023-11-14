module Strategies.VarIntro.Initialization

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
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.Types
open Strategies.GlobalVars.Unaddressed
open Strategies.GlobalVars.Util
open Strategies.GlobalVars.VarIntro
open Strategies.Lift.Generic
open Strategies.Invariant
open Strategies.VarIntro.Defs
open Util.List

let apply_introduced_initializer_ensures_satisfies_global_initializer
  (init: initializer_t)
  (existing_inits: list initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires    memory_satisfies_global_initializers mem existing_inits
                    /\ (forall existing_init. contains_ubool existing_init existing_inits ==>
                         initializers_match_if_same_variable_id existing_init init)
                    /\ initializer_ok_for_var_intro init)
          (ensures  (let mem' = apply_introduced_initializer init mem in
                       memory_satisfies_global_initializer mem' init
                     /\ memory_satisfies_global_initializers mem' existing_inits)) =
  ()

let apply_introduced_initializer_makes_memories_match
  (vs: list var_id_t)
  (init: initializer_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   list_contains init.var_id vs
                    /\ initializer_ok_for_var_intro init)
          (ensures  memories_match_except_global_variables vs mem (apply_introduced_initializer init mem)) =
  ()

let initializers_with_same_variable_id_match_equivalent_to_forall
  (inits: list initializer_t)
  (* see .fsti file for spec *) =
  ()

let rec apply_introduced_initializers_ensures_satisfies_global_initializers_helper
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (all_linits: list initializer_t)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_intros linits hinits
                    /\ initializers_with_same_variable_id_match hinits
                    /\ memory_satisfies_global_initializers lmem all_linits
                    /\ (forall init. contains_ubool init linits ==> contains_ubool init all_linits)
                    /\ (forall linit hinit. contains_ubool linit all_linits /\ contains_ubool hinit hinits ==>
                                      initializers_match_if_same_variable_id linit hinit))
          (ensures  (let hmem = apply_introduced_initializers which_are_intros hinits lmem in
                       memory_satisfies_global_initializers hmem hinits
                     /\ memory_satisfies_global_initializers hmem all_linits
                     /\ memories_match_except_global_variables vs lmem hmem)) =
  let hmem = apply_introduced_initializers which_are_intros hinits lmem in
  match which_are_intros, linits, hinits with
  | [], _, _ -> ()
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      let mem' = apply_introduced_initializers remaining_which_are_intros remaining_hinits lmem in
      apply_introduced_initializers_ensures_satisfies_global_initializers_helper vs remaining_which_are_intros
        all_linits linits remaining_hinits lmem;
      apply_introduced_initializer_ensures_satisfies_global_initializer first_hinit remaining_hinits mem';
      apply_introduced_initializer_ensures_satisfies_global_initializer first_hinit all_linits mem';
      memories_match_except_global_variables_transitive vs lmem mem' hmem
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      apply_introduced_initializers_ensures_satisfies_global_initializers_helper vs remaining_which_are_intros
        all_linits remaining_linits remaining_hinits lmem
  | _, _, _ -> ()

let rec initializers_match_except_global_variables_implies_subset_helper
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (linit: initializer_t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_intros linits hinits
                    /\ contains_ubool linit linits)
          (ensures  contains_ubool linit hinits) =
  match which_are_intros, linits, hinits with
  | [], _, _ -> ()
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      initializers_match_except_global_variables_implies_subset_helper vs remaining_which_are_intros linits
        remaining_hinits linit
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      if eqb first_linit linit then
        ()
      else
        initializers_match_except_global_variables_implies_subset_helper vs remaining_which_are_intros
          remaining_linits remaining_hinits linit
  | _, _, _ -> ()

let initializers_match_except_global_variables_implies_subset
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  : Lemma (requires initializers_match_except_global_variables vs which_are_intros linits hinits)
          (ensures  forall linit. contains_ubool linit linits ==> contains_ubool linit hinits) =
  introduce forall linit. contains_ubool linit linits ==> contains_ubool linit hinits
  with introduce _ ==> _
  with _. initializers_match_except_global_variables_implies_subset_helper vs which_are_intros linits hinits linit

let apply_introduced_initializers_ensures_satisfies_global_initializers
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  initializers_match_except_global_variables_implies_subset vs which_are_intros linits hinits;
  apply_introduced_initializers_ensures_satisfies_global_initializers_helper vs which_are_intros linits
    linits hinits lmem

let rec apply_introduced_initializers_maintains_nonglobal_root
  (which_are_intros: list bool)
  (inits: list initializer_t)
  (lmem: Armada.Memory.t)
  (root_id: root_id_t)
  : Lemma (requires not (RootIdGlobal? root_id))
          (ensures  (let hmem = apply_introduced_initializers which_are_intros inits lmem in
                     hmem root_id == lmem root_id)) =
  match which_are_intros, inits with
  | [], _ -> ()
  | true :: remaining_which_are_intros, first_hinit :: remaining_inits ->
      apply_introduced_initializers_maintains_nonglobal_root remaining_which_are_intros remaining_inits lmem root_id
  | false :: remaining_which_are_intros, first_hinit :: remaining_inits ->
      apply_introduced_initializers_maintains_nonglobal_root remaining_which_are_intros remaining_inits lmem root_id
  | _, _ -> ()

let rec apply_introduced_initializers_ensures_satisfies_main_stack_initializers
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (hinits: list initializer_t)
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
      apply_introduced_initializers_maintains_nonglobal_root which_are_intros hinits lmem root_id;
      apply_introduced_initializers_ensures_satisfies_main_stack_initializers vs which_are_intros hinits
        initial_tid main_method_id initial_frame_uniq remaining_var_ids remaining_initializers lmem
  | _ -> ()

let rec matching_linits_are_present
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : GTot bool =
  match which_are_intros, linits, hinits with
  | [], [], [] -> true
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      matching_linits_are_present remaining_which_are_intros linits remaining_hinits lmem
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      (match lmem (RootIdGlobal first_linit.var_id) with
       | RootGlobal _ -> exists_ghost (var_id_in_initializer first_linit.var_id) linits
       | _ -> false)
  | _, _, _ -> false

let rec initializers_match_except_global_variables_implies_matching_linits_are_present
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (lmem: Armada.Memory.t)
  : Lemma (requires   memory_satisfies_global_initializers lmem linits
                    /\ initializers_match_except_global_variables vs which_are_intros linits hinits)
          (ensures  matching_linits_are_present which_are_intros linits hinits lmem) =
  match which_are_intros, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      initializers_match_except_global_variables_implies_matching_linits_are_present vs remaining_which_are_intros
        linits remaining_hinits lmem
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      initializers_match_except_global_variables_implies_matching_linits_are_present vs remaining_which_are_intros
        remaining_linits remaining_hinits lmem
  | _, _, _ -> ()

let apply_introduced_initializer_updates_memory_invalid_outside_initializations
  (old_inits: list initializer_t)
  (new_init: initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   memory_invalid_outside_initializations mem old_inits initial_tid main_method_id
                        initial_frame_uniq local_variables
                    /\ roots_match mem)
          (ensures  (let mem' = apply_introduced_initializer new_init mem in
                     let combined_inits = list_append [new_init] old_inits in
                       roots_match mem'
                     /\ memory_invalid_outside_initializations mem combined_inits initial_tid main_method_id
                         initial_frame_uniq local_variables)) =
  let mem' = apply_introduced_initializer new_init mem in
  let combined_inits = list_append [new_init] old_inits in
  introduce forall root_id. root_invalid_outside_initializations mem' combined_inits initial_tid
                         main_method_id initial_frame_uniq local_variables root_id
  with (
    assert (root_invalid_outside_initializations mem old_inits initial_tid main_method_id initial_frame_uniq
              local_variables root_id);
    match root_id with
    | RootIdGlobal root_var_id ->
        let f = var_id_in_initializer root_var_id in
        if root_var_id = new_init.var_id then (
          introduce exists init. f init /\ contains_ubool init combined_inits
          with new_init and contains_ubool_append new_init [new_init] old_inits
        )
        else (
          match mem root_id with
          | RootGlobal _ ->
              assert (mem' root_id == mem root_id);
              assert (exists_ghost f old_inits);
              eliminate exists init. f init /\ contains_ubool init old_inits
              returns exists init. f init /\ contains_ubool init combined_inits
              with _. (
                introduce exists init. f init /\ contains_ubool init combined_inits
                with init and contains_ubool_append init [new_init] old_inits
              )
          | _ -> ()
        )
    | _ -> ()
  )

let expand_memory_invalid_outside_initializations
  (old_inits: list initializer_t)
  (new_inits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   memory_invalid_outside_initializations mem old_inits initial_tid main_method_id
                        initial_frame_uniq local_variables
                    /\ roots_match mem)
          (ensures  memory_invalid_outside_initializations mem (list_append new_inits old_inits)
                      initial_tid main_method_id initial_frame_uniq local_variables) =
  let combined_inits = list_append new_inits old_inits in
  introduce forall root_id. root_invalid_outside_initializations mem combined_inits initial_tid
                         main_method_id initial_frame_uniq local_variables root_id
  with (
    assert (root_invalid_outside_initializations mem old_inits initial_tid main_method_id initial_frame_uniq
              local_variables root_id);
    match root_id with
    | RootIdGlobal root_var_id ->
        let f = var_id_in_initializer root_var_id in
        (match mem root_id with
         | RootGlobal _ ->
             assert (exists_ghost f old_inits);
             eliminate exists init. f init /\ contains_ubool init old_inits
             returns exists init. f init /\ contains_ubool init combined_inits
             with _. (
               introduce exists init. f init /\ contains_ubool init combined_inits
               with init and contains_ubool_append init new_inits old_inits
             )
         | _ -> ())
    | _ -> ()
  )

#push-options "--z3rlimit 10"

let rec apply_introduced_initializers_updates_memory_invalid_outside_initializations
  (which_are_intros: list bool)
  (old_inits: list initializer_t)
  (new_inits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (mem: Armada.Memory.t)
  : Lemma (requires   memory_invalid_outside_initializations mem old_inits initial_tid main_method_id
                        initial_frame_uniq local_variables
                    /\ roots_match mem)
          (ensures  (let mem' = apply_introduced_initializers which_are_intros new_inits mem in
                       memory_invalid_outside_initializations mem' (list_append new_inits old_inits)
                         initial_tid main_method_id initial_frame_uniq local_variables
                     /\ roots_match mem')) =
  match which_are_intros, new_inits with
  | [], [] -> ()
  | true :: remaining_which_are_intros, new_init :: remaining_inits ->
      apply_introduced_initializers_updates_memory_invalid_outside_initializations remaining_which_are_intros
        old_inits remaining_inits initial_tid main_method_id initial_frame_uniq local_variables mem;
      let mem' = apply_introduced_initializers remaining_which_are_intros remaining_inits mem in
      assert (memory_invalid_outside_initializations mem' (list_append remaining_inits old_inits)
                initial_tid main_method_id initial_frame_uniq local_variables);
      apply_introduced_initializer_updates_memory_invalid_outside_initializations
        (list_append remaining_inits old_inits) new_init initial_tid main_method_id initial_frame_uniq
        local_variables mem';
      assert (list_append [new_init] (list_append remaining_inits old_inits) ==
                list_append new_inits old_inits)
  | false :: remaining_which_are_intros, new_init :: remaining_inits ->
      apply_introduced_initializers_updates_memory_invalid_outside_initializations remaining_which_are_intros
        old_inits remaining_inits initial_tid main_method_id initial_frame_uniq local_variables mem;
      let mem' = apply_introduced_initializers remaining_which_are_intros remaining_inits mem in
      expand_memory_invalid_outside_initializations (list_append remaining_inits old_inits)
        [new_init] initial_tid main_method_id initial_frame_uniq local_variables mem';
      assert (list_append [new_init] (list_append remaining_inits old_inits) ==
                list_append new_inits old_inits)
  | _, _ ->
      expand_memory_invalid_outside_initializations old_inits new_inits initial_tid main_method_id
        initial_frame_uniq local_variables mem

#pop-options

let if_in_append_but_not_first_of_either_then_in_append_tails
  (#a: Type)
  (x: a)
  (l1: list a)
  (l2: list a)
  : Lemma (requires   contains_ubool x (list_append l1 l2)
                    /\ (match l1, l2 with
                       | hd1 :: tl1, hd2 :: tl2 -> neqb x hd1 /\ neqb x hd2
                       | _, _ -> False))
          (ensures  (match l1, l2 with
                     | hd1 :: tl1, hd2 :: tl2 -> contains_ubool x (list_append tl1 tl2)
                     | _ -> False)) =
  match l1, l2 with
  | hd1 :: tl1, hd2 :: tl2 ->
      contains_ubool_append x l1 l2;
      contains_ubool_append x tl1 tl2

let rec hinits_subset_of_combined_inits
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (init: initializer_t)
  : Lemma (requires   initializers_match_except_global_variables vs which_are_intros linits hinits
                    /\ contains_ubool init (list_append hinits linits))
          (ensures  contains_ubool init hinits) =
  match which_are_intros, linits, hinits with
  | [], [], [] -> ()
  | true :: remaining_which_are_intros, _, first_hinit :: remaining_hinits ->
      if eqb first_hinit init then
        ()
      else
        hinits_subset_of_combined_inits vs remaining_which_are_intros linits remaining_hinits init
  | false :: remaining_which_are_intros, first_linit :: remaining_linits, first_hinit :: remaining_hinits ->
      if eqb first_hinit init then
        ()
      else (
        if_in_append_but_not_first_of_either_then_in_append_tails init hinits linits;
        hinits_subset_of_combined_inits vs remaining_which_are_intros remaining_linits remaining_hinits init
      )
  | _, _, _ -> ()

let apply_introduced_initializers_ensures_memory_invalid_outside_initializations
  (vs: list var_id_t)
  (which_are_intros: list bool)
  (linits: list initializer_t)
  (hinits: list initializer_t)
  (initial_tid: tid_t)
  (main_method_id: method_id_t)
  (initial_frame_uniq: root_id_uniquifier_t)
  (local_variables: list var_id_t)
  (lmem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  let hmem = apply_introduced_initializers which_are_intros hinits lmem in
  apply_introduced_initializers_updates_memory_invalid_outside_initializations which_are_intros linits hinits
    initial_tid main_method_id initial_frame_uniq local_variables lmem;
  introduce forall root_id. root_invalid_outside_initializations hmem hinits initial_tid
                         main_method_id initial_frame_uniq local_variables root_id
  with (
    let combined_inits = list_append hinits linits in
    assert (root_invalid_outside_initializations hmem combined_inits initial_tid main_method_id
              initial_frame_uniq local_variables root_id);
    match hmem root_id with
    | RootGlobal _ ->
        (match root_id with
         | RootIdGlobal var_id ->
             let f = var_id_in_initializer var_id in
             let init = exists_ghost_to_witness f combined_inits in
             hinits_subset_of_combined_inits vs which_are_intros linits hinits init;
             assert (contains_ubool init hinits);
             exists_ghost_equivalent_to_exists f hinits;
             assert (exists_ghost f hinits)
         | _ -> ())
    | _ -> ()
  )

let apply_introduced_initializer_ensures_gvar_has_type
  (init: initializer_t)
  (mem: Armada.Memory.t)
  (* see .fsti file for spec *) =
  ()
