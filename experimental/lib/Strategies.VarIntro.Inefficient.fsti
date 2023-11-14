module Strategies.VarIntro.Inefficient

open Armada.Action
open Armada.Base
open Armada.Init
open Armada.Memory
open Armada.Program
open Armada.State
open Armada.Statement
open Armada.Threads
open Armada.Transition
open Armada.Type
open Spec.Behavior
open Spec.List
open Spec.Logic
open Spec.Ubool
open Strategies.ArmadaStatement.ThreadState
open Strategies.Atomic
open Strategies.Breaking
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Util.List
open Util.Nth
open Util.Relation

noeq type var_intro_witness_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_intros: list bool;
  hpc_to_lpc: pc_t -> GTot pc_t;
  lpc_to_hpcs: pc_t -> GTot (list pc_t);
  return_hpcs: list pc_t;
  is_nonyielding_lpc: pc_t -> GTot bool;
  is_nonyielding_hpc: pc_t -> GTot bool;
  is_breaking_hpc: pc_t -> GTot bool;
  hpcs: list pc_t;
  hpc_info: pc_t -> GTot (hpc_info_t vs tds inv);
  corresponding_hactions_info: list (ltoh_correspondence_t vs tds inv);
}

let var_intro_witness_valid
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: var_intro_witness_t)
  : GTot ubool =
    program_inits_match_except_global_variables vw.vs vw.hpc_to_lpc vw.which_initializers_are_intros
      vw.lprog vw.hprog
  /\ vw.is_breaking_hpc vw.hprog.main_start_pc
  /\ initializers_with_same_variable_id_match vw.hprog.global_initializers
  /\ list_contains vw.hprog.main_start_pc vw.hpcs
  /\ vw.hpc_to_lpc vw.hprog.main_start_pc = vw.lprog.main_start_pc
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers
  /\ every_variable_appears_among_initializers vw.hprog.global_initializers vw.vs vw.tds
  /\ for_all_ghost (for_all_ghost (pcs_contain_new_pcs_of_action vw.hpcs)) hatomic_prog.actions
  /\ every_hpc_appears_among_lpc_to_hpcs vw.lpc_to_hpcs vw.hpc_to_lpc vw.hpcs
  /\ return_pcs_unique vw.hpc_to_lpc vw.return_hpcs
  /\ each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc latomic_prog.actions
  /\ each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc hatomic_prog.actions
  /\ each_action_list_maintains_all_threads_breaking vw.is_breaking_hpc hatomic_prog.actions
  /\ each_action_list_doesnt_internally_yield latomic_prog.actions
  /\ each_action_list_doesnt_internally_yield hatomic_prog.actions
  /\ for_all_ubool (introduced_atomic_action_makes_progress vw.vs vw.tds vw.inv hatomic_prog.actions
                      vw.hpc_info vw.hpc_to_lpc vw.is_nonyielding_lpc) vw.hpcs
  /\ lists_correspond_ubool
       (lactions_correspond_to_hactions_per_correspondence vw.vs vw.tds vw.inv
          vw.hpc_to_lpc vw.lpc_to_hpcs vw.return_hpcs vw.is_breaking_hpc vw.hpc_info hatomic_prog.actions)
      latomic_prog.actions vw.corresponding_hactions_info

val var_intro_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: var_intro_witness_t)
  : Lemma (requires   var_intro_witness_valid latomic_prog hatomic_prog vw
                    /\ is_armada_substep_invariant hatomic_prog vw.inv
                    /\ latomic_prog.init_f == init_program vw.lprog
                    /\ hatomic_prog.init_f == init_program vw.hprog)
          (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hatomic_prog)
                      refinement_requirement))
