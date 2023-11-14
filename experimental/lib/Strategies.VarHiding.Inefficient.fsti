module Strategies.VarHiding.Inefficient

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
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Invariant.Armada.AtomicSubstep
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Util.List
open Util.Nth
open Util.Relation

noeq type inefficient_var_hiding_witness_t = {
  lprog: Armada.Program.t;
  hprog: Armada.Program.t;
  vs: list var_id_t;
  tds: list object_td_t;
  inv: invariant_t Armada.State.t;
  which_initializers_are_hidings: list bool;
  lpc_to_hpc: pc_t -> GTot pc_t;
  return_lpcs: list pc_t;
  is_nonyielding_lpc: pc_t -> GTot bool;
  is_nonyielding_hpc: pc_t -> GTot bool;
  corresponding_hactions_info: list (ltoh_correspondence_t vs tds inv);
}

let inefficient_var_hiding_witness_valid
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: inefficient_var_hiding_witness_t)
  : GTot ubool =
    program_inits_match_except_global_variables vw.vs vw.lpc_to_hpc vw.which_initializers_are_hidings vw.lprog vw.hprog
  /\ vw.lpc_to_hpc vw.lprog.main_start_pc = vw.hprog.main_start_pc
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.global_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.lprog.main_stack_initializers
  /\ global_variables_unaddressed_in_initializers vw.vs vw.hprog.main_stack_initializers
  /\ every_variable_appears_among_initializers vw.lprog.global_initializers vw.vs vw.tds
  /\ return_pcs_unique vw.lpc_to_hpc vw.return_lpcs
  /\ each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_lpc latomic_prog.actions
  /\ each_action_list_consistent_with_is_nonyielding_pc vw.is_nonyielding_hpc hatomic_prog.actions
  /\ each_action_list_doesnt_internally_yield latomic_prog.actions
  /\ each_action_list_doesnt_internally_yield hatomic_prog.actions
  /\ each_action_list_ends_atomic_block_if_necessary hatomic_prog.actions
  /\ lists_correspond_ubool
       (lactions_correspond_to_hactions_per_correspondence vw.vs vw.tds vw.inv vw.lpc_to_hpc vw.return_lpcs
          hatomic_prog.actions)
       latomic_prog.actions vw.corresponding_hactions_info

val inefficient_var_hiding_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: inefficient_var_hiding_witness_t)
  : Lemma (requires   inefficient_var_hiding_witness_valid latomic_prog hatomic_prog vw
                    /\ is_armada_substep_invariant latomic_prog vw.inv
                    /\ latomic_prog.init_f == init_program vw.lprog
                    /\ hatomic_prog.init_f == init_program vw.hprog)
          (ensures (spec_refines_spec
                      (semantics_to_spec (make_atomic_semantics armada_semantics) latomic_prog)
                      (semantics_to_spec (make_atomic_semantics armada_semantics) hatomic_prog)
                      refinement_requirement))
