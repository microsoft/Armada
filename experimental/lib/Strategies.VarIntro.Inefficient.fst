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
open Strategies.GlobalVars
open Strategies.GlobalVars.Permanent
open Strategies.GlobalVars.Statement
open Strategies.GlobalVars.VarIntro
open Strategies.Invariant
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarIntro.Defs
open Strategies.VarIntro.Relation
open Util.List
open Util.Nth
open Util.Relation

let var_intro_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: var_intro_witness_t)
  (* see .fsti file for spec *) =
  let vr: var_intro_relation_t = {
    lprog = vw.lprog;
    hprog = vw.hprog;
    latomic_prog = latomic_prog;
    hatomic_prog = hatomic_prog;
    vs = vw.vs;
    tds = vw.tds;
    inv = vw.inv;
    which_initializers_are_intros = vw.which_initializers_are_intros;
    hpc_to_lpc = vw.hpc_to_lpc;
    lpc_to_hpcs = vw.lpc_to_hpcs;
    return_hpcs = vw.return_hpcs;
    is_nonyielding_lpc = vw.is_nonyielding_lpc;
    is_nonyielding_hpc = vw.is_nonyielding_hpc;
    is_breaking_hpc = vw.is_breaking_hpc;
    hpcs = vw.hpcs;
    hpc_info = vw.hpc_info;
    corresponding_hactions_info = vw.corresponding_hactions_info;
    inv_is_substep_invariant_proof = (fun _ -> ());
    atomic_inits_match_regular_inits_proof = (fun _ -> ());
    program_inits_match_except_global_variables_proof = (fun _ -> ());
    hinitializers_with_same_variable_id_match_proof = (fun _ -> ());
    initial_pc_in_pcs_proof = (fun _ -> ());
    initial_pc_breaking_proof = (fun _ -> ());
    initial_pcs_correspond_proof = (fun _ -> ());
    global_variables_unaddressed_in_initializers_proof = (fun _ -> ());
    all_introduced_global_variables_initialized_proof = (fun _ -> ());
    hpcs_complete_proof = (fun _ -> ());
    lpc_to_hpcs_consistent_with_hpc_to_lpc_proof = (fun _ -> ());
    return_pcs_unique_proof = (fun _ -> ());
    lactions_consistent_with_is_nonyielding_pc_proof = (fun _ -> ());
    hactions_consistent_with_is_nonyielding_pc_proof = (fun _ -> ());
    hactions_end_in_breaking_pc_proof = (fun _ -> ());
    each_laction_doesnt_internally_yield_proof = (fun _ -> ());
    each_haction_doesnt_internally_yield_proof = (fun _ -> ());
    introduced_atomic_actions_make_progress_proof = (fun _ -> ());
    corresponding_hactions_correspond_proof = (fun _ -> ());
  } in
  var_intro_relation_implies_refinement vr
