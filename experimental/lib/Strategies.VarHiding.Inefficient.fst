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
open Strategies.Nonyielding
open Strategies.Semantics
open Strategies.Semantics.Armada
open Strategies.VarHiding.Defs
open Strategies.VarHiding.Relation
open Util.List
open Util.Nth
open Util.Relation

let inefficient_var_hiding_witness_valid_implies_refinement
  (latomic_prog: program_t (make_atomic_semantics armada_semantics))
  (hatomic_prog: program_t (make_atomic_semantics armada_semantics))
  (vw: inefficient_var_hiding_witness_t)
  (* see .fsti file for spec *) =
  let vr: var_hiding_relation_t = {
    lprog = vw.lprog;
    hprog = vw.hprog;
    latomic_prog = latomic_prog;
    hatomic_prog = hatomic_prog;
    vs = vw.vs;
    tds = vw.tds;
    inv = vw.inv;
    which_initializers_are_hidings = vw.which_initializers_are_hidings;
    lpc_to_hpc = vw.lpc_to_hpc;
    return_lpcs = vw.return_lpcs;
    is_nonyielding_lpc = vw.is_nonyielding_lpc;
    is_nonyielding_hpc = vw.is_nonyielding_hpc;
    corresponding_hactions_info = vw.corresponding_hactions_info;
    inv_is_substep_invariant_proof = (fun _ -> ());
    atomic_inits_match_regular_inits_proof = (fun _ -> ());
    program_inits_match_except_global_variables_proof = (fun _ -> ());
    initial_pcs_correspond_proof = (fun _ -> ());
    global_variables_unaddressed_in_initializers_proof = (fun _ -> ());
    all_introduced_global_variables_initialized_proof = (fun _ -> ());
    return_pcs_unique_proof = (fun _ -> ());
    lactions_consistent_with_is_nonyielding_pc_proof = (fun _ -> ());
    hactions_consistent_with_is_nonyielding_pc_proof = (fun _ -> ());
    each_laction_doesnt_internally_yield_proof = (fun _ -> ());
    each_haction_doesnt_internally_yield_proof = (fun _ -> ());
    each_haction_ends_atomic_block_if_necessary_proof = (fun _ -> ());
    corresponding_hactions_correspond_proof = (fun _ -> ());
  } in
  var_hiding_relation_implies_refinement vr
