module Strategies.ArmadaStatement

open Armada.Action
open Armada.Base
open Armada.Computation
open Armada.Expression
open Armada.Init
open Armada.Memory
open Armada.Pointer
open Armada.State
open Armada.Statement
open Armada.Thread
open Armada.Transition
open Armada.Type
open FStar.Sequence.Base
open Spec.List
open Spec.Logic
open Spec.Ubool
open Util.List

let actor_state_predicate = tid_t -> Armada.State.t -> Armada.State.t -> Type0

let actor_state_predicate_transitive (pred: actor_state_predicate) =
  forall actor x1 x2 x3. (pred actor x1 x2 /\ pred actor x2 x3) ==> (pred actor x1 x3)

let actor_state_predicate_reflexive (pred: actor_state_predicate) =
  forall actor x. pred actor x x

let actor_memory_predicate = tid_t -> Armada.Memory.t -> Armada.Memory.t -> Type0

let actor_memory_predicate_transitive (pred: actor_memory_predicate) =
  forall actor x1 x2 x3. (pred actor x1 x2 /\ pred actor x2 x3) ==> (pred actor x1 x3)

let actor_memory_predicate_reflexive (pred: actor_memory_predicate) =
  forall actor x. pred actor x x

let make_push_stack_variables_lemma_conditional
  (pred: actor_state_predicate)
  (initializer_cond: (initializer_t -> GTot bool){
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
          initializer_cond initializer ==>
          (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor writer_pc writer_expression_number method_id frame_uniq initializers s.
         {:pattern push_stack_variables actor writer_pc writer_expression_number method_id
                     frame_uniq initializers s}
         for_all_ghost initializer_cond initializers ==>
         (match push_stack_variables actor writer_pc writer_expression_number method_id
                  frame_uniq initializers s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)) =
  fun _ ->
  let rec internal_lem actor writer_pc writer_expression_number method_id frame_uniq initializers s
    : Lemma (requires for_all_ghost initializer_cond initializers)
            (ensures (match push_stack_variables actor writer_pc writer_expression_number method_id
                              frame_uniq initializers s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases initializers)
            [SMTPat (push_stack_variables actor writer_pc writer_expression_number method_id
                       frame_uniq initializers s)] =
    match initializers with
    | [] -> ()
    | first_initializer :: remaining_initializers ->
        (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                 first_initializer s with
         | ComputationProduces s' ->
             (match push_stack_variables actor writer_pc (writer_expression_number + 1) method_id
                      frame_uniq remaining_initializers s' with
              | ComputationProduces s'' ->
                  internal_lem actor writer_pc (writer_expression_number + 1) method_id frame_uniq
                    remaining_initializers s'
              | _ -> ())
         | _ -> ())
  in
  ()

let make_push_stack_variables_lemma
  (pred: actor_state_predicate{
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
           match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor writer_pc writer_expression_number method_id frame_uniq initializers s.
         {:pattern push_stack_variables actor writer_pc writer_expression_number method_id
                     frame_uniq initializers s}
         match push_stack_variables actor writer_pc writer_expression_number method_id
                 frame_uniq initializers s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  make_push_stack_variables_lemma_conditional pred (fun _ -> true)

let make_push_stack_variables_premium_conditional
  (pred: actor_state_predicate)
  (initializer_cond: initializer_t -> GTot bool{
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
          initializer_cond initializer ==>
          (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ -> frame_uniq: _ ->
          initializers: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == push_stack_variables actor writer_pc writer_expression_number method_id
                              frame_uniq initializers s
                /\ (for_all_ghost initializer_cond initializers ==>
                   (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_push_stack_variables_lemma_conditional pred initializer_cond ();
  let f actor writer_pc writer_expression_number method_id frame_uniq initializers s
    : GTot (result: conditional_computation_t Armada.State.t{
                result == push_stack_variables actor writer_pc writer_expression_number method_id
                            frame_uniq initializers s
              /\ (for_all_ghost initializer_cond initializers ==>
                 (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))}) =
    push_stack_variables actor writer_pc writer_expression_number method_id frame_uniq initializers
      s
  in
  f

let make_push_stack_variables_premium
  (pred: actor_state_predicate{
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializers s.
          match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                  initializers s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: tid_t -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ ->
          frame_uniq: _ -> initializers: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == push_stack_variables actor writer_pc writer_expression_number method_id
                              frame_uniq initializers s
                /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  make_push_stack_variables_premium_conditional pred (fun _ -> true)

let make_push_stack_variables_premium_conditional_negative
  (pred: actor_state_predicate)
  (initializer_cond: (initializer_t -> GTot bool){
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
          (initializer_cond initializer \/
           (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                    initializer s with
            | ComputationProduces s' -> pred actor s s'
            | _ -> True)))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: tid_t -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ ->
          frame_uniq: _ -> initializers: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == push_stack_variables actor writer_pc writer_expression_number method_id
                              frame_uniq initializers s
                /\ (exists_ghost initializer_cond initializers \/
                   (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_push_stack_variables_premium_conditional pred
    (fun initializer -> not (initializer_cond initializer))

let make_push_stack_parameters_lemma_conditional
  (pred: actor_state_predicate)
  (parameter_cond: object_value_t -> GTot bool{
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
            InitializerSpecific? initializer.iv
          /\ parameter_cond (InitializerSpecific?.value initializer.iv) ==>
          (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s.
         {:pattern push_stack_parameters actor writer_pc writer_expression_number
                     method_id frame_uniq var_ids parameters s}
         for_all_ghost parameter_cond parameters ==>
         (match push_stack_parameters actor writer_pc writer_expression_number
                  method_id frame_uniq var_ids parameters s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)) =
  fun _ ->
  let rec internal_lem actor writer_pc writer_expression_number method_id frame_uniq var_ids
                         parameters s
    : Lemma (requires for_all_ghost parameter_cond parameters)
            (ensures (match push_stack_parameters actor writer_pc writer_expression_number
                              method_id frame_uniq var_ids parameters s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases parameters)
            [SMTPat (push_stack_parameters actor writer_pc writer_expression_number
                       method_id frame_uniq var_ids parameters s)] =
    match parameters, var_ids with
    | [], [] -> ()
    | first_parameter :: remaining_parameters, first_var_id :: remaining_var_ids ->
        let first_initializer = { var_id = first_var_id; iv = InitializerSpecific first_parameter;
                                  weakly_consistent = false } in
        (match push_stack_variable actor writer_pc writer_expression_number method_id
                             frame_uniq first_initializer s with
         | ComputationProduces s' ->
             (match push_stack_parameters actor writer_pc (writer_expression_number + 1) method_id
                      frame_uniq remaining_var_ids remaining_parameters s' with
              | ComputationProduces s'' ->
                  internal_lem actor writer_pc (writer_expression_number + 1) method_id frame_uniq
                    remaining_var_ids remaining_parameters s'
              | _ -> ())
         | _ -> ())
    | _ -> ()
  in
  ()

let make_pop_stack_variables_lemma
  (pred: actor_memory_predicate{
       (forall actor method_id frame_uniq var_id mem.
          (match pop_stack_variable actor method_id frame_uniq var_id mem with
           | ComputationProduces mem' -> pred actor mem mem'
           | _ -> True))
     /\ actor_memory_predicate_reflexive pred
     /\ actor_memory_predicate_transitive pred})
  : unit -> Lemma
      (forall actor method_id frame_uniq var_ids mem.
         {:pattern pop_stack_variables actor method_id frame_uniq var_ids mem}
         match pop_stack_variables actor method_id frame_uniq var_ids mem with
         | ComputationProduces mem' -> pred actor mem mem'
         | _ -> True) =
  fun _ ->
  let rec internal_lem actor method_id frame_uniq var_ids mem
    : Lemma (ensures (match pop_stack_variables actor method_id frame_uniq var_ids mem with
                      | ComputationProduces mem' -> pred actor mem mem'
                      | _ -> True))
            (decreases var_ids)
            [SMTPat (pop_stack_variables actor method_id frame_uniq var_ids mem)] =
    match pop_stack_variables actor method_id frame_uniq var_ids mem with
    | ComputationProduces mem' ->
        (match var_ids with
         | [] -> ()
         | first_var_id :: remaining_var_ids ->
             (match pop_stack_variable actor method_id frame_uniq first_var_id mem with
              | ComputationProduces mem2 ->
                  internal_lem actor method_id frame_uniq remaining_var_ids mem2
              | _ -> ()))
    | _ -> ()
  in
  ()

let make_pop_stack_variables_premium
  (pred: actor_memory_predicate{
       (forall actor method_id frame_uniq var_id mem.
          (match pop_stack_variable actor method_id frame_uniq var_id mem with
           | ComputationProduces mem' -> pred actor mem mem'
           | _ -> True))
     /\ actor_memory_predicate_reflexive pred
     /\ actor_memory_predicate_transitive pred})
  : GTot (actor: _ -> method_id: _ -> frame_uniq: _ -> var_ids: _ -> mem: _ ->
          GTot (result: conditional_computation_t Armada.Memory.t{
                  result == pop_stack_variables actor method_id frame_uniq var_ids mem
                /\ (match result with | ComputationProduces mem' -> pred actor mem mem' | _ -> True)})) =
  let f actor method_id frame_uniq var_ids mem
    : GTot (result: conditional_computation_t Armada.Memory.t{
              result == pop_stack_variables actor method_id frame_uniq var_ids mem
            /\ (match result with | ComputationProduces mem' -> pred actor mem mem' | _ -> True)}) =
    make_pop_stack_variables_lemma pred ();
    pop_stack_variables actor method_id frame_uniq var_ids mem
  in
  f

let make_push_stack_parameters_lemma
  (pred: actor_state_predicate{
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
          match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                  initializer s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma (
      forall actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s.
         {:pattern push_stack_parameters actor writer_pc writer_expression_number
                     method_id frame_uniq var_ids parameters s}
         match push_stack_parameters actor writer_pc writer_expression_number
                 method_id frame_uniq var_ids parameters s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  make_push_stack_parameters_lemma_conditional pred (fun _ -> true)

let make_push_stack_parameters_premium_conditional
  (pred: actor_state_predicate)
  (parameter_cond: (object_value_t -> GTot bool){
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
            InitializerSpecific? initializer.iv
          /\ parameter_cond (InitializerSpecific?.value initializer.iv) ==>
          (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ -> frame_uniq: _ ->
          var_ids: _ -> parameters: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                   result == push_stack_parameters actor writer_pc writer_expression_number
                               method_id frame_uniq var_ids parameters s
                 /\ (for_all_ghost parameter_cond parameters ==>
                    (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_push_stack_parameters_lemma_conditional pred parameter_cond ();
  let f actor writer_pc writer_expression_number method_id frame_uniq var_ids parameters s
    : GTot (result: conditional_computation_t Armada.State.t{
              result == push_stack_parameters actor writer_pc writer_expression_number method_id
                          frame_uniq var_ids parameters s
              /\ (for_all_ghost parameter_cond parameters ==>
                 (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))}) =
    push_stack_parameters actor writer_pc writer_expression_number method_id frame_uniq var_ids
      parameters s
  in
  f

let make_push_stack_parameters_premium
  (pred: actor_state_predicate{
       (forall actor writer_pc writer_expression_number method_id frame_uniq var_ids s.
          match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                  var_ids s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ -> frame_uniq: _ ->
          var_ids: _ -> parameters: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                   result == push_stack_parameters actor writer_pc writer_expression_number
                               method_id frame_uniq var_ids parameters s
                 /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  make_push_stack_parameters_premium_conditional pred (fun _ -> true)

let make_push_stack_parameters_premium_conditional_negative
  (pred: actor_state_predicate)
  (parameter_cond: (object_value_t -> GTot bool){
       (forall actor writer_pc writer_expression_number method_id frame_uniq initializer s.
          (InitializerSpecific? initializer.iv /\
           parameter_cond (InitializerSpecific?.value initializer.iv)) \/
          (match push_stack_variable actor writer_pc writer_expression_number method_id frame_uniq
                   initializer s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> method_id: _ -> frame_uniq: _ ->
          var_ids: _ -> parameters: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                   result == push_stack_parameters actor writer_pc writer_expression_number
                               method_id frame_uniq var_ids parameters s
                 /\ (exists_ghost parameter_cond parameters \/
                     (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_push_stack_parameters_premium_conditional pred (fun parameter -> not (parameter_cond parameter))

let make_update_expression_lemma
  (pred: actor_state_predicate{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          match update_expression exp actor writer_pc writer_expression_number
                  bypassing_write_buffer new_value s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)})
  : unit -> Lemma
      (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
         match update_expression exp actor writer_pc writer_expression_number
                 bypassing_write_buffer new_value s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  fun _ -> ()

let make_update_expression_premium_conditional
  (pred: actor_state_predicate)
  (exp_value_pred: expression_t -> object_value_t -> bool{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          exp_value_pred exp new_value ==>
          (match update_expression exp actor writer_pc writer_expression_number
                   bypassing_write_buffer new_value s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (exp: _ -> actor: _ -> writer_pc: _ -> writer_expression_number: _ ->
          bypassing_write_buffer: _ -> new_value: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
            result == update_expression exp actor writer_pc writer_expression_number
                        bypassing_write_buffer new_value s
          /\ (exp_value_pred exp new_value ==>
              (match result with
               | ComputationProduces s' -> pred actor s s'
               | _ -> True))})) =
  let f exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s
    : GTot (result: conditional_computation_t Armada.State.t{
              result == update_expression exp actor writer_pc writer_expression_number
                          bypassing_write_buffer new_value s
              /\ (exp_value_pred exp new_value ==>
                 (match result with
                  | ComputationProduces s' -> pred actor s s'
                  | _ -> True))}) =
    update_expression exp actor writer_pc writer_expression_number bypassing_write_buffer
      new_value s
  in
  f

let make_update_expression_premium
  (pred: actor_state_predicate{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          match update_expression exp actor writer_pc writer_expression_number
                  bypassing_write_buffer new_value s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (exp: _ -> actor: _ -> writer_pc: _ -> writer_expression_number: _ ->
          bypassing_write_buffer: _ -> new_value: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
            result == update_expression exp actor writer_pc writer_expression_number
                        bypassing_write_buffer new_value s
          /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  let f exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s
    : GTot (result: conditional_computation_t Armada.State.t{
              result == update_expression exp actor writer_pc writer_expression_number
                          bypassing_write_buffer new_value s
              /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)}) =
    update_expression exp actor writer_pc writer_expression_number bypassing_write_buffer
      new_value s
  in
  f

let make_update_expressions_lemma_conditional
  (pred: actor_state_predicate)
  (exp_value_pred: expression_t -> object_value_t -> bool{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          exp_value_pred exp new_value ==>
          (match update_expression exp actor writer_pc writer_expression_number
                   bypassing_write_buffer new_value s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s.
         lists_correspond exp_value_pred exps new_values ==>
         (match update_expressions exps actor writer_pc writer_expression_number
                  bypassing_write_buffer new_values s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)) =
  fun _ ->
  let rec internal_lem exps actor writer_pc writer_expression_number bypassing_write_buffer
                         new_values s
    : Lemma (requires lists_correspond exp_value_pred exps new_values)
            (ensures (match update_expressions exps actor writer_pc writer_expression_number
                              bypassing_write_buffer new_values s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases exps)
            [SMTPat (update_expressions exps actor writer_pc writer_expression_number
                              bypassing_write_buffer new_values s)] =
    match exps, new_values with
    | [], [] -> ()
    | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
        (match update_expression first_exp actor writer_pc writer_expression_number
                 bypassing_write_buffer first_new_value s with
         | ComputationProduces s' ->
             internal_lem remaining_exps actor writer_pc (writer_expression_number + 1)
                            bypassing_write_buffer remaining_new_values s'
         | _ -> ())
    | _ -> ()
  in
  ()

let make_update_expressions_lemma
  (pred: actor_state_predicate{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          match update_expression exp actor writer_pc writer_expression_number
                  bypassing_write_buffer new_value s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s.
         match update_expressions exps actor writer_pc writer_expression_number
                 bypassing_write_buffer new_values s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  fun _ ->
  let rec internal_lem exps actor writer_pc writer_expression_number bypassing_write_buffer
                         new_values s
    : Lemma (ensures (match update_expressions exps actor writer_pc writer_expression_number
                              bypassing_write_buffer new_values s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases exps)
            [SMTPat (update_expressions exps actor writer_pc writer_expression_number
                              bypassing_write_buffer new_values s)] =
    match exps, new_values with
    | [], [] -> ()
    | first_exp :: remaining_exps, first_new_value :: remaining_new_values ->
        (match update_expression first_exp actor writer_pc writer_expression_number
                 bypassing_write_buffer first_new_value s with
         | ComputationProduces s' ->
             internal_lem remaining_exps actor writer_pc (writer_expression_number + 1)
                            bypassing_write_buffer remaining_new_values s'
         | _ -> ())
    | _ -> ()
  in
  ()

let make_update_expressions_premium_conditional
  (pred: actor_state_predicate)
  (exp_value_pred: expression_t -> object_value_t -> bool{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          exp_value_pred exp new_value ==>
          (match update_expression exp actor writer_pc writer_expression_number
                   bypassing_write_buffer new_value s with
           | ComputationProduces s' -> pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (exps: _ -> actor: _ -> writer_pc: _ -> writer_expression_number: _ ->
          bypassing_write_buffer: _ -> new_values: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
            result == update_expressions exps actor writer_pc writer_expression_number
                        bypassing_write_buffer new_values s
          /\ (lists_correspond exp_value_pred exps new_values ==>
             (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_update_expressions_lemma_conditional pred exp_value_pred ();
  let f exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s
    : GTot (result: conditional_computation_t Armada.State.t{
              result == update_expressions exps actor writer_pc writer_expression_number
                          bypassing_write_buffer new_values s
              /\ (lists_correspond exp_value_pred exps new_values ==>
                 (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))}) =
    update_expressions exps actor writer_pc writer_expression_number bypassing_write_buffer
      new_values s
  in
  f

let make_update_expressions_premium
  (pred: actor_state_predicate{
       (forall exp actor writer_pc writer_expression_number bypassing_write_buffer new_value s.
          match update_expression exp actor writer_pc writer_expression_number
                  bypassing_write_buffer new_value s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (exps: _ -> actor: _ -> writer_pc: _ -> writer_expression_number: _ ->
          bypassing_write_buffer: _ -> new_values: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
            result == update_expressions exps actor writer_pc writer_expression_number
                        bypassing_write_buffer new_values s
          /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  make_update_expressions_lemma pred ();
  let f exps actor writer_pc writer_expression_number bypassing_write_buffer new_values s
    : GTot (result: conditional_computation_t Armada.State.t{
              result == update_expressions exps actor writer_pc writer_expression_number
                          bypassing_write_buffer new_values s
              /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)}) =
    update_expressions exps actor writer_pc writer_expression_number bypassing_write_buffer
      new_values s
  in
  f

let make_external_method_take_snapshot_of_reads_clauses_computation_lemma_conditional
  (pred: actor_state_predicate)
  (read_clause_pred: (var_id_t * expression_t) -> bool{
       (forall var_id actor writer_pc writer_expression_number bypassing_write_buffer exp s.
          read_clause_pred (var_id, exp) ==>
          (match rvalue_computation exp actor s with
           | ComputationProduces value ->
               let td = expression_to_td exp in
               let local_var = ExpressionLocalVariable td var_id in
               (match update_expression local_var actor writer_pc writer_expression_number
                        bypassing_write_buffer value s with
                | ComputationProduces s' -> pred actor s s'
                | _ -> True)
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor writer_pc writer_expression_number bypassing_write_buffer reads_clauses s.
         {:pattern external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                     writer_expression_number bypassing_write_buffer reads_clauses s}
         for_all_ghost read_clause_pred reads_clauses ==>
         (match external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                   writer_expression_number bypassing_write_buffer reads_clauses s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)) =
  fun _ ->
  let rec internal_lem actor writer_pc writer_expression_number bypassing_write_buffer
                         reads_clauses s
    : Lemma (requires for_all_ghost read_clause_pred reads_clauses)
            (ensures (match external_method_take_snapshot_of_reads_clauses_computation actor
                              writer_pc writer_expression_number bypassing_write_buffer
                              reads_clauses s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases reads_clauses)
            [SMTPat (external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                       writer_expression_number bypassing_write_buffer reads_clauses s)] =
  match reads_clauses with
  | [] -> ()
  | (first_var_id, first_reads_expression) :: remaining_reads_clauses ->
      (match rvalue_computation first_reads_expression actor s with
       | ComputationProduces first_value ->
           let td = expression_to_td first_reads_expression in
           let local_var = ExpressionLocalVariable td first_var_id in
           (match update_expression local_var actor writer_pc writer_expression_number
                    bypassing_write_buffer first_value s with
            | ComputationProduces s' ->
                internal_lem actor writer_pc (writer_expression_number + 1)
                  bypassing_write_buffer remaining_reads_clauses s'
            | _ -> ())
       | _ -> ())
  in
  ()

let make_external_method_take_snapshot_of_reads_clauses_computation_lemma
  (pred: actor_state_predicate{
       (forall var_id actor writer_pc writer_expression_number bypassing_write_buffer exp s.
          match rvalue_computation exp actor s with
          | ComputationProduces value ->
              let td = expression_to_td exp in
              let local_var = ExpressionLocalVariable td var_id in
              (match update_expression local_var actor writer_pc writer_expression_number
                       bypassing_write_buffer value s with
               | ComputationProduces s' -> pred actor s s'
               | _ -> True)
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor writer_pc writer_expression_number bypassing_write_buffer reads_clauses s.
         {:pattern external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                     writer_expression_number bypassing_write_buffer reads_clauses s}
         match external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
                  writer_expression_number bypassing_write_buffer reads_clauses s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  make_external_method_take_snapshot_of_reads_clauses_computation_lemma_conditional
    pred (fun _ -> true)

let make_external_method_take_snapshot_of_reads_clauses_computation_premium_conditional
  (pred: actor_state_predicate)
  (read_clause_pred: (var_id_t * expression_t) -> bool{
       (forall var_id actor writer_pc writer_expression_number bypassing_write_buffer exp s.
          read_clause_pred (var_id, exp) ==>
          (match rvalue_computation exp actor s with
           | ComputationProduces value ->
               let td = expression_to_td exp in
               let local_var = ExpressionLocalVariable td var_id in
               (match update_expression local_var actor writer_pc writer_expression_number
                        bypassing_write_buffer value s with
                | ComputationProduces s' -> pred actor s s'
                | _ -> True)
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> bypassing_write_buffer: _ ->
          reads_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                    result == external_method_take_snapshot_of_reads_clauses_computation actor
                                writer_pc writer_expression_number bypassing_write_buffer
                                reads_clauses s
                  /\ (for_all_ghost read_clause_pred reads_clauses ==>
                     (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_external_method_take_snapshot_of_reads_clauses_computation_lemma_conditional pred
    read_clause_pred ();
  let f actor writer_pc writer_expression_number bypassing_write_buffer reads_clauses s
    : GTot (result: conditional_computation_t Armada.State.t{
                result == external_method_take_snapshot_of_reads_clauses_computation actor
                            writer_pc writer_expression_number bypassing_write_buffer
                            reads_clauses s
              /\ (for_all_ghost read_clause_pred reads_clauses ==>
                 (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))}) =
    external_method_take_snapshot_of_reads_clauses_computation actor writer_pc
      writer_expression_number bypassing_write_buffer reads_clauses s
  in
  f

let make_external_method_take_snapshot_of_reads_clauses_computation_premium
  (pred: actor_state_predicate{
       (forall var_id actor writer_pc writer_expression_number bypassing_write_buffer exp s.
          match rvalue_computation exp actor s with
          | ComputationProduces value ->
              let td = expression_to_td exp in
              let local_var = ExpressionLocalVariable td var_id in
              (match update_expression local_var actor writer_pc writer_expression_number
                       bypassing_write_buffer value s with
               | ComputationProduces s' -> pred actor s s'
               | _ -> True)
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> bypassing_write_buffer: _ ->
          reads_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                    result == external_method_take_snapshot_of_reads_clauses_computation actor
                                writer_pc writer_expression_number bypassing_write_buffer
                                reads_clauses s
                  /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  make_external_method_take_snapshot_of_reads_clauses_computation_premium_conditional
    pred (fun _ -> true)

let make_external_method_take_snapshot_of_reads_clauses_computation_premium_conditional_negative
  (pred: actor_state_predicate)
  (read_clause_pred: (var_id_t * expression_t) -> bool{
       (forall var_id actor writer_pc writer_expression_number bypassing_write_buffer exp s.
          read_clause_pred (var_id, exp) \/
            (match rvalue_computation exp actor s with
             | ComputationProduces value ->
                 let td = expression_to_td exp in
                 let local_var = ExpressionLocalVariable td var_id in
                 (match update_expression local_var actor writer_pc writer_expression_number
                          bypassing_write_buffer value s with
                  | ComputationProduces s' -> pred actor s s'
                  | _ -> True)
             | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> writer_pc: _ -> writer_expression_number: _ -> bypassing_write_buffer: _ ->
          reads_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                    result == external_method_take_snapshot_of_reads_clauses_computation actor
                                writer_pc writer_expression_number bypassing_write_buffer
                                reads_clauses s
                  /\ (exists_ghost read_clause_pred reads_clauses \/
                     (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_external_method_take_snapshot_of_reads_clauses_computation_premium_conditional
    pred (fun ve -> not (read_clause_pred ve))

let make_log_expressions_computation_lemma_conditional
  (pred: actor_state_predicate)
  (logs_clause_cond: expression_t -> GTot bool{
       (forall actor logs_clause s.
          logs_clause_cond logs_clause ==>
          (match rvalue_computation logs_clause actor s with
           | ComputationProduces event ->
               let trace' = s.trace $:: event in
               let s' = { s with trace = trace' } in
               pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor logs_clauses s.
         {:pattern log_expressions_computation actor logs_clauses s}
         for_all_ghost logs_clause_cond logs_clauses ==>
         (match log_expressions_computation actor logs_clauses s with
          | ComputationProduces s' -> pred actor s s'
          | _ -> True)) =
  fun _ ->
  let rec internal_lem actor logs_clauses s
    : Lemma (requires for_all_ghost logs_clause_cond logs_clauses)
            (ensures (match log_expressions_computation actor logs_clauses s with
                      | ComputationProduces s' -> pred actor s s'
                      | _ -> True))
            (decreases logs_clauses)
            [SMTPat (log_expressions_computation actor logs_clauses s)] =
    match logs_clauses with
    | [] -> ()
    | first_logs_clause :: remaining_logs_clauses ->
        (match rvalue_computation first_logs_clause actor s with
         | ComputationProduces event ->
             let trace' = s.trace $:: event in
             let s' = { s with trace = trace' } in
             internal_lem actor remaining_logs_clauses s'
         | _ -> ())
  in
  ()

let make_log_expressions_computation_lemma
  (pred: actor_state_predicate{
       (forall actor logs_clause s.
          match rvalue_computation logs_clause actor s with
          | ComputationProduces event ->
              let trace' = s.trace $:: event in
              let s' = { s with trace = trace' } in
              pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : unit -> Lemma
      (forall actor logs_clauses s.
         {:pattern log_expressions_computation actor logs_clauses s}
         match log_expressions_computation actor logs_clauses s with
         | ComputationProduces s' -> pred actor s s'
         | _ -> True) =
  make_log_expressions_computation_lemma_conditional pred (fun _ -> true)

let make_log_expressions_computation_premium_conditional
  (pred: actor_state_predicate)
  (logs_clause_cond: expression_t -> GTot bool{
       (forall actor logs_clause s.
          logs_clause_cond logs_clause ==>
          (match rvalue_computation logs_clause actor s with
           | ComputationProduces event ->
               let trace' = s.trace $:: event in
               let s' = { s with trace = trace' } in
               pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> logs_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == log_expressions_computation actor logs_clauses s
                /\ (for_all_ghost logs_clause_cond logs_clauses ==>
                   (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_log_expressions_computation_lemma_conditional pred logs_clause_cond ();
  let f actor logs_clauses s
    : GTot (result: conditional_computation_t Armada.State.t{
                result == log_expressions_computation actor logs_clauses s
              /\ (for_all_ghost logs_clause_cond logs_clauses ==>
                 (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))}) =
    log_expressions_computation actor logs_clauses s
  in
  f

let make_log_expressions_computation_premium
  (pred: actor_state_predicate{
       (forall actor logs_clause s.
          match rvalue_computation logs_clause actor s with
          | ComputationProduces event ->
              let trace' = s.trace $:: event in
              let s' = { s with trace = trace' } in
              pred actor s s'
          | _ -> True)
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> logs_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == log_expressions_computation actor logs_clauses s
                /\ (match result with | ComputationProduces s' -> pred actor s s' | _ -> True)})) =
  make_log_expressions_computation_premium_conditional pred (fun _ -> true)

let make_log_expressions_computation_premium_conditional_negative
  (pred: actor_state_predicate)
  (logs_clause_cond: expression_t -> GTot bool{
       (forall actor logs_clause s.
          logs_clause_cond logs_clause \/
          (match rvalue_computation logs_clause actor s with
           | ComputationProduces event ->
               let trace' = s.trace $:: event in
               let s' = { s with trace = trace' } in
               pred actor s s'
           | _ -> True))
     /\ actor_state_predicate_reflexive pred
     /\ actor_state_predicate_transitive pred})
  : GTot (actor: _ -> logs_clauses: _ -> s: _ ->
          GTot (result: conditional_computation_t Armada.State.t{
                  result == log_expressions_computation actor logs_clauses s
                /\ (exists_ghost logs_clause_cond logs_clauses \/
                   (match result with | ComputationProduces s' -> pred actor s s' | _ -> True))})) =
  make_log_expressions_computation_premium_conditional pred
    (fun c -> not (logs_clause_cond c))

let statement_computation_expandables : list string =
  [
    "Armada.Statement.assume_expression_statement_computation";
    "Armada.Statement.assume_predicate_statement_computation";
    "Armada.Statement.assert_true_statement_computation";
    "Armada.Statement.assert_false_statement_computation";
    "Armada.Statement.conditional_jump_statement_computation";
    "Armada.Statement.unconditional_jump_statement_computation";
    "Armada.Statement.update_statement_computation";
    "Armada.Statement.propagate_write_message_statement_computation";
    "Armada.Statement.compare_and_swap_swapping_statement_computation";
    "Armada.Statement.compare_and_swap_nonswapping_statement_computation";
    "Armada.Statement.atomic_exchange_statement_computation";
    "Armada.Statement.make_thread_running";
    "Armada.Statement.create_thread_statement_computation";
    "Armada.Statement.push_stack_frame";
    "Armada.Statement.method_call_statement_computation";
    "Armada.Statement.pop_stack_frame";
    "Armada.Statement.return_statement_computation";
    "Armada.Statement.terminate_thread_statement_computation";
    "Armada.Statement.terminate_process_statement_computation";
    "Armada.Statement.join_statement_computation";
    "Armada.Statement.mark_allocation_root_allocated";
    "Armada.Statement.alloc_successful_statement_computation";
    "Armada.Statement.alloc_returning_null_statement_computation";
    "Armada.Statement.dealloc_statement_computation";
    "Armada.Statement.somehow_statement_computation";
    "Armada.Statement.fence_statement_computation";
    "Armada.Statement.external_method_take_snapshot_of_reads_clauses_computation";
    "Armada.Statement.external_method_start_statement_computation";
    "Armada.Statement.external_method_check_snapshot_computation";
    "Armada.Statement.external_method_middle_statement_computation";
    "Armada.Statement.log_expressions_computation";
    "Armada.Statement.external_method_end_statement_computation";
    "Armada.Statement.statement_computation";
    "Armada.Computation.return";
    "Armada.Computation.bind"
  ]
