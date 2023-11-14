module Util.Tactics

open FStar.Printf
open FStar.Tactics

/// Replacing a function in the current goal
///
/// Using the tactic `replace_fn_in_goal` will replace all instances
/// of a given function invocation in the goal with an invocation of
/// another function.  You give it the name of the function to be
/// replaced (`fn`), the number of arguments to that function
/// (`argc`), and a lemma that demonstrates that the function is
/// equivalent to another function (`lem`).  That lemma must take
/// `argc` arguments and have a postcondition that says that `fn`
/// applied to that many arguments is `==` to another function.  You
/// don't have to supply the name of that second function since it's
/// taken from that postcondition automatically.
///
/// NOTE: The lemma must have as a postcondition that f a1 a2 ... ==
/// f' a1 a2 where f is the replaced function.  If it says that f' a1
/// a2 ... == f a1 a2 instead (i.e., in the wrong order) then
/// `replace_fn_in_goal` won't work.

let rec is_term_an_invocation_of_function (t: term) (fn: term) (argc: nat) : Tac bool =
  if argc = 0 then
    term_eq t fn
  else
    match t with
    | Tv_App fn' arg -> is_term_an_invocation_of_function fn' fn (argc - 1)
    | _ -> false

let replace_fn_in_goal (fn: term) (argc: nat) (lem: term) : Tac unit =
  let my_ctrl (t: term) : Tac (bool & ctrl_flag) =
    (is_term_an_invocation_of_function t fn argc, Continue) in
  let my_rw () : Tac unit =
    apply_lemma lem in
  ctrl_rewrite BottomUp my_ctrl my_rw

/// Synthesizing a lemma invocation for each instance of a function in a term
///
/// The tactic `fn_to_lemma_invocations_in_term` creates an optional
/// term that includes an invocation of lemma `lem` for each time a
/// given function `fn` appears in a given term `t`.  You must also supply
/// `argc`, the number of arguments to the function.  The lemma should take
/// the same arguments as the function, in the same order.
///
/// Once you have optional terms from one or more invocations of
/// `fn_to_lemma_invocations_in_term`, you can use them to synthesize
/// a proof of a squashed proposition.  To do this, use
/// `synthesize_proof_term_from_optional_terms`.  This will invoke the
/// `t_exact` tactic using a term that concatenates all the optional
/// terms.

private let rec combine_optional_terms (ots: list (option term)) : Tac (option term) =
  match ots with
  | [] -> None
  | [ot] -> ot
  | Some t1 :: remaining_ots ->
      (match combine_optional_terms remaining_ots with
       | Some t2 -> Some (`(let _ = (`#t1) in (`#t2)))
       | None -> Some t1)
  | None :: remaining_ots -> combine_optional_terms remaining_ots

private let rec optional_terms_to_terms (ots: list (option term)) : Tac (list term) =
  match ots with
  | [] -> []
  | Some first_term :: remaining_ots -> first_term :: (optional_terms_to_terms remaining_ots)
  | None :: remaining_ots -> optional_terms_to_terms remaining_ots

private let rec combine_terms (ts: list term) : Tac term =
  match ts with
  | [] -> quote ()
  | [t] -> t
  | hd :: tl -> let tl' = combine_terms tl in
              `(let _ = (`#hd) in (`#tl'))

private let optional_terms_to_term (ots: list (option term)) : Tac term =
  combine_terms (optional_terms_to_terms ots)

let synthesize_proof_term_from_optional_terms (ts: list (option term)) : Tac unit =
  let t = optional_terms_to_term ts in
//  print ("Synthesized proof term: " ^ (term_to_string t) ^ " (end synthesized proof term)");
  t_exact true true t

let rec fn_to_lemma_invocation_in_application_term (fn: term) (argc: pos) (lem: term) (t: term) : Tac (option term) =
  match t with
  | Tv_App t' arg ->
     if argc = 1 then
       if term_eq t' fn then
         Some (pack (Tv_App lem arg))
       else
         None
     else
       (match fn_to_lemma_invocation_in_application_term fn (argc - 1) lem t' with
        | Some lem' -> Some (pack (Tv_App lem' arg))
        | None -> None)
  | _ -> None

let rec fn_to_lemma_invocations_in_term (fn: term) (argc: pos) (lem: term) (t: term) : Tac (option term) =
  match inspect t with
  | Tv_Var _ -> None
  | Tv_BVar _ -> None
  | Tv_FVar _ -> None
  | Tv_UInst _ _ -> None
  | Tv_App hd argv ->
      let f' = fn_to_lemma_invocation_in_application_term fn argc lem t in
      let hd' = fn_to_lemma_invocations_in_term fn argc lem hd in
      let argv' = fn_to_lemma_invocations_in_term fn argc lem (fst argv) in
      combine_optional_terms [f'; hd'; argv']
  | Tv_Abs _ _ -> None
  | Tv_Arrow _ _ -> None
  | Tv_Type _ -> None
  | Tv_Refine _ _ -> None
  | Tv_Const _ -> None
  | Tv_Uvar _ _ -> None
  | Tv_Let recf attrs bv def body ->
      let def_lemmas = fn_to_lemma_invocations_in_term fn argc lem def in
      let body_lemmas =
        (match fn_to_lemma_invocations_in_term fn argc lem body with
         | Some body' -> Some (pack (Tv_Let recf attrs bv def body'))
         | None -> None) in
      combine_optional_terms [def_lemmas; body_lemmas]
  | Tv_Match scrutinee ret brs ->
      let scrutinee_lemmas = fn_to_lemma_invocations_in_term fn argc lem scrutinee in
      let any_nontrivial, brs' = fn_to_lemma_invocations_in_branches fn argc lem brs in
      let match_lemmas = if any_nontrivial then Some (pack (Tv_Match scrutinee ret brs')) else None in
      combine_optional_terms [scrutinee_lemmas; match_lemmas]
  | Tv_AscribedT e _ _ _ ->
      fn_to_lemma_invocations_in_term fn argc lem e
  | Tv_AscribedC e _ _ _ ->
      fn_to_lemma_invocations_in_term fn argc lem e
  | Tv_Unknown -> None

and fn_to_lemma_invocations_in_branches
  (fn: term)
  (argc: pos)
  (lem: term)
  (brs: list branch)
  : Tac (bool * (list branch)) =
  match brs with
  | [] -> false, []
  | (branch_pattern, branch_term) :: remaining_branches ->
      let remaining_any_nontrivial, remaining_result = fn_to_lemma_invocations_in_branches fn argc lem remaining_branches in
      match fn_to_lemma_invocations_in_term fn argc lem branch_term with
      | Some result -> true, (branch_pattern, result) :: remaining_result
      | None -> remaining_any_nontrivial, (branch_pattern, quote ()) :: remaining_result

(*

assume val f (x: int) (y: int) : Tot int
assume val f_lemma1 (x: int) (y: int) : Lemma (f x y > x)
assume val f_lemma2 (x: int) (y: int) : Lemma (f x y > y)
let h (x: int) (y: int) (z: int) : Tot int = f (f x y) z

let f' (x: int) (y: int) : Tot (z: int{z > x /\ z > y}) =
  f_lemma1 x y;
  f_lemma2 x y;
  f x y

let f'_equivalence (x: int) (y: int) : Lemma (ensures f x y == f' x y) =
  ()

let lem1 (x: int) (y: int) (z: int) (w: int) : Lemma (requires w = h x y z) (ensures w > x /\ w > y /\ w > z) =
  assert (w = h x y z ==> w > x /\ w > y /\ w > z) by (
    norm [nbe; delta; iota];
    replace_fn_in_goal (`f) 2 (`f'_equivalence)
  )

let lem2 (opt_x: option int) (y: int) (z: int) (w: int{match opt_x with | Some x -> w = h x y z | None -> False})
: squash (match opt_x with | Some x -> w > x /\ w > y /\ w > z | None -> True) =
  _ by (
    let t1 = quote (match opt_x with | Some x -> w == h x y z | None -> False) in
    let t2 = norm_term_env (cur_env ()) [nbe; delta; iota] t1 in
    let ot1 = fn_to_lemma_invocations_in_term (`f) 2 (`f_lemma1) t2 in
    let ot2 = fn_to_lemma_invocations_in_term (`f) 2 (`f_lemma2) t2 in
    synthesize_proof_term_from_optional_terms [ot1; ot2]
  )

*)

/// Converting term views to strings
///
/// The function `term_to_view_to_string` converts a term to a term_view and from
/// that to a string.

let vconst_to_string  (v: vconst) : Tac string =
  match v with
  | C_Unit -> "C_Unit"
  | C_Int i -> "C_Int(" ^ (sprintf "%d" i) ^ ")"
  | C_True -> "C_True"
  | C_False -> "C_False"
  | C_String s -> "C_String(" ^ s ^ ")"
  | C_Range r -> "C_Range"
  | C_Reify -> "C_Reify"
  | C_Reflect _ -> "C_Reflect"

let rec identifier_to_string (id: list string) : Tac string =
  match id with
  | [] -> ""
  | [name] -> name
  | modname :: id' -> modname ^ (identifier_to_string id')

let rec term_to_view_to_string (t: term) : Tac string =
  match inspect t with
  | Tv_Var v -> "Tv_Var " ^ (bv_to_string v)
  | Tv_BVar v -> "Tv_BVar " ^ (bv_to_string v)
  | Tv_FVar v -> "Tv_FVar " ^ (fv_to_string v)
  | Tv_UInst v us -> "Tv_UInst " ^ (fv_to_string v)
  | Tv_App hd argv ->
      "Tv_App(" ^ (term_to_view_to_string hd) ^ " " ^ (term_to_view_to_string (fst argv)) ^ ")"
  | Tv_Abs b body -> "Tv_Abs(" ^ (binder_to_string b) ^ " -> " ^ (term_to_view_to_string body) ^ ")"
  | Tv_Arrow _ _ -> "Tv_Arrow"
  | Tv_Type _ -> "Tv_Type"
  | Tv_Refine bv ref -> "Tv_Refine" ^ (term_to_view_to_string ref)
  | Tv_Const v -> "Tv_Const(" ^ (vconst_to_string v) ^ ")"
  | Tv_Uvar _ _ -> "Tv_Uvar"
  | Tv_Let recf attrs bv def body ->
      "Tv_Let(" ^ (term_to_view_to_string (bv_to_term bv)) ^
              " = " ^ (term_to_view_to_string def) ^ " in " ^ (term_to_view_to_string body) ^ ")"
  | Tv_Match scrutinee ret brs ->
     "Tv_Match(" ^ (term_to_view_to_string scrutinee) ^ " with " ^ (branches_to_string brs) ^ ")"
  | Tv_AscribedT e t tac _ -> "Tv_AscribedT(" ^ (term_to_view_to_string e) ^ ")"
  | Tv_AscribedC e c tac _ -> "Tv_AscribedC(" ^ (term_to_view_to_string e) ^ ")"
  | Tv_Unknown -> "Tv_Unknown"

and term_views_to_strings (ts: list term) : Tac string =
  match ts with
  | [] -> "[]"
  | hd :: tl -> (term_to_view_to_string hd) ^ " :: " ^ (term_views_to_strings tl)

and branches_to_string (bs: list branch) : Tac string =
  match bs with
  | [] -> ""
  | (branch_pattern, branch_term) :: tl -> "| ??? -> " ^ (term_to_view_to_string branch_term) ^ " " ^ (branches_to_string tl)

(*

let test_term_to_view_to_string (ox: option int) : Lemma (True) =
  assert (True) by (
    let t = quote (match ox with | Some x -> True | None -> False) in
    print (term_to_view_to_string t)
  )

*)
