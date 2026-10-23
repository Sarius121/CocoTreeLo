(** module for CTL formulas *)

type label = string
type bool_term = Sat.expr
type var = string

type ctl = L of label | NOTL of label | B of bool_term
         | FACT of Multiset_rewrite_system.fact | NOTFACT of Multiset_rewrite_system.fact
         | AND of ctl * ctl | OR of ctl * ctl
         | FORALL of bool * var * ctl | EXISTS of bool * var * ctl
         | A of ctl_path | E of ctl_path
and ctl_path = X of ctl | U of ctl * ctl | W of ctl * ctl

(** returns the sub-formula of ctl that requires taking a transition (if existent) *)
let transition_relation ((ctl: ctl), (vars: var list)) : (ctl * var list) option =
  match ctl with
  | A (X ctl)
  | E (X ctl) -> Some (ctl, vars)
  | _ -> None

(** returns all sub-formulas of ctl *)
let sub_relation ((ctl: ctl), (vars: var list)) : (ctl * var list) list =
  match ctl with
  | AND (ctl1, ctl2)
  |  OR (ctl1, ctl2) -> [ctl1, vars; ctl2, vars]
  | A (U (ctl1, ctl2)) -> [ctl1, vars; ctl2, vars; A (X (A (U (ctl1, ctl2)))), vars]
  | E (U (ctl1, ctl2)) -> [ctl1, vars; ctl2, vars; E (X (E (U (ctl1, ctl2)))), vars]
  | A (W (ctl1, ctl2)) -> [ctl1, vars; ctl2, vars; A (X (A (W (ctl1, ctl2)))), vars]
  | E (W (ctl1, ctl2)) -> [ctl1, vars; ctl2, vars; E (X (E (W (ctl1, ctl2)))), vars]
  | FORALL (_, x, ctl)
  | EXISTS (_, x, ctl) -> [(ctl, x::vars)]
  | _ -> []

let rec to_string (ctl: ctl) =
  match ctl with
  | L lbl -> lbl
  | NOTL lbl -> "!" ^ lbl
  | B term -> Sat.to_string term
  | FACT fact -> Multiset_rewrite_system.fact_to_string fact
  | NOTFACT fact -> "!" ^ Multiset_rewrite_system.fact_to_string fact
  | AND (ctl1, ctl2) -> String.concat "" ["("; to_string ctl1; " && "; to_string ctl2; ")"]
  | OR (ctl1, ctl2) -> String.concat "" ["("; to_string ctl1; " || "; to_string ctl2; ")"]
  | FORALL (_, x, ctl) -> Printf.sprintf "\u{2200} %s. %s" x (to_string ctl)
  | EXISTS (_, x, ctl) -> Printf.sprintf "\u{2203} %s. %s" x (to_string ctl)
  | A (ctl_path) -> String.concat "" ["A"; path_to_string ctl_path ]
  | E (ctl_path) -> String.concat "" ["E"; path_to_string ctl_path ]
and path_to_string ctl_path =
  match ctl_path with
  | X ctl -> String.concat " " ["X"; to_string ctl]
  | U (ctl1, ctl2) -> String.concat "" ["("; to_string ctl1; " U "; to_string ctl2; ")"]
  | W (ctl1, ctl2) -> String.concat "" ["("; to_string ctl1; " W "; to_string ctl2; ")"]
  
module FactSet = Set.Make(struct
  type t = Multiset_rewrite_system.fact
  let compare = Repr.compare
end)

(**
  Returns all facts that appear in CTL without duplicates.
*)
let get_facts ctl =
  let rec get_facts' ctl facts =
    match ctl with
    | FACT fact
    | NOTFACT fact -> FactSet.add fact facts
    | AND (ctl1, ctl2)
    | OR (ctl1, ctl2) -> get_facts' ctl1 (get_facts' ctl2 facts)
    | FORALL (_, x, ctl)
    | EXISTS (_, x, ctl) -> get_facts' ctl facts
    | A (ctl_path)
    | E (ctl_path) -> path_get_facts' ctl_path facts
    | _ -> facts
  and path_get_facts' ctl_path facts =
    match ctl_path with
    | X ctl -> get_facts' ctl facts
    | U (ctl1, ctl2)
    | W (ctl1, ctl2) -> get_facts' ctl1 (get_facts' ctl2 facts)
  in
  get_facts' ctl FactSet.empty
  |> FactSet.to_list

type ctl_type = ACTL | ECTL | MIXED | ANY

let type_op a b = match a, b with
  | a, b when a = b -> a
  | ANY, a
  | a, ANY -> a
  | _ -> MIXED

let rec get_type ctl = match ctl with
  | A ctl -> type_op ACTL (path_get_type ctl)
  | E ctl -> type_op ECTL (path_get_type ctl)
  | AND (ctl1, ctl2)
  | OR (ctl1, ctl2) -> type_op (get_type ctl1) (get_type ctl2)
  | FORALL (_, _, ctl) -> type_op ACTL (get_type ctl)
  | EXISTS (_, _, ctl) -> type_op ECTL (get_type ctl)
  | _ -> ANY
and path_get_type ctl_path =
  match ctl_path with
  | X ctl -> get_type ctl
  | U (ctl1, ctl2)
  | W (ctl1, ctl2) -> type_op (get_type ctl1) (get_type ctl2)

let put_quantifiers_leading ctl =
  let rec put_quantifiers_leading ctl =
    match ctl with
    | A ctl ->
      let (ctl, all_ok, quantifiers, quantifiers_type) = path_put_quantifiers_leading ctl in
      let all_ok = all_ok && (type_op ACTL quantifiers_type != MIXED) in
      (A ctl, all_ok, quantifiers, quantifiers_type)
    | E ctl ->
      let (ctl, all_ok, quantifiers, quantifiers_type) = path_put_quantifiers_leading ctl in
      let all_ok = all_ok && (type_op ECTL quantifiers_type != MIXED) in
      (E ctl, all_ok, quantifiers, quantifiers_type)
    | AND (ctl1, ctl2) ->
      let (ctl1, all_ok1, quantifiers1, quantifiers_type1) = put_quantifiers_leading ctl1 in
      let (ctl2, all_ok2, quantifiers2, quantifiers_type2) = put_quantifiers_leading ctl2 in
      (AND (ctl1, ctl2), all_ok1 && all_ok2, quantifiers1 @ quantifiers2, type_op quantifiers_type1 quantifiers_type2)
    | OR (ctl1, ctl2) -> 
      let (ctl1, all_ok1, quantifiers1, quantifiers_type1) = put_quantifiers_leading ctl1 in
      let (ctl2, all_ok2, quantifiers2, quantifiers_type2) = put_quantifiers_leading ctl2 in
      (OR (ctl1, ctl2), all_ok1 && all_ok2, quantifiers1 @ quantifiers2, type_op quantifiers_type1 quantifiers_type2)
    | FORALL (_, x, ctl) ->
      let (ctl, all_ok, quantifiers, quantifiers_type) = put_quantifiers_leading ctl in
      (ctl, all_ok, (ACTL, x)::quantifiers, type_op ACTL quantifiers_type)
    | EXISTS (_, x, ctl) ->
      let (ctl, all_ok, quantifiers, quantifiers_type) = put_quantifiers_leading ctl in
      (ctl, all_ok, (ECTL, x)::quantifiers, type_op ECTL quantifiers_type)
    | ctl -> (ctl, true, [], ANY)
  and path_put_quantifiers_leading ctl_path =
    match ctl_path with
    | X ctl -> 
      let (ctl, all_ok, quantifiers, quantifiers_type) = put_quantifiers_leading ctl in
      (X ctl, all_ok, quantifiers, quantifiers_type)
    | U (ctl1, ctl2) ->
      let (ctl1, all_ok1, quantifiers1, quantifiers_type1) = put_quantifiers_leading ctl1 in
      let (ctl2, all_ok2, quantifiers2, quantifiers_type2) = put_quantifiers_leading ctl2 in
      (* can only move forall out of left side and exists out of right side *)
      let all_ok = (type_op quantifiers_type1 ACTL) <> MIXED && quantifiers_type2 = ANY
          || (type_op quantifiers_type2 ECTL) <> MIXED && quantifiers_type1 = ANY in
      (U (ctl1, ctl2), all_ok && all_ok1 && all_ok2, quantifiers1 @ quantifiers2, type_op quantifiers_type1 quantifiers_type2)
    | W (ctl1, ctl2) ->
      let (ctl1, all_ok1, quantifiers1, quantifiers_type1) = put_quantifiers_leading ctl1 in
      let (ctl2, all_ok2, quantifiers2, quantifiers_type2) = put_quantifiers_leading ctl2 in
      (* can only move forall out of left side and exists out of right side *)
      let all_ok = (type_op quantifiers_type1 ACTL) <> MIXED && quantifiers_type2 = ANY
          || (type_op quantifiers_type2 ECTL) <> MIXED && quantifiers_type1 = ANY in
      (W (ctl1, ctl2), all_ok && all_ok1 && all_ok2, quantifiers1 @ quantifiers2, type_op quantifiers_type1 quantifiers_type2)
  in
  let (ctl, all_ok, quantifiers, quantifiers_type) = put_quantifiers_leading ctl in
  if all_ok then
    Some (List.fold_right (fun (q_type, var) ctl -> match q_type with
      | ACTL -> FORALL (true, var, ctl)
      | ECTL -> EXISTS (true, var, ctl)
      | _ -> failwith "Illegal state") quantifiers ctl)
  else
    None

let rec get_leading_quantified_vars ctl = match ctl with
  | FORALL (_, var, ctl)
  | EXISTS (_, var, ctl) -> var :: (get_leading_quantified_vars ctl)
  | _ -> []

let rec get_non_leading_quantified_vars ctl = match ctl with
  | A ctl -> path_get_non_leading_quantified_vars ctl
  | E ctl -> path_get_non_leading_quantified_vars ctl
  | AND (ctl1, ctl2)
  | OR (ctl1, ctl2) -> (get_non_leading_quantified_vars ctl1) @ (get_non_leading_quantified_vars ctl2)
  | FORALL (leading, var, ctl)
  | EXISTS (leading, var, ctl) -> 
    let rest = get_non_leading_quantified_vars ctl in
    if leading then rest
    else var::rest
  | _ -> []
and path_get_non_leading_quantified_vars ctl_path =
  match ctl_path with
  | X ctl -> get_non_leading_quantified_vars ctl
  | U (ctl1, ctl2)
  | W (ctl1, ctl2) -> (get_non_leading_quantified_vars ctl1) @ (get_non_leading_quantified_vars ctl2)

let%expect_test "test_get_facts" =
  let ctl = OR (AND (FACT ("P", [Arg_terms.(Int (Var "x"))]), NOTFACT ("P", [Arg_terms.(Int (Var "y"))])), FACT ("P", [Arg_terms.(Int (Var "x"))])) in
  let facts = get_facts ctl in
  Printf.printf "%s" (Multiset_rewrite_system.ms_to_string facts);
  [%expect {| [P(x), P(y)] |}]

let%expect_test "test_put_quantifiers_leading" =
  let ctl = FORALL (true, "x", A (X (L "P"))) in
  let ctl = Option.get (put_quantifiers_leading ctl) in
  Printf.printf "%s" (to_string ctl);
  [%expect "\u{2200} x. AX P"];

  let ctl = FORALL (true, "x", A (X (FORALL (false, "y", L "P")))) in
  let ctl = Option.get (put_quantifiers_leading ctl) in
  Printf.printf "%s" (to_string ctl);
  [%expect "\u{2200} x. \u{2200} y. AX P"];

  let ctl = AND(A (X (FORALL (false, "x", L "P"))), E (X (EXISTS (false, "y", L "Q")))) in
  let ctl = Option.get (put_quantifiers_leading ctl) in
  Printf.printf "%s" (to_string ctl);
  [%expect "\u{2200} x. \u{2203} y. (AX P && EX Q)"];

  let ctl = AND(A (X (FORALL (false, "x", L "P"))), A (X (EXISTS (false, "y", L "Q")))) in
  let res = if Option.is_none (put_quantifiers_leading ctl) then "None" else "Some" in
  Printf.printf "%s" res;
  [%expect "None"];

  let ctl = A (U (A (X (FORALL (false, "x", L "P"))), A (X (FORALL (false, "y", L "Q"))))) in
  let ctl = Option.get (put_quantifiers_leading ctl) in
  Printf.printf "%s" (to_string ctl);
  [%expect "\u{2200} x. \u{2200} y. A(AX P U AX Q)"];

  let ctl = A (W (A (X (FORALL (false, "x", L "P"))), A (X (FORALL (false, "y", L "Q"))))) in
  let ctl = Option.get (put_quantifiers_leading ctl) in
  Printf.printf "%s" (to_string ctl);
  [%expect "\u{2200} x. \u{2200} y. A(AX P W AX Q)"];
