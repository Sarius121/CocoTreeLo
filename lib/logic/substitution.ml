type t = {
  arg_subst: (string * Arg_terms.term) list;
  ms_subst: (string * Multiset_rewrite_system.term) list
}

let get_arg_opt subst var = List.assoc_opt var subst.arg_subst

let get_ms_opt subst var = List.assoc_opt var subst.ms_subst

let get_ms_var subst var = match get_ms_opt subst var with
  | Some (Multiset_rewrite_system.Var var) -> var
  | None -> var
  | _ -> failwith "Expected a variable renaming of multisets."

let empty = { arg_subst = []; ms_subst = [] }

let add_ms subst var value = {subst with ms_subst=(var, value)::subst.ms_subst}

let add_arg subst var value = {subst with arg_subst=(var, value)::subst.arg_subst}

let apply_arg subst term = Arg_terms.subst_vars term subst.arg_subst

let apply_arg_unknowns subst term = Arg_terms.subst_unknowns term subst.arg_subst

let apply_ms subst term = Multiset_rewrite_system.term_subst_vars term subst.ms_subst subst.arg_subst

let apply_arg_smt subst smt =
  let (vars, exprs) = List.fold_left (fun (concrete_vars, concrete_exprs) (var, expr) ->
      let expr = Arg_terms.to_smt expr in
      (var::concrete_vars, expr::concrete_exprs)
    ) ([], []) subst.arg_subst
  in
  Sat.subst_vars smt vars exprs

(** This function is very much only written for specific use-cases,
  and might not always do what you expect from a "normal" inversion.
  After inversion, multiple substitutions for a variable might exist.
*)
let inv_special subst =
  let ms_subst = List.map (fun (var, value) -> 
    match value with
    | Multiset_rewrite_system.Var value -> (value, Multiset_rewrite_system.Var var)
    | Multiset_rewrite_system.Union (Multiset_rewrite_system.Var const, others) ->
        (const, Multiset_rewrite_system.Minus (Multiset_rewrite_system.Var var, others))
    (* more cases could in theory be supported if required *)
    | _ -> failwith "The substitution cannot be inverted without mapping, because it does map to non-variable terms."
  ) subst.ms_subst in
  let arg_subst = List.filter_map (fun (var, value) -> 
    match value with
    | Arg_terms.(Int Var value) -> Some (value, Arg_terms.(Int (Var var)))
    | Arg_terms.(Int Const _) -> None
    | _ -> failwith "The substitution cannot be inverted without mapping, because it does map to non-variable terms."
  ) subst.arg_subst in
  { ms_subst; arg_subst }

let inv_map subst f_ms f_arg = { ms_subst = List.map f_ms subst.ms_subst; arg_subst = List.map f_arg subst.arg_subst }

let make_total_arg subst vars default = 
  let (arg_subst, _) = List.fold_left (fun (subst, i) var ->
      if List.assoc_opt var subst = None then ((var, default i)::subst, i+1)
      else (subst, i)
    ) (subst.arg_subst, 0) vars in
  {subst with arg_subst}

let restrict subst f =
  let ms_subst = List.filter (fun (var, _) -> f var) subst.ms_subst in
  let arg_subst = List.filter (fun (var, _) -> f var) subst.arg_subst in
  { ms_subst; arg_subst }

(* let compose_ms subst1 subst2 =
  let vars = Str_utils.StringSet.empty in
  let (vars, subst1) = List.fold_left_map (fun vars (var, value) -> (Str_utils.StringSet.add var vars, (var, extract_ms value))) vars subst1 in
  let (vars, subst2) = List.fold_left_map (fun vars (var, value) -> (Str_utils.StringSet.add var vars, (var, extract_ms value))) vars subst2 in
  let subst = List.map (fun var -> (var, Multiset_rewrite_system.Var var)) (Str_utils.StringSet.to_list vars) in
  let subst = List.map (fun (var, value) -> (var, Multiset_rewrite_system.subst_vars value subst2)) subst in
  let subst = List.map (fun (var, value) -> (var, MS (Multiset_rewrite_system.subst_vars value subst1))) subst in
  subst *)

let concat subst1 subst2 = { ms_subst = subst1.ms_subst @ subst2.ms_subst; arg_subst = subst1.arg_subst @ subst2.arg_subst }

let concat_with_dup f_arg f_ms subst1 subst2 acc =
  let concat_with_dup f l1 l2 acc =
    let l = List.sort Repr.compare (l1 @ l2) in
    let rec concat_with_dup' l =
      match l with
      | [] -> ([], acc)
      | x1::x2::l when x1 = x2 ->
        let (l, acc) = concat_with_dup' l in
        let (x, acc) = f x1 x2 acc in
        (x::l, acc)
      | x::l ->
        let (l, acc) = concat_with_dup' l in
        (x::l, acc)
    in
    concat_with_dup' l
  in
  let (ms_subst, acc) = concat_with_dup f_ms subst1.ms_subst subst2.ms_subst acc in
  let (arg_subst, acc) = concat_with_dup f_arg subst1.arg_subst subst2.arg_subst acc in
  ({ ms_subst; arg_subst }, acc)

let compose subst1 subst2 =
  let open Utils in
  let get_all_vars subst1 subst2 =
    let vars = Str_utils.StringSet.empty in
    let vars = List.fold_left (fun vars (var, value) -> Str_utils.StringSet.add var vars) vars subst1 in
    let vars = List.fold_left (fun vars (var, value) -> Str_utils.StringSet.add var vars) vars subst2 in
    Str_utils.StringSet.to_list vars
  in
  let vars_arg = get_all_vars subst1.arg_subst subst2.arg_subst in
  let vars_ms = get_all_vars subst1.ms_subst subst2.ms_subst in
  let ms_subst = List.map (fun var ->
      let value =
        Multiset_rewrite_system.Var var
        |> apply_ms subst2
        |> apply_ms subst1
      in
      (var, value)
    ) vars_ms in
  let arg_subst = List.map (fun var ->
      let value =
        Arg_terms.UntypedVar var
        |> apply_arg subst2
        |> apply_arg subst1
      in
      (var, value)
    ) vars_arg in
  { ms_subst; arg_subst }

let compose_restrict subst1 subst2 =
  let ms_subst = List.map (fun (var, value) -> (var, apply_ms subst1 value)) subst2.ms_subst in
  let arg_subst = List.map (fun (var, value) -> (var, apply_arg subst1 value)) subst2.arg_subst in
  { ms_subst; arg_subst }

let to_string subst =
  let ms_s = List.map (fun (var, value) ->
    let value_s = Multiset_rewrite_system.term_to_string value in
    var ^ "->" ^ value_s) subst.ms_subst
  in
  let arg_s = List.map (fun (var, value) ->
    let value_s = Arg_terms.to_string value in
    var ^ "->" ^ value_s) subst.arg_subst
  in
  "[" ^ String.concat ", " (arg_s @ ms_s) ^ "]"

let to_string_assignment subst =
  let ms_s = List.map (fun (var, value) ->
    let value_s = Multiset_rewrite_system.term_to_string value in
    var ^ ":=" ^ value_s) subst.ms_subst
  in
  let arg_s = List.map (fun (var, value) ->
    let value_s = Arg_terms.to_string value in
    var ^ ":=" ^ value_s) subst.arg_subst
  in
  String.concat ", " (arg_s @ ms_s)

let simplify subst =
  let ms_subst = List.map (fun (var, value) -> (var, Multiset_rewrite_system.term_simplify value)) subst.ms_subst in
  let arg_subst = List.map (fun (var, value) -> (var, Arg_terms.simplify value)) subst.arg_subst in
  { ms_subst; arg_subst }

(** get all arg variables that the substitution maps to (including the ones appearing in ms_subst) *)
let range_arg subst =
  let ms_range = List.map (fun (var, value) -> Multiset_rewrite_system.term_get_arg_vars value) subst.ms_subst in
  let arg_range = List.map (fun (var, value) -> Arg_terms.vars value) subst.arg_subst in
  let module StringSet = Utils.Str_utils.StringSet in
  let range = List.fold_left (fun range vars -> StringSet.add_seq (List.to_seq vars) range) StringSet.empty ms_range in
  let range = List.fold_left (fun range vars -> StringSet.add_seq (List.to_seq vars) range) range arg_range in
  range

let domain subst =
  let module StringSet = Utils.Str_utils.StringSet in
  let domain = List.fold_left (fun domain (var, _) -> StringSet.add var domain) StringSet.empty subst.arg_subst in
  let domain = List.fold_left (fun domain (var, _) -> StringSet.add var domain) domain subst.ms_subst in
  domain