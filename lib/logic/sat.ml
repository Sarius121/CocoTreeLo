open Utils

(** TODO: handling this as a context might be dangerous (at least in concurrent settings) *)
let ctx = Z3.mk_context []

type expr = Z3.Expr.expr * string list

let to_z3 = fst

let to_string (smt, _) = Z3.Expr.to_string smt

let sort_ms = Z3.Sort.mk_uninterpreted_s ctx "Multiset"
let sort_int = Z3.Arithmetic.Integer.mk_sort ctx
let sort_bool = Z3.Boolean.mk_sort ctx
let is_bool_var var = (String.get var 0 >= 'A') && (String.get var 0 <= 'Z')
let mk_z3_var var =
  if is_bool_var var then 
    if String.ends_with ~suffix:"*" var then
      Z3.Expr.mk_const_s ctx var sort_ms
    else
      Z3.Boolean.mk_const_s ctx var
  else Z3.Arithmetic.Integer.mk_const_s ctx var
let mk_var var = (mk_z3_var var, [])
(* an unknown Boolean that depends on the nondeterministic (integer) values [args]: an unknown function *)
let mk_bool_app name args =
  let decl = Z3.FuncDecl.mk_func_decl_s ctx name (List.map (fun _ -> sort_int) args) sort_bool in
  (Z3.Expr.mk_app ctx decl (List.map mk_z3_var args), [])
let mk_var_sort var sort = (Z3.Expr.mk_const_s ctx var sort, [])
let mk_int c = (Z3.Arithmetic.Integer.mk_numeral_i ctx c, [])
let mk_bool c = (Z3.Boolean.mk_val ctx c, [])

let make_unknowns_unique smts =
  let ((all_new_unknowns, _), smts) = List.fold_left_map (fun (all_new_unknowns, counter) (smt, unknown_vars) -> 
      let unknowns_num = List.length unknown_vars in
      let new_unknowns = List.init unknowns_num (fun i -> Printf.sprintf "Unknown%d" (counter + i)) in
      let new_unknowns_smt = List.map (fun unknown -> Z3.Boolean.mk_const_s ctx unknown) new_unknowns in
      let subst_smt = (Z3.Expr.substitute smt (List.map (fun var -> to_z3 (mk_var var)) unknown_vars) new_unknowns_smt) in
      ((new_unknowns@all_new_unknowns, counter + unknowns_num), subst_smt)
    ) ([], 0) smts in
  (smts, all_new_unknowns)

let mk_and smts =
  let (smts, unknown_vars) = make_unknowns_unique smts in
  (Z3.Boolean.mk_and ctx smts, unknown_vars)
let mk_or smts =
  let (smts, unknown_vars) = make_unknowns_unique smts in
  (Z3.Boolean.mk_or ctx smts, unknown_vars)
let mk_not (smt, unknown_vars) = (Z3.Boolean.mk_not ctx smt, unknown_vars)
let mk_eq smt1 smt2 =
  let (smts, unknown_vars) = make_unknowns_unique [smt1; smt2] in
  match smts with
  | [smt1; smt2] -> (Z3.Boolean.mk_eq ctx smt1 smt2, unknown_vars)
  | _ -> failwith "Illegal program state in Sat.mk_eq"
let mk_quantifier_multi universal vars (smt, unknown_vars) =
  if vars = [] then (smt, unknown_vars)
  else
    (Z3.Quantifier.expr_of_quantifier (Z3.Quantifier.mk_quantifier_const ctx universal (List.map (fun var -> mk_z3_var var) vars) smt None [] [] None None), unknown_vars)
let mk_quantifier universal var (smt, unknown_vars) = (Z3.Quantifier.expr_of_quantifier (Z3.Quantifier.mk_quantifier_const ctx universal [(mk_z3_var var)] smt None [] [] None None), unknown_vars)
let mk_forall var smt = mk_quantifier true var smt
let mk_exists var smt = mk_quantifier false var smt
let mk_forall_multi vars smt = mk_quantifier_multi true vars smt
let mk_exists_multi vars smt = mk_quantifier_multi false vars smt
let hide smt =
  let s = to_string smt in
  let s = String.map (fun c -> match c with
      | '(' -> '#'
      | ')' -> '$'
      | ' ' -> '@'
      | '#' | '$' -> failwith "Cannot hide\n" (* actually hiding is also risky if an @ appears, but @ appears often*)
      | _ -> c
    ) s in
  (mk_var ("Hide" ^ s), s)

(* function applications *)

(** get all applications in [smt] of function symbols whose name starts with [prefix], as [(name, application)] *)
let get_apps_with_prefix prefix (smt, _) =
  let rec collect acc e =
    let ast = Z3.Expr.ast_of_expr e in
    if Z3.AST.is_var ast then acc
    else if Z3.AST.is_quantifier ast then collect acc (Z3.Quantifier.get_body (Z3.Quantifier.quantifier_of_expr e))
    else
      let acc = List.fold_left collect acc (Z3.Expr.get_args e) in
      let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)) in
      if String.starts_with ~prefix name && not (List.exists (fun (_, e') -> Z3.Expr.equal e e') acc) 
        then (name, e)::acc
        else acc
  in
  collect [] smt

(** replace the applications [apps] by the Boolean constants [names] *)
let replace_apps_by_vars (smt, unknown_vars) apps names =
  (Z3.Expr.substitute smt apps (List.map mk_z3_var names), unknown_vars)

(** replace the applications [apps] by the Boolean [value] *)
let subst_apps (smt, unknown_vars) apps value =
  (Z3.Expr.substitute smt apps (List.map (fun _ -> Z3.Boolean.mk_val ctx value) apps), unknown_vars)

(** substitute var by e in smt, i.e. returns [smt[var->e]] *)
let subst_var smt var e =
  match make_unknowns_unique [smt; e] with
  | ([smt; e], unknown_vars) -> (Z3.Expr.substitute_one smt (to_z3 (mk_var var)) e, unknown_vars)
  | _ -> failwith "Illegal program state in Sat.subst_var"
let subst_vars smt vars exprs =
  let () = Utils.Monitoring.start_event "subst_vars" in
  (* let () = Printf.printf "%s : %s\n" (to_string smt) (String.concat "," (List.map2 (fun var e -> var ^ "->" ^ to_string e) vars exprs)) in *)
  (match make_unknowns_unique (smt::exprs) with
  | (smt::exprs, unknown_vars) -> (Z3.Expr.substitute smt (List.map (fun var -> to_z3 (mk_var var)) vars) exprs, unknown_vars)
  | _ -> failwith "Illegal program state in Sat.subst_var")
  |> fun x -> Utils.Monitoring.stop_event "subst_vars"; x

let instantiate_unknown_vars (smt, unknown_vars) =
  let () = if unknown_vars = [] then () else Printf.printf "WARNING: There are unknown vars!\n" in
  let unknown_vars = List.map (fun var -> mk_z3_var var) unknown_vars in
  let inst_vars = List.map (fun _ -> Z3.Expr.mk_fresh_const ctx "IUnknown" (Z3.Boolean.mk_sort ctx)) unknown_vars in
  (Z3.Expr.substitute smt unknown_vars inst_vars, [])

let simplify (smt, unknown_vars) =
  let () = Monitoring.start_event "simplify" in
  (Z3.Expr.simplify smt None, unknown_vars)
  |> fun smt -> Monitoring.stop_event "simplify"; smt

(** TODO this is still a bit sketchy *)
let get_vars s =
  let is_smt_name x = match x with
    | "assert" | "or" | "and" | "false" | "true" | "not"
    | "forall" | "exists" | "Int" | "Bool" | "INT2BOOL"
    | "declare" | "fun" -> true
    | _ -> false
  in
  let find_all_ignore_first_char regex s =
    let regex = Str.regexp regex in
    let split = Str.full_split regex s in
    List.filter_map (fun elem -> match elem with
      | Str.Text _ -> None
      | Str.Delim var -> 
        let var = String.sub var 1 (String.length var - 1) in
        if is_smt_name var then None else Some var) split
  in
  (* TODO We shouldn't have any labels anymore. Remove following code!? *)
  let bool_vars =
    let regexLabel = "[^A-Za-z0-9][A-Z][A-Za-z0-9]*" in
    Str_utils.StringSet.of_list (find_all_ignore_first_char regexLabel s)
  in
  let int_vars =
    let regexVars = "[^A-Za-z0-9][a-z][A-Za-z0-9]*" in
    Str_utils.StringSet.of_list (find_all_ignore_first_char regexVars s)
  in
  (Str_utils.StringSet.to_list bool_vars, Str_utils.StringSet.to_list int_vars)

let parse_smt s bool =
  (* let () = if bool then () else Printf.printf "%s\n" s in *)
  let s = if bool then "(assert " ^ s ^ ")" else "(declare-fun INT2BOOL (Int) Bool)\n(assert (INT2BOOL " ^ s ^ "))" in
  let (bool_vars, int_vars) = get_vars s in
  let smt_decl_bool = String.concat "\n" (List.map (fun var -> Printf.sprintf "(declare-fun %s () Bool)" var) bool_vars) in
  let smt_decl_int = String.concat "\n" (List.map (fun var -> Printf.sprintf "(declare-fun %s () Int)" var) int_vars) in
  let input = smt_decl_bool ^ "\n" ^ smt_decl_int ^ "\n" ^ s in
  let smt = Z3.SMT.parse_smtlib2_string ctx input [] [] [] [] in
  let smt = if bool then smt else smt in
  let smt = match Z3.AST.ASTVector.to_expr_list smt with
  | [smt] -> smt
  | _ -> failwith (Printf.sprintf "Parsing smtlib2 expression \"%s\" failed" s) in
  if bool then (smt, [])
  else match Z3.Expr.get_args smt with
    | [smt] -> (smt, [])
    | _ -> failwith (Printf.sprintf "Parsing smtlib2 expression \"%s\" failed" s)

(* one solver for all satisfiability checks; each check runs between push and pop *)
let shared_solver = lazy (
    Z3.Solver.mk_solver ctx None
    (* |> fun solver ->
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "solver2_timeout") 1;
      Z3.Solver.set_parameters solver params;
      solver *)
  )

(** 
  always resets the solver before adding a goal
  if push and pop are used, the solver2_timeout has to be set above -> otherwise often non-terminating
*)
let check_shared smt =
  let solver = Lazy.force shared_solver in
  Z3.Solver.reset solver;
  (* Z3.Solver.push solver; *)
  Z3.Solver.add solver [smt];
  let res = Z3.Solver.check solver [] in
  (* Z3.Solver.pop solver 1; *)
  res

let is_unsat (smt, unknown_vars) =
  (* let () = if unknown_vars = [] then () else Printf.printf "unknowns\n" in *)
  let () = Monitoring.start_event "is_unsat" in
  let smt_res = check_shared smt in
  let () = if smt_res = Z3.Solver.UNKNOWN then (Printf.printf "Unknown\n"; flush stdout) else () in
  let () = Monitoring.stop_event "is_unsat" in
  smt_res = Z3.Solver.UNSATISFIABLE

let is_unsat_opt (smt, _) =
  let () = Monitoring.start_event "is_unsat_opt" in
  let smt_res = check_shared smt  in
  (* let solver = Z3.Solver.mk_solver ctx None in
  let () = Z3.Solver.add solver [smt] in
  let smt_res = Z3.Solver.check solver [] in *)
  let () = if smt_res = Z3.Solver.UNKNOWN then (Printf.printf "Unknown\n"; flush stdout) else () in
  let () = Monitoring.stop_event "is_unsat_opt" in
  match smt_res with
  | Z3.Solver.SATISFIABLE -> Some false
  | Z3.Solver.UNSATISFIABLE -> Some true
  | Z3.Solver.UNKNOWN -> None

let is_eq smt1 smt2 = is_unsat (mk_not (mk_eq smt1 smt2))

let is_true_opt smt = is_unsat_opt (mk_not smt)

let is_sat_model ?(side_constraint=mk_bool true) smt =
  let side_constraint = to_z3 side_constraint in
  (* let () = Printf.printf ";---\n(assert (not %s))\n;---\n" (to_string smt) in *)
  let smt = to_z3 smt in
  let () = Monitoring.start_event "is_true_model" in
  let z3_solver = Z3.Solver.mk_solver ctx None in
  let () = Z3.Solver.add z3_solver [side_constraint] in
  let () = Z3.Solver.add z3_solver [smt] in
  let smt_res = Z3.Solver.check z3_solver [] in
  let () = Monitoring.stop_event "is_true_model" in
  match smt_res with
  | Z3.Solver.SATISFIABLE ->
    let model = Option.get (Z3.Solver.get_model z3_solver) in
    let decls = Z3.Model.get_const_decls model in
    let mapped_model = List.map (fun decl -> 
        let var = Z3.Symbol.get_string (Z3.FuncDecl.get_name decl) in
        let value = Option.get (Z3.Model.get_const_interp model decl) in
        (* let () = Printf.printf "; %s->%s\n" var (to_string (value, [])) in *)
        (var, (value, []))
      ) decls in
    Some mapped_model
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.UNKNOWN -> failwith "Expected concrete result, got unknown."

let is_sat_model_soft ?(side_constraint=mk_bool true) smt soft_constraint =
  let side_constraint = to_z3 side_constraint in
  let soft_constraint = to_z3 soft_constraint in
  (* let () = Printf.printf ";---\n(assert (not %s))\n;---\n" (to_string smt) in *)
  let smt = to_z3 smt in
  let () = Monitoring.start_event "is_true_model_soft" in
  let z3_opt = Z3.Optimize.mk_opt ctx in
  let _ = Z3.Optimize.add_soft z3_opt soft_constraint "1" (Z3.Symbol.mk_string ctx "") in
  let () = Z3.Optimize.add z3_opt [side_constraint] in
  let () = Z3.Optimize.add z3_opt [smt] in
  let smt_res = Z3.Optimize.check z3_opt in
  let () = Monitoring.stop_event "is_true_model_soft" in
  match smt_res with
  | Z3.Solver.SATISFIABLE ->
    let model = Option.get (Z3.Optimize.get_model z3_opt) in
    let decls = Z3.Model.get_const_decls model in
    let mapped_model = List.map (fun decl -> 
        let var = Z3.Symbol.get_string (Z3.FuncDecl.get_name decl) in
        let value = Option.get (Z3.Model.get_const_interp model decl) in
        (* let () = Printf.printf "; %s->%s\n" var (to_string (value, [])) in *)
        (var, (value, []))
      ) decls in
    Some mapped_model
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.UNKNOWN -> failwith "Expected concrete result, got unknown."

(** multiset stuff *)
let ms_sort = Z3.Sort.mk_uninterpreted_s ctx "Multiset"
let ms_union = Z3.FuncDecl.mk_func_decl_s ctx "union" [ms_sort; ms_sort] ms_sort
let ms_minus = Z3.FuncDecl.mk_func_decl_s ctx "minus" [ms_sort; ms_sort] ms_sort
let mk_ms_empty = (Z3.FuncDecl.apply (Z3.FuncDecl.mk_const_decl_s ctx "empty" ms_sort) [], [])
let mk_ms_union (ms1, _) (ms2, _) = (Z3.FuncDecl.apply ms_union [ms1; ms2], [])
let mk_ms_minus (ms1, _) (ms2, _) = (Z3.FuncDecl.apply ms_minus [ms1; ms2], [])
let mk_ms (fact_name, args) =
  let args = List.map (fun (smt, _) -> smt) args in
  let args_sorts = List.map (fun _ -> Z3.Arithmetic.Integer.mk_sort ctx) args in
  let f = Z3.FuncDecl.mk_func_decl_s ctx fact_name args_sorts ms_sort in
  (Z3.FuncDecl.apply f args, [])
let mk_ms_const var = (Z3.Expr.mk_const_s ctx var ms_sort, [])

let%expect_test "test_simplify_smt" =
  let smt = parse_smt "(and true false)" true in
  Printf.printf "%s" (to_string (simplify smt));
  [%expect {| false |}];
  let smt = parse_smt "(and true (= x 5))" true in
  Printf.printf "%s" (to_string (simplify smt));
  [%expect {| (= x 5) |}]

let%expect_test "native_z3_subst" =
  let smt = "(declare-fun x () Int) (assert (= 6 (forall ((x Int)) (= x 5))))" in
  let z3_ctx = Z3.mk_context [] in
  let smt = Z3.SMT.parse_smtlib2_string z3_ctx smt [] [] [] [] in
  let smt = Z3.AST.ASTVector.to_expr_list smt in
  let smt = match smt with
    | [smt] -> smt
    | _ -> failwith "something went wrong"
  in
  let subst = Z3.Expr.substitute smt [Z3.Arithmetic.Integer.mk_const_s z3_ctx "x"] [Z3.Arithmetic.Integer.mk_numeral_i z3_ctx 4] in
  Printf.printf "%s" (Z3.Expr.to_string subst);
  [%expect {| (= 6 (ite (forall ((x Int)) (= x 5)) 1 0)) |}]

let%expect_test "native_z3_subst2" =
  let smt = mk_eq (mk_forall "y" (mk_eq (mk_var "y") (mk_var "x"))) (mk_forall "x" (mk_eq (mk_var "x") (mk_int 5))) in
  (* let smt = "(declare-fun x () Int) (assert (= 6 (forall ((x Int)) (= x 5))))" in *)
  let subst = subst_var smt "x" (mk_int 4) in
  Printf.printf "%s" (to_string subst);
  [%expect {| (= (forall ((y Int)) (= y 4)) (forall ((x Int)) (= x 5))) |}]

let%expect_test "test_parallel_subst" =
  let smt = mk_eq (mk_var "x") (mk_var "y") in
  let subst = subst_vars smt ["x"; "y"] [mk_var "y"; mk_var "x"] in
  Printf.printf "%s" (to_string subst);
  [%expect {| (= y x) |}]

let%expect_test "parse_smt" =
  let input = "(and true false)" in
  let smt = parse_smt input true in
  Printf.printf "%s" (to_string smt);
  [%expect {| (and true false) |}];
  let input = "(+ p 5)" in
  let smt = parse_smt input false in
  Printf.printf "%s" (to_string smt);
  [%expect {| (+ p 5) |}]

(* test whether forall actually binds the variables correctly *)
let%expect_test "test_mk_forall" =
  let smt = mk_forall "x" (mk_eq (mk_var "x") (mk_int 5)) in
  Printf.printf "%B" (is_unsat smt);
  [%expect {| true |}]

(* test whether we can capture variables inside forall
  -> luckily not (otherwise soundness would probably be broken)
  -> but it is not really visible, so we have to be careful
*)
let%expect_test "test_capture_vars" =
  let smt = mk_forall "x" (mk_var "PMx") in
  let expr = mk_eq (mk_var "x") (mk_int 5) in
  let ref = mk_forall "x" expr in
  let res = subst_var smt "PMx" expr in
  Printf.printf "%s" (to_string res);
  [%expect {| (forall ((x Int)) (= x 5)) |}];
  Printf.printf "%B" (is_unsat res);
  [%expect {| false |}];
  Printf.printf "%B" (is_unsat ref);
  [%expect {| true |}]

let%expect_test "test_simplify_exists" =
  let smt = parse_smt "(exists ((x Int)) (= x y))" true in
  Printf.printf "%s -> %s" (to_string smt) (to_string (simplify smt));
  [%expect {| (exists ((x Int)) (= x y)) -> true |}];
  let smt = parse_smt "(exists ((x Int)) (and (= x y) (= x z)))" true in
  Printf.printf "%s -> %s" (to_string smt) (to_string (simplify smt));
  [%expect {| (exists ((x Int)) (and (= x y) (= x z))) -> (= z y) |}]

let%expect_test "test_model" =
  let smt = parse_smt "(and (= x 5) (= x y))" true in
  let model = Option.get (is_sat_model (mk_not smt)) in
  let model_s = String.concat ", " (List.map (fun (var, value) -> var ^ "->" ^ to_string value) model) in
  Printf.printf "%s" model_s;
  [%expect {| x->6, y->5 |}]
