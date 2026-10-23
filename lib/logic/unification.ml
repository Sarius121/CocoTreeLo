type conditioned_unifier = Substitution.t * Sat.expr
type unification_term = conditioned_unifier list

let id: unification_term = [(Substitution.empty, Sat.mk_bool true)]

(**
  {unify_instance args1 args2} tries to unify args1 and args2 where args2 contains no unknowns.
  To this end, it finds a substitution for unknowns in args1 and a condition s.t. args1 and args2 unify with the unifier subst if the condition cond holds.
  The resulting unifier and conditon is as general as possible, i.e. if cond = false, they don't unify.
*)
let unify_instance args1 args2 =
  let (subst, cond) = (List.fold_left2 (fun (subst, cond) arg1 arg2 ->
      match arg1 with
      | Arg_terms.Int (Unknown var) -> (match List.assoc_opt var subst with
        | Some value when value = arg2 -> (subst, cond)
        | Some value -> (subst, Sat.mk_eq (Arg_terms.to_smt value) (Arg_terms.to_smt arg2)::cond)
        | None -> ((var, arg2)::subst, cond)
        )
      | _ ->
        (* terms without unknowns *)
        (subst, Sat.mk_eq (Arg_terms.to_smt arg1) (Arg_terms.to_smt arg2)::cond)
    ) ([], []) args1 args2) in
  ({ Substitution.arg_subst = subst; ms_subst = [] }, Sat.mk_and cond)

let mk_const uni: unification_term = [uni]

let mk_or (unis: unification_term list) = List.flatten unis

let mk_and2 (uni1: unification_term) (uni2: unification_term) =
  List.fold_left (fun res (subst1, cond1) ->
      List.fold_left (fun res (subst2, cond2) ->
          (* add checks whether subst1 and subst2 can be unified *)
          let (subst, extra_cond) = Substitution.concat_with_dup
                (fun (var, val1) (_, val2) accu -> ((var, val1), Sat.mk_and [Sat.mk_eq (Arg_terms.to_smt val1) (Arg_terms.to_smt val2); accu]))
                (fun a b accu -> (a, accu))
                subst1 subst2 (Sat.mk_bool true) in
          (subst, Sat.mk_and [cond1; cond2; extra_cond])::res
        ) res uni2
    ) [] uni1

let mk_and (unis: unification_term list) = List.fold_left (fun res uni -> mk_and2 res uni) [(Substitution.empty, Sat.mk_bool true)] unis

let mk_and_smt (uni: unification_term) smt: unification_term = List.map (fun (subst, cond) -> (subst, Sat.mk_and [cond; smt])) uni

let filter_impossible unis: unification_term =
  List.filter (fun (subst, cond) -> not (Sat.is_unsat_opt cond = Some true)) unis

let unify_instance_in_ms instance1 instances2: unification_term =
  List.map (unify_instance instance1) instances2

(* unknowns only allowed in ms *)
let unify_subset ?(unknowns_in_sub=false) ms ms_sub: unification_term =
  let rec unify_fact_in_ms (fact_name1, args1) ms prefix: (unification_term * Multiset_rewrite_system.multiset) list =
    match ms with
    | (fact_name2, args2)::ms when fact_name1 = fact_name2 ->
        let unify_with_rest = unify_fact_in_ms (fact_name1, args1) ms (prefix @ [(fact_name2, args2)]) in
        let unify_with_this =
          if unknowns_in_sub then (mk_const (unify_instance args1 args2), prefix @ ms)
          else (mk_const (unify_instance args2 args1), prefix @ ms) in
        unify_with_this::unify_with_rest
    | fact2::ms -> unify_fact_in_ms (fact_name1, args1) ms (prefix @ [fact2])
    | [] -> []
  in
  let rec unify_subset' ms ms_sub =
    match ms_sub with
    | fact::ms_sub ->
      let unis = unify_fact_in_ms fact ms [] in
      mk_or (List.map (fun (uni, ms) ->
          let unis_rest = unify_subset' ms ms_sub in
          mk_and2 uni unis_rest
        ) unis)
    | [] -> id
  in
  unify_subset' ms ms_sub

let unify_subset_rest ?(unknowns_in_sub=false) ms ms_sub =
  let rec unify_fact_in_ms (fact_name1, args1) ms prefix: (unification_term * Multiset_rewrite_system.multiset) list =
    match ms with
    | (fact_name2, args2)::ms when fact_name1 = fact_name2 ->
        let unify_with_rest = unify_fact_in_ms (fact_name1, args1) ms (prefix @ [(fact_name2, args2)]) in
        let unify_with_this =
          if unknowns_in_sub then (mk_const (unify_instance args1 args2), prefix @ ms)
          else (mk_const (unify_instance args2 args1), prefix @ ms) in
        unify_with_this::unify_with_rest
    | fact2::ms -> unify_fact_in_ms (fact_name1, args1) ms (prefix @ [fact2])
    | [] -> []
  in
  let rec unify_subset' ms ms_sub =
    match ms_sub with
    | fact::ms_sub ->
      let unis = unify_fact_in_ms fact ms [] in
      List.concat_map (fun (uni, ms) ->
          let res_rest = unify_subset' ms ms_sub in
          List.map (fun (unis_rest, ms_rest) ->
              (mk_and2 uni unis_rest, ms_rest)
            ) res_rest
        ) unis
    | [] -> [(id, ms)]
  in
  unify_subset' ms ms_sub

let to_sat unis =
  let (_, cond) = List.split unis in
  Sat.mk_or cond

let to_string unis =
  let s = List.map (fun (subst, cond) -> Printf.sprintf "(%s, %s)" (Substitution.to_string subst) (Sat.to_string cond)) unis in
  String.concat ", " s

let%expect_test "test_unify_instance" =
  let instance = [Arg_terms.Int (Var "x")] in
  let instances = [[Arg_terms.Int (Var "a")]; [Int (Var "b")]] in
  let unis = unify_instance_in_ms instance instances in
  Printf.printf "%s\n" (to_string unis);
  [%expect {|([], (and (= x a))), ([], (and (= x b))) |}];

  let instance = [Arg_terms.Int (Unknown "u")] in
  let instances = [[Arg_terms.Int (Var "a")]; [Int (Var "b")]] in
  let unis = unify_instance_in_ms instance instances in
  Printf.printf "%s\n" (to_string unis);
  [%expect {| ([u->a], and), ([u->b], and)|}];
  ()

let%expect_test "test_mk_and" =
  let unis = mk_and [[(Substitution.empty, Sat.mk_bool true)]; [(Substitution.empty, Sat.mk_bool false)]] in
  Printf.printf "%s\n" (to_string unis);
  [%expect {|([], (and true true true false true)) |}]

let%expect_test "test_unify_subset" =
  let ms = [] in
  let ms_sub = [] in
  let unis = unify_subset ms ms_sub in
  Printf.printf "%s\n" (to_string unis);
  [%expect {|([], true) |}];

  let ms = [("P", [Arg_terms.Int (Unknown "a")]); ("P", [Int (Unknown "b")])] in
  let ms_sub = [("P", [Arg_terms.Int (Var "x")])] in
  let unis = unify_subset ms ms_sub in
  Printf.printf "%s\n" (to_string unis);
  [%expect {| ([a->x], (and and true true)), ([b->x], (and and true true)) |}];

  let ms = [("P", [Arg_terms.Int (Unknown "a")]); ("Q", [Int (Unknown "b")])] in
  let ms_sub = [("P", [Arg_terms.Int (Var "x")]); ("Q", [Int (Var "x")])] in
  let unis = unify_subset ms ms_sub in
  Printf.printf "%s\n" (to_string unis);
  [%expect {| ([a->x, b->x], (and and and true true true)) |}];

  let ms = [("P", [Arg_terms.Int (Const 5)]); ("Q", [Int (Unknown "b")])] in
  let ms_sub = [("P", [Arg_terms.Int (Var "x")]); ("Q", [Int (Var "x")])] in
  let unis = unify_subset ms ms_sub in
  Printf.printf "%s\n" (to_string unis);
  [%expect {| ([b->x], (and (= 5 x) and true true true)) |}]

let%expect_test "test_unify_subset_rest" =
  let ms = [] in
  let ms_sub = [] in
  let unis = unify_subset_rest ms ms_sub in
  List.iter (fun (unis, ms) -> Printf.printf "%s | %s\n" (to_string unis) (Multiset_rewrite_system.ms_to_string ms)) unis;
  [%expect {|([], true) | [] |}];

  let ms = [("P", [Arg_terms.Int (Unknown "a")]); ("P", [Int (Unknown "b")])] in
  let ms_sub = [("P", [Arg_terms.Int (Var "x")])] in
  let unis = unify_subset_rest ms ms_sub in
  List.iter (fun (unis, ms) -> Printf.printf "%s | %s\n" (to_string unis) (Multiset_rewrite_system.ms_to_string ms)) unis;
  [%expect {| 
    ([a->x], (and and true true)) | [P(b)]
    ([b->x], (and and true true)) | [P(a)]
    |}];

  let ms = [("P", [Arg_terms.Int (Unknown "a")]); ("P", [Arg_terms.Int (Unknown "c")]); ("Q", [Int (Unknown "b")])] in
  let ms_sub = [("P", [Arg_terms.Int (Var "x")])] in
  let unis = unify_subset_rest ms ms_sub in
  List.iter (fun (unis, ms) -> Printf.printf "%s | %s\n" (to_string unis) (Multiset_rewrite_system.ms_to_string ms)) unis;
  [%expect {| 
    ([a->x], (and and true true)) | [P(c), Q(b)]
    ([c->x], (and and true true)) | [P(a), Q(b)]
    |}];

