(* Multiset Terms *)

(** {(name, arguments)} *)
type fact = string * Arg_terms.term list
type multiset = fact list
type term = Var of string | Const of multiset | Union of term * term | Minus of term * term

let fact_to_string (name, args: fact) =
  let args_s = String.concat ", " (List.map Arg_terms.to_string args) in
  String.concat "" [name; "("; args_s; ")"]

let fact_to_detailed_string (name, args: fact) =
  let args_s = String.concat ", " (List.map Arg_terms.to_detailed_string args) in
  String.concat "" [name; "("; args_s; ")"]

let ms_to_string ms = "[" ^ (String.concat ", " (List.map fact_to_string ms)) ^ "]"

let ms_to_detailed_string ms = "[" ^ (String.concat ", " (List.map fact_to_detailed_string ms)) ^ "]"

let rec term_to_string term = match term with
    | Var var -> var
    | Const ms -> ms_to_string ms
    | Union (ms1, ms2) -> "(" ^ term_to_string ms1 ^ " u " ^ term_to_string ms2 ^ ")"
    | Minus (ms1, ms2) -> "(" ^ term_to_string ms1 ^ " \\ " ^ term_to_string ms2 ^ ")"

let rec term_to_smt term = match term with
  | Var var -> Sat.mk_ms_const var
  | Const [(fact_name, args)] -> Sat.mk_ms (fact_name, (List.map Arg_terms.to_smt args))
  | Const (fact::facts) -> term_to_smt (Union (Const [fact], Const facts))
  | Const [] -> Sat.mk_ms_empty
  | Union (ms1, ms2) -> Sat.mk_ms_union (term_to_smt ms1) (term_to_smt ms2)
  | Minus (ms1, ms2) -> Sat.mk_ms_minus (term_to_smt ms1) (term_to_smt ms2)

let rec term_subst_vars term subst subst_arg = match term with
  | Var var -> List.assoc_opt var subst |> Option.value ~default:term
  | Union (ms1, ms2) -> Union ((term_subst_vars ms1 subst subst_arg), (term_subst_vars ms2 subst subst_arg))
  | Minus (ms1, ms2) -> Minus ((term_subst_vars ms1 subst subst_arg), (term_subst_vars ms2 subst subst_arg))
  | Const ms -> Const (List.map (fun (fact, args) -> (fact, List.map (fun arg -> Arg_terms.subst_vars arg subst_arg) args)) ms)

let rec term_get_arg_vars term = match term with
    | Var var -> []
    | Const ms -> List.concat_map (fun (name, instance) -> List.concat_map (fun arg -> Arg_terms.vars arg) instance) ms
    | Union (ms1, ms2)
    | Minus (ms1, ms2) -> term_get_arg_vars ms1 @ term_get_arg_vars ms2

let rec term_get_ms_vars term = match term with
    | Var var -> [var]
    | Const ms -> []
    | Union (ms1, ms2)
    | Minus (ms1, ms2) -> term_get_ms_vars ms1 @ term_get_ms_vars ms2

let rec list_remove l x = match l with
  | x'::l when x = x' -> (true, l)
  | x'::l ->
    let (removed, rest) = list_remove l x in
    (removed, x'::rest)
  | [] -> (false, [])

(** Does *some* simplifications on the term (not the most simple representation) *)
let rec term_simplify term =
  match term with
  | Union (ms1, ms2) -> (match term_simplify ms1, term_simplify ms2 with
      | Const ms1, Const ms2 -> Const (ms1 @ ms2)
      | ms1, ms2 -> Union (ms1, ms2)
    )
  | Minus (ms1, ms2) -> (match term_simplify ms1, term_simplify ms2 with
      | Const ms1, Const ms2 ->
        let (success, res) = List.fold_left (fun (success, res) fact -> if success then list_remove res fact else (success, [])) (true, ms1) ms2 in
        if success then Const res
        else Minus (Const ms1, Const ms2)
      | ms1, ms2 -> Minus (ms1, ms2)
    )
  | _ -> term

(* Generate smt formulas for different situations *)

(** {gen_instance_eq_smt args1 args2} generates a formula encoding whether {args1 = args2} *)
let gen_instance_eq_smt args1 args2 =
  let eq_args = (List.map2 (fun arg1 arg2 -> Sat.mk_eq (Arg_terms.to_smt arg1) (Arg_terms.to_smt arg2)) args1 args2) in
  if eq_args = [] then Sat.mk_bool true else Sat.mk_and eq_args

(** {gen_fact_eq_smt fact1 fact2} generates a formula encoding whether {fact1 = fact2} *)
let gen_fact_eq_smt (name1, args1: fact) (name2, args2: fact) =
  if not (name1 = name2) then Sat.mk_bool false
  else gen_instance_eq_smt args1 args2

(** {gen_fact_in_ms ms fact} generates a formula encoding whether {fact} is contained in {ms} *)
let gen_fact_in_ms (ms: multiset) (fact: fact) =
  Sat.mk_or (List.map (gen_fact_eq_smt fact) ms)

(** Same as {gen_fact_in_ms}, but this function only takes the facts' arguments (without fact symbol) *)
let gen_instance_in_instances instances instance =
  Sat.mk_or (List.map (fun instance' -> gen_instance_eq_smt instance instance') instances)

(** Similar as {gen_instance_in_instances}, but this function returns with the number of matches for every possible match *)
let gen_instance_in_instances_n instances instance =
  List.fold_left (fun matchings instance' ->
      let eq = gen_instance_eq_smt instance instance' in
      List.concat_map (fun (matching, n) ->
          [(Sat.mk_and [Sat.mk_not eq; matching], n); (Sat.mk_and [eq; matching], n+1)]
        ) matchings
    ) [(Sat.mk_bool true, 0)] instances

(** {gen_subset_smt ms ms_sub} generates a formular encoding whether {ms_sub} is a subset of {ms} *)
let gen_subset_smt (ms: multiset) (ms_sub: multiset) =
  let rec all_matchings l1 x prefix = match l1 with
    | x1::l1 -> ((x1, x), prefix @ l1)::all_matchings l1 x (prefix @ [x1])
    | [] -> []
  in
  let rec gen_subset' l1 l2 = 
    match l2 with
    | x2::l2 ->
      let possible_matchings = all_matchings l1 x2 [] in
      if possible_matchings = [] then Sat.mk_bool false
      else
        Sat.mk_or (List.map (fun ((fact1, fact2), rest) ->
            let rec_matchings = gen_subset' rest l2 in
            Sat.mk_and [gen_fact_eq_smt fact1 fact2; rec_matchings]
          ) possible_matchings)
    | [] -> Sat.mk_bool true
  in
  gen_subset' ms ms_sub

let rec term_simplify_with_constraints term =
  let rec list_remove_with_constraints ms fact =
    match ms with
    | fact'::ms when fact = fact' -> [(Sat.mk_bool true, ms)]
    | fact'::ms ->
      let constraintt = gen_fact_eq_smt fact fact' in
      let other_possibilities = list_remove_with_constraints ms fact in
      let other_possibilities = (List.map (fun (c, ms) -> (c, fact'::ms)) other_possibilities) in
      if Sat.is_unsat constraintt then other_possibilities
      else (constraintt, ms)::other_possibilities
    | [] -> []
  in
  let rec term_simplify_with_constraints' term =
    match term with
    | Union (ms1, ms2) ->
      let possibilities1 = term_simplify_with_constraints' ms1 in
      let possibilities2 = term_simplify_with_constraints' ms2 in
      List.concat_map (fun (constraint1, ms1) -> List.map (fun (constraint2, ms2) -> 
          (Sat.mk_and [constraint1; constraint2], ms1 @ ms2)
        ) possibilities2) possibilities1
    | Minus (ms1, ms2) -> 
      let possibilities1 = term_simplify_with_constraints' ms1 in
      let possibilities2 = term_simplify_with_constraints' ms2 in
      List.concat_map (fun (constraint1, ms1) -> List.concat_map (fun (constraint2, ms2) ->
          List.fold_left (fun possibilities fact2 ->
              List.concat_map (fun (other_constraints, ms1) -> 
                  let possibilities = list_remove_with_constraints ms1 fact2 in
                  List.map (fun (constraintt, ms1) ->
                      (Sat.mk_and [constraintt; other_constraints], ms1)
                    ) possibilities
                ) possibilities
            ) [(Sat.mk_and [constraint1; constraint2], ms1)] ms2
        ) possibilities2) possibilities1
    | Const ms -> [(Sat.mk_bool true, ms)]
    | Var _ -> failwith "Var cannot be simplified"
  in
  List.map (fun (constraintt, ms) -> (constraintt, Const ms)) (term_simplify_with_constraints' term)

let gen_term_subset_smt (term: term) (term_sub: term) =
  let possibilities = term_simplify_with_constraints (Minus (term, term_sub)) in
  Sat.simplify (Sat.mk_or (List.map (fun (constraintt, _) -> constraintt) possibilities))

(**
  Generates an smt formula that checks whether term is valid.
  If the function does not fail, the formula is sound and complete.
*)
let rec gen_term_validity_smt term =
  let term = term_simplify term in
  match term with
  | Const ms -> Sat.mk_bool true
  | Minus (Const ms1, Const ms2) -> gen_subset_smt ms1 ms2
    (* |> fun res -> let () = Printf.printf "%s --> %s\n" (term_to_string term) (Sat.to_string res) in res *)
  | _ -> Sat.mk_bool false (*failwith "General term validity checking is not supported yet."*)

let rec is_subset ms ms_sub =
  match ms_sub with
  | [] -> true
  | fact::ms_sub ->
    let (succ, ms) = list_remove ms fact in
    if succ then is_subset ms ms_sub
    else false

let term_is_subset term term_sub =
  match term, term_sub with
  | Const ms, Const ms_sub -> is_subset ms ms_sub
  | _ -> failwith "General term validity checking is not supported yet."

(** 
  {get_possible_removals ms1 ms2} yields all possibilities of removing ms2 from ms1, where only as much elements are removed as possible.
  This is basically getting all possibile leftover of ms1 in the term (M cup ms1) minus ms2, where M can be anything.
  Unfortunately not!
*)
let rec get_possible_removals ms1 ms2 =
  let rec list_remove_with_constraints ms (fact_name, instance) acc_cond =
    match ms with
    | (fact_name', instance')::ms when fact_name = fact_name' ->
      if instance = instance' then [(Sat.mk_bool true, ms)]
      else
        let constraintt = gen_instance_eq_smt instance instance' in
        let other_possibilities = list_remove_with_constraints ms (fact_name, instance) (Sat.mk_and [Sat.mk_not constraintt; acc_cond]) in
        let other_possibilities = List.map (fun (c, ms) -> (c, (fact_name', instance')::ms)) other_possibilities in
        if Sat.is_unsat constraintt then other_possibilities
        else (Sat.mk_and [constraintt; acc_cond], ms)::other_possibilities
    | fact'::ms ->
      let other_possibilities = list_remove_with_constraints ms (fact_name, instance) acc_cond in
      List.map (fun (c, ms) -> (c, fact'::ms)) other_possibilities
    | [] -> [(acc_cond, [])]
  in
  List.fold_left (fun possibilities fact2 ->
      List.concat_map (fun (other_constraints, ms1) -> 
          let possibilities = list_remove_with_constraints ms1 fact2 (Sat.mk_bool true) in
          List.map (fun (constraintt, ms1) ->
              (Sat.mk_and [constraintt; other_constraints], ms1)
            ) possibilities
        ) possibilities
    ) [(Sat.mk_bool true, ms1)] ms2

let rec gen_nothing_removed ms ms_removed =
  Sat.mk_and (List.map (fun fact -> Sat.mk_not (gen_fact_in_ms ms_removed fact)) ms)

(* Multiset Rewrite Systems *)

(** {(name, left, right, action_facts)} *)
type rule = string * multiset * multiset * multiset
(** {(name, rules)} *)
type msrs = string * rule list
(** multiset structured by fact symbol *)
type structured_ms = (string * Arg_terms.term list list) list

let msrs_to_string (name, rules: msrs) =
  let rules_s = List.map (fun (name, facts_l, facts_r, action_facts) ->
      let facts_l_s = ms_to_string facts_l in
      let facts_r_s = ms_to_string facts_r in
      let action_facts_s = ms_to_string action_facts in
      String.concat "" [name; ": "; facts_l_s; " --"; action_facts_s; "-> "; facts_r_s]
    ) rules in
  let name_s = String.cat name ":" in
  String.concat "\n" (name_s::rules_s)

(** get all fact symbols that appear in [msrs] together with their arity *)
let get_fact_symbols (_, rules: msrs) =
  let module StringIntSet = Set.Make(struct
    type t = string * int
    let compare = Repr.compare
  end) in
  let all_facts = List.fold_left (fun all_facts (name, left, right, action) -> 
      let all_facts = List.fold_left (fun all_facts (name, args) -> StringIntSet.add (name, List.length args) all_facts) all_facts left in
      let all_facts = List.fold_left (fun all_facts (name, args) -> StringIntSet.add (name, List.length args) all_facts) all_facts right in
      let all_facts = List.fold_left (fun all_facts (name, args) -> StringIntSet.add (name, List.length args) all_facts) all_facts action in
      all_facts
    ) StringIntSet.empty rules in
  StringIntSet.to_list all_facts

let ms_to_structured (ms: multiset): structured_ms =
  let sorted_ms = List.sort Repr.compare ms in
  let structured_ms = List.fold_left (fun structured_ms (fact, args) ->
    match structured_ms with
    | (fact', instances)::l2 when fact' = fact -> (fact', args::instances)::l2
    | l -> (fact, [args])::l
  ) [] (List.rev sorted_ms) in
  structured_ms

let%expect_test "test_simplify_with_constraints" =
  let term = Minus (Const [("P", [Arg_terms.(Int (Var "x"))])], Const [("P", [Arg_terms.(Int (Const 5))])]) in
  let simplifications = term_simplify_with_constraints term in
  Printf.printf "%s\n" (String.concat " | " (List.map (fun (constraintt, ms) -> Sat.to_string constraintt ^ ", " ^ term_to_string ms) simplifications));
  [%expect {|(and (= 5 x) true true), []|}];

  let term = Minus (Const [("P", [Arg_terms.(Int (Var "x"))]); ("P", [Arg_terms.(Int (Var "y"))]); ("Q", [Arg_terms.(Int (Var "x"))])], Const [("P", [Arg_terms.(Int (Const 5))])]) in
  let simplifications = term_simplify_with_constraints term in
  Printf.printf "%s\n" (String.concat " | " (List.map (fun (constraintt, ms) -> Sat.to_string constraintt ^ ", " ^ term_to_string ms) simplifications));
  [%expect {|(and (= 5 x) true true), [P(y), Q(x)] | (and (= 5 y) true true), [P(x), Q(x)]|}];

  let term = Minus (Minus (Const [("P", [Arg_terms.(Int (Var "x"))])], Const [("P", [Arg_terms.(Int (Var "y"))])]), Const [("P", [Arg_terms.(Int (Var "z"))])]) in
  let simplifications = term_simplify_with_constraints term in
  Printf.printf "%s\n" (String.concat " | " (List.map (fun (constraintt, ms) -> Sat.to_string constraintt ^ ", " ^ term_to_string ms) simplifications));
  [%expect {| |}]

let%expect_test "test_term_subset_smt" =
  let term = Const [("P", [Arg_terms.(Int (Var "x"))])] in
  let term_sub = Minus (Const [("Q", [Arg_terms.(Int (Var "x"))])], Const [("Q", [Arg_terms.(Int (Const 5))])]) in
  let term_is_subset = gen_term_subset_smt term term_sub in
  Printf.printf "%s\n" (Sat.to_string term_is_subset);
  [%expect {|(= 5 x)|}];

  let term = Const [("P", [Arg_terms.(Int (Var "x"))])] in
  let term_sub = Minus (Const [("P", [Arg_terms.(Int (Var "x"))]); ("P", [Arg_terms.(Int (Var "y"))])], Const [("P", [Arg_terms.(Int (Const 5))])]) in
  let term_is_subset = gen_term_subset_smt term term_sub in
  Printf.printf "%s\n" (Sat.to_string term_is_subset);
  [%expect {|(or (= 5 y) (and (= y x) (= 5 x)))|}];
  
  let term = Minus (Const [("P", [Arg_terms.(Int (Var "x"))])], Const [("P", [Arg_terms.(Int (Const 5))])]) in
  let term_sub = Const [("P", [Arg_terms.(Int (Const 5))])] in
  let term_is_subset = gen_term_subset_smt term term_sub in
  Printf.printf "%s\n" (Sat.to_string term_is_subset);
  [%expect {|false|}]

let%expect_test "test_instance_in_instances_n" =
  let open Arg_terms in
  let instance = [Int (Var "x")] in
  let instances = [[Int (Var "a")]; [Int (Var "b")]] in
  let res = gen_instance_in_instances_n instances instance in
  Printf.printf "%s\n" (String.concat " | " (List.map (fun (smt, n) -> Printf.sprintf "(%s, %d)" (Sat.to_string (Sat.simplify smt)) n) res));
  [%expect {|((and (not (= x b)) (not (= x a))), 0) | ((and (= x b) (not (= x a))), 1) | ((and (not (= x b)) (= x a)), 1) | ((and (= x b) (= x a)), 2) |}]

let%expect_test "test_get_possible_removals" =
  let open Arg_terms in
  let ms = [("P", [Int (Var "a")]); ("P", [Int (Var "b")])] in
  let removed = [("P", [Int (Var "v0")]); ("P", [Int (Var "v1")])] in
  let res = get_possible_removals ms removed in
  Printf.printf "%s\n" (String.concat "\n" (List.map (fun (constraintt, ms) -> Sat.to_string (Sat.simplify constraintt) ^ ", " ^ ms_to_string ms) res));
  [%expect {| 
    (and (= v1 b) (= v0 a)), []
    (and (not (= v1 b)) (= v0 a)), [P(b)]
    (and (= v1 a) (= v0 b) (not (= v0 a))), []
    (and (not (= v1 a)) (= v0 b) (not (= v0 a))), [P(a)]
    (and (= v1 a) (not (= v0 b)) (not (= v0 a))), [P(b)]
    (and (= v1 b) (not (= v1 a)) (not (= v0 b)) (not (= v0 a))), [P(a)]
    (and (not (= v1 b)) (not (= v1 a)) (not (= v0 b)) (not (= v0 a))), [P(a), P(b)] 
    |}]
