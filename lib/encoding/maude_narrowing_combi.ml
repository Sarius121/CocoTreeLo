open Logic

(* helper functions for giving names to star vars and similar *)

let is_star_var name = String.ends_with name ~suffix:"*"
let get_star_var name = name ^ "*"
let get_star_fact (name, args) = (get_star_var name, args)
let get_fact_name_of_star_var star_var = String.sub star_var 0 (String.length star_var - 1)
let track_var_to_string ms = "Track*_" ^ String.concat "_" (List.map (fun (fact_name, args) ->
    let args_s = String.concat "_" (List.map Arg_terms.to_string args) in
    fact_name ^ "_" ^ args_s
  ) ms)
let get_fact_maude_sort name = name ^ "Fact"
let encode_stars input =
  let len = String.length input in
  if String.get input (len - 1) = '*' then
    String.sub input 0 (len - 1) ^ "M"
  else input

(** fact names, instances, the name of the star-variable *)
type facts_of_type = string * Arg_terms.term list list * string option
type structured_ms = facts_of_type list
type constraints = (Multiset_rewrite_system.multiset * bool) list

module State = struct
  (** (S, C) S = multiset term, C = constraint *)
  type t = structured_ms * constraints
  (* the constraints as a binary number *)
  (* let hash (ms, constraints) = List.fold_left (fun hash (_, value) -> hash * 2 + (if value then 1 else 0)) 0 constraints *)
  let hash s = Hashtbl.hash_param 256 4096 s (* proposed by AI -> check whether that's really better *)
  let to_string (ms, constraints: t) =
    let ms_str = String.concat ", " (List.concat_map (fun (fact, instances, p_star) ->  
        let suffix = Option.fold ~none:[] ~some:(fun p_star -> [p_star]) p_star in
        List.map (fun instance -> Multiset_rewrite_system.fact_to_string (fact, instance)) instances @ suffix
      ) ms) in
    let constraints_s = String.concat " && " (List.map (fun (star_instance, value) ->
        let star_var = track_var_to_string star_instance in
        if value then star_var else "!" ^ star_var
      ) (constraints)) in
    "[" ^ ms_str ^ "] where " ^ constraints_s
  let to_multiset (ms, _: t) = List.fold_left (fun term (fact, instances, star_fact) ->
      let new_term = let instances_ms = Multiset_rewrite_system.Const (List.map (fun instance -> (fact, instance)) instances) in
        match star_fact with
        | Some star_fact -> Multiset_rewrite_system.Union (instances_ms, Multiset_rewrite_system.Var star_fact)
        | None -> instances_ms
      in
      Multiset_rewrite_system.Union (term, new_term)
    ) (Multiset_rewrite_system.Const []) ms
  let get_constraints (_, constraints) = constraints
end

module Kripke = Kripke.Make(State)
type state = Kripke.state

(** converts a state into a string that fits the maude syntax *)
let structured_ms_to_maude_string (ms: structured_ms) =
  String.concat " ; " (List.map (fun (fact, instances, p_star) ->  
    let suffix = Option.fold ~none:[] ~some:(fun p_star -> [(encode_stars p_star) ^ ":" ^ get_fact_maude_sort fact]) p_star in
    let fact_s =
      String.concat ", " (List.map (fun instance -> 
          let instance_s = String.concat " " (List.map (fun arg -> match arg with
            | Arg_terms.(Int Var arg) -> arg ^ ":Int"
            | arg -> Arg_terms.to_string arg) instance) in
          "(" ^ fact ^ " " ^ instance_s ^ ")"
        ) instances @ suffix) in
    if fact_s = "" then "no" ^ fact else fact_s
  ) ms)

(* generate contexts *)

type structured_rule = string * structured_ms * structured_ms * structured_ms
type structured_msrs = string * structured_rule list

let is_action_fact (_, rules) fact_name =
  let res = List.find_map (fun (_, l, r, action) ->
      let is_action = Option.is_some (List.find_opt (fun (fact_name', _) -> fact_name = fact_name') action) in
      let is_not_action = Option.is_some (List.find_opt (fun (fact_name', _) -> fact_name = fact_name') l)
          || Option.is_some (List.find_opt (fun (fact_name', _) -> fact_name = fact_name') r) in
      match is_action, is_not_action with
      | true, false -> Some true
      | false, true -> Some false
      | false, false -> None
      | _ -> failwith (Printf.sprintf "A fact cannot be an action fact and a state fact at the same time: %s." fact_name)
    ) rules in
  let () = if res = None then Printf.printf "WARNING: The property contains facts that are not present in the MSRS.\n" in
  Option.value ~default:false res

let gen_structured_msrs (name, rules: Multiset_rewrite_system.msrs) all_facts: structured_msrs =
  let all_facts = List.sort Repr.compare all_facts in
  let rule_ms_to_structured_state ms all_facts is_action_fact : structured_ms =
    let sorted_ms = List.sort Repr.compare ms in
    let structured_state = List.fold_left (fun structured_state (fact, args) ->
      match structured_state with
      | (fact', instances, p_star)::l2 when fact' = fact -> (fact', args::instances, p_star)::l2
      | l -> (fact, [args], if is_action_fact then None else Some (get_star_var fact))::l
    ) [] (List.rev sorted_ms) in
    let complete_state = List.map (fun (fact, _) -> Option.value ~default:(fact, [], if is_action_fact then None else Some (get_star_var fact)) (List.find_opt (fun (fact', _, _) -> fact = fact') structured_state)) all_facts in
    complete_state
  in
  (name, List.map (fun (name, l, r, action) ->
    let (state_facts, action_facts) = List.fold_left (fun (state_facts, action_facts) (fact_name, args) ->
      if is_action_fact (name, rules) fact_name then (state_facts, (fact_name, args)::action_facts)
      else ((fact_name, args)::state_facts, action_facts)) ([], []) all_facts in
    (name, rule_ms_to_structured_state l all_facts false, rule_ms_to_structured_state r state_facts false, rule_ms_to_structured_state action action_facts true)) rules)

let gen_maude_context (_, rules: structured_msrs) all_facts =
  let sorts_s = String.concat " " (List.map (fun (name, _) -> get_fact_maude_sort name) all_facts) in
  let fact_decl_s =
    let underscores = String.concat ";" (List.map (fun _ -> "_") all_facts) in
    Printf.sprintf "op <%s> : %s -> State ." underscores sorts_s in
  let all_facts_s = List.fold_left (fun s (name, arg_count) ->
      let underscores = String.init arg_count (fun _ -> '_') in
      let vars = String.concat " " (List.init arg_count (fun _ -> "Int")) in
      let fact_type = get_fact_maude_sort name in
      let fact_s =
        Printf.sprintf "op no%s : -> %s .\n" name fact_type ^
        Printf.sprintf "op _,_ : %s %s -> %s [assoc comm id: no%s] .\n" fact_type fact_type fact_type name ^
        Printf.sprintf "op %s%s : %s -> %s .\n" name underscores vars fact_type
      in
      s ^ "\n" ^ fact_s
    ) "" all_facts in
  let rules = List.map (fun (name, left, right, action) ->
      let left_maude = structured_ms_to_maude_string left in
      let right_action = List.sort Repr.compare (right @ action) in
      let right_maude = structured_ms_to_maude_string right_action in
      (* all made nonexec, because it actually doesn't matter *)
      Printf.sprintf "rl [%s] : < %s > => < %s > [narrowing nonexec] ." name left_maude right_maude
    ) rules in
  let rules_s = String.concat "\n" rules in
  let equations = "" in
  (* print trace to find out which rule has been applied -> makes maude slower! *)
  let maude_ctx = Printf.sprintf "
    mod MSRS is
      protecting INT .
      sorts State %s .
      %s
      %s
      %s
      %s
    endm\n" sorts_s fact_decl_s all_facts_s rules_s equations in
    maude_ctx

let gen_track_var_context msrs property tracked =
  let module TrackVarSet = Set.Make(struct
      type t = Multiset_rewrite_system.multiset
      let compare = Repr.compare
    end)
  in
  let property_track_vars =
    Ctl.get_facts property
    |> List.map (fun (fact_name, args) -> [(get_star_var fact_name, args)])
  in
  let track_vars =
    TrackVarSet.of_list property_track_vars
    |> TrackVarSet.add_seq (List.to_seq tracked)
    |> TrackVarSet.to_list
  in
  
  let all_constraints = List.fold_left (fun combis track_var ->
      List.concat_map (fun combi -> [(track_var, true)::combi; ((track_var, false)::combi)]) combis
    ) [[]] tracked in
  (track_vars, tracked, all_constraints)

let track_vars_by_arg_vars (track_vars, _, _) =
  let track_vars_by_arg_vars = Hashtbl.create 10 in
  List.iter (fun track_var -> 
      let vars = Utils.Str_utils.StringSet.empty in
      let vars = List.fold_left (fun vars (fact_name, instance) ->
          let vars = List.fold_left (fun vars arg -> Utils.Str_utils.StringSet.add_seq (List.to_seq (Arg_terms.vars arg)) vars) vars instance in
          vars
        ) vars track_var in
      Utils.Str_utils.StringSet.iter (fun var ->
          let cur_val = Option.value ~default:[] (Hashtbl.find_opt track_vars_by_arg_vars var) in
          let new_val = track_var_to_string track_var::cur_val in
          Hashtbl.replace track_vars_by_arg_vars var new_val
        ) vars
    ) track_vars;
  track_vars_by_arg_vars

(* helper functions for applying substitutions on structured_ms and arg lists *)

let apply_substs_instance subst instance = List.map (fun arg -> Substitution.apply_arg subst arg) instance

(** apply the substitutions in substs to the state *)
let apply_substs subst state: structured_ms =
  List.map (fun (fact, instances, p_star) ->
      let subst_instances = List.map (apply_substs_instance subst) instances in
      (fact, subst_instances, Option.map (Substitution.get_ms_var subst) p_star)
    ) state
  
(* main functions for constructing the transitions *)

(** expects an already sorted state *)
let reduce_state cap (action_facts, hide_action_facts) (state: structured_ms): (structured_ms * Substitution.t) list =
  (* TODO we dont' need to collect excluded *)
  let get_all_reductions cap (fact_name, instances, p_star) =
    let rec get_all_reductions' cap instances = 
      if cap = 0 then [([], (List.map (fun instance -> (fact_name, instance)) instances))]
      else if List.length instances <= cap then [(instances, [])]
      else match instances with
        | instance::l ->
          (List.map (fun (included, excluded) -> (instance::included, excluded)) (get_all_reductions' (cap-1) l))
          @ (List.map (fun (included, excluded) -> (included, (fact_name, instance)::excluded)) (get_all_reductions' cap l))
        | [] -> failwith "Reducing the state failed"
    in
    let reductions = get_all_reductions' cap instances in
    List.map (fun (included, excluded) -> 
        let (new_p_star, p_star_subst) =
          if p_star = None && excluded = [] then (None, None)
          else match p_star with
            | None -> (Some (get_star_var fact_name), Some (get_star_var fact_name, Multiset_rewrite_system.Const excluded))
            | Some p_star ->
              (* not necessary, but makes the result simpler *)
              let excluded_subst = if excluded = [] then
                  Multiset_rewrite_system.Var p_star
                else
                  Multiset_rewrite_system.Union (Multiset_rewrite_system.Var p_star, Multiset_rewrite_system.Const excluded)
              in
              (Some (get_star_var fact_name), Some (get_star_var fact_name, excluded_subst))
        in
        ((fact_name, included, new_p_star), p_star_subst)
      ) reductions
  in
  let rec reduce_state' state =
    match state with
    | fact::l ->
      let fact_name, _, _ = fact in
      let rests = reduce_state' l in
      if hide_action_facts = false && List.mem fact_name action_facts then
        (* don't reduce action facts*)
        List.map (fun (rest_state, rest_star_subst) ->
            (fact::rest_state, rest_star_subst)
          ) rests
      else
        let reductions = get_all_reductions (List.assoc fact_name cap) fact in
        List.concat_map (fun (fact, star_subst) ->
          List.map (fun (rest_state, rest_star_subst) ->
              (fact::rest_state,
                Option.fold star_subst ~none:rest_star_subst ~some:(fun (var, value) ->
                  Substitution.add_ms rest_star_subst var value))) rests) reductions
    | [] -> [([], Substitution.empty)]
  in
  let reduced_states = reduce_state' state in
  (* let () = List.iter (fun state -> Printf.printf "--> %s\n" (state_to_string state)) reduced_states in *)
  reduced_states

let normalize_variables (state: structured_ms) (nu_star: Substitution.t): structured_ms * Substitution.t =
  let all_vars_state = List.concat_map (fun (fact, instances, p_star) -> List.concat_map Arg_terms.vars (List.flatten instances)) state in
  let all_vars_nu_star = List.concat_map (fun (_, ms) -> Multiset_rewrite_system.term_get_arg_vars ms) nu_star.Substitution.ms_subst in
  let all_vars = all_vars_state @ all_vars_nu_star in

  let nu = Substitution.make_total_arg Substitution.empty all_vars (fun i -> Arg_terms.(Int (Var (Printf.sprintf "v%d" i)))) in
  let state = apply_substs nu state in
  (state, nu)

(* generate conditions and assignments for transitions *)

let get_unknowns (constraints: constraints) =
  let unknowns = List.fold_left (fun unknowns (ms, _) ->
      let open Utils.Str_utils in
      let new_unknowns = List.fold_left (fun unknowns (_, args) ->
          List.fold_left (fun unknowns arg -> StringSet.add_seq (List.to_seq (Arg_terms.unknowns arg)) unknowns) unknowns args
        ) StringSet.empty ms in
      StringSet.to_list new_unknowns @ unknowns
    ) [] constraints in
  unknowns

let gen_track_var_assignments_quantifiers track_vars (star_var_assignment: Substitution.t) transition_id =
  let gen_contained_in_prev prev_term instance track_var_s =
    match prev_term with
    | Multiset_rewrite_system.Var _ -> (* nothing removed *) (Sat.mk_var track_var_s, [])
    | Multiset_rewrite_system.Minus (Multiset_rewrite_system.Var _, Multiset_rewrite_system.Const removed_facts) ->
      let removed_instances = List.map (fun (_, args) -> args) removed_facts in
      let eq_to_removed = Multiset_rewrite_system.gen_instance_in_instances_n removed_instances instance in
      let (unknowns, still_there) = List.fold_left_map (fun unknowns (eq_to_removed, n) ->
          if n = 0 then (unknowns, eq_to_removed)
          else
            let unknown = Printf.sprintf "CountGt%d_%s" n track_var_s in
            (unknown::unknowns, Sat.mk_and [eq_to_removed; Sat.mk_var unknown])
        ) [] eq_to_removed in
      (Sat.mk_and [Sat.mk_var track_var_s; Sat.mk_or still_there], unknowns)
    | _ -> failwith "Illegal state."
  in
  let equal_up_to_unknown_renaming args1 args2 =
    let subst_unknowns args =
      let (_, args) = List.fold_left_map (fun (subst, counter) arg ->
          match arg with
          | Arg_terms.Int Unknown x -> (match List.assoc_opt x subst with
            | None ->
              let new_x = string_of_int counter in
              (((x, new_x)::subst, counter + 1), Arg_terms.Int (Unknown new_x))
            | Some x -> ((subst, counter), Int (Unknown x))
            )
          | _ -> ((subst, counter), arg)
        ) ([], 0) args in
      args
    in
    (* let () = Printf.printf "%s <-> %s\n" (Multiset_rewrite_system.fact_to_string ("", args1)) (Multiset_rewrite_system.fact_to_string ("", args2)) in
    let () = Printf.printf "%s <-> %s\n" (Multiset_rewrite_system.fact_to_string ("", subst_unknowns args1)) (Multiset_rewrite_system.fact_to_string ("", subst_unknowns args2)) in *)
    subst_unknowns args1 = subst_unknowns args2
  in
  let gen_contained_in_some_prev_precise prev_term (star_var, instance) (_, orig_instance) =
    let (track_vars, unknowns, new_track_var) =
      if List.exists (fun track_var ->
            match track_var with
            | [(star_var', args)] when star_var = star_var' -> equal_up_to_unknown_renaming orig_instance args
            | _ -> false
          ) track_vars
        then (track_vars, [], None)
        else
          let new_track_var = [(star_var, orig_instance)] in
          let track_var_unknowns = get_unknowns [(new_track_var, true)] in
          (* TODO make prefix equal wrt alpha-renaming of unknowns *)
          let prefix = "uI" ^ String.map (fun c -> if c = '_' then 'I' else c) (track_var_to_string new_track_var) ^ "I" in
          let prefixed_unknowns = List.map (fun var -> prefix ^ var) track_var_unknowns in
          let new_track_var = List.map (fun (fact_name, args) -> (fact_name, List.map (fun arg ->
              match arg with
              | Arg_terms.Int Unknown x -> Arg_terms.Int (Unknown (prefix ^ x))
              | _ -> arg) args)) new_track_var in
          
          (new_track_var::track_vars, (track_var_to_string new_track_var)::prefixed_unknowns, Some new_track_var)
    in
    let (unknowns, contained_in_prev) = List.fold_left_map (fun unknowns track_var ->
        let track_var_subst = List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "") args)) track_var in
      
        let in_track_var = Multiset_rewrite_system.gen_fact_in_ms track_var_subst (star_var, instance) in
        let (contained_in_prev, new_unknowns) = gen_contained_in_prev prev_term instance (track_var_to_string track_var_subst) in
        if Some track_var = new_track_var then
          let (hidden_smt, hidden_unknown) = Sat.hide contained_in_prev in
          (hidden_unknown::unknowns, Sat.mk_and [in_track_var; hidden_smt])
        else (new_unknowns @ unknowns, Sat.mk_and [in_track_var; contained_in_prev])
      ) unknowns track_vars in
    (Sat.mk_or contained_in_prev, unknowns)
  in
  let gen_contained_in_some_prev prev_term (star_var, instance) (_, orig_instance) =
    if false then
      let (a,b) = gen_contained_in_some_prev_precise prev_term (star_var, instance) ("", orig_instance) in
      (a, b, true)
    else
    let is_precise = List.exists (fun track_var ->
            match track_var with
            | [(star_var', args)] when star_var = star_var' -> equal_up_to_unknown_renaming orig_instance args
            | _ -> false
          ) track_vars
    in
    let (unknowns, contained_in_prev) = List.fold_left_map (fun unknowns track_var ->
        let track_var_subst = List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "") args)) track_var in
      
        let in_track_var = Multiset_rewrite_system.gen_fact_in_ms track_var_subst (star_var, instance) in
        let (contained_in_prev, new_unknowns) = gen_contained_in_prev prev_term instance (track_var_to_string track_var_subst) in
        (new_unknowns @ unknowns, Sat.mk_and [in_track_var; contained_in_prev])
      ) [] track_vars in
    (Sat.mk_or contained_in_prev, unknowns, is_precise)
  in
  let gen_fact_existent (star_var, instance) orig_track_var =
    Substitution.get_ms_opt star_var_assignment star_var
    |> Option.fold ~none:(Sat.mk_bool false, [], true) ~some:(fun value ->
        match value with
        | Multiset_rewrite_system.Const added_facts ->
          let added_instances = List.map (fun (_, args) -> args) added_facts in
          let added = Multiset_rewrite_system.gen_instance_in_instances added_instances instance in
          (added, [], true)
        | Multiset_rewrite_system.Union (prev_term, Multiset_rewrite_system.Const added_facts) ->
          let added_instances = List.map (fun (_, args) -> args) added_facts in
          let added = Multiset_rewrite_system.gen_instance_in_instances added_instances instance in
          let (contained_in_prev, unknowns, is_precise) = gen_contained_in_some_prev prev_term (star_var, instance) orig_track_var in
          (Sat.mk_or [added; contained_in_prev], unknowns, is_precise)
        | prev_term ->
          let (contained_in_prev, unknowns, is_precise) = gen_contained_in_some_prev prev_term (star_var, instance) orig_track_var in
          (contained_in_prev, unknowns, is_precise)
      )
  in

  let res = List.map (fun track_var ->
      let track_var_unknowns = get_unknowns [(track_var, true)] in
      let prefixed_unknowns = List.map (fun var -> "i" ^ var) track_var_unknowns in
      let track_var_subst = List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "i") args)) track_var in
      
      let all_facts_existent = List.map2 gen_fact_existent track_var_subst track_var in
      let (all_facts_existent, unknowns, all_precise) = List.fold_left (fun (al, bl, cl) (a, b, c) -> (a::al, b::bl, c && cl)) ([], [], true) all_facts_existent in
      let quantified = Sat.mk_exists_multi prefixed_unknowns (Sat.mk_and all_facts_existent) in
      if all_precise then (track_var, quantified, List.flatten unknowns)
      else
        let unique_unknown = "SomewhereElse_" ^ (string_of_int transition_id) ^ "_" ^ (track_var_to_string track_var) in
        (track_var, Sat.mk_or [quantified; Sat.mk_var unique_unknown], unique_unknown::List.flatten unknowns)
    ) track_vars
  in
  res

(* the resulting substitution is simplified!!*)
let gen_track_var_assignments track_vars (star_var_assignment: Substitution.t) transition_id nondet_vars =
  let (existent_star_facts, added_facts, removed_facts) = List.fold_left (fun (existent_star_facts, added_facts, removed_facts) (star_var, value) ->
      match value with
      | Multiset_rewrite_system.Var _ -> 
        (star_var::existent_star_facts, added_facts, removed_facts)
      | Multiset_rewrite_system.Minus (Multiset_rewrite_system.Var _, Multiset_rewrite_system.Const new_removed_facts) -> 
        (star_var::existent_star_facts, added_facts, (List.map get_star_fact new_removed_facts) @ removed_facts)
      | Multiset_rewrite_system.Const new_added_facts ->
        (existent_star_facts, (List.map get_star_fact new_added_facts) @ added_facts, removed_facts)
      | Multiset_rewrite_system.Union (Multiset_rewrite_system.Var _, Multiset_rewrite_system.Const new_added_facts) -> 
        (star_var::existent_star_facts, (List.map get_star_fact new_added_facts) @ added_facts, removed_facts)
      | Multiset_rewrite_system.Union (Multiset_rewrite_system.Minus (Multiset_rewrite_system.Var _, Multiset_rewrite_system.Const new_removed_facts), Multiset_rewrite_system.Const new_added_facts) ->
        (star_var::existent_star_facts, (List.map get_star_fact new_added_facts) @ added_facts, (List.map get_star_fact new_removed_facts) @ removed_facts)
      | _ -> failwith "Illegal state"
    ) ([], [], []) star_var_assignment.ms_subst in

  (* filter out track_vars that are definitely false *)
  let track_vars_srcs = List.filter_map (fun track_var ->
      if List.for_all (fun (fact_name, _) -> List.mem fact_name existent_star_facts) track_var
        then Some (List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "") args)) track_var)
        else None
    ) track_vars
  in

  let gen_still_cond track_var_still track_var_src =
    let track_var_src_s = track_var_to_string track_var_src in
    let unis = Unification.unify_subset ~unknowns_in_sub:true track_var_src track_var_still in
    let (unknowns, unis) = List.fold_left_map (fun unknowns (subst, cond) ->
        let track_var_still_subst = List.map (fun (fact_name, args) -> (fact_name, List.map (Substitution.apply_arg_unknowns subst) args)) track_var_still in

        match track_var_still_subst with
        | [(fact_name, instance)] ->
          (* we can be more precise with the count unknowns *)
          let removed_instances = List.filter_map (fun (fact_name', args') -> if fact_name' = fact_name then Some args' else None) removed_facts in
          let eq_to_removed = Multiset_rewrite_system.gen_instance_in_instances_n removed_instances instance in
          let (unknowns, still_there) = List.fold_left_map (fun unknowns (eq_to_removed, n) ->
              if n = 0 then (unknowns, eq_to_removed)
              else
                let unknown = Printf.sprintf "CountGt%d_%s" n track_var_src_s in
                (unknown::unknowns, Sat.mk_and [eq_to_removed; Sat.mk_var unknown])
            ) [] eq_to_removed in
          (unknowns, (subst, Sat.mk_and [Sat.mk_or still_there; cond]))
        | _ ->
          let nothing_removed = Multiset_rewrite_system.gen_nothing_removed track_var_still_subst removed_facts in
          ([], (subst, Sat.mk_and [nothing_removed; cond]))
      ) [] unis in
    (* let () = Printf.printf "%s\n" (Unification.to_string unis) in *)
    (unknowns, Unification.mk_and_smt unis (Sat.mk_var (track_var_to_string track_var_src)))
  in
  let gen_assignment_for_one_possibility (track_var_added, track_var_still) =
    (* let () = Printf.printf "%s < %s\n" (Multiset_rewrite_system.ms_to_string track_var_added) (Multiset_rewrite_system.ms_to_string added_facts) in *)
    let added_cond = Unification.unify_subset ~unknowns_in_sub:true added_facts track_var_added in
    (* let () = Printf.printf "Added: %s | %s\n\n" (Multiset_rewrite_system.ms_to_string track_var_added) (Unification.to_string added_cond) in *)
    (* let () = Printf.printf "- %s\n" (Unification.to_string added_cond) in *)
    if track_var_still = [] then ([], added_cond)
    else if added_cond = [] then ([], []) (* added cannot be unified *)
    else
      let (unknowns, still_cond) = List.fold_left_map (fun unknowns track_var_src ->
          let (new_unknowns, still_cond) = gen_still_cond track_var_still track_var_src in
          (* let () = Printf.printf "%s\n\n" (Unification.to_string still_cond) in *)
          (new_unknowns @ unknowns, still_cond)
        ) [] track_vars_srcs in
      let still_cond = Unification.mk_or still_cond in
      (* let () = Printf.printf "Added: %s\n\n" (Unification.to_string added_cond) in
      let () = Printf.printf "%s\n\n" (Unification.to_string still_cond) in
      let () = Printf.printf "=> %s\n\n" (Unification.to_string (Unification.mk_and [added_cond; still_cond])) in *)
      (unknowns, Unification.mk_and [added_cond; still_cond])
  in
  let gen_splits ms = List.fold_left (fun splits fact -> List.concat_map (fun (ms1, ms2) -> [(fact::ms1, ms2); (ms1, fact::ms2)]) splits) [([],[])] ms in
  
  let is_precise track_var =
    (List.length track_var = 1
      && (List.for_all (fun (_, args) -> List.for_all (fun arg -> Arg_terms.unknowns arg = []) args) track_var))
    || (List.for_all (fun (fact_name, _) -> List.for_all (fun (fact_name', _) -> not (fact_name = fact_name')) added_facts) track_var 
      && List.for_all (fun (fact_name, _) -> List.for_all (fun (fact_name', _) -> not (fact_name = fact_name')) removed_facts) track_var)
  in

  let res = List.map (fun track_var ->
      let splits = gen_splits track_var in
      let (unknowns, unis) = List.fold_left_map (fun unknowns split ->
          let (new_unknowns, uni) = gen_assignment_for_one_possibility split in
          (* let () = Printf.printf "=> %s\n" (Unification.to_string uni) in *)
          (new_unknowns @ unknowns, uni)
        ) [] splits in
      let assignment = Unification.to_sat (Unification.mk_or unis) in
      (* optional simplification *)
      let assignment = Sat.simplify assignment in
      if not (is_precise track_var) then
        (* not precise *)
        (* SomewhereElse is an unknown that depends on the step's nondeterministic values (an unknown function) *)
        let unique_unknown = "SomewhereElse_" ^ (string_of_int transition_id) ^ "_" ^ (track_var_to_string track_var) in
        (track_var, Sat.mk_or [assignment; Sat.mk_bool_app unique_unknown nondet_vars], unknowns)
      else
        (track_var, assignment, unknowns)
    ) track_vars
  in
  res

let gen_transition_conditions_using_constraints rho_S nu (constraints: constraints) =
  let rho_S_star = Substitution.restrict rho_S is_star_var in
  (* the facts that have to be present for the transition to be valid *)
  let required_facts = List.concat_map (fun (var, value) ->
    match value with
      | Multiset_rewrite_system.Const ms -> ms
      | Multiset_rewrite_system.Union (Multiset_rewrite_system.Var _, Multiset_rewrite_system.Const ms) -> ms
      | Multiset_rewrite_system.Var _ -> []
      | _ -> failwith "Illegal state"
    ) rho_S_star.ms_subst in
  let required_facts = List.map (fun (fact_name, args) -> (get_star_var fact_name, args)) required_facts in
  let (pos_constraints, neg_constraints, neg_unknowns) = List.fold_left (fun (pos_constraints, neg_constraints, neg_unknowns) (track_var, positive) ->
      if positive then (track_var::pos_constraints, neg_constraints, neg_unknowns)
      else 
        let unknowns = get_unknowns [(track_var, positive)] in
        (pos_constraints, track_var::neg_constraints, unknowns @ neg_unknowns)  
    ) ([], [], []) constraints in

  let not_subset_of_required = List.map (fun track_var ->
      Sat.mk_not (Multiset_rewrite_system.gen_subset_smt required_facts track_var)
    ) neg_constraints in
  let not_neg_constraint = Sat.mk_forall_multi neg_unknowns (Sat.mk_and not_subset_of_required) in

  (* TODO: we can extract more information: when there is a constraint [P(x)] and [Q(y), P(z)], we can actually also know that P(x) and Q(y) exist *)
  let must_condition =
    if required_facts = [] then Sat.mk_bool true
    else Sat.mk_or (List.map (fun track_var ->
      Multiset_rewrite_system.gen_subset_smt track_var required_facts) pos_constraints) in
  (* let () = Printf.printf "Required_facts: %s\n" (Multiset_rewrite_system.ms_to_string required_facts) in
  let () = Printf.printf "Neg: %s -> %s\n" (Multiset_rewrite_system.ms_to_string (List.flatten neg_constraints)) (Sat.to_string (Sat.simplify not_neg_constraint)) in
  let () = Printf.printf "Pos: %s -> %s\n" (Multiset_rewrite_system.ms_to_string (List.flatten pos_constraints)) (Sat.to_string (Sat.simplify must_condition)) in *)
  (not_neg_constraint, must_condition)

let gen_rule_applicable_condition rho_S =
  let (tmp_vars, conditions) = List.fold_left_map (fun tmp_vars (var, value) ->
      (* mu(var) = rho_S(var) (mu(var) is encoded as var) *)
      let condition = Sat.mk_eq (Sat.mk_var var) (Arg_terms.to_smt value) in
      (tmp_vars, condition)
    ) Utils.Str_utils.StringSet.empty rho_S.Substitution.arg_subst in
  Sat.mk_and conditions

let gen_constraints_reachable_condition tracked track_var_assignments constraints succ_constraints =
  let constraints_subst = { Substitution.ms_subst = [];
    arg_subst = List.map (fun (track_var, value) -> (track_var_to_string track_var, Arg_terms.Bool (Smt (Sat.mk_bool value)))) constraints
  } in
  Sat.mk_and (List.map (fun track_var ->
      let track_var_s = track_var_to_string track_var in
      (* false by default b/c it only appears not in track_var_assignments, if there is no P* in the succ state *)
      let track_var_assignment = Substitution.get_arg_opt track_var_assignments track_var_s
        |> Option.map Arg_terms.to_smt
        |> Option.value ~default:(Sat.mk_bool false) in
      (* let pred_track_var_value = List.assoc track_var constraints in *)
      let succ_track_var_value = List.assoc track_var succ_constraints in
      Sat.mk_eq (Sat.mk_bool succ_track_var_value) (Substitution.apply_arg_smt constraints_subst track_var_assignment)
    ) tracked)

(* actually has one additional parameter succ_constraints in the middle of the function *)
let gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints transition_id =
  let () = Utils.Monitoring.start_event "gen_transition_conditions_and_assignments" in
  (* let () = Printf.printf "rho_l_tmp_vars: %s\n" (String.concat ", " (Utils.Str_utils.StringSet.to_list rho_l_tmp_vars)) in *)
  (* let () = Printf.printf "rho_S: %s\n" (Substitution.to_string rho_S) in *)
  (* let () = Printf.printf "nu: %s\n" (Substitution.to_string nu) in *)
  (* let () = Printf.printf "nu*: %s\n" (Substitution.to_string nu_star) in *)

  let rho_S_inv = Substitution.inv_special rho_S in

  (* a *)
  let rho_R_tmp_vars = Substitution.range_arg rho_R in
  let rho_S_inv_wo_star = { rho_S_inv with ms_subst = [] } in
  (* let () = Printf.printf "rho_S_wo_star_inv: %s\n" (Substitution.to_string rho_S_inv_wo_star) in *)
  let a_regular = rho_S_inv_wo_star in
  let rho_S_tmp_vars = Substitution.range_arg { rho_S with ms_subst = []} in
  let a_nondet = Utils.Str_utils.StringSet.fold (fun rho_R_var a_nondet ->
      if Utils.Str_utils.StringSet.mem rho_R_var rho_S_tmp_vars then a_nondet
      else rho_R_var::a_nondet
    ) rho_R_tmp_vars [] in
  (* let () = Printf.printf "a_regular: %s\n" (Substitution.to_string a_regular) in *)
  (* let () = Printf.printf "a_nondet: %s\n" (String.concat ", " a_nondet) in *)


  (* b_post *)
  let rule_applicable_condition = gen_rule_applicable_condition rho_S in
  (* let () = Printf.printf "rule_applicable_condition: %s\n" (Sat.to_string rule_applicable_condition) in *)

  let tracked_unknowns = get_unknowns constraints in
  let constraints_subst = List.map (fun (track_var, value) -> (List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "") args)) track_var, value)) constraints in
  let (constraint_conditions_may, constraint_conditions_must) = gen_transition_conditions_using_constraints rho_S nu constraints_subst in
  (* let () = Printf.printf "constraint_conditions_may: %s\n" (Sat.to_string (Sat.simplify constraint_conditions_may)) in *)
  (* let () = Printf.printf "constraint_conditions_must: %s\n" (Sat.to_string (Sat.simplify constraint_conditions_must)) in *)

  let rho_S_inv_star = { rho_S_inv with Substitution.arg_subst = [] } in
  let star_var_assignment = Substitution.compose_restrict rho_S_inv_star nu_star in
  let raw_track_var_assignments = gen_track_var_assignments track_vars star_var_assignment transition_id a_nondet in

  let (track_var_assignments, still_unknowns) = List.fold_left (fun (assignment, unknowns) (var, value, new_unknowns) ->
      (Substitution.add_arg assignment (track_var_to_string var) (Arg_terms.(Bool (Smt value))),
      new_unknowns @ unknowns)
    ) (Substitution.empty, []) raw_track_var_assignments in

  (* filter duplicates *)
  let still_unknowns = Utils.Str_utils.StringSet.to_list (Utils.Str_utils.StringSet.of_list still_unknowns) in   

  let nu_inv = Substitution.inv_special nu in

  let () = Utils.Monitoring.stop_event "gen_transition_conditions_and_assignments" in

  (* the rest can be preprocessed for all succ_constraints *)
  fun succ_constraints ->
    let () = Utils.Monitoring.start_event "gen_transition_conditions_and_assignments" in

    let (track_var_assignments_simpl) = List.fold_left (fun assignment_simple (var, value, new_unknowns) ->
        let simplified_value =
          let succ_constraint = List.assoc_opt var succ_constraints in
          Option.fold ~none:value ~some:Sat.mk_bool succ_constraint
        in
        Substitution.add_arg assignment_simple (track_var_to_string var) (Arg_terms.(Bool (Smt simplified_value)))
      ) Substitution.empty raw_track_var_assignments in
    
    let constraints_reachable_condition = gen_constraints_reachable_condition tracked track_var_assignments constraints succ_constraints in

    (* a_post *)
    
    let a_post_regular = Substitution.concat track_var_assignments_simpl (Substitution.concat nu_inv star_var_assignment) in
    (* let () = Printf.printf "a_post_regular: %s\n\n" (Substitution.to_string a_post_regular) in *)

    let b = [Sat.mk_bool true] in
    let a = { Kripke.regular = a_regular; nondet = a_nondet; unknowns = tracked_unknowns @ still_unknowns } in
    let b_post = (
      [Sat.mk_and [rule_applicable_condition; constraint_conditions_may]; constraints_reachable_condition],
      [Sat.mk_and [rule_applicable_condition; constraint_conditions_must]; constraints_reachable_condition]) in
    let a_post = { Kripke.regular = a_post_regular; nondet = []; unknowns = [] } in

    let () = Utils.Monitoring.stop_event "gen_transition_conditions_and_assignments" in
    (b, a, b_post, a_post)

let unique = ref 0
let next_unique () =
  let value = !unique in
  let () = unique := !unique + 1 in
  value

(** takes a maude transition (state, rho|_S, rho|_l, rule_name) and maps it to all actual transitions that are generated from it *)
let convert_maude_transition cap action_facts_ctx (track_vars, tracked, possible_constraints) constraints (succ_state, rho_S, rho_l, rule_name): (structured_ms * (constraints * constraints * Kripke.transition_type * Kripke.condition * Kripke.assignments * Kripke.condition * Kripke.assignments * string) list) list =
  let reductions = reduce_state cap action_facts_ctx succ_state in
  let transitions_by_succ = List.map (fun (succ_state, nu_star) ->
    let (succ_state, nu) = normalize_variables succ_state nu_star in
    let transitions = List.concat_map (fun constraints ->
      let transition_id = next_unique () in
      (* preprocess everything that does not depend on succ_constraints *)
      let gen_transition_conditions_and_assignments' = gen_transition_conditions_and_assignments rho_l rho_S nu nu_star track_vars tracked constraints transition_id in
      List.concat_map (fun succ_constraints ->
        let (b, a, (b_post_may, b_post_must), a_post) = gen_transition_conditions_and_assignments' succ_constraints in
        (* drop infeasible targets before simplifying; the result is the same as filtering afterwards *)
        let may_sat = not (Sat.is_unsat (Sat.mk_and b_post_may)) in
        let must_sat = not (Sat.is_unsat (Sat.mk_and b_post_must)) in
        
        if not may_sat && not must_sat then []
        else
          (* optional simplification *)
          let b = List.map Sat.simplify b in
          let b_post_may = List.map Sat.simplify b_post_may in
          let b_post_must = List.map Sat.simplify b_post_must in
          let a = { a with regular = Substitution.simplify a.regular } in
          let a_post = { a_post with regular = Substitution.simplify a_post.regular } in

          let may_transition = (constraints, succ_constraints, Kripke.ONLY_MAY, b, a, b_post_may, a_post, rule_name) in
          let must_transition = (constraints, succ_constraints, Kripke.MAY_AND_MUST, b, a, b_post_must, a_post, rule_name) in

          (* filter out impossible transitions *)
          match may_sat, must_sat with
          | true, true when Sat.is_eq (Sat.mk_and b_post_may) (Sat.mk_and b_post_must) -> [must_transition]
          | true, true -> [must_transition; may_transition]
          | true, _ -> [may_transition]
          | _, true -> [must_transition]
          | _ -> []
      ) possible_constraints) constraints in
    (succ_state, transitions)
  ) reductions in
  transitions_by_succ
  
let postprocess_maude_output raw_succ_transitions: (structured_ms * Substitution.t * Substitution.t * string) list =
  List.map (fun (state, state_subst, rule_subst, rule_name) ->
      let state = List.map (fun (fact_name, term) -> 
          match term with
          | Multiset_rewrite_system.Const ms -> (fact_name, List.map (fun (fact, args) -> args) ms, None)
          | Multiset_rewrite_system.Union (Multiset_rewrite_system.Var var, Multiset_rewrite_system.Const ms) ->
            (fact_name, List.map (fun (fact, args) -> args) ms, Some var)
          | Multiset_rewrite_system.Var var -> (fact_name, [], Some var)
          | _ -> failwith "Illegal state"
        ) state in
      (state, state_subst, rule_subst, rule_name)
    ) raw_succ_transitions

let get_state_successors msrs maude_path maude_ctx cap action_facts_ctx track_var_ctx (ms, constraints: structured_ms * constraints list): (structured_ms * (constraints * constraints * Kripke.transition_type * Kripke.condition * Kripke.assignments * Kripke.condition * Kripke.assignments * string) list) list =
  (* run maude to get all successors *)
  let state_s = structured_ms_to_maude_string ms in
  let maude_in = String.cat maude_ctx (Printf.sprintf "vu-narrow in MSRS : < %s > =>1 S:State .\nq\n" state_s) in
  
  let raw_succ_transitions = Maude.run_maude maude_path maude_in in
  let raw_succ_transitions = postprocess_maude_output raw_succ_transitions in

  (* TODO sanity check until the new parser is bug-free *)
  (* let () = Maude_parser_legacy.check_against_new_parser maude_path maude_in raw_succ_transitions in *)

  (* map successor transitions to the transitions that go to reduced states in normal-form *)
  List.concat_map (convert_maude_transition cap action_facts_ctx track_var_ctx constraints) raw_succ_transitions

(** generates the Kripke structure from the MSRS *)
let gen_kripke msrs maude_path property params =
  let track_var_ctx = gen_track_var_context msrs property params.Encoding_params.tracked in
  let track_vars_by_arg_vars = track_vars_by_arg_vars track_var_ctx in
  let all_facts_symbols = Multiset_rewrite_system.get_fact_symbols msrs in
  let structured_msrs = gen_structured_msrs msrs all_facts_symbols in
  let maude_ctx = gen_maude_context structured_msrs all_facts_symbols in
  let action_facts = List.filter_map (fun (fact_name, _) -> if is_action_fact msrs fact_name then Some fact_name else None) all_facts_symbols in
  let rec gen_kripke' kripke (states: (structured_ms * (constraints list)) list) =
    (* let () = Printf.printf "Collected %d states\n" (fst (Kripke.get_stats kripke)); flush stdout in *)
    if states = [] then kripke
    else
      let (new_states, kripke) = List.fold_left
        (fun (new_states, kripke) state ->
          (* process a state from states *)
          let state_ms, _ = state in
          (* let () = Printf.printf "New State: %s\n" (state_to_string state); flush stdout in *)
          let succ_transitions = get_state_successors structured_msrs maude_path maude_ctx params.cap (action_facts, params.hide_action_facts) track_var_ctx state in
          let (new_states, kripke) = List.fold_left (fun (new_states, kripke) (succ_ms, transitions) -> 
              let (new_constraints, kripke) = List.fold_left (fun (new_constraints, kripke) (constraints, succ_constraints, transition_type, condition, assignments, condition_post, assignments_post, rule_name) -> 
                  (* process one successor of state *)
                  let state = (state_ms, constraints) in
                  let succ_state = (succ_ms, succ_constraints) in
                  let transition = (state, succ_state, transition_type, condition, assignments, condition_post, assignments_post, rule_name) in
                  if Kripke.contains_state kripke succ_state
                    then (new_constraints, Kripke.add_transition kripke transition)
                    else (succ_constraints::new_constraints, Kripke.add_transition (Kripke.add_state kripke succ_state) transition)
                ) ([], kripke) transitions
              in
              if new_constraints = [] then (new_states, kripke)
              else ((succ_ms, new_constraints)::new_states, kripke)
            ) (new_states, kripke) succ_transitions in
          (new_states, kripke)
        ) ([], kripke) states in
      gen_kripke' kripke new_states
  in
  (* initialize the Kripke structure *)
  let kripke = Kripke.empty in
  let initial_state_ms = List.map (fun (fact, _) -> 
      if params.start_with_empty_state || is_action_fact msrs fact then (fact, [], None)
      else (fact, [], Some (get_star_var fact))
    ) all_facts_symbols in
  let initial_state_constraints =
    let (_, tracked, _) = track_var_ctx in
    List.map (fun var -> (var, false)) tracked in
  let kripke = Kripke.add_state kripke (initial_state_ms, initial_state_constraints) in
  let kripke = Kripke.add_initial_state kripke (initial_state_ms, initial_state_constraints) in
  let (structured_track_vars, _, _) = track_var_ctx in
  (gen_kripke' kripke [(initial_state_ms, [initial_state_constraints])], track_vars_by_arg_vars, structured_track_vars)

let annotate_fact (ms, constraints: state) (fact_name, args) positive =
  let star_instance = (get_star_var fact_name, args) in
  let fact_instances = List.find_opt (fun (fact_name', _, _) -> fact_name = fact_name') ms in
  match fact_instances with
  | None ->
    (*
      the property mentions a fact that doesn't appear in the msrs at all 
      TODO -> maybe this is worth a warning -> usually this is unwanted
    *)
    Sat.mk_bool (not positive)
  | Some (_, concrete_instances, p_star) ->
    let is_in_star_var = if p_star = None then Sat.mk_bool false
      else
        let value = List.find_map (fun (track_var, value) ->
          if value = true && List.mem star_instance track_var then Some true
          else if value = false && track_var = [star_instance] then Some false
          else None) constraints in
        match value with
        | None -> Sat.mk_var (track_var_to_string [star_instance])
        | Some value -> Sat.mk_bool value
    in
    let eq_to_concrete = Multiset_rewrite_system.gen_instance_in_instances concrete_instances args in

    let is_present = Sat.mk_or [eq_to_concrete; is_in_star_var] in
    if positive then is_present
    else Sat.mk_not is_present

let annotate_label _ _ _ = failwith "The fact encodings don't support labels"
