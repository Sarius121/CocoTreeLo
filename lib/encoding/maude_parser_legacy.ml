open Logic

(** fact names, instances, the name of the star-variable *)
type facts_of_type = string * Arg_terms.term list list * string option
type structured_ms = facts_of_type list

let is_star_var name = String.ends_with name ~suffix:"*"
let get_fact_maude_sort name = name ^ "Fact"
let is_star_var_maude (_, sort) = String.ends_with sort ~suffix:"Fact"
let get_fact_name_from_maude_sort sort = String.sub sort 0 (String.length sort - 4)
let is_no_fact name = String.starts_with ~prefix:"no" name
let get_fact_name_from_no_fact name = String.sub name 2 (String.length name - 2)

let encode_stars input = String.map (fun c -> if c = '*' then 'M' else c) input
let decode_star input = if String.ends_with ~suffix:"M" input then String.map (fun c -> if c = 'M' then '*' else c) input
  else input

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

let parse_maude_raw_var raw_arg =
    (* let () = Printf.printf "%s\n" raw_arg in *)
    match String.split_on_char ':' raw_arg with
    | [name; sort] -> (name, sort)
    | _ -> failwith "Parsing the maude variable failed"

let parse_maude_raw_arg raw_arg =
    match String.split_on_char ':' raw_arg with
    | [name; sort] -> Arg_terms.(Int (Var name))
    | [value] -> Arg_terms.(Int (Const (int_of_string value)))
    | _ -> failwith "Parsing the maude fact arg failed"

let parse_maude_state s : structured_ms =
  (* let () = Printf.printf "%s\n" s in *)
  let s = String.map (fun c -> if c = '\n' then ' ' else c) s in
  let raw_facts = String.split_on_char ';' s in
  List.map (fun raw_fact ->
      let raw_fact_instances = String.split_on_char ',' raw_fact in
      Option.get (List.fold_left (fun accu raw_instance ->
          let split = String.split_on_char ' ' raw_instance in
          let split = List.filter (fun elem -> not (elem = "")) split in
          match split with
          | [name] when is_no_fact name ->
            let name = get_fact_name_from_no_fact name in
            let (name', instances, p_star) = Option.value ~default:(name, [], None) accu in
            let () = if name = name' then () else failwith "Parsing the maude state failed" in
            Some (name, instances, p_star)
          | [name] when is_star_var_maude (parse_maude_raw_var name) ->
            let (var, sort) = parse_maude_raw_var name in
            let name = get_fact_name_from_maude_sort sort in
            let (name', instances, p_star) = Option.value ~default:(name, [], None) accu in
            let () = if name = name' then () else failwith "Parsing the maude state failed" in
            Some (name, instances, Some var)
          | name::raw_args ->
            let (name', instances, p_star) = Option.value ~default:(name, [], None) accu in
            let () = if name = name' then () else failwith "Parsing the maude state failed" in
            let args = List.map (fun raw_arg -> 
              let var = parse_maude_raw_arg raw_arg in
              var
              ) raw_args in
            Some (name, args::instances, p_star)
          | [] -> failwith "Parsing the maude state failed"
        ) None raw_fact_instances)
    ) raw_facts

let parse_maude_fact_instances raw =
  List.map (fun raw_instance ->
      let split = String.split_on_char ' ' raw_instance in
      let split = List.filter (fun elem -> not (elem = "")) split in
      match split with
      | fact::args -> (fact, List.map (fun raw_arg -> 
          let arg = parse_maude_raw_arg raw_arg in
          arg
        ) args)
      | _ -> failwith "Parsing fact instances failed"
    ) raw

let parse_maude_substitution subst raw_l raw_r =
  let (var, sort) = parse_maude_raw_var raw_l in
  if sort = "Int" then
    let term = parse_maude_raw_arg raw_r in
    Substitution.add_arg subst var term
  else
    let split = String.split_on_char ',' raw_r in
    let split = List.filter (fun elem -> not (elem = "")) split in
    match split with
    | [value] ->
      (* equal to one variable *)
      if String.starts_with ~prefix:"no" value then
        Substitution.add_ms subst (decode_star var) (Multiset_rewrite_system.Const [])
      else if String.contains value ' ' then
        (* TODO improve this *)
        let fact = parse_maude_fact_instances [value] in
        Substitution.add_ms subst (decode_star var) (Multiset_rewrite_system.Const fact)
      else
        let (value, _) = parse_maude_raw_var value in
        Substitution.add_ms subst (decode_star var) (Multiset_rewrite_system.Var value)
    | value::instances ->
      (* equal to one variable *)
      let value = if String.starts_with ~prefix:"no" value then
          Multiset_rewrite_system.Const []
        else
          let (value, _) = parse_maude_raw_var value in
          Multiset_rewrite_system.Var value
      in
      if instances = [] then
        Substitution.add_ms subst (decode_star var) value
      else
        let instances = parse_maude_fact_instances instances in
        Substitution.add_ms subst (decode_star var) (Multiset_rewrite_system.Union (value, Multiset_rewrite_system.Const instances))
    | _ -> failwith "Parsing a maude subsitution failed."

(** 
  TODO write this parser in a *nice* and efficient way 
  @returns (transition list, var_counter) where transitions contain (succ_state, new_variables, rule_name)
*)
let parse_maude_output s : (structured_ms * Substitution.t * Substitution.t * string) list =
  (* let () = Printf.printf "%s\n\n" s in *)
  let relevant_data = Utils.Str_utils.get_all_matching s "rl \\[[^]]*\\]\\|state: < [^>]* >\\|^[^<\n%#]* --> [^<\n%#]*$" in
  (* let () = Printf.printf "---\n%s\n---\n" (String.concat "\n" relevant_data) in *)
  let (cur_state, state_substs, rule_substs, transitions_with_substs) = List.fold_left (fun (state, state_substs, rule_substs, transitions) raw ->
      if String.starts_with ~prefix:"rl" raw then
        let _ = Str.string_match (Str.regexp {|rl \[\([^]]*\)\]|}) raw 0 in
        let rule = Str.matched_group 1 raw in
        let state = Option.get state in
        (* substs has to be reversed, because there might be multiple substitutions for the same variable
          and the last substitution is actually the one we need *)
        (None, Substitution.empty, Substitution.empty, (state, state_substs, rule_substs, rule)::transitions)
      else if String.starts_with ~prefix:"state: " raw then
        let _ = Str.string_match (Str.regexp "state: < \\([^>]*\\) >") raw 0 in
        let state_raw = Str.matched_group 1 raw in
        let state = parse_maude_state state_raw in
        (Some state, state_substs, rule_substs, transitions)
      else
        (* let () = Printf.printf "%s | " raw in *)
        let _ = Str.string_match (Str.regexp "\\([^<\n%#]*\\) --> \\([^<\n%#]*\\)$") raw 0 in
        let left = Str.matched_group 1 raw in
        let right = Str.matched_group 2 raw in
        if state = None
          then (state, parse_maude_substitution state_substs left right, rule_substs, transitions)
          else (state, state_substs, parse_maude_substitution rule_substs left right, transitions)
    ) (None, Substitution.empty, Substitution.empty, []) (List.rev relevant_data) in
  (* state_substs, rule_substs and cur_state are just helper variables in the parser. They should be empty in the end *)
  let () = if state_substs != Substitution.empty || rule_substs != Substitution.empty || cur_state != None then failwith "Parsing the maude output failed" else () in
  transitions_with_substs

let check_against_new_parser maude_path maude_in raw_succ_transitions =
  let raw_succ_transitions_legacy =
    try
      Some (parse_maude_output (Maude.run_maude_legacy maude_path maude_in))
    with ex -> Printf.printf "WARNING: Legacy maude output parser failed.\n"; None
  in
  match raw_succ_transitions_legacy with
  | None -> ()
  | Some raw_succ_transitions_legacy ->
    let raw_succ_transitions_legacy = List.map (fun (state1, state_subst1, rule_subst1, rule1) ->
        let state1 = List.map (fun (fact_name, instances, var) -> (fact_name, List.rev instances, var)) state1 in
        (state1, state_subst1, rule_subst1, rule1)
      ) raw_succ_transitions_legacy in
    if not (raw_succ_transitions = raw_succ_transitions_legacy) then
      let _ = List.map2 (fun (state1, state_subst1, rule_subst1, rule1) (state2, state_subst2, rule_subst2, rule2) ->
          Printf.printf "Parsers give different results:\n";
          Printf.printf "Actual: %s\n" (structured_ms_to_maude_string state1);
          Printf.printf "Legacy: %s\n\n" (structured_ms_to_maude_string state2);
          Printf.printf "Actual: %s\n" (Substitution.to_string state_subst1);
          Printf.printf "Legacy: %s\n\n" (Substitution.to_string state_subst2);
          Printf.printf "Actual: %s\n" (Substitution.to_string rule_subst1);
          Printf.printf "Legacy: %s\n\n" (Substitution.to_string rule_subst2);
          Printf.printf "Actual: %s\n" rule1;
          Printf.printf "Legacy: %s\n\n" rule2;
        ) raw_succ_transitions raw_succ_transitions_legacy in
      ()
    else ()