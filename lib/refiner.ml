open Logic
open Encoding

module Make (State: Kripke.State) = struct

  module Counterexample = Counterexample.Make(State)

  let get_relevant_track_vars l r track_vars =
    (* all variables in l and r are actually unknowns/arbitrary *)
    let l = List.map (fun (fact_name, args) -> (fact_name ^ "*", List.map Arg_terms.make_vars_unknowns args)) l in
    let r = List.map (fun (fact_name, args) -> (fact_name ^ "*", List.map Arg_terms.make_vars_unknowns args)) r in
    (* let () = Printf.printf "%s -> %s (%s)\n" (Multiset_rewrite_system.ms_to_string l) (Multiset_rewrite_system.ms_to_string r) (String.concat ", " (List.map Multiset_rewrite_system.ms_to_string track_vars)) in *)
    List.concat_map (fun track_var ->
        let track_var = List.map (fun (fact_name, args) -> (fact_name, List.map (Arg_terms.instantiate_unknowns "") args)) track_var in
        let unis = Unification.unify_subset r track_var in
        (* let () = Printf.printf "%s\n" (Unification.to_string unis) in *)
        let unis = Unification.filter_impossible unis in
        if unis = [] then
          (* let () = Printf.printf "A\n" in *)
          (* try r < track_var *)
          let unis = Unification.unify_subset_rest ~unknowns_in_sub:true track_var r in
          List.concat_map (fun (unis, ms) ->
              (* let () = Printf.printf "%s | %s\n" (Unification.to_string unis) (Multiset_rewrite_system.ms_to_string ms) in *)
              let unis = Unification.filter_impossible unis in
              List.map (fun (subst, cond) -> 
                  let l_subst = List.map (fun (fact_name, args) ->
                      (fact_name, List.map (Substitution.apply_arg_unknowns subst) args)
                    ) l in
                  ms @ l_subst
                ) unis
            ) unis
        else
          (* let () = Printf.printf "B\n" in *)
          (* r > track_var *)
          List.map (fun (subst, cond) -> List.map (fun (fact_name, args) ->
              (fact_name, List.map (Substitution.apply_arg_unknowns subst) args)
            ) l) unis
      ) track_vars
    (* |> fun x -> Printf.printf "==> %s\n" (String.concat ", " (List.map Multiset_rewrite_system.ms_to_string x)); x *)

  let replace_non_leading_by_unknown leading_vars track_var =
    List.map (fun (fact_name, args) -> (fact_name, List.map (fun arg -> match arg with
        | Arg_terms.Int Var x when not (List.mem x leading_vars) -> Arg_terms.Int (Unknown x)
        | arg -> arg
      ) args)) track_var

  let sort_relevant_may_edges edges =
    let module Scc = Graph.Components.Make(struct
        type t = Counterexample.edge list
        module V = (struct
          type t = Counterexample.edge
          let compare = Repr.compare
          let hash _ = 0 (* TODO *)
          let equal = Repr.equal
        end)
        let iter_vertex f edges =
          List.iter f edges
        let iter_succ f edges (_, succ_node, _, _) =
          List.iter (fun edge ->
              let (node, _, _, _) = edge in
              if node = succ_node then f edge
              else ()
            ) edges
      end) in
    let sccs = Scc.scc_list edges in
    (* TODO sanity check *)
    let () = List.iter (fun component -> if List.length component != 1 then failwith "Non-trivial component is not supported.") sccs in
    let sorted_edges = List.flatten sccs in
    sorted_edges

  (**
    checks whether two tracking variables are equal up to order of the facts
    TODO should also be capable of checking equality up to unknown renaming
  *)
  let tracking_var_eq track_var1 track_var2 =
    let sorted1 = List.sort Repr.compare track_var1 in
    let sorted2 = List.sort Repr.compare track_var2 in
    sorted1 = sorted2

  let rec add_if_new l x = match l with
    | x'::l when tracking_var_eq x x' -> x'::l
    | x'::l -> x'::(add_if_new l x)
    | [] -> [x]

  let rec update_assoc l a f = match l with
    | [] -> [(a, f None)]
    | (a', b')::l when a = a' -> (a, f (Some b'))::l
    | x::l -> x::update_assoc l a f

  let add_to_track_vars track_vars (fact_name, instance) =
    let (found, track_vars) = List.fold_left_map (fun found (fact_name', instances, is_action) ->
        if fact_name' = fact_name then (true, (fact_name, add_if_new instances instance, is_action))
        else (found, (fact_name', instances, is_action))
      ) false track_vars in
    if found then track_vars
    else (fact_name, [instance], false)::track_vars (* the third parameter is unknown and irrelevant *)

  let rec get_encoding_params ?(refine_loops=false) current_params (maybe_reason: Counterexample.t) (msrs: Multiset_rewrite_system.msrs) property track_vars =
    let leading_vars = Ctl.get_leading_quantified_vars property in

    let relevant_may_edges = Counterexample.get_edges_filtered maybe_reason Counterexample.RELEVANT_MAY_EDGE in
    let relevant_may_edges = sort_relevant_may_edges relevant_may_edges in
    let (required_caps, split_states, _) = List.fold_left (fun (required_caps, split_states, track_vars) edge ->
        let ((stateA, _, ctlA, _), (stateB, _, ctlB, _), edge_type, _) = edge in
        let rule_name = match edge_type with Counterexample.T rule -> rule | _ -> failwith "Illegal state" in
        let (l, r, l_structured, r_structured) =
          let (_, rules) = msrs in
          let (_, l, r, action) = List.find (fun (rule_name', _, _, _) -> rule_name = rule_name') rules in
          (* TODO handling action facts correctly *)
          l, r @ action, Multiset_rewrite_system.ms_to_structured l, Multiset_rewrite_system.ms_to_structured (r @ action) in
        match ctlA with
        | Ctl.A (Ctl.X (Ctl.A (Ctl.U _)))
        | Ctl.A (Ctl.X (Ctl.A (Ctl.W _))) when not refine_loops ->
          (* don't refine loops *)
          (required_caps, split_states, track_vars)
        | Ctl.A _ 
        | Ctl.E _ when true ->
          let new_track_vars = get_relevant_track_vars l r track_vars in
          (* let () = if new_track_vars != [] then Printf.printf "%s -[%s]-> %s\n" (Ctl.to_string ctlA) (rule_name) (Multiset_rewrite_system.ms_to_detailed_string (List.hd new_track_vars)) in *)
          (* TODO!! *)
          (* let () =
            let new_track_vars_old = get_relevant_track_vars_old l r track_vars in
            if not (new_track_vars = new_track_vars_old) then
              (Printf.printf "Not equal:\n";
              List.iter2 (fun track_var track_var_old ->
                  Printf.printf "%s <-> %s\n" (Multiset_rewrite_system.ms_to_string track_var) (Multiset_rewrite_system.ms_to_string track_var_old)
                ) new_track_vars new_track_vars_old)
          in *)
          let new_track_vars = List.map (replace_non_leading_by_unknown leading_vars) new_track_vars in
          (* let () = Printf.printf "%d\n" (List.length relevant_facts); flush stdout in *)
          (* update track vars *)
          let track_vars = List.fold_left (fun track_vars new_track_var -> add_if_new track_vars new_track_var) track_vars new_track_vars in
          (* let track_vars = List.fold_left add_to_track_vars track_vars relevant_facts in *)
          (* let () = List.iter (fun (fact_name, instances, _) -> Printf.printf "Track-var %s: %s\n" fact_name (Multiset_rewrite_system.ms_to_string (List.map (fun instance -> (fact_name, instance)) instances))) track_vars in *)
          (* let () = Printf.printf "Relevant facts: %s\n" (Multiset_rewrite_system.ms_to_string relevant_facts); flush stdout in *)
          (required_caps, (stateA, new_track_vars)::split_states, track_vars)
        | Ctl.E _ ->
          let required_caps = List.fold_left (fun required_caps (fact_name, instances) ->
              update_assoc required_caps fact_name (fun cur_cap ->
                  match cur_cap with
                  | None -> List.length instances
                  | Some cur_cap -> max cur_cap (List.length instances)
                )
            ) required_caps l_structured in
          (required_caps, split_states, track_vars)
        | _ -> failwith "Illegal state"
      ) ([], [], track_vars) relevant_may_edges in

    let relevant_unknowns_edges = Counterexample.get_edges_filtered maybe_reason Counterexample.RELEVANT_UNKNOWNS in
    let non_leading_quantifier_edges = Counterexample.get_edges_filtered maybe_reason Counterexample.NON_LEADING_QUANTIFIER in
    if List.length non_leading_quantifier_edges = 0 && List.length relevant_unknowns_edges = 0 && List.length relevant_may_edges = 0 then
      failwith "Refiner: sanity check failed\n"
    else

    (* use tracked instead of split_states *)
    let tracked = List.fold_left (fun tracked (_, track_vars) -> List.fold_left add_if_new tracked track_vars) current_params.Encoding_params.tracked split_states in
    
    (* don't increase cap, if we already track it differently *)
    let required_caps = List.filter (fun (fact_name, cap) ->
        if List.find_opt (fun track_var -> List.mem_assoc (fact_name ^ "*") track_var) tracked = None then true
        else false
      ) required_caps in

    (* make sure that the required_cap is at least increased by 1 TODO: at the moment not to make it faster *)
    let caps = List.map (fun (fact_name, cap) ->
        match List.assoc_opt fact_name required_caps with
        | None -> (fact_name, cap)
        (* | Some required_cap -> (fact_name, max (cap + 1) required_cap) *)
        | Some required_cap -> (fact_name, max cap required_cap)
      ) current_params.Encoding_params.cap in

    let tracked = Encoding_params.mk_unknowns_distinct tracked in

    let new_params = { current_params with cap = caps; tracked } in
    if new_params = current_params then
      if refine_loops = true then None
      else
        (* try again with allowing refining loops *)
        get_encoding_params ~refine_loops:true current_params maybe_reason msrs property track_vars 
    else Some new_params

end

let%expect_test "test_get_relevant_track_vars" =
  let module Refiner = Make(Kripke.FactState) in
  let open Refiner in
  let open Arg_terms in

  let l = [("P", [Int (Var "a")])] in
  let r = [("Q", [Int (Var "a")])] in
  let track_vars = [[("Q*", [Int (Var "x")])]] in
  let new_track_vars = get_relevant_track_vars l r track_vars in
  Printf.printf "%s" (String.concat "\n" (List.map (fun track_var -> Multiset_rewrite_system.ms_to_string track_var) new_track_vars));
  [%expect {| [P*(x)] |}];

  let l = [("P", [Int (Var "a")])] in
  let r = [("Q1", [Int (Var "a")]); ("Q2", [Int (Var "a")])] in
  let track_vars = [[("Q1*", [Int (Var "x")])]] in
  let new_track_vars = get_relevant_track_vars l r track_vars in
  Printf.printf "%s" (String.concat "\n" (List.map (fun track_var -> Multiset_rewrite_system.ms_to_string track_var) new_track_vars));
  [%expect {| [P*(x)] |}];

  let l = [("P", [Int (Var "a")])] in
  let r = [("Q1", [Int (Var "a")])] in
  let track_vars = [[("Q1*", [Int (Var "x")]); ("Q2*", [Int (Var "x")])]] in
  let new_track_vars = get_relevant_track_vars l r track_vars in
  Printf.printf "%s" (String.concat ", " (List.map (fun track_var -> Multiset_rewrite_system.ms_to_string track_var) new_track_vars));
  [%expect {| [Q2*(x), P*(x)] |}]
