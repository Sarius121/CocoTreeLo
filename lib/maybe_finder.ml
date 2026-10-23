open Logic

type counterexample_status = FOUND | NOT_FOUND | SPURIOUS

(** 
  Contrary to the counterexample finder, the maybe-finder finds transitions in the first-order
  Kripke structure that make the verifier outputting MAYBE. It does not find concrete paths
  that are spurious, but just the transitions in the abstraction. This is probably exactly what
  it needed to refine the abstraction.
*)
module Make (Tableau_product: Tableau_product.Tableau_product) = struct

  module Counterexample = Counterexample.Make(Tableau_product.Kripke.State)

  open Tableau_product
  open Annotation_generator

  let get_outgoing_dependencies tab node =
    let edges = get_outgoing_edges tab node in
    let edges = List.sort (fun edge1 edge2 ->
        match edge1, edge2 with
        | D (_, _, i1), D (_, _, i2) -> i1 - i2
        | _ -> failwith "Expected dependency edges"
      ) edges in
    edges

  let get_outgoing_may_edges tab node =
    let edges = get_outgoing_edges tab node in
    let edges = List.filter (fun edge -> match edge with 
      | T (_, _, (_, _, edge_type, _, _, _, _, _)) -> edge_type = Kripke.ONLY_MAY
      | _ -> false) edges in
    edges

  let get_final ann = match ann with
    | FINAL ann -> ann
    | _ -> failwith "Annotation was not final"

  let to_counterexample_node (state, (ctl, vars)) =
    (state, Kripke.State.to_multiset state, ctl, Substitution.empty)
  
  let to_counterexample_edge edge spurious = match edge with
    | D (nodeA, nodeB, _) -> (to_counterexample_node nodeA, to_counterexample_node nodeB, Counterexample.D, spurious)
    | T (nodeA, nodeB, (_, _, _, _, _, _, _, rule)) -> (to_counterexample_node nodeA, to_counterexample_node nodeB, Counterexample.T rule, spurious)
  
  let add_edge_if_found_anything status counterexample edge =
    match status with
    | FOUND -> Counterexample.add_edge counterexample (to_counterexample_edge edge None)
    | SPURIOUS -> Counterexample.add_edge counterexample (to_counterexample_edge edge (Some Counterexample.INHERITED))
    | NOT_FOUND -> counterexample
  
  let sanity_check_found_anything res = match res with
    | NOT_FOUND -> failwith "sanity check failed"
    | _ -> ()

  let sanity_check_is_true res = if res = true then () else failwith "sanity check failed"

  let is_maybe ann node =
    let ann_tt = get_final (Hashtbl.find ann.tt node) in
    let ann_ff = get_final (Hashtbl.find ann.ff node) in
    if Sat.is_eq ann_tt (Sat.mk_not ann_ff) then false
    else
      if Sat.is_true_opt ann_tt = Some true || Sat.is_true_opt ann_ff = Some true then false
      else true

  let is_true_false ann node expected =
    let ann = if expected then ann.tt else ann.ff in
    let node_ann = get_final (Hashtbl.find ann node) in
    match Sat.is_true_opt node_ann with
    | Some true -> true
    | None -> failwith "Unknown not supported"
    | _ -> false

  (** Generates the formula for the assignment *)
  let gen_assignments_smt next_ann assignments universal =
    let ann_with_unknowns = Sat.mk_quantifier_multi true assignments.Kripke.unknowns next_ann in
    let quantified_ann = Sat.mk_quantifier_multi universal assignments.nondet ann_with_unknowns in
    Substitution.apply_arg_smt assignments.regular quantified_ann

  let are_unknowns_potential_maybe_reason ctl (next_ann_tt, next_ann_ff) (b, a, b_post, a_post) =
    a.Kripke.unknowns != []
    (* let gen_x_annotation positive next_ann =
      match ctl, positive with
      | Ctl.A _, true
      | E _, false ->
        let step1 = Sat.mk_or [Sat.mk_not b_post; gen_assignments_smt next_ann a_post true] in
        (Sat.mk_or [Sat.mk_not b; gen_assignments_smt step1 a true])
      | E _, true
      | A _, false ->
        let step1 = Sat.mk_and [b_post; gen_assignments_smt next_ann a_post false] in
        (Sat.mk_and [b; gen_assignments_smt step1 a false])
      | _ -> failwith "Illegal state"
    in
    let ann_tt = gen_x_annotation true next_ann_tt in
    let ann_ff = gen_x_annotation false next_ann_ff in
    match Sat.is_true_opt ann_tt, Sat.is_true_opt ann_ff with
    | Some true, _
    | _, Some true -> false
    | None, _
    | _, None -> failwith "Unknown not supported"
    | _ -> true *)

  let are_quantifiers_potential_maybe_reason ctl (next_ann_tt, next_ann_ff) var var_dependencies =
    let gen_annotation positive next_ann =
      match ctl, positive with
      | Ctl.FORALL _, true
      | EXISTS _, false ->
        let dependent_vars = Option.value ~default:[] (Hashtbl.find_opt var_dependencies var) in
        let dependencies_quantified = Sat.mk_forall_multi dependent_vars next_ann in
        Sat.mk_forall var dependencies_quantified
      | EXISTS _, true
      | FORALL _, false ->
        let dependent_vars = Option.value ~default:[] (Hashtbl.find_opt var_dependencies var) in
        let dependencies_quantified = Sat.mk_forall_multi dependent_vars next_ann in
        Sat.mk_exists var dependencies_quantified
      | _ -> failwith "Illegal state"
    in
    let ann_tt = gen_annotation true next_ann_tt in
    let ann_ff = gen_annotation false next_ann_ff in
    match Sat.is_true_opt ann_tt, Sat.is_true_opt ann_ff with
    | Some true, _
    | _, Some true -> false
    | None, _
    | _, None -> failwith "Unknown not supported"
    | _ -> true

  let find_counterexample tab var_dependencies ann kripke ctl =

    (* TODO all initial states besides the first are ignored *)
    let initial_states = Kripke.get_initial_states kripke in
    let initial_state = List.hd initial_states in
    let initial_node = (initial_state, (ctl, [])) in
    let initial_counterexample_node = (to_counterexample_node initial_node) in
    let initial_counterexample = Counterexample.create initial_counterexample_node in

    let node_num, _ = Tableau_product.get_stats tab in
    let result_table = Hashtbl.create node_num in

    (** 
      positive = true: we search for a proof that ann=true would be correct
      positive = false: we search for a proof that ann=false would be correct
    *)
    let rec find_failing_path ?(visited=[]) counterexample node =
      let res = Hashtbl.find_opt result_table node in
      match res with
      | Some res ->
        (* no new maybe information can be gathered, so don't add it to the counterexample *)
        (res, counterexample)
      | None ->
        let (res, counterexample) = compute_result visited counterexample node in
        let () = Hashtbl.add result_table node res in
        (res, counterexample)
    and compute_result visited counterexample node =
      (* let () = Printf.printf "Check %s\n" (node_to_string node); flush stdout in *)
      (* let () = Printf.printf "- %s\n" (Sat.to_string node_ann) in *)
      if not (is_maybe ann node) then (NOT_FOUND, counterexample)
      else
        let (_, (ctl, _)) = node in
        (match ctl with
        | Ctl.FACT _
        | Ctl.NOTFACT _
        | Ctl.B _ ->
          (FOUND, counterexample)
        (** need one maybe successor to output FOUND, but add all maybe successors to the counterexample *)
        | Ctl.AND _
        | Ctl.OR _ ->
          let (found_valid, counterexample) = List.fold_left (fun (found_valid, counterexample) edge ->
            match edge with
            | D (_, succ, _)
            | T (_, succ, _) ->
              let (res, counterexample) = find_failing_path counterexample succ in
              let counterexample = add_edge_if_found_anything res counterexample edge in
              (found_valid || res = FOUND, counterexample)
            ) (false, counterexample) (get_outgoing_edges tab node) in
          sanity_check_is_true found_valid;
          (FOUND, counterexample)
        | Ctl.FORALL (leading, var, _)
        | Ctl.EXISTS (leading, var, _) ->
          let succ = List.hd (get_successors tab node) in
          let (res, counterexample) = find_failing_path counterexample succ in
          let counterexample = add_edge_if_found_anything res counterexample (D (node, succ, 0)) in
          if res = FOUND then
            (res, counterexample)
          else
            (* node is maybe, but nothing found in children => the quantifier is the maybe reason *)
            let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge (D (node, succ, 0)) (Some Counterexample.NON_LEADING_QUANTIFIER)) in
            (FOUND, counterexample)
            (* ideas on how to check it: *)
            (* let is_maybe_reason = leading_quantifier = false && are_quantifiers_potential_maybe_reason ctl (get_final (Hashtbl.find ann.tt succ), get_final (Hashtbl.find ann.ff succ)) var var_dependencies in
            if is_maybe_reason then 
              let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge (D (node, succ, 0)) (Some Counterexample.NON_LEADING_QUANTIFIER)) in
              (FOUND, counterexample)
            else
              (sanity_check_found_anything NOT_FOUND;
              (NOT_FOUND, counterexample)) *)
        | Ctl.A (Ctl.X _)
        | Ctl.E (Ctl.X _) ->
          let (found_valid, new_counterexample) = List.fold_left (fun (found_valid, counterexample) edge ->
              match edge with
              | D (_, _, _) -> failwith "Strange tableau"
              | T (_, succ, (_, _, MAY_AND_MUST, b, a, b_post, a_post, _)) ->
                let (res, counterexample) =  find_failing_path counterexample succ ~visited:visited in
                let counterexample = add_edge_if_found_anything res counterexample edge in
                if res = FOUND then 
                  (true, counterexample)
                else
                  let is_maybe_reason = are_unknowns_potential_maybe_reason ctl (get_final (Hashtbl.find ann.tt succ), get_final (Hashtbl.find ann.ff succ)) (b, a, b_post, a_post) in
                  if is_maybe_reason then
                    let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge edge (Some Counterexample.RELEVANT_UNKNOWNS)) in
                    (true, counterexample)
                  else
                    (found_valid, counterexample)
              (** if we are in an AU/AW loop, a may edge is probably not the problem,
                because we want to prove something for all nodes and the may edge definitely exists for some node 
                -> this is not entirely true: we might have an AU/AW only in a state where we are already restricted to some P*
              *)
              (* | T (_, succ, (_, _, ONLY_MAY, _, _, _, _, _)) when visited != [] && (match ctl with | Ctl.A _ -> true | _ -> false) ->
                let (res, counterexample) = find_failing_path counterexample succ ~visited:visited in
                let counterexample = add_edge_if_found_anything res counterexample edge in
                (found_valid || res = FOUND, counterexample) *)
              | T (_, succ, (_, _, ONLY_MAY, b, a, b_post, a_post, _)) ->
                let is_not_maybe_reason = match ctl with
                  (* we cannot really make this more precise without running the complete annotation again with this one edge being MUST.
                  So this only checks whether it's definitely not the maybe reason *)
                  | Ctl.A _ -> is_true_false ann succ true
                  | Ctl.E _ -> is_true_false ann succ false
                  | _ -> failwith "Illegal state"
                in
                if is_not_maybe_reason then
                  (found_valid, counterexample)
                else
                  let (res, counterexample) = find_failing_path counterexample succ ~visited:visited in
                  let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge edge (Some Counterexample.RELEVANT_MAY_EDGE)) in
                  (true, counterexample)
            ) (false, counterexample) (get_outgoing_edges tab node) in
          sanity_check_is_true found_valid;
          (FOUND, new_counterexample)
        | Ctl.A _
        | Ctl.E _ ->
          if Option.is_some (List.find_opt ((=) node) visited) then
            (FOUND, counterexample)
          else
            let visited = node::visited in
            (match get_outgoing_dependencies tab node with
              | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
                let (res_phi2, counterexample) = find_failing_path counterexample succ_phi2 in
                let counterexample = add_edge_if_found_anything res_phi2 counterexample (D (node, succ_phi2, 1)) in

                let (res_phi1, counterexample) = find_failing_path counterexample succ_phi1 in
                let counterexample = add_edge_if_found_anything res_phi1 counterexample (D (node, succ_phi1, 0)) in
                  
                let (res_next, counterexample) = find_failing_path counterexample succ_next ~visited:visited in
                let counterexample = add_edge_if_found_anything res_next counterexample (D (node, succ_next, 2)) in
                
                sanity_check_is_true (res_phi1 = FOUND || res_phi2 = FOUND || res_next = FOUND);
                (FOUND, counterexample)
              | _ -> failwith "Illegal tableau"
            )
        | _ -> failwith "Unsupported node")
    in
    find_failing_path initial_counterexample initial_node
end
