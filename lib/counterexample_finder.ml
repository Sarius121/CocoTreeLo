open Logic

type counterexample_status = FOUND | NOT_FOUND | SPURIOUS

module Make (Tableau_product: Tableau_product.Tableau_product) = struct

  module Counterexample = Counterexample.Make(Tableau_product.Kripke.State)

  open Tableau_product
  open Annotation_generator

  (** Generates the formula for the assignment *)
  let gen_assignments_smt next_ann assignments universal =
    let quantified_ann = Sat.mk_quantifier_multi universal assignments.Kripke.nondet next_ann in
    Substitution.apply_arg_smt assignments.regular quantified_ann

  let prefix_vars smt vars prefix =
    let nondet_subst_s = List.map (fun var -> prefix ^ var) vars in
    let nondet_subst = List.map (fun var -> Sat.mk_var var) nondet_subst_s in
    (nondet_subst_s, Sat.subst_vars smt vars nondet_subst)

  (** updates the assignment a_regular to use no unknowns
      @param ms state in the succ state
      @param subst substition in the current state
      @param a_regular the post assignment
      @param track_vars a list of all track-vars
    *)
  let specify_track_var_assignments ms subst a_regular track_vars =
    let rec remove_consts ms = match ms with
      | Multiset_rewrite_system.Const _ -> Multiset_rewrite_system.Const []
      | Var var -> Var var
      | Union (ms1, ms2) -> Union (remove_consts ms1, remove_consts ms2)
      | _ -> failwith "Illegal state"
    in
    let ms_star = remove_consts ms in

    let new_subst = Substitution.compose subst a_regular in
    let ms_star = Substitution.apply_ms new_subst ms_star in

    let possible_ms_star = Multiset_rewrite_system.term_simplify_with_constraints ms_star in
    let possible_ms_star = List.map (fun (cond, possible_ms) -> match possible_ms with
        | Multiset_rewrite_system.Const possible_ms -> (cond, possible_ms)
        | _ -> failwith "Cannot find the counterexample"
      ) possible_ms_star in

    let possible_subst = List.map (fun (cond, possible_ms) ->
        let a_regular_arg = List.map (fun (var, value) ->
            if String.starts_with ~prefix:"Track" var then
              let track_var = List.find (fun track_var -> Encoding.Maude_narrowing_combi.track_var_to_string track_var = var) track_vars in
              let track_var = List.map (fun (fact_name, args) -> (Encoding.Maude_narrowing_combi.get_fact_name_of_star_var fact_name, args)) track_var in
              let uni = Unification.unify_subset ~unknowns_in_sub:true possible_ms track_var in
              let uni = Unification.filter_impossible uni in
              (var, Arg_terms.Bool (Smt (Unification.to_sat uni)))
            else (var, value)
          ) a_regular.Substitution.arg_subst in

        (cond, { a_regular with Substitution.arg_subst=a_regular_arg })
      ) possible_ms_star in
    possible_subst

  let assign_track_vars ms subst track_vars =
    let rec remove_consts ms = match ms with
      | Multiset_rewrite_system.Const _ -> Multiset_rewrite_system.Const []
      | Var var -> Var var
      | Union (ms1, ms2) -> Union (remove_consts ms1, remove_consts ms2)
      | _ -> failwith "Illegal state"
    in
    let ms_star = remove_consts ms in
    let ms_star = Substitution.apply_ms subst ms_star in

    let ms_star = Multiset_rewrite_system.term_simplify ms_star in
    let ms_star = match ms_star with
        | Multiset_rewrite_system.Const ms_star -> ms_star
        | _ -> failwith "Illegal state"
    in

    let possible_subst_regular = List.map (fun (var, value) ->
      if String.starts_with ~prefix:"Track" var then
        let track_var = List.find (fun track_var -> Encoding.Maude_narrowing_combi.track_var_to_string track_var = var) track_vars in
        let track_var = List.map (fun (fact_name, args) -> (Encoding.Maude_narrowing_combi.get_fact_name_of_star_var fact_name, args)) track_var in
        let uni = Unification.unify_subset ~unknowns_in_sub:true ms_star track_var in
        let uni = Unification.filter_impossible uni in
        (var, Arg_terms.Bool (Smt (Unification.to_sat uni)))
      else (var, value)
    ) subst.arg_subst in

    { subst with Substitution.arg_subst=possible_subst_regular }

  let get_unknowns_from_edges edges =
    List.fold_left (fun unknowns edge -> match edge with
        | D (_, succ, _) -> failwith "Strange tableau"
        | T (_, succ, (_, _, trans_type, b, a, b_post, a_post, rule)) ->
          (* TODO does trans_type matter? *)
           Utils.Str_utils.StringSet.add_seq (List.to_seq a.unknowns) unknowns
      ) Utils.Str_utils.StringSet.empty edges
    |> Utils.Str_utils.StringSet.to_list

  let gen_assignments_smt_no_quantification next_ann assignments prefix =
    let (nondets, quantified_ann) = prefix_vars next_ann assignments.Kripke.nondet prefix in
    (nondets, Substitution.apply_arg_smt assignments.regular quantified_ann)

  let generate_star_constraint a_post substs =
    let a_post_star = { a_post with Substitution.arg_subst = [] } in
    let substs_star = Substitution.restrict substs (String.ends_with ~suffix:"*") in
    let new_subst_star = Substitution.compose substs_star a_post_star in
    Sat.mk_and (List.map (fun (_, value) -> Multiset_rewrite_system.gen_term_validity_smt value) new_subst_star.ms_subst)

  (* give dummy values to all variables that are irrelevant (i.e. not part of the model) *)
  let make_model_complete model vars =
    List.map (fun var ->
        if Sat.is_bool_var var then
          (var, Arg_terms.(Bool (Smt (List.assoc_opt var model |> Option.value ~default:(Sat.mk_bool false)))))
        else
          (var, Arg_terms.(Int (Smt (List.assoc_opt var model |> Option.value ~default:(Sat.mk_int 0)))))
      ) vars

  let check_transition ?(side_constraint=Sat.mk_bool true) ?(soft_constraint=None) next_ann condition assignments substs  =
    (* let () = Printf.printf "%s\n" (String.concat ", " (List.map (fun (var) -> var ^ "->?") nondet)) in
    let () = Printf.printf "%s\n" (String.concat ", " (List.map (fun (var, value) -> var ^ "->" ^ Sat.to_string value) substs)) in
    let () = Printf.printf "%s\n" (String.concat ", " (List.map2 (fun var value -> var ^ "->" ^ Sat.to_string value) concrete_vars concrete_exprs)) in *)
    let substs = Substitution.compose substs assignments.Kripke.regular in
    (* let () = Printf.printf "%s\n" (String.concat ", " (List.map (fun (var, value) -> var ^ "->" ^ Sat.to_string value) substs)) in *)
    let filtered_substs = Substitution.restrict substs (fun var -> Option.is_none (List.find_opt ((=) var) assignments.nondet)) in
    let next_ann = Substitution.apply_arg_smt filtered_substs next_ann in
    let model = match soft_constraint with
      | Some soft_constraint -> Sat.is_sat_model_soft next_ann soft_constraint ~side_constraint:side_constraint
      | None -> Sat.is_sat_model next_ann ~side_constraint:side_constraint
    in
    Option.fold model ~none:None ~some:(fun model ->
        (* let model = List.map (fun (var, value) -> if var = "v0" then (var, Sat.mk_int 5) else (var, value)) model in *)
        let model = make_model_complete model assignments.nondet in
        let model = Substitution.{ ms_subst = []; arg_subst = model } in
        (* let () = Printf.printf "%s\n\n" (String.concat ", " (List.map (fun (var, value) -> var ^ "->" ^ Sat.to_string value) model)) in *)
        let quantified_ann = Substitution.apply_arg_smt model next_ann in
        let new_substs = Substitution.concat model filtered_substs in
        let subst_ann = Substitution.apply_arg_smt assignments.regular quantified_ann in
        let complete_trans = Sat.mk_and [Sat.mk_and condition; subst_ann] in
        match Sat.is_unsat_opt complete_trans with
          | Some true -> None (* the condition makes it UNSAT *)
          | Some false -> Some new_substs (* still SAT -> counterexample *)
          | None -> failwith "Unknown is not supported"
      )

  let get_outgoing_dependencies tab node =
    let edges = get_outgoing_edges tab node in
    let edges = List.sort (fun edge1 edge2 ->
        match edge1, edge2 with
        | D (_, _, i1), D (_, _, i2) -> i1 - i2
        | _ -> failwith "Expected dependency edges"
      ) edges in
    edges

  let get_final ann = match ann with
    | FINAL ann -> ann
    | _ -> failwith "Annotation was not final"

  let get_ann_potentially_negated ann node why_true =
    let node_ann = get_final (Hashtbl.find ann node) in
    if why_true then node_ann else Sat.mk_not node_ann

  let to_counterexample_node (state, (ctl, vars)) substs =
    let substs = Substitution.simplify substs in
    (state, Kripke.State.to_multiset state, ctl, substs)
  
  let to_counterexample_edge edge substA substB spurious = match edge with
    | D (nodeA, nodeB, _) -> (to_counterexample_node nodeA substA, to_counterexample_node nodeB substB, Counterexample.D, spurious)
    | T (nodeA, nodeB, (_, _, _, _, _, _, _, rule)) -> (to_counterexample_node nodeA substA, to_counterexample_node nodeB substB, Counterexample.T rule, spurious)
  
  let add_edge_if_found_anything status counterexample edge substA substB =
    match status with
    | FOUND -> Counterexample.add_edge counterexample (to_counterexample_edge edge substA substB None)
    | SPURIOUS -> Counterexample.add_edge counterexample (to_counterexample_edge edge substA substB (Some Counterexample.INHERITED))
    | NOT_FOUND -> counterexample
  
  let sanity_check_found_anything res = match res with
    | NOT_FOUND -> failwith "sanity check failed"
    | _ -> ()

  let gen_constraint_condition track_var_subst succ_constraint =
    let constraint_correct_cond = List.map (fun (track_var, value) ->
        let track_var_subst_value =
          Substitution.get_arg_opt track_var_subst (Encoding.Maude_narrowing_combi.track_var_to_string track_var)
          |> Option.get
          |> Arg_terms.to_smt
        in
        Sat.mk_eq (Sat.mk_bool value) track_var_subst_value
      ) succ_constraint in

    Sat.mk_and constraint_correct_cond

  let gen_transition_ann_why_false ann edges =
    let smts = List.map (fun edge ->
        match edge with
        | D (_, succ, _) -> failwith "Strange tableau"
        | T (_, succ, (_, _, trans_type, b, a, b_post, a_post, _)) ->
          let succ_ann = get_ann_potentially_negated ann succ false in
          let step1 = Sat.mk_and [(Sat.mk_and b_post); gen_assignments_smt succ_ann a_post false] in
          Sat.mk_and [Sat.mk_and b; gen_assignments_smt step1 a false]
      ) edges in
    Sat.mk_or smts

  let handle_ax_ex_why_true ?(update_a=(fun a _ _ -> a)) tab ann track_vars node subst counterexample length_limited f_rec =
    let outgoing_edges = get_outgoing_edges tab node in

    let (_, found_valid, new_counterexample) = List.fold_left (fun (i, found_valid, counterexample) edge ->
      if found_valid then (i+1, found_valid, counterexample)
      else match edge with
        | D (_, succ, _) -> failwith "Strange tableau"
        | T (_, succ, (_, _, trans_type, b, a, b_post, a_post, rule)) ->
          if trans_type = ONLY_MAY then (i+1, found_valid, counterexample)
          else
            let (succ_state, _) = succ in
            let possible_a_post = specify_track_var_assignments (Kripke.State.to_multiset succ_state) subst a_post.regular track_vars in
            (* let () = List.iter (fun (cond, subst) -> Printf.printf "- (%s, %s)\n" (Sat.to_string cond) (Substitution.to_string subst)) possible_a_post in *)

            let (_, found_valid, counterexample) = List.fold_left (fun (j, found_valid, counterexample) (cond, a_post_regular) ->
                if found_valid then (j+1, found_valid, counterexample)
                else
                  (* change track-var assignments to use no unknowns *)
                  let a_post = { a_post with Kripke.regular = a_post_regular } in
                  let constraint_correct_cond = gen_constraint_condition a_post_regular (Kripke.State.get_constraints succ_state) in
                  (* replace constraint correct condition *)
                  let b_post = match b_post with
                    | [regular_cond; constraint_cond] -> [cond; regular_cond; constraint_correct_cond]
                    | _ -> failwith "Illegal state" in

                  (* update a, if the nondets get concrete values *)
                  let a = update_a a i j in
                  (* sanity check *)
                  let () = if not (a_post.nondet = []) then failwith "nondets in a_post are currently not supported" in

                  let succ_ann = get_ann_potentially_negated ann succ true in
                  let succ_ann_post = Sat.mk_and [Sat.mk_and b_post; gen_assignments_smt succ_ann a_post false] in
                  (* TODO: side_constraint probably not needed *)
                  let side_constraint = generate_star_constraint a_post.regular subst in
                  let new_subst_opt = check_transition succ_ann_post b a subst ~side_constraint:side_constraint in
                  Option.fold new_subst_opt ~none:(j+1, found_valid, counterexample) ~some:(fun new_subst ->
                      let new_subst_opt = check_transition succ_ann b_post a_post new_subst in
                      (* no nondets in a_post -> no reason for new_subst_opt to be None *)
                      let new_subst = Option.get new_subst_opt in
                      let (res, counterexample) = f_rec i j counterexample succ new_subst in
                      let () = if not length_limited then sanity_check_found_anything res in
                      let counterexample = add_edge_if_found_anything res counterexample edge subst new_subst in
                      (j+1, res = FOUND, counterexample)
                    )
              ) (0, found_valid, counterexample) possible_a_post in
            (i+1, found_valid, counterexample)
      ) (0, false, counterexample) outgoing_edges in
    if found_valid then (FOUND, new_counterexample)
    else if length_limited then (NOT_FOUND, counterexample) else failwith "Sanity check failed"

  let possible_a_post_as_condition possible_a_post =
    let cond = List.map (fun (cond, subst) ->
        let subst_cond = List.map (fun (var, value) -> Sat.mk_eq (Sat.mk_var var) (Arg_terms.to_smt value)) subst.Substitution.arg_subst in
        Sat.mk_and (cond::subst_cond)
      ) possible_a_post in
    Sat.mk_and cond

  let handle_ax_ex_why_false ?(update_a=(fun a _ -> a)) ?(inst_unknowns) tab ann track_vars node subst counterexample length_limited f_rec =
    let outgoing_edges = get_outgoing_edges tab node in

    (* find an assignment of the unknowns that makes the formula true *)
    let model = Option.fold inst_unknowns ~none:(
        let trans_ann = gen_transition_ann_why_false ann outgoing_edges in
        let unknowns = get_unknowns_from_edges outgoing_edges in
        let model = Option.get (Sat.is_sat_model trans_ann) in
        make_model_complete model unknowns
      )
      ~some:(fun inst_unknowns ->
        let unknowns = get_unknowns_from_edges outgoing_edges in
        inst_unknowns unknowns
      ) in
    let model = { Substitution.arg_subst = model; ms_subst = [] } in
    (* let () = Printf.printf "Unknown assignment: %s\n" (Substitution.to_string model) in *)
    let new_subst = Substitution.compose subst model in

    let (_, found_anything, found_valid, new_counterexample) = List.fold_left (fun (i, found_anything, found_valid, counterexample) edge ->
      if found_valid then (i+1, found_anything, found_valid, counterexample)
      else match edge with
        | D (_, succ, _) -> failwith "Strange tableau"
        | T (_, succ, (_, _, trans_type, b, a, b_post, a_post, rule)) ->
          (* generate a condition whether the transition is legal and the unknowns are correct *)
          let (succ_state, _) = succ in
          let possible_a_post = specify_track_var_assignments (Kripke.State.to_multiset succ_state) subst a_post.regular track_vars in
          (* TODO maybe this condition is repetitive here, because it is already part of b_post? *)
          let possible_a_post = List.map (fun (cond, subst) ->
              let constraint_correct_cond = gen_constraint_condition subst (Kripke.State.get_constraints succ_state) in
              (Sat.mk_and [cond; constraint_correct_cond], subst)) possible_a_post in
          let unknowns_are_correct_and_transition_legal = possible_a_post_as_condition possible_a_post in

          (* update a, if the nondets get concrete values *)
          let a = update_a a i in
          (* sanity check *)
          let () = if not (a_post.nondet = []) then failwith "nondets in a_post are currently not supported" in

          let succ_ann = get_ann_potentially_negated ann succ false in
          let succ_ann_with_constraint = Sat.mk_and [succ_ann; unknowns_are_correct_and_transition_legal] in
          let succ_ann_with_constraint = Sat.mk_and [Sat.mk_and b_post; gen_assignments_smt succ_ann_with_constraint a_post false] in
          (* TODO: probably star_constraint is not needed *)
          let side_constraint = generate_star_constraint a_post.regular new_subst in
          let new_subst_opt = check_transition succ_ann_with_constraint b a new_subst ~side_constraint:side_constraint in
          let (new_subst_opt, spurious) =
            if new_subst_opt = None then
              (* If it works without the side_constraint, we found a spurious path.
                Still continue to get the exact spurious transition in the counterexample.
                (we can set spurious to true here, because it is ignored for new_subst_opt = None anyway) *)
              let succ_ann_post = Sat.mk_and [Sat.mk_and b_post; gen_assignments_smt succ_ann a_post false] in
              (check_transition succ_ann_post b a subst, true)
            else (new_subst_opt, false)
          in
          Option.fold new_subst_opt ~none:(i+1, found_anything, found_valid, counterexample) ~some:(fun new_subst ->
              let new_subst_opt = check_transition succ_ann b_post a_post new_subst in
              (* no unknowns in a_post -> must not be None *)
              let new_subst = Option.get new_subst_opt in
              if spurious then
                let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge edge subst new_subst (Some Counterexample.REMOVES_NON_EXISTENT_FACT_OR_RELEVANT_UNKNOWNS)) in
                (i+1, true, found_valid, counterexample)
              else
                let (res, counterexample) = f_rec i counterexample succ new_subst in
                let () = if not length_limited then sanity_check_found_anything res in
                let counterexample =
                  if trans_type = Kripke.ONLY_MAY then
                    (* transition is extra marked with UNPROBLEMATIC_RELEVANT_MAY_EDGE, if we found something below, because it is a correct may edge, but Bohn's algorithm can't use it *)
                    match res with
                    | NOT_FOUND -> counterexample
                    | _ -> Counterexample.add_edge counterexample (to_counterexample_edge edge subst new_subst (Some Counterexample.UNPROBLEMATIC_RELEVANT_MAY_EDGE))
                  else add_edge_if_found_anything res counterexample edge subst new_subst
                in
                (i+1, true, res = FOUND, counterexample)
            )
      ) (0, false, false, counterexample) outgoing_edges in
    if found_valid then (FOUND, new_counterexample)
    else if found_anything then (SPURIOUS, new_counterexample)
    else if length_limited then (NOT_FOUND, counterexample) else failwith "Sanity check failed"

  let find_counterexample tab ann kripke track_vars dependent_track_vars ctl res =
    (* 
      select what to find a counterexample/proof for
      - verified: proof that the property verifies
      - falsified: proof that the property is falsified
      - maybe: proof why the property is not verified 
    *)
    let (ann, positive, why_true, not_possible) = match res, Ctl.get_type ctl with
      | Some true, ECTL
      | Some true, ANY -> ann.Annotation_generator.tt, true, true, false
      | None, ECTL -> ann.ff, true, false, false
      | Some false, ACTL
      | Some false, ANY -> ann.ff, false, true, false
      | None, ACTL -> ann.tt, false, false, false
      | _ -> ann.tt, false, false, true
    in
    if not_possible then None
    else

    (* TODO all initial states besides the first are ignored
      (not important at the moment, because the encoding only generates one initial state anyway) *)
    let initial_states = Kripke.get_initial_states kripke in
    let initial_state = List.hd initial_states in

    let rec find_failing_path counterexample node substs =
      (* check whether this node with the substitution is a counterexample *)
      let node_ann = get_ann_potentially_negated ann node why_true in
      let node_ann = Substitution.apply_arg_smt substs node_ann in
      let is_unsat = Option.get (Sat.is_unsat_opt node_ann) in

      (* let () = Printf.printf "Check %s %s -> %B\n" (node_to_string node) (Substitution.to_string substs) is_unsat; flush stdout in *)
      (* let () = Printf.printf "- %s\n" (Sat.to_string node_ann) in *)
      
      if is_unsat then (NOT_FOUND, counterexample)
      else
        let (_, (ctl, _)) = node in
        (match ctl, positive with
        | Ctl.FACT _, _
        | Ctl.NOTFACT _, _
        | Ctl.B _, _ ->
          (FOUND, counterexample)
        | Ctl.AND _, false
        | Ctl.OR _, true ->
          (* one child has to be a counterexample *)
          let (found_valid, counterexample) = List.fold_left (fun (found_valid, counterexample) edge ->
            if found_valid then (found_valid, counterexample)
            else
              match edge with
                | D (_, succ, _)
                | T (_, succ, _) ->
                  let (res, counterexample) = find_failing_path counterexample succ substs in
                  let counterexample = add_edge_if_found_anything res counterexample edge substs substs in
                  (res = FOUND, counterexample)
            ) (false, counterexample) (get_outgoing_edges tab node) in
          if found_valid then (FOUND, counterexample)
          else (SPURIOUS, counterexample)
        | Ctl.OR _, false
        | Ctl.AND _, true ->
          (* all children have to be counterexamples *)
          let (anything_spurious, counterexample) = List.fold_left (fun (anything_spurious, counterexample) edge ->
            if anything_spurious then
              (* we can stop here, because this path will definitely be spurious *)
              (anything_spurious, counterexample)
            else
              match edge with
                | D (_, succ, _)
                | T (_, succ, _) ->
                  let (res, counterexample) = find_failing_path counterexample succ substs in
                  let counterexample = add_edge_if_found_anything res counterexample edge substs substs in
                  match res with
                  | NOT_FOUND -> failwith "Illegal state"
                  | SPURIOUS -> (true, counterexample)
                  | FOUND -> (false, counterexample)
            ) (false, counterexample) (List.rev (get_outgoing_edges tab node)) in
          if anything_spurious then (SPURIOUS, counterexample)
          else (FOUND, counterexample)
        | Ctl.FORALL (leading, var, _), false
        | Ctl.EXISTS (leading, var, _), true ->
          let succ = List.hd (get_successors tab node) in
          let succ_ann = get_ann_potentially_negated ann succ why_true in

          let dependent_track_vars = if leading then [] else Option.value ~default:[] (Hashtbl.find_opt dependent_track_vars var) in
          let succ_ann_with_unknowns = Sat.mk_quantifier_multi why_true dependent_track_vars succ_ann in

          (* remove the current value of this quantified variable (it shouldn't have a value yet, if the variables are unique) *)
          let filtered_substs = Substitution.restrict substs (fun var' -> not (var = var')) in
          let succ_ann_with_unknowns = Substitution.apply_arg_smt filtered_substs succ_ann_with_unknowns in

          (* find a value for the variable that is a counterexample *)
          let model_opt = Sat.is_sat_model succ_ann_with_unknowns in
          let model = Option.get model_opt in

          (* give dummy value to variable if var is irrelevant (i.e. is not part of the model) *)
          let value = Option.value ~default:(Sat.mk_int 0) (List.assoc_opt var model) in
          let new_subst = Substitution.add_arg substs var Arg_terms.(Int (Smt value)) in

          (* assign unknowns *)
          let (state, _) = node in
          let new_subst = assign_track_vars (Kripke.State.to_multiset state) new_subst track_vars in

          let (res, counterexample) = find_failing_path counterexample succ new_subst in
          let counterexample = add_edge_if_found_anything res counterexample (D (node, succ, 0)) substs new_subst in
          if res = NOT_FOUND && why_true then failwith "sanity check failed"
          else if res = NOT_FOUND then
            let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge (D (node, succ, 0)) substs new_subst (Some Counterexample.NON_LEADING_QUANTIFIER)) in
            (SPURIOUS, counterexample)
          else
            (res, counterexample)
        | Ctl.A (Ctl.X _), false
        | Ctl.E (Ctl.X _), true ->
          if why_true
            then handle_ax_ex_why_true tab ann track_vars node substs counterexample false (fun _ _ -> find_failing_path)
            else handle_ax_ex_why_false tab ann track_vars node substs counterexample false (fun _ -> find_failing_path)
        | Ctl.A (Ctl.W _), false
        | Ctl.E (Ctl.U _), true -> find_failing_path_aw_eu counterexample node substs
        | Ctl.A (Ctl.U _), false
        | Ctl.E Ctl.W _, true -> find_failing_path_au_ew counterexample node substs []
        | _ -> failwith "Unsupported node")
    and find_failing_path_aw_eu counterexample node subst =
      let rec build_bounded_counterexample_smt node subst length path_prefix =
        if length = 0 then ([], Sat.mk_bool false)
        else
          let (_, (ctl, _)) = node in
          match ctl, positive with
          | Ctl.A Ctl.W _, false ->
            (match get_outgoing_dependencies tab node with
              | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
                let ann_phi1 = get_ann_potentially_negated ann succ_phi1 why_true in
                let ann_phi2 = get_ann_potentially_negated ann succ_phi2 why_true in
                let (nondets, ann_next_bounded) = build_bounded_counterexample_smt succ_next subst (length - 1) path_prefix in
                (nondets, Sat.mk_and [ann_phi2; Sat.mk_or [ann_phi1; ann_next_bounded]])
              | _ -> failwith "Illegal tableau")
          | Ctl.E Ctl.U _, true ->
            (match get_outgoing_dependencies tab node with
              | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
                let ann_phi1 = get_ann_potentially_negated ann succ_phi1 why_true in
                let ann_phi2 = get_ann_potentially_negated ann succ_phi2 why_true in
                let (nondets, ann_next_bounded) = build_bounded_counterexample_smt succ_next subst (length - 1) path_prefix in
                (nondets, Sat.mk_or [ann_phi2; Sat.mk_and [ann_phi1; ann_next_bounded]])
              | _ -> failwith "Illegal tableau")
          | Ctl.A Ctl.X _, false
          | Ctl.E Ctl.X _, true ->
            if why_true then
              let outgoing_edges = get_outgoing_edges tab node in
              let smt_transitions = List.concat (List.mapi (fun i edge ->
                  match edge with
                  | D _ -> failwith "Illegal tableau"
                  | T (_, succ, (_, _, _, b, a, b_post, a_post, _)) ->

                    let (succ_state, _) = succ in
                    let possible_a_post = specify_track_var_assignments (Kripke.State.to_multiset succ_state) subst a_post.regular track_vars in

                    List.mapi (fun j (cond, a_post_regular) ->
                        let a_post = { a_post with Kripke.regular = a_post_regular } in
                        let constraint_correct_cond = gen_constraint_condition a_post_regular (Kripke.State.get_constraints succ_state) in
                        (* replace constraint correct condition *)
                        let b_post = match b_post with
                          | [regular_cond; constraint_cond] -> [cond; regular_cond; constraint_correct_cond]
                          | _ -> failwith "Illegal state" in

                        let prefix = Printf.sprintf "pre_%d_%d_%s" i j path_prefix in
                        let path_prefix = Printf.sprintf "%d_%d_%s" i j path_prefix in

                        let a_nondet = List.fold_left (fun a_nondet var -> Substitution.add_arg a_nondet var (Arg_terms.Int (Var (prefix ^ var)))) Substitution.empty a.nondet in
                        let a_post_nondet = List.fold_left (fun a_nondet var -> Substitution.add_arg a_nondet var (Arg_terms.Int (Var (prefix ^ var)))) Substitution.empty a_post.nondet in
                        
                        let next_subst = Substitution.compose a_post.regular a_post_nondet in
                        let next_subst = Substitution.compose a_nondet next_subst in
                        let next_subst = Substitution.compose a.Kripke.regular next_subst in
                        let next_subst = Substitution.compose subst next_subst in

                        let (nondets, ann_next_bounded) = build_bounded_counterexample_smt succ next_subst length path_prefix in
                        
                        let (nondet_post, step1) = gen_assignments_smt_no_quantification ann_next_bounded a_post "" in
                        let step1 = Sat.mk_and [Sat.mk_and b_post; step1] in
                        let (nondet, step2) = gen_assignments_smt_no_quantification step1 a prefix in
                        (* let () = Printf.printf "%d,%d : %s\n" i j (Sat.to_string (Sat.mk_and [Sat.mk_and b; step2])) in *)
                        (nondet @ nondet_post @ nondets, Sat.mk_and [Sat.mk_and b; step2])
                    ) possible_a_post
              ) outgoing_edges) in
              let (nondets, smt) = List.fold_left (fun (nondets, smt_transitions) (nondet, smt_transition) -> (nondet @ nondets, Sat.mk_or [smt_transition; smt_transitions])) ([], Sat.mk_bool false) smt_transitions in
              (nondets, smt)
            else
              let outgoing_edges = get_outgoing_edges tab node in
              let smt_transitions = List.mapi (fun i edge ->
                  match edge with
                  | D _ -> failwith "Illegal tableau"
                  | T (_, succ, (_, _, _, b, a, b_post, a_post, _)) ->
                    let prefix = Printf.sprintf "pre_%d_%s" i path_prefix in
                    let path_prefix = Printf.sprintf "%d_%s" i path_prefix in

                    (* this is wrong, but subst is not needed for why_false anyway *)
                    let next_subst = subst in

                    let (nondets, ann_next_bounded) = build_bounded_counterexample_smt succ next_subst length path_prefix in
                    
                    let (nondet_post, step1) = gen_assignments_smt_no_quantification ann_next_bounded a_post "" in
                    let step1 = Sat.mk_and [Sat.mk_and b_post; step1] in
                    let (nondet, step2) = gen_assignments_smt_no_quantification step1 a prefix in
                    (nondet @ nondet_post @ nondets, Sat.mk_and [Sat.mk_and b; step2])
              ) outgoing_edges in
              let (nondets, smt) = List.fold_left (fun (nondets, smt_transitions) (nondet, smt_transition) -> (nondet @ nondets, Sat.mk_or [smt_transition; smt_transitions])) ([], Sat.mk_bool false) smt_transitions in
              
              (* unknowns are existentially quantified => can handle them as nondets *)
              let unknowns = get_unknowns_from_edges outgoing_edges in
              let prefix = Printf.sprintf "unknown_%s" path_prefix in
              let (new_nondets, smt) = prefix_vars smt unknowns prefix in
              (new_nondets @ nondets, smt)
          | _ -> failwith "Illegal state"
      in
      let rec build_bounded_counterexample model length path_prefix counterexample node subst =
        (* let () = Printf.printf "Bounded check %s\n" (node_to_string node) in *)
        if length = 0 then (NOT_FOUND, counterexample)
        else
          let (_, (ctl, _)) = node in
          match ctl, positive with
          | Ctl.A Ctl.W _, false ->
            (match get_outgoing_dependencies tab node with
            | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
              let (res_phi2, counterexample) = find_failing_path counterexample succ_phi2 subst in
              let counterexample = add_edge_if_found_anything res_phi2 counterexample (D (node, succ_phi2, 1)) subst subst in
              if not (res_phi2 = FOUND) then
                (* not a valid counterexample, because phi2 has to be false *)
                (res_phi2, counterexample)
              else
                (* phi1 or next have to be false *)
                let (res_phi1, counterexample) = find_failing_path counterexample succ_phi1 subst in
                let counterexample = add_edge_if_found_anything res_phi1 counterexample (D (node, succ_phi1, 0)) subst subst in
                if res_phi1 = FOUND then
                  (FOUND, counterexample)
                else
                  (* next has to be false *)
                  let (res_next, counterexample) = build_bounded_counterexample model (length - 1) path_prefix counterexample succ_next subst in
                  let counterexample = add_edge_if_found_anything res_next counterexample (D (node, succ_next, 2)) subst subst in
                  (* res_next could also be NOT_FOUND -> took the wrong transition somewhere before *)
                  if res_next = NOT_FOUND then
                    (res_phi1, counterexample)
                  else
                    (res_next, counterexample)
            | _ -> failwith "Illegal tableau")
          | Ctl.E Ctl.U _, true ->
            (match get_outgoing_dependencies tab node with
            | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
              (* phi2 || (phi1 && next) *)
              let (res_phi2, counterexample) = find_failing_path counterexample succ_phi2 subst in
              let counterexample = add_edge_if_found_anything res_phi2 counterexample (D (node, succ_phi2, 1)) subst subst in
              if res_phi2 = FOUND then
                (res_phi2, counterexample)
              else
                let (res_phi1, counterexample) = find_failing_path counterexample succ_phi1 subst in
                let counterexample = add_edge_if_found_anything res_phi1 counterexample (D (node, succ_phi1, 0)) subst subst in
                (match res_phi1 with
                | NOT_FOUND -> (res_phi2, counterexample) (* maybe res_phi2 was SPURIOUS *)
                | SPURIOUS -> (SPURIOUS, counterexample)
                | FOUND ->
                  let (res_next, counterexample) = build_bounded_counterexample model (length - 1) path_prefix counterexample succ_next subst in
                  let counterexample = add_edge_if_found_anything res_next counterexample (D (node, succ_next, 2)) subst subst in
                  if res_next = NOT_FOUND then
                    (res_phi2, counterexample)
                  else
                    (res_next, counterexample)
                )
            | _ -> failwith "Illegal tableau")
          | Ctl.A Ctl.X _, false
          | Ctl.E Ctl.X _, true ->
            if why_true
              then 
                let set_nondets = (fun a i j ->
                    let prefix = Printf.sprintf "pre_%d_%d_%s" i j path_prefix in
                    let a_nondet = List.fold_left (fun a_nondet var ->
                        let prefixed_var = prefix ^ var in
                        Substitution.add_arg a_nondet var (List.assoc prefixed_var model)
                      ) Substitution.empty a.Kripke.nondet in
                    let a = { a with Kripke.nondet = []; regular = Substitution.compose a.regular a_nondet } in
                    a
                  )
                in
                let f_rec i j =
                  let path_prefix = Printf.sprintf "%d_%d_%s" i j path_prefix in
                  build_bounded_counterexample model length path_prefix
                in
                handle_ax_ex_why_true tab ann track_vars node subst counterexample true f_rec ~update_a:set_nondets
              else 
                let set_nondets = (fun a i ->
                    let prefix = Printf.sprintf "pre_%d_%s" i path_prefix in
                    let a_nondet = List.fold_left (fun a_nondet var ->
                        let prefixed_var = prefix ^ var in
                        Substitution.add_arg a_nondet var (List.assoc prefixed_var model)
                      ) Substitution.empty a.Kripke.nondet in
                    let a = { a with Kripke.nondet = []; regular = Substitution.compose a.regular a_nondet } in
                    a
                  )
                in
                let set_unknowns = (fun unknowns ->
                    let prefix = Printf.sprintf "unknowns_%s" path_prefix in
                    List.map (fun unknown ->
                        let prefixed_unknown = prefix ^ unknown in
                        (unknown, (List.assoc prefixed_unknown model))
                      ) unknowns
                  )
                in
                let f_rec i =
                  let path_prefix = Printf.sprintf "%d_%s" i path_prefix in
                  build_bounded_counterexample model length path_prefix
                in
                handle_ax_ex_why_false tab ann track_vars node subst counterexample true f_rec ~update_a:set_nondets ~inst_unknowns:set_unknowns
          | _ -> failwith "Illegal state"
      in
      let rec get_shortest_counterexample node subst length =
        if length > 20 then failwith "Didn't terminate" else
        let (nondets, smt) = build_bounded_counterexample_smt node subst length "" in
        let smt = Substitution.apply_arg_smt subst smt in
        let model = Sat.is_sat_model smt in
        match model with
        | None -> get_shortest_counterexample node subst (length + 1)
        | Some model ->
          (* let () = Printf.printf "%s\n" (Sat.to_string smt) in *)
          (* let () = Printf.printf "Found counterexample of length %d\n" length in *)
          let model = List.map (fun var ->
            (var, Arg_terms.(Int (Smt (
              List.assoc_opt var model
              |> Option.value ~default:(Sat.mk_int 0)))))
          ) nondets in
          (* let () = Printf.printf "%s\n" (String.concat ", " (List.map (fun (var, value) -> Printf.sprintf "%s->%s" var (Arg_terms.to_string value)) model)) in *)
          let (res, counterexample) = build_bounded_counterexample model length "" counterexample node subst in
          let () = if res = NOT_FOUND then failwith "sanity check failed" in
          (res, counterexample)
      in
      get_shortest_counterexample node subst 1
    and find_failing_path_au_ew counterexample node subst visited =
      let () = failwith "AU/EW is still under construction :))\n" in
      let (state, (ctl, _)) = node in
      match ctl with
      | Ctl.A Ctl.U _ ->
        let node_ms = Kripke.State.to_multiset state in
        let node_ms = Substitution.apply_ms subst node_ms in
        let node_ms = Multiset_rewrite_system.term_simplify node_ms in
        let counterexample_node = to_counterexample_node node subst in
        (match List.find_opt (fun (ms, original_node, orig_counterexample_node) -> node = original_node && Multiset_rewrite_system.term_is_subset node_ms ms) visited with
        | Some (_, _, orig_counterexample_node) ->
          (FOUND, Counterexample.add_edge counterexample (counterexample_node, orig_counterexample_node, Counterexample.C, None))
        | None ->
          let visited = (node_ms, node, counterexample_node)::visited in
          (match get_outgoing_dependencies tab node with
            | [D (_, succ_phi1, 0); D (_, succ_phi2, 1); D (_, succ_next, 2)] ->
              let (res_phi2, counterexample) = find_failing_path counterexample succ_phi2 subst in
              let counterexample = add_edge_if_found_anything res_phi2 counterexample (D (node, succ_phi2, 1)) subst subst in
              sanity_check_found_anything res_phi2;
              if res_phi2 = SPURIOUS then
                (* not a valid counterexample -> phi1 has to be false *)
                (SPURIOUS, counterexample)
              else
                (* phi1 or next have to be false *)
                let (res_phi1, counterexample) = find_failing_path counterexample succ_phi1 subst in
                let counterexample = add_edge_if_found_anything res_phi1 counterexample (D (node, succ_phi1, 0)) subst subst in
                if res_phi1 = FOUND then
                  (FOUND, counterexample)
                else
                  (* next has to be false *)
                  let (res_next, counterexample) = find_failing_path_au_ew counterexample succ_next subst visited in
                  let counterexample = add_edge_if_found_anything res_next counterexample (D (node, succ_next, 2)) subst subst in
                  sanity_check_found_anything res_next;
                  (res_next, counterexample)
            | _ -> failwith "Illegal tableau"))
      | Ctl.A Ctl.X _ ->
        let (found_valid, new_counterexample) = List.fold_left (fun (found_valid, counterexample) edge ->
            if found_valid then (found_valid, counterexample)
            else match edge with
              | D (_, succ, _) -> failwith "Strange tableau"
              | T (_, succ, (_, _, _, b, a, b_post, a_post, _)) ->
                let next_subst = Substitution.compose subst a.regular in
                let next_subst = Substitution.restrict next_subst (fun var -> Option.is_none (List.find_opt ((=) var) a.nondet)) in
                let next_subst = Substitution.compose next_subst a_post.regular in
                let next_subst = Substitution.restrict next_subst (fun var -> Option.is_none (List.find_opt ((=) var) a_post.nondet)) in

                let succ_ms = Kripke.State.to_multiset state in
                let succ_ms = Substitution.apply_ms next_subst succ_ms in
                let succ_ms = Multiset_rewrite_system.term_simplify succ_ms in

                let super_set_of_visited_constraint = Sat.mk_or (List.filter_map (fun (visited_ms, node, _) ->
                    if node = succ then Some (Multiset_rewrite_system.gen_term_subset_smt succ_ms visited_ms)
                    else None) visited) in

                let succ_ann = get_final (Hashtbl.find ann succ) in
                let succ_ann_post = Sat.mk_or [Sat.mk_not (Sat.mk_and b_post); gen_assignments_smt succ_ann a_post true] in
                let side_constraint = generate_star_constraint a_post.regular subst in
                let new_subst_opt = check_transition succ_ann_post b a subst ~side_constraint:side_constraint ~soft_constraint:(Some super_set_of_visited_constraint) in
                let (new_subst_opt, spurious) =
                  if new_subst_opt = None then
                    (* If it works without the side_constraint, we found a spurious path.
                      Still continue to get the exact spurious transition in the counterexample.
                      (we can set spurious to true here, because it is ignored for new_subst_opt = None anyway) *)
                    (check_transition succ_ann_post b a subst, true)
                  else (new_subst_opt, false)
                in
                Option.fold new_subst_opt ~none:(false, counterexample) ~some:(fun new_subst ->
                    let new_subst_opt = check_transition succ_ann b_post a_post new_subst in
                    (* if new_subst_opt is None, there is a mistake in the algorithm *)
                    let new_subst = Option.get new_subst_opt in
                    if spurious then
                      let counterexample = Counterexample.add_edge counterexample (to_counterexample_edge edge subst new_subst (Some Counterexample.REMOVES_NON_EXISTENT_FACT)) in
                      (false, counterexample)
                    else
                      let (res, counterexample) = find_failing_path_au_ew counterexample succ new_subst visited in
                      let counterexample = add_edge_if_found_anything res counterexample edge subst new_subst in
                      (res = FOUND, counterexample)
                  )
            ) (false, counterexample) (get_outgoing_edges tab node) in
          if found_valid then (FOUND, new_counterexample)
          else (SPURIOUS, new_counterexample)
      | _ -> failwith "Illegal state"
    in
    let initial_node = (initial_state, (ctl, [])) in
    let initial_subst = 
      { Substitution.arg_subst = []; 
        Substitution.ms_subst = 
          List.map (fun star_var -> (star_var, Multiset_rewrite_system.Const [])) 
            (Multiset_rewrite_system.term_get_ms_vars (Kripke.State.to_multiset initial_state)) } in
    let initial_counterexample_node = (to_counterexample_node initial_node initial_subst) in
    let counterexample = Counterexample.create initial_counterexample_node in
    Some (find_failing_path counterexample initial_node initial_subst)
end
