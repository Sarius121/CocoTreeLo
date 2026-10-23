open Logic

type annotation = FINAL of Sat.expr | TEMP of Sat.expr | NONE
(** type for node annotations*)
type 'a annotations = {
  tt: ('a, annotation) Hashtbl.t;
  ff: ('a, annotation) Hashtbl.t
}

module type AnnotationImpl = sig
  type state
  (** takes state, fact, positive *)
  val annotate_fact: state -> Multiset_rewrite_system.fact -> bool -> Sat.expr
  (** takes state, label, positive *)
  val annotate_label: state -> string -> bool -> Sat.expr
end

module Make (Tableau_product: Tableau_product.Tableau_product) (Impl: AnnotationImpl with type state = Tableau_product.Kripke.State.t) = struct

  type node = Tableau_product.node

  open Tableau_product

  (** state stuff *)

  (** graph for checking stability *)
  module Scc_traversal = Scc_traversal.Make (struct
    type t = node
    let compare = Repr.compare
    let hash (state, (_, _)) = Kripke.State.hash state
    let equal = Repr.equal
  end)

  (** Initializes the stability graph; can be optimized by giving the outgoing_map to Scc_traversal *)
  let init_verification_state (nodes, edges, _) =
    let edges_mapped = (List.map (fun edge -> 
        match edge with
        | D (a, b, _) -> (a, b)
        | T (a, b, _) -> (a, b)
      ) (EdgeSet.to_list edges)) in
    Scc_traversal.init (Scc_traversal.convert_graph ((NodeSet.to_list nodes), edges_mapped))

  (**
    Checks if the new annotation is stable, i.e. semantically equal to the old one.
    It updates the stability graph accordingly.
    If the annotation is stable, it returns the old annotation (because it might be syntactically smaller).
    If not, it returns [new_ann].
    FINAL annotations are considered stable. *)
  let update_stability_and_simplify ann verification_state node new_ann =
    let (is_stable, new_ann) =
      match Hashtbl.find_opt ann node with
      | Some TEMP old_ann -> (
        match new_ann with
        | TEMP new_ann ->
          if Sat.is_eq old_ann new_ann then (true, TEMP old_ann)
          else (false, TEMP (Sat.simplify new_ann))
        | FINAL new_ann ->
          (* checking against old is not necessary *)
          Printf.printf "TODO: checking against old is not necessary\n";
          if Sat.is_eq old_ann new_ann then (true, FINAL old_ann)
          else (true, FINAL (Sat.simplify new_ann))
        | NONE -> (false, new_ann))
      | Some NONE
      | None -> (* NONE cannot be stable *)
        (match new_ann with
        | TEMP new_ann -> (false, TEMP (Sat.simplify new_ann))
        | FINAL new_ann -> (true, FINAL (Sat.simplify new_ann))
        | NONE -> (false, NONE))
      | Some FINAL old_ann ->
        (true, FINAL old_ann)
        (* TODO: failwith "Illegal state: It shouldn't be possible to update final annotation." *)
    in
    (* let () = Printf.printf "Update stability: %s" (node_to_string node) in *)
    Scc_traversal.set_stability verification_state node is_stable;
    new_ann

  (** annotation stuff *)
  
  (** generate the annotation for a leaf *)
  let gen_leaf_annotation (node: node) positive =
    let (state, (ctl, _)) = node in
    let open Ctl in
    FINAL (match ctl with
    | L lbl -> Impl.annotate_label state lbl positive
    | NOTL lbl -> Impl.annotate_label state lbl (not positive)
    | FACT fact -> Impl.annotate_fact state fact positive
    | NOTFACT fact -> Impl.annotate_fact state fact (not positive)
    | B term -> term |> fun ann -> if positive then ann else Sat.mk_not ann
    | A X _ -> Sat.mk_bool true |> fun ann -> if positive then ann else Sat.mk_not ann
    | E X _ -> Sat.mk_bool false |> fun ann -> if positive then ann else Sat.mk_not ann
    | _ -> failwith "The tableau is not valid: This cannot be a leaf")

  (** initialize the annotations *)
  let init_annotations tab =
    let (nodes, _, _) = tab in
    let cur_temp = [] in
    let new_final = [] in
    let ann = { tt = Hashtbl.create (NodeSet.cardinal nodes); ff = Hashtbl.create (NodeSet.cardinal nodes)} in
    let new_final = fold_leaves (fun node new_final ->
      Hashtbl.add ann.tt node (gen_leaf_annotation node true);
      Hashtbl.add ann.ff node (gen_leaf_annotation node false);
      node::new_final) tab new_final in
    let cur_temp = fold_minimal_nodes (fun node cur_temp ->
      Hashtbl.add ann.tt node (TEMP (Sat.mk_bool false));
      (match node with
        | (_, (Ctl.A _, _)) -> Hashtbl.add ann.ff node (TEMP (Sat.mk_bool true))
        | (_, (Ctl.E _, _)) -> Hashtbl.add ann.ff node (TEMP (Sat.mk_bool true))
        | _ -> failwith "Illegal state"
      ); (* TODO ??? *)
      node::cur_temp) tab cur_temp in
    let cur_temp = fold_maximal_nodes (fun node cur_temp ->
      Hashtbl.add ann.tt node (TEMP (Sat.mk_bool true));
      Hashtbl.add ann.ff node (TEMP (Sat.mk_bool false));
      node::cur_temp) tab cur_temp in
    (ann, cur_temp, new_final)

  let annotate_if_not_none_and_trans f f_trans ann edges =
    let () = Utils.Monitoring.start_event "annotate_if_not_none_and_trans" in
    let (all_ok, all_final, mapped) = List.fold_left (fun (all_ok, all_final, mapped) edge ->
        match edge with 
        | T (_, succ, transition) -> (
          match Hashtbl.find_opt ann succ with
          | Some (FINAL succ_ann) ->
            let res = f_trans succ_ann transition in
            (true, all_final, res::mapped)
          | Some (TEMP succ_ann) ->
            let res = f_trans succ_ann transition in
            (true, false, res::mapped)
          | _ -> (false, all_final, mapped)
        )
        | _ -> (false, all_final, mapped)
      ) (true, true, []) edges in
    (if all_ok then
      if all_final then
        let () = Utils.Monitoring.start_event "f_end" in
        FINAL (f mapped)
        |> fun x -> Utils.Monitoring.stop_event "f_end"; x
      else
        let () = Utils.Monitoring.start_event "f_end" in
        TEMP (f mapped)
        |> fun x -> Utils.Monitoring.stop_event "f_end"; x
    else NONE)
    |> fun x -> Utils.Monitoring.stop_event "annotate_if_not_none_and_trans"; x

  (** only annotate if last child is not-none at the others are final *)
  let annotate_if_not_none_and_dep default_ann f ann edges =
    let rec map_if_not_none_and_dep edges mapped =
      match edges with
      | edge::edges -> (match edge with
        | D (_, succ, i) -> (match Hashtbl.find_opt ann succ with
          | Some (FINAL succ_ann) -> map_if_not_none_and_dep edges ((i, succ_ann, true)::mapped)
          | Some (TEMP succ_ann) -> map_if_not_none_and_dep edges ((i, succ_ann, false)::mapped)
          | _ -> (false, mapped)
        )
        | _ -> (false, mapped)
      )
      | [] -> (true, mapped)
    in
    let (all_ok, mapped) = map_if_not_none_and_dep edges [] in
    if all_ok then
      let mapped = List.sort (fun (i1,_,_) (i2,_,_) -> i1 - i2) mapped in
      f mapped
    else default_ann

  let annotate_if_final_and_dep f ann edges =
    let rec map_if_final_and_dep edges mapped =
      match edges with
      | edge::edges -> (match edge with 
        | D (_, succ, i) -> (match Hashtbl.find_opt ann succ with
          | Some (FINAL succ_ann) -> map_if_final_and_dep edges ((i, succ_ann)::mapped)
          | _ -> (false, mapped)
        )
        | _ -> (false, mapped)
      )
      | [] -> (true, mapped)
    in
    let (all_final, mapped) = map_if_final_and_dep edges [] in
    if all_final then
      let mapped = List.sort (fun (i1,_) (i2,_) -> i1 - i2) mapped in
      if all_final then FINAL (f mapped)
      else TEMP (f mapped)
    else NONE

  (** Generates the formula for the assignment *)
  let gen_assignments_smt next_ann assignments universal =
    (* let ann_with_unknowns = Sat.mk_quantifier_multi true assignments.Kripke.unknowns next_ann in *)
    let quantified_ann = Sat.mk_quantifier_multi universal assignments.Kripke.nondet next_ann in
    Substitution.apply_arg_smt assignments.regular quantified_ann

  
  let get_somewhere_else_apps smt = Sat.get_apps_with_prefix "SomewhereElse_" smt

  (* SomewhereElse_i(nondet) is an unknown that depends on the step's nondeterministic values. Like every
     unknown it is universally quantified, and since it is Boolean, forall s. phi is phi[s:=true] /\ phi[s:=false]. *)
  let quantify_somewhere_else apps smt =
    let names = List.sort_uniq compare (List.map fst apps) in
    List.fold_left (fun smt name ->
        let apps = List.fold_left (fun acc (name', app) ->
            if name' = name && not (List.exists (Z3.Expr.equal app) acc) 
              then app::acc 
              else acc
          ) [] apps in
        (* TODO is this really better than using quantifiers?? *)
        Sat.simplify (Sat.mk_and [Sat.subst_apps smt apps true; Sat.subst_apps smt apps false])
      ) smt names

  (** Updates the annotation of a node *)
  let gen_node_annotation tab var_dependencies ann stability_graph node positive =
    let succ = get_outgoing_edges tab node in
    let (state, (ctl, vars)) = node in
    let open Ctl in
    match ctl, positive with
    | AND (ctl1, ctl2), true
    | OR (ctl1, ctl2), false ->
      annotate_if_final_and_dep (fun succ_ann ->
        match succ_ann with
        | [(_, succ1); (_, succ2)] -> Sat.mk_and [succ1; succ2]
        | _ -> failwith "The tableau is not valid: AND needs exactly two successors"
      ) ann succ
    | OR (ctl1, ctl2), true
    | AND (ctl1, ctl2), false ->
      annotate_if_final_and_dep (fun succ_ann ->
        match succ_ann with
        | [(_, succ1); (_, succ2)] -> Sat.mk_or [succ1; succ2]
        | _ -> failwith "The tableau is not valid: OR needs exactly two successors"
      ) ann succ
    | FORALL (leading, x, ctl), true
    | EXISTS (leading, x, ctl), false ->
      annotate_if_final_and_dep (fun succ_ann ->
        match succ_ann with
        | [(_, succ1)] ->
          let dependencies_quantified =
            if leading then succ1
            else
              let dependent_vars = Option.value ~default:[] (Hashtbl.find_opt var_dependencies x) in
              Sat.mk_forall_multi dependent_vars succ1
          in
          Sat.mk_forall x dependencies_quantified
        | _ -> failwith "The tableau is not valid: FORALL needs exactly one successor"
      ) ann succ
    | EXISTS (leading, x, ctl), true
    | FORALL (leading, x, ctl), false ->
      annotate_if_final_and_dep (fun succ_ann ->
        match succ_ann with
        | [(_, succ1)] ->
          let dependencies_quantified =
            if leading then succ1
            else
              let dependent_vars = Option.value ~default:[] (Hashtbl.find_opt var_dependencies x) in
              Sat.mk_forall_multi dependent_vars succ1
          in
          Sat.mk_exists x dependencies_quantified
        | _ -> failwith "The tableau is not valid: EXISTS needs exactly one successor"
      ) ann succ
    | A (X ctl), true
    | E (X ctl), false ->
      let new_ann = 
        annotate_if_not_none_and_trans
          (fun succ_anns_with_unknowns ->
            let (succ_anns, unknowns) = List.fold_left (fun (succ_anns, unknowns) (succ_ann, new_unknowns) ->
                (succ_ann::succ_anns, Utils.Str_utils.StringSet.add_seq (List.to_seq new_unknowns) unknowns)
              ) ([], Utils.Str_utils.StringSet.empty) succ_anns_with_unknowns in
            let unknowns = Utils.Str_utils.StringSet.to_list unknowns in
            (* let () = Printf.printf "unknowns: %d\n" (List.length unknowns) in *)
            Sat.mk_quantifier_multi true unknowns (Sat.mk_and succ_anns))
          (fun succ_ann (_, _, _, condition, assignments, condition_post, assignments_post, _) ->
            let unknowns = assignments.unknowns in
            let step1 = Sat.mk_or [Sat.mk_not (Sat.mk_and condition_post); gen_assignments_smt succ_ann assignments_post true] in
            (* every quantifier of this row is universal, so the unknown functions can be quantified at the node
               as constants, like the other unknowns *)
            let (names, apps) = List.split (get_somewhere_else_apps step1) in
            let step1 = Sat.replace_apps_by_vars step1 apps names in
            let unknowns = (List.sort_uniq compare names) @ unknowns in
            (Sat.mk_or [Sat.mk_not (Sat.mk_and condition); gen_assignments_smt step1 assignments true], unknowns)
          )
          ann succ in
      new_ann
    | E (X ctl), true
    | A (X ctl), false ->
      (* Only MUST edges count. SomewhereElse_i(nondet) is an unknown function of the step's values, so the
         node's "forall unknowns" has to enclose all targets of the step, and
         forall f. exists x. phi(x, f(x))  is  exists x. forall s. phi(x, s)  (Skolem normal form). *)
      let new_ann =
        annotate_if_not_none_and_trans
          (fun succ_anns_with_unknowns ->
            let succ_anns_with_unknowns = List.filter_map Fun.id succ_anns_with_unknowns in

            (* get unique unknowns list *)
            let unknowns = List.fold_left (fun unknowns (_, _, _, _, new_unknowns) ->
                Utils.Str_utils.StringSet.add_seq (List.to_seq new_unknowns) unknowns
              ) Utils.Str_utils.StringSet.empty succ_anns_with_unknowns
              |> Utils.Str_utils.StringSet.to_list in

            let (singles, groups) = List.fold_left (fun (singles, groups) (apps, condition, assignments, step1, _) ->
                if apps = [] then
                  (* no SomewhereElse -> can process transition as usual *)
                  (Sat.mk_and [Sat.mk_and condition; gen_assignments_smt step1 assignments false]::singles, groups)
                else
                  let names = List.sort_uniq compare (List.map fst apps) in

                  match List.assoc_opt names groups with
                  | Some (condition', assignments', apps', steps) ->
                    (* sanity check that the assignments and conditions are equal *)
                    let () = if condition <> condition' || assignments <> assignments' 
                      then failwith "Illegal state: edges using the same SomewhereElse variable do not have the same first condition and assignments" 
                    in
                    (singles, (names, (condition', assignments', apps @ apps', step1::steps))::List.remove_assoc names groups)
                  | None -> 
                    (* no other entry with these names yet *)
                    (singles, (names, (condition, assignments, apps, [step1]))::groups)
              ) ([], []) succ_anns_with_unknowns in

            let grouped = List.map (fun (_, (condition, assignments, apps, steps)) ->
                let somewhere_else_quantified = quantify_somewhere_else apps (Sat.mk_or steps) in
                Sat.mk_and [Sat.mk_and condition; gen_assignments_smt somewhere_else_quantified assignments false]
              ) groups in
            Sat.mk_quantifier_multi true unknowns (Sat.mk_or (singles @ grouped)))
          (fun succ_ann (_, _, transition_type, condition, assignments, condition_post, assignments_post, _) ->
            if transition_type = Kripke.ONLY_MAY then None
            else
              let step1 = Sat.mk_and [(Sat.mk_and condition_post); gen_assignments_smt succ_ann assignments_post false] in
              Some (get_somewhere_else_apps step1, condition, assignments, step1, assignments.unknowns))
        ann succ in
      new_ann
    | A (U _), true
    | E (U _), true
    | A (W _), true
    | E (W _), true ->
      let old_ann = match Hashtbl.find ann node with | TEMP old_ann -> old_ann | _ -> failwith "U/W should be TEMP" in
      let new_ann = annotate_if_not_none_and_dep (TEMP old_ann)
        (fun succ_ann ->
          match List.sort Repr.compare succ_ann with
          (* first two childs should be final *)
          | [(0, phi1, true); (1, phi2, true); (2, next, _)] ->
            let new_ann = TEMP (Sat.mk_or [phi2; (Sat.mk_and [phi1; next])]) in (* TODO I think we don't need to update with old_ann *)
            new_ann
          | [(0, phi1, _); (1, phi2, _); (2, next, _)] -> TEMP old_ann
          | _ -> failwith "The tableau is not valid: U/W has not the correct successors")
        ann succ in
      new_ann
    | A (U _), false
    | E (U _), false
    | A (W _), false
    | E (W _), false ->
      let () = if node_to_string node = "[P*, Q*] where  : E(P(x) U E(Q(x) U R(x))) [x]" then
              Printf.printf "found it\n"
              else ()
            in
      let old_ann = match Hashtbl.find ann node with | TEMP old_ann -> old_ann | _ -> failwith "U/W should be TEMP" in
      let new_ann = annotate_if_not_none_and_dep (TEMP old_ann)
        (fun succ_ann ->
          match List.sort Repr.compare succ_ann with
          (* first two childs should be final *)
          | [(0, phi1, true); (1, phi2, true); (2, next, _)] ->
            let () = if node_to_string node = "[P*, Q*] where  : E(P(x) U E(Q(x) U R(x))) [x]" then
              Printf.printf "Update: %s -> %s\n" (Sat.to_string old_ann) (Sat.to_string (Sat.mk_and [phi2; (Sat.mk_or [phi1; next])]))
              else ()
            in
            let new_ann = TEMP (Sat.mk_and [phi2; (Sat.mk_or [phi1; next])]) in (* TODO I think we don't need to update with old_ann *)
            new_ann
          | [(0, phi1, _); (1, phi2, _); (2, next, _)] ->
            let () = if node_to_string node = "[P*, Q*] where  : E(P(x) U E(Q(x) U R(x))) [x]" then
              Printf.printf "Children not final yet\n"
              else ()
            in
            TEMP old_ann
          | _ -> failwith "The tableau is not valid: U/W has not the correct successors")
        ann succ in
      new_ann
    | _ -> (* leaf nodes *) failwith "Leaf nodes need no update, they are final from the beginning." (* or this: Hashtbl.find ann node *)

  (**
    Updates the annotations of all nodes in nodes_to_update.
    It first generates all new annotations and then sets them.
  *)
  let update_annotations tab var_dependencies ann verification_state nodes_to_update positive =
    let (pending_ann, cur_temp, new_final) = List.fold_left (fun (pending_ann, cur_temp, new_final) node ->
      (* Printf.printf "Update %s\n" (node_to_string node); *)
      match Hashtbl.find_opt ann node with
      | Some FINAL s -> ((node, FINAL s)::pending_ann, cur_temp, new_final) (* no need to update if already final, nodes_to_update is an over-approximation of updatable nodes *)
      | _ ->
        (match gen_node_annotation tab var_dependencies ann verification_state node positive with
        | FINAL s -> (
          (*Printf.printf "%s -> FINAL %s\n" (node_to_string node) s;*)
          ((node, FINAL s)::pending_ann, cur_temp, node::new_final))
        | NONE ->
          (* Printf.printf "%s -> NONE\n" (node_to_string node);  *)
          (* TODO I guess this case doesn't happen? *)
          (pending_ann, cur_temp, new_final)
        | s (* TEMP *) -> (
          (* Printf.printf "%s -> TEMP %s\n" (node_to_string node) s; *)
          ((node, s)::pending_ann, node::cur_temp, new_final))
        )
    ) ([], [], []) nodes_to_update in
    (* TODO I guess we can use add instead of replace, because we never remove. Does that have any advantages? *)
    List.fold_left (fun () (node, node_ann) ->
        let node_ann = update_stability_and_simplify ann verification_state node node_ann in
        Hashtbl.replace ann node node_ann
      ) () pending_ann;
    verification_state

  (** main part *)

  (** Type for the annotation process status *)
  type annotation_status = DONE | CANCELLED

  (**
    Annotates the product structure for maximally [max_rounds] rounds.
    [f_step] is called after every round.
  *)
  let annotate_tab tab var_dependencies max_rounds f_step =
    let verification_state_tt = init_verification_state tab in
    let verification_state_ff = init_verification_state tab in
    let scc_count = Array.length verification_state_tt.components in
    let (ann, cur_temp, new_final) = init_annotations tab in
    let () = f_step ann (verification_state_tt, verification_state_ff) (0, 0) scc_count in
    let rec annotate_tab' (max_rounds_tt, max_rounds_ff) (verification_state_tt, verification_state_ff) =
      if Scc_traversal.is_done verification_state_tt
        && Scc_traversal.is_done verification_state_ff then DONE
      else if max_rounds_tt = 0 || max_rounds_ff = 0 then CANCELLED
      else
        let do_one_annotation ann verification_state positive =
          let nodes_to_update = Scc_traversal.get_cur_scc_nodes verification_state in
          (* let (_, (ctl, _)) = List.hd nodes_to_update in
          let () = Printf.printf "%d: %s\n" (List.length nodes_to_update) (Ctl.to_string ctl); flush stdout in *)
          (* let () = NodeSet.fold (fun node () -> Printf.printf "Update %s\n" (node_to_string node)) nodes_to_update () in *)
          let verification_state = update_annotations tab var_dependencies ann verification_state nodes_to_update positive in
          (* all finals are now stable, because they didn't change anymore *)
          Scc_traversal.check_if_scc_done verification_state (fun node ->
              let final_ann = match Hashtbl.find ann node with
                | TEMP node_ann -> FINAL node_ann
                | node_ann -> node_ann
              in
              Hashtbl.replace ann node final_ann
            )
        in
        let (scc_done_tt, verification_state_tt) =
          if Scc_traversal.is_done verification_state_tt then (true, verification_state_tt)
          else do_one_annotation ann.tt verification_state_tt true
        in
        let (scc_done_ff, verification_state_ff) =
          if Scc_traversal.is_done verification_state_ff then (true, verification_state_ff)
          else do_one_annotation ann.ff verification_state_ff false
        in
        let max_rounds_tt = if scc_done_tt then max_rounds else max_rounds_tt - 1 in
        let max_rounds_ff = if scc_done_tt then max_rounds else max_rounds_ff - 1 in
        let () = f_step ann (verification_state_tt, verification_state_ff)
                            (verification_state_tt.Scc_traversal.cur_scc, verification_state_ff.Scc_traversal.cur_scc) scc_count in
        annotate_tab' (max_rounds_tt, max_rounds_ff) (verification_state_tt, verification_state_ff)
    in
    (annotate_tab' (max_rounds, max_rounds) (verification_state_tt, verification_state_ff), ann)

  (** Check whether the property is verified given that the annotation is correct. *)
  let check_if_verified ann kripke ctl track_vars =
    let track_vars_false_subst = { Substitution.ms_subst = []; arg_subst = List.map (fun track_var -> (Encoding.Maude_narrowing_combi.track_var_to_string track_var, Arg_terms.Bool (Smt (Sat.mk_bool false)))) track_vars } in

    let (verified, falsified) = List.fold_left (fun (verified, falsified) state ->
      if falsified then (verified, falsified)
      else
        match Hashtbl.find_opt ann.tt (state, (ctl, [])), Hashtbl.find_opt ann.ff (state, (ctl, [])) with
        | Some FINAL ann_tt, Some FINAL ann_ff ->
          (* Make sure that all track_vars are false in the beginning. This is not automatically done, if we start with a non-empty state. *)
          let ann_tt = Substitution.apply_arg_smt track_vars_false_subst ann_tt in
          let ann_ff = Substitution.apply_arg_smt track_vars_false_subst ann_ff in
          (match Sat.is_true_opt ann_tt, Sat.is_true_opt ann_ff with
          | Some true, Some true -> failwith "Illegal verification result"
          | Some true, _ -> (true && verified, false)
          | _, Some true -> (false, true)
          | _ -> (false, false))
        | _ -> (false, false)
      ) (true, false) (Kripke.get_initial_states kripke) in
    if verified then Some true
    else if falsified then Some false
    else None

  (** drawing stuff *)

  let print_smt_status smt =
    (* "Unknown" *)
    match Sat.is_true_opt smt with
    | Some true -> "True"
    | Some false -> "False"
    | None -> "Unknown"

  (** draw the product structure by generating a .dot string *)
  let draw_with_annotations ((nodes, edges, _): tableau_product) ann (verification_state_tt, verification_state_ff) =
    let () = Utils.Monitoring.start_event "draw_with_annotations" in
    let sat_to_string smt =
      let s = Sat.to_string smt in
      let s = if String.length s > 50 then String.sub s 0 25 ^ "..."
        else s in
      Utils.Str_utils.replace s "\n" "\\n"
    in
    let nodes_s = String.concat "\n"
      (List.map (fun node ->
        let (color_tt, ann_tt) = (match Option.value ~default:NONE (Hashtbl.find_opt ann.tt node) with
          | NONE -> ("black","")
          | FINAL ann_s -> ("green", ((print_smt_status ann_s) ^ " :: " ^ sat_to_string ann_s))
          | TEMP ann_s -> ("blue", (sat_to_string ann_s))
        ) in
        let (color_ff, ann_ff) = (match Option.value ~default:NONE (Hashtbl.find_opt ann.ff node) with
          | NONE -> ("black","")
          | FINAL ann_s -> ("green", ((print_smt_status ann_s) ^ " :: " ^ sat_to_string ann_s))
          | TEMP ann_s -> ("blue", (sat_to_string ann_s))
        ) in
        let color = match color_tt, color_ff with
          | color_tt, color_ff when color_tt = color_ff -> color_tt
          | "green", "black"
          | "black", "green" -> "darkgreen"
          | "blue", "black"
          | "black", "blue" -> "darkblue"
          | "green", "blue" -> "yellow"
          | "blue", "green" -> "yellow"
          | _ -> "red"
        in
        if Scc_traversal.is_stable verification_state_tt node && Scc_traversal.is_stable verification_state_ff node
          then Printf.sprintf "\"%s\" [color=%s,xlabel=\"tt: %s\\nff: %s\"]" (node_to_string node) color ann_tt ann_ff
        else Printf.sprintf "\"%s\" [color=%s,xlabel=\"tt: %s\\nff: %s\",style=\"dashed\"]" (node_to_string node) color ann_tt ann_ff
      ) (NodeSet.to_list nodes)) in
    let edges_s = String.concat "\n"
      (List.map (fun edge ->
        match edge with
        | D (node1, node2, _) ->
          Printf.sprintf "\"%s\" -> \"%s\" [style=\"dotted\"]" (node_to_string node1) (node_to_string node2)
        | T (node1, node2, transition) ->
          (match transition with
          | _, _, Kripke.MAY_AND_MUST, _, _, _, _, _ ->
            Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\"]" (node_to_string node1) (node_to_string node2) (Kripke.transition_labels_to_string transition)
          | _, _, Kripke.ONLY_MAY, _, _, _, _, _ ->
            Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\", style=\"dashed\"]" (node_to_string node1) (node_to_string node2) (Kripke.transition_labels_to_string transition))
      ) (EdgeSet.to_list edges)) in
    String.concat "\n" ["digraph g {"; nodes_s; edges_s; "}"]
    |> fun s -> Utils.Monitoring.stop_event "draw_with_annotations"; s

  (** draw the product structure that is reachable by node by generating a .dot string *)
  let draw_reachable_with_annotations (tab: tableau_product) ann stability_graph node =
    let sat_to_string smt =
      let s = Sat.to_string smt in
      if String.length s > 50 then String.sub s 0 50 ^ "..."
      else s
    in
    let rec collect_reachable new_nodes state =
      if new_nodes = [] then state else
      let (new_nodes, state) = List.fold_left (fun (new_nodes, state) new_node -> 
          let succs = get_outgoing_edges tab new_node in
          List.fold_left (fun (new_nodes, (nodes, edges)) succ -> 
              match succ with
              | D (_, b, _)
              | T (_, b, _) -> if NodeSet.find_opt b nodes = None then (b::new_nodes, (NodeSet.add b nodes, succ::edges)) else (new_nodes, (nodes, succ::edges))
            ) (new_nodes, state) succs
        ) ([], state) new_nodes in
      collect_reachable new_nodes state
    in
    let (nodes, edges) = collect_reachable [node] (NodeSet.add node NodeSet.empty, []) in
    let nodes_s = String.concat "\n"
      (List.map (fun node ->
        let ann_node = (match Hashtbl.find_opt ann node with
          | Some ann_node -> ann_node
          | None -> NONE) in
        let (color, ann_s) = (match ann_node with
          | NONE -> ("black","")
          | FINAL ann_s -> ("green", ((print_smt_status ann_s) ^ " :: " ^ sat_to_string ann_s))
          | TEMP ann_s -> ("blue", (sat_to_string ann_s))
        ) in
        if Scc_traversal.is_stable stability_graph node
          then Printf.sprintf "\"%s\" [color=%s,xlabel=\"%s\"]" (node_to_string node) color ann_s
        else Printf.sprintf "\"%s\" [color=%s,xlabel=\"%s\",style=\"dashed\"]" (node_to_string node) color ann_s
      ) (NodeSet.to_list nodes)) in
    let edges_s = String.concat "\n"
      (List.map (fun edge ->
        match edge with
        | D (node1, node2, _) ->
          Printf.sprintf "\"%s\" -> \"%s\" [style=\"dotted\"]" (node_to_string node1) (node_to_string node2)
        | T (node1, node2, transition) ->
          Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\"]" (node_to_string node1) (node_to_string node2) (Kripke.transition_labels_to_string transition)
      ) edges) in
    String.concat "\n" ["digraph g {"; nodes_s; edges_s; "}"]

  (** only used for tests *)
  let print_annotation ann =
    match ann with
    | NONE -> "NONE"
    | FINAL x -> "FINAL " ^ (Sat.to_string x)
    | TEMP x -> "TEMP" ^ (Sat.to_string x)

end

(* Tests *)

module LabeledImpl: (AnnotationImpl with type state = Kripke.LabeledKripke.State.t) = struct
  type state = Kripke.LabeledState.t
  let annotate_fact _ _ _ = failwith "The labeled Kripke structure can't be used for facts."
  let annotate_label (_, labels) lbl pos =
    if pos then
      if List.find_opt (fun label -> lbl = label) labels = None then Sat.mk_bool false else Sat.mk_bool true
    else
      if List.find_opt (fun label -> lbl = label) labels = None then Sat.mk_bool true else Sat.mk_bool false
end

let%expect_test "test_annotate_if_final_and_dep" =
  let open Ctl in
  let module LabeledKripkeTab = Tableau_product.Make(Kripke.LabeledKripke) in
  let module Annotator = Make(LabeledKripkeTab)(LabeledImpl) in
  let open Annotator in
  let ann = Hashtbl.create 10 in
  let stateA = ("A", []) in
  let stateB = ("B", ["P"]) in
  let nodeA = (stateA, (A (X (L "P")), [])) in
  let nodeB = (stateB, ((L "P"), [])) in
  let () = Hashtbl.add ann nodeB (TEMP (Sat.mk_bool false)) in
  let edges = [LabeledKripkeTab.T (nodeA, nodeB, (stateA, stateB, Kripke.LabeledKripke.ONLY_MAY, [Sat.mk_bool true], Kripke.LabeledKripke.{ nondet = ["x"]; regular = Substitution.empty; unknowns = []}, [Sat.mk_bool true], Kripke.LabeledKripke.{ nondet = []; regular = Substitution.empty; unknowns = []}, "rule1"))] in
  Printf.printf "%s" (print_annotation (annotate_if_final_and_dep (fun l -> Sat.mk_int 0) ann edges));
  [%expect {| NONE |}]

module DummyFactImpl: (AnnotationImpl with type state = Kripke.FactState.t) = struct
  type state = Kripke.FactState.t
  let annotate_label _ _ _ = failwith "The fact Kripke structure can't be used for labels."
  let annotate_fact (_, ms) fact positive =
    if positive then Multiset_rewrite_system.gen_fact_in_ms ms fact
    else Sat.mk_not (Multiset_rewrite_system.gen_fact_in_ms ms fact)
  let state_to_multiset _ = failwith "The labeled Kripke structure can't be used for facts."
end

let%expect_test "test_fact_annotation" =
  let module FactKripkeTab = Tableau_product.Make(Kripke.FactKripke) in
  let module Annotator = Make(FactKripkeTab)(DummyFactImpl) in
  let open Annotator in
  let state = ("", [("P", [Arg_terms.(Int (Var "v0"))])]) in
  let node = (state, (Ctl.FACT ("P", [Arg_terms.(Int (Var "x"))]), [])) in
  Printf.printf "%s\n" (print_annotation (gen_leaf_annotation node true));
  [%expect {| FINAL (or (and (= x v0))) |}];
  let state = ("", [("P", [Arg_terms.(Int (Var "v0"))]); ("Q", [Arg_terms.(Int (Var "v1"))]); ("QM", [])]) in
  let node = (state, (Ctl.FACT ("P", [Arg_terms.(Int (Var "x"))]), [])) in
  Printf.printf "%s\n" (print_annotation (gen_leaf_annotation node true));
  [%expect {| FINAL (or (and (= x v0)) false false) |}]
