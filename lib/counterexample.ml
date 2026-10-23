open Logic

module Make (State: Kripke.State) = struct

  type node = State.t * Multiset_rewrite_system.term * Ctl.ctl * Substitution.t
  type transition_edge = node * node * string
  type dependency_edge = node * node
  type cycle_edge = node * node
  type spurious_reason = REMOVES_NON_EXISTENT_FACT | INHERITED | REMOVES_NON_EXISTENT_FACT_OR_RELEVANT_UNKNOWNS
                        | UNPROBLEMATIC_RELEVANT_MAY_EDGE
                        | RELEVANT_MAY_EDGE | RELEVANT_UNKNOWNS | NON_LEADING_QUANTIFIER
  type spurious_status = spurious_reason option
  type edge_type = T of string | D | C
  type edge = node * node * edge_type * spurious_status

  module NodeSet = Set.Make(struct
      type t = node
      let compare = Repr.compare
    end)
  module EdgeSet = Set.Make(struct
      type t = edge
      let compare = Repr.compare
    end)

  type t = NodeSet.t * EdgeSet.t * node

  let create initial_node = (NodeSet.add initial_node NodeSet.empty, EdgeSet.empty, initial_node)

  let add_edge (nodes, edges, initial_node) edge =
    let (nodeA, nodeB, _, _) = edge in
    (NodeSet.add nodeA (NodeSet.add nodeB nodes), EdgeSet.add edge edges, initial_node)

  (* for adding states that are not part of any edges *)
  let add_state (nodes, edges) node = (NodeSet.add node nodes, edges) 

  let node_to_string (state, _, ctl, substs) =
    let substs_s = Substitution.to_string substs in
    let node_s = Printf.sprintf "%s : %s %s" (State.to_string state) (Ctl.to_string ctl) substs_s in
    (* escape \, b/c it seems to be a special character in .dot files (double escape because of regex) *)
    Utils.Str_utils.replace node_s "\\" "\\\\\\\\"

  let path_node_to_string (_, ms, _, _) =
    let node_s = Printf.sprintf "%s" (Multiset_rewrite_system.term_to_string ms) in
    (* escape \, b/c it seems to be a special character in .dot files (double escape because of regex) *)
    Utils.Str_utils.replace node_s "\\" "\\\\\\\\"

  let spurious_status_to_string spurious_opt = match spurious_opt with
    | Some REMOVES_NON_EXISTENT_FACT -> "Removes non-existent fact"
    | Some REMOVES_NON_EXISTENT_FACT_OR_RELEVANT_UNKNOWNS -> "Removes non-existent fact or relevant unknowns"
    | Some RELEVANT_MAY_EDGE -> "Relevant may edge"
    | Some UNPROBLEMATIC_RELEVANT_MAY_EDGE -> "Relevant (but existing) may edge"
    | Some RELEVANT_UNKNOWNS -> "Relevant unknowns"
    | Some NON_LEADING_QUANTIFIER -> "Non-leading quantifier"
    | Some INHERITED -> ""
    | None -> ""

  let draw_generic (nodes, edges, _) node_to_string =
    let nodes_s = String.concat "\n"
      (List.map (fun node ->
        Printf.sprintf "\"%s\"" (node_to_string node)
      ) (NodeSet.to_list nodes)) in
    let edges_s = String.concat "\n"
      (List.map (fun edge ->
        let (node1, node2, edge_type, spurious) = edge in
        let (color, spurious_label) = match spurious with
          | Some UNPROBLEMATIC_RELEVANT_MAY_EDGE -> ("orange", spurious_status_to_string spurious)
          | Some _ -> ("red", spurious_status_to_string spurious)
          | None -> ("black", "")
        in
        let node1_s = node_to_string node1 in
        let node2_s = node_to_string node2 in
        match edge_type with
        | D ->
          Printf.sprintf "\"%s\" -> \"%s\" [style=\"dotted\", color=\"%s\", xlabel=\"%s\"]" node1_s node2_s color spurious_label
        | T rule ->
          Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\", color=\"%s\", xlabel=\"%s\"]" node1_s node2_s rule color spurious_label
        | C ->
          Printf.sprintf "\"%s\" -> \"%s\" [style=\"dashed\", label=\"cycle\", color=\"%s\", xlabel=\"%s\"]" node1_s node2_s color spurious_label
      ) (EdgeSet.to_list edges)) in
    String.concat "\n" ["digraph g {"; nodes_s; edges_s; "}"]

  let draw counterexample = draw_generic counterexample node_to_string

  let draw_path counterexample = draw_generic counterexample path_node_to_string

  let get_outgoing_edges (_, edges, _) node =
    EdgeSet.fold (fun edge succ ->
        let (s1, s2, _, _) = edge in
        if s1 = node then edge::succ else succ
      ) edges []

  let extract_kripke counterexample include_spurious =
    let rec to_path_node (state, ms, _, subst) =
      let ms = Substitution.apply_ms subst ms in
      let ms = Multiset_rewrite_system.term_simplify ms in
      (state, ms, Ctl.B (Sat.mk_var "dummy"), subst)
    in

    let rec skip_dependency_and_spurious_edges node =
      let edges = get_outgoing_edges counterexample node in
      let edges =
        if include_spurious then edges
        else List.filter (fun (_, _, _, spurious) -> spurious = None || spurious = Some UNPROBLEMATIC_RELEVANT_MAY_EDGE) edges
      in
      List.concat_map (fun edge ->
          match edge with
          | nodeA, nodeB, T rule, spurious -> [Some nodeB, (to_path_node nodeA, to_path_node nodeB, T rule, spurious)]
          | nodeA, nodeB, C, spurious -> [None, (to_path_node nodeA, to_path_node nodeB, C, spurious)]
          | _, succ, D, _ -> skip_dependency_and_spurious_edges succ
        ) edges
    in
    
    let rec extract_kripke' kripke node =
      let new_edges = skip_dependency_and_spurious_edges node in
      let (kripke, next_nodes) = List.fold_left (fun (kripke, next_nodes) (next_node, edge) -> (add_edge kripke edge, Option.fold next_node ~none:next_nodes ~some:(fun next_node -> next_node::next_nodes))) (kripke, []) new_edges in
      List.fold_left extract_kripke' kripke next_nodes
    in
    let (_, _, initial_node) = counterexample in
    extract_kripke' (create (to_path_node initial_node)) initial_node

  let get_edges_filtered (_, edges, _: t) reason =
    EdgeSet.fold (fun edge accu -> match edge with
        | (_, _, _, Some reason') when reason = reason' -> edge::accu
        | _ -> accu
      ) edges []
end