open Logic

module type Tableau_product = sig
  module Kripke: Kripke.Kripke
  type node = Kripke.state * (Ctl.ctl * string list)
  type transition_edge = node * node * Kripke.transition
  type dependency_edge = node * node * int
  type edge = T of transition_edge | D of dependency_edge

  module NodeSet: Set.S with type elt = node
  module EdgeSet: Set.S with type elt = edge
  module OutgoingMap: Utils.Outgoing_map.OutgoingMap

  type tableau_product = NodeSet.t * EdgeSet.t * edge OutgoingMap.t

  val empty : tableau_product
  val gen_product_structure : Kripke.kripke -> Ctl.ctl -> tableau_product
  val node_to_string : Kripke.state * (Ctl.ctl * string list) -> string
  val draw : tableau_product -> string
  val fold_leaves : (node -> 'a -> 'a) -> tableau_product -> 'a -> 'a
  val fold_minimal_nodes : (node -> 'a -> 'a) -> tableau_product -> 'a -> 'a
  val fold_maximal_nodes : (node -> 'a -> 'a) -> tableau_product -> 'a -> 'a
  val get_predecessors : tableau_product -> node -> node list
  val get_successors : tableau_product -> node -> node list
  val get_outgoing_edges : tableau_product -> node -> edge list

  val get_stats: tableau_product -> int * int
end

module Make (Kripke: Kripke.Kripke): Tableau_product with module Kripke = Kripke = struct

  module Kripke = Kripke

  open Kripke

  type node = state * (Ctl.ctl * Ctl.var list)
  type transition_edge = node * node * Kripke.transition
  type dependency_edge = node * node * int (* dependency edges are numbered, because the order matters sometimes*)
  type edge = T of transition_edge | D of dependency_edge

  module NodeSet = Set.Make(struct
      type t = node
      let compare = Repr.compare
    end)
  module EdgeSet = Set.Make(struct
      type t = edge
      let compare = Repr.compare
    end)
  module OutgoingMap = Utils.Outgoing_map.Make(struct
      type t = node
      let compare = Repr.compare
    end)

  (** product structure type *)
  type tableau_product = NodeSet.t * EdgeSet.t * edge OutgoingMap.t

  (** empty product structure *)
  let empty : tableau_product = (NodeSet.empty, EdgeSet.empty, OutgoingMap.empty)

  (** generate the product structure given a Kripke structure and a ctl formula *)
  let gen_product_structure (g: kripke) (ctl: Ctl.ctl) : tableau_product =
    let initial = get_initial_states g in
    let rec process_state (nodes, edges, outgoing_map) (state, ctl_node) =
      (* no need to process if the node already exists *)
      if NodeSet.find_opt (state, ctl_node) nodes != None then (nodes, edges, outgoing_map)
      else
        (* add node to tableau *)
        let nodes = NodeSet.add (state, ctl_node) nodes in
        (* add dependency edges *)
        let (new_nodes, new_edges, _) = 
          let sub_nodes = Ctl.sub_relation ctl_node in
          List.fold_left (fun (new_nodes, new_edges, i) sub_node -> ((state, sub_node)::new_nodes, (D ((state, ctl_node), (state, sub_node), i))::new_edges, i+1))
            ([], [], 0) sub_nodes 
        in
        (* add transition edges *)
        let (new_nodes, new_edges) = match Ctl.transition_relation ctl_node with
          | Some ctl_node2 ->
              Kripke.fold_transitions
                (fun (new_nodes, new_edges) transition -> 
                  let (_, new_state, _, _, _, _, _, _) = transition in
                  ((new_state, ctl_node2)::new_nodes, (T ((state, ctl_node), (new_state, ctl_node2), transition)::new_edges)))
                (new_nodes, new_edges) g state
          | None -> (new_nodes, new_edges)
        in
        (* add new edges to tableau *)
        let edges = List.fold_left (fun edges edge -> EdgeSet.add edge edges) edges new_edges in
        let outgoing_map = OutgoingMap.update_list (state, ctl_node) new_edges outgoing_map in
        (* process new nodes *)
        List.fold_left process_state (nodes, edges, outgoing_map) new_nodes
    in
    List.fold_left (fun tab state -> process_state tab (state, (ctl, []))) empty initial

  (** convert a node to a string*)
  let node_to_string (state, (ctl, vars)) =
    Printf.sprintf "%s : %s [%s]" (State.to_string state) (Ctl.to_string ctl) (String.concat "," vars)

  (** draw the product structure by generating a .dot string *)
  let draw ((nodes, edges, _): tableau_product) =
    let nodes_s = String.concat "\n"
      (List.map (fun node ->
        Printf.sprintf "\"%s\" []" (node_to_string node)
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

  (** fold over all leaf nodes *)
  let fold_leaves f (nodes, edges, _) accu =
    let leaves = EdgeSet.fold (fun edge leaf_nodes -> 
      match edge with
      | D (s1, _, _) -> NodeSet.remove s1 leaf_nodes
      | T (s1, _, _) -> NodeSet.remove s1 leaf_nodes
      ) edges nodes in
    NodeSet.fold f leaves accu

  (** fold over minimal nodes (i.e. U nodes) *)
  let fold_minimal_nodes f (nodes, edges, _) accu =
    NodeSet.fold (fun node accu ->
      match node with
      | (_, (A (U _), _))
      | (_, (E (U _), _)) -> f node accu
      | _ -> accu) nodes accu

  (** fold over maximal nodes (i.e. W nodes) *)
  let fold_maximal_nodes f (nodes, edges, _) accu =
    NodeSet.fold (fun node accu ->
      match node with
      | (_, (A (W _), _))
      | (_, (E (W _), _)) -> f node accu
      | _ -> accu) nodes accu

  (** get all predecessors of a node *)
  let get_predecessors (_, edges, _) node =
    EdgeSet.fold (fun edge pres -> 
      match edge with
      | D (s1, s2, _)
      | T (s1, s2, _) -> if s2 = node then s1::pres else pres
      ) edges []

  (** get all successors of a node *)
  let get_successors (_, edges, _) node =
    EdgeSet.fold (fun edge succs -> 
      match edge with
      | D (s1, s2, _)
      | T (s1, s2, _) -> if s1 = node then s2::succs else succs
      ) edges []

  (** get all outgoing edges of a node *)
  let get_outgoing_edges (_, _, outgoing_map) node =
    let () = Utils.Monitoring.start_event "get_outgoing_edges" in
    let outgoing = OutgoingMap.get node outgoing_map in 
    outgoing
    |> fun x -> Utils.Monitoring.stop_event "get_outgoing_edges"; x

  let get_stats (nodes, edges, _) =
    (NodeSet.cardinal nodes, EdgeSet.cardinal edges)
end