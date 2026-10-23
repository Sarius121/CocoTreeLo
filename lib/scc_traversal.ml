module Make(Node: Graph.Sig.COMPARABLE) = struct
  type node = Node.t

  module OutgoingMap = Utils.Outgoing_map.Make(Node)

  type graph = {nodes: Node.t list; edges: (Node.t * Node.t) list; outgoing_map: Node.t OutgoingMap.t}

  let convert_graph (nodes, edges) =
    let outgoing_map = OutgoingMap.init Fun.id edges in
    { nodes; edges; outgoing_map }

  module SCC = Graph.Components.Make(struct
      type t = graph
      module V = Node
      let iter_vertex f g = List.iter f g.nodes
      let iter_succ f g v = List.iter f (OutgoingMap.get v g.outgoing_map)
    end)

  type stability_graph = {
    components: node list array;
    node_to_comp: node -> int;
    cur_scc: int;
    stable_scc_nodes: (node, bool) Hashtbl.t
  }

  module EdgeSet = Set.Make(struct
    type t = int * int
    let compare = Repr.compare
  end)

  module IntSet = Set.Make(struct
    type t = int
    let compare = Repr.compare
  end)

  let init g: stability_graph =
    let components = SCC.scc_array g in
    let (_, node_to_comp) = SCC.scc g in
    let state = {
      components;
      node_to_comp;
      cur_scc = 0;
      stable_scc_nodes = Hashtbl.create 10
    } in
    state

  let is_done state = state.cur_scc >= Array.length state.components

  let get_cur_scc_nodes state =
    state.components.(state.cur_scc)
    
  (** Checks if the current SCC is done and updates state for the next SCC *)
  let check_if_scc_done state f =
    let scc_done = List.for_all (fun node -> 
        Option.value ~default:false (Hashtbl.find_opt state.stable_scc_nodes node)) state.components.(state.cur_scc) in
    (scc_done, if scc_done then
      (List.iter f state.components.(state.cur_scc);
      { state with cur_scc = state.cur_scc + 1; stable_scc_nodes = Hashtbl.create 10 })
    else state)

  let set_stability state node stability =
    (* sanity check *)
    let () = if state.node_to_comp node != state.cur_scc then failwith "You can only set the stability for nodes in the current SCC!" in
    Hashtbl.replace state.stable_scc_nodes node stability

  let is_stable state node =
    if state.node_to_comp node = state.cur_scc then
      Option.value ~default:false (Hashtbl.find_opt state.stable_scc_nodes node)
    else state.node_to_comp node < state.cur_scc

end

let%expect_test "test_complete" =
  let open Make (String) in
  let graph = convert_graph (
    ["A"; "B"; "C1"; "C2"; "C3"; "D"],
    [("A", "C1"); ("A", "C2"); ("C1", "C2"); ("C2", "C3"); ("C3", "C1"); ("C3", "D"); ("A", "B")]
  ) in
  let state = init graph in
  let () = Printf.printf "%s" (String.concat ", " state.components.(state.cur_scc)) in
  [%expect {|D|}];
  let () = set_stability state "D" true in
  let (_, state) = check_if_scc_done state (Printf.printf "%s,") in
  let () = Printf.printf " -> %d\n" state.cur_scc in
  [%expect {| D, -> 1|}];
  let () = set_stability state "C1" true in
  let (_, state) = check_if_scc_done state (Printf.printf "%s,") in
  let () = Printf.printf " -> %d\n" state.cur_scc in
  [%expect {| -> 1|}];
  let () = set_stability state "C2" true in
  let () = set_stability state "C3" true in
  let (_, state)= check_if_scc_done state (Printf.printf "%s,") in
  let () = Printf.printf " -> %d\n" state.cur_scc in
  [%expect {| C3,C2,C1, -> 2|}];
  ()