module Make(Node: Graph.Sig.COMPARABLE) = struct
  type node = Node.t
  type graph = {nodes: Node.t list; edges: (Node.t * Node.t) list}

  module SCC = Graph.Components.Make(struct
      type t = graph
      module V = Node
      let iter_vertex f g = List.iter f g.nodes
      let iter_succ f g v = List.iter (fun (a, b) -> if a = v then f b else ()) g.edges
    end)

  type stability_graph = {
    components: node list array;
    v_to_comp: node -> int;
    condensation_graph: (int * int) list;
    preds_rec: int list array;
    (* TODO next two could be arrays *)
    all_below_component_stable: (int, bool) Hashtbl.t;
    stable_components: (int, bool) Hashtbl.t;
    stable_nodes: (node, bool) Hashtbl.t
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
    let (n, v_to_comp) = SCC.scc g in
    let condensation_graph =
      List.fold_left (fun graph (a, b) -> 
          let compA = v_to_comp a in
          let compB = v_to_comp b in
          if compA = compB then
            graph
          else EdgeSet.add (v_to_comp a, v_to_comp b) graph
        ) EdgeSet.empty g.edges
      |> EdgeSet.to_list
    in
    let rec get_preds_rec comps accu =
      if comps = [] then accu
      else
        let (new_preds, preds) = List.fold_left (fun accu comp ->
          List.fold_left (fun (new_preds, preds) (a,b) ->
            if b = comp && IntSet.find_opt a preds = None then 
              (a::new_preds, IntSet.add a preds)
            else (new_preds, preds)) accu condensation_graph
          ) ([], accu) comps in
        get_preds_rec new_preds preds
    in
    (* could theoretically be improved with DP, but is only computed once -> probably not necessary *)
    let preds_rec = Array.init n (fun comp -> get_preds_rec [comp] (IntSet.add comp IntSet.empty) |> IntSet.to_list |> List.sort Repr.compare) in
    let stability_graph = {
      components = components;
      condensation_graph = condensation_graph;
      preds_rec = preds_rec;
      v_to_comp = v_to_comp;
      all_below_component_stable = Hashtbl.create n;
      stable_components = Hashtbl.create n;
      stable_nodes = Hashtbl.create (List.length g.nodes)
    } in
    stability_graph

  let are_all_below_stable stability_graph node =
    let comp = stability_graph.v_to_comp node in
    Option.value ~default:false (Hashtbl.find_opt stability_graph.all_below_component_stable comp)

  let set_stability stability_graph node stability =
    let () = Utils.Monitoring.start_event "set_stability" in
    let comp = stability_graph.v_to_comp node in
    let () = Hashtbl.replace stability_graph.stable_nodes node stability in
    let () =
      if not stability then
        Hashtbl.replace stability_graph.stable_components comp false
      else
        let is_comp_stable = List.for_all (fun node -> Option.value ~default:false (Hashtbl.find_opt stability_graph.stable_nodes node)) stability_graph.components.(comp) in
        Hashtbl.replace stability_graph.stable_components comp is_comp_stable
      in
    let () = List.iter (fun comp -> 
        let succ_comps = List.filter_map (fun (a,b) -> if a = comp then Some b else None) stability_graph.condensation_graph in
        let is_stable = Option.value ~default:false (Hashtbl.find_opt stability_graph.stable_components comp) in
        let all_below_stable = is_stable && List.for_all (fun succ_comp -> Option.value ~default:false (Hashtbl.find_opt stability_graph.all_below_component_stable succ_comp)) succ_comps in
        Hashtbl.replace stability_graph.all_below_component_stable comp all_below_stable
      ) stability_graph.preds_rec.(comp) in
    let () = Utils.Monitoring.stop_event "set_stability" in
    ()

  let is_stable stability_graph node =
    Option.value ~default:false (Hashtbl.find_opt stability_graph.stable_nodes node)

end

let%expect_test "test_condensation_graph" =
  let open Make (String) in
  let graph = {
    nodes = ["A"; "B"; "C1"; "C2"; "C3"; "D"];
    edges = [("A", "B"); ("A", "C1"); ("A", "C2"); ("C1", "C2"); ("C2", "C3"); ("C3", "C1"); ("C3", "D")]
  } in
  let stability_graph = init graph in
  let () = List.iter (fun (a,b) -> Printf.printf "%d->%d, " a b) stability_graph.condensation_graph in
  [%expect {| 1->0, 3->1, 3->2, |}]

let%expect_test "test_get_preds_rec" =
  let open Make (String) in
  let graph = {
    nodes = ["A"; "B"; "C1"; "C2"; "C3"; "D"];
    edges = [("A", "B"); ("A", "C1"); ("A", "C2"); ("C1", "C2"); ("C2", "C3"); ("C3", "C1"); ("C3", "D")]
  } in
  let stability_graph = init graph in
  let rec get_preds_rec comps accu =
    if comps = [] then accu
    else
      let (new_preds, preds) = List.fold_left (fun accu comp ->
        List.fold_left (fun (new_preds, preds) (a,b) ->
          if b = comp && IntSet.find_opt a preds = None then 
            (a::new_preds, IntSet.add a preds)
          else (new_preds, preds)) accu stability_graph.condensation_graph
        ) ([], accu) comps in
      get_preds_rec new_preds preds
  in
  let () = IntSet.iter (fun comp -> Printf.printf "%d, " comp) (get_preds_rec [0] (IntSet.add 0 IntSet.empty)); Printf.printf "\n" in
  [%expect {|0, 1, 3, |}]

let%expect_test "test_complete" =
  let open Make (String) in
  let graph = {
    nodes = ["A"; "B"; "C1"; "C2"; "C3"; "D"];
    edges = [("A", "B"); ("A", "C1"); ("A", "C2"); ("C1", "C2"); ("C2", "C3"); ("C3", "C1"); ("C3", "D")]
  } in
  let stability_graph = init graph in
  let print_all_below_stable () =
    let all_below_list = List.map (fun node -> (node, are_all_below_stable stability_graph node)) graph.nodes in
    Printf.printf "%s\n" (String.concat ", " (List.map (fun (node, value) -> Printf.sprintf "%s:%B" node value) all_below_list))
  in
  let () = set_stability stability_graph "D" true in
  print_all_below_stable ();
  [%expect {|A:false, B:false, C1:false, C2:false, C3:false, D:true|}];
  let () = set_stability stability_graph "B" true in
  print_all_below_stable ();
  [%expect {|A:false, B:true, C1:false, C2:false, C3:false, D:true|}];
  let () = set_stability stability_graph "C2" true in
  print_all_below_stable ();
  [%expect {|A:false, B:true, C1:false, C2:false, C3:false, D:true|}];
  let () = set_stability stability_graph "A" true in
  print_all_below_stable ();
  [%expect {|A:false, B:true, C1:false, C2:false, C3:false, D:true|}];
  let () = set_stability stability_graph "C1" true in
  print_all_below_stable ();
  [%expect {|A:false, B:true, C1:false, C2:false, C3:false, D:true|}];
  let () = set_stability stability_graph "C3" true in
  print_all_below_stable ();
  [%expect {|A:true, B:true, C1:true, C2:true, C3:true, D:true|}];
  let () = set_stability stability_graph "C2" false in
  print_all_below_stable ();
  [%expect {|A:false, B:true, C1:false, C2:false, C3:false, D:true|}]
  