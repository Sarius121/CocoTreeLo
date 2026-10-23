open Logic

(** module for handling Kripke structures *)

module type State = sig
  type t
  val to_string: t -> string
  val hash: t -> int
  val to_multiset: t -> Multiset_rewrite_system.term
  val get_constraints: t -> (Multiset_rewrite_system.multiset * bool) list
end

module type Kripke = sig
  module State: State
  (* name, labels or facts *)
  type state = State.t

  (* condition in SMTLib2 format, actual condition is the conjunction of the list elements *)
  type condition = Sat.expr list
  (* x := e *)
  type assignments = { regular: Substitution.t; nondet: string list; unknowns: string list }
  (* state1, state2, condition, assignments, condition_post, assignments_post, name *)
  type transition_type = MAY_AND_MUST | ONLY_MAY
  type transition = state * state * transition_type * condition * assignments * condition * assignments * string

  type kripke

  (** create an empty Kripke structure *)
  val empty : kripke

  (** add a state to a Kripke structure *)
  val add_state: kripke -> state -> kripke

  val contains_state: kripke -> state -> bool

  (** add a may-transition to a Kripke structure *)
  val add_transition: kripke -> transition -> kripke

  (** add an initial state to a Kripke structure (it is not automatically added as a state) *)
  val add_initial_state: kripke -> state -> kripke

  (** get all initial states *)
  val get_initial_states: kripke -> state list

  (** fold over all transitions that start at the given state *)
  val fold_transitions: ('a -> transition -> 'a) -> 'a -> kripke -> state -> 'a

  val transition_labels_to_string: transition -> string

  val draw: kripke -> string

  val read_from_file: string -> kripke

  val get_stats: kripke -> int * int
end

module Make(S: State): (Kripke with module State = S) = struct
  module State = S
  type state = State.t

  type condition = Sat.expr list
  type assignments = { regular: Substitution.t; nondet: string list; unknowns: string list }
  type transition_type = MAY_AND_MUST | ONLY_MAY
  type transition = state * state * transition_type * condition * assignments * condition * assignments * string

  module StateSet = Set.Make(struct
      type t = state
      let compare = Repr.compare
    end)
  module TransitionSet = Set.Make(struct
      type t = transition
      let compare = Repr.compare
    end)

  module OutgoingMap = Utils.Outgoing_map.Make(struct
      type t = state
      let compare = Repr.compare
    end)

  (** type of Kripke structures*)
  type kripke = {states: StateSet.t; transitions: TransitionSet.t; initial: state list; outgoing_map: transition OutgoingMap.t}

  (** create an empty Kripke structure *)
  let empty = {
    states = StateSet.empty;
    transitions = TransitionSet.empty;
    initial = [];
    outgoing_map = OutgoingMap.empty}

  (** add a state to a Kripke structure *)
  let add_state kripke state = {kripke with states = StateSet.add state kripke.states}

  let contains_state kripke state = StateSet.find_opt state kripke.states != None

  let add_transition kripke transition =
    (* TODO sanity check -> could/should be removed for production *)
    let (stateA, stateB, _, _, _, _, _, _) = transition in
    let () = if StateSet.find_opt stateA kripke.states = None || StateSet.find_opt stateB kripke.states = None
      then failwith "State has to be added to the Kripke structure, before you can add a transition with it"
      else () in
    {kripke with 
      transitions = TransitionSet.add transition kripke.transitions;
      outgoing_map = OutgoingMap.update stateA transition kripke.outgoing_map}

  (** add an initial state to a Kripke structure (it is not automatically added as a state) *)
  let add_initial_state kripke state =
    (* TODO sanity check -> could/should be removed for production *)
    let () = if StateSet.find_opt state kripke.states = None
      then failwith "State has to be added to the Kripke structure, before you can add it as an initial state"
      else () in
    {kripke with initial = state::kripke.initial}

  (** get all initial states *)
  let get_initial_states kripke = kripke.initial

  let fold_transitions (f: 'a -> transition -> 'a) (accu:'a) kripke state =
    let outgoing = OutgoingMap.get state kripke.outgoing_map in
    List.fold_left f accu outgoing

  let assignments_to_string assignments =
    let regular_s = Substitution.to_string_assignment assignments.regular in
    let regular_s = Utils.Str_utils.replace regular_s "\\" "\\\\\\\\" in
    let nondet_s = List.map (fun var -> var ^ ":=?") assignments.nondet in
    let unknowns_s = List.map (fun var -> var ^ ":=??") assignments.unknowns in
    if regular_s = "" then
      String.concat "," (nondet_s @ unknowns_s)
    else
      String.concat "," (regular_s::nondet_s @ unknowns_s)

  let transition_labels_to_string (_, _, _, condition, assignments, condition_post, assignments_post, name: transition) = 
    let assignments_s = assignments_to_string assignments in
    let assignments_post_s = assignments_to_string assignments_post in
    Printf.sprintf "%s: %s->%s|%s->%s" name (Sat.to_string (Sat.mk_and condition)) assignments_s (Sat.to_string (Sat.mk_and condition_post)) assignments_post_s

  let draw kripke = 
    let transitions_s = String.concat "\n"
      (List.map (fun transition ->
          let (stateA, stateB, transition_type, _, _, _, _, _) = transition in
          if transition_type = MAY_AND_MUST then
            Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\"]" (State.to_string stateA) (State.to_string stateB) (transition_labels_to_string transition)
          else
            Printf.sprintf "\"%s\" -> \"%s\" [label=\"%s\", style=\"dashed\"]" (State.to_string stateA) (State.to_string stateB) (transition_labels_to_string transition)
        ) (TransitionSet.to_list kripke.transitions)) in
    String.concat "\n" ["digraph g {"; transitions_s; "}"]

  let read_from_file filename = failwith "This Kripke type cannot be read from a file."

  let get_stats kripke =
    (StateSet.cardinal kripke.states, TransitionSet.cardinal kripke.transitions)
end

module LabeledState = struct
  type t = string * string list
  let to_string (name, labels) = 
    let labels_s = String.concat ", " labels in
    Printf.sprintf "%s {%s}" name labels_s
  let hash (state_name, _) = String.hash state_name (* TODO *)
  let to_multiset _ = failwith "The labeled states can't be used for facts."
  let get_constraints _ = []
end

module LabeledKripke = struct
  include Make(LabeledState)

  let parse_state state_s: state =
      let regex = Str.regexp "\\([^[]*\\) \\[\\(.*\\)\\]" in
      let b = Str.string_match regex state_s 0 in
      if b then () else failwith (Printf.sprintf "Cannot parse state: %s. Correct format: name [label1, label2, ...]\n" state_s);
      let name = Str.matched_group 1 state_s in
      let labels_s = Str.matched_group 2 state_s in
      let labels = Utils.Str_utils.get_all_matching labels_s "[A-Za-z0-9_]+" in
      (name, labels)

  let parse_assignments assignments_s : assignments =
    if assignments_s = "" then { regular = Substitution.empty; nondet = []; unknowns = [] } else
    let assignments_s = String.split_on_char ',' assignments_s in
    let (regular, nondet) = List.fold_left (fun (regular, nondet) assignment_s ->
        let regex = Str.regexp " *\\([^:= ]+\\) *:= *\\([^:= ]+\\)" in
        let b = Str.string_match regex assignment_s 0 in
        if b then () else failwith (Printf.sprintf "Cannot parse assignment: %s. Correct format: x:=e\n" assignment_s);
        let var = Str.matched_group 1 assignment_s in
        let expr = Str.matched_group 2 assignment_s in
        if expr = "?" then (regular, var::nondet)
        else (Substitution.add_arg regular var (Arg_terms.(Int (Smt (Sat.parse_smt expr false)))), nondet)
      ) (Substitution.empty, []) assignments_s in
    { regular; nondet; unknowns = [] }

  (** parse a Kripke structure from .dot file, the parser is very primitive and it ignores lines that it cannot parse *)
  let read_from_file filename =
    let channel = open_in filename in
    let g = ref empty in
    try
      (* ignore first line *)
      let _ = input_line channel in
      let rec read_lines () =
        let line = input_line channel in
        if line = "}" then !g
        else if line = "" then read_lines () (* skip blank lines *)
        else
          let regex = Str.regexp "[^\"]*\"\\([^\"]*\\)\"[^\"]*\"\\([^\"]*\\)\"[^\"]*\"\\([^\">-]*\\)->\\([^\">-]*\\)\".*\"\\([^\"]*\\)\"" in
          let b = Str.string_match regex line 0 in
          if b then () else failwith (Printf.sprintf "Cannot parse line: %s. Correct format: \"state1\" -> \"state2\" [label=\"condition->assignment\"]\n" line);
          let state1_s = Str.matched_group 1 line in
          let state2_s = Str.matched_group 2 line in
          let condition = Str.matched_group 3 line in
          let assignments_s = Str.matched_group 4 line in
          let name = Str.matched_group 5 line in
          let assignments = parse_assignments assignments_s in
          let state2 = parse_state state2_s in
          if state1_s = "start" then (g := (add_initial_state (add_state !g state2) state2); read_lines ())
          else
            let state1 = parse_state state1_s in
            (g := add_state !g state1;
            g := add_state !g state2;
            g := add_transition !g (state1, state2, MAY_AND_MUST, [(Sat.parse_smt condition true)], assignments, [Sat.mk_bool true], { regular = Substitution.empty; nondet = []; unknowns = [] }, name);
            read_lines ())
      in
      read_lines ()
    with End_of_file ->
      close_in_noerr channel;
      !g

end

(* TODO legacy code *)
module FactState = struct
  type t = string * Multiset_rewrite_system.multiset
  let to_string (name, facts) = 
    let facts_s = Multiset_rewrite_system.ms_to_string facts in 
    Printf.sprintf "%s %s" name facts_s
  let hash (state_name, _) = String.hash state_name (* TODO *)
  let to_multiset (_, ms) = Multiset_rewrite_system.Const ms
  let get_constraints _ = []
end

(* TODO legacy code *)
module FactKripke = Make(FactState)

(* Tests *)

(*let%expect_test "test_state_set" =
  let stateA = ("", []) in
  let stateB = ("", [("P", ["x"])]) in
  let states = FactKripke.StateSet.empty in
  let states = FactKripke.StateSet.add stateA states in
  if FactKripke.StateSet.find_opt stateB states = None then Printf.printf "None"
  else Printf.printf "Some";
  [%expect {| None |}] *)
