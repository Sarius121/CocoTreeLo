open Cocotreelo
open Logic

let maude_path = "extlib/custom-maude/maude"
let rounds = 100
let max_cegar_cycles = 10
let test_cases = [
  (* ACTL*)
  ("rule12_always-next-still-px-or-qx", "∀ x. AG (P(x) => AX (P(x) || Q(x)))", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-next-still-px-or-qx.ctl", (Some true)));
  ("rule12_always-px-wuntil-qx", "∀ x. AG (P(x) => A(P(x) W Q(x)))", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px-wuntil-qx.ctl", (Some true)));
  ("rule123_always-px-wuntil-qx-wuntil-rx", "∀ x. AG (P(x) => A(P(x) W A(Q(x) W R(x))))", ("examples/msrs/rule123.spthy", "examples/properties/actl/always-px-wuntil-qx-wuntil-rx.ctl", (Some true)));

  ("consume-equal-vars1_always-next-still-px-qx-or-rx", "∀ x. AG ((P(x) && Q(x)) => AX (((P(x) && Q(x)) || R(x))))", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-next-still-px-qx-or-rx.ctl", (Some true)));
  ("consume-equal-vars1_always-px-qx-wuntil-rx", "∀ x. AG ((P(x) && Q(x)) => A(((P(x) && Q(x)) W R(x))))", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-px-qx-wuntil-rx.ctl", (Some true)));
  
  ("rule12_always-px-iff-py", "∀ x. ∃ y. AG ((P(x) && P(y)) || (!P(x) && !P(y)))", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px-iff-py.ctl", (Some true))); (* problem with unknown *)
  
  ("rule12_one-p-stays", "∀ x. ∀ y. (x = y) || AG ((P(x) && P(y)) => AX (P(x) || P(y)))", ("examples/msrs/rule12.spthy", "examples/properties/actl/one-p-stays.ctl", Some true)); (* see below *)

  (* ECTL *)
  ("rule123_exists-eventually-rx", "∀ x. EF (P(x) && EF R(x))", ("examples/msrs/rule123.spthy", "examples/properties/ectl/exists-eventually-rx.ctl", Some true));
  
  (* ACTL where capp doesn't help *)
  ("rule12_always-no-px-next-no-qx", "∀ x. AG (P(x) || Q(x) || AX !Q(x))", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-no-px-next-no-qx.ctl", Some true)); (* cap>0 doesn't help anymore *)
  ("rule123_always-no-px-next-next-no-rx", "∀ x. AG (P(x) || Q(x) || R(x) || AX AX !R(x))", ("examples/msrs/rule123.spthy", "examples/properties/actl/always-no-px-next-next-no-rx.ctl", Some true));
  
  ("rule123_exists-eventually-r5", "EF R(5)", ("examples/msrs/rule123.spthy", "examples/properties/ectl/exists-eventually-r5.ctl", Some true));
  ("rule123_eventually-r5", "AF R(5)", ("examples/msrs/rule123.spthy", "examples/properties/actl-false/eventually-r5.ctl", Some false)); (* annotation terminates, b/c we can choose path w/o Q's *)

  (* mixed (classical data minimization pattern) *)
  ("rule12_ag-px-ef-qx", "∀ x. AG (P(x) => EF Q(x))", ("examples/msrs/rule12.spthy", "examples/properties/mixed/ag-px-ef-qx.ctl", Some true)); (* only verifies with cap_P>0, verifies with cap_p>0 b/c EF Q(x) holds *)

  ("rule12_ag-px-ex-qx", "∀ x. AG (P(x) => EX Q(x))", ("examples/msrs/rule12.spthy", "examples/properties/mixed/ag-px-ex-qx.ctl", Some true));
  ("rule123_ag-px-ex-ex-rx", "∀ x. AG (P(x) => EX EX R(x))", ("examples/msrs/rule123.spthy", "examples/properties/mixed/ag-px-ex-ex-rx.ctl", Some true));
  
  (* action facts *)
  ("action_always-px-next-qx", "∀ x. AG (ActionP(x) => EX ActionQ(x))", ("examples/msrs/action.spthy", "examples/properties/action-facts/always-px-next-qx.ctl", Some true));
  ("action123_always-px-next-next-rx", "∀ x. AG (ActionP(x) => EX EX ActionR(x))", ("examples/msrs/action123.spthy", "examples/properties/action-facts/always-px-next-next-rx.ctl", Some true));

  (* general quantifiers *)
  ("rule1_always-something", "AX AG (∃ x. P(x))", ("examples/msrs/rule1.spthy", "examples/properties/general-quantifiers/always-something.ctl", Some true)); (* reason are non-leading quantifiers, only verifies with cap_P>0 *)
  ("rule1_always-ex-something", "AG (∃ x. EX P(x))", ("examples/msrs/rule1.spthy", "examples/properties/general-quantifiers/always-ex-something.ctl", Some true));

  (* relevant removing facts *)
  ("rule12_always-next-still-px", "∀ x. AG (P(x) => AX P(x))", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-next-still-px.ctl", (Some false))); (* no refinement b/o removing facts is relevant *)

  (* two paths *)
  ("two-paths_ag-px-ex-ex-rxy", "∀ x. AG (P(x) => EX EX R(x))", ("examples/msrs/two-paths-simple.spthy", "examples/properties/two-paths/ag-px-ex-ex-rx.ctl", Some true));
  ("two-paths_ef-rx-via-both-paths", "∀ x. AG (P(x) => (EF (R(x) && Path1(x)) && EF (R(x) && Path2(x))))", ("examples/msrs/two-paths-simple.spthy", "examples/properties/two-paths/ef-rx-via-both-paths.ctl", Some true));
  ("two-paths_ex-ex-rx-via-both-paths", "∀ x. AG (P(x) => (EX EX (R(x) && Path1(x)) && EX EX (R(x) && Path2(x))))", ("examples/msrs/two-paths-simple.spthy", "examples/properties/two-paths/ex-ex-rx-via-both-paths.ctl", Some true));
]

type result = CANCELLED of string | TERMINATED

(* init modules *)
module Enc = Encoding.Maude_narrowing_combi
module Tableau_product = Tableau_product.Make(Enc.Kripke)
module Annotation_generator = Annotation_generator.Make(Tableau_product)(Enc)
module Maybe_finder = Maybe_finder.Make(Tableau_product)
module Refiner = Refiner.Make(Tableau_product.Kripke.State)
module Counterexample = Counterexample.Make(Tableau_product.Kripke.State)

let run_test_case (program_file, ctl_file, expected) =
  (* parse input files *)
  let property = Parser.Utils.read_ctl_from_file ctl_file in
  let property_leading = Ctl.put_quantifiers_leading property in
  let property = Option.value ~default:property property_leading in
  let msrs = Parser.Utils.read_msrs_from_file program_file in

  let rule_num = List.length (snd msrs) in

  let initial_params = Encoding.Encoding_params.determine_parameters msrs property in

  let rec cegar_cycle cegar_round params =
    (* convert MSRS to Kripke *)
    let (kripke, var_dependencies, track_vars) = Enc.gen_kripke msrs maude_path property params in
    
    (* generate product structure*)
    let tab = Tableau_product.gen_product_structure kripke property in
    let (node_num, edge_num) = Tableau_product.get_stats tab in

    let stats = (fst msrs, Ctl.to_string property, rule_num, node_num, edge_num, cegar_round) in

    (* annotate product structure *)
    let (status, ann) = Annotation_generator.annotate_tab tab var_dependencies rounds (fun ann verification_state (cur_scc_tt, cur_scc_ff) scc_count -> ()) in
    let verified = Annotation_generator.check_if_verified ann kripke property track_vars in
    match verified with
    | Some _ -> 
      if verified = expected then (TERMINATED, stats)
      else (Printf.printf "v Unexpected Result v\n"; (TERMINATED, stats))
    | None -> 
      if status = CANCELLED then (CANCELLED "annotation", stats)
      else 
      (* maybe finder *)
      let (res, maybe_reason) = Maybe_finder.find_counterexample tab var_dependencies ann kripke property in
      
      (* refine parameters *)
      let params = Refiner.get_encoding_params params maybe_reason msrs property track_vars in
      match params with
      | Some params -> 
        if cegar_round + 1 >= max_cegar_cycles then (CANCELLED "max cegar", stats)
        else cegar_cycle (cegar_round + 1) params
      | None -> (CANCELLED "no refinement", stats)
  in

  cegar_cycle 0 initial_params

let make_long s d =
  let len = String.length s in
  if len > d then s
  else s ^ String.make (d - len) ' '

let longest_msrs = 20
let longest_property = 70

let print_test_res (name, friendly_property_name, (res, (msrs, property, rule_num, node_num, edge_num, cegar_round)), time) =
  let cancelled_s = match res with
    | TERMINATED -> ""
    | CANCELLED reason -> " CANCELLED b/o " ^ reason 
  in
  Printf.printf "%s | %s\t | %d\t  | %d\t   | %d   \t | %d\t   | %.1f s%s\n" (make_long msrs longest_msrs) (make_long friendly_property_name longest_property) rule_num node_num edge_num (cegar_round+1) time cancelled_s;
  flush stdout

let () =
  let () = Printf.printf "%s | %s\t | #Rules | #Nodes | #Edges\t | #Cycles | Verification Time\n" (make_long "MSRS" longest_msrs) (make_long "Property" longest_property) in
  let () = Printf.printf "--------------------------------------------------------------------------------------------------------------------------------------------------------------\n" in

  List.iter (fun (name, friendly_property_name, test_case) ->
      Utils.Monitoring.init_stats ();
      let res = run_test_case test_case in
      let (_, time) = Utils.Monitoring.get_total_time () in
      print_test_res (name, friendly_property_name, res, time)
    ) test_cases;

  Maude.remove_maude_input_file ()
