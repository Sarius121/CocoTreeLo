open Cocotreelo
open Encoding.Encoding_params
open Logic.Arg_terms

(** WARNING:
  These tests compare the drawn Kripke graphs against reference files.
  Because the Kripke graphs are implemented as sets, the string representation could differ between execution by order of lines.
  This is not taken into account at the moment!
*)

let max_rounds = 20

let params_cap_p_1 = {cap=[("P", 1); ("Q", 0)]; tracked=[]; start_with_empty_state = true; hide_action_facts = false}
let params_cap_0 = {cap=[("P", 0); ("Q", 0)]; tracked=[]; start_with_empty_state = true; hide_action_facts = false}

let test_cases = [
  (* testing individual operators *)
  ("rule12_x-is-5", "examples/msrs/rule12.spthy", "examples/properties/actl-false/x-is-5.ctl", params_cap_p_1, Some false, Counterexample_finder.FOUND);
  ("rule12_p5-next-q5", "examples/msrs/rule12.spthy", "examples/properties/actl-false/p5-next-q5.ctl", params_cap_p_1, Some false, FOUND);
  ("rule12_always-p5-next-q5", "examples/msrs/rule12.spthy", "examples/properties/actl-false/always-p5-next-q5.ctl", params_cap_p_1, Some false, FOUND);
  ("rule1_eventually-q5", "examples/msrs/rule1.spthy", "examples/properties/actl-false/eventually-q5.ctl", params_cap_p_1, Some false, FOUND);
  (* combination of operators *)
  ("rule12_always-next-still-px", "examples/msrs/rule12.spthy", "examples/properties/actl/always-next-still-px.ctl", params_cap_0, None, FOUND);

  (* counterexample needs iterating a cycle *)
  (* TODO *)

  (* wrongly falsified (i.e. no valid counterexample exists) *)
  ("rule12_no-px-next-no-qx", "examples/msrs/rule12.spthy", "examples/properties/actl/no-px-next-no-qx.ctl", params_cap_0, None, SPURIOUS);
  ("rule12_always-no-px-next-no-qx", "examples/msrs/rule12.spthy", "examples/properties/actl/always-no-px-next-no-qx.ctl", params_cap_0, None, SPURIOUS);

  (* with constraints *)
  ("rule12_exists-next-next-qx", "examples/msrs/rule12.spthy", "examples/properties/ectl/exists-next-next-qx.ctl", {cap=[("P", 0); ("Q", 0)]; tracked=[[("P*", [Int (Var "x")])]]; start_with_empty_state = true; hide_action_facts = false}, Some true, FOUND);
  ("rule123_ex-exists-next-next-rx", "examples/msrs/rule123.spthy", "examples/properties/ectl/ex-exists-next-next-rx.ctl", {cap=[("P", 0); ("Q", 0); ("R", 0)]; tracked=[[("P*", [Int (Var "x")])]; [("Q*", [Int (Var "x")])]]; start_with_empty_state = true; hide_action_facts = false}, Some true, FOUND);
  ("rule123_ex-exists-next-next-rx_none", "examples/msrs/rule123.spthy", "examples/properties/ectl/ex-exists-next-next-rx.ctl", {cap=[("P", 0); ("Q", 0); ("R", 0)]; tracked=[[("P*", [Int (Var "x")])]]; start_with_empty_state = true; hide_action_facts = false}, None, FOUND);

  (* non-leading quantifiers *)
  ("rule12_ex-ex-qx", "examples/msrs/rule12.spthy", "examples/properties/general-quantifiers/ex-ex-qx.ctl", params_cap_p_1, None, FOUND);
]

let reference_files_path = "test/refs/counterexamples/"

let read_file filename =
  let file = open_in filename in
  let contents = ref "" in
  try
    while true; do
      let line = input_line file in
      contents := !contents ^ line ^ "\n"
    done;
  with End_of_file -> !contents

let convert_test_case (test_name, input_file, ctl_file, params, expected_result, expected_found) () =
  let msrs = Logic.Parser.Utils.read_msrs_from_file input_file in
  let property = Logic.Parser.Utils.read_ctl_from_file ctl_file in
  let (kripke, dependent_vars, track_vars) = Encoding.Maude_narrowing_combi.gen_kripke msrs Config.maude_path property params in
  
  let open Counterexample_finder in
  let module Tableau_product = Tableau_product.Make(Encoding.Maude_narrowing_combi.Kripke) in
  let module Annotation_generator = Annotation_generator.Make(Tableau_product)(Encoding.Maude_narrowing_combi) in
  let module Counterexample_finder = Counterexample_finder.Make(Tableau_product) in

  let tab = Tableau_product.gen_product_structure kripke property in

  let (status, ann) = Annotation_generator.annotate_tab tab dependent_vars max_rounds (fun ann verification_state cur_scc scc_count -> ()) in
  let status_to_string = (fun status -> match status with
    | Annotation_generator.DONE -> "DONE"
    | CANCELLED -> "CANCELLED") in
  let status_testable = Alcotest.testable (Fmt.of_to_string status_to_string) (=) in
  let () = Alcotest.(check status_testable) "Annotation process termination" DONE status in
  let ann_res = Annotation_generator.check_if_verified ann kripke property track_vars in
  let () = Alcotest.(check (option bool)) "Expected verification result" expected_result ann_res in
  
  let (result, counterexample) = Option.get (Counterexample_finder.find_counterexample tab ann kripke track_vars dependent_vars property ann_res) in
  let result_to_string = (fun res -> match res with
    | FOUND -> "FOUND"
    | NOT_FOUND -> "NOT_FOUND"
    | SPURIOUS -> "SPURIOUS") in
  let result_testable = Alcotest.testable (Fmt.of_to_string result_to_string) (=) in
  let () = Alcotest.(check result_testable) "Actual result value differs." expected_found result in

  let module Counterexample = Counterexample.Make(Tableau_product.Kripke.State) in

  let counterexample_expected = read_file (reference_files_path ^ test_name ^ ".dot") in
  let () = Alcotest.(check string) "Counterexample is not as expected." counterexample_expected (Counterexample.draw counterexample ^ "\n") in

  let counterexample_path = Counterexample.extract_kripke counterexample (result = SPURIOUS) in
  let counterexample_path_expected = read_file (reference_files_path ^ test_name ^ "_path.dot") in
  let () = Alcotest.(check string) "Counterexample path is not as expected." counterexample_path_expected (Counterexample.draw_path counterexample_path ^ "\n") in
  ()

let register_tests () =
  List.map (fun test_case ->
      let (test_name, _, _, _, _, _) = test_case in
      Alcotest.test_case test_name `Slow (convert_test_case test_case)
    ) test_cases
