open Cocotreelo
open Encoding

(* currently somewhat fast: 0-18,21-30,32,34-40,42-49 *)
(* slow but correct: 31, (41?) *)
(* no refinement found: 2,14,15, 17,36,37 (last three depend on AG triggering refinement), 44 *)

let system_test ?(manual_params) max_cegar_cycles max_rounds_per_scc (msrs, property, expected_result) () =
  let module Encoding = Maude_narrowing_combi in
  let initial_params = Encoding_params.determine_parameters msrs property ?additional_manual_params:manual_params in

  let rec cegar_cycle cegar_round params =
    let () = Alcotest.(check bool) "Check whether max cegar cycles are reached." true (cegar_round < max_cegar_cycles) in
    (* convert MSRS to Kripke *)
    let (kripke, var_dependencies, structured_track_vars) = Encoding.gen_kripke msrs Config.maude_path property params in
    
    (* generate product structure*)
    let module Tableau_product = Tableau_product.Make(Encoding.Kripke) in
    let tab = Tableau_product.gen_product_structure kripke property in

    (* annotate product structure *)
    let module Annotation_generator = Annotation_generator.Make(Tableau_product)(Encoding) in
    let (status, ann) = Annotation_generator.annotate_tab tab var_dependencies max_rounds_per_scc (fun ann verification_state (cur_scc_tt, cur_scc_ff) scc_count -> ()) in
    
    let () = Alcotest.(check bool) "Check whether max rounds was reached for a SCC." true (status = DONE) in
    let verified = Annotation_generator.check_if_verified ann kripke property structured_track_vars in

    match verified with
    | Some verified -> verified
    | None ->
      (* maybe finder *)
      let module Maybe_finder = Maybe_finder.Make(Tableau_product) in
      let (res, maybe_reason) = Maybe_finder.find_counterexample tab var_dependencies ann kripke property in
      let () = Alcotest.(check bool) "Check whether the maybe reason was found." true (res = FOUND) in
      
      (* refine parameters *)
      let module Refiner = Refiner.Make(Tableau_product.Kripke.State) in
      let params = Refiner.get_encoding_params params maybe_reason msrs property structured_track_vars in
      match params with
      | Some params -> cegar_cycle (cegar_round + 1) params
      | None -> Alcotest.(check bool) "No refinement found." true false; true
  in

  let result = cegar_cycle 0 initial_params in
  Alcotest.(check bool) "Check whether the verification result is as expected." expected_result result

let register_tests () =
  List.map (fun (test_input_id, (msrs_file, ctl_file, expected_result)) ->
    let expected_result = Option.get expected_result in
    let test_name = String.concat "_" [test_input_id] in
    let msrs = Logic.Parser.Utils.read_msrs_from_file msrs_file in
    let property = Logic.Parser.Utils.read_ctl_from_file ctl_file in
    Alcotest.test_case test_name `Slow (system_test 3 10 (msrs, property, expected_result))
  ) Test_annotation_process.test_inputs

