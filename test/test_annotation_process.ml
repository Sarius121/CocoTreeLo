open Cocotreelo
open Logic

(* 
  currently terminating: 0-13,16,21-30,32-40
  currently giving precise results for cap=0: 0-1,3-13,16,21,23,27,30,32-33
*)
let test_inputs = [
  (* ACTL *)
  ("rule12_always-px-or-not", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px-or-not.ctl", Some true));
  ("rule12_always-next-still-px-or-qx", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-next-still-px-or-qx.ctl", (Some true)));
  ("rule12_always-next-still-px", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-next-still-px.ctl", (Some false)));
  ("rule12_always-px-wuntil-qx", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px-wuntil-qx.ctl", (Some true)));
  ("rule12_initial-state-empty", ("examples/msrs/rule12.spthy", "examples/properties/actl/initial-state-empty.ctl", (Some true)));
  ("rule123_always-px-soon-rx", ("examples/msrs/rule123.spthy", "examples/properties/actl/always-px-soon-rx.ctl", (Some true)));
  ("rule123_always-px-wuntil-qx-wuntil-rx", ("examples/msrs/rule123.spthy", "examples/properties/actl/always-px-wuntil-qx-wuntil-rx.ctl", (Some true)));
  ("consume-equal-vars1_always-next-still-px-qx-or-rx", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-next-still-px-qx-or-rx.ctl", (Some true)));
  ("consume-equal-vars1_always-px-qx-wuntil-rx", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-px-qx-wuntil-rx.ctl", (Some true)));
  ("consume-equal-vars2_always-next-still-px-qx-or-rx", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-next-still-px-qx-or-rx.ctl", (Some true)));
  ("consume-equal-vars2_always-px-qx-wuntil-rx", ("examples/msrs/consume-equal-vars1.spthy", "examples/properties/actl/always-px-qx-wuntil-rx.ctl", (Some true)));
  ("produce-equal-vars_always-next-still-px-qx-or-rx", ("examples/msrs/produce-equal-vars.spthy", "examples/properties/actl/always-next-still-px-qx-or-rx.ctl", (Some true)));
  ("consume-equal-vars_always-px-qx-wuntil-rx", ("examples/msrs/produce-equal-vars.spthy", "examples/properties/actl/always-px-qx-wuntil-rx.ctl", (Some true)));
  ("rule12_initial-uniqueness", ("examples/msrs/rule12.spthy", "examples/properties/actl/initial-uniqueness.ctl", (Some true)));
  ("track-multi1_always-twop-implies-next-px1", ("examples/msrs/track-multi1.spthy", "examples/properties/actl/always-twop-implies-next-px1.ctl", (Some true))); (* problem with unknown *)
  ("track-multi2_always-twop-implies-next-px2", ("examples/msrs/track-multi2.spthy", "examples/properties/actl/always-twop-implies-next-px2.ctl", (Some true))); (* problem with unknown *)
  ("rule1_always-px-iff-py", ("examples/msrs/rule1.spthy", "examples/properties/actl/always-px-iff-py.ctl", (Some true)));
  ("rule12_always-px-iff-py", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px-iff-py.ctl", (Some true))); (* problem with unknown *)
  ("rule12_always-px", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-px.ctl", Some false)); (* problem with unknown *)
  ("two-paths-multi_always-wuntil-rxy", ("examples/msrs/two-paths-multi.spthy", "examples/properties/actl/always-wuntil-rxy.ctl", Some true)); (* doesn't terminate *)
  ("two-paths-multi_always-wuntil-rxy2", ("examples/msrs/two-paths-multi.spthy", "examples/properties/actl/always-wuntil-rxy2.ctl", Some true)); (* doesn't terminate *)
  ("rule12_one-p-stays", ("examples/msrs/rule12.spthy", "examples/properties/actl/one-p-stays.ctl", Some true)); (* see below *)
  ("random-chain_one-p-stays", ("examples/msrs/random-chain.spthy", "examples/properties/actl/one-p-stays.ctl", Some true)); (* edge case: non-invertible rules are not handled as precisely as invertible rules yet *)
  (* ACTL (counterexample for cap>0 necessary and cap>0 also doesn't solve it in the general case) *)
  ("rule12_px-next-qx2", ("examples/msrs/rule12.spthy", "examples/properties/actl/px-next-qx2.ctl", Some true));
  ("rule12_px-next-qx", ("examples/msrs/rule12.spthy", "examples/properties/actl/px-next-qx.ctl", Some true)); (* same property expressed differently -> only verifies for cap(P)>0 *)
  ("rule12_no-px-next-no-qx", ("examples/msrs/rule12.spthy", "examples/properties/actl/no-px-next-no-qx.ctl", Some true)); (* verifies for cap>0 *)
  ("rule12_always-no-px-next-no-qx", ("examples/msrs/rule12.spthy", "examples/properties/actl/always-no-px-next-no-qx.ctl", Some true)); (* cap>0 doesn't help anymore *)
  ("rule123_no-px-next-next-no-rx", ("examples/msrs/rule123.spthy", "examples/properties/actl/no-px-next-next-no-rx.ctl", Some true));
  ("rule123_always-no-px-next-next-no-rx", ("examples/msrs/rule123.spthy", "examples/properties/actl/always-no-px-next-next-no-rx.ctl", Some true));
  (* ECTL *)
  ("rule12_exists-eventually-rx", ("examples/msrs/rule12.spthy", "examples/properties/ectl/exists-eventually-rx.ctl", Some false));
  ("rule12_exists-eventually-qx", ("examples/msrs/rule12.spthy", "examples/properties/ectl/exists-eventually-qx.ctl", Some true));
  ("rule123_exists-eventually-rx", ("examples/msrs/rule123.spthy", "examples/properties/ectl/exists-eventually-rx.ctl", Some true));
  ("users_user-value-change", ("examples/msrs/users.spthy", "examples/properties/ectl/user-value-change.ctl", Some true));
  ("two-paths-multi_two-paths-multi-lead-to-r", ("examples/msrs/two-paths-multi.spthy", "examples/properties/ectl/two-paths-lead-to-r.ctl", Some true)); (* doesn't terminate *)
  (* ACTL with constants as fact arguments *)
  ("5-is-special_only-q5", ("examples/msrs/5-is-special.spthy", "examples/properties/actl-consts/only-q5.ctl", Some true));
  ("5-is-special_never-q6", ("examples/msrs/5-is-special.spthy", "examples/properties/actl-consts/never-q6.ctl", Some true));
  (* ACTL where annotation does not terminate *)
  ("rule12_eventually-q5", ("examples/msrs/rule12.spthy", "examples/properties/actl-false/eventually-q5.ctl", Some false)); (* annotation terminates, b/c we can choose path w/o Q's *)
  ("rule12_eventually-p5", ("examples/msrs/rule12.spthy", "examples/properties/actl-false/eventually-p5.ctl", Some false)); (* annotation does not terminate *)
  (* mixed *)
  ("rule12_px-ef-qx", ("examples/msrs/rule12.spthy", "examples/properties/mixed/px-ef-qx.ctl", Some true)); (* only verifies with cap_P>0 *)
  ("rule12_ag-px-ef-qx", ("examples/msrs/rule12.spthy", "examples/properties/mixed/ag-px-ef-qx.ctl", Some true)); (* only verifies with cap_P>0, verifies with cap_p>0 b/c EF Q(x) holds *)
  ("rule12_always-px-until-qx", ("examples/msrs/rule12.spthy", "examples/properties/mixed/always-px-until-qx.ctl", Some true)); (* only verifies with cap_P>0, verifies with cap_P>0 b/c ??? *)
  ("rule123_always-px-until-qx-until-rx", ("examples/msrs/rule123.spthy", "examples/properties/mixed/always-px-until-qx-until-rx.ctl", Some true)); (* only verifies with cap_P>0 & cap_Q>0 *)
  ("rule12_ag-px-ex-qx", ("examples/msrs/rule12.spthy", "examples/properties/mixed/ag-px-ex-qx.ctl", Some true));
  ("rule123_ag-px-ex-ex-rx", ("examples/msrs/rule123.spthy", "examples/properties/mixed/ag-px-ex-ex-rx.ctl", Some true));
  (* general quantifiers *)  
  ("rule1_always-something", ("examples/msrs/rule1.spthy", "examples/properties/general-quantifiers/always-something.ctl", Some true)); (* only verifies with cap_P>0 *)
  ("rule1_always-ex-something", ("examples/msrs/rule1.spthy", "examples/properties/general-quantifiers/always-ex-something.ctl", Some true));
  (* action facts *)  
  ("action_actions-disappear", ("examples/msrs/action.spthy", "examples/properties/action-facts/actions-disappear.ctl", Some true));
  ("action_actions-disappear2", ("examples/msrs/action.spthy", "examples/properties/action-facts/actions-disappear2.ctl", Some true));
  ("action_px-next-qx", ("examples/msrs/action.spthy", "examples/properties/action-facts/px-next-qx.ctl", Some true));
  ("action_always-px-next-qx", ("examples/msrs/action.spthy", "examples/properties/action-facts/always-px-next-qx.ctl", Some true));
]

let gen_params facts cap tracked =
  let open Encoding.Encoding_params in
  {
    cap = List.map (fun fact -> (fact, cap)) facts;
    tracked = tracked;
    start_with_empty_state = true;
    hide_action_facts = false
  }

let test_cases = [
]

let kripke_test_cases = [
  ("examples/simple-kripke.dot", "examples/properties/eventually-q.ctl", 10, (Some true));

  ("examples/opaque-rule1.dot", "examples/properties/opaque/next-px.ctl", 2, (Some true));
  ("examples/opaque-rule1.dot", "examples/properties/opaque/eventually-px.ctl", 7, (Some true));
  ("examples/opaque-rule1.dot", "examples/properties/opaque/always-px.ctl", 9, (Some true));
  ("examples/opaque-rule1.dot", "examples/properties/opaque/eventually-qx.ctl", 11, (Some false));

  ("examples/opaque-rule12.dot", "examples/properties/opaque/eventually-qx.ctl", 12, (Some true));
  ("examples/opaque-rule12.dot", "examples/properties/opaque/qx-always-possible.ctl", 9, (Some true));
  ("examples/opaque-rule12.dot", "examples/properties/opaque/eventually-not-px.ctl", 10, (Some true));
  ("examples/opaque-rule12.dot", "examples/properties/opaque/always-px-wuntil-qx.ctl", 9, (Some true));
  ("examples/opaque-rule12.dot", "examples/properties/opaque/soon-qx.ctl", 8, (Some true));

  ("examples/opaque-using-x.dot", "examples/properties/opaque-nodummy/eventually-qx.ctl", 13, (Some false));
  ("examples/opaque-using-x.dot", "examples/properties/opaque-nodummy/always-px-wuntil-qx.ctl", 9, (Some true));
  ("examples/opaque-using-x.dot", "examples/properties/opaque-nodummy/eventually-q5.ctl", 12, (Some true));
  ("examples/opaque-using-x.dot", "examples/properties/opaque-nodummy/exists-eventually-qx.ctl", 13, (Some true));

  ("examples/opaque-rule12-nodummy.dot", "examples/properties/opaque-nodummy/eventually-all-px.ctl", 9, (Some true));
  ("examples/opaque-rule12-nodummy.dot", "examples/properties/opaque-nodummy/eventually-all-next-px.ctl", 7, (Some true));

  ("examples/over-under2.dot", "examples/properties/over-under/eventually-qx.ctl", 12, (Some true));
  ("examples/over-under2.dot", "examples/properties/over-under/eventually-not-px.ctl", 10, (Some true));
  (* 
    holds for the rewrite system, but not for this encoding:
    WARNING:
      Before encoding changing SMT implementation from strings to Z3 expressions, this test needed only 14 steps.
      Either there is a mistake in the new implementation, or (more-likely) the old version terminated to early
      because of the unsoundness of the string substitution. 
   *)
  ("examples/over-under2.dot", "examples/properties/over-under/qx-always-possible.ctl", 18, (Some false));
]

let test_labeled_kripke (kripke_file, ctl_file, rounds, expected) () =
  let module Encoding = Encoding.Encoding_utils.DefaultEncoding in
  let kripke = Kripke.LabeledKripke.read_from_file kripke_file in
  let property = Parser.Utils.read_ctl_from_file ctl_file in
  
  let module Tableau_product = Tableau_product.Make(Encoding.Kripke) in
  let module Annotation_generator = Annotation_generator.Make(Tableau_product)(Encoding) in
  let tab = Tableau_product.gen_product_structure kripke property in

  let (status, ann) = Annotation_generator.annotate_tab tab (Hashtbl.create 0) rounds (fun ann verification_state cur_scc scc_count -> ()) in
  let result = Annotation_generator.check_if_verified ann kripke property [] in
  if expected = result then () else
    let expected = Option.fold ~none:"None" ~some:(fun res -> Printf.sprintf "Some %B" res) expected in
    let result = Option.fold ~none:"None" ~some:(fun res -> Printf.sprintf "Some %B" res) result in
    failwith (Printf.sprintf "Expected %s, actually was %s" expected result)

let test_with_encoding input_file ctl_file ((module Enc: Encoding.Encoding_utils.Encoding), params, rounds, expected) () =
  let msrs = Parser.Utils.read_msrs_from_file input_file in
  let property = Parser.Utils.read_ctl_from_file ctl_file in
  let params = { Encoding.Encoding_params.cap = fst params; tracked = snd params; start_with_empty_state = true; hide_action_facts = false } in
  let (kripke, dependent_vars, track_vars) = Enc.gen_kripke msrs Config.maude_path property params in
  
  let module Tableau_product = Tableau_product.Make(Enc.Kripke) in
  let module Annotation_generator = Annotation_generator.Make(Tableau_product)(Enc) in
  let tab = Tableau_product.gen_product_structure kripke property in

  let (status, ann) = Annotation_generator.annotate_tab tab dependent_vars rounds (fun ann verification_state cur_scc scc_count -> ()) in
  let result = Annotation_generator.check_if_verified ann kripke property track_vars in
  if expected = result then () else
    let expected = Option.fold ~none:"None" ~some:(fun res -> Printf.sprintf "Some %B" res) expected in
    let result = Option.fold ~none:"None" ~some:(fun res -> Printf.sprintf "Some %B" res) result in
    failwith (Printf.sprintf "Expected %s, actually was %s" expected result)

let register_annotation_tests () =
  let encoding_tests = List.map (fun (test_input_id, setting_name, test_setting) ->
      let test_name = String.concat "_" [setting_name; test_input_id] in
      let (msrs_file, ctl_file, correct_result) = List.assoc test_input_id test_inputs in
      Alcotest.test_case test_name `Slow (test_with_encoding msrs_file ctl_file test_setting)
    ) test_cases in
  let kripke_tests = List.map (fun test_case ->
      let (kripke_file, ctl_file, _, _) = test_case in 
      let extract_filename filename =
        let regex = Str.regexp ".*/\\([^/.]*\\)." in
        let _ = Str.string_match regex filename 0 in
        Str.matched_group 1 filename
      in
      let test_name = String.concat "_" ["kripke"; extract_filename kripke_file; extract_filename ctl_file] in
      Alcotest.test_case test_name `Slow (test_labeled_kripke test_case)
    ) kripke_test_cases in
  encoding_tests @ kripke_tests

let register_all_on_one_encoding_tests (module Enc: Encoding.Encoding_utils.Encoding) () =
    List.map (fun (test_input_id, (msrs_file, ctl_file, correct_result)) ->
      let test_name = String.concat "_" [test_input_id] in
      let msrs = Parser.Utils.read_msrs_from_file msrs_file in
      let property = Parser.Utils.read_ctl_from_file ctl_file in
      let params = Encoding.Encoding_params.determine_parameters msrs property in
      let params = (params.cap, params.tracked) in
      let test_setting = ((module Enc: Encoding.Encoding_utils.Encoding), params, 20, correct_result) in
      Alcotest.test_case test_name `Slow (test_with_encoding msrs_file ctl_file test_setting)
    ) test_inputs
