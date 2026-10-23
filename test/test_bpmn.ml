open Cocotreelo
open Encoding.Encoding_params

(* 
  The bpmn test cases become more advanced and nearer to the full test from step to step.
  Tests that take more than a few seconds are marked with a time estimate.
*)
let bpmn_test_cases = [
  ("step0", ("bpmn/simplified/step0.spthy", "bpmn/simplified/step0.ctl", 1, true, 
    { cap=[("Step2", 1)]; tracked=[[("CreditCard*", [Int (Var "x")])]]; start_with_empty_state=true; hide_action_facts = true }));
  (* 15s *)
  ("step1a", ("bpmn/simplified/step1a.spthy", "bpmn/simplified/step1a.ctl", 1, true, 
    { cap=[("Step2", 1); ("Step3", 1)]; tracked=[[("CreditCard*", [Int (Var "x")])]]; start_with_empty_state=true; hide_action_facts = true }));
  ("step1b", ("bpmn/simplified/step1b.spthy", "bpmn/simplified/step1b.ctl", 1, true, 
    { cap=[("Step2", 1)]; tracked=[[("CreditCard*", [Int (Var "x"); Int (Unknown "u1")])]; [("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])]]; start_with_empty_state=true; hide_action_facts = true }));
  (* 1min *)
  ("step2", ("bpmn/simplified/step2.spthy", "bpmn/simplified/step2.ctl", 1, true, 
    { cap=[("Step2", 1); ("Step3", 1)]; tracked=[[("CreditCard*", [Int (Var "x"); Int (Unknown "u1")])]; [("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])]]; start_with_empty_state=true; hide_action_facts = true }));
  (* unknown min; from 3a on, the a steps are similar as the original system, but the CreditCard and Shipment facts do not share arguments with other facts *)
  ("step3a", ("bpmn/simplified/step3a.spthy", "bpmn/simplified/step3a.ctl", 1, true, 
    { cap=[]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));
  (* from 3b on, the b steps are less near to the original system, but the CreditCard and Shipment facts do share arguments with other facts *)
  ("step3b1", ("bpmn/simplified/step3b1.spthy", "bpmn/simplified/step3b1.ctl", 1, true,
    { cap=[]; tracked=[[("Step2*", [Int (Unknown "u1"); Int (Unknown "u2")]); ("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])]]; start_with_empty_state=true; hide_action_facts = true }));
  ("step3b2", ("bpmn/simplified/step3b2.spthy", "bpmn/simplified/step3b2.ctl", 1, true,
    { cap=[]; tracked=[
        [("Step2*", [Int (Unknown "u1"); Int (Unknown "u2")]); ("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])];
        [("Step3*", [Int (Unknown "u3"); Int (Unknown "u4")]); ("CreditCard*", [Int (Unknown "u4"); Int (Var "x")])];]; 
      start_with_empty_state=true; hide_action_facts = true }));
  (* unknown min, extension of 3a *)
  ("step4a1", ("bpmn/simplified/step4a.spthy", "bpmn/simplified/step4a_s2.ctl", 1, true,
    { cap=[("Writeccn2", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));
  (* unknown min *)
  ("step4a2", ("bpmn/simplified/step4a.spthy", "bpmn/simplified/step4a_s2_2.ctl", 1, true,
    { cap=[("Writeccn2", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));
  (* unknown min, extension of 4a2*)
  ("step5", ("bpmn/simplified/step5a.spthy", "bpmn/simplified/step5a_s2.ctl", 1, true,
    { cap=[("Writeccn2", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Var "x")])];
        
        [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x")])];
        [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));


  (** versions that almost match the original one *)

  (* same simplifications as credit_card_s2, but leading and trailing unneccessary rules are removed *)
  ("credit_card_focused_s2", ("bpmn/simplified/petshop_credit_card_focused.spthy", "bpmn/simplified/s2_leading.ctl", 1, true,
    { cap=[("WriteSimple", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Unknown "u5"); Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Unknown "u15"); Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Unknown "u25"); Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Unknown "u35"); Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));

  (* same simplifications as complete_s2, but shipment part is removed *)
  ("credit_card_s2", ("bpmn/simplified/petshop_credit_card.spthy", "bpmn/simplified/s2_leading.ctl", 1, true,
    { cap=[("WriteSimple", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Unknown "u5"); Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Unknown "u15"); Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Unknown "u25"); Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Unknown "u35"); Int (Var "x")])];];
      start_with_empty_state=false; hide_action_facts = true }));

  (* same simplifications as shipment_s2, but leading and trailing unneccessary rules are removed *)
  ("shipment_focused_s2", ("bpmn/simplified/petshop_shipment_focused.spthy", "bpmn/simplified/s2_leading.ctl", 1, true,
    { cap=[("WriteSimple", 1)]; tracked=[
        [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x"); Int (Unknown "u43")])];
        [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x"); Int (Unknown "u53")])];];
      start_with_empty_state=false; hide_action_facts = true }));

  (* 45s, same simplifications as complete_s2, but credit card part is removed *)
  ("shipment_s2", ("bpmn/simplified/petshop_shipment.spthy", "bpmn/simplified/s2_leading.ctl", 1, true,
    { cap=[("WriteSimple", 1)]; tracked=[
        [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x"); Int (Unknown "u43")])];
        [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x"); Int (Unknown "u53")])];];
      start_with_empty_state=false; hide_action_facts = true }));

  (* complete test, the petshop has been changed:
      - to satisfy the property (i.e. Collect(8, u) and Collect(8, pname) are removed)
      - (ccname, expmonth, expyear, n) is replaced by cc_data
      - the relevant Write(c, z, t, x) and Read(c, z, t, x) facts are replaced by WriteSimple(c, t, x) and ReadSimple(c, t, x)
  *)
  ("complete_s2", ("bpmn/simplified/petshop_complete.spthy", "bpmn/simplified/s2_leading.ctl", 1, true,
    { cap=[("WriteSimple", 1)]; tracked=[
        [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Unknown "u5"); Int (Var "x")])];
        [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Unknown "u15"); Int (Var "x")])];
        [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Unknown "u25"); Int (Var "x")])];
        [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Unknown "u35"); Int (Var "x")])];

        [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x"); Int (Unknown "u43")])];
        [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x"); Int (Unknown "u53")])];];
      start_with_empty_state=false; hide_action_facts = true }));

  (** s5 *)
  ("complete_s5", ("bpmn/simplified/petshop_complete.spthy", "bpmn/s5_leading.ctl", 1, false,
    { cap=[("Write", 1)]; tracked=[]; start_with_empty_state=false; hide_action_facts = true }));
]

let register_tests () =
  List.map (fun (test_input_id, (msrs_file, ctl_file, cycles, expected_result, manual_params)) ->
    let test_name = String.concat "_" [test_input_id] in
    let msrs = Logic.Parser.Utils.read_msrs_from_file msrs_file in
    let property = Logic.Parser.Utils.read_ctl_from_file ctl_file in
    Alcotest.test_case test_name `Slow (Test_system.system_test cycles 20 (msrs, property, expected_result) ~manual_params)
  ) bpmn_test_cases
