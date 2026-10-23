open Logic.Arg_terms

let cap = [("WriteSimple", 1)]
    
let tracked = [
  [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x"); Int (Unknown "u43")])];
  [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x"); Int (Unknown "u53")])];
]
      
let start_with_empty_state = false

let hide_action_facts = true
