open Logic.Arg_terms

let cap = [("WriteSimple", 1)]
    
let tracked = [
  [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Unknown "u5"); Int (Var "x")])];
  [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Unknown "u15"); Int (Var "x")])];
  [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Unknown "u25"); Int (Var "x")])];
  [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Unknown "u35"); Int (Var "x")])];
  
  [("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown "u41"); Int (Unknown "u42"); Int (Unknown "u43"); Int (Unknown "u44"); Int (Unknown "u45")]); ("Shipment*", [Int (Unknown "u46"); Int (Var "x"); Int (Unknown "u43")])];
  [("TokPurchasingSHIPPINGSTART*", [Int (Unknown "u51"); Int (Unknown "u52"); Int (Unknown "u53"); Int (Unknown "u54"); Int (Unknown "u55")]); ("Shipment*", [Int (Unknown "u56"); Int (Var "x"); Int (Unknown "u53")])];
]
      
let start_with_empty_state = false

let hide_action_facts = true
