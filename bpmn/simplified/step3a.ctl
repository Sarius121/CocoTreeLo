FORALL p. (FORALL x. (AG (!Collect(p, x) || (EX EX EX EX Use(p, x) ))))
// works with:
// cap = []
// tracked = [
    [("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown "u1"); Int (Unknown "u2"); Int (Unknown "u3"); Int (Unknown "u4"); Int (Unknown "u5")]); ("CreditCard*", [Int (Var "x")])];
    [("TokPurchasingBUYSTART*", [Int (Unknown "u11"); Int (Unknown "u12"); Int (Unknown "u13"); Int (Unknown "u14"); Int (Unknown "u15")]); ("CreditCard*", [Int (Var "x")])];
    [("TokPurchasingBUYEND*", [Int (Unknown "u21"); Int (Unknown "u22"); Int (Unknown "u23"); Int (Unknown "u24"); Int (Unknown "u25")]); ("CreditCard*", [Int (Var "x")])];
    [("TokPurchasingCARDVALIDATESTART*", [Int (Unknown "u31"); Int (Unknown "u32"); Int (Unknown "u33"); Int (Unknown "u34"); Int (Unknown "u35")]); ("CreditCard*", [Int (Var "x")])];
]
// probably also works with cap for the tracked with only unknowns, but is much faster with unknowns