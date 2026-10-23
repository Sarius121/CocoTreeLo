FORALL p. (FORALL x. (AG (!Collect(p, x) || Use(p, x) || (EXISTS z. (EXISTS t. Writesimple(z, t, x) && EX (E ( (FORALL y. !Writesimple(z, t, y)) U (Readsimple(z, t, x) && Use(p, x)) )))))))
// works with:
// cap = [("Writesimple", 1)]
// tracked = [
    ("CreditCard*", [Int (Var "x")]);
    ("Shipment*", [Int (Unknown); Int (Var "x")]);
    ("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYSTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingCARDVALIDATESTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingENTERSHIPPINGADDRESSEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingSHIPPINGSTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
]