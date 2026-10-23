FORALL p. (FORALL x. (AG (!Collect(p, x) || Use(p, x) || (EXISTS z. (EXISTS t. Writeccn2(z, t, x) && EX (E ( (FORALL y. !Writeccn2(z, t, y)) U (Readccn(z, t, x) && Use(p, x)) )))))))
// works with:
// cap = [("Writeccn2", 1)]
// tracked = [
    ("CreditCard*", [Int (Var "x")]);
    ("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYSTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingCARDVALIDATESTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
]