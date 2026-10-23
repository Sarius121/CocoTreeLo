FORALL p. (FORALL x. (AG (!Collect(p, x) || Use(p, x) || (Writeccn2(18, 17, x) && EX (E ( (FORALL y. !Writeccn2(18, 17, y)) U (Readccn(18, 17, x) && Use(p, x)) ))))))
// works with:
// cap = [("Writeccn2", 1)]
// tracked = [
    ("CreditCard*", [Int (Var "x")]);
    ("TokPurchasingENTERBANKDETAILEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYSTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingBUYEND*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
    ("TokPurchasingCARDVALIDATESTART*", [Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown); Int (Unknown)]);
]