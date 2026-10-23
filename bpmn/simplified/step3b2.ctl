FORALL p. (FORALL x. (AG (!Collect(p, x) || (EX EX Use(p, x) ))))
// works with:
// cap = [ ]
// tracked = [
    [("Step2*", [Int (Unknown "u1"); Int (Unknown "u2")]); ("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])];
    [("Step3*", [Int (Unknown "u3"); Int (Unknown "u4")]); ("CreditCard*", [Int (Unknown "u4"); Int (Var "x")])];
]