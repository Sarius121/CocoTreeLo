FORALL x. AG (!Collect(x) || EX Use(x))
// works with:
// cap = [("Step2", 1)]
// tracked = [
//     [[("CreditCard*", [Int (Var "x"); Int (Unknown "u1")])]; 
//      [("CreditCard*", [Int (Unknown "u2"); Int (Var "x")])]]
// ]