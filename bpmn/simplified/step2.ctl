FORALL x. AG (!Collect(x) || EX EX Use(x))
// works with:
// cap = [("Step2", 1); ("Step3", 1)]
// tracked = [
//     ("CreditCard*", [Int (Var "x"), Int (Unknown)]);
//     ("CreditCard*", [Int (Unknown), Int (Var "x")])
// ]