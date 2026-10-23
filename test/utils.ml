let assert_equals expected actual =
  Alcotest.(check string) "" expected actual

let assert_equals_poly expected actual to_string =
  if expected = actual then ()
  else
    (Alcotest.(check string) "" (to_string expected ^ ".") (to_string actual);
    failwith "assert_equals_poly failed, but the string representation is equal")

let assert_starts_with expected actual =
  let actual_prefix = String.sub actual 0 (String.length expected) in
  Alcotest.(check string) "" expected actual_prefix
