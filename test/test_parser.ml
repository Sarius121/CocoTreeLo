open Logic
open Parser.Utils

let test_ctl_parser () =
  let ctl = {| FORALL x. AG P(x)|} ^ "\n" in
  let expected = "\u{2200} x. A(P(x) W false)" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. AG !P(x) || EF Q(x) |} ^ "\n" in
  let expected = "\u{2200} x. (A(!P(x) W false) || E(true U Q(x)))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = " \u{2200} x. AG (!P(x) || EF Q(x)) \n" in
  let expected = "\u{2200} x. A((!P(x) || E(true U Q(x))) W false)" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. A P(x) U Q(x) |} ^ "\n" in
  let expected = "\u{2200} x. A(P(x) U Q(x))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. P(x) || Q(x) |} ^ "\n" in
  let expected = "\u{2200} x. (P(x) || Q(x))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. EXISTS y. P(x) || Q(x) |} ^ "\n" in
  let expected = "\u{2200} x. \u{2203} y. (P(x) || Q(x))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. P(x) || FORALL y. Q(x) && R(x) |} ^ "\n" in
  let expected = "\u{2200} x. (P(x) || \u{2200} y. (Q(x) && R(x)))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| FORALL x. P(x) && FORALL x. Q(x) && FORALL x. R(x) |} ^ "\n" in
  let expected = "\u{2200} x. (P(x) && \u{2200} x. (Q(x) && \u{2200} x. R(x)))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);
  
  let ctl = {| FORALL x. P(x) && Q(x) && FORALL x. R(x) |} ^ "\n" in
  let expected = "\u{2200} x. ((P(x) && Q(x)) && \u{2200} x. R(x))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  let ctl = {| A X AX P(x) && Q(x) |} ^ "\n" in
  let expected = "(AX AX P(x) && Q(x))" in
  let parsed = parse_ctl ctl in
  Alcotest.(check string) "ctl string not equal" expected (Ctl.to_string parsed);

  ()

let parser_test_cases = [
  Alcotest.test_case "test_ctl_parser" `Quick test_ctl_parser;
]

let register_tests () =
  parser_test_cases
