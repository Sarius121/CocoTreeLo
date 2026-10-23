let file_suffix = Printf.sprintf "%.0f" (Unix.time ())

let parse_maude_output output =
  try
    let lexbuf = Lexing.from_string output in
    Some (Parser.main Lexer.token lexbuf)
  with ex ->
    None

let parse_maude_output_s output =
  try
    let lexbuf = Lexing.from_string output in
    Parser.main Lexer.token lexbuf
  with ex ->
    failwith "Error parsing the maude output."

let run_maude_legacy maude_path input =
  (* let () = Printf.printf "%s\n" input in *)
  let input = {|
    set trace on .
    set trace rl on .|}
    ^ input in
  let out_channel = open_out "maude_in.maude" in
  let () =
    Printf.fprintf out_channel "%s\n" input;
    close_out out_channel in
  let cmd = maude_path ^ " maude_in.maude -no-banner" in
  let in_channel = Unix.open_process_in cmd in
  let output = In_channel.input_all in_channel in
  let status = Unix.close_process_in in_channel in
  let () = if not (status = Unix.WEXITED 0) then failwith "Running maude failed.\n" else () in
  output

let run_maude_cmd cmd =
  let (in_channel, out_channel, err_channel) = Unix.open_process_full cmd [||] in
  (* maude reads commands from stdin if it cannot process its input file, so close stdin to make it exit instead of waiting forever *)
  let () = close_out out_channel in
  let output = parse_maude_output (In_channel.input_all in_channel) in
  let err = In_channel.input_all err_channel in
  let status = Unix.close_process_full (in_channel, out_channel, err_channel) in
  match output with
  | None ->
    if err = "" then failwith "Parsing maude output failed for unknown reasons.\n"
    else failwith ("Maude error:\n" ^ err)
  | Some output ->
    let () = if not (status = Unix.WEXITED 0) then failwith ("Running maude failed, but we still got valid output.\n" ^ err) else () in
    output

let run_maude maude_path input =
  (* let () = Printf.printf "%s\n" input in *)
  (* let () = Printf.printf "Run maude\n"; flush stdout in *)
  let input = {|
    set show command off .
    set show timing off .
    set print with parentheses on .
    set trace on .
    set trace rl on .|}
    ^ input in
  let out_channel = open_out ("maude_in_" ^ file_suffix ^ ".maude") in
  let () =
    Printf.fprintf out_channel "%s\n" input;
    close_out out_channel in
  run_maude_cmd (maude_path ^ " maude_in_" ^ file_suffix ^ ".maude -no-banner -no-tecla -no-wrap -batch")

let remove_maude_input_file () =
  let file = "maude_in_" ^ file_suffix ^ ".maude" in
  Sys.remove file

let run_maude_test maude_path =
  run_maude_cmd (maude_path ^ " maude_in.maude -no-banner")

let%expect_test "parse_complete" =
  (* let _ = Parsing.set_trace true in *)
  let output = "*********** narrowing step
rl [Rule1] : (< PM:PFact ; QM:QFact ; RM:RFact >) => (< (PM:PFact, (P x:Int)) ;
    QM:QFact ; RM:RFact >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> @1:PFact
QM:QFact --> @2:QFact
RM:RFact --> @3:RFact
x:Int --> @4:Int
Subject variable bindings:
#1:PFact --> @1:PFact
#2:QFact --> @2:QFact
#3:RFact --> @3:RFact
(< #1:PFact ; #2:QFact ; #3:RFact >)
--->
(< (@1:PFact, (P @4:Int)) ; @2:QFact ; @3:RFact >)

Solution 1
rewrites: 1
state: (< (@1:PFact, (P @4:Int)) ; @2:QFact ; @3:RFact >)
accumulated substitution:
PM:PFact --> @1:PFact
QM:QFact --> @2:QFact
RM:RFact --> @3:RFact
variant unifier:
S:State --> (< (%1:PFact, (P %2:Int)) ; %3:QFact ; %4:RFact >)
@1:PFact --> %1:PFact
@4:Int --> %2:Int
@2:QFact --> %3:QFact
@3:RFact --> %4:RFact
*********** narrowing step
rl [Rule2] : (< (PM:PFact, (P x:Int)) ; QM:QFact ; RM:RFact >) => (< PM:PFact ;
    (QM:QFact, (Q x:Int)) ; RM:RFact >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> @1:PFact
x:Int --> @2:Int
QM:QFact --> @3:QFact
RM:RFact --> @4:RFact
Subject variable bindings:
#1:PFact --> (@1:PFact, (P @2:Int))
#2:QFact --> @3:QFact
#3:RFact --> @4:RFact
(< #1:PFact ; #2:QFact ; #3:RFact >)
--->
(< @1:PFact ; (@3:QFact, (Q @2:Int)) ; @4:RFact >)

Solution 2
rewrites: 2
state: (< @1:PFact ; (@3:QFact, (Q @2:Int)) ; @4:RFact >)
accumulated substitution:
PM:PFact --> (@1:PFact, (P @2:Int))
QM:QFact --> @3:QFact
RM:RFact --> @4:RFact
variant unifier:
S:State --> (< %1:PFact ; (%2:QFact, (Q %3:Int)) ; %4:RFact >)
@1:PFact --> %1:PFact
@3:QFact --> %2:QFact
@2:Int --> %3:Int
@4:RFact --> %4:RFact
*********** narrowing step
rl [Rule2] : (< PM:PFact ; (QM:QFact, (Q x:Int)) ; RM:RFact >) => (< PM:PFact ;
    QM:QFact ; (RM:RFact, (R x:Int)) >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> @3:PFact
QM:QFact --> @1:QFact
x:Int --> @2:Int
RM:RFact --> @4:RFact
Subject variable bindings:
#1:PFact --> @3:PFact
#2:QFact --> (@1:QFact, (Q @2:Int))
#3:RFact --> @4:RFact
(< #1:PFact ; #2:QFact ; #3:RFact >)
--->
(< @3:PFact ; @1:QFact ; (@4:RFact, (R @2:Int)) >)

Solution 3
rewrites: 3
state: (< @3:PFact ; @1:QFact ; (@4:RFact, (R @2:Int)) >)
accumulated substitution:
PM:PFact --> @3:PFact
QM:QFact --> (@1:QFact, (Q @2:Int))
RM:RFact --> @4:RFact
variant unifier:
S:State --> (< %1:PFact ; %2:QFact ; (%3:RFact, (R %4:Int)) >)
@3:PFact --> %1:PFact
@1:QFact --> %2:QFact
@4:RFact --> %3:RFact
@2:Int --> %4:Int

No more solutions.
rewrites: 3
Bye.
" in
  let solutions = parse_maude_output_s output in
  let (state, state_subst, rule_subst, rule) = List.nth solutions 0 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: (@1 u [P(@4)]); Q: @2; R: @3 | [P*->@1, Q*->@2, R*->@3] | [x->@4, P*->@1, Q*->@2, R*->@3] | Rule1 |}];
  let (state, state_subst, rule_subst, rule) = List.nth solutions 1 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: @1; Q: (@3 u [Q(@2)]); R: @4 | [P*->(@1 u [P(@2)]), Q*->@3, R*->@4] | [x->@2, P*->@1, Q*->@3, R*->@4] | Rule2 |}];
  let (state, state_subst, rule_subst, rule) = List.nth solutions 2 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: @3; Q: @1; R: (@4 u [R(@2)]) | [P*->@3, Q*->(@1 u [Q(@2)]), R*->@4] | [x->@2, P*->@3, Q*->@1, R*->@4] | Rule2 |}]


let%expect_test "parse_with_no" =
  (* let _ = Parsing.set_trace true in *)
  let output = "*********** narrowing step
rl [Rule1] : (< PM:PFact ; QM:QFact >) => (< (PM:PFact, (P x:Int)) ; QM:QFact >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> noP
QM:QFact --> noQ
x:Int --> @1:Int
Subject variable bindings:
empty substitution
(< noP ; noQ >)
--->
(< (noP, (P @1:Int)) ; noQ >)

Solution 1
rewrites: 1
state: (< (P @1:Int) ; noQ >)
accumulated substitution:
variant unifier:
S:State --> (< (P %1:Int) ; noQ >)
@1:Int --> %1:Int

No more solutions.
rewrites: 1
Bye.
" in
  let solutions = parse_maude_output_s output in
  let (state, state_subst, rule_subst, rule) = List.nth solutions 0 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: [P(@1)]; Q: [] | [] | [x->@1, P*->[], Q*->[]] | Rule1 |}]

let%expect_test "parse_with_cap1" =
  (* let _ = Parsing.set_trace true in *)
  let output = "*********** narrowing step
rl [Rule1] : (< PM:PFact ; QM:QFact >) => (< (PM:PFact, (P x:Int)) ; QM:QFact >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> (P @1:Int)
QM:QFact --> noQ
x:Int --> @2:Int
Subject variable bindings:
#1:Int --> @1:Int
(< (P #1:Int) ; noQ >)
--->
(< ((P @1:Int), (P @2:Int)) ; noQ >)

Solution 1
rewrites: 1
state: (< ((P @1:Int), (P @2:Int)) ; noQ >)
accumulated substitution:
v0:Int --> @1:Int
variant unifier:
S:State --> (< ((P %1:Int), (P %2:Int)) ; noQ >)
@1:Int --> %1:Int
@2:Int --> %2:Int
*********** narrowing step
rl [Rule2] : (< (PM:PFact, (P 5)) ; QM:QFact >) => (< PM:PFact ; (QM:QFact, (Q 5)) >) [nonexec narrowing] .
Rule variable bindings:
PM:PFact --> noP
QM:QFact --> noQ
Subject variable bindings:
#1:Int --> 5
(< (P #1:Int) ; noQ >)
--->
(< noP ; (noQ, (Q 5)) >)

Solution 2
rewrites: 2
state: (< noP ; (Q 5) >)
accumulated substitution:
v0:Int --> 5
variant unifier:
S:State --> (< noP ; (Q 5) >)

No more solutions.
rewrites: 2
Bye.
" in
  let solutions = parse_maude_output_s output in
  let (state, state_subst, rule_subst, rule) = List.nth solutions 0 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: [P(@1), P(@2)]; Q: [] | [v0->@1] | [x->@2, P*->[P(@1)], Q*->[]] | Rule1 |}];
  let (state, state_subst, rule_subst, rule) = List.nth solutions 1 in
  Printf.printf "%s | %s | %s | %s" (String.concat "; " (List.map (fun (fact, term) -> fact ^ ": " ^ Logic.Multiset_rewrite_system.term_to_string term) state))
      (Logic.Substitution.to_string state_subst) (Logic.Substitution.to_string rule_subst) rule;
  [%expect {| P: []; Q: [Q(5)] | [v0->5] | [P*->[], Q*->[]] | Rule2 |}]
