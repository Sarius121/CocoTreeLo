open Utils
open Cocotreelo.Encoding.Maude_narrowing_combi
open Logic

(* not up to date anymore *)
let test_gen_kripke () =
  let msrs = Parser.Utils.parse_msrs "theory P
    begin
    rule Rule: [ ] --> [ P(x) ]
    end" in
  let (kripke, _, _) = gen_kripke msrs Config.maude_path (Ctl.FACT ("P", [Arg_terms.(Int (Var "x"))])) {cap=["P", 1]; tracked=[[("P*", [Arg_terms.(Int (Var "x"))])]]; start_with_empty_state = true; hide_action_facts = false} in
  assert_equals {|digraph g {
"[] where !P*_x" -> "[P(v0)] where !P*_x" [label="Rule: true->v0:=?|(and (= false false))->"]
"[P(v0)] where !P*_x" -> "[P(v0), P*] where !P*_x" [label="Rule: (exists ((r@1 Int)) (and (= v0 r@1)))->v1:=v0,v0:=?|(let ((a!1 (= false (or (and (= x v1))))))
  (and a!1))->P*_x:=(or (and (= x v1)))"]
"[P(v0)] where !P*_x" -> "[P(v0), P*] where !P*_x" [label="Rule: (exists ((r@1 Int)) (and (= v0 r@1)))->v1:=?,v0:=v0|(let ((a!1 (= false (or (and (= x v1))))))
  (and a!1))->P*_x:=(or (and (= x v1)))"]
"[P(v0)] where !P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@1 Int)) (and (= v0 r@1)))->v1:=v0,v0:=?|(let ((a!1 (= true (or (and (= x v1))))))
  (and a!1))->P*_x:=(or (and (= x v1)))"]
"[P(v0)] where !P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@1 Int)) (and (= v0 r@1)))->v1:=?,v0:=v0|(let ((a!1 (= true (or (and (= x v1))))))
  (and a!1))->P*_x:=(or (and (= x v1)))"]
"[P(v0), P*] where !P*_x" -> "[P(v0), P*] where !P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=v0,v0:=?|(let ((a!1 (= false (or (and (= x v1)) (and false true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
"[P(v0), P*] where !P*_x" -> "[P(v0), P*] where !P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=?,v0:=v0|(let ((a!1 (= false (or (and (= x v1)) (and false true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
"[P(v0), P*] where !P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=v0,v0:=?|(let ((a!1 (= true (or (and (= x v1)) (and false true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
"[P(v0), P*] where !P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=?,v0:=v0|(let ((a!1 (= true (or (and (= x v1)) (and false true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
"[P(v0), P*] where P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=v0,v0:=?|(let ((a!1 (= true (or (and (= x v1)) (and true true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
"[P(v0), P*] where P*_x" -> "[P(v0), P*] where P*_x" [label="Rule: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=?,v0:=v0|(let ((a!1 (= true (or (and (= x v1)) (and true true)))))
  (and a!1))->P*_x:=(or (and (= x v1)) (and P*_x true))"]
}|} (Kripke.draw kripke)

(* not up to date anymore *)
let test_gen_kripke2 () =
  let msrs = Parser.Utils.parse_msrs "theory P
    begin
    rule Rule1: [ ] --> [ P(x) ]
    rule Rule2: [ P(x) ] --> [ Q(x) ]
    end" in
  let property = (Ctl.OR (Ctl.FACT ("P", [Arg_terms.(Int (Var "x"))]), Ctl.FACT ("Q", [Arg_terms.(Int (Var "x"))]))) in
  let (kripke, _, _) = gen_kripke msrs Config.maude_path property {cap=[("P", 1); ("Q", 1)]; tracked=[]; start_with_empty_state = true; hide_action_facts = false} in
  assert_starts_with {|digraph g {
"[] where " -> "[P(v0)] where " [label="Rule1: true->v0:=?|and->"]
"[Q(v0)] where " -> "[P(v0), Q(v1)] where " [label="Rule1: (exists ((r@1 Int)) (and (= v0 r@1)))->v1:=v0,v0:=?|and->"]
"[Q(v0), Q*] where " -> "[P(v0), Q(v1), Q*] where " [label="Rule1: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=v0,v0:=?|and->Q*_x:=(or or (and Q*_x true))"]
"[P*, Q(v0)] where " -> "[P*, Q(v0), Q*] where " [label="Rule2: (exists ((r@3 Int)) (and (= v0 r@3)))->v1:=v0,v0:=?|and->P*_x:=(let ((a!1 (not (or (and (= x v0))))) (a!2 (and (or (and (= x v0))) Unknown0)))
  (or or (and P*_x (or a!1 a!2)))),Q*_x:=(or (and (= x v1)))"]
"[P*, Q(v0)] where " -> "[P*, Q(v0), Q*] where " [label="Rule2: (exists ((r@3 Int)) (and (= v0 r@3)))->v1:=?,v0:=v0|and->P*_x:=(let ((a!1 (not (or (and (= x v1))))) (a!2 (and (or (and (= x v1))) Unknown0)))
  (or or (and P*_x (or a!1 a!2)))),Q*_x:=(or (and (= x v1)))"]
"[P*, Q(v0)] where " -> "[P(v0), P*, Q(v1)] where " [label="Rule1: (exists ((r@2 Int)) (and (= v0 r@2)))->v1:=v0,v0:=?|and->P*_x:=(or or (and P*_x true))"]
"[P*, Q(v0), Q*] where " -> "[P*, Q(v0), Q*] where " [label="Rule2: (exists ((r@4 Int)) (and (= v0 r@4)))->v1:=v0,v0:=?|and->P*_x:=(let ((a!1 (not (or (and (= x v0))))) (a!2 (and (or (and (= x v0))) Unknown0)))
  (or or (and P*_x (or a!1 a!2)))),Q*_x:=(or (and (= x v1)) (and Q*_x true))"]
"[P*, Q(v0), Q*] where " -> "[P*, Q(v0), Q*] where " [label="Rule2: (exists ((r@4 Int)) (and (= v0 r@4)))->v1:=?,v0:=v0|and->P*_x:=(let ((a!1 (not (or (and (= x v1))))) (a!2 (and (or (and (= x v1))) Unknown0)))
  (or or (and P*_x (or a!1 a!2)))),Q*_x:=(or (and (= x v1)) (and Q*_x true))"]
"[P*, Q(v0), Q*] where " -> "[P(v0), P*, Q(v1), Q*] where " [label="Rule1: (exists ((r@3 Int)) (and (= v0 r@3)))->v1:=v0,v0:=?|and->P*_x:=(or or (and P*_x true)),Q*_x:=(or or (and Q*_x true))"]
"[P(v0)] where " -> "[Q(v0)] where " [label="Rule2: (exists ((r@1 Int)) (and (= v0 r@1)))->v0:=v0|and->"]|} (Kripke.draw kripke)

let test_gen_transition_conditions_and_assignments () =
  let open Substitution in
  let open Arg_terms in
  let open Multiset_rewrite_system in
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let succ_constraints = [] in
  let tracked = [] in
  (* [P(v0)]->[Q(v0)] via rule2 *)
  let rho_S = { arg_subst = [("v0", Int (Var "@1"))]; ms_subst = [] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1"))]; ms_subst = [("PM", Const []); ("QM", Const [])] } in
  let nu = { arg_subst = [("@1", Int (Var "v0"))]; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [] } in
  let constraints = [] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[@1->v0]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(and (= v0 @1) and and)" (Sat.to_string (Sat.mk_and b_post_may));
  Alcotest.(check string) "b_post_must" "(and (= v0 @1) true and)" (Sat.to_string (Sat.mk_and b_post_must));
  Alcotest.(check string) "a_post" "[Track*_P*_x->false, v0->@1]" (Substitution.to_string a_post.Kripke.regular);

  (* [P*]->[Q*] via rule2 *)
  let rho_S = { arg_subst = []; ms_subst = [("P*", Union (Var "@1", Const [("P",[Int (Var "@2")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@2"))]; ms_subst = [("PM", Var "@1"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Var "@1"); ("Q*", Const [("Q",[Int (Var "@2")])])] } in
  let constraints = [] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@2" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "true" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->(and (or (not (= x @2)) (and (= x @2) CountGt1_Track*_P*_x)) Track*_P*_x), P*->(P* \\ [P(@2)]), Q*->[Q(@2)]]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));

  (* [P*]->[P*] via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [("P*", Union (Var "@1", Const [("P",[Int (Var "@2")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@2")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@1"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@1", Const [("P",[Int (Var "@3")])]))] } in
  let constraints = [] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @2" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "true" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->(let ((a!1 (and (or (not (= x @2)) (and (= x @2) CountGt1_Track*_P*_x))\n                Track*_P*_x)))\n  (or (= x @3) a!1)), P*->((P* \\ [P(@2)]) u [P(@3)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));

  (* [P(v0),P(v1)]->[] via rule [P(x),P(x)]->[] *)
  let rho_S = { arg_subst = [("v0", Int (Var "@1")); ("v1", Int (Var "@1"))]; ms_subst = [] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1"))]; ms_subst = [("PM", Const []); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [] } in
  let constraints = [] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[@1->v0, @1->v1]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(and (= v0 @1) (= v1 @1) and and)" (Sat.to_string (Sat.mk_and b_post_may));
  Alcotest.(check string) "b_post_must" "(and (= v0 @1) (= v1 @1) true and)" (Sat.to_string (Sat.mk_and b_post_must));
  Alcotest.(check string) "a_post" "[Track*_P*_x->false]" (Substitution.to_string a_post.Kripke.regular);

  (* [P(v0),P*]->[P*] via rule [P(x),P(x)]->[] *)
  let rho_S = { arg_subst = [("v0", Int (Var "@1"))]; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Var "@2")] } in
  let constraints = [] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[@1->v0]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(= v0 @1)" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->(and (or (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x)) Track*_P*_x), P*->(P* \\ [P(@1)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));

  (* [P(v0),P*] where P*_x->[P*] where P*_x via rule [P(x),P(x)]->[] *)
  let rho_S = { arg_subst = [("v0", Int (Var "@1"))]; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Var "@2")] } in
  let tracked = [[("P*", [Int (Var "x")])]] in
  let constraints = [([("P*", [Int (Var "x")])], true)] in
  let succ_constraints = [([("P*", [Int (Var "x")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[@1->v0]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(and (= v0 @1) (or (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "(and (= v0 @1) (= x @1) (or (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->true, P*->(P* \\ [P(@1)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));

  (* [P(v0),P*] where !P*_x->[P*] where !P*_x via rule [P(x),P(x)]->[] *)
  let rho_S = { arg_subst = [("v0", Int (Var "@1"))]; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Var "@2")] } in
  let tracked = [[("P*", [Int (Var "x")])]] in
  let constraints = [([("P*", [Int (Var "x")])], false)] in
  let succ_constraints = [([("P*", [Int (Var "x")])], false)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[@1->v0]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(and (= v0 @1) (not (= @1 x)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->false, P*->(P* \\ [P(@1)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));

  (* [P*] where P*_x->[P*] where P*_x via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@2", Const [("P", [Int (Var "@3")])]))] } in
  let tracked = [[("P*", [Int (Var "x")])]] in
  let constraints = [([("P*", [Int (Var "x")])], true)] in
  let succ_constraints = [([("P*", [Int (Var "x")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @1" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "b_post_may" "(or (= x @3) (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "(and (= x @1) (or (= x @3) (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x->true, P*->((P* \\ [P(@1)]) u [P(@3)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));
  
  let track_vars = [[("P*", [Int (Unknown "u")])]] in
  (* [P*] where P*_u->[P*] where !P*_u via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@2", Const [("P", [Int (Var "@3")])]))] } in
  let tracked = [[("P*", [Int (Unknown "u")])]] in
  let constraints = [([("P*", [Int (Unknown "u")])], true)] in
  let succ_constraints = [([("P*", [Int (Unknown "u")])], false)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @1" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "a_unknowns" "u, CountGt1_Track*_P*_u" (String.concat ", " a.Kripke.unknowns);
  Alcotest.(check string) "b_post_may" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "false" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_u->false, P*->((P* \\ [P(@1)]) u [P(@3)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));
  
  (* [P*] where P*_!->[P*] where P*_! via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])]))] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@2"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@2", Const [("P", [Int (Var "@3")])]))] } in
  let tracked = [[("P*", [Int (Unknown "u")])]] in
  let constraints = [([("P*", [Int (Unknown "u")])], true)] in
  let succ_constraints = [([("P*", [Int (Unknown "u")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @1" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check bool) "b_post_may_sat" true (Sat.is_eq (Sat.mk_and b_post_may) (Sat.mk_bool true));
  Alcotest.(check bool) "b_post_must_sat" true (Sat.is_eq (Sat.mk_and b_post_must) (Sat.mk_eq (Sat.mk_var "u") (Sat.mk_var "@1")));
  (* Alcotest.(check string) "b_post_may" "true" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may))); *)
  (* Alcotest.(check string) "b_post_must" "(= u @1)" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must))); *)
  Alcotest.(check string) "a_post" "[Track*_P*_u->true, P*->((P* \\ [P(@1)]) u [P(@3)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));
  

  let track_vars = [[("P*", [Int (Var "x"); Int (Unknown "u")])]] in
  (* [P*] where P*_x_!->[P*] where P*_x_! via rule [P(x1,x2)]->[P(y1,y2)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@5", Const [("P", [Int (Var "@1"); Int (Var "@2")])]))] } in
  let rho_R = { arg_subst = [("x1", Int (Var "@1")); ("x2", Int (Var "@2")); ("y1", Int (Var "@3")); ("y2", Int (Var "@4"))]; ms_subst = [("PM", Var "@5"); ("QM", Const [])] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@5", Const [("P", [Int (Var "@3"); Int (Var "@4")])]))] } in
  let tracked = [[("P*", [Int (Var "x"); Int (Unknown "u")])]] in
  let constraints = [([("P*", [Int (Var "x"); Int (Unknown "u")])], true)] in
  let succ_constraints = [([("P*", [Int (Var "x"); Int (Unknown "u")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@4, @3, @2, @1" (String.concat ", " a.Kripke.nondet);
  (* Alcotest.(check string) "b_post_may" "(or (= x @3) (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x_!))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may))); *)
  (* Alcotest.(check string) "b_post_must" "(and (= x @1)\n     (= u_1_Track*_P*_x_! @2)\n     (or (= x @3) (not (= x @1)) (and (= x @1) CountGt1_Track*_P*_x_!)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must))); *)
  Alcotest.(check string) "a_post" "[Track*_P*_x_u->true, P*->((P* \\ [P(@1, @2)]) u [P(@3, @4)])]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));
  ()

let test_gen_transition_conditions_and_assignments_multi_constraints () =
  let open Substitution in
  let open Arg_terms in

  let track_vars = [[("P*", [Int (Var "x")]); ("Q*", [Int (Var "y")])]] in
  (* [P*, Q*] where [P*_x,Q*_y]->[P*, Q*] where [P*_x,Q*_y] via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])])); ("Q*", Var "@4")] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@2"); ("QM", Var "@4")] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@2", Const [("P", [Int (Var "@3")])])); ("Q*", Var "@4")] } in
  let tracked = [[("P*", [Int (Var "x")]); ("Q*", [Int (Var "y")])]] in
  let constraints = [([("P*", [Int (Var "x")]); ("Q*", [Int (Var "y")])], true)] in
  let succ_constraints = [([("P*", [Int (Var "x")]); ("Q*", [Int (Var "y")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @1" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "a_unknowns" "" (String.concat ", " a.Kripke.unknowns);
  Alcotest.(check string) "b_post_may" "(or (= x @3) (not (= x @1)) (SomewhereElse_0_Track*_P*_x_Q*_y @3 @1))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "(and (= x @1)\n     (or (= x @3) (not (= x @1)) (SomewhereElse_0_Track*_P*_x_Q*_y @3 @1)))" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_x_Q*_y->true, P*->((P* \\ [P(@1)]) u [P(@3)]), Q*->Q*]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular));
  
  let track_vars = [[("P*", [Int (Unknown "u")]); ("Q*", [Int (Unknown "u"); Int (Var "y")])]] in
  (* [P*, Q*] where [P*_u,Q*_u_y]->[P*, Q*] where [P*_u,Q*_u_y] via rule [P(x)]->[P(y)] *)
  let rho_S = { arg_subst = []; ms_subst = [ ("P*", Union (Var "@2", Const [("P", [Int (Var "@1")])])); ("Q*", Var "@4")] } in
  let rho_R = { arg_subst = [("x", Int (Var "@1")); ("y", Int (Var "@3"))]; ms_subst = [("PM", Var "@2"); ("QM", Var "@4")] } in
  let nu = { arg_subst = []; ms_subst = [] } in
  let nu_star = { arg_subst = []; ms_subst = [("P*", Union (Var "@2", Const [("P", [Int (Var "@3")])])); ("Q*", Var "@4")] } in
  let tracked = [[("P*", [Int (Unknown "u")]); ("Q*", [Int (Unknown "u"); Int (Var "y")])]] in
  let constraints = [([("P*", [Int (Unknown "u")]); ("Q*", [Int (Unknown "u"); Int (Var "y")])], true)] in
  let succ_constraints = [([("P*", [Int (Unknown "u")]); ("Q*", [Int (Unknown "u"); Int (Var "y")])], true)] in
  let (b, a, (b_post_may, b_post_must), a_post) = (gen_transition_conditions_and_assignments rho_R rho_S nu nu_star track_vars tracked constraints 0) succ_constraints in
  Alcotest.(check string) "b" "(and true)" (Sat.to_string (Sat.mk_and b));
  Alcotest.(check string) "a" "[]" (Substitution.to_string a.Kripke.regular);
  Alcotest.(check string) "a_nondet" "@3, @1" (String.concat ", " a.Kripke.nondet);
  Alcotest.(check string) "a_unknowns" "u" (String.concat ", " a.Kripke.unknowns);
  Alcotest.(check string) "b_post_may" "true" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_may)));
  Alcotest.(check string) "b_post_must" "(= u @1)" (Sat.to_string (Sat.simplify (Sat.mk_and b_post_must)));
  Alcotest.(check string) "a_post" "[Track*_P*_u_Q*_u_y->true, P*->((P* \\ [P(@1)]) u [P(@3)]), Q*->Q*]" (Substitution.to_string (Substitution.simplify a_post.Kripke.regular))
  
let test_track_var_assignments () =
  let open Substitution in
  let open Arg_terms in
  let open Multiset_rewrite_system in
  
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Const [])] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x := false" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string value));
  
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Const [("P", [Int (Const 5)])])] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x := (= x 5)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string value));
  
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Const [("P", [Int (Const 5)])])] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x := (= x 5)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string value));
  
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Union (Var "P*", Const [("P", [Int (Const 5)])]))] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x := (or (= x 5) Track*_P*_x)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string value));
  
  let track_vars = [[("P*", [Int (Var "x")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Union (Minus (Var "P*", Const [("P", [Int (Const 6)])]), Const [("P", [Int (Const 5)])]))] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x := (let ((a!1 (and (or (not (= x 6)) (and (= x 6) CountGt1_Track*_P*_x))\n                Track*_P*_x)))\n  (or (= x 5) a!1))" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  
  let track_vars = [[("P*", [Int (Var "x"); Int (Unknown "u")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Union (Minus (Var "P*", Const [("P", [Int (Const 6); Int (Const 7)])]), Const [("P", [Int (Const 5); Int (Const 4)])]))] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_x_u := (let ((a!1 (or (not (and (= x 6) (= u 7)))\n               (and (= x 6) (= u 7) CountGt1_Track*_P*_x_u))))\n  (or (= x 5) (and a!1 Track*_P*_x_u) SomewhereElse_0_Track*_P*_x_u))" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  
  let track_vars = [[("P*", [Int (Unknown "u1")]); ("Q*", [Int (Unknown "u1")])]; [("P*", [Int (Unknown "u2")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Union (Minus (Var "P*", Const [("P", [Int (Const 6)])]), Const [("P", [Int (Const 5)])])); ("Q*", Var "Q*")] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_u1_Q*_u1 := (or (and (not (= u1 6)) Track*_P*_u1_Q*_u1)\n    SomewhereElse_0_Track*_P*_u1_Q*_u1\n    Track*_P*_u1_Q*_u1)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 1 in
  Alcotest.(check string) "assignment" "Track*_P*_u2 := true" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  
  let track_vars = [[("P*", [Int (Unknown "u1")]); ("Q*", [Int (Unknown "u1")])]; [("P*", [Int (Unknown "u2")])]; [("Q*", [Int (Unknown "u3")])]] in
  let star_var_assignment = { arg_subst = []; ms_subst = [("P*", Union (Minus (Var "P*", Const [("P", [Int (Const 6)])]), Const [("P", [Int (Const 5)])])); ("Q*", Var "Q*")] } in
  let track_var_assignment = gen_track_var_assignments track_vars star_var_assignment 0 [] in
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 0 in
  Alcotest.(check string) "assignment" "Track*_P*_u1_Q*_u1 := (or (and (not (= u1 6)) Track*_P*_u1_Q*_u1)\n    Track*_Q*_u3\n    SomewhereElse_0_Track*_P*_u1_Q*_u1\n    Track*_P*_u1_Q*_u1)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 1 in
  Alcotest.(check string) "assignment" "Track*_P*_u2 := true" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  let (track_var, value, new_unknowns) = List.nth track_var_assignment 2 in
  Alcotest.(check string) "assignment" "Track*_Q*_u3 := (or Track*_Q*_u3 Track*_P*_u1_Q*_u1)" (Printf.sprintf "%s := %s" (track_var_to_string track_var) (Sat.to_string (Sat.simplify value)));
  ()
  
let encoding_test_cases = [
  (* Alcotest.test_case "gen_kripke" `Quick test_gen_kripke; *)
  (* Alcotest.test_case "gen_kripke2" `Quick test_gen_kripke2; *)
  Alcotest.test_case "test_gen_transition_conditions_and_assignments" `Quick test_gen_transition_conditions_and_assignments;
  Alcotest.test_case "test_gen_transition_conditions_and_assignments_multi_constraints" `Quick test_gen_transition_conditions_and_assignments_multi_constraints;
  Alcotest.test_case "test_track_var_assignments" `Quick test_track_var_assignments;
]

let register_encoding_tests () =
  encoding_test_cases
