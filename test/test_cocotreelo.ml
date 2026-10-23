type test = string * (unit -> unit)
type register_fun = unit -> unit Alcotest.test_case list

let register_funs: (string * register_fun) list = [
  ("encoding_tests_combi", Test_encoding_combi.register_encoding_tests);
  ("annotation_tests", Test_annotation_process.register_annotation_tests);
  ("counterexample_tests", Test_counterexamples.register_tests);
  ("all_on_one_encoding", Test_annotation_process.register_all_on_one_encoding_tests (Config.all_on_one_encoding));
  ("parser_tests", Test_parser.register_tests);
  ("system_tests", Test_system.register_tests);
  ("bpmn_tests", Test_bpmn.register_tests)
]

let () =
  (* accumulate all tests *)
  let test_suite = List.map (fun (name, register_fun) -> 
      (name, register_fun ())
    ) register_funs
  in

  (* run tests *)
  let ret_code =
    try
      Alcotest.run ~and_exit:false "Cocotreelo" test_suite;
      0
    with Alcotest.Test_error ->
      1
  in
  Maude.remove_maude_input_file ();
  exit ret_code
