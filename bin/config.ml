open Cocotreelo

let usage_msg = "cocotreelo <program-file> <ctl-file>"

type config = {
  verbose: bool;
  output_files: bool;
  print_stats: bool;
  rounds: int;
  program_file: string;
  ctl_file: string;
  encoding: (module Encoding.Encoding_utils.Encoding);
  maude_path: string;
  output_frequency: int;
  max_cegar_cycles: int
}

let default_config = {
  verbose = false;
  output_files = false;
  print_stats = false;
  rounds = 0;
  program_file = "";
  ctl_file = "";
  encoding = Encoding.Encoding_utils.get_encoding "combi";
  maude_path = "extlib/custom-maude/maude";
  output_frequency = 0;
  max_cegar_cycles = 3;
}

let verbose = ref false
let output_files = ref false
let print_stats = ref false
let rounds = ref 20
let cegar_cycles = ref 1
let program_file = ref None
let ctl_file = ref None
let cur_arg = ref 0

let handle_args arg =
  cur_arg := !cur_arg + 1;
  match !cur_arg with
  | 1 -> program_file := Some arg
  | 2 -> ctl_file := Some arg
  | _ -> raise (Arg.Bad "Too many arguments")

let options =
  Arg.align
  [("-v", Arg.Set verbose, "\tOutput intermediate steps");
    ("-o", Arg.Set output_files, "\tWrite debugging graphs (only works in combination with -v)");
    ("-t", Arg.Set print_stats, "\tPrint running-time statistics");
    ("-r", Arg.Set_int rounds, "<i> \tRun the annotation process for at most i rounds per strongly connected component in the product structure");
    ("-c", Arg.Set_int cegar_cycles, "<i> \tRun the abstraction-refinement cycle for at most i times")]

let check_config () =
  if !cegar_cycles <= 0 then
    (Printf.eprintf "-c should be at least 1\n";
    Arg.usage options usage_msg;
    exit 1)
  else if !rounds <= 0 then
    (Printf.eprintf "-r should be at least 1\n";
    Arg.usage options usage_msg;
    exit 1)
  else ()

let construct_config () = match !program_file, !ctl_file with
  | Some program_file, Some ctl_file ->
    { default_config with
      verbose = !verbose;
      output_files = !output_files;
      rounds = !rounds;
      program_file = program_file;
      ctl_file = ctl_file;
      max_cegar_cycles = !cegar_cycles;
      print_stats = !print_stats
    }
  | _ ->
    Printf.eprintf "Expected two arguments.\n";
    Arg.usage options usage_msg;
    exit 1

let parse () = 
  Arg.parse options handle_args usage_msg;
  check_config ();
  construct_config ()
