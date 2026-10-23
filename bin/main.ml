open Cocotreelo
open Logic

let write_to_file s filename =
  let out_channel = open_out filename in
  Printf.fprintf out_channel "%s\n" s;
  close_out out_channel

(**
  if input_filename is <file>.dot, return <file>_out

  otherwise return <input_filename>_out
*)
let get_out_dir input_filename =
  let regex = Str.regexp {|\(.*\)/\([^/]*\)\.\(dot\|spthy\)|} in
  let b = Str.string_match regex input_filename 0 in
  if b then
    let path = Str.matched_group 1 input_filename in
    let filename = Str.matched_group 2 input_filename in
    String.concat "" [path; "/"; filename; "_out/"]  
  else String.concat "" [input_filename; "_out/"]

let get_filename ?(cegar_round) input_filename suffix =
  match cegar_round with
  | Some cegar_round -> Printf.sprintf "%s%d-%s.dot" (get_out_dir input_filename) cegar_round suffix
  | None -> Printf.sprintf "%s-%s.dot" (get_out_dir input_filename) suffix

let create_out_dir input_filename =
  let dir_name = get_out_dir input_filename in
  if Sys.file_exists dir_name && Sys.is_directory dir_name then ()
  else Sys.mkdir dir_name 493

type 'a result = CANCELLED | TERMINATED of (bool option * 'a)

let () =
  Utils.Monitoring.init_stats ();
  let config = Config.parse () in

  (* init modules *)
  let module Enc = (val config.encoding) in
  let module Tableau_product = Tableau_product.Make(Enc.Kripke) in
  let module Annotation_generator = Annotation_generator.Make(Tableau_product)(Enc) in
  let module Maybe_finder = Maybe_finder.Make(Tableau_product) in
  let module Refiner = Refiner.Make(Tableau_product.Kripke.State) in
  let module Counterexample = Counterexample.Make(Tableau_product.Kripke.State) in

  (* create out directory *)
  let () = if config.verbose then create_out_dir config.program_file else () in

  (* parse input files *)
  let property = Parser.Utils.read_ctl_from_file config.ctl_file in
  let () = Printf.printf "Verify property %s.\n" (Ctl.to_string property) in
  let () = Printf.printf "Try to put quantifiers in leading position...\n" in
  let property_leading = Ctl.put_quantifiers_leading property in
  let () = if Option.is_none property_leading then
    Printf.printf "WARNING: Quantifiers cannot be put into leading position.\n" else () in
  let property_leading = Option.value ~default:property property_leading in
  let () = if not (property = property_leading) then Printf.printf "Adjusted property: %s.\n" (Ctl.to_string property_leading) in
  let property = property_leading in

  let () = Printf.printf "Parsing input file as a multiset rewrite system...\n"; flush stdout in
  let msrs = Parser.Utils.read_msrs_from_file config.program_file in

  let initial_params = Encoding.Encoding_params.determine_parameters msrs property in

  let rec cegar_cycle cegar_round params =
    let () = Printf.printf "Abstraction-Refinement Cycle %d\n" cegar_round in
    let () = if config.verbose then
      Printf.printf "- Encoding params:\n%s" (Encoding.Encoding_params.to_string params (Enc.Kripke.State.to_string) "- - ");
    in

    (* convert MSRS to Kripke *)
    let () = Printf.printf "- Convert multiset rewrite system into an FO-KMTS...\n"; flush stdout in
    let (kripke, var_dependencies, track_vars) = Enc.gen_kripke msrs config.maude_path property params in
    let () = if config.verbose then
      let (state_num, trans_num) = Enc.Kripke.get_stats kripke in
      Printf.printf "- - FO-KMTS stats: Number of states: %d, number of transitions: %d.\n" state_num trans_num;
      if config.output_files then
        let kripke_file = get_filename config.program_file ~cegar_round "kripke" in
        (Printf.printf "- - Write FO-KMTS to %s.\n" kripke_file; flush stdout;
        write_to_file (Enc.Kripke.draw kripke) kripke_file)
    in
    let () = if config.print_stats then Utils.Monitoring.print_stats "- - " in

    (* generate product structure*)
    let () = Printf.printf "- Generate product structure...\n"; flush stdout in
    let tab = Tableau_product.gen_product_structure kripke property in
    let () = if config.verbose then
      let (node_num, edge_num) = Tableau_product.get_stats tab in
      Printf.printf "- - Product structure stats: Number of nodes: %d, number of edges: %d.\n" node_num edge_num;
      if config.output_files then
        let tab_file = get_filename config.program_file ~cegar_round "tab" in
        (Printf.printf "- - Write product structure to %s.\n" tab_file;
        write_to_file (Tableau_product.draw tab) tab_file)
    in

    (* annotate product structure *)
    let () = Printf.printf "- Annotate product structure for %d rounds...\n" config.rounds; flush stdout in
    let ann_round = ref 0 in
    let (status, ann) = Annotation_generator.annotate_tab tab var_dependencies config.rounds (fun ann verification_state (cur_scc_tt, cur_scc_ff) scc_count -> 
      if config.verbose then
        let () = Printf.printf "- - Current SCC: %d/%d (tt/ff) of %d\r" cur_scc_tt cur_scc_ff scc_count; flush stdout in
        if (cur_scc_tt = scc_count && cur_scc_ff = scc_count)
            || (config.output_frequency != 0 
                && (!ann_round mod (max 1 (scc_count / config.output_frequency))) = 0) then
          let () = if config.print_stats then Utils.Monitoring.print_stats "- - "; flush stdout in
          let () = if config.output_files then
            let ann_file = get_filename config.program_file ~cegar_round (Printf.sprintf "ann-%d" !ann_round) in
            (Printf.printf "\n- - Write annotation step to %s.\n" ann_file; flush stdout;
            Async_file_tasks.do_with_timeout (fun () -> Annotation_generator.draw_with_annotations tab ann verification_state) (fun s -> write_to_file s ann_file) 60 ~stop_events:["draw_with_annotations"])
          in
          ()
        else ();
        ann_round := !ann_round + 1;
      else ()) in
    let () = match status with
      | Annotation_generator.CANCELLED -> Printf.printf "- Annotation process cancelled\n"; flush stdout
      | Annotation_generator.DONE -> Printf.printf "- Annotation process terminated successfully.\n"; flush stdout in
    let verified = Annotation_generator.check_if_verified ann kripke property track_vars in
    match verified with
    | Some true ->
      Printf.printf "- Property verified.\n";
      TERMINATED (verified, (kripke, tab, ann, track_vars, var_dependencies))
    | Some false ->
      Printf.printf "- Property falsified.\n";
      TERMINATED (verified, (kripke, tab, ann, track_vars, var_dependencies))
    | None ->
      let () = Printf.printf "- Property neither verified nor falsified.\n" in
    if status = CANCELLED then
      (Printf.printf "- Try again with higher -r.\n";
      CANCELLED)
    else 
      (* maybe finder *)
      let () = Printf.printf "- Find maybe-reason...\n"; flush stdout in
      let (res, maybe_reason) = Maybe_finder.find_counterexample tab var_dependencies ann kripke property in
      let () = match res with
        | FOUND -> Printf.printf "- Maybe-reason found.\n"; flush stdout
        | SPURIOUS -> failwith "Illegal state"
        | NOT_FOUND -> Printf.printf "- ERROR: Could not find the maybe-reason.\n"; flush stdout
      in
      let () = if config.verbose && config.output_files then
          let file = get_filename config.program_file ~cegar_round "maybe-reason" in
          Printf.printf "- - Write maybe-reason graph to %s.\n" file;
          write_to_file (Counterexample.draw maybe_reason) file
        else () in
      
      (* refine parameters *)
      let () = Printf.printf "- Find refinement...\n"; flush stdout in
      let params = Refiner.get_encoding_params params maybe_reason msrs property track_vars in
      match params with
      | Some params -> 
        if cegar_round + 1 >= config.max_cegar_cycles then
          let () = if config.verbose then
            Printf.printf "- Refined params:\n%s" (Encoding.Encoding_params.to_string params (Enc.Kripke.State.to_string) "- - ");
          in
          (Printf.printf "Abstraction-refinement cycle cancelled because max_cegar_cycles was reached.\nProperty neither verified nor falsified.\n";
          TERMINATED (verified, (kripke, tab, ann, track_vars, var_dependencies)))
        else 
          cegar_cycle (cegar_round + 1) params
      | None ->
        Printf.printf "Abstraction-refinement cycle cancelled because no refinement was found.\nProperty neither verified nor falsified.\n";
        TERMINATED (verified, (kripke, tab, ann, track_vars, var_dependencies))
  in

  let res = cegar_cycle 0 initial_params in

  (* generate counterexample *)
  let () = match res with
    | CANCELLED -> ()
    | TERMINATED (res, (kripke, tab, ann, track_vars, var_dependencies)) ->
      let module Counterexample_finder = Counterexample_finder.Make(Tableau_product) in
      let () = Printf.printf "Generate counterexample...\n"; flush stdout in
      let counterexample_res = Counterexample_finder.find_counterexample tab ann kripke track_vars var_dependencies property res in
      match counterexample_res with
      | None -> Printf.printf "- Cannot generate a counterexample for this kind of property with the result.\n"; flush stdout
      | Some (res, counterexample) ->
        let () = match res with
          | FOUND -> Printf.printf "- Counterexample found.\n"; flush stdout
          | SPURIOUS -> Printf.printf "- Only found spurious counterexamples.\n"; flush stdout
          | NOT_FOUND -> Printf.printf "- Could not find a valid or spurious counterexample.\n"; flush stdout
        in
        let () = if config.verbose then
          (* we output the counterexample even if output_files=false *)
          let counterexample_path = Counterexample.extract_kripke counterexample (res = SPURIOUS) in
          let file = get_filename config.program_file "counterexample" in
          Printf.printf "- - Write counterexample to %s.\n" file;
          write_to_file (Counterexample.draw counterexample) file;
          let file = get_filename config.program_file "counterexample_path" in
          Printf.printf "- - Write counterexample path to %s.\n" file;
          write_to_file (Counterexample.draw_path counterexample_path) file
        in
        ()
  in

  if config.print_stats then Utils.Monitoring.print_stats "";
  Maude.remove_maude_input_file () 
