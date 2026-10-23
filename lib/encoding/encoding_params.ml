open Logic

type 'a params = {
  cap: (string * int) list;
  tracked: Multiset_rewrite_system.multiset list;
  start_with_empty_state: bool;
  hide_action_facts: bool
}

let additional_manual_params = 
  let open Manual_params in
  { cap; tracked; start_with_empty_state; hide_action_facts }

let determine_parameters ?(additional_manual_params=additional_manual_params) msrs property =
  let fact_symbols = Multiset_rewrite_system.get_fact_symbols msrs in
  let cap = List.map (fun (fact_symbol, _) -> (fact_symbol, 0)) fact_symbols in
  
  let params = { cap; tracked = []; start_with_empty_state = true; hide_action_facts = false (* ignored later *) } in
  (* TODO remove ability to set manual params in the future *)
  let params = {
      cap = additional_manual_params.cap @ params.cap;
      tracked = additional_manual_params.tracked @ params.tracked;
      start_with_empty_state = additional_manual_params.start_with_empty_state;
      hide_action_facts = additional_manual_params.hide_action_facts
    } in
  params

let mk_unknowns_distinct tracked =
  let (_, tracked) = List.fold_left_map (fun var_counter track_var ->
      let ((_, var_counter), track_var) = List.fold_left_map (fun (subst, var_counter) (fact_name, args) -> 
          let ((subst, var_counter), args) = List.fold_left_map (fun (subst, var_counter) arg -> match arg with
              | Arg_terms.Int Unknown x -> (match List.assoc_opt x subst with 
                | Some x -> ((subst, var_counter), Arg_terms.Int (Unknown x))
                | None ->
                  let new_unknown = Printf.sprintf "u%d" var_counter in
                  (((x, new_unknown)::subst, var_counter + 1), Arg_terms.Int (Unknown new_unknown))
                )
              | _ -> ((subst, var_counter), arg)
            ) (subst, var_counter) args in
          ((subst, var_counter), (fact_name, args))
        ) ([], var_counter) track_var in
      (var_counter, track_var)
    ) 0 tracked in
  tracked

let to_string params state_to_string prefix =
  let cap_s = String.concat ", " (List.map (fun (fact_name, cap) -> Printf.sprintf "(%s, %d)" fact_name cap) params.cap) in
  let tracked_s = "{" ^ String.concat ",\n" (List.map Multiset_rewrite_system.ms_to_detailed_string params.tracked) ^ "}" in
  Printf.sprintf "%sCaps: %s\n%sTracked: %s\n%sStart with empty state: %B\n%sHide action facts: %B\n" prefix cap_s prefix tracked_s prefix params.start_with_empty_state prefix params.hide_action_facts
