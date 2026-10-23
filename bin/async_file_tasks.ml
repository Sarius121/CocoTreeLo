exception Timeout

let do_with_timeout ?(stop_events=[]) func postprocess timeout =
  let _ = Sys.signal Sys.sigalrm (Signal_handle (fun _ -> raise Timeout)) in
  let _ = Unix.alarm timeout in
  try
    let res = func () in
    let _ = Unix.alarm 0 in
    postprocess res
  with Timeout ->
    List.iter Utils.Monitoring.stop_event stop_events;
    Printf.printf "WARNING: function timed-out.\n"
