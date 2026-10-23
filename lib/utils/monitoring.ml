type event_type = START | STOP
type event = event_type * string * Unix.process_times * float

let events = ref []
let start_time = ref (0., 0.)

let init_stats () =
  events := [];
  start_time := ((Unix.times ()).Unix.tms_utime, Unix.gettimeofday ())

let start_event event = events := (START, event, Unix.times (), Unix.gettimeofday ())::!events

let stop_event event = events := (STOP, event, Unix.times (), Unix.gettimeofday ())::!events

let print_stats prefix =
  let (start_cpu, start_clock) = !start_time in
  let total_time_cpu = (Unix.times ()).Unix.tms_utime -. start_cpu in
  let total_time_clock = Unix.gettimeofday () -. start_clock in
  let times_per_event = Hashtbl.create 10 in
  let () = List.iter (fun event -> 
      let _, event_name, _, _ = event in
      match Hashtbl.find_opt times_per_event event_name with
      | None -> Hashtbl.add times_per_event event_name [event]
      | Some rest -> Hashtbl.replace times_per_event event_name (event::rest)
    ) !events in
  let () = Printf.printf "%sStats (CPU time / Clock time): (Total time %0.2f s / %0.2f s)\n" prefix total_time_cpu total_time_clock in
  Hashtbl.iter (fun event_name events ->
      let rec get_total_time events (time_cpu, time_clock) = (match events with
        | (START, _, time_start_cpu, time_start_clock)::(STOP, _, time_stop_cpu, time_stop_clock)::l ->
          let time_cpu = time_cpu +. (time_stop_cpu.Unix.tms_utime -. time_start_cpu.Unix.tms_utime) in
          let time_clock = time_clock +. (time_stop_clock -. time_start_clock) in
          get_total_time l (time_cpu, time_clock)
        | [] -> (time_cpu, time_clock)
        | _ -> failwith "Event has never been stopped or started\n")
      in
      let (event_cpu, event_clock) = get_total_time events (0., 0.) in
      let percentage_cpu = event_cpu /. total_time_cpu *. 100. in
      let percentage_clock = event_clock /. total_time_clock *. 100. in
      Printf.printf "%s- %s: %0.2f s (%0.2f %%) / %0.2f s (%0.2f %%)\n" prefix event_name event_cpu percentage_cpu event_clock percentage_clock
    ) times_per_event

let get_total_time () =
  let (start_cpu, start_clock) = !start_time in
  let total_time_cpu = (Unix.times ()).Unix.tms_utime -. start_cpu in
  let total_time_clock = Unix.gettimeofday () -. start_clock in
  (total_time_cpu, total_time_clock)
