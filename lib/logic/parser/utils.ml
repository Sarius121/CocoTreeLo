let read_ctl_from_file filename =
  let channel = open_in filename in
  try
    let lexbuf = Lexing.from_channel channel in
    let res = Ctl_parser.main Ctl_lexer.token lexbuf in
    close_in channel; res
  with ex ->
    close_in_noerr channel;
    failwith "Error parsing the ctl file. Please provide one CTL property in the first line of the file, followed by a line-break."

let parse_ctl s =
  try
    let lexbuf = Lexing.from_string s in
    Ctl_parser.main Ctl_lexer.token lexbuf
  with ex ->
    failwith "Error parsing the ctl input."

let parse_msrs s =
  try
    let lexbuf = Lexing.from_string s in
    Msrs_parser.main Msrs_lexer.token lexbuf
  with ex ->
    failwith "Error parsing the msrs input."

let read_msrs_from_file filename =
  let channel = open_in filename in
  try
    let lexbuf = Lexing.from_channel channel in
    let res = Msrs_parser.main Msrs_lexer.token lexbuf in
    close_in channel; res
  with ex ->
    close_in_noerr channel;
    failwith "Error parsing the msrs file."

let read_msrs_from_file_opt filename =
  let channel = open_in filename in
  try
    let lexbuf = Lexing.from_channel channel in
    let res = Some (Msrs_parser.main Msrs_lexer.token lexbuf) in
    close_in channel; res
  with ex ->
    close_in_noerr channel;
    None
