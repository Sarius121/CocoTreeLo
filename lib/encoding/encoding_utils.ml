open Logic

type raw_params = (string * string) list

module type Encoding = sig
  module Kripke: Kripke.Kripke
  type state = Kripke.state
  val gen_kripke: Multiset_rewrite_system.msrs -> string -> Ctl.ctl -> state Encoding_params.params -> Kripke.kripke * (string, string list) Hashtbl.t * Multiset_rewrite_system.multiset list
  val annotate_fact: state -> Multiset_rewrite_system.fact -> bool -> Sat.expr
  val annotate_label: state -> string -> bool -> Sat.expr
end

module DefaultEncoding: (Encoding with module Kripke = Kripke.LabeledKripke) = struct
  module Kripke = Kripke.LabeledKripke
  type state = Kripke.state
  type params = unit
  let parse_params raw = if raw = [] then Ok () else Error "The default encoding expects no parameters"
  let gen_kripke _ _ _ = failwith "The default encoding can't generate a Kripke structure."
  let annotate_fact _ _ _ = failwith "The default encoding can't be used for facts."
  let annotate_label (_, labels) lbl pos =
    if pos then
      if List.find_opt (fun label -> lbl = label) labels = None then Sat.mk_bool false else Sat.mk_bool true
    else
      if List.find_opt (fun label -> lbl = label) labels = None then Sat.mk_bool true else Sat.mk_bool false
end

(**
  Get the module corresponding to the string id.
  Returns an empty encoding by default.  
*)
let get_encoding name =
  match name with
  | "combi" -> (module Maude_narrowing_combi: Encoding)
  | _ -> (module DefaultEncoding)