let get_all_matching s regex =
  let regex = Str.regexp regex in
  let split = Str.full_split regex s in
  List.filter_map (fun elem -> match elem with
    | Str.Text _ -> None
    | Str.Delim matching -> Some matching
  ) split

module StringSet = Set.Make(struct
  type t = string
  let compare = Repr.compare
end)

let replace s regex replacement =
  let regex = Str.regexp_string regex in
  Str.global_replace regex replacement s
