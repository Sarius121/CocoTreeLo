module type Elem = sig
  type t
  val compare: t -> t -> int
end

module type OutgoingMap = sig
  type key
  type 'a t

  val empty: 'a t

  val update: key -> 'a -> 'a t -> 'a t

  val update_list: key -> 'a list -> 'a t -> 'a t

  val init: ('b -> key * 'a) -> 'b list -> 'a t

  val get: key -> 'a t -> 'a list
end

module Make (Elem: Elem): (OutgoingMap with type key = Elem.t) = struct

  module ElemMap = Map.Make(Elem)

  type 'a t = ('a list) ElemMap.t
  type key = Elem.t

  let empty = ElemMap.empty

  let update key new_elem map =
    ElemMap.update key (fun cur_elem ->
        match cur_elem with
        | Some cur_elem -> Some (new_elem::cur_elem)
        | None -> Some [new_elem]
      ) map

  let update_list key new_elem map =
    ElemMap.update key (fun cur_elem ->
        match cur_elem with
        | Some cur_elem -> Some (new_elem @ cur_elem)
        | None -> Some new_elem
      ) map

  let init f elems =
    List.fold_left (fun map elem -> 
        let (key, new_elem) = f elem in
        update key new_elem map
      ) ElemMap.empty elems

  let get key map = Option.value ~default:[] (ElemMap.find_opt key map)
end