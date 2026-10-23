type int_term = Var of string | Const of int | Smt of Sat.expr | Unknown of string
type bool_term = Var of string | Smt of Sat.expr
type term = Int of int_term | Bool of bool_term | UntypedVar of string (* for variables whose type is unknown -> it should be known when converting to smt at latest! *)

let to_string term = match term with
  | Int Var x
  | Bool Var x
  | UntypedVar x -> x
  | Int Const n -> string_of_int n
  | Int Smt smt
  | Bool Smt smt -> Sat.to_string smt
  | Int Unknown x -> x

let to_detailed_string term = match term with
  | Int Unknown x -> "(U " ^ x ^ ")"
  | _ -> to_string term

let to_smt arg = match arg with
  | Int Var x -> Sat.mk_var_sort x Sat.sort_int
  | Bool Var x -> Sat.mk_var_sort x Sat.sort_bool
  | Int Const n -> Sat.mk_int n
  | Int Smt smt
  | Bool Smt smt -> smt
  | UntypedVar _ -> failwith "Cannot convert an untyped variable to smt"
  | Int Unknown x -> failwith "Cannot convert unknown to smt."

let subst_vars term subst = match term with
  | Int Var x -> List.assoc_opt x subst |> Option.value ~default:(Int (Var x))
  | Bool Var x -> List.assoc_opt x subst |> Option.value ~default:(Bool (Var x))
  | UntypedVar x -> List.assoc_opt x subst |> Option.value ~default:(UntypedVar x)
  | Int Const _ -> term
  | Int Smt smt
  | Bool Smt smt ->
    let (vars, values) = List.fold_left (fun (vars, values) (var, value) ->
      let value = to_smt value in
      (var::vars, value::values)) ([], []) subst in
    Int (Smt (Sat.subst_vars smt vars values))
  | Int Unknown x -> Int (Unknown x)

let simplify arg = match arg with
  | Int Smt smt -> Int (Smt (Sat.simplify smt))
  | Bool Smt smt -> Bool (Smt (Sat.simplify smt))
  | arg -> arg

let is_var term = match term with
  | Int Var _
  | Bool Var _
  | UntypedVar _ -> true
  | _ -> false

let unknowns term = match term with
  | Int Unknown x -> [x]
  | _ -> []

let instantiate_unknowns prefix term = match term with
  | Int Unknown x -> Int (Var (prefix ^ x))
  | term -> term

let subst_unknowns term subst =
  match term with
  | Int Unknown x -> List.assoc_opt x subst |> Option.value ~default:(Int (Unknown x))
  | _ -> term

let make_vars_unknowns term = match term with
  | Int Var x -> Int (Unknown x)
  | term -> term

(* following functions do not work with smt *)
let vars term = match term with
  | Int Var x
  | Bool Var x
  | UntypedVar x -> [x]
  | Int Const _ -> []
  | Int Unknown x -> []
  | _ -> failwith "Smt term is not supported in function vars."

let prefix_vars term prefix = match term with
  | Int Var x -> Int (Var (prefix ^ x))
  | Bool Var x -> Int (Var (prefix ^ x))
  | UntypedVar x -> UntypedVar (prefix ^ x)
  | Int Const _ -> term
  | _ -> failwith "Smt term is not supported in function prefix_vars."
