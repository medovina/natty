open List
open Printf

open Logic
open Util

type source =
  | Id of id
  | File of string * id  (* filename, id *)
  | Inference of id * id * source list  (* name, status, parents *)

let rec show_source = function
  | Id id -> id
  | File (_, _) -> "file"
  | Inference (id, _, parents) ->
      sprintf "%s(%s)" id (comma_join (map show_source parents))

type clause = id * id * formula * source  (* name, role, formula, source *)

let name_of (name, _, _, _) = name
let formula_of (_, _, f, _) = f

let map_clause fn =
  fun (name, role, f, source) -> (name, role, fn f, source)

let find_clause_opt id = find_opt (fun s -> name_of s = id)

let find_clause id clauses = Option.get (find_clause_opt id clauses)

let rec hypotheses = function
  | Id id -> [id]
  | File _ -> []
  | Inference (_, _, sources) ->
      concat_map hypotheses sources

let hypotheses_of (_, _, _, source) = hypotheses source

let rec source_rules = function
  | Inference (name, _, children) ->
      name :: concat_map source_rules children
  | _ -> []

let gather_hypotheses formulas =
  let ids = concat_map hypotheses_of formulas in
  let is_axiom id =
    let (_, role, _, _) = find_clause id formulas in
    role = "axiom" in
  unique (filter is_axiom ids)
