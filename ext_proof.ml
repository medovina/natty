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

type clause_attributes = {
  proof_depth: int; proof_size: int
}

type clause = {
  name: id; role: string; formula: formula; source: source;
  info: string; arg: string option; attributes: clause_attributes option
}

let map_clause fn clause = { clause with formula = fn (clause.formula) }

let find_clause_opt id = find_opt (fun s -> s.name = id)

let find_clause id clauses = Option.get (find_clause_opt id clauses)

let rec hypotheses = function
  | Id id -> [id]
  | File _ -> []
  | Inference (_, _, sources) ->
      concat_map hypotheses sources

let hypotheses_of clause = hypotheses clause.source

let get_hypothesis clause = match hypotheses_of clause with
  | [id] -> id
  | _ -> assert false

let rec source_rules = function
  | Inference (name, _, children) ->
      name :: concat_map source_rules children
  | _ -> []

let gather_hypotheses clauses =
  let ids = concat_map hypotheses_of clauses in
  let is_axiom id =
    (find_clause id clauses).role = "axiom" in
  unique (filter is_axiom ids)

type e_proof = {
  clauses: clause list;
  heuristic_def : string list option;
  proof: (clause list * string) option;  (* proof clauses, total steps *)
  user_time: string
}
