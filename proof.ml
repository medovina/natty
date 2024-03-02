open List

open Logic
open Util

type source =
  | Id of id
  | File of string * id  (* filename, id *)
  | Inference of id * id * source list  (* name, status, children *)

type proof_formula = id * id * formula * source  (* name, role, formula, source *)

let rec hypotheses = function
  | Id id -> [id]
  | File _ -> []
  | Inference (_, _, sources) -> concat_map hypotheses sources

let gather_hypotheses formulas =
  let ids = concat_map (fun (_, _, _, source) -> hypotheses source) formulas in
  let is_axiom id =
    let (_, role, _, _) = find (fun (name, _, _, _) -> name = id) formulas in
    role = "axiom" in
  unique (filter is_axiom ids)
