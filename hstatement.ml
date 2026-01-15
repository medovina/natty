open Printf

open Logic
open Module
open Util

type reason = (string * range) list

type proof_step =
  | Assert of formula * reason
  | Let of (id * typ) list
  | LetDef of id * typ * formula
  | Assume of formula
  | IsSome of (id * typ) list * formula * reason
  | Escape
  | Group of proof_step list

let mk_assert f = Assert (f, [])
let mk_assume f = Assume f

let get_assert step = match step with
  | Assert (f, _) -> f
  | _ -> failwith "get_assert"

let is_let_def = function
  | LetDef _ -> true
  | _ -> false

let is_assume = function
  | Assume _ -> true
  | _ -> false

let is_is_some = function
  | IsSome _ -> true
  | _ -> false

let step_types step : typ list = match step with
  | Let ids_types | IsSome (ids_types, _, _) -> unique (map snd ids_types)
  | LetDef (_, typ, _) -> [typ]
  | _ -> []
  
let rec step_decl_vars = function
  | Let ids_types | IsSome (ids_types, _, _) -> map fst ids_types
  | LetDef (id, _, _) -> [id]
  | Group steps -> unique (concat_map step_decl_vars steps)
  | _ -> []

let rec step_formulas = function
  | Assert (f, _) -> [f]
  | Let _ | Escape -> []
  | LetDef (_, _, f) -> [f]
  | Assume f -> [f]
  | IsSome (_, f, _) -> [f]
  | Group steps -> concat_map step_formulas steps

let step_free_vars step = unique @@
  let vars =
    concat_map free_vars_in_type (step_types step) @
    concat_map free_vars (step_formulas step) in
  match step with
    | IsSome (ids_types, _, _) -> subtract vars (map fst ids_types)
    | _ -> vars

let step_free_type_vars step = unique @@
  concat_map free_type_vars_in_type (step_types step) @
  concat_map free_type_vars (step_formulas step)

let show_chain chain : string =
  let to_str (op, f, _) =
    let s = show_formula f in
    if op = "" then s else op ^ " " ^ s in
  unwords (map to_str chain)

let show_ids_types ids_types : string =
  let show (id, typ) = sprintf "%s : %s" id (show_type typ) in
  comma_join (map show ids_types)

let rec show_proof_step step : string = match step with
  | Assert (f, _) -> sprintf "assert %s" (show_formula f)
  | Let ids_types -> "let " ^ show_ids_types ids_types
  | LetDef (_id, _typ, f) -> sprintf "let_def : %s" (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (ids_types, f, _) -> sprintf "is_some %s : %s"
      (show_ids_types ids_types) (show_formula f)
  | Escape -> "escape"
  | Group steps ->
      sprintf "[%s]" (comma_join (map show_proof_step steps))

type haxiom = {
  sub_index: string; name: string option;
  steps: proof_step list
}

type hdef = {
  sub_index: string; formula: formula
}

type htheorem = {
  sub_index: string; name: string option;
  steps: proof_step list; proof_steps: proof_step list
}

type hstatement =
  | HTypeDef of id * (id * typ) list * string option  (* name, constructors, long name *)
  | HConstDecl of id * typ
  | HAxiomGroup of (id * typ) option * haxiom list
  | HDefinition of {
      id_type: (id * typ) option; recursive: bool; defs: hdef list;
      justification: proof_step list
    }
  | HTheoremGroup of htheorem list

let defined_id_type hstmt : id * typ = match hstmt with
  | HTypeDef (id, _, _) -> (id, Type)
  | HConstDecl (id, typ) -> (id, typ)
  | _ -> failwith "defined_id_type"

let theorem_name id name : string =
  "theorem " ^ id ^ (match name with
    | Some name -> sprintf " (%s)" name
    | _ -> "")

let definition_id f : id =
  match is_eq_or_iff (remove_universal f) with
    | Some (f, _g) ->
        get_const_or_var (head_of f)
    | _ -> failwith "definition_id: definition expected"

type hmodule = hstatement _module
