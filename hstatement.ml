open Printf

open Logic
open Module
open Util

let encode_range ((line1, col1), (line2, col2)) : string =
  sprintf "@ %d %d %d %d" line1 col1 line2 col2

let decode_range s : range =
  if s = "" then empty_range else
  let words = String.split_on_char ' ' (string_from s 1) |>
    filter ((<>) "") |> map int_of_string in
  match words with
    | [line1; col1; line2; col2] -> ((line1, col1), (line2, col2))
    | _ -> failwith "decode_range"

let strip_range f : formula = match f with
  | App (Const (c, _), g) when starts_with "@" c -> g
  | _ -> f

let rec strip_ranges f : formula =
  map_formula strip_ranges (strip_range f)

let rec range_of f : range = match f with
  | App (Const (c, _), _) when starts_with "@" c -> decode_range c
  | App (Const ("(∀)", _), Lambda (_, _, g)) -> range_of g
  | _ -> empty_range

type reason = (string * range) list

type chain = (id * formula * reason) list  (* op, formula, reason(s) *)

type proof_step =
  | Assert of chain
  | Let of (id * typ) list
  | LetDef of id * typ * formula
  | Assume of formula
  | IsSome of id list * typ * formula
  | Escape
  | Group of proof_step list

let mk_assert f = Assert [("", f, [])]

let is_assert f = function
  | Assert [(_, f', _)] when f = f' -> true
  | _ -> false

let is_assume = function
  | Assume _ -> true
  | _ -> false

let step_types step : typ list = match step with
  | Let ids_types -> unique (map snd ids_types)
  | LetDef (_, typ, _) | IsSome (_, typ, _) -> [typ]
  | _ -> []
  
let rec step_decl_vars = function
  | Let ids_types -> map fst ids_types
  | LetDef (id, _, _) -> [id]
  | IsSome (ids, _, _) -> ids
  | Group steps -> unique (concat_map step_decl_vars steps)
  | _ -> []

let rec step_formulas = function
  | Assert fs -> let+ (_, f, _) = fs in [f]
  | Let _ | Escape -> []
  | LetDef (_, _, f) -> [f]
  | Assume f -> [f]
  | IsSome (_, _, f) -> [f]
  | Group steps -> concat_map step_formulas steps

let step_free_vars step = unique @@
  let vars =
    concat_map free_vars_in_type (step_types step) @
    concat_map free_vars (step_formulas step) in
  match step with
    | IsSome (ids, _, _) -> subtract vars ids
    | _ -> vars

let step_free_type_vars step = unique @@
  concat_map free_type_vars_in_type (step_types step) @
  concat_map free_type_vars (step_formulas step)

let show_chain chain : string =
  let to_str (op, f, _) =
    let s = show_formula f in
    if op = "" then s else op ^ " " ^ s in
  unwords (map to_str chain)

let rec show_proof_step step : string = match step with
  | Assert chain -> sprintf "assert %s" (show_chain chain)
  | Let ids_types ->
      let show (id, typ) = sprintf "%s : %s" id (show_type typ) in
      "let " ^ comma_join (map show ids_types)
  | LetDef (_id, _typ, f) -> sprintf "let_def : %s" (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (ids, typ, f) -> sprintf "is_some %s : %s : %s"
      (comma_join ids) (show_type typ) (show_formula f)
  | Escape -> "escape"
  | Group steps ->
      sprintf "[%s]" (comma_join (map show_proof_step steps))

let is_function_definition = function
  | LetDef (_id, _typ, f) -> (match strip_range f with
      | Eq _ -> false
      | _ -> true)
  | _ -> false

type hstatement =
  | HTypeDecl of id * string option  (* e.g. "ℤ", "integer" *)
  | HConstDecl of id * typ
  | HAxiom of id * proof_step list * string option (* num, steps, name *)
  | HDefinition of id * typ * formula
  | HTheorem of
      { id: string; name: string option;
        steps: proof_step list; proof_steps: proof_step list }

let hstmt_id = function
  | HTypeDecl (id, _) | HConstDecl (id, _) | HAxiom (id, _, _)
  | HDefinition (id, _, _)
  | HTheorem { id; _ } -> id

let hstmt_kind = function
  | HTypeDecl _ -> "typedecl"
  | HConstDecl _ -> "const"
  | HAxiom _ -> "axiom"
  | HDefinition _ -> "definition"
  | HTheorem _ -> "theorem"

let hstmt_id_name stmt : string =
  let base = hstmt_kind stmt ^ " " ^ strip_prefix (hstmt_id stmt) in
  match stmt with
  | HAxiom (_, _, name)
  | HTheorem { name; _ } -> 
      base ^ (match name with
        | Some name -> sprintf " (%s)" name
        | _ -> "")
  | _ -> base

let definition_id f : id =
  match is_eq_or_iff (strip_range (remove_universal f)) with
    | Some (f, _g) ->
        get_const_or_var (head_of f)
    | _ -> failwith "definition_id: definition expected"

type hmodule = hstatement _module
