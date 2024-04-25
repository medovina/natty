open List
open Printf

open Logic
open Util

type proof_step =
  | Assert of formula
  | Let of id list * typ
  | LetVal of id * typ * formula
  | Assume of formula
  | IsSome of id * typ * formula
  | By of id * id list * id
      (* theorem/axiom name, outer vars, induction variable *)

let step_decl_vars = function
  | Let (ids, _) -> ids
  | LetVal (id, _, _) -> [id]
  | IsSome (id, _, _) -> [id]
  | _ -> []

let step_free_vars = function
  | Assert f -> free_vars f
  | LetVal (_, _, f) -> free_vars f
  | Assume f -> free_vars f
  | IsSome (id, _, f) -> remove id (free_vars f)
  | _ -> []

let show_proof_step = function
  | Assert f -> sprintf "assert %s" (show_formula f)
  | Let (ids, typ) -> sprintf "let %s : %s" (comma_join ids) (show_type typ)
  | LetVal (id, typ, f) -> sprintf "let %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (id, typ, f) -> sprintf "exists %s : %s : %s"
      id (show_type typ) (show_formula f)
  | By (name, outer, var) ->
      let for_any =
        if outer = [] then ""
        else " for any " ^ comma_join outer in
      sprintf "by %s on %s%s" name var for_any

type proof =
  | Steps of proof_step list
  | Formulas of (formula * formula) list  (* full, short original *)

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula * id option (* id, formula, name *)
  | Definition of id * typ * formula
  | Theorem of id * formula * proof option

let stmt_name = function
  | TypeDecl id -> "type " ^ id
  | ConstDecl (id, _) -> "const " ^ id
  | Axiom (id, _, _) -> "axiom " ^ id
  | Definition (id, _, _) -> "definition " ^ id
  | Theorem (id, _, _) -> "theorem " ^ id

let stmt_formula = function
  | Axiom (_, f, _) -> Some f
  | Definition (_, _, f) -> Some f
  | Theorem (_, f, _) -> Some f
  | _ -> None

let stmt_const = function
  | ConstDecl (id, _) -> Some id
  | Definition (id, _, _) -> Some id
  | _ -> None

let axiom_named name = function
  | Axiom (_id, f, Some n) when eq_icase n name -> Some f
  | _ -> None

let show_statement multi s =
  let name = stmt_name s in
  let show prefix f =
    indent_with_prefix (name ^ ": " ^ prefix) (show_formula_multi multi f) in
  match s with
    | TypeDecl _ -> name
    | ConstDecl (_, typ) -> sprintf "%s : %s" name (show_type typ)
    | Axiom (_, f, _) -> show "" f
    | Definition (_, typ, f) ->
        show (sprintf "%s ; " (show_type typ)) f
    | Theorem (_, f, _) -> show "" f
