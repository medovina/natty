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
  | Escape
  | Group of proof_step list

let mk_assert f = Assert f

let rec step_decl_vars = function
  | Let (ids, _) -> ids
  | LetVal (id, _, _) -> [id]
  | IsSome (id, _, _) -> [id]
  | Group steps -> unique (concat_map step_decl_vars steps)
  | _ -> []

let rec step_free_vars = function
  | Assert f -> free_vars f
  | LetVal (_, _, f) -> free_vars f
  | Assume f -> free_vars f
  | IsSome (id, _, f) -> remove id (free_vars f)
  | Group steps -> unique (concat_map step_free_vars steps)
  | _ -> []

let rec show_proof_step = function
  | Assert f -> sprintf "assert %s" (show_formula f)
  | Let (ids, typ) -> sprintf "let %s : %s" (comma_join ids) (show_type typ)
  | LetVal (id, typ, f) -> sprintf "let_val %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (id, typ, f) -> sprintf "is_some %s : %s : %s"
      id (show_type typ) (show_formula f)
  | Escape -> "escape"
  | Group steps -> sprintf "[%s]" (comma_join (map show_proof_step steps))

type proof =
  | Steps of proof_step list
  | Formulas of (formula * formula) list  (* full, short original *)

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula * id option (* id, formula, descriptive name *)
  | Definition of id * typ * formula
  | Theorem of id * formula * proof option

let stmt_id = function
  | TypeDecl id -> id
  | ConstDecl (id, _) -> id
  | Axiom (id, _, _) -> id
  | Definition (id, _, _) -> id
  | Theorem (id, _, _) -> id

let stmt_name stmt = (match stmt with
  | TypeDecl _ -> "type"
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom"
  | Definition _ -> "definition"
  | Theorem _ -> "theorem") ^ " " ^ stmt_id stmt

let stmt_formula = function
  | Axiom (_, f, _) -> Some f
  | Definition (_, _, f) -> Some f
  | Theorem (_, f, _) -> Some f
  | _ -> None

let stmt_const = function
  | ConstDecl (id, _) -> Some id
  | Definition (id, _, _) -> Some id
  | _ -> None

let mk_eq_def sym typ f =
  Definition (sym, typ, Eq (Const (sym, typ), f))

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
