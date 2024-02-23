open Printf

open List
open Util

type id = string

type typ =
  | Bool
  | Fun of typ * typ
  | Base of id

let rec show_type = function
  | Bool -> "𝔹"
  | Fun (t, u) -> sprintf "(%s → %s)" (show_type t) (show_type u)
  | Base id -> id

let mk_base_type = function
  | "𝔹" -> Bool
  | id -> Base id

let unknown_type = Base "?"

type formula =
  | Const of id * typ
  | Var of id * typ
  | App of formula * formula
  | Lambda of id * typ * formula
  | Eq of formula * formula

let logical_binary = ["∧"; "→"]

let quant_type = Fun (Fun (Base "_", Bool), Bool)

let logical_consts =
  map (fun sym -> (sym, Fun (Bool, Fun (Bool, Bool)))) logical_binary @
  [("¬", Fun (Bool, Bool)); ("∀", quant_type); ("∃", quant_type)]

let const id = Const (id, unknown_type)

let not f = App (const "¬", f)

let binop op f g = App (App (const op, f), g) 

let mk_and = binop "∧"
let implies = binop "→"

let binder name id typ f = App (const name, Lambda (id, typ, f))
let binder' name (id, typ) f = binder name id typ f

let for_all = binder "∀"
let for_all' = binder' "∀"

let exists = binder "∃"

let mk_eq f g = Eq (f, g)

let mk_neq f g = not (mk_eq f g)

type formula_kind =
  | Binary of id * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let kind = function
  | App (App (Const (op, _), t), u) ->
      Binary (op, t, u)
  | App (Const (q, _), Lambda (id, typ, u)) when q = "∀" || q = "∃" ->
      Quant(q, id, typ, u)
  | f -> Other f

let binary_ops = ["+"; "·"] @ logical_binary

let rec show_formula f = match kind f with
  | Binary (op, t, u) when mem op binary_ops ->
      sprintf "(%s %s %s)" (show_formula t) op (show_formula u)
  | Quant (q, id, typ, u) ->
      sprintf "%s%s:%s.%s" q id (show_type typ) (show_formula u)
  | _ -> match f with
    | Const (id, _typ) -> id
    | Var (id, _typ) -> id
    | App (Const ("¬", _), Eq (t, u)) ->
        sprintf "%s ≠ %s" (show_formula t) (show_formula u)
    | App (t, u) ->
        sprintf "%s(%s)" (show_formula t) (show_formula u)
    | Lambda (id, typ, t) -> sprintf "λ%s:%s.%s" id (show_type typ) (show_formula t)
    | Eq (t, u) -> sprintf "%s = %s" (show_formula t) (show_formula u)

let free_vars f =
  let rec free = function
    | Const _ -> []
    | Var (id, _) -> [id]
    | App (t, u) | Eq (t, u) -> free t @ free u
    | Lambda (id, _, t) -> subtract (free t) [id] in
  unique (free f)

let for_all_n (ids, typ) f =
  List.fold_right (fun id f -> for_all id typ f) ids f

let for_all_n' (ids, typ) f =
  for_all_n (intersect ids (free_vars f), typ) f

let multi_eq f =
  let rec collect = function
    | Eq (f, g) -> f :: collect g
    | f -> [f] in
  let rec join = function
    | [x; y] -> mk_eq x y
    | x :: y :: xs -> mk_and (mk_eq x y) (join (y :: xs))
    | _ -> assert false in
  match collect f with
    | [] -> assert false
    | [f] -> f
    | fs -> join fs

(* statements *)

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula
  | Definition of id * typ * formula
  | Theorem of id * formula

let mk_axiom id f = Axiom (id, f)
let mk_theorem id f = Theorem (id, f)

let show_statement = function
  | TypeDecl id -> sprintf "type %s" id
  | ConstDecl (id, typ) -> sprintf "const %s : %s" id (show_type typ)
  | Axiom (name, t) -> sprintf "axiom %s: %s" name (show_formula t)
  | Definition (id, typ, f) ->
      sprintf "definition %s : %s ; %s" id (show_type typ) (show_formula f)
  | Theorem (name, t) -> sprintf "theorem %s: %s" name (show_formula t)
