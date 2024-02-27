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

let rec type_of = function
  | Const (_, typ) | Var (_, typ) -> typ
  | App (f, _) -> (match type_of f with
      | Fun (_, u) -> u
      | _ -> assert false)
  | Lambda (_, typ, f) -> Fun (typ, type_of f)
  | Eq (_, _) -> Bool

let mk_false = Const ("⊥", Bool)

let mk_not f = App (Const ("¬", Fun (Bool, Bool)), f)

let logical_binary = ["∧"; "∨"; "→"]

let quant_type = Fun (Fun (Base "_", Bool), Bool)

let binop op typ f g = App (App (Const (op, typ), f), g) 
let binop_unknown op = binop op unknown_type

let logical_op op = binop op (Fun (Bool, Fun (Bool, Bool)))

let mk_and = logical_op "∧"
let mk_or = logical_op "∨"
let implies1 = logical_op "→"

let binder name id typ f = App (Const (name, quant_type), Lambda (id, typ, f))
let binder' name (id, typ) f = binder name id typ f

let for_all = binder "∀"
let for_all' = binder' "∀"

let exists = binder "∃"

let mk_eq f g = Eq (f, g)

let mk_neq f g = mk_not (mk_eq f g)

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

let implies f g = match kind f with
  | Binary ("∧", s, t) -> implies1 s (implies1 t g)
  | _ -> implies1 f g

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
    | Lambda (id, _, t) -> remove id (free t) in
  unique (free f)

let for_all_vars_typ (ids, typ) f =
  fold_right (fun id f -> for_all id typ f) ids f

let for_all_vars_typ_if_free (ids, typ) f =
  for_all_vars_typ (intersect ids (free_vars f), typ) f

let for_all_vars_typs = fold_right for_all'

let rec for_alls f = match kind f with
  | Quant ("∀", id, typ, f) ->
      let (vs, g) = for_alls f in ((id, typ) :: vs, g)
  | _ -> ([], f)

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id
  
(* t[u/x] *)
let rec subst1 t u x = match t with
  | Const _ -> t
  | Var (y, _) -> if x = y then u else t
  | App (f, g) -> App (subst1 f u x, subst1 g u x)
  | Lambda (y, typ, t') -> if x = y then t else
      if not (mem y (free_vars u)) then Lambda (y, typ, subst1 t' u x)
      else let y' = rename y (x :: free_vars t') in
        Lambda (y', typ, subst1 (subst1 t' (Var (y', typ)) y) u x)
  | Eq (f, g) -> Eq (subst1 f u x, subst1 g u x)

let subst_n subst f =
  fold_left (fun f (x, t) -> subst1 f t x) f subst
  
let rec reduce = function
  | App (f, g) -> (match reduce f, reduce g with
      | Lambda (x, _typ, f), g -> reduce (subst1 f g x)
      | f, g -> App (f, g))
  | Lambda (id, typ, f) -> Lambda (id, typ, reduce f)
  | Eq (f, g) -> Eq (reduce f, reduce g)
  | f -> f

let simp = function
  | Lambda (id, typ, App (f, Var (id', typ'))) when id = id' && typ = typ' ->
      f  (* η-reduction *)
  | f -> f

let unify =
  let rec unify' subst t u = match simp t, simp u with
    | Const (id, typ), Const (id', typ') ->
        if id = id' && typ = typ' then Some [] else None
    | Var (id, typ), f | f, Var (id, typ) ->
        if typ = type_of f then Some ((id, f) :: subst) else None
    | App (f, g), App (f', g') | Eq (f, g), Eq (f', g') ->
        let* subst = unify' subst f f' in
        unify' subst g g'
    | _, _ -> None
  in unify' []

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

let rec premises f = match kind f with
  | Binary ("→", f, g) ->
      let (fs, concl) = premises g in (f :: fs, concl)
  | _ -> ([], f)

(* statements *)

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
  | Let (ids, typ) -> sprintf "let %s : %s" (String.concat ", " ids) (show_type typ)
  | LetVal (id, typ, f) -> sprintf "let %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (id, typ, f) -> sprintf "exists %s : %s : %s"
      id (show_type typ) (show_formula f)
  | _ -> assert false

type proof =
  | Steps of proof_step list
  | Formulas of formula list

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula * id option (* id, formula, name *)
  | Definition of id * typ * formula
  | Theorem of id * formula * proof option

let axiom_named name = function
  | Axiom (_id, f, Some n) when eq_icase n name -> Some f
  | _ -> None

let show_statement = function
  | TypeDecl id -> sprintf "type %s" id
  | ConstDecl (id, typ) -> sprintf "const %s : %s" id (show_type typ)
  | Axiom (id, f, _) -> sprintf "axiom %s: %s" id (show_formula f)
  | Definition (id, typ, f) ->
      sprintf "definition %s : %s ; %s" id (show_type typ) (show_formula f)
  | Theorem (name, t, _) -> sprintf "theorem %s: %s" name (show_formula t)
