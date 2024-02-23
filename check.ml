open List
open Printf

open Logic

let is_const id = function
  | ConstDecl (i, typ) when i = id -> Some typ
  | Definition (i, typ, _f) when i = id -> Some typ
  | _ -> None

let check_const env id =
  match find_map (is_const id) env with
    | Some typ -> (Const (id, typ), typ)
    | None -> printf "undefined: %s\n" id; assert false

let rec subtype t u = match t, u with
  | Bool, Bool -> true
  | Fun (t, u), Fun (t', u') -> subtype t t' && subtype u u'
  | Base id, Base id' when id = id' -> true
  | _, Base "_" -> true
  | _ -> false

let rec check_formula env vars =
  let rec check formula = match formula with
    | Const (id, _) as c -> (
        match assoc_opt id logical_consts with
          | Some typ -> (c, typ)
          | None -> check_const env id)
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> (Var (id, typ), typ)
          | None -> check_const env id)
    | App (f, g) ->
        let (f, typ_f), (g, typ_g) = check f, check g in (
        match typ_f with
          | Fun (tg, u) ->
              if subtype typ_g tg then (App (f, g), u)
              else failwith ("type mismatch: " ^ show_formula formula)
          | _ -> check (binop "·" f g))
    | Lambda (id, typ, f) ->
        let (f, typ_f) = check_formula env ((id, typ) :: vars) f in
        (Lambda (id, typ, f), Fun (typ, typ_f))
    | Eq (f, g) ->
        let (f, typ_f), (g, typ_g) = check f, check g in
        if typ_f = typ_g then (Eq (f, g), Bool)
        else failwith ("type mismatch: " ^ show_formula formula) in
  check

let top_check env f =
  let (f, typ) = check_formula env [] f in
  if typ = Bool then f else failwith ("bool expected: " ^ show_formula f)

let check_stmt env stmt =
  match stmt with
    | Axiom (name, f) -> Axiom (name, top_check env f)
    | Definition (id, typ, f) ->
        Definition (id, typ, top_check (stmt :: env) f)
    | Theorem (name, f) -> Theorem (name, top_check env f)
    | stmt -> stmt

let check_program stmts =
  let check env stmt = (stmt :: env, check_stmt env stmt) in
  snd (fold_left_map check [] stmts)
