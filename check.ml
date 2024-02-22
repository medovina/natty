open List
open Printf

open Logic

let logical_consts = ["¬"; "→"; "∀"; "∃"]

let is_const id = function
  | ConstDecl (i, typ) when i = id -> Some typ
  | _ -> None

let check_const env id =
  match find_map (is_const id) env with
    | Some typ -> Const (id, typ)
    | None -> printf "undefined: %s\n" id; assert false

let rec check_formula env vars =
  let rec check = function
    | Const (id, _) as c ->
      if mem id logical_consts then c else check_const env id
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> Var (id, typ)
          | None -> check_const env id)
    | App (f, g) -> App (check f, check g)
    | Lambda (id, typ, f) ->
        Lambda (id, typ, check_formula env ((id, typ) :: vars) f)
    | Eq (t, u) -> Eq (check t, check u) in
  check

let check_stmt env = function
  | Axiom (name, f) -> Axiom (name, check_formula env [] f)
  | Theorem (name, f) -> Theorem (name, check_formula env [] f)
  | stmt -> stmt

let check_program stmts =
  let check env stmt = (stmt :: env, check_stmt env stmt) in
  snd (fold_left_map check [] stmts)
