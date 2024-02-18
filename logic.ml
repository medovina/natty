open Printf

type id = string

type typ =
  | Bool
  | Fun of typ * typ
  | Base of id

let rec show_type = function
  | Bool -> "𝔹"
  | Fun (t, u) -> sprintf "(%s → %s)" (show_type t) (show_type u)
  | Base id -> id

let unknown_type = Base "?"

type term =
  | Const of id * typ
  | Var of id * typ
  | App of term * term
  | Lambda of id * typ * term
  | Eq of term * term

let rec show_term = function
  | Const (id, _typ) -> id
  | Var (id, _typ) -> id
  | App (t, u) -> (
      match t, u with
        | App (Const ("→", _), t), _ ->
            sprintf "[%s → %s]" (show_term t) (show_term u)
        | Const (q, _), Lambda (id, typ, u) when q == "∀" || q == "∃" ->
            sprintf "%s%s:%s.%s" q id (show_type typ) (show_term u)
        | _, _ -> sprintf "%s(%s)" (show_term t) (show_term u) )
  | Lambda (id, typ, t) -> sprintf "λ%s:%s.%s" id (show_type typ) (show_term t)
  | Eq (t, u) -> sprintf "%s = %s" (show_term t) (show_term u)

let const id = Const (id, unknown_type)

let not f = App (const "¬", f)

let implies f g = App (App (const "→", f), g)

let binder name id typ f = App (const name, Lambda (id, typ, f))
let binder' name (id, typ) f = binder name id typ f

let for_all = binder "∀"
let for_all' = binder' "∀"

let exists = binder "∃"

let for_all_n ids typ f = List.fold_right (fun id f -> for_all id typ f) ids f

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of term

let show_statement = function
  | TypeDecl id -> sprintf "type %s" id
  | ConstDecl (id, typ) -> sprintf "const %s : %s" id (show_type typ)
  | Axiom t -> sprintf "axiom: %s" (show_term t)
