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
  | App (t, u) -> sprintf "%s(%s)" (show_term t) (show_term u)
  | Lambda (id, typ, t) -> sprintf "λ%s:%s.%s" id (show_type typ) (show_term t)
  | Eq (t, u) -> sprintf "%s = %s" (show_term t) (show_term u)

let const id = Const (id, unknown_type)

let not f = App (const "¬", f)

let exists id typ f = App (const "∃", Lambda (id, typ, f))

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of term

let show_statement = function
  | TypeDecl id -> sprintf "type %s" id
  | ConstDecl (id, typ) -> sprintf "const %s : %s" id (show_type typ)
  | Axiom t -> sprintf "axiom: %s" (show_term t)
