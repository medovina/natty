open List
open Printf

open Logic
open Util

let parens b s = if b then sprintf "(%s)" s else s

let quote s = if is_lower (s.[0]) then s else sprintf "'%s'" s

let base_type = function
  | "ℕ" -> "nat"
  | id -> id

let thf_type =
  let rec f left = function
  | Bool -> "$o"
  | Base id -> base_type id
  | Fun (t, u) ->
      let s = sprintf "%s > %s" (f true t) (f false u) in
      if left then sprintf "(%s)" s else s
  in f false

let rec gather_quant q f = match kind f with
  | Quant (q', id, typ, u) when q = q' ->
      let (qs, f) = gather_quant q u in ((id, typ) :: qs, f)
  | _ -> ([], f)

let binary = [("∧", "&"); ("→", "=>")]

let rec thf outer right f = match kind f with
  | Binary (op, t, u) when mem op binary_ops ->
      let s = sprintf "%s %s %s"
        (thf op false t) (assoc op binary) (thf op true u) in
      parens (op != "∧" || op != outer) s
  | Quant (q, id, typ, u) ->
      let (ids_typs, f) = gather_quant q u in
      quant (if q = "∀" then "!" else "?") ((id, typ) :: ids_typs) f
  | _ -> match f with
    | Const (id, _) -> quote id
    | Var (id, _) -> capitalize id
    | App (t, u) -> (
        match t, u with
          | Const ("¬", _), Eq(t, u) ->
              sprintf "(%s != %s)" (thf "=" false t) (thf "=" true u)
          | Const ("¬", _), u -> sprintf "~ %s" (thf "¬" false u)
          | _, _ ->
              let s = sprintf "%s @ %s" (thf "@" false t) (thf "@" true u) in
              parens (outer != "@" || right) s
              ) 
    | Lambda (id, typ, f) -> quant "^" [(id, typ)] f
    | Eq (t, u) ->
        sprintf "(%s = %s)" (thf "=" false t) (thf "=" true u)

and quant q ids_typs f =
  let pair (id, typ) = sprintf "%s: %s" (capitalize id) (thf_type typ) in
  let pairs = String.concat ", " (map pair ids_typs) in
  sprintf "%s[%s]: %s" q pairs (thf q false f)

and thf_formula f = thf "" false f

let thf_statement is_conjecture f =
  let conv = function
    | TypeDecl id ->
        let t = base_type id in
        sprintf "%s_type, type, %s: $tType" t t
    | ConstDecl (id, typ) ->
        sprintf "%s, type, %s: %s" (quote (id ^ "_decl")) (quote id) (thf_type typ)
    | Axiom (name, f) ->
        sprintf "%s, axiom, %s" (quote name) (thf_formula f)
    | Theorem (name, f) ->
        let t = if is_conjecture then "conjecture" else "theorem" in
        sprintf "%s, %s, %s" (quote name) t (thf_formula f) in
  sprintf "thf(%s)." (conv f)
