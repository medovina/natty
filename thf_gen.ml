open Printf

open Logic
open Statement
open Util

let quote s =
  let s = str_replace "." "_" s in
  if is_lower (s.[0]) && String.for_all is_id_char s
    then s else sprintf "'%s'" s

let thf_type typ =
  let rec f left = function
    | Bool -> "$o"
    | Base id -> quote id
    | Fun (t, u) ->
        let s = sprintf "%s > %s" (f true t) (f false u) in
        if left then sprintf "(%s)" s else s
    | Product _ -> failwith "thf_type"
  in f false typ

let binary = [("∧", "&"); ("∨", "|"); ("→", "=>"); ("↔", "<=>")]

(* Suffix uppercase identifiers with _ to avoid name clashes e.g. between
 * variables G and g, since all variable names will be made uppercase. *)
let suffix_upper s =
    if is_upper s.[0] then
        let (s, typ) = split_type_suffix s in
        s ^ "_" ^ typ
    else s

let to_var id = capitalize (suffix_upper (str_replace "'" "_" id))

let rec thf outer right f : string =
  let parens b s = if b && outer <> "" then sprintf "(%s)" s else s in
  match bool_kind f with
    | True -> "$true"
    | False -> "$false"
    | Not f -> (match f with
      | Eq(t, u) ->
          parens true (sprintf "%s != %s" (thf "=" false t) (thf "=" true u))
      | _ -> sprintf "~ %s" (thf "¬" false f))
    | Binary (op, _, t, u) ->
        let s = sprintf "%s %s %s"
          (thf op false t) (assoc op binary) (thf op true u) in
        parens (op <> "∧" && op <> "∨" || op <> outer) s
    | Quant (q, id, typ, u) ->
        let (ids_typs, f) = gather_quant q u in
        quant (if q = "∀" then "!" else "?") ((id, typ) :: ids_typs) f
    | _ -> match f with
      | Const (id, _) -> quote (suffix_upper id)
      | Var (id, _) -> to_var id
      | App (t, u) ->
          let s = sprintf "%s @ %s" (thf "@" false t) (thf "@" true u) in
          parens (outer <> "@" || right) s
      | Lambda (id, typ, f) -> quant "^" [(id, typ)] f
      | Eq (t, u) ->
          parens true (sprintf "%s = %s" (thf "=" false t) (thf "=" true u))

and quant q ids_typs f =
  let pair (id, typ) = sprintf "%s: %s" (to_var id) (thf_type typ) in
  let pairs = comma_join (map pair ids_typs) in
  sprintf "%s[%s]: %s" q pairs (thf q false f)

and thf_formula f = thf "" false f

let thf_statement is_conjecture f : string =
  let const id typ =
    sprintf "%s, type, %s: %s"
      (quote (id ^ "_decl")) (quote (suffix_upper id)) (thf_type typ) in
  let axiom name kind f =
    sprintf "%s, %s, %s" (quote name) kind (thf_formula f) in
  let type_decl t = sprintf "%s, type, %s: $tType" (quote (t ^ "_type")) (quote t) in
  let thm_or_hyp name kind f =
    [sprintf "%s, %s, %s" (quote ("thm_" ^ name)) kind (thf_formula f)] in
  let conv = function
    | TypeDecl id -> [type_decl id]
    | ConstDecl (id, typ) -> [const id typ]
    | Axiom (name, f, _) -> [axiom ("ax_" ^ name) "axiom" f]
    | Hypothesis (name, f) -> thm_or_hyp name "hypothesis" f
    | Definition (id, typ, f) -> [
        const id typ;
        axiom (id ^ "_def") "definition" f
        ]
    | Theorem (num, _, f, _, _) ->
        let kind = if is_conjecture then "conjecture" else "theorem" in
        thm_or_hyp num kind f in
  unlines (map (sprintf "thf(%s).") (conv f))

