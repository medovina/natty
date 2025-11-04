open Printf

open Logic
open Statement
open Util

let quote s =
  let s = str_replace "." "_" s in
  if is_lower (s.[0]) && String.for_all is_id_char s
    then s else sprintf "'%s'" (str_replace "'" "\\'" s)

(* Prefix uppercase constants with _ to avoid possible name clashes with
 * variables, which begin with uppercase letters. *)
let prefix_upper s =
    if is_upper s.[0] then "_" ^ s else s

let var_char v : string =
  if "a" <= v && v <= "z" then String.uppercase_ascii v
  else if "A" <= v && v <= "Z" then v ^ "_"
  else if "α" <= v && v <= "ω" then
    let i = Uchar.to_int (uchar v) - Uchar.to_int(uchar "α") in
    let c = Char.chr(i + Char.code('A')) in
    String.make 2 c  (* e.g. α → AA, β → BB *)
  else if v = "'" then "p"
  else if v = "·" then "Dot"
  else if v = "^" then "Exp"
  else if "₀" <= v && v <= "₉" then "_" ^ sub_to_digit v
  else failwith "bad variable name"

let to_var id : string =
  String.concat "" (map var_char (uchars id))

let rec thf_type typ =
  let rec f left typ = match typ with
    | Bool -> "$o"
    | Type -> "$tType"
    | Base id -> quote id
    | TypeVar id -> to_var id
    | Fun (t, u) ->
        let s = sprintf "%s > %s" (f true t) (f false u) in
        if left then sprintf "(%s)" s else s
    | Pi _ ->
        let (xs, typ) = gather_pi typ in
        let decls = xs |> map (fun x -> to_var x ^ ": $tType") in
        sprintf "!>[%s]: %s" (comma_join decls) (f true typ)
    | Product typs -> sprintf "[%s]" (comma_join (map thf_type typs))
  in f false typ

let binary = [("∧", "&"); ("∨", "|"); ("→", "=>"); ("↔", "<=>")]

let rec thf outer right f : string =
  let parens b s = if b && outer <> "" then sprintf "(%s)" s else s in
  match collect_args f with
    | (Const (c, _), args) when is_tuple_constructor c ->
        sprintf "[%s]" (comma_join (map thf_formula args))
    | _ ->
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
          | Const (id, typ) ->
              if id = _type then thf_type typ else quote (prefix_upper id)
          | Var (id, _) -> to_var id
          | App (g, h) ->
              let s = sprintf "%s @ %s" (thf "@" false g) (thf "@" true h) in
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
      (quote (id ^ "_decl")) (quote (prefix_upper id)) (thf_type typ) in
  let axiom name kind f =
    sprintf "%s, %s, %s" (quote name) kind (thf_formula f) in
  let type_decl t = sprintf "%s, type, %s: $tType" (quote (t ^ "_type")) (quote t) in
  let thm_or_hyp name kind f =
    [sprintf "%s, %s, %s" (quote ("thm_" ^ name)) kind (thf_formula f)] in
  let conv = function
    | TypeDecl (id, _) -> [type_decl id]
    | ConstDecl (id, typ) -> [const id typ]
    | Axiom (name, f, _) -> [axiom ("ax_" ^ name) "axiom" f]
    | Hypothesis (name, f) -> thm_or_hyp name "hypothesis" f
    | Definition (id, typ, f) -> [
        const id typ;
        axiom (id ^ "_def") "definition" f
        ]
    | Theorem (num, _, f, _, _) ->
        let kind = if is_conjecture then "conjecture" else "theorem" in
        thm_or_hyp num kind f
    | HAxiom _
    | HTheorem _ -> failwith "thf_statement" in
  unlines (map (sprintf "thf(%s).") (conv f))

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name using proven (stmt: statement option) =
  let f = thf_file dir (str_replace "." "_" name) in
  if not (Sys.file_exists f) then (
    let out = open_out f in
    stmt |> Option.iter (fun stmt ->
      let problem = Option.get (stmt_formula stmt) in
      let problem =
        if free_vars problem = [] then remove_universal problem else problem in
      fprintf out "%% Problem: %s\n\n" (show_formula problem));
    using |> iter (fun name ->
      fprintf out "include('../%s/%s.thf').\n" name name);
    if using <> [] then fprintf out "\n";
    let write is_last stmt = (
      fprintf out "%% %s\n" (show_statement false (mono_statement stmt));
      fprintf out "%s\n\n" (thf_statement is_last stmt)) in
    iter (write false) proven;
    Option.iter (write true) stmt;
    Out_channel.close out)

let base_name md = Filename.remove_extension (Filename.basename md.filename)

let export_module dir all_modules md =
  let module_name = base_name md in
  let subdir = mk_path dir module_name in
  mk_dir subdir;
  let using = map base_name (all_using md all_modules) in
  expand_proofs md.stmts true |> iter (fun (thm, known) ->
    match thm with
      | Theorem (num, name, _, _, _) ->
          let filename = String.concat ":" ([num] @ Option.to_list name) in
          write_thf subdir filename using (rev known) (Some thm)
      | _ -> failwith "theorem expected");
  write_thf subdir module_name [] md.stmts None
