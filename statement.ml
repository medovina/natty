open Printf

open Logic
open Module
open Options
open Util

type str = string

type stmt_ref =
  | NameRef of string
  | LabelRef of string * string   (* kind, label *)

let parse_ref r : stmt_ref =
  if r.[0] = '$' then
    match str_words (string_from r 1) with
      | [kind; label] ->
          let kind =
            if kind = "corollary" || kind = "lemma" then "theorem" else kind in
          LabelRef (kind, label)
      | _ -> failwith "parse_ref"
  else NameRef r

let show_ref = function
  | NameRef s -> s
  | LabelRef (kind, label) -> kind ^ ":" ^ label

type statement =
  | ConstDecl of { id : id; typ : typ; constructor: bool }
  | Axiom of
      { label: string; formula: formula; name: string option;
        defined: (id * typ) option }
  | Hypothesis of { label: string; formula: formula; name: string option }
  | Definition of { label: string; id: string; typ: typ; formula: formula }
  | Theorem of
      { label: string; name: string option; formula: formula;
        steps: statement list list; by: stmt_ref list; is_step: bool; range: range }

let mk_const_decl id typ =
  ConstDecl { id; typ; constructor = false }

let mk_const_decl' constructor (id, typ) =
  ConstDecl { id; typ; constructor }

let is_hypothesis = function
  | Hypothesis _ -> true | _ -> false

let is_definition = function
  | Definition _ -> true | _ -> false

let stmt_defined = function
  | Definition { id = c; _ } -> Some c
  | Axiom { defined = Some (c, _); _ } -> Some c
  | _ -> None

let is_definitional stmt = is_some (stmt_defined stmt)

let is_theorem = function
  | Theorem _ -> true | _ -> false

let is_step = function
  | Theorem { is_step = true; _ } -> true
  | _ -> false

let stmt_label = function
  | ConstDecl { id; _ } -> id
  | Axiom { label; _ } | Theorem { label; _ }
  | Hypothesis { label; _ } | Definition { label; _ } -> label

let with_stmt_label label = function
  | Hypothesis hyp -> Hypothesis { hyp with label }
  | Theorem thm -> Theorem { thm with label }
  | _ -> assert false

let stmt_kind = function
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom" | Hypothesis _ -> "hypothesis" | Definition _ -> "definition"
  | Theorem _ -> "theorem"

let stmt_name = function
  | Axiom { name; _ } | Hypothesis { name; _ } | Theorem { name; _ } -> name
  | _ -> None

let stmt_kind = function
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom"
  | Hypothesis _ -> "hypothesis"
  | Definition _ -> "definition"
  | Theorem _ -> "theorem"

let stmt_label_name stmt : string =
  let base = stmt_kind stmt ^ " " ^ strip_prefix (stmt_label stmt) in
  match stmt with
  | Axiom { name; _ }
  | Theorem { name; _ } -> 
      base ^ (match name with
        | Some name -> sprintf " (%s)" name
        | _ -> "")
  | _ -> base

let stmt_formula stmt : formula option = match stmt with
  | Axiom { formula = f; _ } | Hypothesis { formula = f; _ }
  | Theorem { formula = f; _ } | Definition { formula = f; _ } -> Some f
  | _ -> None

let get_stmt_formula f : formula = Option.get (stmt_formula f)

let thm_by = function
  | Theorem { by; _ } -> by | _ -> failwith "thm_by"

let strip_proof stmt : statement = match stmt with
  | Theorem thm -> Theorem { thm with steps = [] }
  | stmt -> stmt

let show_statement multi s : string =
  let name = stmt_label_name s in
  let show prefix f = indent_with_prefix prefix (show_formula_multi multi f) in
  match s with
    | ConstDecl { id; typ = Type; _ } -> "type " ^ id
    | ConstDecl { id; typ; _ } ->
        sprintf "const %s : %s" (without_type_suffix id) (show_type typ)
    | Axiom { formula = f; _ } | Hypothesis { formula = f; _ } -> show (name ^ ": ") f
    | Definition { id; typ; label = _; formula = f } ->
        let prefix =
          sprintf "definition (%s: %s): " (without_type_suffix id) (show_type typ) in
        show prefix f
    | Theorem { formula = f; _ } -> show (name ^ ": ") f

let rec map_statement1 id_fn typ_fn fn stmt =
  match stmt with
  | ConstDecl { id;  typ; constructor } ->
      ConstDecl { id = id_fn typ id; typ = typ_fn typ; constructor }
  | Axiom { label; formula; name; defined } ->
      Axiom { label; formula = fn formula; name;
              defined = let* (id, typ) = defined in Some (id_fn typ id, typ_fn typ) }
  | Hypothesis hyp -> Hypothesis { hyp with formula = fn hyp.formula }
  | Definition { label; id; typ; formula = f } ->
      Definition { label; id = id_fn typ id; typ = typ_fn typ; formula = fn f }
  | Theorem ({ formula = f; steps = esteps; _ } as thm) ->
      let map_proof esteps = map (map (map_statement1 id_fn typ_fn fn)) esteps in
      Theorem { thm with formula = fn f; steps = map_proof esteps }

let map_statement = map_statement1 (fun _typ id -> id)

let map_stmt_formulas fn = map_statement Fun.id fn

let apply_types_in_stmt = map_statement without_pi apply_types_in_formula

let decl_var stmt : (id * typ) option = match stmt with
  | ConstDecl { id; typ; _ } -> Some (id, typ)
  | _ -> None

let is_const_decl id def : typ option =
  let* (i, typ) = decl_var def in
  if i = id then Some typ else None

let is_type_decl id = function
  | ConstDecl { id = id'; typ = Type; _ } when id = id' -> true
  | _ -> false

let match_ref r stmt = match r with
  | NameRef s -> stmt_name stmt = Some s
  | LabelRef ("_", label) -> stmt_label stmt = label
  | LabelRef (kind, label) ->
      (stmt_kind stmt, stmt_label stmt) = (kind, label)

let number_hypotheses name stmts =
  let f n = function
    | (Hypothesis _) as hyp ->
        let hyp_name = sprintf "%s.h%d" name n in
        (n + 1, with_stmt_label hyp_name hyp)
    | stmt -> (n, stmt) in
  snd (fold_left_map f 1 stmts)

let match_thm_id thm_id selector =
  thm_id = selector || starts_with (selector ^ ".") thm_id

let match_thm thm selector = match_thm_id (stmt_label thm) selector

let expand_proofs apply_types stmts with_full : (statement * statement list) list =
  let only_thm = !(opts.only_thm) in
  let rec expand known = function
    | stmt :: stmts ->
        let thms = match stmt with
          | Theorem { label = id; steps = fs; _ } as thm ->
              let thm_known =
                if opt_for_all (match_thm_id id) only_thm && (with_full || fs = [])
                then [(thm, known)] else [] in
              thm_known @
                (fs |> filter_mapi (fun j stmts ->
                  let step_name = sprintf "%s.s%d" id (j + 1) in
                  if opt_for_all (match_thm_id step_name) only_thm then
                    let (hypotheses, conjecture) = split_last (map apply_types stmts) in
                    Some (with_stmt_label step_name conjecture,
                          rev (number_hypotheses id hypotheses) @ known)
                  else None))
          | _ -> [] in
        thms @ expand (stmt :: known) stmts
    | [] -> [] in
  expand [] stmts

let expand_modules1 modules all_modules :
    (string * statement * statement list * statement list) list =
  let stmts =
    let+ m = modules in
    let using_env = map apply_types_in_stmt (module_env m all_modules) in
    let+ (stmt, local_env) =
      expand_proofs apply_types_in_stmt (map apply_types_in_stmt m.stmts) false in
    [(m.filename, stmt, using_env, rev local_env)] in
  let stmts = match !(opts.from_thm) with
    | Some id -> stmts |> drop_while (fun (_, stmt, _, _) -> not (match_thm stmt id))
    | None -> stmts in
  if (is_some !(opts.only_thm) || is_some !(opts.from_thm)) && stmts = [] then
    failwith "theorem not found";
  stmts

let expand_modules modules :
    (string * statement * statement list * statement list) list =
  expand_modules1 modules modules

let write_thm_info md =
  let thms = filter is_theorem md.stmts in
  let thm_steps = function
    | Theorem { steps; _ } -> steps
    | _ -> assert false in
  let step_groups = map thm_steps thms |> filter (fun steps -> steps <> []) in
  printf "%s: %d theorems (%d with proofs, %d without); %d proof steps\n"
    md.filename
    (length thms) (length step_groups) (length thms - length step_groups)
    (length (concat step_groups))

type smodule = statement _module
