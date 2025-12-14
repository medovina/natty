open Printf

open Logic
open Module
open Options
open Util

type str = string

type statement =
  | ConstDecl of id * typ
  | Axiom of id * formula * string option (* id, formula, name *)
  | Hypothesis of id * formula
  | Definition of id * typ * formula
  | Theorem of
      { id: string; name: string option; formula: formula;
        steps: statement list list; by: id list; is_step: bool; range: range }

let is_hypothesis = function
  | Hypothesis _ -> true | _ -> false

let is_definition = function
  | Definition _ -> true | _ -> false

let is_theorem = function
  | Theorem _ -> true | _ -> false

let is_step = function
  | Theorem { is_step = true; _ } -> true
  | _ -> false

let stmt_id = function
  | ConstDecl (id, _) | Axiom (id, _, _)
  | Hypothesis (id, _) | Definition (id, _, _)
  | Theorem { id; _ } -> id

let with_stmt_id id = function
  | Hypothesis (_, formula) -> Hypothesis (id, formula)
  | Theorem thm -> Theorem { thm with id }
  | _ -> assert false

let stmt_prefix = function
  | ConstDecl _ -> "const"
  | Axiom _ -> "ax" | Hypothesis _ -> "hyp" | Definition _ -> "def"
  | Theorem _ -> "thm"

let stmt_prefix_id sep stmt = stmt_prefix stmt ^ sep ^ stmt_id stmt
  
let stmt_ref = stmt_prefix_id ":"

let stmt_name = function
  | Axiom (_, _, name) -> name
  | Theorem { name; _ } -> name
  | _ -> None

let stmt_kind = function
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom"
  | Hypothesis _ -> "hypothesis"
  | Definition _ -> "definition"
  | Theorem _ -> "theorem"

let stmt_id_name stmt : string =
  let base = stmt_kind stmt ^ " " ^ strip_prefix (stmt_id stmt) in
  match stmt with
  | Axiom (_, _, name)
  | Theorem { name; _ } -> 
      base ^ (match name with
        | Some name -> sprintf " (%s)" name
        | _ -> "")
  | _ -> base

let stmt_formula stmt : formula option = match stmt with
  | Axiom (_, f, _) | Hypothesis (_, f) | Theorem { formula = f; _ } -> Some f
  | Definition (_id, _typ, f) -> Some f
  | _ -> None

let get_stmt_formula f : formula = Option.get (stmt_formula f)

let thm_by = function
  | Theorem { by; _ } -> by | _ -> failwith "thm_by"

let strip_proof stmt : statement = match stmt with
  | Theorem thm -> Theorem { thm with steps = [] }
  | stmt -> stmt

let show_statement multi s : string =
  let name = stmt_id_name s in
  let show prefix f = indent_with_prefix prefix (show_formula_multi multi f) in
  match s with
    | ConstDecl (id, Type) -> "type " ^ id
    | ConstDecl (id, typ) ->
        sprintf "const %s : %s" (without_type_suffix id) (show_type typ)
    | Axiom (_, f, _) | Hypothesis (_, f) -> show (name ^ ": ") f
    | Definition (id, typ, f) ->
        let prefix =
          sprintf "definition (%s: %s): " (without_type_suffix id) (show_type typ) in
        show prefix f
    | Theorem { formula = f; _ } -> show (name ^ ": ") f

let rec map_statement1 id_fn typ_fn fn stmt =
  match stmt with
  | ConstDecl (id, typ) -> ConstDecl (id_fn typ id, typ_fn typ)
  | Axiom (id, f, name) -> Axiom (id, fn f, name)
  | Hypothesis (id, f) -> Hypothesis (id, fn f)
  | Definition (id, typ, f) -> Definition (id_fn typ id, typ_fn typ, fn f)
  | Theorem ({ formula = f; steps = esteps; _ } as thm) ->
      let map_proof esteps = map (map (map_statement1 id_fn typ_fn fn)) esteps in
      Theorem { thm with formula = fn f; steps = map_proof esteps }

let map_statement = map_statement1 (fun _typ id -> id)

let map_stmt_formulas fn = map_statement Fun.id fn

let apply_types_in_stmt = map_statement without_pi apply_types_in_formula

let decl_var stmt : (id * typ) option = match stmt with
  | ConstDecl (i, typ) -> Some (i, typ)
  | _ -> None

let is_const_decl id def : typ option =
  let* (i, typ) = decl_var def in
  if i = id then Some typ else None

let is_type_decl id = function
  | ConstDecl (id', Type) when id = id' -> true
  | _ -> false

let number_hypotheses name stmts =
  let f n = function
    | (Hypothesis _) as hyp ->
        let hyp_name = sprintf "%s.h%d" name n in
        (n + 1, with_stmt_id hyp_name hyp)
    | stmt -> (n, stmt) in
  snd (fold_left_map f 1 stmts)

let match_thm_id thm_id selector =
  thm_id = selector || starts_with (selector ^ ".") thm_id

let match_thm thm selector = match_thm_id (stmt_id thm) selector

let expand_proofs apply_types stmts with_full : (statement * statement list) list =
  let only_thm = !(opts.only_thm) in
  let rec expand known = function
    | stmt :: stmts ->
        let thms = match stmt with
          | Theorem { id; steps = fs; _ } as thm ->
              let thm_known =
                if opt_for_all (match_thm_id id) only_thm &&
                  (with_full || fs = [])
                then [(thm, known)] else [] in
              thm_known @
                (fs |> filter_mapi (fun j stmts ->
                  let step_name = sprintf "%s.s%d" id (j + 1) in
                  if opt_for_all (match_thm_id step_name) only_thm then
                    let (hypotheses, conjecture) = split_last (map apply_types stmts) in
                    Some (with_stmt_id step_name conjecture,
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
    let env = map apply_types_in_stmt (module_env m all_modules) in
    let+ (stmt, known) =
      expand_proofs apply_types_in_stmt (map apply_types_in_stmt m.stmts) false in
    let known = rev known in
    [(m.filename, stmt, env @ known, known)] in
  let stmts = match !(opts.from_thm) with
    | Some id -> stmts |> drop_while (fun (_, stmt, _, _) -> not (match_thm stmt id))
    | None -> stmts in
  if (opt_is_some !(opts.only_thm) || opt_is_some !(opts.from_thm)) && stmts = [] then
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
