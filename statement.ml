open Printf

open Logic
open Options
open Util

type str = string

type pos = int * int   (* line number, colum number *)

type range = pos * pos
let empty_range = ((0, 0), (0, 0))

let show_pos (line, col) = sprintf "%d:%d" line col

let show_range (pos1, pos2) =
  if pos2 = (0, 0) then show_pos pos1
  else sprintf "%s - %s" (show_pos pos1) (show_pos pos2)

type frange = string * range

type syntax = SType of typ | SFormula of formula
let mk_type_syntax t = SType t
let mk_formula_syntax f = SFormula f

let syntax_ref_eq x y = match x, y with
  | SType t, SType u -> t == u
  | SFormula f, SFormula g -> f == g
  | _, _ -> false

type proof_step =
  | Assert of formula
  | Let of (id * typ) list
  | LetVal of id * typ * formula
  | Assume of formula
  | IsSome of id list * typ * formula
  | Escape
  | Group of (proof_step * range) list

type proof_step_r = proof_step * range

let mk_assert f = Assert f

let is_assume = function
  | Assume _ -> true
  | _ -> false

let step_types step : typ list = match step with
  | Let ids_types -> unique (map snd ids_types)
  | LetVal (_, typ, _) | IsSome (_, typ, _) -> [typ]
  | _ -> []
  
let rec step_decl_vars = function
  | Let ids_types -> map fst ids_types
  | LetVal (id, _, _) -> [id]
  | IsSome (ids, _, _) -> ids
  | Group steps -> unique (concat_map step_decl_vars (map fst steps))
  | _ -> []

let rec step_free_vars = function
  | Assert f -> free_vars f
  | LetVal (_, _, f) -> free_vars f
  | Assume f -> free_vars f
  | IsSome (ids, _, f) -> subtract (free_vars f) ids
  | Group steps -> unique (concat_map step_free_vars (map fst steps))
  | _ -> []

let rec show_proof_step = function
  | Assert f -> sprintf "assert %s" (show_formula f)
  | Let ids_types ->
      let show (id, typ) = sprintf "%s : %s" id (show_type typ) in
      "let " ^ comma_join (map show ids_types)
  | LetVal (id, typ, f) -> sprintf "let_val %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (ids, typ, f) -> sprintf "is_some %s : %s : %s"
      (comma_join ids) (show_type typ) (show_formula f)
  | Escape -> "escape"
  | Group steps ->
      sprintf "[%s]" (comma_join (map show_proof_step (map fst steps)))

type statement =
  | TypeDecl of id * string option  (* e.g. "ℤ", "integer" *)
  | ConstDecl of id * typ
  | Axiom of id * formula * string option (* num, formula, name *)
  | Hypothesis of id * formula
  | Definition of id * typ * formula
  | Theorem of id * string option * formula * statement list list * range
  | HTheorem of id * string option * formula * (proof_step * range) list * range

let is_type_decl id = function
  | TypeDecl (id', _) when id = id' -> true
  | _ -> false

let is_hypothesis = function
  | Hypothesis _ -> true
  | _ -> false

let is_theorem = function
  | Theorem _ -> true
  | _ -> false

let stmt_id = function
  | TypeDecl (id, _)
  | ConstDecl (id, _)
  | Axiom (id, _, _)
  | Hypothesis (id, _)
  | Definition (id, _, _)
  | Theorem (id, _, _, _, _)
  | HTheorem (id, _, _, _, _) -> id

let set_stmt_id id = function
  | Hypothesis (_, formula) -> Hypothesis (id, formula)
  | Theorem (_, name, formula, proof, range) -> Theorem (id, name, formula, proof, range)
  | _ -> assert false

let stmt_kind = function
  | TypeDecl _ -> "type"
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom"
  | Hypothesis _ -> "hypothesis"
  | Definition _ -> "definition"
  | Theorem _ -> "theorem"
  | HTheorem _ -> failwith "stmt_kind"

let stmt_name stmt =
  let base = stmt_kind stmt ^ " " ^ stmt_id stmt in
  match stmt with
  | Axiom (_, _, name)
  | Theorem (_, name, _, _, _) -> 
      base ^ (match name with
        | Some name -> sprintf " (%s)" name
        | _ -> "")
  | _ -> base

let stmt_formula = function
  | Axiom (_, f, _) | Hypothesis (_, f) | Theorem (_, _, f, _, _) -> Some f
  | Definition (_id, _typ, f) -> Some f
  | _ -> None

let rec map_statement1 id_fn typ_fn fn stmt = match stmt with
  | TypeDecl _ -> stmt
  | ConstDecl (id, typ) -> ConstDecl (id_fn typ id, typ_fn typ)
  | Axiom (id, f, name) -> Axiom (id, fn f, name)
  | Hypothesis (id, f) -> Hypothesis (id, fn f)
  | Definition (id, typ, f) -> Definition (id_fn typ id, typ_fn typ, fn f)
  | Theorem (id, name, f, esteps, range) ->
      let map_proof esteps = map (map (map_statement1 id_fn typ_fn fn)) esteps in
      Theorem (id, name, fn f, map_proof esteps, range)
  | HTheorem _ -> failwith "map_statement1"

let map_statement = map_statement1 (fun _typ id -> id)

let map_stmt_formulas fn = map_statement Fun.id fn

let mono_statement = map_statement without_pi implicit_formula

let decl_var = function
  | TypeDecl (id, _) -> Some (id, Fun (Base id, Bool))   (* universal set for type *)
  | ConstDecl (i, typ) -> Some (i, typ)
  | Definition (i, typ, _f) -> Some (i, typ)
  | _ -> None

let is_const id def =
  let* (i, typ) = decl_var def in
  if i = id then Some typ else None

let show_statement multi s : string =
  let name = stmt_name s in
  let show prefix f = indent_with_prefix prefix (show_formula_multi multi f) in
  match s with
    | TypeDecl _ -> name
    | ConstDecl (id, typ) ->
        sprintf "const %s : %s" (without_type_suffix id) (show_type typ)
    | Axiom (_, f, _) | Hypothesis (_, f) -> show (name ^ ": ") f
    | Definition (id, typ, f) ->
        let prefix =
          sprintf "definition (%s: %s): " (without_type_suffix id) (show_type typ) in
        show prefix f
    | Theorem (_, _, f, _, _) -> show (name ^ ": ") f
    | HTheorem _ -> failwith "show_statement"

let number_hypotheses name stmts =
  let f n = function
    | (Hypothesis _) as hyp ->
        let hyp_name = sprintf "%s.h%d" name n in
        (n + 1, set_stmt_id hyp_name hyp)
    | stmt -> (n, stmt) in
  snd (fold_left_map f 1 stmts)

let match_thm_id thm_id selector = starts_with selector thm_id

let match_thm thm selector = match_thm_id (stmt_id thm) selector

let expand_proofs stmts with_full : (statement * statement list) list =
  let only_thm = !(opts.only_thm) in
  let rec expand known = function
    | stmt :: stmts ->
        let thms = match stmt with
          | Theorem (id, _, _, fs, _) as thm ->
              let thm_known =
                if opt_for_all (match_thm_id id) only_thm &&
                  (with_full || fs = [])
                then [(thm, known)] else [] in
              thm_known @
                (fs |> filter_mapi (fun j stmts ->
                  let step_name = sprintf "%s.s%d" id (j + 1) in
                  if opt_for_all (match_thm_id step_name) only_thm then
                    let (hypotheses, conjecture) = split_last stmts in
                    Some (set_stmt_id step_name conjecture,
                          rev (number_hypotheses id hypotheses) @ known)
                  else None))
          | _ -> [] in
        thms @ expand (stmt :: known) stmts
    | [] -> [] in
  expand [] stmts

type _module = {
  filename: string;
  using: string list;
  stmts: statement list;
  syntax_map : (syntax * range) list; 
}

let find_module modules name : _module =
    find (fun m -> m.filename = name) modules

let all_using md existing : _module list =
  let uses m = map (find_module existing) m.using in
  rev (tl (dsearch md uses))

let module_env md existing : statement list =
  concat_map (fun m -> m.stmts) (all_using md existing)

let expand_modules modules : (string * statement * statement list) list =
  let stmts =
    let+ m = modules in
    let env = map mono_statement (module_env m modules) in
    let+ (stmt, known) = expand_proofs (m.stmts) false in
    [(m.filename, mono_statement stmt, env @ rev known)] in
  let stmts = match !(opts.from_thm) with
    | Some id -> stmts |> drop_while (fun (_filename, stmt, _known) -> not (match_thm stmt id))
    | None -> stmts in
  if (Option.is_some !(opts.only_thm) || Option.is_some !(opts.from_thm)) && stmts = [] then
    failwith "theorem not found";
  stmts

let write_thm_info md =
  let thms = filter is_theorem md.stmts in
  let thm_steps = function
    | Theorem (_, _, _, steps, _) -> steps
    | _ -> assert false in
  let step_groups = map thm_steps thms |> filter (fun steps -> steps <> []) in
  printf "%s: %d theorems (%d with proofs, %d without); %d proof steps\n"
    md.filename
    (length thms) (length step_groups) (length thms - length step_groups)
    (length (concat step_groups))
