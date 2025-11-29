open Printf

open Logic
open Options
open Util

type str = string

type pos = int * int   (* line number, column number *)

type range = pos * pos
let empty_range = ((0, 0), (0, 0))

type frange = string * range  (* filename, position *)

let show_pos (line, col) = sprintf "%d:%d" line col

let show_range (pos1, pos2) : string =
  if pos2 = (0, 0) then show_pos pos1
  else sprintf "%s - %s" (show_pos pos1) (show_pos pos2)

let encode_range ((line1, col1), (line2, col2)) : string =
  sprintf "@ %d %d %d %d" line1 col1 line2 col2

let decode_range s : range =
  if s = "" then empty_range else
  let words = String.split_on_char ' ' (string_from s 1) |>
    filter ((<>) "") |> map int_of_string in
  match words with
    | [line1; col1; line2; col2] -> ((line1, col1), (line2, col2))
    | _ -> failwith "decode_range"

let strip_range f : formula = match f with
  | App (Const (c, _), g) when starts_with "@" c -> g
  | _ -> f

let rec strip_ranges f : formula =
  map_formula strip_ranges (strip_range f)

let rec range_of f : range = match f with
  | App (Const (c, _), _) when starts_with "@" c -> decode_range c
  | App (Const ("(∀)", _), Lambda (_, _, g)) -> range_of g
  | _ -> empty_range

type chain = (id * formula * (string * range) list) list  (* op, formula, reason(s) *)

type proof_step =
  | Assert of chain
  | Let of (id * typ) list
  | LetDef of id * typ * formula
  | Assume of formula
  | IsSome of id list * typ * formula
  | Escape
  | Group of proof_step list

let mk_assert f = Assert [("", f, [])]

let is_assert f = function
  | Assert [(_, f', _)] when f = f' -> true
  | _ -> false

let is_assume = function
  | Assume _ -> true
  | _ -> false

let step_types step : typ list = match step with
  | Let ids_types -> unique (map snd ids_types)
  | LetDef (_, typ, _) | IsSome (_, typ, _) -> [typ]
  | _ -> []
  
let rec step_decl_vars = function
  | Let ids_types -> map fst ids_types
  | LetDef (id, _, _) -> [id]
  | IsSome (ids, _, _) -> ids
  | Group steps -> unique (concat_map step_decl_vars steps)
  | _ -> []

let rec step_formulas = function
  | Assert fs -> let+ (_, f, _) = fs in [f]
  | Let _ | Escape -> []
  | LetDef (_, _, f) -> [f]
  | Assume f -> [f]
  | IsSome (_, _, f) -> [f]
  | Group steps -> concat_map step_formulas steps

let step_free_vars step = unique @@
  let vars =
    concat_map free_vars_in_type (step_types step) @
    concat_map free_vars (step_formulas step) in
  match step with
    | IsSome (ids, _, _) -> subtract vars ids
    | _ -> vars

let step_free_type_vars step = unique @@
  concat_map free_type_vars_in_type (step_types step) @
  concat_map free_type_vars (step_formulas step)

let show_chain chain : string =
  let to_str (op, f, _) =
    let s = show_formula f in
    if op = "" then s else op ^ " " ^ s in
  unwords (map to_str chain)

let rec show_proof_step step : string = match step with
  | Assert chain -> sprintf "assert %s" (show_chain chain)
  | Let ids_types ->
      let show (id, typ) = sprintf "%s : %s" id (show_type typ) in
      "let " ^ comma_join (map show ids_types)
  | LetDef (_id, _typ, f) -> sprintf "let_def : %s" (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (ids, typ, f) -> sprintf "is_some %s : %s : %s"
      (comma_join ids) (show_type typ) (show_formula f)
  | Escape -> "escape"
  | Group steps ->
      sprintf "[%s]" (comma_join (map show_proof_step steps))

let is_function_definition = function
  | LetDef (_id, _typ, f) -> (match strip_range f with
      | Eq _ -> false
      | _ -> true)
  | _ -> false

type statement =
  | TypeDecl of id * string option  (* e.g. "ℤ", "integer" *)
  | ConstDecl of id * typ
  | Axiom of id * formula * string option (* id, formula, name *)
  | Hypothesis of id * formula
  | Definition of id * typ * formula
  | Theorem of
      { id: string; name: string option; formula: formula;
        steps: statement list list; by: id list; is_step: bool; range: range }
  | HAxiom of id * proof_step list * string option (* num, steps, name *)
  | HTheorem of
      { id: string; name: string option;
        steps: proof_step list; proof_steps: proof_step list }

let is_type_decl id = function
  | TypeDecl (id', _) when id = id' -> true
  | _ -> false

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
  | TypeDecl (id, _) | ConstDecl (id, _) | Axiom (id, _, _)
  | Hypothesis (id, _) | Definition (id, _, _)
  | Theorem { id; _ } | HAxiom (id, _, _) | HTheorem { id; _ } ->
      id

let with_stmt_id id = function
  | Hypothesis (_, formula) -> Hypothesis (id, formula)
  | Theorem thm -> Theorem { thm with id }
  | _ -> assert false

let stmt_prefix = function
  | Axiom _ -> "ax" | Theorem _ -> "thm" | Hypothesis _ -> "hyp"
  | Definition _ -> "def"
  | _ -> failwith "stmt_prefix"

let stmt_prefix_id sep stmt = stmt_prefix stmt ^ sep ^ stmt_id stmt
  
let stmt_ref = stmt_prefix_id ":"

let stmt_name = function
  | Axiom (_, _, name) -> name
  | Theorem { name; _ } -> name
  | _ -> None

let with_stmt_name name = function
  | Axiom (id, f, _) -> Axiom (id, f, name)
  | Theorem thm -> Theorem { thm with name }
  | _ -> failwith "with_stmt_name"

let stmt_kind = function
  | TypeDecl _ -> "type"
  | ConstDecl _ -> "const"
  | Axiom _ | HAxiom _ -> "axiom"
  | Hypothesis _ -> "hypothesis"
  | Definition _ -> "definition"
  | Theorem _ | HTheorem _ -> "theorem"

let stmt_id_name stmt =
  let base = stmt_kind stmt ^ " " ^ strip_prefix (stmt_id stmt) in
  match stmt with
  | Axiom (_, _, name)
  | Theorem { name; _ } -> 
      base ^ (match name with
        | Some name -> sprintf " (%s)" name
        | _ -> "")
  | _ -> base

let stmt_formula = function
  | Axiom (_, f, _) | Hypothesis (_, f) | Theorem { formula = f; _ } -> Some f
  | Definition (_id, _typ, f) -> Some f
  | _ -> None

let thm_by = function
  | Theorem { by; _ } -> by | _ -> failwith "thm_by"

let strip_proof stmt : statement = match stmt with
  | Theorem thm -> Theorem { thm with steps = [] }
  | stmt -> stmt

let show_statement multi s : string =
  let name = stmt_id_name s in
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
    | Theorem { formula = f; _ } -> show (name ^ ": ") f
    | HAxiom (id, _, _) -> "haxiom: " ^ id
    | HTheorem { id; _ } -> "htheorem: " ^ id

let rec map_statement1 id_fn typ_fn fn stmt =
  match stmt with
  | TypeDecl _ -> stmt
  | ConstDecl (id, typ) -> ConstDecl (id_fn typ id, typ_fn typ)
  | Axiom (id, f, name) -> Axiom (id, fn f, name)
  | Hypothesis (id, f) -> Hypothesis (id, fn f)
  | Definition (id, typ, f) -> Definition (id_fn typ id, typ_fn typ, fn f)
  | Theorem ({ formula = f; steps = esteps; _ } as thm) ->
      let map_proof esteps = map (map (map_statement1 id_fn typ_fn fn)) esteps in
      Theorem { thm with formula = fn f; steps = map_proof esteps }
  | HAxiom _
  | HTheorem _ -> failwith "map_statement1"

let map_statement = map_statement1 (fun _typ id -> id)

let map_stmt_formulas fn = map_statement Fun.id fn

let apply_types_in_stmt = map_statement without_pi apply_types_in_formula

let decl_var stmt : (id * typ) option = match stmt with
  | TypeDecl (id, _) -> Some (id, Type)
  | ConstDecl (i, typ) -> Some (i, typ)
  | Definition (i, typ, _f) -> Some (i, typ)
  | _ -> None

let is_const_decl id def : typ option =
  let* (i, typ) = decl_var def in
  if i = id then Some typ else None

let definition_id f : id =
  match is_eq_or_iff (strip_range (remove_universal f)) with
    | Some (f, _g) ->
        get_const_or_var (fst (collect_args f))
    | _ -> failwith "definition_id: definition expected"

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

type _module = {
  filename: string;
  using: string list;
  stmts: statement list;
}

let find_module modules name : _module =
    find (fun m -> m.filename = name) modules

let all_using md existing : _module list =
  let uses m = map (find_module existing) m.using in
  rev (tl (dsearch md uses))

let module_env md existing : statement list =
  concat_map (fun m -> m.stmts) (all_using md existing)

let expand_modules1 modules all_modules : (string * statement * statement list) list =
  let stmts =
    let+ m = modules in
    let env = map apply_types_in_stmt (module_env m all_modules) in
    let+ (stmt, known) =
      expand_proofs apply_types_in_stmt (map apply_types_in_stmt m.stmts) false in
    [(m.filename, stmt, env @ rev known)] in
  let stmts = match !(opts.from_thm) with
    | Some id -> stmts |> drop_while (fun (_filename, stmt, _known) -> not (match_thm stmt id))
    | None -> stmts in
  if (Option.is_some !(opts.only_thm) || Option.is_some !(opts.from_thm)) && stmts = [] then
    failwith "theorem not found";
  stmts

let expand_modules modules = expand_modules1 modules modules

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
