open Printf

open Logic
open Options
open Util

type pos = int * int   (* line number, colum number *)

type range = Range of pos * pos
let empty_range = Range ((0, 0), (0, 0))

let show_range (Range ((line1, col1), (line2, col2))) =
  sprintf "%d:%d - %d:%d" line1 col1 line2 col2

type syntax = Type of typ | Formula of formula
let mk_type_syntax t = Type t
let mk_formula_syntax f = Formula f

let syntax_ref_eq x y = match x, y with
  | Type t, Type u -> t == u
  | Formula f, Formula g -> f == g
  | _, _ -> false

type proof_step =
  | Assert of formula
  | Let of id list * typ
  | LetVal of id * typ * formula
  | Assume of formula
  | IsSome of id list * typ * formula
  | Escape
  | Group of (proof_step * range) list

let mk_assert f = Assert f

let step_types = function
  | Let (_, typ) | LetVal (_, typ, _) | IsSome (_, typ, _) -> [typ]
  | _ -> []
  
let rec step_decl_vars = function
  | Let (ids, _) -> ids
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
  | Let (ids, typ) -> sprintf "let %s : %s" (comma_join ids) (show_type typ)
  | LetVal (id, typ, f) -> sprintf "let_val %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (ids, typ, f) -> sprintf "is_some %s : %s : %s"
      (comma_join ids) (show_type typ) (show_formula f)
  | Escape -> "escape"
  | Group steps ->
      sprintf "[%s]" (comma_join (map show_proof_step (map fst steps)))

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula * id option (* id, formula, descriptive name *)
  | Hypothesis of id * formula
  | Definition of id * typ * formula
  | Theorem of id * formula * proof option * range

and proof =
  | Steps of (proof_step * range) list
  | ExpandedSteps of statement list list

let mk_def id typ formula = Definition (id, typ, formula)

let is_hypothesis = function
  | Hypothesis _ -> true
  | _ -> false

let is_theorem = function
  | Theorem _ -> true
  | _ -> false

let stmt_id = function
  | TypeDecl id -> id
  | ConstDecl (id, _) -> id
  | Axiom (id, _, _) -> id
  | Hypothesis (id, _) -> id
  | Definition (id, _, _) -> id
  | Theorem (id, _, _, _) -> id

let set_stmt_id id = function
  | Hypothesis (_, formula) -> Hypothesis (id, formula)
  | Theorem (_, formula, proof, range) -> Theorem (id, formula, proof, range)
  | _ -> assert false

let stmt_name stmt = (match stmt with
  | TypeDecl _ -> "type"
  | ConstDecl _ -> "const"
  | Axiom _ -> "axiom"
  | Hypothesis _ -> "hypothesis"
  | Definition _ -> "definition"
  | Theorem _ -> "theorem") ^ " " ^ stmt_id stmt

let stmt_formula = function
  | Axiom (_, f, _) | Hypothesis (_, f) | Theorem (_, f, _, _) -> Some f
  | Definition (id, typ, f) -> Some (Eq (Const (id, typ), f))
  | _ -> None

let rec map_stmt_formulas fn stmt = match stmt with
  | Axiom (id, f, name) -> Axiom (id, fn f, name)
  | Hypothesis (id, f) -> Hypothesis (id, fn f)
  | Definition (id, typ, f) -> Definition (id, typ, fn f)
  | Theorem (id, f, proof, range) ->
      let map_proof = function
        | Steps steps -> Steps steps
        | ExpandedSteps esteps ->
            ExpandedSteps (map (map (map_stmt_formulas fn)) esteps) in
      Theorem (id, fn f, Option.map map_proof proof, range)
  | TypeDecl _ | ConstDecl _ -> stmt

let decl_var = function
  | TypeDecl id -> Some (id, Fun (Base id, Bool))   (* universal set for type *)
  | ConstDecl (i, typ) -> Some (i, typ)
  | Definition (i, typ, _f) -> Some (i, typ)
  | _ -> None

let is_const id def =
  let* (i, typ) = decl_var def in
  if i = id then Some typ else None

let show_statement multi s =
  let name = stmt_name s in
  let show prefix f = indent_with_prefix prefix (show_formula_multi multi f) in
  match s with
    | TypeDecl _ -> name
    | ConstDecl (id, typ) ->
        sprintf "const %s : %s" (without_type_suffix id) (show_type typ)
    | Axiom (_, f, _) | Hypothesis (_, f) -> show (name ^ ": ") f
    | Definition (id, typ, f) ->
        let prefix =
          sprintf "definition %s: %s = " (without_type_suffix id) (show_type typ) in
        show prefix f
    | Theorem (_, f, _, _) -> show (name ^ ": ") f

let number_hypotheses name stmts =
  let f n = function
    | (Hypothesis _) as hyp ->
        let hyp_name = sprintf "%s.h%d" name n in
        (n + 1, set_stmt_id hyp_name hyp)
    | stmt -> (n, stmt) in
  snd (fold_left_map f 1 stmts)

let expand_proofs stmts : (statement * statement list) list =
  let only_thm, from_thm, to_thm =
    !(opts.only_thm), !(opts.from_thm), !(opts.to_thm) in
  let active = ref (not (Option.is_some only_thm) && not (Option.is_some from_thm)) in
  let rec expand known = function
    | stmt :: stmts ->
        let thms = match stmt with
          | Theorem (name, _, proof, _) as thm -> (
            let thm_known =
              if !active || only_thm = Some name || from_thm = Some name then
                (if from_thm = Some name then active := true;
                 [(thm, known)])
              else [] in
            thm_known @ match proof with
                | Some (ExpandedSteps fs) ->
                    fs |> filter_mapi (fun j stmts ->
                      let step_name = sprintf "%s.s%d" name (j + 1) in
                      if !active || only_thm = Some name || only_thm = Some step_name then
                        let (hypotheses, conjecture) = split_last stmts in
                        Some (set_stmt_id step_name conjecture,
                              rev (number_hypotheses name hypotheses) @ known)
                      else None)
                | Some (Steps _) -> assert false
                | None -> [])
          | _ -> [] in
        thms @ (if to_thm |> opt_exists ((=) (stmt_id stmt)) then []
                else expand (stmt :: known) stmts)
    | [] -> [] in
  let res = expand [] stmts in
  only_thm |> Option.iter (fun only_thm ->
    if res = [] then failwith (sprintf "theorem %s not found" only_thm));
  res
