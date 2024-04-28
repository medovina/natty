open List
open Printf

open Logic
open Statement
open Util

let debug = ref 0

let is_const id = function
  | ConstDecl (i, typ) when i = id -> Some typ
  | Definition (i, typ, _f) when i = id -> Some typ
  | _ -> None

let check_const env id =
  match find_map (is_const id) env with
    | Some typ -> (Const (id, typ), typ)
    | None -> printf "undefined: %s\n" id; assert false

let rec subtype t u = match t, u with
  | Bool, Bool -> true
  | Fun (t, u), Fun (t', u') -> subtype t t' && subtype u u'
  | Base id, Base id' when id = id' -> true
  | _, Base "_" -> true
  | _ -> false

let rec check_formula env vars =
  let rec check formula = match formula with
    | Const (id, typ) ->
        if typ = unknown_type then check_const env id else (formula, typ)
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> (Var (id, typ), typ)
          | None -> check_const env id)
    | App (f, g) ->
        let (f, typ_f), (g, typ_g) = check f, check g in (
        match typ_f with
          | Fun (tg, u) ->
              if subtype typ_g tg then (App (f, g), u)
              else (
                printf "type mismatch: can't apply %s : %s to %s : %s\n"
                  (show_formula f) (show_type typ_f) (show_formula g) (show_type typ_g);
                failwith "check_formula")
          | _ -> check (binop "·" unknown_type f g))
    | Lambda (id, typ, f) ->
        let (f, typ_f) = check_formula env ((id, typ) :: vars) f in
        (Lambda (id, typ, f), Fun (typ, typ_f))
    | Eq (f, g) ->
        let (f, typ_f), (g, typ_g) = check f, check g in
        if typ_f = typ_g then (Eq (f, g), Bool)
        else failwith ("type mismatch: " ^ show_formula formula) in
  check

let top_check env f =
  let (f, typ) = check_formula env [] f in
  if typ = Bool then f else failwith ("bool expected: " ^ show_formula f)

type block = Block of proof_step * block list

let mk_assert f = Block (Assert f, [])

let print_blocks blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print "" blocks;
  print_newline ()

let infer_blocks steps =
  let rec all_vars = function
    | [] -> []
    | step :: steps ->
        subtract (step_free_vars step @ all_vars steps) (step_decl_vars step) in
  let rec infer vars steps = match steps with
    | [] -> ([], steps)
    | step :: rest ->
        if overlap (step_decl_vars step) (concat vars) then ([], steps)
        else let in_use = match vars with
          | [] -> true
          | top_vars :: _ -> overlap top_vars (all_vars steps) in
        if not in_use then ([], steps)
        else
          let (children, rest1) =
            match step with
              | Assume _ -> infer vars rest
              | _ -> match step_decl_vars step with
                | [] -> ([], rest)
                | step_vars -> infer (step_vars :: vars) rest in
          let (blocks, rest2) = infer vars rest1 in
          (Block (step, children) :: blocks, rest2) in
  let (blocks, rest) = infer [] steps in
  assert (rest = []);
  blocks

let rec blocks_formulas = function
  | [] -> ([], _true)
  | block :: rest ->
      let (fs, concl) = block_formulas block in
      let (gs, final_concl) = blocks_formulas rest in
      (fs @ map_fst (fun f -> implies concl f) gs,
      if rest = [] then concl else final_concl)

and block_formulas (Block (step, children)) =
  let (fs, concl) = blocks_formulas children in
  let apply fn = (map_fst fn fs, fn concl) in
  match step with
    | Assert f -> (
        match expand_multi_eq f with
          | Some (eqs, concl) ->
              (map (fun eq -> (eq, eq)) eqs, concl)
          | None -> ([(f, f)], f))
    | Let (ids, typ) -> apply (for_all_vars_typ (ids, typ))
    | LetVal (id, _typ, value) -> apply (fun f -> rsubst1 f value id)
    | Assume a -> apply (implies a)
    | IsSome (id, typ, g) ->
        let ex = _exists id typ g in
        ((ex, ex) :: map_fst (fun f -> _for_all id typ (implies g f)) fs,
         concl)

let expand_proof env f = function
  | Steps steps ->
      let blocks = infer_blocks steps in
      if !debug > 0 then print_blocks blocks;
      let fs = fst (blocks_formulas (blocks @ [mk_assert f])) in
      (* fs |> iter (fun (f, _) -> print_line (show_multi f)); *)
      Formulas (map_fst (top_check env) fs)
  | _ -> assert false

let check_stmt env stmt =
  match stmt with
    | Axiom (id, f, name) -> Axiom (id, top_check env f, name)
    | Definition (id, typ, f) ->
        Definition (id, typ, top_check (stmt :: env) f)
    | Theorem (name, f, proof) ->
        let f = top_check env f in
        Theorem (name, f, Option.map (expand_proof env f) proof)
    | stmt -> stmt

let check_program _debug stmts =
  debug := _debug;
  let check env stmt =
    let stmt = check_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check [] stmts)
