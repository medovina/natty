open List
open Printf

open Logic
open Util

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
              else failwith ("type mismatch: " ^ show_formula formula)
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

let proof_by env f name outer var =
  match find_map (axiom_named name) env with
    | None -> failwith ("can't find axiom: " ^ name)
    | Some ax ->
        let (_, ax) = for_alls ax in
        let (ps, concl) = premises ax in
        let (vars_typs, f) = for_alls f in
          match assoc_opt var vars_typs with
            | None -> failwith ("no variable: " ^ var)
            | Some typ -> (
                let outer_vars_typs = map (fun v -> (v, assoc v vars_typs)) outer in
                let inner_vars_typs =
                  subtract vars_typs ((var, typ) :: outer_vars_typs) in (
                let goal = for_all_vars_typs ((var, typ) :: inner_vars_typs) f in
                match unify concl goal with
                  | None ->
                      printf "no match:\n  concl = %s\n  goal = %s\n"
                        (show_formula concl) (show_formula goal);
                      assert false
                  | Some subst ->
                      let g f = for_all_vars_typs outer_vars_typs
                        (reduce (subst_n subst f)) in
                      map g ps
  ))

type block = Block of proof_step * block list

let print_blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print ""

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
        else let (children, rest1) =
          match step with
            | Assume _ | By _ -> infer vars rest
            | _ -> match step_decl_vars step with
              | [] -> ([], rest)
              | step_vars -> infer (step_vars :: vars) rest in
          let (blocks, rest2) = infer vars rest1 in
          (Block (step, children) :: blocks, rest2) in
  let (blocks, rest) = infer [] steps in
  assert (rest = []);
  blocks

let rec blocks_formulas env f blocks = concat_map (block_formulas env f) blocks

and block_formulas env f (Block (step, children)) =
  let fs = (blocks_formulas env f) children in
  match step with
    | Assert f -> [f]
    | Let (ids, typ) -> map (for_all_vars_typ (ids, typ)) fs
    | LetVal (id, _typ, value) -> map (fun f -> subst1 f value id) fs
    | Assume a -> map (implies a) fs
    | IsSome (id, typ, g) -> exists id typ g ::
        map (fun f -> for_all id typ (implies g f)) fs
    | By (name, outer, var) -> fs @ proof_by env f name outer var

let expand_proof env f = function
  | Steps steps ->
      let blocks = infer_blocks steps in
      print_blocks blocks;
      Formulas (map (top_check env) (blocks_formulas env f blocks))
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

let check_program stmts =
  let check env stmt =
    let stmt = check_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check [] stmts)
