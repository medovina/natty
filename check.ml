open List
open Printf

open Logic

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
    | Const (id, _) as c -> (
        match assoc_opt id logical_consts with
          | Some typ -> (c, typ)
          | None -> check_const env id)
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
          | _ -> check (binop "·" f g))
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

let expand_proof env f = function
  | By (name, var) -> (
      match find_map (axiom_named name) env with
        | None -> failwith ("can't find axiom: " ^ name)
        | Some ax ->
            let (_, ax) = for_alls ax in
            let (ps, concl) = premises ax in
            let (vars, f) = for_alls f in (
              match assoc_opt var vars with
                | None -> failwith ("no variable: " ^ var)
                | Some typ -> (
                    let goal = for_all var typ f in
                    match unify concl goal with
                      | None ->
                          printf "no match:\n  concl = %s\n  goal = %s\n"
                            (show_formula concl) (show_formula goal);
                          assert false
                      | Some subst ->
                          let others = remove_assoc var vars in
                          let g f = fold_right for_all' others (reduce (subst_n subst f)) in
                          Steps (map g ps)
      )))
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
