open Printf

open Logic
open Options
open Statement
open Util

exception Check_error of string * syntax

let error s f = raise (Check_error (s, Formula f))
let errorf s f = error (sprintf "%s: %s" s (show_formula f)) f

let type_error s typ = raise (Check_error (s, Type typ))

let rec check_type env typ = match typ with
  | Bool -> ()
  | Fun (t, u) -> check_type env t; check_type env u
  | Product typs -> iter (check_type env) typs
  | Base id ->
      if not (is_unknown typ) && not (mem (TypeDecl id) env) then
        type_error ("undefined type " ^ id) typ
      else ()

let const_types1 env id : typ list = filter_map (is_const id) env

let const_types formula env id : typ list =
  match const_types1 env id with
    | [] -> error (sprintf "undefined: %s\n" id) formula
    | types -> types

let rec subtype t u = t = u || match t, u with
  | Fun (t, u), Fun (t', u') -> subtype t t' && subtype u u'
  | _, Base "_" -> true
  | _ -> false

let rec possible_types env dot_types vars : formula -> typ list =
  let rec possible formula : typ list = match formula with
    | Const (id, typ) ->
        if is_unknown typ then const_types formula env id
        else [typ]
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> [typ]
          | None -> const_types formula env id)
    | App (Const (":", Fun (t, t')), _) ->
        assert (t = t'); [t]
    | App (App (Const ("∈", _), _), _) -> [Bool]
    | App (f, g) -> (
        match is_tuple_apply formula with
          | Some (_, args) ->
              let rec poss = function
                | [] -> [[]]
                | x :: args ->
                    let+ t = possible x in
                    let+ u = poss args in
                    [t :: u] in
              map mk_product_type (poss args)
          | _ -> unique @@
              possible_app env dot_types vars formula f g true |>
                map (fun (_t, _u, typ, _kind) -> typ))
    | Lambda (id, typ, f) ->
        possible_types env dot_types ((id, typ) :: vars) f |>
          map (fun t -> Fun (typ, t))
    | Eq (_, _) -> [Bool] in
  possible

(* returns list of (f type, g type, return type, is dot) *)
and possible_app env dot_types vars formula f g with_dot : (typ * typ * typ * bool) list =
  let possible : formula -> typ list = possible_types env dot_types vars in
  let all =
    let+ t = possible f in
    let+ u = possible g in
    let app = match t with
      | Fun (v, w) -> if subtype u v then [(t, u, w, false)] else []
      | _ -> [] in
    let prod =
      if with_dot then
        let+ dot = dot_types in
        match dot with
          | Fun (w, Fun (x, y)) when w = t && x = u -> [(t, u, y, true)]
          | _ -> []
      else [] in
    app @ prod in
  match all with
    | [] ->
        printf "f types: %s\n" (comma_join (map show_type (possible f)));
        printf "g types: %s\n" (comma_join (map show_type (possible g)));
        errorf "can't apply" formula
    | all -> all

let tuple_cons_type typs : typ =
  fold_right mk_fun_type typs (Product typs)

let check_formula env formula as_type : formula =
  let dot_types = const_types1 env "·" in
  let type_opt t = if is_unknown t then None else Some t in
  let rec check vars formula as_type : formula =
    let possible = possible_types env dot_types vars in
    let find_const id : formula =
      let types = const_types formula env id in
      match (types |> filter (fun typ -> opt_all_eq typ as_type)) with
        | [typ] -> Const (id, typ)
        | [] -> error ("expected " ^ show_type (Option.get as_type)) formula
        | _ -> error "ambiguous type" formula in
    let check_app f g with_dot : formula =
      match possible_app env dot_types vars formula f g with_dot with
        | [] -> errorf "can't apply" formula
        | possible ->
            let possible = possible |>
              filter (fun (_t, _u, typ, _kind) -> opt_all_eq typ as_type) in
            match possible with
              | [(t, u, typ, dot)] ->
                  let f, g = check vars f (Some t), check vars g (Some u) in
                  if dot then
                    App (App (Const ("·", (Fun (t, Fun (u, typ)))), f), g)
                  else App (f, g)
              | [] -> error (show_type (Option.get as_type) ^ " expected") formula
              | _ ->
                  possible |> iter (fun (t, u, ret, dot) ->
                    printf "t = %s, u = %s, ret = %s, dot = %b\n"
                      (show_type t) (show_type u) (show_type ret) dot);
                  errorf "ambiguous" formula in
    match formula with
      | Const (id, typ) ->
          if is_unknown typ then find_const id
          else if opt_all_eq typ as_type then Const (id, typ)
          else error "type_mismatch" formula
      | Var (id, _) -> (
          match assoc_opt id vars with
            | Some typ ->
                if opt_all_eq typ as_type then Var (id, typ)
                else error "type_mismatch" formula
            | None -> find_const id)
      | App (Const (":", Fun (t, t')), f) ->
          assert (t = t'); check vars f (Some t)
      | App (App (Const ("∈", _), f), g) -> check_app g f false
      | App (f, g) -> (
          match is_tuple_apply formula with 
            | Some (s, args) ->
                let args = (match as_type with
                  | Some (Product arg_types) ->
                      map2 (check vars) args (map mk_some arg_types)
                  | Some _ -> error "type mismatch" formula
                  | None -> map (fun x -> check vars x None) args) in
                apply (Const (s, tuple_cons_type (map type_of args)) :: args)
            | _ -> check_app f g true)
      | Lambda (id, typ, f) ->
          let u = match as_type with
            | Some (Fun (t, u)) when t = typ -> type_opt u
            | Some __ -> error "type mismatch" formula
            | None -> None in
          Lambda (id, typ, check ((id, typ) :: vars) f u)
      | Eq (f, g) ->
          if opt_all_eq Bool as_type then
            match intersect (possible f) (possible g) with
              | [t] ->
                  let f, g = check vars f (Some t), check vars g (Some t) in (
                  match g with
                    | Const (id, Fun (Base id', Bool)) when id = id' ->
                        (* transform e.g. P = ℕ to ∀x:ℕ.P(x) *)
                        let x = next_var "x" (free_vars f) in
                        _for_all x (Base id) (App (f, Var (x, Base id)))
                    | _ -> Eq (f, g))
              | [] ->
                  printf "left types = %s\n" (comma_join (map show_type (possible f)));
                  printf "right types = %s\n" (comma_join (map show_type (possible g)));
                  error "can't compare different types" formula
              | _ -> error "ambiguous" formula
          else error (show_type (Option.get as_type) ^ " expected") formula in
  check [] formula (type_opt as_type)

let top_check env f = b_reduce (check_formula env f Bool)

type block = Block of proof_step * range * block list

let print_blocks blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, _range, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print "" blocks;
  print_newline ()

let infer_blocks steps : block list =
  let rec all_vars : proof_step list -> id list = function
    | [] -> []
    | step :: steps ->
        subtract (step_free_vars step @ all_vars steps) (step_decl_vars step) in
  let rec infer vars in_assume steps : block list * (proof_step * range) list * bool =
    match steps with
      | [] -> ([], steps, false)
      | (step, range) :: rest ->
          if overlap (step_decl_vars step) (concat vars) then ([], steps, false)
          else let in_use = match vars with
            | [] -> true
            | top_vars :: _ -> overlap top_vars (all_vars (map fst steps)) in
          if step <> Assert _false && not in_use then ([], steps, false)
          else match step with
            | Escape ->
                if in_assume then ([], rest, true) else infer vars false rest
            | Assert f when f = _false ->
                if in_assume then ([Block (step, range, [])], rest, true)
                  else error "contradiction without assumption" f
            | Group steps ->
                let rec group_blocks = function
                  | [] -> []
                  | steps ->
                      let (blocks, rest, _bail) = infer [] false steps in
                      blocks @ group_blocks rest in
                let blocks = group_blocks steps in
                let (blocks2, rest2, bail) = infer vars in_assume rest in
                (blocks @ blocks2, rest2, bail)
            | _ ->
              let (children, rest1, bail) =
                match step with
                  | Assume _ ->
                      let (blocks, rest, _bail) = infer vars true rest in
                      (blocks, rest, false)
                  | _ -> match step_decl_vars step with
                    | [] -> ([], rest, false)
                    | step_vars -> infer (step_vars :: vars) in_assume rest in
              let (blocks, rest2, bail) =
                if bail then ([], rest1, true) else infer vars in_assume rest1 in
              let out_blocks = match step with
                | IsSome _ ->
                    [Block (step, range, children @ blocks)]  (* pull siblings into block *)
                | _ -> Block (step, range, children) :: blocks in
              (out_blocks, rest2, bail) in
  let (blocks, rest, _bail) = infer [] false steps in
  assert (rest = []);
  blocks

let skolem_name id = if looks_like_var id then id ^ "0" else id

let rec with_skolem_names ids = function
  | Const (id, typ) when mem id ids -> Const (skolem_name id, typ)
  | Var (id, typ) when mem id ids -> Var (skolem_name id, typ)
  | f -> map_formula (with_skolem_names ids) f

let stmt_with_skolem_names ids = map_stmt_formulas (with_skolem_names ids)

let rec blocks_steps blocks : statement list list * formula =
  match blocks with
    | [] -> ([], _true)
    | block :: rest ->
        let (fs, concl) = block_steps block in
        let (gs, final_concl) = blocks_steps rest in
        (fs @ map (cons (Hypothesis ("hyp", concl))) gs,
        if rest = [] then concl
        else match last blocks with
          | Block (Assume _, _, _) -> _and concl final_concl
          | _ -> final_concl)

and block_steps (Block (step, range, children)) : statement list list * formula =
  let (fs, concl) = blocks_steps children in
  let const_decls ids_typs : statement list * statement list list =
    if ids_typs = [] then ([], fs) else
    let decls = map (fun (id, typ) -> ConstDecl (skolem_name id, typ)) ids_typs in
    let fs = map (map (stmt_with_skolem_names (map fst ids_typs))) fs in
    (decls, fs) in
  match step with
    | Assert f -> (
        match expand_multi_eq f with
          | Some (eqs, concl) ->
              (map (fun eq -> [Theorem ("", None, eq, None, range)]) eqs, concl)
          | None -> ([[Theorem ("", None, f, None, range)]], f)  )
    | Let (ids, typ) ->
        let ids_typs = ids |> map (fun id -> (id, typ)) in
        let (decls, fs) = const_decls ids_typs in
        (map (append decls) fs, for_all_vars_typ (ids, typ) concl)
    | LetVal (id, typ, value) ->
        (map (cons (Definition (id, typ, value))) fs, rsubst1 concl value id)
    | Assume a ->
        let (ids_typs, f) = remove_exists a in
        let (decls, fs) = const_decls ids_typs in
        let f = with_skolem_names (map fst ids_typs) f in
        let decls = decls @ [Hypothesis ("hyp", f)] in
        (map (append decls) fs, if concl = _true then _true else implies a concl)
    | IsSome (ids, typ, g) ->
        let ex = exists_vars_typ (ids, typ) g in
        let stmts =
          map (fun id -> ConstDecl (skolem_name id, typ)) ids @
            [Hypothesis ("hyp", with_skolem_names ids g)] in
        let fs = map (map (stmt_with_skolem_names ids)) fs in
        ([Theorem ("", None, ex, None, range)] :: map (append stmts) fs,
         if any_free_in ids concl then exists_vars_typ (ids, typ) concl else concl)
    | Escape | Group _ -> failwith "block_formulas"

let rec expand_proof stmt env f range proof : proof option = match proof with
  | Steps steps ->
      let thm_name = stmt_id stmt in
      let only_thm = !(opts.only_thm) in
      if not (only_thm |> opt_for_all (fun o ->
          thm_name = o || starts_with (thm_name ^ ".") o)) then None else (
        if !debug > 0 then (
          printf "%s:\n\n" (stmt_name stmt);
          if !debug > 1 then (
            steps |> iter (fun (s, _range) -> print_endline (show_proof_step s));
            print_newline ()
          );
        );
        concat_map step_types (map fst steps) |> iter (check_type env);
        let blocks = infer_blocks steps @ [Block (Assert f, range, [])] in
        if !debug > 0 then print_blocks blocks;
        let fs = fst (blocks_steps blocks) in
        Some (ExpandedSteps (map (check_stmts env) fs)))
  | _ -> assert false

and check_stmt env stmt : statement =
  match stmt with
    | Axiom (id, f, name) -> Axiom (id, top_check env f, name)
    | Hypothesis (id, f) -> Hypothesis (id, top_check env f)
    | Definition (id, typ, f) ->
        let f = check_formula env f typ in
        Definition (id, type_of f, f)
    | Theorem (num, name, f, proof, range) ->
        let f1 = top_check env f in
        Theorem (num, name, f1, Option.bind proof (expand_proof stmt env f range), range)
    | TypeDecl _ | ConstDecl _ -> stmt

and check_stmts initial_env stmts : statement list =
  let check env stmt =
    let stmt = check_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check initial_env stmts)
    
let type_as_id typ = str_replace " " "" (show_type typ)

let tuple_constructor types : string =
  String.concat "" (tuple_cons (length types) :: map show_type types)

let encode_id id typ : id =
  if mem id logical_ops then id
  else if starts_with "(," id then
    let types = collect_arg_types typ in
    assert (length types = tuple_arity id);
    tuple_constructor types
  else if String.contains id ':' then failwith "encode_id: double encode"
  else
    let id' = if id = "u-" then "-" else id in  (* 'u' prefix is unnecessary with explicit type *)
    sprintf "%s:%s" id' (type_as_id typ)

let rec encode_type tuple_types typ : typ = match typ with
  | Product typs ->
      tuple_types := union [typs] !tuple_types;
      Base (type_as_id typ)
  | Fun (t, u) -> Fun (encode_type tuple_types t, encode_type tuple_types u)
  | _ -> typ

let rec encode_formula tuple_types f : formula =
  match f with
    | Const (id, typ) -> Const (encode_id id typ, encode_type tuple_types typ)
    | Var (id, typ) -> Var (id, encode_type tuple_types typ)
    | Lambda (id, typ, f) ->
        Lambda (id, encode_type tuple_types typ, encode_formula tuple_types f)
    | f -> map_formula (encode_formula tuple_types) f

let rec encode_stmts known_tuple_types stmts : statement list = match stmts with
  | [] -> []
  | stmt :: stmts ->
      let tuple_types : typ list list ref = ref [] in
      let encode = encode_formula tuple_types in
      let stmt = match stmt with
        | ConstDecl (id, typ) ->
            ConstDecl (encode_id id typ, encode_type tuple_types typ)
        | Definition (id, typ, f) ->
            Definition (encode_id id typ, encode_type tuple_types typ, encode f)
        | Theorem (num, name, f, proof, range) ->
            let map_proof = function
              | ExpandedSteps esteps ->
                  ExpandedSteps (map (encode_stmts known_tuple_types) esteps)
              | _ -> assert false in
            Theorem (num, name, encode f, Option.map map_proof proof, range)
        | _ -> map_stmt_formulas encode stmt in
      let new_tuple_types = subtract !tuple_types known_tuple_types in
      let tuple_defs typs =
        let tuple_type_id = type_as_id (Product typs) in
        [TypeDecl tuple_type_id;
         ConstDecl (tuple_constructor typs,
                    fold_right mk_fun_type typs (Base tuple_type_id))] in
      concat_map tuple_defs new_tuple_types @ (stmt ::
        encode_stmts (new_tuple_types @ known_tuple_types) stmts)

let rec syntax_pos item = function
  | [] -> None
  | (s, range) :: ss ->
      if syntax_ref_eq s item then (
        assert (syntax_pos item ss = None);
        Some range)
      else syntax_pos item ss

let check_program from_thf origin_map stmts =
  try
    let stmts = check_stmts [] stmts in
    Ok (if from_thf then stmts else encode_stmts [] stmts)
  with
    | Check_error (err, item) -> Error (err, syntax_pos item origin_map)
