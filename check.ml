open Printf

open Logic
open Options
open Statement
open Util

exception Check_error of string * syntax

let error s f = raise (Check_error (s, Formula f))
let type_error s typ = raise (Check_error (s, Type typ))

let rec check_type env typ = match typ with
  | Bool -> ()
  | Fun (t, u) | Product (t, u) ->
      check_type env t; check_type env u
  | Base id ->
      if not (is_unknown typ) && not (mem (TypeDecl id) env) then
        type_error ("undefined type " ^ id) typ
      else ()

let is_const id = function
  | ConstDecl (i, typ) when i = id -> Some typ
  | Definition (i, typ, _f) when i = id -> Some typ
  | _ -> None

let const_types1 env id = filter_map (is_const id) env

let const_types formula env id =
  match const_types1 env id with
    | [] -> error (sprintf "undefined: %s\n" id) formula
    | types -> types

let rec subtype t u = t = u || match t, u with
  | Fun (t, u), Fun (t', u') -> subtype t t' && subtype u u'
  | _, Base "_" -> true
  | _ -> false

let rec possible_types env dot_types vars =
  let rec possible formula = match formula with
    | Const (id, typ) ->
        if is_unknown typ then const_types formula env id
        else [typ]
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> [typ]
          | None -> const_types formula env id)
    | App (App (Const ("(,)", _), f), g) ->
        let+ t = possible f in
        let+ u = possible g in
        [Product (t, u)]
    | App (Const (":", Fun (t, t')), _) ->
        assert (t = t'); [t]
    | App (App (Const ("∈", _), _), _) -> [Bool]
    | App (f, g) -> unique @@
        possible_app env dot_types vars formula f g true |>
          map (fun (_t, _u, typ, _kind) -> typ)
    | Lambda (id, typ, f) ->
        possible_types env dot_types ((id, typ) :: vars) f |>
          map (fun t -> Fun (typ, t))
    | Eq (_, _) -> [Bool] in
  possible

and possible_app env dot_types vars formula f g with_dot =
  let possible = possible_types env dot_types vars in
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
    | [] -> error "can't apply" formula
    | all -> all

let tuple_cons_type t u = Fun (t, Fun (u, Product (t, u)))

let check_formula env =
  let dot_types = const_types1 env "·" in
  let rec check vars formula as_type =
    let possible = possible_types env dot_types vars in
    let find_const id =
      if mem as_type (const_types formula env id)
        then Const (id, as_type)
        else error ("expected " ^ show_type as_type) formula in
    let check_app f g with_dot =
      let possible =
        possible_app env dot_types vars formula f g with_dot |>
          filter (fun (_t, _u, typ, _kind) -> typ = as_type) in
      match possible with
        | [(t, u, typ, dot)] ->
            let f, g = check vars f t, check vars g u in
            if dot then
              App (App (Const ("·", (Fun (t, Fun (u, typ)))), f), g)
            else App (f, g)
        | [] -> error (show_type as_type ^ " expected") formula
        | _ -> error ("ambiguous as type " ^ show_type as_type) formula in
    match formula with
      | Const (id, typ) ->
          if is_unknown typ then find_const id
          else if typ = as_type then Const (id, as_type)
          else error "type_mismatch" formula
      | Var (id, _) -> (
          match assoc_opt id vars with
            | Some typ ->
                if typ = as_type then Var (id, as_type)
                else error "type_mismatch" formula
            | None -> find_const id)
      | App (App (Const ("(,)", _), f), g) -> (
          match as_type with
            | Product (t, u) ->
                apply [Const ("(,)", tuple_cons_type t u);
                       check vars f t; check vars g u]
            | _ -> error "type mismatch" formula)
      | App (Const (":", Fun (t, t')), f) ->
          assert (t = t'); check vars f t
      | App (App (Const ("∈", _), f), g) -> check_app g f false
      | App (f, g) -> check_app f g true
      | Lambda (id, typ, f) -> (
          match as_type with
            | Fun (t, u) when t = typ -> Lambda (id, typ, check ((id, typ) :: vars) f u)
            | _ -> error "type mismatch" formula)
      | Eq (f, g) ->
          if as_type = Bool then
            match intersect (possible f) (possible g) with
              | [t] -> Eq (check vars f t, check vars g t)
              | [] -> error "can't compare different types" formula
              | _ -> error "ambiguous" formula
          else error (show_type as_type ^ " expected") formula in
  check

let top_check env f = reduce (check_formula env [] f Bool)

type block = Block of proof_step * range * block list

let print_blocks blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, _range, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print "" blocks;
  print_newline ()

let infer_blocks steps =
  let rec all_vars = function
    | [] -> []
    | step :: steps ->
        subtract (step_free_vars step @ all_vars steps) (step_decl_vars step) in
  let rec infer vars in_assume steps = match steps with
    | [] -> ([], steps)
    | (step, range) :: rest ->
        if overlap (step_decl_vars step) (concat vars) then ([], steps)
        else let in_use = match vars with
          | [] -> true
          | top_vars :: _ -> overlap top_vars (all_vars (map fst steps)) in
        if step <> Assert _false && not in_use then ([], steps)
        else match step with
          | Escape ->
              if in_assume then ([], rest) else infer vars false rest
          | Group steps ->
              let rec group_blocks = function
                | [] -> []
                | steps ->
                    let (blocks, rest) = infer [] false steps in
                    blocks @ group_blocks rest in
              let blocks = group_blocks steps in
              let (blocks2, rest2) = infer vars in_assume rest in
              (blocks @ blocks2, rest2)
          | _ ->
            let (children, rest1) =
              match step with
                | Assume _ -> infer vars true rest
                | _ -> match step_decl_vars step with
                  | [] -> ([], rest)
                  | step_vars -> infer (step_vars :: vars) in_assume rest in
            let (blocks, rest2) = infer vars in_assume rest1 in
            (Block (step, range, children) :: blocks, rest2) in
  let (blocks, rest) = infer [] false steps in
  assert (rest = []);
  blocks

let rec blocks_steps blocks : statement list list * formula =
  match blocks with
    | [] -> ([], _true)
    | block :: rest ->
        let (fs, concl) = block_steps block in
        let (gs, final_concl) = blocks_steps rest in
        (fs @ map (cons (Theorem ("hyp", concl, None, empty_range))) gs,
        if rest = [] then concl
        else match last blocks with
          | Block (Assume _, _, _) -> _and concl final_concl
          | _ -> final_concl)

and block_steps (Block (step, range, children)) : statement list list * formula =
  let (fs, concl) = blocks_steps children in
  (* let apply fn = (map_fst fn fs, fn concl) in *)
  match step with
    | Assert f -> (
        match expand_multi_eq f with
          | Some (eqs, concl) ->
              (map (fun eq -> [Theorem ("", eq, None, range)]) eqs, concl)
          | None -> ([[Theorem ("", f, None, range)]], f)  )
    | Let (ids, typ) ->
        let decls = map (fun id -> ConstDecl (id, typ)) ids in
        (map (append decls) fs, for_all_vars_typ (ids, typ) concl)
    | LetVal (id, _typ, value) ->
        let sub f = rsubst1 f value id in
        (map (map (map_stmt_formulas sub)) fs, sub concl)
    | Assume a ->
        (map (cons (Theorem ("hyp", a, None, empty_range))) fs, implies a concl)
    | IsSome (ids, typ, g) ->
        let ex = exists_vars_typ (ids, typ) g in
        let stmts =
          map (fun id -> ConstDecl (id, typ)) ids @ [Theorem ("hyp", g, None, empty_range)] in
        ([Theorem ("", ex, None, range)] :: map (append stmts) fs,
         if any_free_in ids concl then exists_vars_typ (ids, typ) concl else concl)
    | Escape | Group _ -> failwith "block_formulas"

let rec expand_proof stmt env f range = function
  | Steps steps ->
      let thm_name = !(opts.thm_name) in
      if thm_name <> "" && stmt_id stmt <> thm_name then None else (
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

and check_stmt env stmt =
  match stmt with
    | Axiom (id, f, name) -> Axiom (id, top_check env f, name)
    | Definition (id, typ, f) ->
        Definition (id, typ, top_check env f)
    | Theorem (name, f, proof, range) ->
        let f1 = top_check env f in
        Theorem (name, f1, Option.bind proof (expand_proof stmt env f range), range)
    | stmt -> stmt

and check_stmts initial_env stmts =
  let check env stmt =
    let stmt = check_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check initial_env stmts)
    
let type_as_id typ = str_replace " " "" (show_type typ)

let tuple_constructor t u = sprintf "(,)%s%s" (show_type t) (show_type u)

let encode_id id typ =
  if mem id logical_ops then id
  else if id = "(,)" then
    match typ with
      | Fun (t, Fun (u, Product _)) -> tuple_constructor t u
      | _ -> failwith "encode_id"
  else if String.contains id ':' then failwith "encode_id"
  else sprintf "%s:%s" id (type_as_id typ)

let rec encode_type tuple_types typ = match typ with
  | Product (t, u) ->
      tuple_types := union [(t, u)] !tuple_types;
      Base (type_as_id typ)
  | Fun (t, u) -> Fun (encode_type tuple_types t, encode_type tuple_types u)
  | _ -> typ

let rec encode_formula tuple_types f =
  match f with
    | Const (id, typ) -> Const (encode_id id typ, encode_type tuple_types typ)
    | Var (id, typ) -> Var (id, encode_type tuple_types typ)
    | Lambda (id, typ, f) ->
        Lambda (id, encode_type tuple_types typ, encode_formula tuple_types f)
    | f -> map_formula (encode_formula tuple_types) f

let rec encode_stmts known_tuple_types = function
  | [] -> []
  | stmt :: stmts ->
      let tuple_types = ref [] in
      let encode = encode_formula tuple_types in
      let stmt = match stmt with
        | ConstDecl (id, typ) ->
            ConstDecl (encode_id id typ, encode_type tuple_types typ)
        | Definition (id, typ, f) ->
            Definition (encode_id id typ, encode_type tuple_types typ, encode f)
        | Theorem (id, f, proof, range) ->
            let map_proof = function
              | ExpandedSteps esteps ->
                  ExpandedSteps (map (encode_stmts known_tuple_types) esteps)
              | _ -> assert false in
            Theorem (id, encode f, Option.map map_proof proof, range)
        | _ -> map_stmt_formulas encode stmt in
      let new_tuple_types = subtract !tuple_types known_tuple_types in
      let tuple_defs (t, u) =
        let tuple_type_id = type_as_id (Product (t, u)) in
        [TypeDecl tuple_type_id;
         ConstDecl (tuple_constructor t u,
                    Fun (t, Fun (u, Base tuple_type_id)))] in
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
