open Printf

open Logic
open Options
open Statement
open Util

exception Check_error of string * syntax

let error s f = raise (Check_error (s, SFormula f))
let errorf s f = error (sprintf "%s: %s" s (show_formula f)) f

let type_error s typ = raise (Check_error (s, SType typ))

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

let rec with_skolem_names ids f : formula = match f with
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
        let g = Eq (Const (id, typ), value) in
        (map (cons (Definition (id, typ, g))) fs, rsubst1 concl value id)
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
let is_type_defined id env = exists (is_type_decl id) env

let check_type1 env vars typ =
  let rec check vars = function
    | Bool | Type -> ()
    | Base id ->
        if not (is_unknown typ) && not (is_type_defined id env) then
          type_error ("undefined type " ^ id) typ
        else ()
    | TypeVar id ->
        if not (mem (id, Type) vars) then
          type_error ("undefined type variable " ^ id) typ
    | Fun (t, u) -> check vars t; check vars u
    | Pi (id, t) -> check ((id, Type) :: vars) t
    | Product typs -> iter (check vars) typs
  in check vars typ

let check_type env typ = check_type1 env [] typ

let find_const env formula id : formula list =
  let consts = filter_map (is_const id) env |> map (fun typ -> Const (id, typ)) in
  match consts with
    | [] -> error (sprintf "undefined: %s\n" id) formula
    | _ -> consts

let infer_formula env vars formula : typ * formula =
  let new_type_var : unit -> typ =
    let n = ref (-1) in
    fun () -> incr n; TypeVar (sprintf "$%d" !n) in
  let rec inst f typ : formula * typ = match typ with
    | Pi (x, t) ->
        let v = new_type_var () in
          inst (App (f, Const (_type, v))) (type_subst t v x)
    | _ -> (f, typ) in
  let rec check vars tsubst formula : (tsubst * typ * formula) list =
    match formula with
      | Const (id, typ) ->
          let+ c = if is_unknown typ
                    then find_const env formula id else [formula] in
          let (f, typ) = inst c (type_of c) in
          [(tsubst, typ, f)]
      | Var (id, _) -> (
          match assoc_opt id vars with
            | Some typ -> [(tsubst, typ, Var (id, typ))]
            | None -> check vars tsubst (Const (id, unknown_type)))
      | App (f, g) ->
          let all =
            let+ (tsubst, t, f) = check vars tsubst f in
            let+ (tsubst, u, g) = check vars tsubst g in (
            match t with
              | Fun (v, w) -> (
                  match unify_types_or_pi tsubst v u with
                    | Some tsubst -> [tsubst, w, App (f, g)]
                    | None -> [])
              | _ ->
                  let h = apply [Const ("·", unknown_type); f; g] in
                  check vars tsubst h) in (
          match all with
            | [] -> errorf "can't apply" formula
            | [sol] -> [sol]
            | _ ->
                let types = all |> map (fun (tsubst, typ, _) -> subst_types tsubst typ) in
                if all_same types
                  then error "ambiguous application" formula
                else all)
      | Lambda (x, typ, f) ->
          check_type1 env vars typ;
          let+ (tsubst, t, f) = check ((x, typ) :: vars) tsubst f in
          let return_type = if typ = Type then Pi (x, t) else Fun (typ, t) in
          [(tsubst, return_type, Lambda (x, typ, f))]
      | Eq (f, g) ->
          let all =
            let+ (tsubst, t, f) = check vars tsubst f in
            let+ (tsubst, u, g) = check vars tsubst g in
            match unify_types tsubst t u with
              | Some tsubst -> [(tsubst, Bool, Eq (f, g))]
              | None -> [] in
          match all with
            | [] -> error "incomparable types" formula
            | [sol] -> [sol]
            | _ -> error "ambiguous comparison" formula in
  match check vars [] formula with
    | [(tsubst, typ, f)] ->
        (typ, subst_types_in_formula tsubst f)
    | [] -> failwith "infer_formula"
    | _ -> error "ambiguous" formula

let top_infer_with_type env f =
  let (typ, f) = infer_formula env [] f in
  (typ, b_reduce f)

let top_infer env f = snd (top_infer_with_type env f)

let rec arg_vars f : id list = match f with 
  | Var (id, _) -> [id]
  | _ -> match is_tuple_apply f with
      | Some (_id, args) -> concat_map arg_vars args
      | None -> failwith "invalid argument in definition"

let rec expand_proof stmt env f range proof : proof option = match proof with
  | Steps steps ->
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
      Some (ExpandedSteps (map (infer_stmts env) fs))
  | _ -> assert false

and infer_stmt env stmt : statement =
  match stmt with
    | TypeDecl _ -> stmt
    | ConstDecl (_, typ) -> check_type env typ; stmt      
    | Axiom (id, f, name) -> Axiom (id, top_infer env f, name)
    | Hypothesis (id, f) -> Hypothesis (id, top_infer env f)
    | Definition (_id, _typ, f) ->
        let (c, f) = raise_definition f in
        let (typ, f) = top_infer_with_type env f in
        let g = Option.get (lower_definition (Eq (Const (c, typ), f))) in
        Definition (c, typ, g)
    | Theorem (num, name, f, proof, range) ->
        let f1 = top_infer env f in
        Theorem (num, name, f1, Option.bind proof (expand_proof stmt env f range), range)

and infer_stmts initial_env stmts : statement list =
  let check env stmt =
    let stmt = infer_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check initial_env stmts)

let rec syntax_pos item origin_map : range option = match origin_map with
  | [] -> None
  | (s, range) :: ss ->
      if syntax_ref_eq s item then Some range
      else syntax_pos item ss

let infer_module checked md : (_module list, string * frange) result =
  let env : statement list = module_env md checked in
  try 
    let modd = { md with stmts = infer_stmts env md.stmts } in
    Ok (modd :: checked)
  with
    | Check_error (err, item) ->
        let pos = syntax_pos item md.syntax_map in
        Error (err, (md.filename, opt_default pos empty_range))

let infer_modules modules : (_module list, string * frange) result =
  fold_left_res infer_module [] modules |> Result.map rev

let type_as_id typ = str_replace " " "" (show_type typ)

let tuple_constructor types : string =
  String.concat "" (tuple_cons (length types) :: map show_type types)

let encode_id consts typ id : id =
  if id = _type || mem id logical_ops then id
  else
    let n = count_true (fun (c, _) -> c = id) consts in
    if n > (if mem (id, typ) consts then 1 else 0) then (
      let id' = if id = "u-" then "-" else id in  (* 'u' prefix is unnecessary with explicit type *)
      sprintf "%s:%s" id' (type_as_id typ))
    else id

let encode_type typ : typ = match typ with
  | Fun (Product typs, u) ->
        fold_right mk_fun_type typs u   (* curry type *)
  | _ -> typ

let encode_formula consts f : formula =
  let rec encode f =
    match collect_args f with
      | (Const (":", _), [g]) ->  (* type ascription *)
          encode g
      | (Const (c, typ), args) when is_tuple_constructor c ->
          mono_const c typ (map encode args)
      | (Const ("∈", _), [_type; x; set]) ->
          encode (App (set, x))
      | _ ->
        match f with
          | Const (id, typ) -> Const (encode_id consts typ id, encode_type typ)
          | Var (id, typ) -> Var (id, encode_type typ)
          | App (f, g) ->
              let f, g = encode f, encode g in (
              match collect_args g with
                | (Const (c, _), args) when is_tuple_constructor c ->
                    apply (f :: args)   (* curry arguments *)
                | _ -> App (f, g))
          | Lambda (id, typ, f) ->
              Lambda (id, encode_type typ, encode f)
          | Eq (f, Const (id, Fun (Base id', Bool))) when id = id' ->
              (* transform e.g. P = ℕ to ∀x:ℕ.P(x) *)
              let x = next_var "x" (free_vars f) in
              let h = _for_all x (Base id) (App (f, Var (x, Base id))) in
              encode h
          | f -> map_formula encode f in
  encode f

let encode_stmt consts stmt : statement =
  let encode f = b_reduce (encode_formula consts f) in
  map_statement1 (encode_id consts) encode_type encode stmt

let encode_module consts md : _module =
  { md with stmts = map (encode_stmt consts) md.stmts }

let basic_check env f : typ * formula =
  let rec check vars f = match f with
    | Const (id, typ) -> (
        match filter_map (is_const id) env with
          | [] ->
              if mem id logical_ops
                then (typ, Const (id, typ))
                else errorf "undefined constant" f
          | [typ] -> (typ, Const (id, typ))
          | _ -> failwith "ambiguous constant")
    | Var (id, _) ->
        let typ = assoc id vars in
        (typ, Var (id, typ))
    | App (f, g) ->
        let (f_type, f) = check vars f in
        let (g_type, g) = check vars g in
        let typ = match f_type with
          | Fun (t, u) when t = g_type -> u
          | Pi (x, t) -> type_subst t (get_const_type g) x
          | _ -> failwith "can't apply" in
        (typ, App (f, g))
    | Lambda (x, t, f) ->
        check_type1 env vars t;
        let (u, f) = check ((x, t) :: vars) f in
        let typ = if t = Type then Pi (x, u) else Fun (t, u) in
        (typ, Lambda (x, t, f))
    | Eq (g, h) ->
        let (g_type, g) = check vars g in
        let (h_type, h) = check vars h in
        if g_type <> h_type then (
          printf "g_type = %s, h_type = %s\n" (show_type g_type) (show_type h_type);
          errorf "can't compare" f);
        (Bool, Eq (g, h)) in
  check [] f

let basic_check_stmt env stmt : statement =
  let type_check typ = check_type env typ; typ in
  let bool_check f = match basic_check env f with
    | (Bool, f) -> f
    | _ -> failwith "boolean expected" in
  map_statement type_check bool_check stmt

let basic_check_stmts stmts : statement list =
  let rec check env = function
    | [] -> rev env
    | stmt :: stmts ->
        let stmt = basic_check_stmt env stmt in
        check (stmt :: env) stmts in
  check [] stmts

let check_module md : (_module, string * frange) result =
  try 
    Ok ({ md with stmts = basic_check_stmts md.stmts })
  with
    | Check_error (err, _item) ->
        Error (err, (md.filename, empty_range))

let check_modules modules : (_module list, string * frange) result =
    match modules with
      | [md] ->
          let** md = check_module md in Ok [md]
      | _ -> failwith "single module expected"

let check from_thf modules : (_module list, string * frange) result =
  if from_thf then check_modules modules
  else
    let** modules = infer_modules modules in
    let consts = filter_map decl_var (concat_map (fun m -> m.stmts) modules) in
    Ok (map (encode_module consts) modules)
