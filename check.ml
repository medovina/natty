open Printf

open Logic
open Options
open Statement
open Util

exception Check_error of string * range

let error s range = raise (Check_error (s, decode_range range))
let errorf s f range = error (sprintf "%s: %s" s (show_formula f)) range

let strip_range f : formula = match f with
  | App (Const (c, _), g) when starts_with "@" c -> g
  | _ -> f

let range_of f : str = match f with
  | App (Const (c, _), _) when starts_with "@" c -> c
  | _ -> ""

type block = Block of proof_step * range * block list

let print_blocks blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, _range, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print "" blocks;
  print_newline ()

let rec chain_blocks steps : block list = match steps with
  | [] -> []
  | (step, range) :: steps -> [Block (step, range, chain_blocks steps)]

let infer_blocks steps : block list =
  let rec all_vars steps : id list = match steps with
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
            | top_vars :: _ -> overlap top_vars ("·" :: all_vars (map fst steps)) in
          if step <> Assert _false && not in_use then ([], steps, false)
          else match step with
            | Escape ->
                if in_assume then ([], rest, true) else infer vars false rest
            | Assert f when strip_range f = _false ->
                if in_assume then ([Block (step, range, [])], rest, true)
                  else error "contradiction without assumption" (range_of f)
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

let is_comparison f =
  match strip_range f with
    | Eq (g, h) -> Some ("=", g, h)
    | App (App (Var (c, _), g), h) when mem c Parser.compare_ops -> Some (c, g, h)
    | _ -> None

let rec collect_cmp f : formula list * id list =
  match is_comparison f with
    | Some (op, g, h) ->
        let (gs, g_ops), (hs, h_ops) = collect_cmp g, collect_cmp h in
        (gs @ hs, g_ops @ [op] @ h_ops)
    | None -> ([f], [])

let rec join_cmp fs ops : formula list =
  let app op f g : formula =
    if op = "=" then Eq (f, g) else apply [_var op; f; g] in
  match fs, ops with
    | [f], [] -> [f]
    | [f; g], [op] -> [app op f g]
    | f :: g :: fs, op :: ops ->
        app op f g :: join_cmp (g :: fs) ops
    | _ -> failwith "join_cmp"

let chain_comparisons f : formula list =
  let fs, ops = collect_cmp f in
  join_cmp fs ops

let rec expand_chains f : formula =
  match collect_cmp f with
    | [f], [] -> map_formula expand_chains f
    | fs, ops -> multi_and (join_cmp fs ops)

let is_type_defined id env = exists (is_type_decl id) env

let check_type1 env vars typ : typ =
  let rec check range vars typ = match typ with
    | Bool | Type -> typ
    | Base id ->
        if not (is_unknown typ) && not (is_type_defined id env) then
          error ("undefined type " ^ id) range
        else typ
    | TypeVar id ->
        if mem (id, Type) vars then TypeVar id
        else if is_type_defined id env then Base id
        else error ("undefined type variable " ^ id) range
    | Fun (t, u) -> Fun (check range vars t, check range vars u)
    | Pi (id, t) -> Pi (id, check range ((id, Type) :: vars) t)
    | Product typs -> Product (map (check range vars) typs)
    | TypeApp (c, [typ]) when c.[0] = '@' -> check c vars typ
    | TypeApp _ -> failwith "check_type1"
  in check "" vars typ

let check_type env typ : typ = check_type1 env [] typ

let id_types env id : typ list = filter_map (is_const_decl id) env

let find_const env formula range id : formula list =
  let consts = id_types env id |> map (fun typ -> Const (id, typ)) in
  match consts with
    | [] -> errorf (sprintf "undefined: %s\n" id) formula range
    | _ -> consts

let univ f : formula = match f with
  | Var (id, Type) -> Lambda ("x", TypeVar id,  _true)
  | Const (id, Type) -> Lambda ("x", Base id, _true)
  | f -> f

let is_declared env id =
  env |> exists (fun stmt -> match decl_var stmt with
    | Some (id', _) when id' = id -> true
    | _ -> false)

let infer_formula env vars formula : typ * formula =
  let formula = expand_chains formula in
  let new_type_var : unit -> typ =
    let n = ref (-1) in
    fun () -> incr n; TypeVar (sprintf "$%d" !n) in
  let is_var x = x.[0] = '$' in
  let rec inst f typ : formula * typ = match typ with
    | Pi (x, t) ->
        let v = new_type_var () in
          inst (App (f, type_const v)) (type_subst t v x)
    | _ -> (f, typ) in
  let rec check range vars tsubst formula : (tsubst * typ * formula) list =
    match formula with
      | Const (id, typ) ->
          let+ c = if is_unknown typ
                    then find_const env formula range id
                    else [Const (id, check_type1 env vars typ)] in
          let c = univ c in
          let (f, typ) = inst c (type_of c) in
          [(tsubst, typ, f)]
      | Var (id, _) -> (
          match assoc_opt id vars with
            | Some typ ->
                let f = univ (Var (id, typ)) in
                [(tsubst, type_of f, f)]
            | None -> check range vars tsubst (_const id))
      | App (Const (c, _), f) when c.[0] = '@' ->
          check c vars tsubst f
      | App (App (Const ("_", _), f), g) ->
          let h = match f, g with
            | Var (v, _), Const (c, _) ->
                let name = v ^ digit_to_sub c in
                if mem name (map fst vars) || is_declared env name
                  then _var name else App (f, g)
            | _ -> failwith "infer_formula" in
          check range vars tsubst h
      | App (f, g) ->
          let all =
            let+ (tsubst, t, f) = check range vars tsubst f in
            let+ (tsubst, u, g) = check range vars tsubst g in (
            match t with
              | Fun (v, w) -> (
                  match unify_types_or_pi is_var tsubst v u with
                    | Some tsubst -> [tsubst, w, App (f, g)]
                    | None -> [])
              | _ ->
                  let h = apply [Var ("·", unknown_type); f; g] in
                  check range vars tsubst h) in (
          match all with
            | [] -> errorf "can't apply" formula range
            | [sol] -> [sol]
            | _ ->
                let types = all |> map (fun (tsubst, typ, _) -> subst_types tsubst typ) in
                if all_same types
                  then errorf "ambiguous application" formula range
                else all)
      | Lambda (x, typ, f) ->
          let typ = check_type1 env vars typ in
          let+ (tsubst, t, f) = check range ((x, typ) :: vars) tsubst f in
          let return_type = if typ = Type then Pi (x, t) else Fun (typ, t) in
          [(tsubst, return_type, Lambda (x, typ, f))]
      | Eq (f, g) ->
          let all =
            let+ (tsubst, t, f) = check range vars tsubst f in
            let+ (tsubst, u, g) = check range vars tsubst g in
            match unify_types is_var tsubst t u with
              | Some tsubst -> [(tsubst, Bool, Eq (f, g))]
              | None -> [] in
          match all with
            | [] -> errorf "incomparable types" formula range
            | [sol] -> [sol]
            | _ -> errorf "ambiguous comparison" formula range in
  match check "" vars [] formula with
    | [(tsubst, typ, f)] ->
        (typ, subst_types_in_formula tsubst f)
    | [] -> failwith "infer_formula"
    | _ -> errorf "ambiguous" formula (range_of formula)

let top_infer_with_type env f =
  let (typ, f) = infer_formula env [] f in
  (typ, b_reduce f)

let top_infer env f = snd (top_infer_with_type env f)

let infer_type_decl env id name =
  if is_type_defined id env then (
    printf "duplicate type definition: %s\n" id;
    failwith "infer_type_decl");
  TypeDecl (id, name)

let check_dup_const env id typ kind =
  if mem typ (id_types env id) then (
    printf "duplicate %s: %s : %s\n" kind id (show_type typ);
    failwith "check_dup_const")

let infer_const_decl env id typ =
  let typ = check_type env typ in
  check_dup_const env id typ "constant declaration";
  ConstDecl (id, typ)

let infer_definition env f : id * typ * formula =
  (* f has the form ∀σ₁...σₙ v₁...vₙ (C φ₁ ... φₙ = ψ) .  We check types and build
    * a formula of the form ∀σ₁...σₙ v₁...vₙ (C σ₁...σₙ φ₁ ... φₙ = ψ) .*)
  let (vs, f) = gather_quant "∀" (strip_range f) in
  let f = lower_definition f in
  let (vs2, f) = gather_quant "∀" f in
  let (type_vars, vars) = (vs @ vs2) |> partition (fun (_, typ) -> typ = Type) in
  let univ = map fst type_vars in
  let vars = vars |> map (fun (v, typ) -> (v, check_type1 env type_vars typ)) in
  let vs = type_vars @ vars in (
  match strip_range f with
    | Eq (f, g) | App (App (Const ("↔", _), f), g) ->
        let (c, args) = collect_args (strip_range f) in (
        match strip_range c with
          | Const (id, _) | Var (id, _) ->
              let infer f = infer_formula env vs f in
              let arg_types, args = unzip (map infer args) in
              let g_type, g = infer g in
              let c_type = mk_pi_types univ (mk_fun_types arg_types g_type) in
              let type_args = univ |> map (fun v -> type_const (TypeVar v)) in
              let eq = if g_type = Bool then _iff else mk_eq in
              let body = for_all_vars_types vs @@
                eq (apply (Const (id, c_type) :: type_args @ args)) g in
              (id, c_type, body)
          | _ -> failwith "definition expected")
    | _ -> failwith "definition expected")

(* Restore type variables for any type that has become a constant in the
 * local environment. *)
let rec with_type_vars env typ : typ = match typ with
  | Base id ->
      if is_type_defined id env then TypeVar id else typ
  | _ -> map_type (with_type_vars env) typ

let rec blocks_steps env lenv blocks : statement list list * formula =
  match blocks with
    | [] -> ([], _true)
    | block :: rest ->
        let (fs, concl) = block_steps env lenv block in
        let hyp = Hypothesis ("hyp", top_infer env concl) in
        let (gs, final_concl) = blocks_steps (hyp :: env) (hyp :: lenv) rest in
        ( fs @ gs,
          if rest = [] then concl
          else match last blocks with
            | Block (Assume _, _, _) -> _and concl final_concl
            | _ -> final_concl)

and block_steps env lenv (Block (step, range, children)) : statement list list * formula =
  let child_steps stmts = blocks_steps (stmts @ env) (stmts @ lenv) children in
  let const_decl (id, typ) =
    if typ = Type then infer_type_decl env id None else infer_const_decl env id typ in
  let const_decls ids_typs = rev (map const_decl ids_typs) in
  let mk_thm eq = Theorem ("", None, top_infer env eq, [], range) :: lenv in
  match step with
    | Assert f ->
        let eqs = chain_comparisons f in
        let concl =
          if length eqs > 2 && for_all is_eq eqs then
            match hd eqs, last eqs with
              | Eq (a, _), Eq (_, b) -> Eq (a, b)
              | _ -> failwith "block_steps"
          else f in
        (map mk_thm eqs, concl)
    | Let ids_types ->
        let decls = const_decls ids_types in
        let (fs, concl) = child_steps decls in
        (fs, for_all_vars_types_if_free ids_types concl)
    | LetDef (_id, _typ, g) ->
        let (id, typ, f) = infer_definition env g in
        let (fs, concl) = child_steps [Definition (id, typ, f)] in
        let concl = match g with
          | Eq (Const (id, _typ), value) -> rsubst1 concl value id
          | _ -> _for_all id (with_type_vars lenv typ) (implies g concl) in
        (fs, concl)
    | Assume a ->
        let (ids_typs, f) = remove_exists a in
        let decls = const_decls ids_typs in
        let decls = Hypothesis ("hyp", top_infer (decls @ env) f) :: decls in
        let (fs, concl) = child_steps decls in
        (fs, if concl = _true then _true
             else for_all_vars_types ids_typs (implies f concl))
    | IsSome (ids, typ, g) ->
        let ex = exists_vars_typ (ids, typ) g in
        let decls = rev (map (fun id -> infer_const_decl env id typ) ids) in
        let stmts = Hypothesis ("hyp", top_infer (decls @ env) g) :: decls in
        let (fs, concl) = child_steps stmts in
        (mk_thm ex :: fs,
         if any_free_in ids concl then exists_vars_typ (ids, typ) concl else concl)
    | Escape | Group _ -> failwith "block_formulas"

let trim_lets steps : (proof_step * range) list =
  let vs = unique (steps |> concat_map (fun (step, _) -> step_free_vars step)) in
  let+ (step, range) = steps in (
  match step with
    | Let ids_types ->
        let ids_types = ids_types |> filter (fun (id, _) ->
          mem id vs || id = "·") in  (* "·" may not be explicitly present *)
        if ids_types = [] then [] else [(Let ids_types, range)]
    | _ -> [(step, range)])

let collect_lets steps : id list =
  steps |> concat_map (function
    | Let ids_types -> map fst ids_types
    | _ -> [])

let duplicate_lets vars steps : bool =
  let rec check = function
    | [] -> false
    | (step, _range) :: steps ->
        match step with
          | Assert _ -> false
          | Let ids_types ->
              let ids = map fst ids_types in
              overlap ids vars || check steps
          | _ -> check steps in
  check steps

let rec expand_proof stmt env steps proof_steps : formula * statement list list =
  let steps = trim_lets steps in
  let blocks0 = chain_blocks steps in
  let (_, concl) = blocks_steps env [] blocks0 in
  let stmtss = if proof_steps = [] then [] else
    let (init, f) = split_last steps in
    let proof_steps =
      if duplicate_lets (collect_lets (map fst init)) proof_steps
        then proof_steps @ [(Assert concl, snd f)]
        else init @ proof_steps @ [f] in
    if !debug > 0 then (
      printf "%s:\n\n" (stmt_name stmt);
      if !debug > 1 then (
        proof_steps |> iter (fun (s, _range) -> print_endline (show_proof_step s));
        print_newline ()
      );
    );
    let blocks = infer_blocks proof_steps in
    if !debug > 0 then print_blocks blocks;
    let (stmtss, _concl) = blocks_steps env [] blocks in
    map rev stmtss in
  (top_infer env concl, stmtss)

and infer_stmt env stmt : statement =
  match stmt with
    | TypeDecl (id, name) -> infer_type_decl env id name
    | ConstDecl (id, typ) -> infer_const_decl env id typ
    | Axiom _ -> failwith "infer_stmt"
    | Hypothesis (id, f) -> Hypothesis (id, top_infer env f)
    | Definition (_id, _typ, f) ->
        let (id, typ, f) = infer_definition env f in
        Definition (id, typ, f)
    | Theorem _ -> failwith "infer_stmt"
    | HAxiom (id, steps, name) ->
        let blocks = infer_blocks steps in
        let (_, f) = blocks_steps env [] blocks in
        Axiom (id, top_infer env f, name)
    | HTheorem (num, name, steps, proof_steps) ->
        let (f, stmts) = expand_proof stmt env steps proof_steps in
        Theorem (num, name, f, stmts, snd (last steps))

and infer_stmts initial_env stmts : statement list =
  let check env stmt =
    let stmt = infer_stmt env stmt in
    (stmt :: env, stmt) in
  snd (fold_left_map check initial_env stmts)

let infer_module checked md : (_module list, string * frange) result =
  let env : statement list = module_env md checked in
  try 
    let modd = { md with stmts = infer_stmts env md.stmts } in
    Ok (modd :: checked)
  with
    | Check_error (err, pos) ->
        Error (err, (md.filename, pos))

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
          | Eq (f, Lambda (_, typ, tr)) when tr = _true ->
              (* apply functional extensionality *)
              let x = next_var "x" (free_vars f) in
              let h = _for_all x typ (App (f, Var (x, typ))) in
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
        match filter_map (is_const_decl id) env with
          | [] ->
              if mem id logical_ops
                then (typ, Const (id, typ))
                else errorf "undefined constant" f ""
          | [typ] -> (typ, Const (id, typ))
          | _ -> failwith "ambiguous constant")
    | Var (id, _) ->
        let typ = assoc id vars in
        (typ, Var (id, typ))
    | App (g, h) ->
        let (g_type, g) = check vars g in
        let (h_type, h) = check vars h in
        let typ = match g_type, h_type with
          | Fun (Fun (Type, t), u), Pi (_, t') when t = t' ->
              u (* allow * → τ to match Πσ.τ, like in unify_types_or_pi *)
          | Fun (t, u), t' when t = t' -> u
          | Pi (x, t), Type -> type_subst t (get_const_type h) x
          | _ ->
              printf "f = %s\n" (show_formula f);
              failwith "can't apply" in
        (typ, App (g, h))
    | Lambda (x, t, f) ->
        let t = check_type1 env vars t in
        let (u, f) = check ((x, t) :: vars) f in
        let typ = if t = Type then Pi (x, u) else Fun (t, u) in
        (typ, Lambda (x, t, f))
    | Eq (g, h) ->
        let (g_type, g) = check vars g in
        let (h_type, h) = check vars h in
        if g_type <> h_type then (
          printf "g_type = %s, h_type = %s\n" (show_type g_type) (show_type h_type);
          errorf "can't compare" f "");
        (Bool, Eq (g, h)) in
  check [] f

let basic_check_stmt env stmt : statement =
  let bool_check f = match basic_check env f with
    | (Bool, f) -> f
    | _ -> failwith "boolean expected" in
  map_statement (check_type env) bool_check stmt

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
