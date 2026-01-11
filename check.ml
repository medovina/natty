open Printf

open Hstatement
open Logic
open Module
open Options
open Statement
open Util

exception Check_error of string * range

let axiom_count = ref 0
let theorem_count = ref 0

let error s range = raise (Check_error (s, range))
let errorf s f range = error (sprintf "%s: %s" s (show_formula f)) range

let is_declared env id =
  env |> exists (fun stmt -> match decl_var stmt with
    | Some (id', _) when id' = id -> true
    | _ -> false)

type block = Block of proof_step * block list

let print_blocks blocks =
  let rec print indent blocks =
    blocks |> iter (fun (Block (step, children)) ->
      printf "%s%s\n" indent (show_proof_step step);
      print (indent ^ "  ") children) in
  print "" blocks;
  print_newline ()

let rec chain_blocks steps body : block list = match steps with
  | [] -> body
  | step :: steps -> [Block (step, chain_blocks steps body)]

let rec all_vars steps : id list = match steps with
  | [] -> []
  | step :: steps ->
      subtract (step_free_vars step @ all_vars steps) (step_decl_vars step)

(* Tranform "assume x ∈ g" to a variable declaration "let x : [g]". *)
let map_assume_step env vars step = match step with
  | Assume f -> (
      match strip_range f with
        | (App (App (Const ("∈", _), v), g)) -> (
            match strip_range v with
              | Var (x, _) ->
                  if mem x (concat vars) || is_declared env x
                    then step else Let [(x, Sub g)]
              | _ -> step)
        | _ -> step)
  | _ -> step

let has_premise f g =
  match remove_for_all (strip_ranges f) with
    | App (App (Const ("(→)", _), g'), _) when g' = strip_ranges g -> true
    | _ -> false

let trim_escape rest : proof_step list = match rest with
  | Escape :: rest -> rest  (* ignore an escape that immediately follows an assert ⊥ *)
  | _ -> rest

let is_assert_false step = match step with
  | Assert (f, _) when strip_range f = _false -> true
  | _ -> false

let infer_blocks env steps : block list =
  let rec infer vars scope_vars in_assume steps : block list * proof_step list * bool =
    match steps with
      | [] -> ([], steps, false)
      | step :: rest ->
          let step = map_assume_step env vars step in
          if overlap (step_decl_vars step) (concat vars) then ([], steps, false) else
          let in_use = "·" :: all_vars steps in
          let vars_in_use = head_opt vars |> opt_for_all (fun top_vars
            -> overlap top_vars in_use) in
          let let_vars_in_use = head_opt scope_vars |> opt_for_all (fun top_vars
            -> overlap top_vars in_use) in
          if not (is_assert_false step) && not vars_in_use && not let_vars_in_use
            then ([], steps, false)
          else match step with
            | Escape ->
                if is_some in_assume then ([], rest, true)
                  else infer vars scope_vars None rest
            | Assert (f, _) when opt_exists (has_premise f) in_assume ->
                ([], steps, true)  (* proof invoked last assumption as a premise, so exit scope *)
            | Assert (f, _) when strip_range f = _false ->
                if is_some in_assume then
                  ([Block (step, [])], trim_escape rest, true)
                else error "contradiction without assumption" (range_of f)
            | Group steps ->
                let rec group_blocks steps : block list = match steps with
                  | [] -> []
                  | steps ->
                      let (blocks, rest, _bail) = infer [] [] None steps in
                      blocks @ group_blocks rest in
                let blocks = group_blocks steps in
                let rest = if is_assert_false (last steps) then trim_escape rest else rest in
                let (blocks2, rest2, bail) = infer vars scope_vars in_assume rest in
                (blocks @ blocks2, rest2, bail)
            | _ ->
              let (children, rest1, bail) =
                match step with
                  | Assume f ->
                      let (blocks, rest, _bail) =
                        infer vars scope_vars (Some f) rest in
                      (blocks, rest, false)
                  | _ -> match step_decl_vars step with
                    | [] -> ([], rest, false)
                    | step_vars ->
                        let scope_vars = if is_let_def step || is_is_some step
                          then scope_vars else step_vars :: scope_vars in
                        infer (step_vars :: vars) scope_vars in_assume rest in
              let (blocks, rest2, bail) =
                if bail then ([], rest1, true) else infer vars scope_vars in_assume rest1 in
              let out_blocks = Block (step, children) :: blocks in
              (out_blocks, rest2, bail) in
  let (blocks, rest, _bail) = infer [] [] None steps in
  assert (rest = []);
  blocks

let is_comparison f : (string * formula * formula) option =
  match strip_range f with
    | Eq (g, h) -> Some ("=", g, h)
    | App (Const ("(¬)", _), Eq (g, h)) -> Some ("≠", g, h)
    | App (App (Var (c, _), g), h) when mem c Parser.compare_ops -> Some (c, g, h)
    | _ -> None

let comparison_op f = match is_comparison f with
  | Some (op, _, _) -> op
  | None -> failwith "comparison_op"

let rec collect_cmp f : formula list * id list =
  match is_comparison f with
    | Some (op, g, h) ->
        let (gs, g_ops), (hs, h_ops) = collect_cmp g, collect_cmp h in
        (gs @ hs, g_ops @ [op] @ h_ops)
    | None -> ([f], [])

let apply_comparison op f g : formula =
  if op = "=" then Eq (f, g)
  else if op = "≠" then _neq f g
  else apply [_var op; f; g]

let rec extract_by f : formula * reason = match f with
  | App (Const (c, _), h) -> (
      match opt_remove_prefix "$by " c with
        | Some reasons ->
            let rs = String.split_on_char ',' reasons in
            let by = map (fun r -> (r, empty_range)) rs in
            (h, by)
        | None -> (f, []))
  | _ ->
      (* In an assertion such as "x < 0 or 0 < x by [trichotomy]", we want
         the reason to apply to the entire formula. *)
    let (f, args) = collect_args f in
    if args = [] then (f, []) else
    let args, last = split_last args in
    let (last, by) = extract_by last in
    (apply (f :: args @ [last]), by)

let rec join_comparisons fs ops : (formula * reason) list =
  match fs, ops with
    | [f], [] ->
        let f, by = extract_by f in
        [(f, by)]
    | [f; g], [op] ->
        let g, by = extract_by g in
        [(apply_comparison op f g, by)]
    | f :: g :: fs, op :: ops ->
        let g, by = extract_by g in
        (apply_comparison op f g, by) :: join_comparisons (g :: fs) ops
    | _ -> failwith "chain_comparisons"

let join_cmp fs ops : formula list =
  let fs, reasons = unzip (join_comparisons fs ops) in
  assert (for_all ((=) []) reasons);
  fs

let rec expand_chains f : formula =
  let fs, ops = collect_cmp f in
  if length fs <= 2 then map_formula expand_chains f
  else multi_and (join_cmp (map expand_chains fs) ops)

let is_type_defined id env = exists (is_type_decl id) env

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

let quant1 q id typ f =
  if q = "{}" then Lambda (id, typ, f) else quant q id typ f

let is_lambda_or_set_comp f = match f with
  | Lambda _ | App (Const ("{}", _), _) -> true
  | _ -> false

let rec check_type1 env vars typ : typ =
  let rec check range vars typ =
    let lookup_type id =
      if mem (id, Type) vars then Some (TypeVar id)
      else if is_type_defined id env then Some (Base id)
      else None in
    match typ with
      | Bool | Type -> typ
      | Base id ->
          if not (is_unknown typ) && not (is_type_defined id env) then
            error ("undefined type " ^ id) range
          else typ
      | TypeVar id -> (match lookup_type id with
          | Some typ -> typ
          | None -> error ("undefined type variable " ^ id) range)
      | Fun (t, u) -> Fun (check range vars t, check range vars u)
      | Pi (id, t) -> Pi (id, check range ((id, Type) :: vars) t)
      | Product typs -> Product (map (check range vars) typs)
      | TypeApp (c, [typ]) when c.[0] = '@' -> check (decode_range c) vars typ
      | TypeApp _ -> failwith "check_type1: typeapp"
      | Sub f -> match strip_range f with
        | Var (id, _) as f ->
            opt_or (lookup_type id) (fun () ->
              let (_typ, f) = infer_formula env vars f in
              Sub f)
        | _ -> failwith "check_type1: sub"
  in check empty_range vars typ

and check_type env typ : typ = check_type1 env [] typ

and infer_formula env vars formula : typ * formula =
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
          check (decode_range c) vars tsubst f
      | App (App (Const ("_", _), f), g) ->
          let h = match f, g with
            | Var (v, _), Const (c, _) ->
                let name = v ^ digit_to_sub c in
                if mem name (map fst vars) || is_declared env name
                  then _var name else App (f, g)
            | _ -> failwith "infer_formula" in
          check range vars tsubst h
      | App (Const (q, _), Lambda (x, (Sub _ as typ), g))
            when q = "(∀)" || q = "(∃)" || q = "{}" ->
          let join = if q = "(∀)" then implies else _and in
          let typ, g = match check_type1 env vars typ with
            | Sub p ->
                let typ = erase_sub (Sub p) in
                typ, join (App (p, Var (x, typ))) g
            | typ -> typ, g in
          check range vars tsubst (quant1 q x typ g)
      | App (Const ("{}", _), f) -> check range vars tsubst f
      | App (f, g) ->
          let possible = 
            let+ (tsubst, t, f) = check range vars tsubst f in
            let& (tsubst, u, g) = check range vars tsubst g in
            (tsubst, t, u, f, g) in
          let all =
            let+ (tsubst, t, u, f, g) = possible in
            match t with
              | Fun (v, w) -> (
                  match unify_types_or_pi is_var tsubst v u with
                    | Some tsubst -> [tsubst, w, App (f, g)]
                    | None -> [])
              | _ ->
                  let h = apply [Var ("·", unknown_type); f; g] in
                  check range vars tsubst h in (
          match all with
            | [] ->
                possible |> iter (fun (_, t, u, f, g) ->
                  printf "f = %s : %s, g = %s : %s\n"
                    (show_formula f) (show_type t) (show_formula g) (show_type u));
                errorf "can't apply" formula range
            | [sol] -> [sol]
            | _ ->
                let types = all |> map (fun (tsubst, typ, _) -> subst_types tsubst typ) in
                if all_same types
                  then errorf "ambiguous application" formula range
                else all)
      | Lambda (x, typ, f) ->
          let typ = check_type1 env vars typ in
          let+ (tsubst, t, f) = check range ((x, erase_sub typ) :: vars) tsubst f in
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
  match check empty_range vars [] formula with
    | [(tsubst, typ, f)] ->
        (subst_types tsubst typ, subst_types_in_formula tsubst f)
    | [] -> failwith "infer_formula"
    | _ -> errorf "ambiguous" formula (range_of formula)

let top_infer_with_type env f =
  let (typ, f) = infer_formula env [] f in
  (typ, b_reduce f)

let top_infer env f = snd (top_infer_with_type env f)

let check_dup_const env id typ kind range =
  if mem typ (id_types env id) then (
    let e = sprintf "duplicate %s: %s : %s\n" kind id (show_type typ) in
    error e range)

let check_const env (id, typ) : id * typ =
  let typ = check_type env typ in
  check_dup_const env id typ "constant declaration" empty_range;
  (id, typ)

let infer_const_decl env id typ : statement =
  let (id, typ) = check_const env (id, typ) in
  ConstDecl (id, typ)

(* Generate inductive axioms.  If the constructors are 0 : ℕ and s : ℕ → ℕ we produce
 *  1. ∀x:ℕ. 0 ≠ s(x)
 *  2. ∀x:ℕ.∀y.ℕ. s(x) ≠ s(y)
 *  3. ∀P:ℕ → 𝔹. P(0) → (∀x:ℕ.P(x) → P(s(x))) → (∀x:ℕ.P(x)) *)
let inductive_axioms id constructors : statement list =
  if constructors = [] then [] else (
  incr axiom_count;
  let t = Base id in
  let var v = Var (v, t) in
  let var_for typ v = if typ = t then [] else [v] in
  let fs1 =
    let& ((c, ctyp), (d, dtyp)) = all_pairs constructors in
    let cvar, dvar = var_for ctyp "x", var_for dtyp "y" in
    for_all_vars_typ (cvar @ dvar) t
      (_neq (apply (Const (c, ctyp) :: map var cvar))
            (apply (Const (d, dtyp) :: map var dvar))) in
  let fs2 =
    let+ (c, ctyp) = constructors in
    if is_fun ctyp then
      [for_all_vars_typ ["x"; "y"] t
        (implies (Eq (App (Const (c, ctyp), var "x"), App (Const (c, ctyp), var "y")))
                 (Eq (var "x", var "y")))] else [] in
  let f3 =
    let p = Var ("P", Fun (t, Bool)) in
    let preserves (c, ctyp) =
      if ctyp = t then App (p, Const (c, t)) else
        _for_all "x" t (implies (App (p, var "x"))
                                (App (p, App (Const (c, ctyp), var "x")))) in
    let fs = map preserves constructors in
    let concl = Eq (p, Lambda ("x", t, _true)) in
    _for_all "P" (Fun (t, Bool)) (fold_right implies1 fs concl) in
  let fs =
    (fs1 @ fs2 |> map (fun f -> (f, None))) @ [(f3, Some ("induction on " ^ id))] in
  fs |> mapi (fun i (f, name) ->
    let id = sprintf "%d.%c" !axiom_count (Char.chr (Char.code 'a' + i)) in
    Axiom { id; formula = f; name; defined = Some (last constructors) }))

let infer_type_definition env id constructors : statement list =
  if is_type_defined id env then (
    let e = sprintf "duplicate type definition: %s\n" id in
    error e empty_range);
  let type_decl = ConstDecl (id, Type) in
  let cs = map (check_const (type_decl :: env)) constructors |> map (fun (c, typ) ->
    if typ <> Base id && typ <> Fun (Base id, Base id) then (
      let e = sprintf "unsupported constructor type: %s\n" (show_type typ) in
      error e empty_range);
    (c, typ)) in
  type_decl :: map mk_const_decl cs @ inductive_axioms id cs

let infer_definition env f : id * typ * formula =
  (* f has the form ∀σ₁...σₙ v₁...vₙ (C φ₁ ... φₙ = ψ) .  We check types and build
    * a formula of the form ∀σ₁...σₙ v₁...vₙ (C σ₁...σₙ φ₁ ... φₙ = ψ) .*)
  let (vs, f) = gather_quant "(∀)" (strip_range f) in
  let (type_vars, vars) = vs |> partition (fun (_, typ) -> typ = Type) in
  let univ = map fst type_vars in
  let vars = vars |> map (fun (v, typ) -> (v, check_type1 env type_vars typ)) in
  let vs = type_vars @ vars in (
  match strip_range f with
    | Eq (f, g) | App (App (Const ("(↔)", _), f), g) | App (App (Const ("(→)", _), g), f)->
        let (c, args) = collect_args (strip_range f) in
        let (c, args) = match c with
          | Const (c, _) when c.[0] = '@' -> (hd args, tl args)
          | _ -> (c, args) in
        let (c, decl_type, args) = match c with
          | Const (":", Fun (typ, _)) -> (hd args, Some (check_type env typ), tl args)
          | _ -> (c, None, args) in (
        match strip_range c with
          | Const (id, _) | Var (id, _) ->
              let infer f = infer_formula env vs f in
              let arg_types, args = unzip (map infer args) in
              let g_type, g = infer g in
              let c_type = mk_fun_types arg_types g_type in
              decl_type |> Option.iter (fun t -> if t <> c_type then (
                  printf "infer_definition: declared type = %s, actual = %s\n"
                    (show_type t) (show_type c_type);
                  failwith "infer_definition")
              );
              let c_type = mk_pi_types univ c_type in
              let type_args = univ |> map (fun v -> Var (v, Type)) in
              let eq = if g_type = Bool then _iff else mk_eq in
              let body = for_all_vars_types vs @@
                eq (apply (Const (id, c_type) :: type_args @ args)) g in
              (id, c_type, body)
          | _ -> failwith "definition expected (1)")
    | _ -> failwith "definition expected (2)")

let check_ref env (name, range) : id =
  match find_opt (fun s -> stmt_name s = Some name) env with
    | Some stmt -> stmt_ref stmt
    | None -> error ("theorem not found: " ^ name) range

let chain_comparisons env f : (formula * string list) list =
  let fs, ops = collect_cmp f in
  let& (f, reasons) = join_comparisons fs ops in
  (f, map (check_ref env) reasons)

(* Restore type variables for any type that has become a constant in the
 * local environment. *)
let rec with_type_vars env typ : typ = match typ with
  | Base id ->
      if is_type_defined id env then TypeVar id else typ
  | _ -> map_type (with_type_vars env) typ

let mk_thm env lenv f by : statement list = Theorem {
    id = ""; name = None; formula = top_infer env f;
    steps = []; by; is_step = true; range = range_of f } :: lenv

let assert_chain env lenv in_proof f by =
  let eqs, reasons = unzip (chain_comparisons env f) in
  let reasons : str list list =
    let rs, last = split_last reasons in
    rs @ [last @ by] in
  let eqs' = map strip_range eqs in
  let concl =
    if in_proof && length eqs' >= 2 && count_false is_eq eqs' <= 1 then
      let op = match find_opt (Fun.negate is_eq) eqs' with
        | Some eq -> comparison_op eq
        | None -> "=" in
      match is_comparison (hd eqs'), is_comparison (last eqs') with
        | Some (_, a, _), Some (_, _, b) ->
            apply_comparison op a b
        | _ -> failwith "block_steps"
    else multi_and eqs in
  (map2 (mk_thm env lenv) eqs reasons, concl)

let rec blocks_steps in_proof env lenv blocks : statement list list * formula =
  match blocks with
    | [] -> ([], _true)
    | block :: rest ->
        let (fs, concl) = block_steps in_proof env lenv block in
        let hyp = Hypothesis ("hyp", top_infer env concl) in
        let (gs, final_concl) = blocks_steps in_proof (hyp :: env) (hyp :: lenv) rest in
        ( fs @ gs,
          if rest = [] then concl
          else match last blocks with
            | Block (Assume _, _) -> _and concl final_concl
            | _ -> final_concl)

and block_steps in_proof env lenv (Block (step, children)) : statement list list * formula =
  let child_steps stmts = blocks_steps in_proof (stmts @ env) (stmts @ lenv) children in
  let const_decl (id, typ) =
    if typ = Type then infer_type_definition env id [] else [infer_const_decl env id typ] in
  let const_decls ids_typs = rev (concat_map const_decl ids_typs) in
  match step with
    | Assert (f, reason) ->
        let fs = gather_and f in
        let reasons = map (Fun.const []) (tl fs) @ [map (check_ref env) reason] in
        let steps, concls = unzip (map2 (assert_chain env lenv in_proof) fs reasons) in
        (concat steps, multi_and concls)
    | Let ids_types ->
        let resolve_subtype (id, typ) = match typ, check_type env typ with
          | Sub f, (Sub f' as t) ->
              let ptyp = erase_sub t in
              let hyp = Hypothesis ("hyp", App (f', Const (id, ptyp))) in
              [(id, f)], [hyp], (id, ptyp)
          | _ -> [], [], (id, typ) in
        let subids, hyps, ids_types = unzip3 (map resolve_subtype ids_types) in
        let subids, hyps = concat subids, concat hyps in
        let decls = const_decls ids_types in
        let (fs, concl) = child_steps (rev hyps @ decls) in
        let imps = multi_and (let+ (id, f) = subids in [App (f, _var id)]) in
        (fs, for_all_vars_types_if_free ids_types (implies imps concl))
    | LetDef (_id, _typ, g) ->
        let (id, typ, f) = infer_definition env g in
        let (fs, concl) =
          child_steps [Hypothesis ("hyp", f); ConstDecl (id, typ)] in
        let mk_concl h = _for_all id (with_type_vars lenv typ) (implies h concl) in
        let concl = match g with
          | Eq (Const (id, typ), value) ->
              if is_free_in id concl then
                if is_lambda_or_set_comp value
                  then mk_concl (Eq (Var (id, typ), value))
                  else rsubst1 concl value id
              else concl
          | _ -> mk_concl g in
        (fs, concl)
    | Assume a ->
        let (ids_typs, f) = gather_exists a in
        let decls = const_decls ids_typs in
        let decls = Hypothesis ("hyp", top_infer (decls @ env) f) :: decls in
        let (fs, concl) = child_steps decls in
        (fs, if concl = _true then _true
             else for_all_vars_types ids_typs (implies f concl))
    | IsSome (ids_types, g, reason) ->
        let by = map (check_ref env) reason in
        let ex = exists_vars_types ids_types g in
        let decls = rev (map (fun (id, typ) -> infer_const_decl env id typ) ids_types) in
        let stmts = Hypothesis ("hyp", top_infer (decls @ env) g) :: decls in
        let (fs, concl) = child_steps stmts in
        (mk_thm env lenv ex by :: fs,
         if concl = _true then ex else
         if any_free_in (map fst ids_types) concl
            then exists_vars_types ids_types concl else concl)
    | Escape | Group _ -> failwith "block_formulas"

let trim_lets steps : proof_step list =
  let vs = unique (steps |> concat_map step_free_vars) in
  let+ step = steps in (
  match step with
    | Let ids_types ->
        let ids_types = ids_types |> filter (fun (id, _) ->
          mem id vs || id = "·") in  (* "·" may not be explicitly present *)
        if ids_types = [] then [] else [Let ids_types]
    | _ -> [step])

let collect_lets steps : id list =
  steps |> concat_map (function
    | Let ids_types -> map fst ids_types
    | _ -> [])

let duplicate_lets vars steps : bool =
  let rec check = function
    | [] -> false
    | step :: steps ->
        match step with
          | Assert _ -> false
          | Let ids_types ->
              let ids = map fst ids_types in
              overlap ids vars || check steps
          | _ -> check steps in
  check steps

let free_type_vars_in_steps steps : id list =
  let rec find steps = match steps with
    | [] -> []
    | step :: steps ->
        let type_vars = step_free_type_vars step @ find steps in
        match step with
          | Let ids_typs ->
              let decl_types = map fst (ids_typs |> filter (fun (_, typ) -> typ = Type)) in
              subtract type_vars decl_types
          | _ -> type_vars in
  unique (find steps)

let count_sub_index num sub_index =
  if sub_index = "" then sprintf "%d" num
  else sprintf "%d.%s" num sub_index

let rec gather_eif f = match collect_args f with
  | (c, [_type; p; f; g]) when c = _eif_c ->
      (p, f) :: gather_eif g
  | (c, [_type]) when c = undefined -> []
  | _ -> failwith "gather_eif"

let rec insert_conclusion_step blocks init last_step : block list =
  match init, blocks with
    | [], [] -> failwith "insert_conclusion_step"
    | [], blocks ->
        let first_blocks, last_block = split_last blocks in
        let append = blocks @ [Block (last_step, [])] in (
        match last_block with
          | Block (LetDef _ as parent, blocks)
          | Block (IsSome _ as parent, blocks) ->
              let f = get_assert last_step in
              if not (any_free_in (step_decl_vars parent) f) then
                first_blocks @ [Block (parent, insert_conclusion_step blocks [] last_step)]
              else append
          | Block (Let ids_typs, blocks) ->
              let f = get_assert last_step in
              let (xs, g) = gather_for_all f in
              let strip (id, typ) = (id, strip_type_range typ) in
              if list_starts_with (map strip ids_typs) (map strip xs) then (
                let h = for_all_vars_types (drop (length ids_typs) xs) g in
                first_blocks @
                  [Block (Let ids_typs, insert_conclusion_step blocks [] (mk_assert h))])
              else append
          | _ -> append)
    | step :: steps, [Block (step', blocks)] ->
        assert (step = step');
        [Block (step, insert_conclusion_step blocks steps last_step)]
    | _ -> failwith "insert_conclusion_step"

let generalize_types steps =
  let type_vars = free_type_vars_in_steps steps in
  (type_vars |> map (fun id -> Let [(id, Type)])) @ steps

let rec expand_proof id name env steps proof_steps : formula * statement list list =
  let steps = generalize_types (trim_lets steps) in
  let blocks0 = chain_blocks steps [] in
  let (_, concl) = blocks_steps false env [] blocks0 in
  let stmtss = if proof_steps = [] then [] else
    let (init, last_step) = split_last steps in
    let include_init = not (duplicate_lets (collect_lets init) proof_steps) in
    if !(opts.show_structure) then (
      printf "%s:\n\n" (theorem_name id name);
      if !debug > 1 then (
        let show_steps = (if include_init then init else []) @ proof_steps in
        show_steps |> iter (fun s -> print_endline (show_proof_step s));
        print_newline ()
      );
    );
    let blocks = infer_blocks env proof_steps in
    let blocks =
      if include_init
        then insert_conclusion_step (chain_blocks init blocks) init last_step
      else blocks @ [Block (mk_assert concl, [])] in
    if !(opts.show_structure) then print_blocks blocks;
    let (stmtss, _concl) = blocks_steps true env [] blocks in
    map rev stmtss in
  (top_infer env concl, stmtss)

and translate_if_block f : formula option * formula * formula option =
  let vs, f' = gather_for_all f in
  match f' with
    | Eq (x, g) when head_of g = _eif_c ->
        let conds_vals = gather_eif g in
        let conds, vals = unzip conds_vals in
        let justify = multi_and (multi_or conds ::
          let& (c, d) = all_pairs conds in
          _not (_and c d)) in
        let eqs = multi_and (
          let& (c, d) = conds_vals in
          implies c (Eq (x, d))
        ) in
        let eq_some = for_all_vars_types vs (multi_or (let& v = vals in Eq (x, v))) in
        Some (for_all_vars_types vs justify), for_all_vars_types vs eqs, Some eq_some
    | _ -> None, f, None

and infer_stmt env stmt : statement list =
  match stmt with
    | HTypeDef (id, constructors, _name) -> infer_type_definition env id constructors
    | HConstDecl (id, typ) -> [infer_const_decl env id typ]
    | HDefinition (f, justification) ->
        let (id, typ, f') = infer_definition env (generalize f) in
        check_dup_const env id typ "definition" (range_of f);
        let justify, f', eq_some = translate_if_block f' in
        let justify =
          let& j = opt_to_list justify in
          incr theorem_count;
          let thm_id = string_of_int !theorem_count in
          let name = Some ("justify " ^ id) in
          let steps = if justification = [] then [] else
            snd (expand_proof thm_id name env [mk_assert j] justification) in
          Theorem { id = thm_id; name; formula = j; steps; by = [];
                    is_step = false; range = empty_range } in
        let gs =
          let& eq_some = opt_to_list eq_some in
          incr axiom_count;
          Axiom { id = string_of_int !axiom_count; formula = eq_some;
                  name = Some (id ^ "_eq_some"); defined = None } in
        justify @ [ConstDecl (id, typ); Definition (id, typ, f')] @ gs
    | HAxiomGroup (id_typ, haxioms) ->
        incr axiom_count;
        let+ { sub_index; name; steps } = haxioms in
        let id = count_sub_index !axiom_count sub_index in
        let blocks = infer_blocks env (generalize_types steps) in
        let (_, f) = blocks_steps false env [] blocks in
        [Axiom { id; formula = top_infer env f; name; defined = id_typ }]
    | HTheoremGroup htheorems ->
        incr theorem_count;
        let check env htheorem : statement list * statement =
          let { sub_index; name; steps; proof_steps } = htheorem in
          let id = count_sub_index !theorem_count sub_index in
          let (f, stmts) = expand_proof id name env steps proof_steps in
          let range = match (last steps) with
            | Assert (f, _) -> range_of f
            | _ -> failwith "assert expected" in
          let stmt = Theorem { id; name; formula = f; steps = stmts;
                               by = []; is_step = false; range } in
          (stmt :: env, stmt) in
        snd (fold_left_map check env htheorems)

and check_stmts check_stmt initial_env stmts : statement list =
  let check env stmt =
    let stmts = check_stmt env stmt in
    (stmts @ env, stmts) in
  concat (snd (fold_left_map check initial_env stmts))

let check_module check_stmt checked md : (smodule list, string * frange) result =
  let env : statement list = module_env md checked in
  try 
    let modd = { md with stmts = check_stmts check_stmt env md.stmts } in
    Ok (modd :: checked)
  with
    | Check_error (err, pos) ->
        Error (err, (md.filename, pos))

let check_modules check_stmt modules : (smodule list, string * frange) result =
  fold_left_res (check_module check_stmt) [] modules |> Result.map rev

let infer_modules = check_modules infer_stmt

let type_as_id typ = str_replace " " "" (show_type typ)

let tuple_constructor types : string =
  str_join (tuple_cons (length types) :: map show_type types)

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

let check_subtypes typ : unit =
  let rec check typ = match typ with
    | Sub _ -> failwith "unencoded subtype"
    | _ -> map_type check typ
  in ignore (check typ)

let check_formula_subtypes f = iter check_subtypes (formula_types f)
  
let encode_formula consts f : formula =
  let rec encode f =
    match collect_args f with
      | (Const (":", _), [g]) ->  (* type ascription *)
          encode g
      | (Const (c, typ), args) when is_tuple_constructor c ->
          apply_types c typ (map encode args)
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
  let f = encode f in
  check_formula_subtypes f;
  f

let encode_stmt consts stmt : statement =
  let encode f = b_reduce (encode_formula consts f) in
  map_statement1 (encode_id consts) encode_type encode stmt

let encode_module consts md : smodule =
  { md with stmts = map (encode_stmt consts) md.stmts }

let basic_check env f : typ * formula =
  let rec check vars f : typ * formula = match f with
    | Const (id, typ) -> (
        if id = _type then (Type, f) else
        match filter_map (is_const_decl id) env with
          | [] ->
              if mem id logical_ops
                then (typ, Const (id, typ))
                else errorf "undefined constant" f empty_range
          | [typ] -> (typ, Const (id, typ))
          | _ -> failwith "ambiguous constant")
    | Var (id, _) -> (
        match assoc_opt id vars with
          | Some typ -> (typ, Var (id, typ))
          | None -> errorf "undefined variable" f empty_range)
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
          errorf "can't compare" f empty_range);
        (Bool, Eq (g, h)) in
  check [] f

let fix_by env by : string =
  match env |> find_opt (fun stmt -> stmt_id stmt = by) with
    | Some stmt -> stmt_ref stmt
    | _ -> error ("formula not found: " ^ by) empty_range

let basic_check_stmt env stmt : statement list =
  let bool_check f = match basic_check env f with
    | (Bool, f) -> f
    | _ -> failwith "boolean expected" in
  let stmt = map_statement (check_type env) bool_check stmt in
  [match stmt with
    | Theorem ({ by; _ } as thm) -> Theorem { thm with by = map (fix_by env) by }
    | _ -> stmt]

let basic_check_modules = check_modules basic_check_stmt

let check modules : (smodule list, string * frange) result =
  axiom_count := 0;
  theorem_count := 0;
  let** modules = infer_modules modules in
  let consts = filter_map decl_var (concat_map (fun m -> m.stmts) modules) in
  Ok (map (encode_module consts) modules)
