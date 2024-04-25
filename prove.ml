open List
open Printf

open Logic
open Statement
open Util

let debug = ref 0

let formula_counter = ref 0

type pformula = {
  id: int;
  rule: string;
  parents: pformula list;
  rewrites: pformula list;
  simp: bool;
  formula: formula;
  goal: bool;
  delta: float;
  cost: float
}

let print_formula with_origin prefix pformula =
  let prefix =
    if pformula.id > 0 then prefix ^ sprintf "%d. " (pformula.id) else prefix in
  let origin =
    if with_origin then
      let parents = pformula.parents |> map (fun p -> string_of_int (p.id)) in
      let rule = if pformula.rule <> "" then [pformula.rule] else [] in
      let rewrites = pformula.rewrites |> map (fun r -> r.id) in
      let rw = if rewrites = [] then []
        else [sprintf "rw(%s)" (comma_join (map string_of_int rewrites))] in
      let simp = if pformula.simp then ["simp"] else [] in
      let all = parents @ rule @ rw @ simp in
      sprintf " [%s]" (comma_join all)
    else "" in
  printf "%s%s {%s%.2f}\n"
    (indent_with_prefix prefix (show_multi pformula.formula))
    origin (if pformula.goal then "g " else "") pformula.cost

let dbg_print_formula with_origin prefix pformula =
  if !debug > 0 then print_formula with_origin prefix pformula

let is_inductive pformula = match kind pformula.formula with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false

let adjust_delta parents delta =
  if exists is_inductive parents then 1.0 else delta

let merge_cost parents = match parents with
    | [] -> 0.0
    | [p] -> p.cost
    | _ ->
      let ancestors = search parents (fun p -> p.parents) in
      sum (ancestors |> map (fun p -> p.delta))

let total_cost parents delta =
  merge_cost parents +. adjust_delta parents delta

let max_cost = 1.3

let mk_pformula rule parents formula delta =
  let (as_goal, delta) = if delta = -1.0 then (true, 0.0) else (false, delta) in
  { id = 0; rule; rewrites = []; simp = false; parents; formula;
    goal = as_goal || exists (fun p -> p.goal) parents;
    delta = adjust_delta parents delta;
    cost = total_cost parents delta }

let rec number_formula pformula =
  if pformula.id > 0 then pformula
  else
    let parents = map number_formula pformula.parents in
    incr formula_counter;
    let p = { pformula with parents; id = !formula_counter } in
    dbg_print_formula true "" p;
    p

let create_pformula rule parents formula delta =
  number_formula (mk_pformula rule parents formula delta)

(* Symbol precedence.  ⊥ > ⊤ have the lowest precedence.  We group other
 * symbols by arity, then (arbitrarily) alphabetically. *)
 let const_gt f g =
  match f, g with
    | Const (c, _), Const ("⊤", _) -> c <> "⊤"
    | Const (c, _), Const ("⊥", _) -> c <> "⊥"
    | Const (f, f_type), Const (g, g_type) ->
        (arity f_type, f) > (arity g_type, g)
    | _ -> failwith "const_gt"

let rec lex_gt gt ss ts = match ss, ts with
  | [], [] -> false
  | s :: ss, t :: ts ->
    gt s t || s = t && lex_gt gt ss ts
  | _ -> failwith "lex_gt"

let rec inc_var x = function
  | [] -> [(x, 1)]
  | (y, n) :: rest ->
      if x = y then (y, n + 1) :: rest
      else (y, n) :: inc_var x rest

let count_vars f =
  let rec count acc = function
    | Var (v, _) -> inc_var v acc
    | f -> fold_left_formula count acc f in
  count [] f

let lookup_var v vars = opt_default (assoc_opt v vars) 0

let sym_weight for_kb c typ = match c with
  | "∀" | "∃" -> if for_kb then 1_000_000 else 0
  | _ -> if arity typ = 1 then 2 else 1

let term_weight for_kb =
  let rec weight = function
    | Const (c, typ) -> sym_weight for_kb c typ
    | Var _ -> 1
    | App (f, g) | Eq (f, g) -> weight f + weight g
    | Lambda (_, _, f) -> weight f in
  weight

let basic_weight = term_weight false

let unary_check s t = match s, t with
  | App (Const (f, _), g), Var (v, _) ->
      let rec check = function
        | App (Const (f', _), g) -> f' = f && check g
        | Var (v', _) -> v' = v
        | _ -> false in
      check g
  | _ -> false

(* Knuth-Bendix ordering on first-order terms *)
let rec kb_gt s t =
  let s_vars, t_vars = count_vars s, count_vars t in
  (s_vars |> for_all (fun (v, n) -> n >= lookup_var v t_vars)) &&
    let ws, wt = term_weight true s, term_weight true t in
    ws > wt || ws = wt && (
      unary_check s t ||
      is_app_or_const s && is_app_or_const t &&
          let (f, ss), (g, ts) = collect_args s, collect_args t in
          const_gt f g || f = g && lex_gt kb_gt ss ts)

let get_index x map =
  match index_of_opt x !map with
    | Some i -> length !map - 1 - i
    | None ->
        map := x :: !map;
        length !map - 1

(* Map higher-order terms to first-order terms as described in
 * Bentkamp et al, section 3.9 "A Concrete Term Order". *)
 let encode_term type_map fluid_map t =
  let encode_fluid t = _var ("@v" ^ string_of_int (get_index t fluid_map)) in
  let encode_type typ = _const ("@t" ^ string_of_int (get_index typ type_map)) in
  let rec fn outer t =
    let prime = if outer = [] then "" else "'" in
    let lookup_var v = match index_of_opt v outer with
      | Some i -> _const ("@d" ^ string_of_int i)
      | None -> _var v in
    let u = match t with
      | Const _ -> t
      | Var (v, _) -> lookup_var v
      | App _ ->
          let (head, args) = collect_args t in
          let head = match head with
            | Var (v, _) -> lookup_var v
            | _ -> head in (
          match head with
            | Var _ -> encode_fluid (apply (head :: args))
            | Const (q, _) when q = "∀" || q = "∃" -> (
                match args with
                  | [Lambda (x, typ, f)] ->
                      let q1 = _const (q ^ prime) in
                      apply [q1; encode_type typ; fn (x :: outer) f]
                  | _ -> failwith "encode_term")
            | Const _ -> apply (head :: map (fn outer) args)
            | _ -> failwith "encode_term")
      | Lambda (x, typ, f) ->
          if is_ground t then
            apply [_const "λ"; encode_type typ; fn (x :: outer) f]
          else encode_fluid t (* assume fluid *)
      | Eq (t, u) ->
          apply [_const "="; encode_type (type_of t); fn outer t; fn outer u] in
    match u with
      | Var (v, typ) -> Var (v ^ prime, typ)
      | u -> u
  in fn [] t

let term_gt s t =
  let type_map, fluid_map = ref [], ref [] in
  let s1 = encode_term type_map fluid_map s in
  let t1 = encode_term type_map fluid_map t in
  kb_gt s1 t1

let term_ge s t = s = t || term_gt s t

let terms = function
  | Eq (f, g) -> (true, f, g)
  | App (Const ("¬", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("¬", _), f) -> (true, f, _false)
  | f -> (true, f, _true)

let lit_to_multi f =
  let eq, t, u = terms f in
  if eq then [[t]; [u]] else [[t; _false]; [u; _false]]

let lit_gt f g =
  multi_gt (multi_gt term_gt) (lit_to_multi f) (lit_to_multi g)

let clause_gt = multi_gt lit_gt

let split f = match bool_kind f with
  | Binary ("∨", s, t) -> Some (s, t)
  | Binary ("→", s, t) -> Some (_not s, t)
  | _ -> None

(*      s = ⊤ ∨ C                 s = ⊥ ∨ C
      ═════════════   oc       ══════════════   oc
        oc(s) ∨ C                oc(¬s) ∨ C

        oc(s ∨ t) = s = ⊤ ∨ t = ⊤
        oc(s → t) = s = ⊥ ∨ t = ⊤
        oc(∀x.s) = s[y/x] = ⊤  (y not in s or C)
        oc(∃x.s) = s[k(y̅)/x] = ⊤
        oc(¬(s ∧ t)) = s = ⊤ ∨ t = ⊥
        oc(¬(∀x.s)) = s[k(y̅)/x] = ⊥
        oc(¬(∃x.s)) = s[y/x] = ⊥  (y not in s or C)
        
        k is a new constant
        y̅ are all free variables in ∃x.s
*)

let clausify_step pformula lits =
  let rec new_lits f = match split f with
    | Some (s, t) -> Some ([s; t], [])
    | None -> match bool_kind f with
      | Quant ("∀", x, typ, f) ->
          let f =
            let vars = concat_map free_vars lits in
            if mem x vars then 
              let y = next_var x vars in
              subst1 f (Var (y, typ)) x
            else f in
          Some ([f], [f])
      | Quant ("∃", x, typ, g) ->
          let vars_types = free_vars_types f in
          let skolem_type = fold_right1 mk_fun_type (typ :: map snd vars_types) in
          let skolem_const = Const (sprintf "%s%d" x pformula.id, skolem_type) in
          let skolem = apply (skolem_const :: map mk_var' vars_types) in
          let g = subst1 g skolem x in
          Some ([g], [g])
      | Not g -> (match bool_kind g with
        | Binary ("→", f, g) -> Some ([_and f (_not g)], [])
        | Quant ("∀", x, typ, g) ->
            new_lits (_exists x typ (_not g))
        | Quant ("∃", x, typ, g) ->
            new_lits (_for_all x typ (_not g))
        | _ -> None)
      | _ -> None in
  let rec loop before = function
    | [] -> None
    | lit :: after ->
        match new_lits lit with
          | Some (lits, exposed) -> Some (rev before @ lits @ after, lits, exposed)
          | None -> loop (lit :: before) after in
  if lits = [] then
    let f = pformula.formula in
    Some ([f], [f], [f])  (* initial step *)
  else loop [] lits

let clausify_steps pformula =
  let rec run lits =
    match clausify_step pformula lits with
      | None -> []
      | Some ((lits, _, _) as step) -> step :: run lits in
  run []

let run_clausify pformula rule =
  let+ (lits, new_lits, _) = clausify_steps pformula in
  let+ f = new_lits in
  rule pformula (remove1 f lits) f
  
let clausify pformula =
  let (lits, _, _) = last (clausify_steps pformula) in
  lits

let prefix_vars f =
  let rec prefix outer = function
    | Var (x, typ) when not (mem x outer) ->
        Var ("$" ^ x, typ)
    | Lambda (x, _typ, f) ->
        Lambda (x, _typ, prefix (x :: outer) f)
    | f -> map_formula (prefix outer) f
  in prefix [] f

let unprefix_vars f =
  let rec build_map all_vars = function
    | [] -> []
    | var :: rest ->
        if var.[0] = '$' then
          let v = string_from var 1 in
          let w = next_var v all_vars in
          (var, w) :: build_map (w :: all_vars) rest
        else build_map all_vars rest in
  let var_map = build_map (all_vars f) (free_vars f) in
  let rec fix outer = function
    | Var (v, typ) as var when not (mem v outer) ->
        if v.[0] = '$' then Var (assoc v var_map, typ) else var
    | Lambda (x, _typ, f) ->
      Lambda (x, _typ, fix (x :: outer) f)
    | f -> map_formula (fix outer) f in
  fix [] f
  
let subterms is_blue t =
  let rec gather parent_eq acc t = (t, parent_eq) :: match t with
    | App _ ->
        let (head, args) = collect_args t in
        if head = c_for_all || head = c_exists then
          if is_blue then match args with
            | [Lambda (_x, _typ, f)] -> gather parent_eq acc f
            | _ -> acc
          else acc
        else fold_left (gather parent_eq) acc args
    | Eq (f, g) ->
        let acc = gather ((f, g) :: parent_eq) acc f in
        gather ((g, f) :: parent_eq) acc g
    | _-> acc in
  gather [] [] t

let green_subterms = subterms false
let blue_subterms t = map fst (subterms true t)

let is_fluid t = match t with
  | App _ ->
      let (head, _args) = collect_args t in
      is_var head
  | Lambda _ -> not (is_ground t) (* approximate *)
  | _ -> false

let is_applied_symbol f = match bool_kind f with
  | True | False | Not _ | Binary _ -> true
  | _ -> false

let is_eligible sub parent_eq =
  parent_eq |> for_all (fun (s, t) ->
    not (term_gt (subst_n sub t) (subst_n sub s)))

(* Clausify ignoring quantifiers and conjunctions *)
let rec mini_clausify f = match bool_kind f with
  | Binary ("∨", f, g) -> mini_clausify f @ mini_clausify g
  | Binary ("→", f, g) -> mini_clausify (_not f) @ mini_clausify g
  | Not g -> (match bool_kind g with
    | Binary ("∧", f, g) -> mini_clausify (_not f) @ mini_clausify (_not g)
    | _ -> [f])
  | _ -> [f]

let top_positive u c sub inductive =
  let (pos, _, _) = terms u in 
  let cs = mini_clausify c in
  pos && mem u cs &&
    (inductive || is_maximal lit_gt (rsubst sub u) (map (rsubst sub) cs))

let eq_pairs t t' = [(t, t'); (t', t)] |>
  filter (fun (t, t') -> not (term_ge t' t))

(*      D:[D' ∨ t = t']    C⟨u⟩
 *    ───────────────────────────   sup
 *          (D' ∨ C⟨t'⟩)σ             σ ∈ csu(t, u)
 *
 *     (i) u is not fluid
 *     (ii) u is not a variable
 *     (iii) tσ ≰ t'σ
 *     (iv) the position of u is eligible in C w.r.t. σ
 *     (v) Cσ ≰ Dσ
 *     (vi) t = t' is maximal in D w.r.t. σ
 *     (vii) tσ is not a fully applied logical symbol
 *     (viii) if t'σ = ⊥, u is at the top level of a positive literal  *)

let super dp d' t_t' cp c c1 =
  let pairs = match terms t_t' with
    | (false, _, _) -> (match bool_kind t_t' with
        | Not (Eq _ as eq) -> [(eq, _false)]
        | _ -> failwith "super")
    | (true, t, t') -> eq_pairs t t' in   (* iii: pre-check *)
  let+ (t, t') = pairs in
  let+ (u, parent_eq) = green_subterms c1 |>
    filter (fun (u, _) -> not (is_var u || is_fluid u)) in  (* i, ii *)
  match unify t u with
    | None -> []
    | Some sub ->
        let d'_s = map (rsubst sub) d' in
        let t_s, t'_s = rsubst sub t, rsubst sub t' in
        let t_eq_t'_s = Eq (t_s, t'_s) in
        let d_s = t_eq_t'_s :: d'_s in
        let c_s = map (rsubst sub) c in
        let c1_s = rsubst sub c1 in
        if term_ge t'_s t_s ||  (* iii *)
            not (is_maximal lit_gt c1_s c_s) ||  (* iv *)
            not (is_eligible sub parent_eq) ||  (* iv *)
            t'_s <> _false && clause_gt d_s c_s ||  (* v *)
            not (is_maximal lit_gt t_eq_t'_s d'_s) ||  (* vi *)
            is_applied_symbol t_s || (* vii *)
            t'_s = _false && not (top_positive u c1 sub (is_inductive cp))  (* viii *)
        then [] else
          let c1_t' = replace_in_formula t' u c1 in
          let c_s = replace1 (rsubst sub c1_t') c1_s c_s in
          let e = multi_or (d'_s @ c_s) in
          let tt'_show = str_replace "\\$" "" (show_formula (Eq (t, t'))) in
          let u_show = show_formula u in
          let rule = sprintf "sup: %s / %s" tt'_show u_show in
          let w, cw = basic_weight e, basic_weight cp.formula in
          let cost =
            if w < cw then 0.01 else if w = cw then 0.02 else 1.0 in
          [mk_pformula rule [dp; cp] (unprefix_vars e) cost]

let all_super dp cp =
  if total_cost [dp; cp] 0.0 > max_cost ||
    dp = cp && is_inductive dp then []
  else (
    let d_steps, c_steps = clausify_steps dp, clausify_steps cp in
    let+ (dp, d_steps, cp, c_steps) =
      [(dp, d_steps, cp, c_steps); (cp, c_steps, dp, d_steps)] in
    let+ (d_lits, new_lits, _) = d_steps in
    let d_lits, new_lits = map prefix_vars d_lits, map prefix_vars new_lits in
    let+ d_lit = new_lits in
    let+ (c_lits, _, exposed_lits) = c_steps in
    let+ c_lit = exposed_lits in
    super dp (remove1 d_lit d_lits) d_lit cp c_lits c_lit)

(*      C' ∨ u ≠ u'
 *     ────────────   eres
 *         C'σ          σ ∈ csu(s, t)  *)

let eres cp c' c_lit =
  match terms c_lit with
    | (true, _, _) -> []
    | (false, u, u') ->
        match unify u u' with
          | None -> []
          | Some sub ->
              let c1 = map (rsubst sub) c' in
              [mk_pformula "eres" [cp] (multi_or c1) 0.01]

let all_eres cp = run_clausify cp eres

(*     (s ∧ t) ∨ C
 *    ═══════════════   split
 *     s ∨ C, t ∨ C      *)

let all_split pformula =
  let rec run lits =
    match clausify_step pformula lits with
      | None -> []
      | Some (lits, new_lits, _) ->
          let split_on lit = match bool_kind lit with
            | Binary ("∧", f, g) ->
                let new_formulas = [f; g] |> map (fun t ->
                  let u = multi_or (replace1 t lit lits) in
                  mk_pformula "split" [pformula] u 0.02) in
                Some new_formulas
            | _ -> None in
          match find_map split_on new_lits with
            | Some new_formulas -> new_formulas
            | None -> run lits in
  if is_inductive pformula then [] else run []

let update p rewriting f =
  let (r, simp) = match rewriting with
    | Some p -> ([p], false)
    | None -> ([], true) in
  if p.id = 0 then
    { p with rewrites = union r p.rewrites; simp = p.simp || simp; formula = f }
  else
    { id = 0; rule = ""; rewrites = r; simp; parents = [p];
      goal = p.goal; delta = 0.0; cost = p.cost; formula = f }

(*     t = t'    C⟨tσ⟩
 *   ═══════════════════   rw
 *     t = t'    C⟨t'σ⟩
 *
 *   (i) tσ > t'σ
 *   (ii) C > (t = t')σ   *)

let rewrite dp cp =
  let pairs = match remove_universal dp.formula with
    | Eq (t, t') -> eq_pairs t t' (* i: pre-check *)
    | App (Const ("¬", _), Eq _) as neq -> [(neq, _true)]
    | _ -> [] in
  let+ (t, t') = pairs in
  let t, t' = prefix_vars t, prefix_vars t' in
  let c = cp.formula in
  let+ u = blue_subterms c in
  match try_match t u with
    | Some sub ->
        let t_s, t'_s = u, rsubst sub t' in
        if term_gt t_s t'_s &&  (* (i) *)
           clause_gt (clausify cp) [Eq (t_s, t'_s)] then (* (ii) *)
          let e = replace_in_formula t'_s t_s c in
          [update cp (Some dp) e]
        else []
    | _ -> []

let rewrite_from ps q =
  let rewrite_opt cp dp =
    match rewrite dp cp with
      | new_cp :: _ -> Some new_cp
      | _ -> None in
  find_map (rewrite_opt q) ps

let rec expand f = match split f with
  | Some (s, t) -> expand s @ expand t
  | None -> [f]

let rec simp f = match bool_kind f with
  | Not f ->
      let f = simp f in (
      match bool_kind f with
        | True -> _false
        | False -> _true
        | Not g -> g
        | _ -> _not f)
  | Binary (op, p, q) ->
      let p, q = simp p, simp q in (
      match op, bool_kind p, bool_kind q with
        | "∧", True, _ -> q
        | "∧", _, True -> p
        | "∧", False, _ -> _false
        | "∧", _, False -> _false
        | "∨", True, _ -> _true
        | "∨", _, True -> _true
        | "∨", False, _ -> q
        | "∨", _, False -> p
        | "→", True, _ -> q
        | "→", _, True -> _true
        | "→", False, _ -> _true
        | "→", _, False -> simp (_not p)
        | "→", t, u when t = u -> _true
        | _ -> logical_op op p q)
  | Quant (q, x, typ, f) ->
      let f = simp f in (
      match bool_kind f with
        | True -> _true
        | False -> _false
        | _ -> quant q x typ f)
  | Other (Eq (f, g)) ->
      let f, g = simp f, simp g in
      if f = g then _true else Eq (f, g)
  | _ -> map_formula simp f

let simplify pformula =
  let f = simp pformula.formula in
  if f = pformula.formula then pformula
  else update pformula None f

let is_tautology f = mem _true (expand f)

let associative_axiom f =
  let is_assoc (f, g) = match kind f, kind g with
    | Binary (op, f1, Var (z, _)), Binary (op3, Var (x', _), g1) -> (
        match kind f1, kind g1 with
          | Binary (op2, Var (x, _), Var (y, _)),
            Binary (op4, Var (y', _), Var (z', _))
              when op = op2 && op2 = op3 && op3 = op4 &&
                  (x, y, z) = (x', y', z') -> Some op
          | _ -> None)
    | _ -> None in
  remove_universal f |> function
    | Eq (f, g) -> find_map is_assoc [(f, g); (g, f)]
    | _ -> None

let commutative_axiom f = remove_universal f |> function
    | Eq (f, g) -> (match kind f, kind g with
        | Binary (op, Var (x, _), Var (y, _)), Binary (op', Var (y', _), Var (x', _))
            when (op, x, y) = (op', x', y') -> Some op
        | _ -> None)
    | _ -> None

let rec gather_op op f = match kind f with
  | Binary (op', f, g) when op = op' ->
      gather_op op f @ gather_op op g
  | _ -> [f]

let is_ac_tautology ac_ops = function
  | Eq (f, g) as eq -> (
      match kind f with
        | Binary (op, _, _) when mem op ac_ops ->
            let b =
              std_sort (gather_op op f) = std_sort (gather_op op g) &&
              not (associative_axiom eq = Some op || commutative_axiom eq = Some op) in
            if b && !debug > 0 then
              printf "AC tautology: %s\n" (show_formula eq);
            b
        | _ -> false)
  | _ -> false

let rec canonical_lit = function
  | Eq (f, g) ->
      let f, g = canonical_lit f, canonical_lit g in
      if f < g then Eq (f, g) else Eq (g, f)
  | f -> map_formula canonical_lit f

(* approximate: equivalent formulas could possibly have different canonical forms *)
let canonical pformula =
  let lits = sort Stdlib.compare (map canonical_lit (clausify pformula)) in
  rename_vars (fold_left1 _or lits)

module FormulaMap = Map.Make (struct
  type t = formula
  let compare = Stdlib.compare
end)

module PFQueue = Psq.Make (struct
  type t = pformula
  let compare = Stdlib.compare
end) (struct
  type t = float * int
  let compare = Stdlib.compare
end)

let queue_add queue pformulas =
  let queue_element p =
    (p, (p.cost, if p.goal then 0 else 1)) in
  let extra = PFQueue.of_list (map queue_element pformulas) in
  PFQueue.(++) queue extra

let dbg_newline () =
  if !debug > 0 then print_newline ()

let rw_simplify ac_ops used found pformula =
  let rec repeat_rewrite p = match rewrite_from used p with
    | None -> p
    | Some p -> repeat_rewrite p in
  let p = repeat_rewrite pformula in
  if p.id > 0 then Some (p, found)
  else let p = simplify p in
    if is_tautology p.formula || is_ac_tautology ac_ops p.formula then None
    else 
        let f = canonical p in
        match FormulaMap.find_opt f found with
          | Some pf ->
              if !debug > 0 then (
                let prefix = sprintf "duplicate of #%d: " pf.id in
                printf "%s\n" (indent_with_prefix prefix (show_multi p.formula)));
              None
          | None ->
              let p = number_formula p in
              Some (p, FormulaMap.add f p found)

let rec rw_simplify_all ac_ops used found = function
  | [] -> ([], found)
  | p :: ps ->
      let (ps', found) = rw_simplify_all ac_ops used found ps in
      match rw_simplify ac_ops used found p with
        | None -> (ps', found)
        | Some (p', found) -> (p' :: ps', found)

let rec back_simplify from = function
  | [] -> ([], [])
  | p :: ps ->
      let (ps', rewritten) = back_simplify from ps in
      match rewrite_from [from] p with
        | Some p' -> (ps', p' :: rewritten)
        | None -> (p :: ps', rewritten)

let find_ac_ops pformulas =
  let formulas = map (fun p -> p.formula) pformulas in
  let associative = filter_map associative_axiom formulas in
  let commutative = filter_map commutative_axiom formulas in
  intersect associative commutative

let refute pformulas =
  dbg_newline ();
  let ac_ops = find_ac_ops pformulas in
  if !debug > 0 && ac_ops <> [] then
    printf "AC operators: %s\n\n" (comma_join ac_ops);
  let found = FormulaMap.of_list (pformulas |> map
    (fun p -> (canonical p, p))) in
  let queue = queue_add PFQueue.empty pformulas in
  let rec loop queue found used =
    match PFQueue.pop queue with
      | None -> None
      | Some ((p, _cost), queue) ->
          dbg_print_formula false "given: " p;
          match rw_simplify ac_ops used found p with
            | None -> loop queue found used
            | Some (p, found) ->
                let (used, rewritten) = back_simplify p used in
                if p.formula = _false then Some p else
                  let used = p :: used in
                  let generated =
                    concat_map (all_super p) used @ all_eres p @ all_split p |>
                      filter (fun p -> p.cost <= max_cost) in
                  let (new_pformulas, found) =
                    rw_simplify_all ac_ops used found (rewritten @ generated) in
                  dbg_newline ();
                  match find_opt (fun p -> p.formula = _false) new_pformulas with
                    | Some p -> Some p
                    | None ->
                        let queue = queue_add queue new_pformulas in
                        loop queue found used
  in loop queue found []

let to_pformula stmt = stmt_formula stmt |> Option.map (fun f ->
  create_pformula (stmt_name stmt) [] (rename_vars f) 0.0)

let prove known_stmts stmt =
  formula_counter := 0;
  let known = known_stmts |> filter_map (fun s ->
    match to_pformula s with
      | Some p -> dbg_newline (); Some p
      | None -> None) in
  let pformula = Option.get (to_pformula stmt) in
  let negated =
    create_pformula "negate" [pformula] (_not pformula.formula) (-1.0) in
  refute (known @ [negated])

let output_proof pformula =
  let steps =
    search [pformula] (fun p -> unique (p.parents @ p.rewrites)) in
  let id_compare p q = Int.compare p.id q.id in
  List.sort id_compare steps |> iter (print_formula true "");
  print_newline ()

let prove_all _debug show_proofs thf prog =
  debug := _debug;
  let rec prove_stmts known_stmts = function
    | [] -> if (not thf) then print_endline "All theorems were proved."
    | stmt :: rest ->
        if (match stmt with
          | Theorem _ -> (
              print_endline (show_statement true stmt ^ "\n");
              let start = Sys.time () in
                match prove known_stmts stmt with
                  | Some pformula ->
                      let elapsed = Sys.time () -. start in
                      printf "proved in %.2f s\n" elapsed;
                      if thf then printf "SZS status Theorem\n";
                      if show_proofs then (
                        print_newline ();
                        output_proof pformula);
                      true
                  | None -> false)
          | _ -> true) then (
          prove_stmts (known_stmts @ [stmt]) rest)
        else (
          printf "Not proved.\n";
          if thf then printf "SZS status GaveUp\n") in
  prove_stmts [] prog
