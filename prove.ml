open Printf

open Logic
open Options
open Statement
open Util

let step_strategy = ref false
let destructive_rewrites = ref false

let formula_counter = ref 0

let comm_ops = ref ([] : id list)
let ac_ops = ref ([] : (id * typ) list)
let or_equal_ops = ref ([] : id list)

let output = ref false

type ac_type = Assoc | Comm | LDist | RDist | Extra

let ac_other = function
  | Assoc -> Comm
  | Comm -> Assoc
  | _ -> failwith "ac_other"

type pformula = {
  id: int;
  rule: string;
  description: string;
  parents: pformula list;
  rewrites: pformula list;  (* rewrites that created this formula *)
  simp: bool;
  formula: formula;
  ac: ac_type option;
  delta: float;
  cost: float;
  definition: string;
  hypothesis: int;
  goal: bool;
  by: bool;
  derived: bool;
  destruct: bool;       (* true if this formula is destructively rewritable *)
  rewritten: bool ref;   (* true if this formula was non-destructively rewritten *)
  safe_for_rewrite: bool
}

let id_of pf = pf.id

let rec num_literals f = match bool_kind f with
  | True | False -> 0
  | Not f -> num_literals f
  | Binary (_, _, t, u) -> num_literals t + num_literals u
  | Quant (_, _, _, u) -> num_literals u
  | Other _ -> 1

let weight f : int =
  let rec weigh f = match f with
    | Const (c, _typ) ->
        if mem c ["%⊥"; "(¬)"; "(∀)"; "(∃)"] then 0 else 1
    | Var _ -> 1
    | App (f, g) -> weigh f + weigh g
    | Eq (f, g) -> weigh f + weigh g
    | Lambda (_, _, f) -> weigh f in
  weigh f

let prefix_var var = "$" ^ var

let is_prefixed var = var.[0] = '$'

let rec prefix_type_vars t : typ = match t with
  | TypeVar id -> TypeVar (prefix_var id)
  | Sub f -> Sub (prefix_vars f)
  | t -> map_type prefix_type_vars t

and prefix_vars f : formula = profile @@
  let rec prefix outer = function
    | Const (x, typ) -> Const (x, prefix_type_vars typ)
    | Var (x, typ) ->
        let x = if mem x outer then x else prefix_var x in
        Var (x, prefix_type_vars typ)
    | Lambda (x, typ, f) ->
        Lambda (x, prefix_type_vars typ, prefix (x :: outer) f)
    | f -> map_formula (prefix outer) f
  in prefix [] f

let unprefix_vars f : formula = profile @@
  let rec build_map all_vars vars : (id * id) list = match vars with
    | [] -> []
    | var :: rest ->
        if is_prefixed var then
          let v = string_from var 1 in
          let w = next_var v all_vars in
          (var, w) :: build_map (w :: all_vars) rest
        else build_map all_vars rest in
  let var_map =
    build_map (all_vars f) (free_vars f) in
  let rec unprefix_type t = match t with
    | TypeVar x ->
        if is_prefixed x then TypeVar (assoc x var_map) else t
    | Sub f -> Sub (fix f)
    | t -> map_type unprefix_type t
  and fix = function
    | Const (c, typ) -> Const (c, unprefix_type typ)
    | Var (v, typ) ->
        let v = if is_prefixed v then assoc v var_map else v in
        Var (v, unprefix_type typ)
    | Lambda (x, typ, f) ->
        Lambda (x, unprefix_type typ, fix f)
    | f -> map_formula fix f in
  fix f

let is_inductive pformula =
  let f = pformula.formula in
  match kind f with
  | Quant ("(∀)", p, Fun (_, Bool), _) -> (
      match kind (last (gather_implies (remove_universal f))) with
        | Quant ("(∀)", x, _, App (Var (p', _), Var (x', _)))
            when p = p' && x = x' -> true
        | _ -> false)
  | _ -> false
  
let associative_axiom f : (str * typ) option =
  let is_assoc (f, g) = match kind f, kind g with
    | Binary (op, _, f1, Var (z, typ)), Binary (op3, _, Var (x', _), g1) -> (
        match kind f1, kind g1 with
          | Binary (op2, _, Var (x, _), Var (y, _)),
            Binary (op4, _, Var (y', _), Var (z', _))
              when op = op2 && op2 = op3 && op3 = op4 &&
                  (x, y, z) = (x', y', z') -> Some (op, typ)
          | _ -> None)
    | _ -> None in
  remove_universal f |> function
    | Eq (f, g) -> find_map is_assoc [(f, g); (g, f)]
    | _ -> None

let is_associative_axiom p = is_some (associative_axiom p.formula)

let commutative_axiom f : (str * typ) option =
  remove_universal f |> function
    | Eq (f, g) -> (match kind f, kind g with
        | Binary (op, _, Var (x, typ), Var (y, _)), Binary (op', _, Var (y', _), Var (x', _))
            when (op, x, y) = (op', x', y') -> Some (op, typ)
        | _ -> None)
    | _ -> None

let is_commutative_axiom p = is_some (commutative_axiom p.formula)

let distributive_templates : (ac_type * formula) list =
    let& (kind, t) =
      [LDist, "f(c)(g(a)(b)) = g(f(c)(a))(f(c)(b))";    (* c · (a + b) = c · a + c · b *)
       RDist, "f(g(a)(b))(c) = g(f(a)(c))(f(b)(c))"] in (* (a + b) · c = a · c + b · c *)
    (kind, prefix_vars (Parser.parse_formula t))

let distributive_axiom f : (str * str * typ * ac_type) option =
    let f = remove_universal f in
    head_opt @@
    let+ (kind, t) = distributive_templates in
    let+ (_tsubst, vsubst) = _match !comm_ops t f in
    match (let& v = ["f"; "g"; "a"; "b"; "c"] in assoc ("$" ^ v) vsubst) with
      | [Const (f_op, ftyp); Const (g_op, gtyp); Var (_, typ); Var _; Var _] ->
          assert (ftyp = gtyp);
          assert (ftyp = Fun (typ, Fun(typ, typ)));
          [(f_op, g_op, typ, kind)]
      | _ -> []

let is_hyp p = p.hypothesis > 0
let is_def p = p.definition <> ""
let goal_or_hyp p = p.goal || is_hyp p
let goal_or_last_hyp p = p.goal || p.hypothesis = 1

let orig_hyp p = is_hyp p && not p.derived
let orig_goal p = p.goal && not p.derived
let orig_def p = is_def p && not p.derived
let orig_by p = p.by && not p.derived
let orig_goal_or_last_hyp p = goal_or_last_hyp p && not p.derived

let can_rewrite p = p.destruct || not (goal_or_last_hyp p)

type queue_item =
  | Unprocessed of pformula
  | Deferred of pformula * pformula

module PFQueue = Psq.Make (struct
  type t = queue_item
  let compare = Stdlib.compare
end) (struct
  type t = float * int * int
  let compare = Stdlib.compare
end)

let merge_cost parents = match unique parents with
    | [] -> 0.0
    | [p] -> p.cost
    | parents ->
        let ancestors = searchq parents (fun p -> p.parents) in
        sum (ancestors |> map (fun p -> p.delta))

let inducted p =
  searchq [p] (fun p -> p.parents) |> exists (fun p -> is_inductive p)

let cost_limit = 1.5

let mk_pformula rule description parents step formula =
  let goal = exists (fun p -> p.goal) parents in
  { id = 0; rule; description; rewrites = []; simp = false; parents;
    formula; ac = None;
    goal; delta = 0.0; cost = 0.0;
    hypothesis = (
      if goal then 0
      else let hs = filter_map (fun p -> if is_hyp p then Some p.hypothesis else None) parents in
      if hs = [] then 0 else minimum hs);
    definition = (if step then "" else
      match find_opt is_def parents with
        | Some d -> d.definition
        | None -> "");
    by = parents <> [] && for_all (fun p -> p.by) parents;
    derived = step || exists (fun p -> p.derived) parents;
    rewritten = ref false; destruct = false; safe_for_rewrite = false
  }

let number_formula pformula : pformula =
  if pformula.id > 0 then pformula
  else (
    assert ((pformula.parents @ pformula.rewrites) |> for_all (fun p -> p.id > 0));
    incr formula_counter;
    { pformula with id = !formula_counter } )

(* Symbol precedence for term ordering, from highest to lowest:
 *   Skolem constants created during inference, e.g. ~x10
 *   constants from input text, in declaration order (later = higher)
 *      e.g. [003]c
 *   constants generated by higher-order mapping (e.g. @=, @lam)
 *   logical constants (e.g. (¬), (∧), (∨)), alphabetically (arbitrarily)
 *   %⊥
 *   %⊤
 * The string forms above have been chosen so that a lexicographic comparison
 * will produce the desired ordering.
 * In particular, in ASCII '%' < '(' < '@' < '[' < '~'.  In Unicode '⊤' < '⊥'.
 *)

let const_gt c d : bool = c > d
            
let get_index x map : int =
  match index_of_opt x !map with
    | Some i -> length !map - 1 - i
    | None ->
        map := x :: !map;
        length !map - 1

let de_bruijn_encode x f : formula =
  let rec encode count t = match t with
    | Var (id, _typ) ->
        if id = x then _const ("@db" ^ string_of_int count) else t
    | Lambda (id, typ, f) ->
        if id = x then t else Lambda (id, typ, encode (count + 1) f)
    | t -> map_formula (encode count) t in
  encode 0 f

(* Map higher-order terms to first-order terms as described in
 * Bentkamp et al, section 3.9 "A Concrete Term Order".  That section introduces
 * a distinct symbol f_k for each arity k.  We use the symbol f to represent
 * all the f_k, then order by arity in lpo_gt.
 * We do not implement the transformation to terms ∀_1', ∃_1', z_u', which is
 * intended for the Knuth-Bendix ordering.
 * This function returns an encoded formula plus a list of unencoded arguments,
 * which lets us perform the encoding incrementally in lpo_gt. *)
let encode_term type_map fluid_map t : formula * formula list = profile @@
  let encode_fluid t = _var ("@v" ^ string_of_int (get_index t fluid_map)) in
  let encode_type typ = _const ("@t" ^ string_of_int (get_index typ type_map)) in
  match t with
    | Const (c, typ) when c = _type -> (encode_type typ, [])
    | Const _ -> (t, [])
    | Var (v, _) -> (_var v, [])
    | App _ ->
        let (head, args) = collect_args t in
        let head = match head with
          | Var (v, _) -> _var v
          | _ -> head in (
        match head with
          | Var _ -> (encode_fluid t, [])
          | Const (q, _) when q = "(∀)" || q = "(∃)" -> (
              match args with
                | [Lambda (x, typ, f)] ->
                    let q1 = _const ("@" ^ q) in
                    (q1, [type_const typ; de_bruijn_encode x f])
                | _ -> failwith "encode_term: quantifier not applied to lambda")
          | Const _ -> (head, args)
          | _ -> failwith "encode_term: head is not var or const")
    | Lambda (x, typ, f) ->
        if is_ground t then
          (_const "@lam", [type_const typ; de_bruijn_encode x f])
        else (encode_fluid t, []) (* assume fluid *)
    | Eq (t, u) -> (_const "@=", [t; u])

(* Lexicographic path ordering on first-order terms.  We use
 * the optimized version lpo_4 described in Lochner, "Things to Know
 * When Implementing LPO". *)
let rec lpo_gt s t = profile @@
  let type_map, fluid_map = ref [], ref [] in
  let encode = encode_term type_map fluid_map in

  let rec lpo s t =
    let (f, ss), (g, ts) = encode s, encode t in
    match f, g with
      | Const (c, _), Const (d, _) ->
          let (nf, ng) = length ss, length ts in
          if const_gt c d || c = d && nf > ng then majo s ts
          else if c = d && nf = ng then lex_ma s t ss ts
          else alpha ss t
      | _, Var (y, _) -> s <> t && (
          if (starts_with "@v" y) then
            let i = int_of_string (string_from y 2) in
            let t' = nth !fluid_map i in
            has_subformula t' s
          else is_var_in y s)
      | Var _, Const _ -> false
      | _, _ -> failwith "lpo"

  and alpha ss t = exists (fun s -> s = t || lpo_gt s t) ss

  and majo s ts = for_all (lpo_gt s) ts

  and lex_ma s t ss ts = match ss, ts with
    | [], [] -> false
    | s_i :: ss, t_i :: ts ->
        if s_i = t_i then lex_ma s t ss ts
        else if lpo_gt s_i t_i then majo s ts
        else alpha ss t
    | _ -> failwith "lex_ma" in
  
  lpo s t

let term_gt = lpo_gt

let term_ge s t = s = t || term_gt s t

let terms with_iff f : bool * formula * formula = match f with
  | Eq (f, g) -> (true, f, g)
  | App (App (Const ("(↔)", _), f), g) when with_iff -> (true, f, g)
  | App (Const ("(¬)", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("(¬)", _), f) -> (true, f, _false)
  | f -> (true, f, _true)

let lit_to_multi f : formula list list =
  let eq, t, u = terms false f in
  if eq then [[t]; [u]] else [[t; _false]; [u; _false]]

let lit_gt f g =
  multi_gt (multi_gt term_gt) (lit_to_multi f) (lit_to_multi g)

let clause_gt = multi_gt lit_gt

let or_split f : (formula * formula) option = match bool_kind f with
  | Binary ("(∨)", _, s, t) -> Some (s, t)
  | Binary ("(→)", _, s, t) -> Some (negate s, t)
  | Not g -> (match bool_kind g with
    | Binary ("(∧)", _, f, g) -> Some (negate f, negate g)
    | Binary ("(↔)", _, f, g) -> Some (_not (implies f g), _not (implies g f))
    | _ -> None)
  | _ -> None

(* Clausify ignoring quantifiers and conjunctions *)
let rec mini_clausify f : formula list = match or_split f with
    | Some (f, g) -> mini_clausify f @ mini_clausify g
    | _ -> [f]

(*      s = ⊤ ∨ C                 s = ⊥ ∨ C
      ═════════════   oc       ══════════════   oc
        oc(s) ∨ C                oc(¬s) ∨ C

        oc(s ∨ t) = s = ⊤ ∨ t = ⊤
        oc(s → t) = s = ⊥ ∨ t = ⊤
        oc(∀x.s) = s[y/x] = ⊤  (y not in s or C)
        oc(∃x.s) = s[k(y̅)/x] = ⊤
        oc(¬(s ∧ t)) = s = ⊥ ∨ t = ⊥
        oc(¬(s ↔ t)) = (s → t) = ⊥ ∨ (t → s) = ⊥
        oc(¬(∀x.s)) = s[k(y̅)/x] = ⊥
        oc(¬(∃x.s)) = s[y/x] = ⊥  (y not in s or C)
        
        k is a new constant
        y̅ are all free variables in ∃x.s
*)

let clausify_step id lits in_use :
      (formula list * formula list * formula list) option =
  let rec new_lits f = match or_split f with
    | Some (s, t) -> Some ([s; t], [])
    | None -> match bool_kind f with
      | Quant ("(∀)", x, typ, f) ->
          let f =
            let vars = concat_map free_vars lits in
            if mem x vars then 
              let y = next_var x vars in
              subst1 f (Var (y, typ)) x
            else f in
          Some ([f], [f])
      | Quant ("(∃)", x, typ, g) ->
          let vars_types = free_vars_types f in
          let skolem_type = fold_right1 mk_fun_type (map snd vars_types @ [typ]) in
          let c = sprintf "~%s%d" x id in
          let c = match in_use with
            | Some names ->
                let c = suffix c !names in
                names := c :: !names;
                c
            | None -> c in
          let skolem_const = Const (c, skolem_type) in
          let skolem = apply (skolem_const :: map mk_var' vars_types) in
          let g = subst1 g skolem x in
          Some ([g], [g])
      | Not g -> (match bool_kind g with
        | Quant ("(∀)", x, typ, g) ->
            new_lits (_exists x typ (negate g))
        | Quant ("(∃)", x, typ, g) ->
            new_lits (_for_all x typ (negate g))
        | _ -> None)
      | _ -> None in
  let rec loop before = function
    | [] -> None
    | lit :: after ->
        match new_lits lit with
          | Some (lits, exposed) -> Some (rev before @ lits @ after, lits, exposed)
          | None -> loop (lit :: before) after in
  loop [] lits

let initial_step pformula =
  let f = pformula.formula in ([f], [f], [f])

let clausify_steps1 id lits in_use :
      (formula list * formula list * formula list) list =
  let rec run ((lits, _, _) as step) =
    step :: match clausify_step id lits in_use with
      | None -> []
      | Some step -> run step in
  run (lits, lits, lits)

let clausify_steps p : (formula list * formula list * formula list) list =
  clausify_steps1 p.id [p.formula] None

let run_clausify pformula rule =
  let+ (lits, new_lits, _) = clausify_steps pformula in
  let+ f = new_lits in
  rule pformula (remove1 f lits) f
  
let clausify1 id lits in_use : formula list =
  let (lits, _, _) = last (clausify_steps1 id lits in_use) in
  lits

let clausify p = clausify1 p.id [p.formula] None

let is_fluid t = match t with
  | App _ ->
      let (head, _args) = collect_args t in
      is_var head
  | Lambda _ -> not (is_ground t) (* approximate *)
  | _ -> false

(* Gather green or blue subterms.  *)
let subterms is_blue t : (formula * ((formula * formula) list)) list =
  let rec gather parent_eq acc t =
    (if is_var t || not is_blue && is_fluid t then [] else [(t, parent_eq)]) @
    match t with
      | App (f, g) ->
          if is_quantifier f then
            if is_blue then match g with
              | Lambda (_x, _typ, h) -> gather parent_eq acc h
              | _ -> acc
            else acc
          else
            let acc = gather parent_eq acc f in
            gather parent_eq acc g
      | Eq (f, g) ->
          let acc = gather ((f, g) :: parent_eq) acc f in
          gather ((g, f) :: parent_eq) acc g
      | _-> acc in
  gather [] [] t

let green_subterms = subterms false
let blue_subterms t = map fst (subterms true t)

let is_eligible sub parent_eq =
  parent_eq |> for_all (fun (s, t) ->
    not (term_gt (subst_n sub t) (subst_n sub s)))

let top_level pos u c : bool =
  let cs = mini_clausify c in
  let lit = if pos then u else _not u in
  mem lit cs

let simp_eq = function
  | Eq (Eq (t, t'), f) when f = _true -> Eq (t, t')
  | f -> f

let is_higher (_, vsubst) = vsubst |> exists (fun (_, f) -> is_lambda f)

let oriented upward t t' = [(t, t'); (t', t)] |>
  filter (fun (t, t') -> upward || not (term_ge t' t))

let eq_pairs with_iff upward f = match terms with_iff f with
  | (true, t, t') ->
      if is_bool_const t' then [(t, t')]
      else (Eq (t, t'), _true) :: oriented upward t t'   (* iii: pre-check *)
  | (false, t, t') -> [(Eq (t, t'), _false)]

let by_induction p = exists is_inductive p.parents

(* Find terms such as g in "g = ...". *)
let rec eq_terms f : formula list = match f with
  | App (Const ("(¬)", _), f) -> eq_terms f
  | Eq (g, h) -> [g; h]
  | _ -> []

let top_consts p : id list =
  let rec find f = match f with
    | App (Const ("(¬)", _), f) -> find f
    | App (Const ("(∀)", _), Lambda (_, _, f)) -> find f
    | Eq (f, g) -> find f @ find g
    | _ ->
        opt_to_list (opt_const (fst (collect_args f))) in
  subtract (find p.formula) logical_ops

let expand_limit = 3
let def_expand_limit = 3
let hyp_expand_limit = 2

let _expand_def, _expand_hyp = "expand def", "expand hyp"

let is_expand p = starts_with "expand " p.rule

let rec expansions p : string list =
  (if is_expand p then [p.rule] else []) @ concat_map expansions p.parents

let at_limit parents kind limit =
  let e = concat_map expansions parents in
  length e >= expand_limit || count_eq kind e >= limit

let is_def_expansion parents =
  not (at_limit parents _expand_def def_expand_limit) &&
  let def = find_opt orig_def parents in
  let last = parents |> find_opt (fun p -> orig_goal p || orig_hyp p) in
  match def, last with
    | Some def, Some last ->
        let goal_consts =
          if orig_goal last then all_consts last.formula else top_consts last in
        mem def.definition goal_consts
    | _ -> false

let is_hyp_expansion parents =
  not (at_limit parents _expand_hyp hyp_expand_limit) &&
  match opt_or_opt (find_opt orig_goal parents)
                   (find_opt (fun p -> orig_hyp p && p.hypothesis = 1) parents) with
    | Some last ->
        let i = if last.goal then 1 else 2 in (
        match (parents |> find_opt (fun p -> p.hypothesis >= i)) with
          | Some hyp ->
              overlap (eq_terms (remove_exists hyp.formula))
                      (map fst (green_subterms last.formula))
          | _ -> false)
    | _ -> false

let is_by parents = 
  concat_map expansions parents = [] && exists orig_goal parents && exists orig_by parents

let is_last_hyp_to_goal parents =
  concat_map expansions parents = [] &&
  for_all orig_goal_or_last_hyp parents

let by_cost = 0.0
let step_cost = 0.01
let induction_cost = 1.0
let infinite_cost = 10.0

let cost p : float * bool =
  if p.rule = "eres" then (step_cost, p.derived) else
  if length p.parents < 2 then (0.0, p.derived) else
  let qs = p.parents |> filter (fun p -> p.goal || is_hyp p) in
  let qs = if qs = [] then p.parents else qs in
  let max = maximum (map (fun p -> weight p.formula) qs) in
  let c =
    let non_increasing = weight p.formula <= max in
    if is_by p.parents then (if non_increasing then by_cost else step_cost) else
    if !(opts.all_superpositions) || is_expand p ||
       is_last_hyp_to_goal p.parents ||
       non_increasing then step_cost else
    if not !step_strategy && by_induction p then induction_cost
    else infinite_cost in
  (c, p.derived && not (is_expand p))

(*      D:[D' ∨ t = t']    C⟨u⟩
 *    ───────────────────────────   sup
 *          (D' ∨ C⟨t'⟩)σ             σ ∈ csu(t, u)
 *
 *     (i) u is not fluid
 *     (ii) u is not a variable
 *     (iii) tσ ≰ t'σ
 *     (iv) the position of u is eligible in C with respect to σ
 *     (v) Cσ ≰ Dσ
 *     (vi) t = t' is maximal in D with respect to σ
 *     (vii)  if t'σ = ⊥, u is in a literal of the form u = ⊤;
              if t'σ = ⊤, u is in a literal of the form u = ⊥ *)

let super rule with_para lenient upward dp d' pairs cp c_lits c_lit : pformula list = profile @@
  let dbg = (dp.id, cp.id) = !debug_super in
  if dbg then printf "super\n";
  let+ (t, t') = pairs in
  let res = is_bool_const t' in
  if not res && not with_para then [] else
  let lenient = res && lenient in
  let+ (u, parent_eq) = green_subterms c_lit in  (* i, ii *)
  let+ sub = unify !comm_ops t u in
  if dbg then printf "super: unified %s with %s\n" (show_formula t) (show_formula u);
  let d'_s = map (rsubst sub) d' in
  let t_s, t'_s = rsubst sub t, rsubst sub t' in
  let t_eq_t'_s = Eq (t_s, t'_s) in
  (* let d_s = t_eq_t'_s :: d'_s in *)
  let c_s = map (rsubst sub) c_lits in
  let c1_s = rsubst sub c_lit in
  let fail n = if dbg then printf "super: failed check %d\n" n; true in
  if is_higher sub && not (orig_goal dp || orig_hyp dp && dp.hypothesis = 1) && fail 0 ||
      is_bool_const t'_s && not (top_level (t'_s = _false) u c_lit) && fail 7 || (* vii *)
      not lenient && not (is_maximal lit_gt (simp_eq t_eq_t'_s) d'_s) && fail 6 ||  (* vi *)
      not upward && term_ge t'_s t_s && fail 3 ||  (* iii *)
      not (lenient || upward) && not (is_maximal lit_gt c1_s c_s &&
                                      is_eligible sub parent_eq) && fail 4 (* *||  (* iv *)
      not (lenient || upward) && t'_s <> _false && clause_gt d_s c_s && fail 5  (* v *) *)
  then [] else (
    let c1_t' = replace_in_formula t' u c_lit in
    let c_s = replace1 (rsubst sub c1_t') c1_s c_s in
    let e = unprefix_vars (multi_or (d'_s @ c_s)) in
    let tt'_show = str_replace "\\$" "" (show_formula (Eq (t, t'))) in
    let u_show = show_formula u in
    let rule = if rule = "" then (if res then "res" else "para") else rule in
    let description = sprintf "%s / %s" tt'_show u_show in
    if dbg then printf "super: passed checks, produced %s\n" (show_formula e);
    [mk_pformula rule description [dp; cp] true e])

let allow p = goal_or_hyp p

let is_unit_equality f = is_eq (remove_for_all f)

let is_conditioned_equality f = is_eq (last (gather_implies (remove_for_all f)))

let all_super1 dp cp : pformula list =
  let by = is_by [dp; cp] in
  let def_expand = is_def_expansion [dp; cp] in
  let hyp_expand = is_hyp_expansion [dp; cp] in
  let upward = hyp_expand in
  let lenient = by || def_expand || orig_goal cp in
  let rule =
    if def_expand then _expand_def
    else if hyp_expand then _expand_hyp else "" in
  let d_steps, c_steps = clausify_steps dp, clausify_steps cp in
  let+ (dp, d_steps, cp, c_steps) =
    [(dp, d_steps, cp, c_steps); (cp, c_steps, dp, d_steps)] in
  let+ (d_lits, new_lits, _) = d_steps in
  let d_lits, new_lits = map prefix_vars d_lits, map prefix_vars new_lits in
  let+ t_t' = new_lits in
  let pairs = eq_pairs false upward t_t' in  (* iii: pre-check *)
  let+ (c_lits, _, exposed_lits) = c_steps in
  let+ c_lit = exposed_lits in
  let with_para = !(opts.all_superpositions) || (
    dp.ac = Some Comm || dp.ac = Some Assoc || by || def_expand || hyp_expand ||
    allow cp && (not !step_strategy ||
                 is_unit_equality dp.formula ||
                 is_conditioned_equality dp.formula && cp.goal ||
                 is_last_hyp_to_goal [cp; dp])) in
  super rule with_para lenient upward dp (remove1 t_t' d_lits) pairs cp c_lits c_lit

let is_ac p = is_some p.ac

let allow_super dp cp =
  let induct_ok d c = not (is_inductive c) ||
    ((orig_goal d || orig_hyp d) && not (inducted d)) in
  !(opts.all_superpositions) || (
    dp.id <> cp.id && (allow dp || allow cp) &&
    induct_ok dp cp && induct_ok cp dp)

let all_super queue dp cp : pformula list = profile @@
  assert (dp.id <> 0 && cp.id <> 0);
  let dbg = (dp.id, cp.id) = !debug_super in
  if dbg then printf "all_super\n";
  if not (allow_super dp cp) then [] else
  if !(opts.deferred) then
    let cost = match PFQueue.min !queue with
      | Some (_, (cost, _, _)) -> cost
      | None -> 10.0 in
    let min_cost = merge_cost [cp; dp] +. step_cost in
    if min_cost <= cost then all_super1 dp cp else (
      queue := PFQueue.add (Deferred (dp, cp)) (min_cost, 0, 0) !queue;
      []
    )
  else all_super1 dp cp

(*      C' ∨ u ≠ u'
 *     ────────────   eres
 *         C'σ          σ ∈ csu(s, t)  *)

let eres cp c' c_lit : pformula list =
  match terms false c_lit with
    | (true, _, _) -> []
    | (false, u, u') ->
        let+ sub = unify !comm_ops u u' in
        let c1 = map (rsubst sub) c' in
        [mk_pformula "eres" "" [cp] true (multi_or c1)]

let all_eres cp = run_clausify cp eres

(*      s = ⊤ ∨ C                       s = ⊥ ∨ C
 *    ══════════════  split           ══════════════  split
 *       sp(s, C)                        sp(¬s, C)
 *
 *  sp(s ∧ t, C) = { s = ⊤ ∨ C, t = ⊤ ∨ C }
 *  sp(s ↔ t, C) = { s → t ∨ C, t → s ∨ C }
 *  sp(¬(s ∨ t), C) = { s ═ ⊥ ∨ C, t = ⊥ ∨ C }
 *  sp(¬(s → t), C) = { s = ⊤ ∨ C, t = ⊥ ∨ C }
 *)

let all_split p : pformula list =
  if is_def p && p.safe_for_rewrite then [] else
  let skolem_names = ref [] in
  let rec run lits : formula list list =
    let lits1 : formula list = clausify1 p.id lits (Some skolem_names) in
    let split lit f g =
      let top = if lits1 = lits then [] else [lits] in
      let children = [f; g] |> concat_map (fun t -> run (replace1 t lit lits1)) in
      Some (top @ children) in
    let split_on lit = match bool_kind lit with
      | Binary ("(∧)", _, f, g) -> split lit f g
      | Binary ("(↔)", _, f, g) -> split lit (implies f g) (implies g f)
      | Not f -> (match bool_kind f with
          | Binary ("(∨)", _, f, g) -> split lit (_not f) (_not g)
          | Binary ("(→)", _, f, g) -> split lit f (_not g)
          | _ -> None)
      | _ -> None in
    match find_map split_on lits1 with
      | Some new_clauses -> new_clauses
      | None -> [lits] in
  if p.rule = "split" || is_inductive p then []
  else
    let splits = remove [p.formula] (run [p.formula]) in
    rev splits |> map (fun lits ->
      mk_pformula "split" "" [p] false (multi_or lits))

let update p rewriting f : pformula =
  let (r, simp) = match rewriting with
    | Some p -> ([p], false)
    | None -> ([], true) in
  if p.id = 0 then
    { p with rewrites = r @ p.rewrites; simp = p.simp || simp; formula = f }
  else (
    { p with id = 0; rule = if simp then "simp" else "rw"; description = "";
        rewrites = r; simp; parents = [p];
        delta = 0.0; formula = f }
  )

let allow_rewrite dp cp =
  dp.id <> cp.id && not (exists (fun p -> p.id = dp.id) cp.parents) &&
    (!destructive_rewrites || allow cp || dp.safe_for_rewrite) &&
    not (orig_hyp dp && (orig_hyp cp || orig_goal cp))

(*     t = t'    C⟪tσ⟫
 *   ═══════════════════   rw
 *     t = t'    C⟪t'σ⟫
 *
 *   (i) tσ > t'σ
 *)
let rewrite dp cp c_subterms only_safe : pformula option =
  if not (allow_rewrite dp cp) || only_safe && not dp.safe_for_rewrite then None else
  let d = remove_universal dp.formula in
  let with_iff = dp.safe_for_rewrite in
  if not (num_literals d <= 1 || with_iff && is_iff d) then None else
    let c = cp.formula in
    let rewrite_with (t, t', u) : pformula option = head_opt @@
      let+ sub = try_match !comm_ops ([], []) t u in
      let t_s, t'_s = u, rsubst sub t' in
      if term_gt t_s t'_s  (* (i) *) then
        let e = b_reduce (replace_in_formula t'_s t_s c) in
        [update cp (Some dp) e]
      else [] in
    let all =
      let+ (t, t') =
        eq_pairs with_iff false d in  (* i: pre-check *)
      let t, t' = prefix_vars t, prefix_vars t' in
      let& u = c_subterms in
      (t, t', u) in
    find_map rewrite_with all

let rewrite_from ps q only_safe : pformula option = profile @@
  if !(q.rewritten) then None else
  let q_subterms = blue_subterms q.formula in
  find_map (fun p -> rewrite p q q_subterms only_safe) ps

let repeat_rewrite used p only_safe : pformula = profile @@
  let rec loop p = match rewrite_from used p only_safe with
    | None -> p
    | Some p -> loop p in
  loop p

(*     C    Cσ ∨ R
 *   ═══════════════   subsume
 *         C                 *)

let subsumes cp (d_lits, d_exist) : bool =
  let subsume subst c d =
    if d_exist = [] then try_match !comm_ops subst c d
    else
      (* Existential subsumption, e.g. x + 0 = x subsumes ∃z:ℕ.x + z = x *)
      let+ (_, vsubst) = unify_or_match true !comm_ops subst c d in
      if vsubst |> for_all (fun (id, f) ->
        not (is_prefixed id) || mem id d_exist || 
          match f with
            | Var (id, _typ) -> not (is_prefixed id)
            | _ -> false) then [subst] else [] in
  let rec subsume_lits c_lits d_lits subst : bool = match c_lits with
    | [] -> true
    | c :: c_lits ->
        d_lits |> exists (fun d ->
          subsume subst c d |> exists (fun subst ->
            subsume_lits c_lits (remove1q d d_lits) subst)) in
  let c_lits = mini_clausify (remove_universal cp.formula) in
  subsume_lits c_lits d_lits ([], [])

let prefix_lits dp : formula list * id list =
  let (f, exist) = remove_quants true dp.formula in
  (mini_clausify (prefix_vars f), map prefix_var exist)

let any_subsumes cs dp : pformula option = profile @@
  if orig_goal dp || orig_hyp dp || is_ac dp then None else
  let d_lits = prefix_lits dp in
  cs |> find_opt (fun cp -> subsumes cp d_lits)

let subsumes1 cp dp : bool = is_some (any_subsumes [cp] dp)

let rec expand f : formula list = match or_split f with
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
  | Binary (op, _, p, q) ->
      let p, q = simp p, simp q in (
      match op, bool_kind p, bool_kind q with
        | "(∧)", True, _ -> q
        | "(∧)", _, True -> p
        | "(∧)", False, _ -> _false
        | "(∧)", _, False -> _false
        | "(∧)", t, u when t = u -> p
        | "(∨)", True, _ -> _true
        | "(∨)", _, True -> _true
        | "(∨)", False, _ -> q
        | "(∨)", _, False -> p
        | "(∨)", t, u when t = u -> p
        | "(→)", True, _ -> q
        | "(→)", _, True -> _true
        | "(→)", False, _ -> _true
        | "(→)", _, False -> simp (_not p)
        | "(→)", t, u when t = u -> _true
        | "(↔)", True, _ -> q
        | "(↔)", _, True -> p
        | "(↔)", False, _ -> _not q
        | "(↔)", _, False -> _not p
        | "(↔)", t, u when t = u -> _true
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

let rec canonical_lit f : formula =
  let commutative_pair op f g =
    let f, g = canonical_lit f, canonical_lit g in
    if f < g then op f g else op g f in
  match f with
    | App (App (Const (op, typ), f), g)
        when mem op !comm_ops -> commutative_pair (binop op typ) f g
    | Eq (f, g) ->
        commutative_pair mk_eq f g
    | f -> map_formula canonical_lit f

let simplify pformula =
  let f = simp pformula.formula in
  let f = multi_or (unique1 canonical_lit (gather_or f)) in
  if f = pformula.formula then pformula
  else update pformula None f

let taut_lit f = match bool_kind f with
  | True -> true
  | Quant ("(∃)", x, _typ, Eq (Var (x', _), _)) when x = x' -> true
  | Quant ("(∃)", x, _typ, Eq (_, Var (x', _))) when x = x' -> true
  | _ -> false

let is_tautology f =
  let rec pos_neg = function
    | [] -> ([], [])
    | f :: fs ->
        let (pos, neg) = pos_neg fs in
        match bool_kind f with
          | Not g -> (pos, g :: neg)
          | _ -> (f :: pos, neg) in
  let (pos, neg) = pos_neg (map canonical_lit (map simp (expand f))) in
  exists taut_lit pos || intersect pos neg <> []

let print_formula with_origin prefix pf =
  output := true;
  let prefix =
    if pf.id > 0 then prefix ^ sprintf "%d. " (pf.id) else prefix in
  let origin =
    if with_origin then
      let parents = pf.parents |> map (fun p -> string_of_int (p.id)) in
      let rule = if mem pf.rule [""; "nrw"; "rw"; "simp"] then [] else
        let full_rule = if pf.description = "" then pf.rule
          else sprintf "%s: %s" pf.rule pf.description in
        [full_rule] in
      let rewrites = rev pf.rewrites |> map (fun r -> r.id) in
      let rw = if rewrites = [] then []
        else
          let rw = if pf.rule = "nrw" then "nrw" else "rw" in
          [sprintf "%s(%s)" rw (comma_join (map string_of_int rewrites))] in
      let simp = if pf.simp then ["simp"] else [] in
      let all = parents @ rule @ rw @ simp in
      sprintf " [%s]" (comma_join all)
    else "" in
  let mark b c = if b then " " ^ (if pf.derived then c else to_upper c) else "" in
  let annotate =
    mark pf.by "b" ^ mark (is_def pf) "d" ^
    mark pf.goal "g" ^
    mark (is_hyp pf) (if pf.hypothesis = 1 then "lh" else "h") ^
    mark pf.destruct "u" in
  printf "%s%s {%d/%d: %.2f%s}\n"
    (indent_with_prefix prefix (show_multi pf.formula))
    origin (num_literals pf.formula) (weight pf.formula) pf.cost annotate

let dbg_print_formula with_origin prefix pformula =
  if !debug > 0 then print_formula with_origin prefix pformula

let create_pformula rule parents formula =
  let p = number_formula (mk_pformula rule "" parents false formula) in
  dbg_print_formula true "" p;
  p

let all_steps pformula =
  searchq [pformula] (fun p -> unique (p.parents @ p.rewrites))

let output_proof pformula =
  sort_by id_of (all_steps pformula) |> iter (print_formula true "");
  print_newline ()

let is_ac_tautology f =
  let rec ac_reduce f = match kind f with
    | Binary (op, (Fun (typ, Fun (_, _)) as op_typ), _, _) 
        when mem (op, typ) !ac_ops ->
          let terms = std_sort (map ac_reduce (gather_associative op f)) in
          fold_right1 (binop op op_typ) terms
    | _ -> map_formula ac_reduce f in
  match f with
    | Eq (t, u) -> ac_reduce t = ac_reduce u
    | _ -> false

(* approximate: equivalent formulas could possibly have different canonical forms *)
let canonical p : formula =
  let lits =
    let f = mini_clausify (remove_universal p.formula) in
    sort Stdlib.compare (map canonical_lit f) in
  rename_vars (fold_left1 _or lits)

module FormulaMap = Map.Make (struct
  type t = formula
  let compare = Stdlib.compare
end)

let expansion f = match remove_for_all f with
  | Eq (f, g) -> weight g - weight f
  | _ -> 0

let queue_class p : int =
  if p.cost = 0.0 then
    if is_ac p then 0
    else if p.safe_for_rewrite then 1
    else if p.by then 2
    else if orig_goal p then 3
    else if orig_hyp p then 100 - p.hypothesis
    else if expansion p.formula >= 0 then 100 + p.id
    else 1000 + p.id
  else 0

let queue_cost p : float * int * int =
  (p.cost, queue_class p, weight p.formula + (if p.goal then -100 else 0))

let queue_add queue pformulas =
  let queue_element p = (Unprocessed p, queue_cost p) in
  let extra = PFQueue.of_list (map queue_element pformulas) in
  queue := PFQueue.(++) !queue extra

let dbg_newline () =
  if !debug > 0 && !output then (print_newline (); output := false)

let finish p f_canonical found delta cost : pformula =
  let p = { (number_formula p) with delta; cost } in
  dbg_print_formula true "" p;
  found := FormulaMap.add f_canonical p !found;
  if p.id = !(opts.show_proof_of) then output_proof p;
  p

let remove_from_map found p =
  let f_canonical = canonical p in
  assert (FormulaMap.mem f_canonical !found);
  found := FormulaMap.remove f_canonical !found

let rw_simplify cheap src queue used found p0 : pformula option =
  if is_ac p0 then (assert (p0.id <> 0); Some p0) else
  let only_safe = not (can_rewrite p0) && not !destructive_rewrites in
  let p1 = repeat_rewrite !used p0 only_safe in
  let p = simplify p1 in
  if p0.id > 0 && p.id = 0 then remove_from_map found p0;
  let taut = is_tautology p.formula in
  if taut || is_ac_tautology p.formula then (
    if !debug > 1 || !debug = 1 && src <> "generated" then (
      printf "%s %stautology: " src (if taut then "" else "ac ");
      if p1.formula <> p.formula then printf "%s ==> " (show_formula p1.formula);
      print_formula true "" p
    );
    if p.id > 0 then remove_from_map found p;
    None)
  else
    match (if cheap then None else any_subsumes !used p) with
      | Some pf ->
          if !debug > 0 then (
            let prefix = sprintf "%s subsumed by #%d: " src pf.id in
            print_line (prefix_show prefix p.formula));
          if p.id > 0 then remove_from_map found p;
          None
      | None ->
          if p.id > 0 then Some p else
            let delta, step = cost p in
            let p = { p with derived = step } in
            let cost = merge_cost p.parents +. delta in
            if p.formula <> _false && cost > cost_limit then (
              if !debug > 1 then
                print_formula true "dropping (over cost limit): " {p with cost};
              None)
            else
              let f_canonical = canonical p in
              let final () = finish p f_canonical found delta cost in
              match FormulaMap.find_opt f_canonical !found with
                | Some pf when pf.id = p0.id -> (* e.g. due to C-unification *)
                    if !debug > 0 then
                      printf "#%d: rewritten clause is duplicate of original\n" p0.id;
                    Some p0
                | Some pf ->
                    if p.by || orig_goal p && not (orig_goal pf) || cost < pf.cost then (
                      let p = final () in
                      if !debug > 0 then
                        if p.by || orig_goal p then
                          printf "%s (%s) is a duplicate of #%d; replacing it\n"
                            src (if p.by then "by" else "goal") pf.id
                        else printf "(%d is a duplicate of %d; replacing with lower cost of %.2f)\n"
                          p.id pf.id p.cost;
                      if PFQueue.mem (Unprocessed pf) !queue then
                        queue := PFQueue.remove (Unprocessed pf) !queue
                      else
                        used := remove1q pf !used;
                      (* Ideally we would also update descendents of pf
                        to have p as an ancestor instead. *)
                      Some p
                    ) else (
                        let prefix = sprintf "%s duplicate of #%d: " src pf.id in
                        dbg_print_formula true prefix p;
                      None)
                | None ->
                    Some (final ())

type proof_stats = {
  initial: int; given: int; generated: int; max_cost: float
}

type proof_result = Proof of pformula * proof_stats | Timeout | GaveUp | Stopped

let szs = function
  | Proof _ -> "Theorem"
  | Timeout -> "Timeout"
  | GaveUp -> "GaveUp"
  | Stopped -> "Stopped"
                  
let forward_simplify queue used found p : pformula option = profile @@
  rw_simplify false (sprintf "given (#%d) is" p.id) queue used found p
  
let back_simplify found from used : pformula list = profile @@
  let back_simp p : pformula list * pformula list =
    if is_ac p then ([p], []) else
    let keep, rewritten = if subsumes1 from p then (
      if !debug > 0 then
        printf "%d. %s was back subsumed by %d. %s\n"
          p.id (show_formula p.formula) from.id (show_formula from.formula);
      (false, []))
    else match rewrite_from [from] p false with
      | Some p' -> (not (!destructive_rewrites || can_rewrite p), [p'])
      | None -> (true, []) in
    if not keep then remove_from_map found p;
    ((if keep then [p] else []), rewritten) in
  let (new_used, rewritten) = map_pair concat (unzip (map back_simp !used)) in
  used := new_used;
  rewritten

let nondestruct_rewrite used p : pformula list = profile @@
  if !destructive_rewrites || !(p.rewritten) || can_rewrite p then [] else (
    (* perform just a single rewrite here; remaining will occur in rw_simplify_all *)
    let& q = opt_to_list (rewrite_from used p false) in
    p.rewritten := true;
    assert (q.rule = "rw");
    {q with rule = "nrw"; destruct = true; rewritten = ref false}
  )

let generate queue p used : pformula list = profile @@
  nondestruct_rewrite !used p @ all_eres p @
  concat_map (all_super queue p) !used

let rw_simplify_all queue used found ps = profile @@
  let simplify (p: pformula) : pformula option =
    let p = rw_simplify true "generated" queue used found p in
    p |> Option.iter (fun p -> queue := PFQueue.add (Unprocessed p) (queue_cost p) !queue);
    p in
  filter_map simplify ps

let rec build_map pformulas : pformula FormulaMap.t * pformula list =
  match pformulas with
    | [] -> (FormulaMap.empty, [])
    | p :: ps ->
        let map, ps = build_map ps in
        let c = canonical p in
        if FormulaMap.mem c map then
          if is_ac p then (map, p :: ps) else (
            dbg_print_formula false "dropping redundant formula: " p;
            (map, ps))
        else (FormulaMap.add c p map, p :: ps)

let refute pformulas cancel_check : proof_result = profile @@
  let timeout = !(opts.timeout) in
  let map, pformulas = build_map pformulas in
  let found = ref map in
  let used, queue = ref [], ref PFQueue.empty in
  queue_add queue pformulas;
  let start = Sys.time () in
  let count, num_generated, max_cost = ref 0, ref 0, ref 0.0 in
  let stats () =
    { initial = length pformulas;
      given = !count; generated = !num_generated; max_cost = !max_cost} in
  let rec loop () =
    dbg_newline();
    let elapsed = Sys.time () -. start in
    if timeout > 0.0 && elapsed > timeout then Timeout
    else if cancel_check () then Stopped
    else match PFQueue.pop !queue with
      | None -> GaveUp
      | Some ((item, (cost, _, _)), q) ->
          queue := q;
          max_cost := max cost !max_cost;
          let (rewritten, generated) = match item with
            | Unprocessed given -> (
                match forward_simplify queue used found given with
                  | None -> ([], [])
                  | Some p -> (
                      incr count;
                      dbg_print_formula false (sprintf "[%.3f s] given: " elapsed) given;
                      if p.formula = _false then ([], [p]) else
                        let splits = all_split p in
                        if is_and (remove_for_all p.formula) then (
                          remove_from_map found p;
                          ([], splits)
                        ) else (
                          let rewritten = back_simplify found p used in
                          used := p :: !used;
                          let generated = generate queue p used in
                          (rewritten, splits @ generated)))
                        )
            | Deferred (dp, cp) ->
                if !debug > 1 then printf "deferred superposition: %d, %d\n" dp.id cp.id;
                let generated =
                  if memq dp !used && memq cp !used then all_super1 dp cp
                  else (if !debug > 1 then printf "  no longer present; ignoring\n"; []) in
                ([], generated) in
          num_generated := !num_generated + length generated;
          let new_pformulas =
            rw_simplify_all queue used found (rev (rewritten @ generated)) in
          match find_opt (fun p -> p.formula = _false) new_pformulas with
            | Some p -> Proof (p, stats ())
            | None -> loop () in
  loop ()

let def_match template f : (id * id) option = head_opt @@
  let g = prefix_vars (Parser.parse_formula template) in
  let+ (_, vsubst) = _match !comm_ops g (remove_for_all f) in
  match (let& x = ["f"; "g"; "x"; "y"] in assoc ("$" ^ x) vsubst) with
    | [Const (c, _ctyp); Const (d, _dtyp); Var _; Var _] -> [(c, d)]
    | _ -> []

let def_is_or_equal f : (str * str) option =
  def_match "f(x)(y) ↔ g(x)(y) ∨ x = y" f

let def_is_synonym f : (str * str) option =
  def_match "f(x)(y) ↔ g(y)(x)" f

let def_is_atomic f : (str * str) option = match remove_for_all f with
  | App (App (Const ("(↔)", _), f), g) -> (
      match head_of f, head_of g with
        | Const (c, _), Const (d, _) when not (mem d logical_ops) ->
            Some (c, d)
        | _ -> None)
  | _ -> None

let is_safe_for_rewrite f =
  let xs, _ = gather_for_all f in
  is_some (def_is_synonym f) ||
    length xs <= 1 && is_some (def_is_atomic f)

(* Given an associative/commutative operator *, construct the axiom
 *     x * (y * z) = y * (x * z)
 * which turns * into a ground convergent system.
 * See e.g. Baader/Nipkow, section 11.2 "Ordered rewriting". *)
let ac_completion_axiom op typ =
  let c_op = Const (op, Fun (typ, Fun (typ, typ))) in
  let var v = Var (v, typ) in
  let e1 = apply [c_op; var "x"; apply [c_op; var "y"; var "z"]] in
  let e2 = apply [c_op; var "y"; apply [c_op; var "x"; var "z"]] in
  for_all_vars_typ (["x"; "y"; "z"], typ) (Eq (e1, e2))

let to_pformula name f =
  create_pformula name [] (rename_vars (lower_definition f))

let ac_completion op typ : pformula =
  if !debug > 0 then printf "AC operator: %s\n\n" (strip_prefix op);
  ac_ops := (op, typ) :: !ac_ops;
  let name = "AC completion: " ^ basic_const op in
  let axiom = { (to_pformula name (ac_completion_axiom op typ)) with ac = Some Extra } in
  dbg_newline ();
  axiom

(* Given a left-distributive or right-distributive axiom over operators * and +
 * where * is associative and commutative, add the complementary (right- or left-distributive)
 * axiom to produce a ground convergent system.
 * See e.g. Martin/Nipkow, Ordered Rewriting and Confluence, 4.7 Distributivity. *)
let dist_completion kind op1 op2 typ : pformula =
  let (kind2, t) = distributive_templates |> find (fun (k, _) -> k <> kind) in
  let op_type = Fun (typ, Fun (typ, typ)) in
  let vsubst = [("$f", Const (op1, op_type)); ("$g", Const (op2, op_type));
               ("$a", Var ("x", typ)); ("$b", Var ("y", typ)); ("$c", Var ("z", typ))] in
  let name = sprintf "distributive completion: %s, %s" (basic_const op1) (basic_const op2) in
  let f = for_all_vars_typ (["x"; "y"; "z"], typ) (subst_vars vsubst t) in
  let axiom = { (to_pformula name f) with ac = Some kind2 } in
  axiom

let ac_kind f : (ac_type * str * str * typ) option =
  match associative_axiom f with
    | Some (op, typ) -> Some (Assoc, op, "", typ)
    | None ->
        match commutative_axiom f with
          | Some (op, typ) -> Some (Comm, op, "", typ)
          | None -> (
              match distributive_axiom f with
                | Some (f, g, typ, kind) ->
                    if !debug > 0 then
                      printf "distributive operators: %s over %s\n\n"
                        (basic_const f) (basic_const g);
                    Some (kind, f, g, typ)
                | None -> None)

let rec map_const const_map c : id =
  match assoc_opt c const_map with
    | Some d -> map_const const_map d
    | None -> c

let consts_of const_map f : id list =
  map (map_const const_map) (all_consts f)

let use_premise const_map proof_consts f def is_ac _name =
  let fs = gather_and (remove_for_all f) in
  (not !step_strategy || is_ac || def ||
    fs |> for_all (fun g -> num_literals g <= 3 || length (all_consts g) <= 1)) && (
  fs |> exists (fun g ->
    subset (consts_of const_map g) proof_consts))

let const_def f : (id * id) option =
  opt_or_opt (def_is_synonym f)
    (opt_or_opt (def_is_or_equal f) (def_is_atomic f))

let find_proof_consts thm all_known local_known by_thms hyps const_map =
  let main_premises = map get_stmt_formula (thm :: by_thms @ hyps) in
  let proof_consts = unique (concat_map (consts_of const_map) main_premises) in
  let proof_types = unique (concat_map formula_base_types main_premises) in
  let extra =
    if !step_strategy then
      all_known |> concat_map (function
        | Definition (c, _, f) when mem c proof_consts ->
            if subset (formula_base_types f) proof_types
              then consts_of const_map f else []
        | _ -> [])
    else
      let+ stmt = local_known in
      let+ f = opt_to_list (stmt_formula stmt) in
      let cs = consts_of const_map f in
      if overlap cs proof_consts then cs else [] in
  unique (proof_consts @ extra)

let find_or_equal_ops stmts : id list =
  let+ s = filter is_definition stmts in
  let f = Option.get (stmt_formula s) in
  let& (c, _) = opt_to_list (def_is_or_equal f) in
  c

let gen_pformulas thm all_known local_known : pformula list =
  let by_thms = all_known |> filter (fun s -> mem (stmt_ref s) (thm_by thm)) in
  let by_contradiction = (stmt_formula thm = Some _false) in
  let hyps = rev (filter is_hypothesis local_known) in
  let const_map =
    let+ s = filter is_definition all_known in
    opt_to_list (const_def (get_stmt_formula s)) in
  let proof_consts = find_proof_consts thm all_known local_known by_thms hyps const_map in
  let scan ops stmt : (ac_type * str * typ) list * pformula list =
    match stmt_formula stmt with
      | None -> (ops, [])
      | Some f ->
          let by = memq stmt by_thms in
          let def = defined_symbol stmt in
          let kind_op = ac_kind f in
          if not ( by || is_hypothesis stmt ||
                   use_premise const_map proof_consts f
                               (is_some def) (is_some kind_op) (stmt_name stmt))
          then (ops, []) else
          let kind = Option.map (fun (kind, _, _, _) -> kind) kind_op in
          let hyp = match index_of_opt stmt hyps with
            | Some i ->
                (* when proving ⊥, two last hypotheses have number 1 *)
                max 1 (i + 1 - (if by_contradiction then 1 else 0))
            | _ -> 0 in
          let p = { (to_pformula (stmt_id_name stmt) f)
            with hypothesis = hyp;
                 definition = opt_default def "";
                 by; ac = kind;
                 safe_for_rewrite = is_some def && is_safe_for_rewrite f } in
          dbg_newline ();
          match kind_op with
            | Some (kind, op, "", typ) when kind = Assoc || kind = Comm ->
                let ps =
                  if kind = Comm then (comm_ops := op :: !comm_ops; []) else [p] in
                if mem (ac_other kind, op, typ) ops then
                  (remove (kind, op, typ) ops, ps @ [ac_completion op typ])
                else ((kind, op, typ) :: ops, ps)
            | Some (kind, op1, op2, typ)
                when (kind = LDist || kind = RDist) && mem (op1, typ) !ac_ops ->
                (ops, [p; dist_completion kind op1 op2 typ])
            | _ -> (ops, [p]) in
  concat (snd (fold_left_map scan [] all_known))

let encode_consts all_known local_known thm : statement list * statement list * statement =
  let consts = map fst (filter_map decl_var all_known) in
  let rec log10 n =
    if n = 0 then 0 else 1 + log10 (n / 10) in
  let digits = log10 (length consts - 1) in
  let map_const _typ c =
    if c = "_" || mem c logical_ops then c else
      match index_of_opt c consts with
        | Some i -> sprintf "[%0*d]%s" digits i c
        | None ->
            printf "encode_consts: %s\n" c;
            failwith "encode_consts" in
  let rec mapf = function
    | Const (c, typ) -> Const (map_const typ c, typ)
    | f -> map_formula mapf f in
  let map_stmt = map_statement1 map_const Fun.id mapf in
  (map map_stmt (map strip_proof all_known),
   map map_stmt (map strip_proof local_known),
   map_stmt thm)

let functional_extend f : formula list = match f with
  | Eq (g, h) -> (match type_of g with
      | Fun (t, Bool) ->  (* apply functional extensionality *)
          [_for_all "x" t (_iff (App (g, Var ("x", t))) (App (h, Var ("x", t))))]
      | _ -> [])
  | _ -> []

let prove all_known local_known thm cancel_check : proof_result * float =
  step_strategy := is_step thm;
  destructive_rewrites := not !step_strategy;
  let all_known, local_known, thm = encode_consts all_known local_known thm in
  comm_ops := [];
  ac_ops := [];
  or_equal_ops := find_or_equal_ops all_known;
  formula_counter := 0;
  let known = gen_pformulas thm all_known local_known in
  let f = get_stmt_formula thm in
  let fs = f :: functional_extend f in
  let goals = fs |> map (fun f -> to_pformula (stmt_id_name thm) f) in
  let goals = if !(opts.disprove) then goals else
      goals |> map (fun goal -> create_pformula "negate" [goal] (negate goal.formula)) in
  let goals = goals |> map (fun g -> {g with goal = true}) in
  let all = known @ goals in
  dbg_newline ();
  let start = Sys.time () in
  let result = refute all cancel_check in
  (result, Sys.time () -. start)

let show_proof pf dis elapsed stats =
  printf "%sproved in %.2f s (" dis elapsed;
  if !(opts.stats) then printf "initial: %d; " stats.initial;
  printf "given: %d; "  stats.given;
  if !(opts.stats) then printf "generated: %d; " stats.generated;
  printf "cost: %.2f)\n" stats.max_cost;
  if !(opts.show_proofs) then (
    print_newline ();
    output_proof pf)

let prove_all thf modules = profile @@
  let dis = if !(opts.disprove) then "dis" else "" in
  let rec prove_stmts succeeded failed = function
    | [] ->
        if (not thf) then
          if failed = 0 then
            printf "%s theorems were %sproved.\n"
              (if !(opts.disprove) then "No" else "All") dis
          else if !(opts.keep_going) then
            if !(opts.disprove) then
              printf "%d theorems/steps disproved.\n" failed
            else
              printf "%d theorems/steps proved, %d not proved.\n" succeeded failed
    | (_, thm, all_known, local_known) :: rest ->
        let (succeed, fail) = match thm with
          | Theorem { steps = []; _ } ->
              print_endline (show_statement true thm ^ "\n");
              let (result, elapsed) =
                prove all_known local_known thm (Fun.const false) in
              let b = match result with
                  | Proof (pf, stats) -> show_proof pf dis elapsed stats; true
                  | GaveUp -> printf "Not %sproved.\n" dis; false
                  | Timeout -> printf "Time limit exceeded.\n"; false
                  | Stopped -> assert false in
              if thf then printf "SZS status %s\n" (szs result);
              print_newline ();
              if !(opts.disprove) then (not b, b) else (b, not b)
          | _ -> assert false in
        let (succeeded, failed) = (succeeded + int_of_bool succeed), (failed + int_of_bool fail) in
        if failed = 0 || !(opts.keep_going) then
          prove_stmts succeeded failed rest in
  let prove_modules = if !(opts.all_modules) then modules else [last modules] in
  prove_stmts 0 0 (expand_modules1 prove_modules modules)
