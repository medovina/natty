open Printf

open Logic
open Options
open Statement
open Util

let formula_counter = ref 0
let consts = ref ([] : (id * typ) list)
let ac_ops = ref ([] : (id * typ) list)
let goal_consts = ref ([] : id list)

type pformula = {
  id: int;
  rule: string;
  parents: pformula list;
  rewrites: pformula list;
  simp: bool;
  formula: formula;
  delta: float;
  cost: float;
  hypothesis: bool;
  goal: bool;
  derived: bool;
  definition: bool
}

let ac_axioms = ref ([] : pformula list)

let rec num_literals f = match bool_kind f with
  | True | False -> 0
  | Not f -> num_literals f
  | Binary (_, _, t, u) -> num_literals t + num_literals u
  | Quant (_, _, _, u) -> num_literals u
  | Other _ -> 1

let weight1 goal_relative f =
  let rec weigh f = match f with
    | Const (c, _typ) ->
        if f = _false || goal_relative && mem c !goal_consts then 0 else 1
    | Var _ -> 1
    | App (f, g) -> weigh f + weigh g
    | Eq (f, g) -> 1 + weigh f + weigh g
    | Lambda (_, _, f) -> weigh f in
  weigh (remove_quantifiers f)

let weight = weight1 false
let goal_rel_weight = weight1 true

let print_formula with_origin prefix pf =
  let prefix =
    if pf.id > 0 then prefix ^ sprintf "%d. " (pf.id) else prefix in
  let origin =
    if with_origin then
      let parents = pf.parents |> map (fun p -> string_of_int (p.id)) in
      let rule = if pf.rule <> "" then [pf.rule] else [] in
      let rewrites = rev pf.rewrites |> map (fun r -> r.id) in
      let rw = if rewrites = [] then []
        else [sprintf "rw(%s)" (comma_join (map string_of_int rewrites))] in
      let simp = if pf.simp then ["simp"] else [] in
      let all = parents @ rule @ rw @ simp in
      sprintf " [%s]" (comma_join all)
    else "" in
  let mark b c = if b then " " ^ (if pf.derived then c else to_upper c) else "" in
  let annotate = mark pf.definition "d" ^ mark pf.goal "g" ^ mark pf.hypothesis "h" in
  printf "%s%s {%d/%d: %.2f%s}\n"
    (indent_with_prefix prefix (show_multi pf.formula))
    origin (num_literals pf.formula) (weight pf.formula) pf.cost annotate

let dbg_print_formula with_origin prefix pformula =
  if !debug > 0 then print_formula with_origin prefix pformula

let is_inductive pformula = match kind pformula.formula with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false
  
let associative_axiom f =
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

let commutative_axiom f = remove_universal f |> function
    | Eq (f, g) -> (match kind f, kind g with
        | Binary (op, _, Var (x, typ), Var (y, _)), Binary (op', _, Var (y', _), Var (x', _))
            when (op, x, y) = (op', x', y') -> Some (op, typ)
        | _ -> None)
    | _ -> None

let is_commutative_axiom p = Option.is_some (commutative_axiom p.formula)
  
let orig_goal p = p.goal && not p.derived

let orig_hyp p = p.hypothesis && not p.derived

let merge_cost parents = match unique parents with
    | [] -> 0.0
    | [p] -> p.cost
    | parents ->
        let ancestors = search parents (fun p -> p.parents) in
        sum (ancestors |> map (fun p -> p.delta))

let inducted p =
  search [p] (fun p -> p.parents) |> exists (fun p -> is_inductive p)

let cost_limit = 1.0

let mk_pformula rule parents step formula =
  { id = 0; rule; rewrites = []; simp = false; parents; formula;
    goal = exists (fun p -> p.goal) parents;
    delta = 0.0; cost = 0.0;
    hypothesis = exists (fun p -> p.hypothesis) parents;
    derived = step || exists (fun p -> p.derived) parents;
    definition = not step && exists (fun p -> p.definition) parents }

let number_formula pformula =
  if pformula.id > 0 then pformula
  else (
    assert ((pformula.parents @ pformula.rewrites) |> for_all (fun p -> p.id > 0));
    incr formula_counter;
    { pformula with id = !formula_counter } )

let create_pformula rule parents formula =
  let p = number_formula (mk_pformula rule parents false formula) in
  dbg_print_formula true "" p;
  p

let is_skolem s = is_letter s.[0] && is_digit s.[strlen s - 1]

(* Symbol precedence for term ordering.  From highest to lowest:
 *   Skolem constants created during inference
 *   constants from input text, in declaration order (later = higher)
 *   predefined constants (e.g. ¬, ∧, ∨), alphabetically (arbitrarily)
 *   ⊥
 *   T 
 *)
let const_gt f g =
  let prio (c, c_type) =
    let index = match find_index (fun x -> x = (c, c_type)) !consts with
      | None ->
          if is_skolem c then Some (length !consts)
          else (
            if c.[0] <> '@' && c.[0] <> '_' && not (mem c logical_ops)
            then (printf "no precedence: %s" c; assert false);
            None)
      | Some i -> Some i in
    (index, c) in
  match f, g with
    | Const ("⊤", _), _ -> false
    | Const _, Const ("⊤", _) -> true
    | Const ("⊥", _), _ -> false
    | Const _, Const ("⊥", _) -> true
    | Const (f, f_type), Const (g, g_type) ->
        prio (f, f_type) > prio (g, g_type)
    | _ -> failwith "const_gt"

let rec lex_gt gt ss ts = match ss, ts with
  | [], [] -> false
  | s :: ss, t :: ts ->
    gt s t || s = t && lex_gt gt ss ts
  | _ -> failwith "lex_gt"

let lookup_var v vars = opt_default (assoc_opt v vars) 0

(* Lexicographic path ordering on first-order terms.  We use
 * the optimized version lpo_4 described in Lochner, "Things to Know
 * When Implementing LPO". *)
let rec lpo_gt s t =
  match t with
    | Var (y, _) -> s <> t && is_var_in y s
    | _ ->
        is_app_or_const s && is_app_or_const t &&
          let (f, ss), (g, ts) = collect_args s, collect_args t in
          let (nf, ng) = length ss, length ts in
          if const_gt f g || f = g && nf > ng then majo s ts
          else if f = g && nf = ng then lex_ma s t ss ts
          else alpha ss t

and alpha ss t = exists (fun s -> s = t || lpo_gt s t) ss

and majo s ts = for_all (lpo_gt s) ts

and lex_ma s t ss ts = match ss, ts with
  | [], [] -> false
  | s_i :: ss, t_i :: ts ->
      if s_i = t_i then lex_ma s t ss ts
      else if lpo_gt s_i t_i then majo s ts
      else alpha ss t
  | _ -> failwith "lex_ma"
            
let get_index x map =
  match index_of_opt x !map with
    | Some i -> length !map - 1 - i
    | None ->
        map := x :: !map;
        length !map - 1

let de_bruijn_encode x =
  let rec encode count t = match t with
    | Var (id, _typ) ->
        if id = x then _const ("@db" ^ string_of_int count) else t
    | Lambda (id, typ, f) ->
        if id = x then t else Lambda (id, typ, encode (count + 1) f)
    | t -> map_formula (encode count) t in
  encode 0

(* Map higher-order terms to first-order terms as described in
 * Bentkamp et al, section 3.9 "A Concrete Term Order".  That section introduces
 * a distinct symbol f_k for each arity k.  We use the symbol f to represent
 * all the f_k, then order by arity in lpo_gt.
 * We do not implement the transformation to terms ∀_1', ∃_1', z_u', which is
 * intended for the Knuth-Bendix ordering. *)
let encode_term type_map fluid_map t =
  let encode_fluid t = _var ("@v" ^ string_of_int (get_index t fluid_map)) in
  let encode_type typ = _const ("@t" ^ string_of_int (get_index typ type_map)) in
  let rec encode t =
    match t with
      | Const _ -> t
      | Var (v, _) -> _var v
      | App _ ->
          let (head, args) = collect_args t in
          let head = match head with
            | Var (v, _) -> _var v
            | _ -> head in (
          match head with
            | Var _ -> encode_fluid (apply (head :: args))
            | Const (q, _) when q = "∀" || q = "∃" -> (
                match args with
                  | [Lambda (x, typ, f)] ->
                      let q1 = _const ("@" ^ q) in
                      apply [q1; encode_type typ; encode (de_bruijn_encode x f)]
                  | _ -> failwith "encode_term")
            | Const _ ->
                apply (head :: map encode args)
            | _ -> failwith "encode_term")
      | Lambda (x, typ, f) ->
          if is_ground t then
            apply [_const "@lam"; encode_type typ; encode (de_bruijn_encode x f)]
          else encode_fluid t (* assume fluid *)
      | Eq (t, u) ->
          apply [_const "@="; encode_type (type_of t); encode t; encode u] in
  encode t

let term_gt s t =
  profile "term_gt" @@ fun () ->
  let type_map, fluid_map = ref [], ref [] in
  let s1 = encode_term type_map fluid_map s in
  let t1 = encode_term type_map fluid_map t in
  lpo_gt s1 t1

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

let or_split f = match bool_kind f with
  | Binary ("∨", _, s, t) -> Some (s, t)
  | Binary ("→", _, s, t) -> Some (negate s, t)
  | Not g -> (match bool_kind g with
    | Binary ("∧", _, f, g) -> Some (negate f, negate g)
    | Binary ("↔", _, f, g) -> Some (_not (implies f g), _not (implies g f))
    | _ -> None)
  | _ -> None

(* Clausify ignoring quantifiers and conjunctions *)
let rec mini_clausify f = match or_split f with
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
        oc(¬(s ↔ t)) = ¬(s → t) ∨ ¬(t → s)
        oc(¬(∀x.s)) = s[k(y̅)/x] = ⊥
        oc(¬(∃x.s)) = s[y/x] = ⊥  (y not in s or C)
        
        k is a new constant
        y̅ are all free variables in ∃x.s
*)

let clausify_step id lits in_use =
  let rec new_lits f = match or_split f with
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
          let skolem_type = fold_right1 mk_fun_type (map snd vars_types @ [typ]) in
          let c = sprintf "%s%d" x id in
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
        | Quant ("∀", x, typ, g) ->
            new_lits (_exists x typ (negate g))
        | Quant ("∃", x, typ, g) ->
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

let clausify_steps1 id lits in_use =
  let rec run ((lits, _, _) as step) =
    step :: match clausify_step id lits in_use with
      | None -> []
      | Some step -> run step in
  run (lits, lits, lits)

let clausify_steps p = clausify_steps1 p.id [p.formula] None

let run_clausify pformula rule =
  let+ (lits, new_lits, _) = clausify_steps pformula in
  let+ f = new_lits in
  rule pformula (remove1 f lits) f
  
let clausify1 id lits in_use =
  let (lits, _, _) = last (clausify_steps1 id lits in_use) in
  lits

let clausify p = clausify1 p.id [p.formula] None

let prefix_var var = "$" ^ var

let is_prefixed var = var.[0] = '$'

let prefix_vars f =
  let rec prefix outer = function
    | Var (x, typ) when not (mem x outer) ->
        Var (prefix_var x, typ)
    | Lambda (x, _typ, f) ->
        Lambda (x, _typ, prefix (x :: outer) f)
    | f -> map_formula (prefix outer) f
  in prefix [] f

let unprefix_vars f =
  let rec build_map all_vars = function
    | [] -> []
    | var :: rest ->
        if is_prefixed var then
          let v = string_from var 1 in
          let w = next_var v all_vars in
          (var, w) :: build_map (w :: all_vars) rest
        else build_map all_vars rest in
  let var_map = build_map (all_vars f) (free_vars f) in
  let rec fix outer = function
    | Var (v, typ) as var when not (mem v outer) ->
        if is_prefixed v then Var (assoc v var_map, typ) else var
    | Lambda (x, _typ, f) ->
      Lambda (x, _typ, fix (x :: outer) f)
    | f -> map_formula (fix outer) f in
  fix [] f

(* Gather green or blue subterms.  *)
let subterms is_blue t =
  let rec gather parent_eq acc t =
    (if is_var t then [] else [(t, parent_eq)]) @ match t with
      | App _ ->
          let (head, args) = collect_args t in
          if head = c_for_all || head = c_exists then
            if is_blue then match args with
              | [Lambda (_x, _typ, f)] -> gather parent_eq acc f
              | _ -> acc
            else acc
          else fold_left (gather parent_eq) acc
                  (if is_blue then head :: args else args)
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

let is_eligible sub parent_eq =
  parent_eq |> for_all (fun (s, t) ->
    not (term_gt (subst_n sub t) (subst_n sub s)))

let top_level pos u c sub inductive =
  let cs = mini_clausify c in
  let lit = if pos then u else _not u in
  mem lit cs &&
    (inductive || is_maximal lit_gt (rsubst sub lit) (map (rsubst sub) cs))

let simp_eq = function
  | Eq (Eq (t, t'), f) when f = _true -> Eq (t, t')
  | f -> f

let is_higher subst = subst |> exists (fun (_, f) -> is_lambda f)

let oriented t t' = [(t, t'); (t', t)] |>
  filter (fun (t, t') -> not (term_ge t' t))

let eq_pairs para_ok f = match terms f with
  | (true, t, t') ->
      if is_bool_const t' then [(t, t')]
      else (Eq (t, t'), _true) ::
        (if para_ok then oriented t t' else [])   (* iii: pre-check *)
  | (false, t, t') -> [(Eq (t, t'), _false)]

let is_resolution p = starts_with "res:" p.rule

let trim_rule rule =
  match String.index_opt rule ':' with
    | Some i -> String.sub rule 0 i
    | None -> rule

let origin pf =
  if pf.parents = [] then "axiom"
  else if pf.rule = "negate" || pf.rule = "negate1" then "goal"
  else trim_rule pf.rule

let by_induction p = exists is_inductive p.parents

type features = {
  orig: string; from_goal: bool;
  by_definition: bool; by_induction: bool; by_commutative: bool;
  lits: int; lits_lt_min: bool; lits_gt_max: bool; lits_eq_max: bool;
  lits_eq_1: bool; lits_le_2: bool;
  lits_rel_min: int; lits_rel_max: int; lits_rel_right: int;
  weight: int; weight_lt_min: bool; weight_lt_max: bool; weight_le_max: bool;
  weight_rel_min: int; weight_rel_max: int; weight_rel_right: int;
  goal_rel_weight: int
}

let features p =
  let parent_lits = p.parents |> map (fun q -> num_literals q.formula) in
  let parent_weights = p.parents |> map (fun q -> weight q.formula) in
  let lits, w = num_literals p.formula, weight p.formula in
  let min_lits, max_lits = minimum parent_lits, maximum parent_lits in
  let min_weight, max_weight = minimum parent_weights, maximum parent_weights in {
    orig = origin p; from_goal = p.goal;
    by_definition = p.parents |> exists (fun q -> q.definition);
    by_induction = by_induction p;
    by_commutative = p.parents |> exists (fun q -> is_commutative_axiom q);
    lits; lits_lt_min = lits < min_lits; lits_gt_max = lits > max_lits;
    lits_eq_max = lits = max_lits;
    lits_eq_1 = lits = 1; lits_le_2 = lits <= 2;
    lits_rel_min = lits - min_lits; lits_rel_max = lits - max_lits;
      lits_rel_right = lits - nth parent_lits 1;
    weight = w; weight_lt_min = w < min_weight; weight_lt_max = w < max_weight;
      weight_le_max = w <= max_weight;
    weight_rel_min = w - min_weight; weight_rel_max = w - max_weight;
      weight_rel_right = w - nth parent_weights 1;
    goal_rel_weight = goal_rel_weight p.formula
  }

let csv_header =
  "theorem,id,orig,from_goal," ^
  "by_definition,by_induction,by_commutative," ^
  "lits,lits_lt_min,lits_gt_max,lits_eq_max," ^
  "lits_eq_1,lits_le_2," ^
  "lits_rel_min,lits_rel_max,lits_rel_right," ^
  "weight,weight_lt_min,weight_lt_max,weight_le_max,weight_rel_min,weight_rel_max,weight_rel_right," ^
  "goal_rel_weight,in_proof,formula"

let all_steps pformula =
  search [pformula] (fun p -> unique (p.parents @ p.rewrites))

let write_generated thm_name all proof out =
  let thm_name = str_replace "theorem" "thm" thm_name in
  let in_proof = all_steps proof in
  all |> filter (fun pf -> length pf.parents = 2)
      |> sort_by (fun pf -> pf.id) |> iter (fun pf ->
    let f = features pf in
    let b = function | true -> "T" | false -> "F" in
    fprintf out "\"%s\",%d,%s,%s," thm_name pf.id f.orig (b f.from_goal);
    fprintf out "%s,%s,%s," (b f.by_definition) (b f.by_induction) (b f.by_commutative);
    fprintf out "%d,%s,%s,%s,"  
      f.lits (b f.lits_lt_min) (b f.lits_gt_max) (b f.lits_eq_max);
    fprintf out "%s,%s," (b f.lits_eq_1) (b f.lits_le_2);
    fprintf out "%d,%d,%d,"f.lits_rel_min f.lits_rel_max f.lits_rel_right;
    fprintf out "%d,%s,%s,%s,%d,%d,%d," f.weight
      (b f.weight_lt_min) (b f.weight_lt_max) (b f.weight_le_max)
      f.weight_rel_min f.weight_rel_max f.weight_rel_right;
    fprintf out "%d,%s,%s\n" f.goal_rel_weight (b (memq pf in_proof)) (show_formula pf.formula)
  )

let cost p =
  match p.parents with
    | [_; _] ->
        let f = features p in
        if f.by_induction then 0.03
        else if f.lits_lt_min then 0.0
        else if f.lits_gt_max then 10.0
        else if is_resolution p then
          if f.lits_eq_max && not (f.from_goal || f.by_definition) then 10.0 else
          if f.weight_lt_min then 0.0 else
          if f.weight_le_max then 0.01 else 0.03
        else (* paramodulation *)
          if f.by_commutative then 0.01 else
          if f.weight_lt_max then
            if f.lits_le_2 then 0.02 else 10.0
          else 10.0

    | _ -> 0.0

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
 *     (vii) if t'σ = ⊥, u is a literal
             if t'σ = ⊤, ¬u is a literal *)

let super only_res dp d' t_t' cp c c1 : pformula list =
  profile "super" @@ fun () ->
  let dbg = (dp.id, cp.id) = !debug_super in
  if dbg then printf "super\n";
  let pairs = eq_pairs (not only_res) t_t' in  (* iii: pre-check *)
  let+ (t, t') = pairs in
  let+ (u, parent_eq) = green_subterms c1 |>
    filter (fun (u, _) -> not (is_var u || is_fluid u)) in  (* i, ii *)
  match unify t u with
    | None -> []
    | Some sub ->
        if dbg then printf "super: unified %s with %s\n" (show_formula t) (show_formula u);
        let d'_s = map (rsubst sub) d' in
        let t_s, t'_s = rsubst sub t, rsubst sub t' in
        let t_eq_t'_s = Eq (t_s, t'_s) in
        let d_s = t_eq_t'_s :: d'_s in
        let c_s = map (rsubst sub) c in
        let c1_s = rsubst sub c1 in
        let fail n = if dbg then printf "super: failed check %d\n" n; true in
        if is_higher sub && (only_res || not (orig_goal dp)) ||
            is_bool_const t'_s &&
              not (top_level (t'_s = _false) u c1 sub (is_inductive cp)) && fail 7 || (* vii *)
            not (is_maximal lit_gt (simp_eq t_eq_t'_s) d'_s) && fail 6 ||  (* vi *)
            term_ge t'_s t_s && fail 3 ||  (* iii *)
            not (is_maximal lit_gt c1_s c_s) && fail 4 ||  (* iv *)
            not (is_eligible sub parent_eq) && fail 4 ||  (* iv *)
            t'_s <> _false && clause_gt d_s c_s && fail 5  (* v *)
        then [] else (
          let c1_t' = replace_in_formula t' u c1 in
          let c_s = replace1 (rsubst sub c1_t') c1_s c_s in
          let e = unprefix_vars (multi_or (d'_s @ c_s)) in
          let tt'_show = str_replace "\\$" "" (show_formula (Eq (t, t'))) in
          let u_show = show_formula u in
          let res = is_bool_const t' in
          let rule = sprintf "%s: %s / %s" (if res then "res" else "para") tt'_show u_show in
          if dbg then printf "super: passed checks, produced %s\n" (show_formula e);
          [mk_pformula rule [dp; cp] true e])

let all_super quick dp cp : pformula list =
  profile "all_super" @@ fun () ->
  let dbg = (dp.id, cp.id) = !debug_super in
  if dbg then printf "all_super\n";
  let no_induct d c = is_inductive c &&
    (not (orig_goal d) && not (orig_hyp d) || inducted d) in
  let allow p =
    p.hypothesis || p.goal || p.definition || is_commutative_axiom p ||
    num_literals p.formula = 1 in
  if dp.id = cp.id || not (allow dp || allow cp) || no_induct dp cp || no_induct cp dp
  then [] else
    let d_steps, c_steps = clausify_steps dp, clausify_steps cp in
    let+ (dp, d_steps, cp, c_steps) =
      [(dp, d_steps, cp, c_steps); (cp, c_steps, dp, d_steps)] in
    let+ (d_lits, new_lits, _) = d_steps in
    let d_lits, new_lits = map prefix_vars d_lits, map prefix_vars new_lits in
    let+ d_lit = new_lits in
    let+ (c_lits, _, exposed_lits) = c_steps in
    let+ c_lit = exposed_lits in
    super quick dp (remove1 d_lit d_lits) d_lit cp c_lits c_lit

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
              [mk_pformula "eres" [cp] true (multi_or c1)]

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

let all_split p =
  let skolem_names = ref [] in
  let rec run lits : formula list list =
    let lits1 = clausify1 p.id lits (Some skolem_names) in
    let split lit f g =
      let top = if lits1 = lits then [] else [lits] in
      let children = [f; g] |> concat_map (fun t -> run (replace1 t lit lits1)) in
      Some (top @ children) in
    let split_on lit = match bool_kind lit with
      | Binary ("∧", _, f, g) -> split lit f g
      | Binary ("↔", _, f, g) -> split lit (implies f g) (implies g f)
      | Not f -> (match bool_kind f with
          | Binary ("∨", _, f, g) -> split lit (_not f) (_not g)
          | Binary ("→", _, f, g) -> split lit f (_not g)
          | _ -> None)
      | _ -> None in
    match find_map split_on lits1 with
      | Some new_clauses -> new_clauses
      | None -> [lits] in
  if p.rule = "split" || is_inductive p then []
  else
    let splits = remove [p.formula] (run [p.formula]) in
    rev splits |> map (fun lits ->
      mk_pformula "split" [p] false (multi_or lits))

let update p rewriting f =
  let (r, simp) = match rewriting with
    | Some p -> ([p], false)
    | None -> ([], true) in
  if p.id = 0 then
    { p with rewrites = r @ p.rewrites; simp = p.simp || simp; formula = f }
  else
    { id = 0; rule = ""; rewrites = r; simp; parents = [p];
      goal = p.goal; delta = 0.0; cost = p.cost; formula = f;
      hypothesis = p.hypothesis; derived = p.derived; definition = p.definition }

(*     t = t'    C⟪tσ⟫
 *   ═══════════════════   rw
 *     t = t'    C⟪t'σ⟫
 *
 *   (i) tσ > t'σ
 *   (ii) (t = t')σ ≯ C
 *
 *)
let rewrite quick dp cp c_subterms : pformula list =
  if dp.id = cp.id then [] else
  let d = remove_universal dp.formula in
  if num_literals d > 1 then [] else
    let+ (t, t') = eq_pairs true d in
    let t, t' = prefix_vars t, prefix_vars t' in
    let c = cp.formula in
    let+ u = c_subterms in
    match try_match [] t u with
      | Some sub ->
          let t_s, t'_s = u, rsubst sub t' in
          if term_gt t_s t'_s &&  (* (i) *)
            (quick || type_of t = Bool ||
                not (clause_gt [Eq (t_s, t'_s)] [cp.formula])) then (* (ii) *)
            let e = b_reduce (replace_in_formula t'_s t_s c) in
            [update cp (Some dp) e]
          else []
      | _ -> []

let rewrite1 quick dp cp = rewrite quick dp cp (blue_subterms cp.formula)

(*     C    Cσ ∨ R
 *   ═══════════════   subsume
 *         C                 *)

let subsumes cp (d_lits, d_exist) : bool =
  let subsume subst c d =
    if d_exist = [] then try_match subst c d
    else
      (* Existential subsumption, e.g. x + 0 = x subsumes ∃z:ℕ.x + z = x *)
      let* subst = unify_or_match true subst c d in
      if subst |> for_all (fun (id, f) ->
        not (is_prefixed id) || mem id d_exist || 
          match f with
            | Var (id, _typ) -> not (is_prefixed id)
            | _ -> false) then Some subst else None in
  let rec subsume_lits c_lits d_lits subst : bool = match c_lits with
    | [] -> true
    | c :: c_lits ->
        d_lits |> exists (fun d ->
          subsume subst c d |> opt_exists (fun subst ->
            subsume_lits c_lits (remove1q d d_lits) subst)) in
  let c_lits = mini_clausify (remove_universal cp.formula) in
  subsume_lits c_lits d_lits []

let prefix_lits dp =
  let (f, exist) = remove_quants true dp.formula in
  (mini_clausify (prefix_vars f), map prefix_var exist)

let subsumes1 cp dp = subsumes cp (prefix_lits dp)

let any_subsumes cs dp : pformula option =
  profile "any_subsumes" @@ fun () ->
  let d_lits = prefix_lits dp in
  cs |> find_opt (fun cp -> subsumes cp d_lits)

let rec expand f = match or_split f with
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
        | "∧", True, _ -> q
        | "∧", _, True -> p
        | "∧", False, _ -> _false
        | "∧", _, False -> _false
        | "∧", t, u when t = u -> p
        | "∨", True, _ -> _true
        | "∨", _, True -> _true
        | "∨", False, _ -> q
        | "∨", _, False -> p
        | "∨", t, u when t = u -> p
        | "→", True, _ -> q
        | "→", _, True -> _true
        | "→", False, _ -> _true
        | "→", _, False -> simp (_not p)
        | "→", t, u when t = u -> _true
        | "↔", True, _ -> q
        | "↔", _, True -> p
        | "↔", False, _ -> _not q
        | "↔", _, False -> _not p
        | "↔", t, u when t = u -> _true
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

let rec canonical_lit = function
  | Eq (f, g) ->
      let f, g = canonical_lit f, canonical_lit g in
      if f < g then Eq (f, g) else Eq (g, f)
  | f -> map_formula canonical_lit f

let taut_lit f = match bool_kind f with
  | True -> true
  | Quant ("∃", x, _typ, Eq (Var (x', _), _)) when x = x' -> true
  | Quant ("∃", x, _typ, Eq (_, Var (x', _))) when x = x' -> true
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

let output_proof pformula =
  sort_by (fun pf -> pf.id) (all_steps pformula) |> iter (print_formula true "");
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
  type t = float * float * int
  let compare = Stdlib.compare
end)

let queue_delta p =
  if orig_goal p && p.rule = "negate1" then 0.1
  else if orig_hyp p then 0.2
  else if orig_goal p then 0.3
  else p.delta

let queue_cost p = (p.cost, queue_delta p, p.id)

let queue_add queue pformulas =
  let queue_element p = (p, queue_cost p) in
  let extra = PFQueue.of_list (map queue_element pformulas) in
  queue := PFQueue.(++) !queue extra

let dbg_newline () =
  if !debug > 0 then print_newline ()

let rewrite_opt dp cp c_subterms = head_opt (rewrite false dp cp c_subterms)

let rewrite_from ps q =
  let q_subterms = blue_subterms q.formula in
  find_map (fun p -> rewrite_opt p q q_subterms) ps

let repeat_rewrite used p : pformula =
  profile "repeat_rewrite" @@ fun () ->
  let rec loop p = match rewrite_from !used p with
    | None -> p
    | Some p -> loop p in
  loop p

let finish p f found delta cost =
  let p = { (number_formula p) with delta; cost } in
  dbg_print_formula true "" p;
  found := FormulaMap.add f p !found;
  if p.id = !(opts.show_proof_of) then output_proof p;
  p

let rw_simplify cheap src queue used found p =
  let p1 = repeat_rewrite used p in
  let p = simplify p1 in
  let taut = is_tautology p.formula in
  if taut || not (memq p !ac_axioms) && is_ac_tautology p.formula then (
    if !debug > 1 || !debug = 1 && src <> "generated" then (
      printf "%s %stautology: " src (if taut then "" else "ac ");
      if p1.formula <> p.formula then printf "%s ==> " (show_formula p1.formula);
      print_formula true "" p
    );
    None)
  else
    match (if cheap then None else any_subsumes !used p) with
      | Some pf ->
          if !debug > 0 then (
            let prefix = sprintf "%s subsumed by #%d: " src pf.id in
            print_line (prefix_show prefix p.formula));
          None
      | None ->
          if p.id > 0 then Some p else
            let delta = cost p in
            let cost = merge_cost p.parents +. delta in
            if cost > cost_limit then (
              if !debug > 1 then
                print_formula true "dropping (over cost limit): " {p with cost};
              None)
            else
              let f_canonical = canonical p in
              let final () = finish p f_canonical found delta cost in
              match FormulaMap.find_opt f_canonical !found with
                | Some pf ->
                    if cost < pf.cost then (
                      let p = final () in
                      if !debug > 0 then
                        printf "(%d is a duplicate of %d; replacing with lower cost of %.2f)\n"
                          p.id pf.id p.cost;
                      if PFQueue.mem pf !queue then
                        queue := PFQueue.add p (queue_cost p) (PFQueue.remove pf !queue)
                      else
                        used := p :: remove1 pf !used;
                      found := FormulaMap.add f_canonical p !found;
                      (* Ideally we would also update descendents of pf
                        to have p as an ancestor instead. *)
                      Some p
                    ) else (
                        let prefix = sprintf "%s duplicate of #%d: " src pf.id in
                        dbg_print_formula true prefix p;
                      None)
                | None ->
                    Some (final ())

type result = Proof of pformula * int * float | Timeout | GaveUp | Stopped

let szs = function
  | Proof _ -> "Theorem"
  | Timeout -> "Timeout"
  | GaveUp -> "GaveUp"
  | Stopped -> "Stopped"
                  
let forward_simplify queue used found p =
  profile "forward_simplify" @@ fun () ->
  rw_simplify false (sprintf "given (#%d) is" p.id) queue used found p
  
let back_simplify from used : pformula list =
  profile "back_simplify" @@ fun () ->
  let rec loop = function
    | [] -> ([], [])
    | p :: ps ->
        let (ps', rewritten) = loop ps in
        if subsumes1 from p then (
          if !debug > 1 then
            printf "%d. %s was back subsumed by %d. %s\n"
              p.id (show_formula p.formula) from.id (show_formula from.formula);
          (ps', rewritten))
        else match rewrite_from [from] p with
          | Some p' -> (ps', p' :: rewritten)
          | None -> (p :: ps', rewritten) in
  let (new_used, rewritten) = loop !used in
  used := new_used;
  rewritten

let generate p used =
  profile "generate" @@ fun () ->
  concat_map (all_super false p) !used @ all_eres p @ all_split p

let rw_simplify_all queue used found ps =
  profile "rw_simplify_all" @@ fun () ->
  let simplify (p: pformula) =
    let p = rw_simplify true "generated" queue used found p in
    p |> Option.iter (fun p -> queue := PFQueue.add p (queue_cost p) !queue);
    p in
  filter_map simplify ps

let refute thm_name pformulas cancel_check gen_out : result =
  profile "refute" @@ fun () ->
  let timeout = !(opts.timeout) in
  let found = ref @@ FormulaMap.of_list (pformulas |> map (fun p -> (canonical p, p))) in
  let used = ref [] in
  let queue = ref PFQueue.empty in
  queue_add queue pformulas;
  let start = Sys.time () in
  let all_generated = ref pformulas in
  let rec loop count max_cost =
    let elapsed = Sys.time () -. start in
    if timeout > 0.0 && elapsed > timeout then Timeout
    else if cancel_check () then Stopped
    else match PFQueue.pop !queue with
      | None -> GaveUp
      | Some ((given, _cost), q) ->
          queue := q;
          let max_cost = max given.cost max_cost in
          match forward_simplify queue used found given with
            | None ->
                if !debug > 0 then print_newline ();
                loop count max_cost
            | Some p ->
                let count = if count = 0 then (if p.goal then 1 else 0) else count + 1 in
                let prefix = if count = 0 then "" else sprintf "#%d, " count in
                dbg_print_formula false (sprintf "[%s%.3f s] given: " prefix elapsed) given;
                if p.formula = _false then Proof (p, count, max_cost) else
                  let rewritten = back_simplify p used in
                  used := p :: !used;
                  let generated = generate p used in
                  let new_pformulas =
                    rw_simplify_all queue used found (rev (rewritten @ generated)) in
                  dbg_newline ();
                  match find_opt (fun p -> p.formula = _false) new_pformulas with
                    | Some p -> Proof (p, count, max_cost)
                    | None ->
                        if !(opts.record_generated) then
                          all_generated := new_pformulas @ !all_generated;
                        queue_add queue new_pformulas;
                        loop count max_cost in
  let res = loop 0 0.0 in (
  match res with
    | Proof (proof, _, _) ->
        gen_out |> Option.iter (write_generated thm_name !all_generated proof);
    | _ -> ());
  res

(* Given an associative/commutative operator *, construct the axiom
 *     x * (y * z) = y * (x * z)
 * which turns * into a ground convergent system.
 * See e.g. Baader/Nipkow, section 11.2 "Ordered rewriting". *)
let ac_axiom (op, typ) =
  let c_op = Const (op, Fun (typ, Fun (typ, typ))) in
  let var v = Var (v, typ) in
  let e1 = apply [c_op; var "x"; apply [c_op; var "y"; var "z"]] in
  let e2 = apply [c_op; var "y"; apply [c_op; var "x"; var "z"]] in
  for_all_vars_typ (["x"; "y"; "z"], typ) (Eq (e1, e2))

type ac_type = Assoc | Comm

let ac_complete formulas : (id * formula * bool * bool) list =
  let rec scan ops = function
    | (name, f, is_hyp) :: rest -> 
        let kind = match associative_axiom f with
          | Some op_typ -> Some (Assoc, op_typ)
          | None -> match commutative_axiom f with
            | Some op_typ -> Some (Comm, op_typ)
            | None -> None in
        (name, f, is_hyp, Option.is_some kind) ::
        (match kind with
          | Some (kind, ((op, _typ) as op_typ)) ->
              let other = match kind with Assoc -> Comm | Comm -> Assoc in
              if mem (other, op_typ) ops then (
                if !debug > 0 then printf "AC operator: %s\n\n" op;
                ac_ops := op_typ :: !ac_ops;
                let axiom =
                  ("AC completion: " ^ without_type_suffix op, ac_axiom op_typ, false, true) in
                axiom :: scan (remove (kind, op_typ) ops) rest
              ) else scan ((kind, op_typ) :: ops) rest
          | None -> scan ops rest)
    | [] -> [] in
  scan [] formulas

let lower = function
  | Eq (Const _ as c,
      Lambda (x, x_typ, Lambda (y, y_typ,
        App (App ((Const _ as d), (Var (y', _) as vy)), (Var (x', _) as vx)))))
        when (x, y) = (x', y') ->
          let f = for_all_vars_typs [(x, x_typ); (y, y_typ)]
                    (Eq (apply [c; vx; vy], apply [d; vy; vx])) in
          (f, false)
  | Eq ((Const (_, typ) as c), (Lambda _ as l)) when target_type typ = Bool ->
      let (vars_typs, g) = gather_lambdas l in
      let f = for_all_vars_typs vars_typs (
                _iff (apply (c :: map mk_var' vars_typs)) g) in
      (f, true)
  | f -> (f, false)

let to_pformula name f =
  let (f, is_def) = lower f in
  { (create_pformula name [] (rename_vars f)) with definition = is_def }

let goal_resolve r p =
  let p = all_super true r p |> find_map (fun q ->
    let q = simplify q in
    if q.formula = _false then Some q else None) in
  Option.get p

let quick_refute all =
  profile "quick_refute" @@ fun () ->
  let index = FormulaMap.of_list (all |> map (fun p -> (canonical p, p))) in
  let proof p = Proof (number_formula p, -1, 0.0) in
  all |> find_map (fun p ->
    all |> find_map (fun q ->
      if p.id >= q.id then None else
      rewrite1 true p q @ rewrite1 true q p @ all_super true p q |> find_map (fun r ->
        let r = simplify r in
        if r.formula = _false then Some (proof r)
        else FormulaMap.find_opt (negate (canonical r)) index |> Option.map
          (fun p -> proof (goal_resolve (number_formula r) p))
      )))

let prove known_stmts thm cancel_check gen_out =
  let known_stmts = rev known_stmts in
  consts := filter_map decl_var known_stmts;
  ac_ops := [];
  let formulas = known_stmts |> filter_map (fun stmt ->
    stmt_formula stmt |> Option.map (fun f ->
      (stmt_name stmt, f, is_hypothesis stmt))) in
  formula_counter := 0;
  let formulas = ac_complete formulas in
  let known = formulas |> map (fun (name, f, is_hyp, is_ac_axiom) ->
    let p = {(to_pformula name f) with hypothesis = is_hyp } in
    if is_ac_axiom then ac_axioms := p :: !ac_axioms;
    dbg_newline (); p) in
  let goal = to_pformula (stmt_name thm) (Option.get (stmt_formula thm)) in
  goal_consts := subtract (all_consts (goal.formula)) logical_ops;
  let goals = if !(opts.disprove) then [goal] else
    ["negate1"; "negate"] |> map (fun rule ->
      create_pformula rule [goal] (_not goal.formula)) in
  let goals = goals |> map (fun g -> {g with goal = true}) in
  let all = known @ goals in
  dbg_newline ();
  let start = Sys.time () in
  let result = if !(opts.no_quick) then None else quick_refute all in
  let result = match result with
    | Some p -> p
    | None -> if !(opts.only_quick) then GaveUp else (
        if !debug > 0 then
          printf "no quick refutation in %.2f s; beginning main loop\n\n" (Sys.time () -. start);
          refute (stmt_name thm) all cancel_check gen_out) in
  (result, Sys.time () -. start)

let prove_all thf prog =
  profile "prove_all" @@ fun () ->
  let gen_out = if !(opts.record_generated) then
    let out = open_out "generated.csv" in
    fprintf out "%s\n" csv_header;
    Some out
  else None in
  let dis = if !(opts.disprove) then "dis" else "" in
  let rec prove_stmts all_success = function
    | [] ->
        if (not thf) then
          if all_success then
            printf "%s theorems were %sproved.\n"
              (if !(opts.disprove) then "No" else "All") dis
          else if !(opts.keep_going) then
            printf "Some theorems were %sproved.\n" dis
    | (thm, known) :: rest ->
        let success = match thm with
          | Theorem (_, _, None, _) ->
              print_endline (show_statement true thm ^ "\n");
              let (result, elapsed) =
                prove known thm (Fun.const false) gen_out in
              let b = match result with
                  | Proof (pf, given, cost) ->
                      let stats = if given < 0 then "0; quick" else
                        sprintf "%d; cost: %.2f" given cost in
                      printf "%sproved in %.2f s (given clauses: %s)\n" dis elapsed stats;
                      if !(opts.show_proofs) then (
                        print_newline ();
                        output_proof pf);
                      true
                  | GaveUp -> printf "Not %sproved.\n" dis; false
                  | Timeout -> printf "Time limit exceeded.\n"; false
                  | Stopped -> assert false in
              if thf then printf "SZS status %s\n" (szs result);
              print_newline ();
              if !(opts.disprove) then not b else b
          | Theorem _ -> true
          | _ -> assert false in
        if success || !(opts.keep_going) then
          prove_stmts (all_success && success) rest in
  prove_stmts true (expand_proofs prog);
  Option.iter Out_channel.close gen_out
