open List
open Printf

open Logic
open Statement
open Util

let formula_counter = ref 0

type pformula = {
  id: int;
  rule: string;
  parents: pformula list;
  formula: formula;
  cost: int
}

let print_formula with_origin prefix pformula =
  let prefix = prefix ^ sprintf "%d. " (pformula.id) in
  let origin =
    if with_origin then sprintf " [%s]" (comma_join
      ((pformula.parents |> map (fun p -> string_of_int (p.id))) @ [pformula.rule]))
    else "" in
  printf "%s%s\n"
    (indent_with_prefix prefix (show_multi pformula.formula)) origin

let merge_cost parents = sum (map (fun p -> p.cost) parents)

let mk_pformula rule parents formula delta =
  { id = 0; rule; parents; formula;
    cost = merge_cost parents + delta }

let number_formula clause =
  incr formula_counter;
  let clause = { clause with id = !formula_counter } in
  print_formula true "" clause;
  clause

let create_pformula rule parents formula delta =
  number_formula (mk_pformula rule parents formula delta)

let is_inductive formula = match kind formula with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false

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

let sym_weight = function
  | "∀" | "∃" -> 1_000_000
  | _ -> 1

let rec term_weight = function
  | Const (c, _) -> sym_weight c
  | Var _ -> 1
  | App (f, g) | Eq (f, g) -> term_weight f + term_weight g
  | Lambda (_, _, f) -> term_weight f

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
    let ws, wt = term_weight s, term_weight t in
    ws > wt || ws = wt && (
      unary_check s t ||
      match s, t with
        | App _, App _ ->
            let (f, ss), (g, ts) = collect_args s, collect_args t in
            const_gt f g || f = g && lex_gt kb_gt ss ts
        | _ -> false)

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
  
let green_subterms t =
  let rec gather acc t = t :: match t with
    | App _ ->
        let (head, args) = collect_args t in
        if head = c_for_all || head = c_exists then acc
        else fold_left gather acc args
    | Eq (f, g) -> fold_left gather acc [f; g]
    | _-> [] in
  gather [] t

let is_fluid t = match t with
  | App _ ->
      let (head, _args) = collect_args t in
      is_var head
  | Lambda _ -> not (is_ground t) (* approximate *)
  | _ -> false

(* replace v with u in t *)
let rec replace_in_term u v t =
  if t == v then u  (* physical equality test *)
  else map_formula (replace_in_term u v) t 

(*      D:[D' ∨ t = t']    C⟨u⟩
 *    ───────────────────────────   sup
 *          (D' ∨ C⟨t'⟩)σ             σ ∈ csu(t, u)
 *
 *     (i) u is not fluid
 *     (ii) u is not a variable
 *     (iii) tσ ≰ t'σ
 *     (iv) t = t' is maximal in D w.r.t. σ
 *)
let super cp dp d' d_lit =
  let c = prefix_vars cp.formula in
  match terms d_lit with
    | (false, _, _) -> []
    | (true, t, t') ->
        let+ t, t' = [(t, t'); (t', t)] in
        let exclude u = is_var u || is_fluid u in  (* i, ii *)
        let+ u = filter (Fun.negate exclude) (green_subterms c) in (
        match unify t u with
          | None -> []
          | Some sub ->
              let d'_s = map (rsubst sub) d' in
              let t_s, t'_s = rsubst sub t, rsubst sub t' in
              let t_eq_t'_s = Eq (t_s, t'_s) in
              if term_ge t'_s t_s ||   (* iii *)
                 not (is_inductive dp.formula) &&
                 not (is_maximal lit_gt t_eq_t'_s d'_s) then [] else  (* iv *)
                let c' = replace_in_term t' u c in
                let e = multi_or (d'_s @ [rsubst sub c']) in
                let tt'_show = show_formula (Eq (t, t')) in
                let u_show = str_replace "\\$" "" (show_formula u) in
                let rule = sprintf "sup: %s / %s" tt'_show u_show in
                [mk_pformula rule [dp; cp] (unprefix_vars e) 0])

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
              [mk_pformula "eres" [cp] (multi_or c1) 0]

let split f = match bool_kind f with
  | Binary ("∨", s, t) -> Some (s, t)
  | Binary ("→", s, t) -> Some (_not s, t)
  | _ -> None

let rec expand f = match split f with
  | Some (s, t) -> expand s @ expand t
  | None -> [f]

let rec simp f = match bool_kind f with
  | Not f ->
      let f = simp f in (
      match bool_kind f with
        | True -> _false
        | False -> _true
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
        | _ -> logical_op op p q)
  | Other (Eq (f, g)) ->
      let f, g = simp f, simp g in
      if f = g then _true else Eq (f, g)
  | _ -> map_formula simp f

let is_tautology f = mem _true (expand f)

let simplify pformula =
  let f = simp pformula.formula in
  if is_tautology f then None
  else Some { pformula with formula = f }

let clausify_step pformula lits =
  let rec new_clauses f = match split f with
    | Some (s, t) -> Some [s; t]
    | None -> match bool_kind f with
      | Quant ("∀", x, typ, f) ->
          let f =
            let vars = concat_map free_vars lits in
            if mem x vars then 
              let y = next_var x vars in
              subst1 f (Var (y, typ)) x
            else f in
          Some [f]
      | Quant ("∃", x, typ, f) ->
          let skolem = Const (sprintf "%s%d" x pformula.id, typ) in
          Some [subst1 f skolem x]
      | Not g -> (match bool_kind g with
        | Binary ("→", f, g) -> Some [_and f (_not g)]
        | Quant ("∀", x, typ, g) ->
            new_clauses (_exists x typ (_not g))
        | Quant ("∃", x, typ, g) ->
            new_clauses (_for_all x typ (_not g))
        | _ -> None)
      | _ -> None in
  let rec loop before = function
    | [] -> None
    | lit :: after ->
        match new_clauses lit with
          | Some fs -> Some (rev before @ fs @ after, fs)
          | None -> loop (lit :: before) after in
  if lits = [] then Some ([pformula.formula], [pformula.formula])  (* initial step *)
  else loop [] lits

let run_clausify pformula rule =
  let rec run lits =
    match clausify_step pformula lits with
      | None -> []
      | Some (lits, fs) ->
          let new_pformulas =
            let+ f = fs in
            rule pformula (remove f lits) f in
          new_pformulas @ run lits in
  run []

let max_cost = 1

let all_super cp dp =
  let new_cost = merge_cost [cp; dp] in
  if new_cost > max_cost then []
  else run_clausify cp (super dp) @ run_clausify dp (super cp)

let all_eres cp = run_clausify cp eres

let all_oc pformula =
  let rec run lits =
    match clausify_step pformula lits with
      | None -> []
      | Some (lits, fs) ->
          let split_on lit = match bool_kind lit with
            | Binary ("∧", f, g) ->
                let new_formulas = [f; g] |> map (fun t ->
                  let u = multi_or (replace t lit lits) in
                  mk_pformula "oc" [pformula] u 0) in
                Some new_formulas
            | _ -> None in
          match find_map split_on fs with
            | Some new_formulas -> new_formulas
            | None -> run lits in
  if is_inductive pformula.formula then [] else run []

let refute pformulas =
  print_newline ();
  let queue = Queue.of_seq (to_seq pformulas) in
  let rec loop used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some pformula ->
          print_formula false "given: " pformula;
          let new_pformulas =
            concat_map (all_super pformula) used @
            all_eres pformula @ all_oc pformula in
          let new_pformulas = filter_map simplify new_pformulas in
          let new_pformulas = map number_formula (rev new_pformulas) in
          let used = pformula :: used in
          print_newline ();
          match find_opt (fun p -> p.formula = _false) new_pformulas with
            | Some c -> Some c
            | None ->
                queue_add queue new_pformulas;
                loop used
  in loop []

let to_pformula stmt = stmt_formula stmt |> Option.map (fun f ->
  let init_cost = if is_inductive f then 1 else 0 in
  create_pformula (stmt_name stmt) [] (rename_vars f) init_cost)

let prove known_stmts stmt =
  formula_counter := 0;
  let known = known_stmts |> filter_map (fun s ->
    match to_pformula s with
      | Some p -> print_newline(); Some p
      | None -> None) in
  let pformula = Option.get (to_pformula stmt) in
  let negated =
    create_pformula "negate" [pformula] (_not pformula.formula) 0 in
  refute (known @ [negated])

let prove_all prog =
  let rec prove_stmts known_stmts = function
    | [] -> print_endline "All theorems were proved."
    | stmt :: rest ->
        if (match stmt with
          | Theorem _ -> (
              match prove known_stmts stmt with
                | Some _clause ->
                    printf "proof found!\n";
                    true
                | None -> false)
          | _ -> true) then (
          prove_stmts (known_stmts @ [stmt]) rest)
        else print_endline "Not proved.\n" in
  prove_stmts [] prog
