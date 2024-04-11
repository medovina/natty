open List
open Printf

open Logic
open Statement
open Util

let clause_counter = ref 0

type clause = {
  id: int;
  rule: string;
  parents: clause list;
  lits: formula list
}

let clause_to_formula clause = fold_left1 _or clause.lits

let clauses_to_formula cs = fold_left1 _and (map clause_to_formula cs)

let print_clause with_origin prefix clause =
  let prefix = prefix ^ sprintf "%d. " (clause.id) in
  let origin =
    if with_origin then sprintf " [%s]" (comma_join
      ((clause.parents |> map (fun p -> string_of_int (p.id))) @ [clause.rule]))
    else "" in
  printf "%s%s\n"
    (indent_with_prefix prefix (show_multi (clause_to_formula clause))) origin

let mk_clause rule parents lits =
  { id = 0; rule; parents; lits }

let number_clause clause =
  incr clause_counter;
  let clause = { clause with id = !clause_counter } in
  print_clause true "" clause;
  clause

let create_clause rule parents lits =
  number_clause (mk_clause rule parents lits)

let clause_formula clause =
  assert (length clause.lits = 1);
  hd (clause.lits)

let is_inductive clause = match kind (clause_formula clause) with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false

type env = {
  clauses: clause list;
  inductive: clause list;
  consts: id list
}

let empty_env = { clauses = []; inductive = []; consts = [] }

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

(* Lexicographic path ordering on first-order terms *)
let rec lpo_gt s t =
  match s, t with
    | s, Var (x, _) -> mem x (free_vars s) && s <> t
    | Var _, _ -> false
    | _ -> let (f, ss), (g, ts) = collect_args s, collect_args t in
        exists (fun s_i -> s_i = t || lpo_gt s_i t) ss ||
        for_all (fun t_j -> lpo_gt s t_j) ts &&
          (const_gt f g || f = g && lex_gt lpo_gt ss ts)

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
  if s_vars |> for_all (fun (v, n) -> n >= lookup_var v t_vars) then
    let ws, wt = term_weight s, term_weight t in
    ws > wt || ws = wt && (
      unary_check s t ||
      let (f, ss), (g, ts) = collect_args s, collect_args t in
      const_gt f g || f = g && lex_gt kb_gt ss ts)
  else false

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

let eq_terms = function
  | Eq (f, g) -> (true, f, g)
  | App (Const ("¬", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("¬", _), f) -> (false, f, mk_true)
  | f -> (true, f, mk_true)

let eq_formula eq f g = match eq, f, g with
  | true, f, Const ("⊤", _) | true, Const ("⊤", _), f -> f
  | false, f, Const ("⊤", _) | false, Const ("⊤", _), f  -> _not f
  | true, f, g -> Eq (f, g)
  | false, f, g -> mk_neq f g

let lit_to_multi f =
  let eq, t, u = eq_terms f in
  if eq then [[t]; [u]] else [[t; u]]

let lit_gt f g =
  multi_gt (multi_gt term_gt) (lit_to_multi f) (lit_to_multi g)

let rec prefix_vars = function
  | Var (x, typ) -> Var ("$" ^ x, typ)
  | f -> map_formula prefix_vars f

let unprefix_vars lits =
  let rec build_map vars = function
    | [] -> []
    | var :: rest ->
        if var.[0] = '$' then
          let v = string_from var 1 in
          let w = next_var v vars in
          (var, w) :: build_map (w :: vars) rest
        else build_map vars rest in
  let vars = all_vars (fold_left1 _or lits) in
  let var_map = build_map vars vars in
  let rec fix = function
    | Var (v, typ) as var ->
        if v.[0] = '$' then Var (assoc v var_map, typ) else var
    | f -> map_formula fix f in
  map fix lits

(*      C ∨ s ≠ t
 *     ───────────   eq_res (equality resolution) 
 *         Cσ          σ = mgu(s, t)  *)

let eq_res c =
  let+ lit = c.lits in
  match eq_terms lit with
    | (false, s, t) -> (
        match unify s t with
          | None -> []
          | Some sub ->
              let d = map (subst_n sub) (remove lit c.lits) in
              [mk_clause "eq_res" [c] d])
    | _ -> []

let subterms t =
  let rec gather acc t = t :: match t with  
    | App (f, g) | Eq (f, g) -> gather (gather acc g) f
    | _ -> [] in
  gather [] t

(* replace v with u in t *)
let rec replace u v t =
  if t == v then u  (* physical equality test *)
  else map_formula (replace u v) t 

(*     C ∨ s = t    D ∨ u[s'] ≐ v
 *    ────────────────────────────   super (superposition)
 *        (C ∨ D ∨ u[t] ≐ v)σ          σ = mgu(s, s')
 *
 *     (i) tσ ≱ sσ, (ii) vσ ≱ uσ
 *     (iii) (s = t)σ is maximal with respect to Cσ
 *     (iv) (u = v)σ is maximal with respect to Dσ
 *     (v) s' is not a variable
 *     (vi) (s = t)σ ≱ (u = v)σ   (positive superposition only)
 *)

let super c d =
  let+ c, d = [(c, d); (d, c)] in
  let c_lits = map prefix_vars c.lits in
  let+ lit = c_lits in
  match eq_terms lit with
    | (true, s, t) ->
        let+ s, t = [(s, t); (t, s)] in
        let+ lit' = d.lits in
        let (pos, u, v) = eq_terms lit' in
        let+ u, v = [(u, v); (v, u)] in
        let+ s' = filter (Fun.negate is_var) (subterms u) in (  (* v *)
        match unify s s' with
          | None -> []
          | Some sub ->
              let s1, t1 = subst_n sub s, subst_n sub t in
              let s_t = mk_eq s1 t1 in
              if term_gt t1 s1 then [] else  (* i *)
                let u1, v1 = subst_n sub u, subst_n sub v in
                let u_v = mk_eq u1 v1 in
                if term_gt v1 u1 || pos && lit_gt s_t u_v then [] else  (* ii, vi *)
                  let c1 = map (subst_n sub) (remove lit c_lits) in
                  if not (is_maximal lit_gt s_t c1) then [] else  (* iii *)
                    let d1 = map (subst_n sub) (remove lit' d.lits) in
                    if not (is_maximal lit_gt u_v d1) then [] else (* iv *)
                      let uv' = eq_formula pos (replace t s' u) v in
                      let e = c1 @ d1 @ [subst_n sub uv'] in
                      let st = str_replace "\\$" "" (show_formula (Eq (s, t))) in
                      let uv = show_formula (mk_eq' pos u v) in
                      let rule = sprintf "superposition: %s / %s" st uv in
                      [mk_clause rule [c; d] (unprefix_vars e)])
    | _ -> []

(* We judge a clause to be a tautology if the conjunction of its negated
 * literals implies any positive literal via transitivity of equality, e.g.
 *   x ≠ y ∨ y ≠ z ∨ x = z.
 * (A literal t = t is vacuously implied in this way.) *)
let is_tautology lits =
  let neq_pair lit = match eq_terms lit with
    | (true, _, _) -> None
    | (false, f, g) -> Some (f, g) in
  let neq_pairs = filter_map neq_pair lits in
  let neighbors x = neq_pairs |> filter_map
    (fun (f, g) -> if x = f then Some g else if x = g then Some f else None) in
  let is_implied lit = match eq_terms lit with
    | (true, f, g) ->
        let rec search visited = function
          | [] -> false
          | x :: xs -> x = g ||
              let ns = subtract (neighbors x) visited in
              search (ns @ visited) (ns @ xs) in
        search [f] [f]
    | (false, _, _) -> false in
  exists is_implied lits

module FormulaSet = Set.Make(struct
  type t = formula
  let compare = Stdlib.compare
end)

let variants = function
  | Eq (f, g) -> [Eq (f, g); Eq (g, f)]
  | f -> [f]

let dedup lits =
  let rec dedup' seen = function
    | [] -> []
    | (f :: lits) ->
        if variants f |> exists (fun v -> FormulaSet.mem v seen)
          then dedup' seen lits
        else f :: dedup' (FormulaSet.add f seen) lits in
  dedup' FormulaSet.empty lits

let simplify clause =
  if is_tautology clause.lits then None
    else Some { clause with lits = dedup clause.lits }

let rec canonical_formula = function
  | Eq (f, g) ->
      let f, g = canonical_formula f, canonical_formula g in
      if f < g then Eq (f, g) else Eq (g, f)
  | f -> map_formula canonical_formula f

(* approximate: equivalent lits could possibly have different canonical forms *)
let canonical clause =
  let lits = sort Stdlib.compare (map canonical_formula clause.lits) in
  rename_vars (fold_left1 _or lits)

let refute clauses =
  print_newline ();
  let found = FormulaSet.of_list (map canonical clauses) in
  let queue = Queue.of_seq (to_seq clauses) in
  let rec loop found used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some clause ->
          print_clause false "given: " clause;
          let new_clauses = eq_res clause @ concat_map (super clause) used |>
            filter_map simplify in
          let check_clause (found, out) c =
            let f = canonical c in
            if FormulaSet.mem f found then (found, out)
            else (FormulaSet.add f found, c :: out) in
          let (found, new_clauses) = fold_left check_clause (found, []) new_clauses in
          let new_clauses = map number_clause (rev new_clauses) in
          let used = clause :: used in
          print_newline ();
          match find_opt (fun c -> c.lits = []) new_clauses with
            | Some c -> Some c
            | None ->
                queue_add queue new_clauses;
                loop found used
  in loop found []

let to_clause stmt = stmt_formula stmt |> Option.map (fun f ->
  create_clause (stmt_name stmt) [] [f])

let prove known stmt =
  clause_counter := 0;
  let extend_env env stmt =
    match to_clause stmt with
      | Some clause ->
          let env =
            if is_inductive clause then
              { env with inductive = clause :: env.inductive }
            else
              { env with clauses = clause :: env.clauses } in
          print_newline ();
          env
      | None -> env in
  let all_consts = filter_map stmt_const known in
  let initial_env = { clauses = []; inductive = []; consts = all_consts } in
  let env = fold_left extend_env initial_env known in
  let env = { env with clauses = rev env.clauses; inductive = rev env.inductive } in
  let clause = Option.get (to_clause stmt) in
  let f = clause_formula clause in
  let env = match kind f with
    | Quant ("∀", x, typ, f) ->
        let add_inductive env ind = match kind (clause_formula ind) with
          | Quant ("∀", y, Fun(typ', Bool), g) ->
              if typ = typ' then
                let g = reduce (subst1 g (Lambda (x, typ, f)) y) in
                let inst = create_clause "inductive" [ind] [g] in
                { env with clauses = env.clauses @ [inst] }
              else env
          | _ -> failwith "not inductive" in
        fold_left add_inductive env env.inductive
    | _ -> env in
  let negated = create_clause "negate" [clause] [_not (clause_formula clause)] in
  refute (env.clauses @ [negated])

let prove_all prog =
  let rec prove_stmts known = function
    | [] -> print_endline "All theorems were proved."
    | stmt :: rest ->
        if (match stmt with
          | Theorem _ -> (
              match prove known stmt with
                | Some _clause ->
                    printf "proof found!\n";
                    true
                | None -> false)
          | _ -> true) then (
          prove_stmts (known @ [stmt]) rest)
        else print_endline "  Not proved.\n" in
  prove_stmts [] prog
