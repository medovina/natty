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
  incr clause_counter;
  let clause = { id = !clause_counter; rule; parents; lits } in
  print_clause true "" clause;
  clause

let clause_formula clause =
  assert (length clause.lits = 1);
  hd (clause.lits)

let rec nnf fm = match bool_kind fm with
  | Not f -> (match bool_kind f with
    | Not f -> nnf f
    | Binary ("∧", f, g) -> _or (nnf (_not f)) (nnf (_not g))
    | Binary ("∨", f, g) -> _and (nnf (_not f)) (nnf (_not g))
    | Binary ("→", f, g) -> _and (nnf f) (nnf (_not g))
    | Quant ("∀", x, typ, f) -> _exists x typ (nnf (_not f))
    | Quant ("∃", x, typ, f) -> _for_all x typ (nnf (_not f))
    | _ -> fm)
  | Binary ("→", f, g) -> _or (nnf (_not f)) (nnf g)
  | Binary (op, f, g) -> logical_op op (nnf f) (nnf g)
  | Quant (q, x, typ, f) -> binder q x typ (nnf f)
  | _ -> fm

let rec skolemize outer_vars consts f = match bool_kind f with
  | Binary (op, f, g) ->
      let (consts, f) = skolemize outer_vars consts f in
      let (consts, g) = skolemize outer_vars consts g in
      (consts, logical_op op f g)
  | Quant ("∀", x, typ, f) ->
      let (consts, f) = skolemize ((x, typ) :: outer_vars) consts f in
      (consts, _for_all x typ f)
  | Quant ("∃", x, typ, f) ->
      let c = next_var "c" consts in
      let outer = rev outer_vars in
      let outer_types = map snd outer in
      let c_type = fold_right1 mk_fun_type (outer_types @ [typ]) in
      let d = apply (Const (c, c_type) :: map mk_var' outer) in
      skolemize outer_vars (c :: consts) (subst1 f d x)
  | _ -> (consts, f)

(* If f is in NNF and all variable names are unique, we can simply
 * remove universal quantifiers. *)
let rec remove_universal f = match bool_kind f with
  | Binary (op, f, g) when mem op logical_binary ->
      logical_op op (remove_universal f) (remove_universal g)
  | Quant ("∀", _, _, f) -> remove_universal f
  | _ -> f

let rec to_cnf f = match bool_kind f with
  | Binary ("∧", f, g) -> to_cnf f @ to_cnf g
  | Binary ("∨", f, g) ->
      let+ x = to_cnf f in
      let+ y = to_cnf g in
      [x @ y]
  | _ -> [[f]]

let clausify consts clause =
  let (consts, f) = skolemize [] consts (nnf (clause_formula clause)) in
  let f = remove_universal (rename_vars f) in
  let clauses = map (fun lits -> mk_clause "clausify" [clause] lits) (to_cnf f) in
  (consts, clauses)

let is_inductive clause = match kind (clause_formula clause) with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false

type env = {
  clauses: clause list;
  inductive: clause list;
  consts: id list
}

let empty_env = { clauses = []; inductive = []; consts = [] }

let const_gt f g =
  match f, g with
    | Const (f, f_type), Const (g, g_type) ->
       (arity f_type, f) > (arity g_type, g)
    | _ -> failwith "const_gt"

let rec lpo_gt s t =
  let rec list_gt ss ts = match ss, ts with
    | [], [] -> false
    | s :: ss, t :: ts ->
      lpo_gt s t || s = t && list_gt ss ts
    | _ -> failwith "list_gt" in
  match s, t with
    | s, Var (x, _) -> mem x (free_vars s) && s <> t
    | Var _, _ -> false
    | _ -> let (f, ss), (g, ts) = collect_args s, collect_args t in
        exists (fun s_i -> s_i = t || lpo_gt s_i t) ss ||
        for_all (fun t_j -> lpo_gt s t_j) ts &&
          (const_gt f g || f = g && list_gt ss ts)

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
  multi_gt (multi_gt lpo_gt) (lit_to_multi f) (lit_to_multi g)

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
              if lpo_gt t1 s1 then [] else  (* i *)
                let u1, v1 = subst_n sub u, subst_n sub v in
                let u_v = mk_eq u1 v1 in
                if lpo_gt v1 u1 || pos && lit_gt s_t u_v then [] else  (* ii, vi *)
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

let refute clauses =
  print_newline ();
  let queue = Queue.of_seq (to_seq clauses) in
  let rec loop used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some clause ->
          print_clause false "given: " clause;
          let new_clauses = eq_res clause @ concat_map (super clause) used in
          let used = clause :: used in
          print_newline ();
          match find_opt (fun c -> c.lits = []) new_clauses with
            | Some c -> Some c
            | None ->
                queue_add queue new_clauses;
                loop used
  in loop []

let to_clause stmt = stmt_formula stmt |> Option.map (fun f ->
  mk_clause (stmt_name stmt) [] [f])

let prove env stmt =
  let clause = Option.get (to_clause stmt) in
  let f = clause_formula clause in
  let env = match kind f with
    | Quant ("∀", x, typ, f) ->
        let add_inductive env ind = match kind (clause_formula ind) with
          | Quant ("∀", y, Fun(typ', Bool), g) ->
              if typ = typ' then
                let g = reduce (subst1 g (Lambda (x, typ, f)) y) in
                let inst = mk_clause "inst" [ind] [g] in
                let (consts, g_clauses) = clausify env.consts inst in
                { env with clauses = g_clauses @ env.clauses; consts }
              else env
          | _ -> failwith "not inductive" in
        fold_left add_inductive env env.inductive
    | _ -> env in
  let negated = mk_clause "negate" [clause] [_not (clause_formula clause)] in
  let (_, f_clauses) = clausify env.consts negated in
  refute (f_clauses @ env.clauses)

let prove_all prog =
  let rec prove_stmts env = function
    | [] -> print_endline "All theorems were proved."
    | stmt :: rest ->
        if (match stmt with
          | Theorem _ -> (
              match prove env stmt with
                | Some _clause ->
                    printf "proof found!\n";
                    true
                | None -> false)
          | _ -> true) then
          let add_known env clause =
            if is_inductive clause then
              { env with inductive = clause :: env.inductive }
            else
              let (consts, f_clauses) = clausify env.consts clause in
              { env with clauses = f_clauses @ env.clauses; consts } in
          let env = opt_fold add_known env (to_clause stmt) in
          print_newline ();
          let env = { env with consts = Option.to_list (stmt_const stmt) @ env.consts } in
          prove_stmts env rest
        else print_endline "  Not proved.\n" in
  prove_stmts empty_env prog
