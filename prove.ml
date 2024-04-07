open List
open Printf

open Logic
open Statement
open Util

type clause = {
  rule: string;
  parents: clause list;
  lits: formula list
}

let mk_clause rule parents lits = { rule; parents; lits }

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
  let clauses = match to_cnf f with
    | [lits] -> [mk_clause "clausify" [clause] lits]
    | cnf ->
        let c = mk_clause "clausify" [clause] [f]
        in map (mk_clause "split" [c]) cnf in
  (consts, clauses)

let clause_to_formula clause = fold_left1 _or clause.lits

let clauses_to_formula cs = fold_left1 _and (map clause_to_formula cs)

let is_inductive clause = match kind (clause_formula clause) with
  | Quant ("∀", _, Fun (_, Bool), _) -> true
  | _ -> false

type env = {
  clauses: clause list;
  inductive: clause list;
  consts: id list
}

let empty_env = { clauses = []; inductive = []; consts = [] }

let rec lpo_gt s t =
  let rec list_gt ss ts = match ss, ts with
    | [], [] -> false
    | s :: ss, t :: ts -> lpo_gt s t && list_gt ss ts
    | _ -> failwith "list_gt" in
  match s, t with
    | s, Var (x, _) -> mem x (free_vars s) && s <> t
    | Var _, _ -> false
    | _ -> let (f, ss), (g, ts) = collect s, collect t in
        exists (fun u -> lpo_gt u t) ss ||
        for_all (fun u -> lpo_gt s u) ts &&
          (f > g || list_gt ss ts)

let eq_terms = function
  | Eq (f, g) -> (true, f, g)
  | App (Const ("¬", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("¬", _), f) -> (false, f, mk_true)
  | f -> (true, f, mk_true)

let eq_formula eq f g = match eq, f, g with
  | true, f, Const ("⊤", _) -> f
  | false, f, Const ("⊤", _) -> _not f
  | true, Const ("⊤", _), f -> f
  | false, Const ("⊤", _), f -> _not f
  | true, f, g -> Eq (f, g)
  | false, f, g -> mk_neq f g

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
 *     s' is not a variable *)

let super c d =
  let+ c, d = [(c, d); (d, c)] in
  let+ lit = c.lits in
  match eq_terms lit with
    | (true, s, t) ->
        let+ s, t = [(s, t); (t, s)] in
        let+ lit' = remove lit d.lits in
        let (eq, u, v) = eq_terms lit' in
        let+ u, v = [(u, v); (v, u)] in
        let+ s' = filter (Fun.negate is_var) (subterms u) in (
        match unify s s' with
          | None -> []
          | Some sub ->
              let uv' = eq_formula eq (replace t s' u) v in
              let e = map (subst_n sub) (
                remove lit c.lits @ remove lit' d.lits @ [uv']) in
              [mk_clause "super" [c; d] e])
    | _ -> []

let refute clauses =
  let queue = Queue.of_seq (to_seq clauses) in
  let rec loop used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some clause ->
          printf "%s\n" (indent_with_prefix "given: " (show_multi (clause_to_formula clause)));
          let used = clause :: used in
          let new_clauses = eq_res clause @ concat_map (super clause) used in
          new_clauses |> iter (fun c ->
            printf "%s\n" (show_multi (clause_to_formula c)));
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
                printf "\n  inductive instantiation:\n";
                printf "%s\n" (indent_lines 2 (show_multi g));
                let inst = mk_clause "inst" [ind] [g] in
                let (consts, g_clauses) = clausify env.consts inst in
                printf "%s\n\n" (indent_lines 2 (show_multi (clauses_to_formula g_clauses)));
                { env with clauses = g_clauses @ env.clauses; consts }
              else env
          | _ -> failwith "not inductive" in
        fold_left add_inductive env env.inductive
    | _ -> env in
  let negated = mk_clause "negate" [clause] [_not (clause_formula clause)] in
  let (_, f_clauses) = clausify env.consts negated in
  printf "  %s\n" (show_multi (clauses_to_formula f_clauses));
  refute (f_clauses @ env.clauses)

let prove_all prog =
  let rec prove_stmts env = function
    | [] -> print_endline "All theorems were proved."
    | stmt :: rest ->
        printf "%s\n" (show_statement true stmt);
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
              printf "  %s\n" (show_multi (clauses_to_formula f_clauses));
              { env with clauses = f_clauses @ env.clauses; consts } in
          let env = opt_fold add_known env (to_clause stmt) in
          print_newline ();
          let env = { env with consts = Option.to_list (stmt_const stmt) @ env.consts } in
          prove_stmts env rest
        else print_endline "  Not proved.\n" in
  prove_stmts empty_env prog
