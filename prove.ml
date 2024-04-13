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
  formula: formula
}

let print_formula with_origin prefix pformula =
  let prefix = prefix ^ sprintf "%d. " (pformula.id) in
  let origin =
    if with_origin then sprintf " [%s]" (comma_join
      ((pformula.parents |> map (fun p -> string_of_int (p.id))) @ [pformula.rule]))
    else "" in
  printf "%s%s\n"
    (indent_with_prefix prefix (show_multi pformula.formula)) origin

let mk_pformula rule parents formula =
  { id = 0; rule; parents; formula }

let number_formula clause =
  incr formula_counter;
  let clause = { clause with id = !formula_counter } in
  print_formula true "" clause;
  clause

let create_pformula rule parents formula =
  number_formula (mk_pformula rule parents formula)

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
let rec replace u v t =
  if t == v then u  (* physical equality test *)
  else map_formula (replace u v) t 

(*      D:[D' ∨ t = t']    C⟨u⟩
 *    ───────────────────────────   sup
 *          (D' ∨ C⟨t'⟩)σ             σ ∈ csu(t, u)
 *
 *     (i) u is not fluid
 *     (ii) u is not a variable
 *     (iii) t = t' is maximal in D w.r.t. σ
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
              let d1 = map (rsubst sub) d' in
              let tt1 = rsubst sub (Eq (t, t')) in
              if not (is_maximal lit_gt tt1 d1) then [] else  (* iii *)
                let c' = replace t' u c in
                let e = fold_left1 _or (d1 @ [rsubst sub c']) in
                let tt'_show = show_formula (Eq (t, t')) in
                let u_show = str_replace "\\$" "" (show_formula u) in
                let rule = sprintf "sup: %s / %s" tt'_show u_show in
                [mk_pformula rule [dp; cp] (unprefix_vars e)])

let split f = match bool_kind f with
  | Binary ("∨", s, t) -> Some (s, t)
  | Binary ("→", s, t) -> Some (_not s, t)
  | _ -> None

let rec expand f = match split f with
  | Some (s, t) -> expand s @ expand t
  | None -> [f]

let is_tautology pf = mem _true (expand pf.formula)

let clausify pformula rule =
  let rec run lits =
    let clauses f = match split f with
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
        | _ -> None in
    let rec loop before = function
      | [] -> []
      | lit :: after ->
          match clauses lit with
            | Some fs ->
                let lits = rev before @ fs @ after in
                let new_pformulas =
                  let+ f = fs in
                  rule pformula (remove f lits) f in
                new_pformulas @ run lits
            | None -> loop (lit :: before) after in
    loop [] lits in
  rule pformula [] pformula.formula @ run [pformula.formula]

let all_super cp dp = clausify cp (super dp) @ clausify dp (super cp)

let refute pformulas =
  print_newline ();
  let queue = Queue.of_seq (to_seq pformulas) in
  let rec loop used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some pformula ->
          print_formula false "given: " pformula;
          let new_pformulas = concat_map (all_super pformula) used |>
            filter (Fun.negate is_tautology) in
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
  create_pformula (stmt_name stmt) [] f)

let prove known_stmts stmt =
  formula_counter := 0;
  let known = known_stmts |> filter_map (fun s ->
    match to_pformula s with
      | Some p -> print_newline(); Some p
      | None -> None) in
  let pformula = Option.get (to_pformula stmt) in
  let negated = create_pformula "negate" [pformula] (_not pformula.formula) in
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
