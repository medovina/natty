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
  
let terms = function
  | Eq (f, g) -> (true, f, g)
  | App (Const ("¬", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("¬", _), f) -> (true, f, _false)
  | f -> (true, f, _true)

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

(*      D' ∨ t = t'    C⟨u⟩
 *    ──────────────────────   sup
 *       (D' ∨ C⟨t'⟩)σ           σ ∈ csu(t, u)
 *
 *     (i) u is not fluid
 *     (ii) u is not a variable
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
              let c' = replace t' u c in
              let e = subst_n sub (fold_left1 _or (d' @ [c'])) in
              [mk_pformula "superposition" [dp; cp] (unprefix_vars e)])

let clausify pformula rule =
  let rec run lits =
    let split f = match bool_kind f with
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
          match split lit with
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
          let new_pformulas = concat_map (all_super pformula) used in
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
