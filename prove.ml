open List
open Logic
open Printf
open Util

type clause = formula list

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

let rec all_consts f =
  let gather acc = function
    | Const (id, _typ) -> id :: acc
    | f -> fold_left_formula all_consts acc f in
  gather [] f 

let clausify f =
  let (_, f) = skolemize [] (all_consts f) (nnf f) in
  to_cnf (remove_universal (rename_vars f))

let clause_to_formula = fold_left1 _or

let clauses_to_formula cs = fold_left1 _and (map clause_to_formula cs)

let to_equation = function
  | Eq (f, g) -> (true, f, g)
  | App (Const ("¬", _), Eq (f, g)) -> (false, f, g)
  | App (Const ("¬", _), f) -> (false, f, mk_true)
  | f -> (true, f, mk_true)

let prove _known f =
  printf "%s\n" (show_multi f);
  printf "%s\n" (show_multi (clauses_to_formula (clausify f)));
  print_endline "Not proved.\n"

let prove_all prog =
  let rec loop known = function
    | [] -> print_endline "No theorems were proved."
    | stmt :: rest -> match stmt with
        | Axiom (_, f, _) | Definition (_, _, f) ->
            loop (f :: known) rest
        | Theorem (_, f, _) ->
            prove known f;
            loop (f :: known) rest
        | _ -> loop known rest in
  loop [] prog
