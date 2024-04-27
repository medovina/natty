open Printf

open List
open Util

type id = string

type typ =
  | Bool
  | Fun of typ * typ
  | Base of id

let rec show_type = function
  | Bool -> "𝔹"
  | Fun (t, u) -> sprintf "(%s → %s)" (show_type t) (show_type u)
  | Base id -> id

let mk_fun_type t u = Fun (t, u)

let mk_base_type = function
  | "𝔹" -> Bool
  | id -> Base id

let unknown_type = Base "?"

let rec arity = function
  | Fun (_, typ) -> 1 + arity typ
  | _ -> 0

type formula =
  | Const of id * typ
  | Var of id * typ
  | App of formula * formula
  | Lambda of id * typ * formula
  | Eq of formula * formula

let _const c = Const (c, unknown_type)
let _var v = Var (v, unknown_type)
let mk_var' (id, typ) = Var (id, typ)
let mk_app f g = App (f, g)
let mk_eq f g = Eq (f, g)

let apply = fold_left1 mk_app

let is_var = function
  | Var _ -> true
  | _ -> false

let is_eq = function
  | Eq _ -> true
  | _ -> false

let is_app_or_const = function
  | App _ | Const _ -> true
  | _ -> false

let map_formula fn = function
  | App (f, g) -> App (fn f, fn g)
  | Lambda (id, typ, f) -> Lambda (id, typ, fn f)
  | Eq (f, g) -> Eq (fn f, fn g)
  | f -> f

let fold_left_formula fn acc = function
  | App (f, g) | Eq (f, g) -> fn (fn acc f) g
  | Lambda (_id, _typ, f) -> fn acc f
  | _ -> acc

let app_or_eq h f g = match h with
  | App _ -> App (f, g)
  | Eq _ -> Eq (f, g)
  | _ -> assert false

let rec type_of = function
  | Const (_, typ) | Var (_, typ) -> typ
  | App (f, _) -> (match type_of f with
      | Fun (_, u) -> u
      | _ -> assert false)
  | Lambda (_, typ, f) -> Fun (typ, type_of f)
  | Eq (_, _) -> Bool

let rec count_binders = function
  | Const _ | Var _ -> 0
  | App (f, g) | Eq (f, g) -> count_binders f + count_binders g
  | Lambda (_, _, f) -> 1 + count_binders f

let _false = Const ("⊥", Bool)
let _true = Const ("⊤", Bool)

let _not f = App (Const ("¬", Fun (Bool, Bool)), f)

let logical_binary = ["∧"; "∨"; "→"]

let binop op typ f g = App (App (Const (op, typ), f), g) 
let binop_unknown op = binop op unknown_type

let logical_op op = binop op (Fun (Bool, Fun (Bool, Bool)))

let _and = logical_op "∧"
let _or = logical_op "∨"
let implies1 = logical_op "→"

let multi_or = function
  | [] -> _false
  | xs -> fold_left1 _or xs

let lambda id typ f = Lambda (id, typ, f)

let quant_type = Fun (Fun (Base "_", Bool), Bool)

let quant q id typ f =
  App (Const (q, quant_type), Lambda (id, typ, f))
  
let quant' q (id, typ) f = quant q id typ f

let _for_all = quant "∀"
let _for_all' = quant' "∀"
let _exists = quant "∃"

let c_for_all = Const("∀", quant_type)
let c_exists = Const("∃", quant_type)

let mk_neq f g = _not (mk_eq f g)
let mk_eq' eq f g = (if eq then mk_eq else mk_neq) f g

type formula_kind =
  | True
  | False
  | Not of formula
  | Binary of id * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let fkind boolean = function
  | Const ("⊤", _) -> True
  | Const ("⊥", _) -> False
  | App (Const ("¬", _), f) -> Not f
  | App (App (Const (op, _), t), u)
      when mem op logical_binary || (not boolean) ->
        Binary (op, t, u)
  | App (Const (q, _), Lambda (id, typ, u)) when q = "∀" || q = "∃" ->
      Quant(q, id, typ, u)
  | f -> Other f

let bool_kind = fkind true
let kind = fkind false

let rec gather_associative op f = match kind f with
  | Binary (op', f, g) when op' = op ->
      gather_associative op f @ gather_associative op g
  | _ -> [f]

let gather_and = gather_associative "∧"

let implies f g = match bool_kind f with
  | Binary ("∧", s, t) -> implies1 s (implies1 t g)
  | _ -> implies1 f g

let rec gather_implies f = match bool_kind f with
  | Binary ("→", f, g) -> f :: gather_implies g
  | _ -> [f]

let premises f = split_last (gather_implies f)

let binary_ops = [("·", 6); ("+", 5); ("-", 5); ("∧", 3); ("∨", 2); ("→", 0)]
let not_prec = 7
let eq_prec = 4
let quantifier_prec = 1

let single_letter = function
  | (Const (id, _) | Var (id, _)) when is_letter id.[0] -> Some id
  | _ -> None

let show_formula_multi multi f =
  let parens b s = if b then sprintf "(%s)" s else s in
  let rec show indent multi outer right f =
    let show1 outer right f = show indent multi outer right f in
    let show_eq eq f g = parens (eq_prec < outer)
      (sprintf "%s %s %s" (show1 eq_prec false f) eq (show1 eq_prec true g)) in
    match kind f with
      | True -> "⊤"
      | False -> "⊥"
      | Not g -> (match g with
        | Eq (t, u) -> show_eq "≠" t u
        | _ -> parens (not_prec < outer) ("¬" ^ show1 not_prec false g))
      | Binary (op, t, u) when mem_assoc op binary_ops ->
          let prec = assoc op binary_ops in
          let p = prec < outer ||
            prec = outer && (op = "·" || op = "+" || op = "→" && not right) in
          let layout multi =
            match single_letter t, single_letter u with
              | Some t, Some u when op = "·" -> t ^ u
              | _ ->
                  sprintf "%s %s %s" (show indent multi prec false t) op
                                     (show indent multi prec true u) in
          let s = if (op = "→" || op = "∧" || op = "∨") && multi then
            let line = layout false in
            if String.length line <= 60 then line
            else
              let fs = (if op = "→" then gather_implies else gather_associative op) f in
              let ss = (show1 prec false (hd fs)) ::
                map (show (indent + 3) multi prec false) (tl fs) in
              String.concat (sprintf "\n%s %s " (n_spaces indent) op) ss
          else layout multi in
          parens p s
      | Quant (q, id, typ, u) ->
          let prefix = sprintf "%s%s:%s." q id (show_type typ) in
          parens (quantifier_prec < outer)
            (prefix ^ show (indent + utf8_len prefix) multi quantifier_prec false u)
      | _ -> match f with
        | Const (id, _typ) -> id
        | Var (id, _typ) -> id
        | App (t, u) ->
            sprintf "%s(%s)" (show1 10 false t) (show1 (-1) false u)
        | Lambda (id, typ, t) ->
            parens (quantifier_prec < outer)
              (sprintf "λ%s:%s.%s" id (show_type typ) (show1 quantifier_prec false t))
        | Eq (t, u) -> show_eq "=" t u in
  show 0 multi (-1) false f

let show_formula = show_formula_multi false
let show_multi = show_formula_multi true

let prefix_show prefix f =
  indent_with_prefix prefix (show_multi f)

let is_ground f =
  let rec has_free outer = function
    | Const _ -> false
    | Var (v, _) -> not (mem v outer)
    | Lambda (x, _, f) -> has_free (x :: outer) f
    | App (t, u) | Eq (t, u) ->
        has_free outer t || has_free outer u in
  not (has_free [] f)

let find_vars_types only_free f =
  let rec find = function
    | Const _ -> []
    | Var (id, typ) -> [(id, typ)]
    | App (t, u) | Eq (t, u) -> find t @ find u
    | Lambda (id, typ, t) ->
        if only_free then remove (id, typ) (find t)
        else (id, typ) :: find t in
  find f

let find_vars only_free f =
  unique (map fst (find_vars_types only_free f))

let all_vars = find_vars false
let free_vars = find_vars true
let free_vars_types = find_vars_types true

let is_free_in x f = mem x (free_vars f)

let is_free_in_any x fs = exists (fun f -> is_free_in x f) fs

let consts f =
  let rec collect = function
    | Const (id, _) -> [id]
    | Var _ -> []
    | App (t, u) | Eq (t, u) -> collect t @ collect u
    | Lambda (_, _, f) -> collect f in
  unique (collect f)

let for_all_vars_typ (ids, typ) f =
  fold_right (fun id f -> _for_all id typ f) ids f

let for_all_vars_typ_if_free (ids, typ) f =
  for_all_vars_typ (intersect ids (free_vars f), typ) f

let for_all_vars_typs = fold_right _for_all'

let rec gather_quant q f = match kind f with
  | Quant (q', id, typ, u) when q = q' ->
      let (qs, f) = gather_quant q u in ((id, typ) :: qs, f)
  | _ -> ([], f)

let for_alls = gather_quant "∀"

let rec remove_universal f = match bool_kind f with
  | Quant ("∀", _x, _typ, g) -> remove_universal g
  | Not g -> (match bool_kind g with
      | Quant ("∃", _x, _typ, h) -> remove_universal (_not h)
      | _ -> f)
  | _ -> f

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id

(* replace [u/v] in t *)
let rec replace_in_formula u v t =
  if t == v then u  (* physical equality test *)
  else map_formula (replace_in_formula u v) t 

(* t[u/x] *)
let rec subst1 t u x = match t with
  | Const _ -> t
  | Var (y, _) -> if x = y then u else t
  | App (f, g) | Eq (f, g) ->
      app_or_eq t (subst1 f u x) (subst1 g u x)
  | Lambda (y, typ, t') -> if x = y then t else
      if not (mem y (free_vars u)) then Lambda (y, typ, subst1 t' u x)
      else let y' = rename y (x :: free_vars t') in
        Lambda (y', typ, subst1 (subst1 t' (Var (y', typ)) y) u x)

let subst_n subst f =
  fold_left (fun f (x, t) -> subst1 f t x) f subst
  
(* β-reduction *)
let rec reduce = function
  | App (f, g) -> (match reduce f, reduce g with
      | Lambda (x, _typ, f), g -> reduce (subst1 f g x)  
      | f, g -> App (f, g))
  | Lambda (id, typ, f) -> Lambda (id, typ, reduce f)
  | Eq (f, g) -> Eq (reduce f, reduce g)
  | f -> f

let rsubst subst f = reduce (subst_n subst f)

let eta = function
  | Lambda (id, typ, App (f, Var (id', typ'))) when id = id' && typ = typ' -> f  
  | f -> f

let unify_or_match is_unify =
  let rec unify' subst t u =
    let unify_pairs f g f' g' =
      let* subst = unify' subst f f' in
      unify' subst g g' in
    match eta t, eta u with
      | Const (c, typ), Const (c', typ') ->
          if c = c' && typ = typ' then Some subst else None
      | Var (x, typ), f ->
          if typ = type_of f then
            match assoc_opt x subst with
              | Some g ->
                  if is_unify then unify' subst f g
                  else if f = g then Some subst else None
              | None ->
                  let f = subst_n subst f in
                  if mem x (free_vars f) then None else
                    let subst = subst |> map (fun (y, g) -> (y, subst1 g f x)) in
                    Some ((x, f) :: subst)
          else None
      | _f, Var (_x, _typ) when is_unify -> unify' subst u t
      | App (f, g), App (f', g') ->
          unify_pairs f g f' g'
      | Eq (f, g), Eq (f', g') -> (
          match unify_pairs f g f' g' with
            | Some subst -> Some subst
            | None -> unify_pairs f g g' f')
      | Lambda (x, xtyp, f), Lambda (y, ytyp, g) ->
          let* subst = unify' subst f g in
          let x', y' = assoc_opt x subst, assoc_opt y subst in
          if (x' = None || x' = Some (Var (y, ytyp))) &&
            (y' = None || y' = Some (Var (x, xtyp)))
          then let subst = remove_assoc x (remove_assoc y subst) in
              let fs = map snd subst in
              if is_free_in_any x fs || is_free_in_any y fs then None
              else Some subst
          else None
      | _, _ -> None
  in unify' []

let unify = unify_or_match true
let try_match = unify_or_match false

let multi_eq f =
  let rec collect = function
    | Eq (f, g) -> f :: collect g
    | f -> [f] in
  let rec join = function
    | [x; y] -> mk_eq x y
    | x :: y :: xs -> _and (mk_eq x y) (join (y :: xs))
    | _ -> assert false in
  match collect f with
    | [] -> assert false
    | [f] -> f
    | fs -> join fs

let outer_eq f =
  let fs = gather_and f in
  assert (for_all is_eq fs);
  match hd fs, last fs with
    | Eq (a, _), Eq(_, b) -> Eq(a, b)
    | _ -> failwith "outer_eq"

let next_var x avoid =
  let rec next x =
    if mem x avoid then
      let wrap c = sprintf "%c'" c in  (* add prime mark *)
      let t = match x.[0] with
        | 'o' -> wrap 'a'  (* constants a .. o *)
        | 'z' -> wrap 'q'  (* variables q .. z *)
        | _ -> char_to_string (Char.chr (Char.code x.[0] + 1)) in
      next (t ^ string_from x 1)
    else x in
  next x

let first_var start_var = function
  | Fun (_, Bool) -> "P"
  | _ -> start_var

(* Alpha-equivalent formulas should have the same form after renaming.
 * We choose a new name for each variable as soon as we encounter it in
 * the formula structure.  Note that free_vars returns variable names in
 * alphabetical order.  We can't use this order for choosing new names since it
 * may not be isomorphic across equivalent formulas. *)
let rename_vars f =
  let num_vars = count_binders f + length (free_vars f) in
  let start_var = char_to_string (
    if num_vars <= 3 then 'x' else
      let c = Char.chr (Char.code 'z' - num_vars + 1) in
      if c < 'q' then 'q' else c) in
  let rec rename name_map used h =
    let next typ = next_var (first_var start_var typ) used in
    match h with
      | Const (id, typ) -> (Const (id, typ), name_map, used)
      | Var (id, typ) -> (
          match assoc_opt id name_map with
            | Some name -> (Var (name, typ), name_map, used)
            | None -> 
                let x = next typ in (Var (x, typ), (id, x) :: name_map, x :: used))
      | App (f, g) | Eq (f, g) ->
          let (f, name_map, used) = rename name_map used f in
          let (g, name_map, used) = rename name_map used g in
          (app_or_eq h f g, name_map, used)
      | Lambda (id, typ, f) ->
          let x = next typ in
          let (f, name_map, used) = rename ((id, x) :: name_map) (x :: used) f in
          (Lambda (x, typ, f), remove_assoc id name_map, used) in
  let (f, _map, _used) = rename [] [] f in
  f

let collect_args t =
  let rec collect = function
    | App (f, g) ->
        let (head, args) = collect f in
        (head, g :: args)
    | head -> (head, []) in
  let (head, args) = collect t in
  (head, rev args)
