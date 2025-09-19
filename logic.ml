open Printf

open Util

type id = string

type typ =
  | Bool
  | Fun of typ * typ
  | Base of id
  | Product of typ * typ

let show_type t =
  let rec show outer left typ =
    let op prec sym t u =
      parens_if (outer > prec || outer = prec && left) @@
      sprintf "%s %s %s" (show prec true t) sym (show prec false u) in
    match typ with
      | Bool -> "𝔹"
      | Fun (t, u) -> op 0 "→" t u
      | Base id -> id
      | Product (t, u) -> op 1 "⨯" t u in
  show (-1) false t

let mk_fun_type t u = Fun (t, u)

let rec target_type = function
  | Fun (_, u) -> target_type u
  | t -> t

let mk_base_type = function
  | "𝔹" -> Bool
  | id -> Base id

let unknown_type = Base "?"
let unknown_type_n n = Base (sprintf "?%d" n)

let is_unknown = function
  | Base id -> id.[0] = '?'
  | _ -> false

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

let apply : formula list -> formula = fold_left1 mk_app

let _tuple2 = Const ("(,)", unknown_type)

let tuple2 f g = App (App (_tuple2, f), g)

let tuple_apply f = function
  | [g] -> App (f, g)
  | [g; h] ->  App (f, tuple2 g h)
  | _ -> failwith "tuple_apply"

let is_var = function
  | Var _ -> true
  | _ -> false

let is_lambda = function
  | Lambda _ -> true
  | _ -> false

let is_eq = function
  | Eq _ -> true
  | _ -> false

let is_app_or_const = function
  | App _ | Const _ -> true
  | _ -> false

let app_or_eq h f g = match h with
  | App _ -> App (f, g)
  | Eq _ -> Eq (f, g)
  | _ -> assert false

let map_formula fn = function
  | App (f, g) -> App (fn f, fn g)
  | Lambda (id, typ, f) -> Lambda (id, typ, fn f)
  | Eq (f, g) -> Eq (fn f, fn g)
  | f -> f

let fold_left_formula fn acc = function
  | App (f, g) | Eq (f, g) -> fn (fn acc f) g
  | Lambda (_id, _typ, f) -> fn acc f
  | _ -> acc

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

let is_bool_const x = x = _true || x = _false

let _not f = App (Const ("¬", Fun (Bool, Bool)), f)

let logical_binary = ["∧"; "∨"; "→"; "↔"]

let logical_ops = ["⊥"; "⊤"; "¬"; "∀"; "∃"] @ logical_binary

let binop op typ f g = App (App (Const (op, typ), f), g) 
let binop_unknown op = binop op unknown_type

let logical_op_type = Fun (Bool, Fun (Bool, Bool))
let logical_op op = binop op logical_op_type

let _and = logical_op "∧"
let _or = logical_op "∨"
let implies1 = logical_op "→"
let _iff = logical_op "↔"

let multi_and = function
  | [] -> _true
  | xs -> fold_left1 _and xs

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

let c_and = Const("∧", logical_op_type)
let c_for_all = Const("∀", quant_type)
let c_exists = Const("∃", quant_type)

let mk_neq f g = _not (mk_eq f g)
let mk_eq' eq f g = (if eq then mk_eq else mk_neq) f g

type formula_kind =
  | True
  | False
  | Not of formula
  | Binary of id * typ * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let fkind boolean = function
  | Const ("⊤", _) -> True
  | Const ("⊥", _) -> False
  | App (Const ("¬", _), f) -> Not f
  | App (App (Const (op, typ), t), u)
      when mem op logical_binary || (not boolean) ->
        Binary (op, typ, t, u)
  | App (Const (q, _), Lambda (id, typ, u)) when q = "∀" || q = "∃" ->
      Quant(q, id, typ, u)
  | Eq (f, g) when boolean && type_of f = Bool -> (
      assert (type_of g = Bool);
      Binary ("↔", logical_op_type, f, g))   (* via boolean extensionality *)
  | f -> Other f

let bool_kind = fkind true
let kind = fkind false

let negate f = match bool_kind f with
  | Not f -> f
  | _ -> _not f

let rec gather_associative op f = match kind f with
  | Binary (op', _, f, g) when op' = op ->
      gather_associative op f @ gather_associative op g
  | _ -> [f]

let gather_and = gather_associative "∧"
let gather_or = gather_associative "∨"

let implies f g = fold_right implies1 (gather_and f) g

let rec gather_implies f = match bool_kind f with
  | Binary ("→", _, f, g) -> f :: gather_implies g
  | _ -> [f]

let premises f = split_last (gather_implies f)

let binary_ops = [
  ("·", 8);
  ("+", 7); ("-", 7);
  ("∈", 6); ("|", 6); ("~", 6);
  ("<", 5); ("≤", 5); (">", 5); ("≥", 5);
  ("∧", 4); ("∨", 3); ("→", 1); ("↔", 0)
]

let not_prec = 9
let eq_prec = 5
let quantifier_prec = 2

let single_letter = function
  | (Const (id, _) | Var (id, _)) when is_letter id.[0] -> Some id
  | _ -> None

let split_type_suffix id =
  match String.index_opt id ':' with
    | Some i -> (String.sub id 0 i, string_from id i)
    | None -> (id, "")

let without_type_suffix id = fst (split_type_suffix id)

let show_formula_multi multi f =
  let rec show indent multi outer right f =
    let show1 outer right f = show indent multi outer right f in
    let show_eq eq f g = parens_if (eq_prec < outer)
      (sprintf "%s %s %s" (show1 eq_prec false f) eq (show1 eq_prec true g)) in
    match kind f with
      | True -> "⊤"
      | False -> "⊥"
      | Not g -> (match g with
        | Eq (t, u) -> show_eq "≠" t u
        | _ -> parens_if (not_prec < outer) ("¬" ^ show1 not_prec false g))
      | Binary (op, _, t, u) when mem_assoc (without_type_suffix op) binary_ops ->
          let op = without_type_suffix op in
          let prec = assoc op binary_ops in
          let p = prec < outer ||
            prec = outer && (op = "·" || op = "+" || op = "→" && not right) in
          let layout multi =
            match single_letter t, single_letter u with
              | Some t, Some u when op = "·" && strlen t = 1 && strlen u = 1
                  -> t ^ u
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
          parens_if p s
      | Quant (q, id, typ, u) ->
          let prefix = sprintf "%s%s:%s." q id (show_type typ) in
          parens_if (quantifier_prec < outer)
            (prefix ^ show (indent + utf8_len prefix) multi quantifier_prec false u)
      | _ -> match f with
        | Const (id, _typ) -> without_type_suffix id
        | Var (id, _typ) -> id
        | App (App (Const (id, _), f), g) when starts_with "(,)" id ->
            parens_if (outer > -2) @@
              sprintf "%s, %s" (show1 (-1) false f) (show1 (-1) false g)
        | App (t, u) ->
            sprintf "%s(%s)" (show1 10 false t) (show1 (-2) false u)
        | Lambda (id, typ, t) ->
            parens_if (quantifier_prec < outer)
              (sprintf "λ%s:%s.%s" id (show_type typ) (show1 quantifier_prec false t))
        | Eq (t, u) -> show_eq "=" t u in
  show 0 multi (-1) false f

let show_formula = show_formula_multi false
let show_formulas fs =
  sprintf "[%s]" (comma_join (map show_formula fs))
  
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

let all_consts f =
  let rec find = function
    | Const (id, _typ) -> [id]
    | Var _ -> []
    | App (t, u) | Eq (t, u) -> find t @ find u
    | Lambda (id, _typ, t) -> remove id (find t)
  in unique (find f)

let find_vars_types only_free f =
  let rec find = function
    | Const _ -> []
    | Var (id, typ) -> [(id, typ)]
    | App (t, u) | Eq (t, u) -> find t @ find u
    | Lambda (id, typ, t) ->
        if only_free then
          filter (fun (x, _typ) -> x <> id) (find t)
        else (id, typ) :: find t in
  find f

let find_vars only_free f =
  unique (map fst (find_vars_types only_free f))

let all_vars = find_vars false
let free_vars = find_vars true
let free_vars_types f = unique (find_vars_types true f)

let is_var_in v =
  let rec find_var = function
    | Const _ -> false
    | Var (x, _) -> x = v
    | App (f, g) | Eq (f, g) -> find_var f || find_var g
    | Lambda (x, _typ, f) -> x = v || find_var f
  in find_var

let is_free_in x f = mem x (free_vars f)
let any_free_in xs f = overlap xs (free_vars f)

let is_free_in_any x fs = exists (fun f -> is_free_in x f) fs

let quant_vars_typ quant (ids, typ) f =
  fold_right (fun id f -> quant id typ f) ids f

let for_all_vars_typ : (id list * typ) -> formula -> formula =
  quant_vars_typ _for_all
let exists_vars_typ : (id list * typ) -> formula -> formula =
  quant_vars_typ _exists

let for_all_vars_typs : (id * typ) list -> formula -> formula =
  fold_right _for_all'

let for_all_vars_typs_if_free ids_typs f : formula =
  let fv = free_vars f in
  for_all_vars_typs (ids_typs |> filter (fun (id, _typ) -> mem id fv)) f

  (* for_all_vars_typ (intersect ids (free_vars f), typ) f *)

let rec gather_quant q f : (id * typ) list * formula = match kind f with
  | Quant (q', id, typ, u) when q = q' ->
      let (qs, f) = gather_quant q u in ((id, typ) :: qs, f)
  | _ -> ([], f)

let rec gather_quant_of_type q typ f = match kind f with
  | Quant (q', id, typ', u) when q = q' && typ = typ' ->
      let (qs, f) = gather_quant_of_type q typ u in (id :: qs, f)
  | _ -> ([], f)

let rec gather_lambdas = function
  | Lambda (x, typ, f) ->
      let (vars, g) = gather_lambdas f in
      ((x, typ) :: vars, g)
  | f -> ([], f)

let remove_quants with_existential =
  let rec remove f = match bool_kind f with
    | Quant ("∀", _x, _typ, g) -> remove g
    | Quant ("∃", x, _typ, g) when with_existential ->
        let (f, ex) = remove g in
        (f, x :: ex)
    | Not g -> (match bool_kind g with
        | Quant ("∀", x, _typ, h) when with_existential ->
            let (f, ex) = remove (_not h) in
            (f, x :: ex)
        | Quant ("∃", _x, _typ, h) -> remove (_not h)
        | _ -> (f, []))
    | _ -> (f, []) in
  remove

let remove_universal f = fst (remove_quants false f)
let remove_quantifiers f = fst (remove_quants true f)

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id

let suffix id avoid =
  let rec try_suffix n =
    let id' = sprintf "%s_%d" id n in
    if mem id' avoid then try_suffix (n + 1) else id' in
  if mem id avoid then try_suffix 1 else id

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

type subst = (id * formula) list

let subst_n subst f =
  fold_left (fun f (x, t) -> subst1 f t x) f subst
  
(* β-reduction *)
let rec b_reduce = function
  | App (f, g) -> (match b_reduce f, b_reduce g with
      | Lambda (x, _typ, f), g -> b_reduce (subst1 f g x)  
      | f, g -> App (f, g))
  | Lambda (id, typ, f) -> Lambda (id, typ, b_reduce f)
  | Eq (f, g) -> Eq (b_reduce f, b_reduce g)
  | f -> f

let rsubst1 t u x = b_reduce (subst1 t u x)
let rsubst subst f = b_reduce (subst_n subst f)

let eta = function
  | Lambda (id, typ, App (f, Var (id', typ'))) when id = id' && typ = typ' -> f  
  | f -> f

(* t and u unify if tσ = uσ for some substitution σ.
   t matches u if tσ = u for some substitution σ.   *)
let unify_or_match is_unify subst t u : subst option =
  let rec unify' subst t u =
    let unify_pairs f g f' g' =
      let* subst = unify' subst f f' in
      unify' subst g g' in
    match eta t, eta u with
      | Const (c, typ), Const (c', typ') ->
          if c = c' && typ = typ' then Some subst else None
      | Var (x, typ), f ->
          if f = Var (x, typ) then Some subst
          else if typ = type_of f || typ = unknown_type then
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
  in unify' subst t u

let unify = unify_or_match true []
let _match = unify_or_match false []
let try_match = unify_or_match false

let rec chain_ops (f, ops_exprs) = match ops_exprs with
  | [] -> f
  | [(op, g)] -> op f g
  | (op, g) :: ops_exprs -> _and (op f g) (chain_ops (g, ops_exprs))

let expand_multi_eq f : (formula list * formula) option =
  let rec expand = function
    | [] -> Some []
    | Eq (_, g) as eq :: rest -> (
        match expand rest with
          | Some [] -> Some [eq]
          | Some ((Eq (g', _) :: _) as eqs) when g = g' ->
              Some (eq :: eqs)
          | _ -> None)
    | _ -> None in
  match expand (gather_and f) with
    | Some eqs ->
        let concl = if length eqs <= 2 then multi_and eqs else
          match hd eqs, last eqs with
            | Eq (a, _), Eq (_, b) -> Eq (a, b)
            | _ -> assert false in
        Some (eqs, concl)
    | None -> None

let next_var x avoid =
  let rec next x =
    if mem x avoid || mem (x ^ "0") avoid then
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

let looks_like_var id = 'q' <= id.[0] && id.[0] <= 'z'

(* Alpha-equivalent formulas should have the same form after renaming.
 * We choose a new name for each variable as soon as we encounter it in
 * the formula structure.  Note that free_vars returns variable names in
 * alphabetical order.  We can't use this order for choosing new names since it
 * may not be isomorphic across equivalent formulas. *)
let rename_vars f =
  let consts = all_consts f in
  let free = free_vars f in
  let num_vars = count_binders f + length free +
    length (filter looks_like_var consts) in
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
  let (f, _map, _used) = rename [] (consts @ free) f in
  f

let collect_args t =
  let rec collect = function
    | App (f, g) ->
        let (head, args) = collect f in
        (head, g :: args)
    | head -> (head, []) in
  let (head, args) = collect t in
  (head, rev args)
