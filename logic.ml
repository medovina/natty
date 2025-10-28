open Printf

open Util

type id = string

type typ =
  | Bool
  | Type
  | Base of id
  | TypeVar of id
  | Fun of typ * typ
  | Pi of id * typ
  | Product of typ list

let mk_base_type = function
  | "𝔹" -> Bool
  | id -> Base id

let mk_type_var x = TypeVar x
let mk_fun_type t u = Fun (t, u)
let mk_pi_type x t = Pi (x, t)
let mk_product_type ts = Product ts

let show_type t =
  let rec show outer left typ : string =
    let op prec sym t u =
      parens_if (outer > prec || outer = prec && left) @@
      sprintf "%s %s %s" (show prec true t) sym (show prec false u) in
    match typ with
      | Bool -> "𝔹"
      | Type -> "*"
      | Base id -> id
      | TypeVar id -> id
      | Fun (t, u) -> op 1 "→" t u
      | Pi (id, t) ->
          parens_if (0 < outer) (sprintf "Π%s.%s" id (show 0 false t))
      | Product typs ->
          parens_if (outer >= 2) @@
          String.concat " ⨯ " (map (show 2 true) typs) in
  show (-1) false t

let rec target_type = function
  | Fun (_, u) -> target_type u
  | t -> t

let unknown_type = Base "?"
let unknown_type_n n = Base (sprintf "?%d" n)

let is_unknown = function
  | Base id -> id.[0] = '?'
  | _ -> false

let rec arity = function
  | Fun (_, typ) -> 1 + arity typ
  | _ -> 0

let rec collect_arg_types = function
  | Fun (t, u) -> t :: collect_arg_types u
  | _ -> []

let map_type fn = function
  | Fun (t, u) -> Fun (fn t, fn u)
  | Pi (id, t) -> Pi (id, fn t)
  | Product typs -> Product (map fn typs)
  | t -> t

let prefix_var var = "$" ^ var

let is_prefixed var = var.[0] = '$'

let rec prefix_type_vars t : typ = match t with
  | TypeVar id -> TypeVar (prefix_var id)
  | t -> map_type prefix_type_vars t

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
let lambda id typ f = Lambda (id, typ, f)
let lambda' (id, typ) f = Lambda (id, typ, f)
let mk_eq f g = Eq (f, g)

(* Const ("_type", τ) is the type τ itself. *)
let _type = "_type"

let apply formulas : formula = fold_left1 mk_app formulas

let tuple_cons n = sprintf "(%s)" (String.make (n - 1) ',')

let tuple_cons_type typs : typ = fold_right mk_fun_type typs (Product typs)

let _tuple n : formula =
  (* Build a type such as Πσ.Πτ.σ → τ → σ ⨯ τ. *)
  let sigma = Uchar.to_int (uchar "σ") in
  let ids = List.init n (fun i -> uchar_to_string (Uchar.of_int (sigma + i))) in
  let typ = fold_right mk_pi_type (ids) (tuple_cons_type (map mk_type_var ids)) in
  Const (tuple_cons n, typ)

let is_tuple_constructor = starts_with "(,"

let tuple_arity s : int =
  let s = match String.index_from_opt s 0 ')' with  (* remove type suffix if present *)
    | Some i -> String.sub s 0 (i + 1)
    | None -> s in
  assert (is_tuple_constructor s);
  assert (ends_with ",)" s);
  strlen s - 1

let mk_tuple = function
  | [] -> failwith "mk_tuple" 
  | [g] -> g
  | vals -> apply (_tuple (length vals) :: vals)

let is_const = function
  | Const _ -> true
  | _ -> false

let const_type id = function
  | Const (id', typ) when id = id' -> Some typ
  | _ -> None

let is_var = function
  | Var _ -> true
  | _ -> false

let get_var = function
  | Var (v, _) -> v
  | _ -> failwith "variable expected"

let get_const_or_var = function
  | Const (id, _) | Var (id, _) -> id
  | _ -> failwith "const or var expected"

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

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id

let type_vars only_free typ =
  let rec find = function
    | Bool | Type | Base _ -> []
    | TypeVar id -> [id]
    | Fun (t, u) -> find t @ find u
    | Pi (id, t) -> 
        if only_free then remove id (find t) else find t
    | Product ts -> concat_map find ts in
  unique (find typ)

let free_type_vars = type_vars true
let all_type_vars = type_vars false

let type_vars_in_formula only_free f =
  let rec find = function
    | Const _ -> []
    | Var (_id, typ) -> all_type_vars typ
    | App (t, u) | Eq (t, u) -> find t @ find u
    | Lambda (id, typ, f) ->
        let vars = all_type_vars typ @ find f in
        if only_free && typ = Type then remove id vars else vars in
  unique (find f)

let free_type_vars_in_formula = type_vars_in_formula true
let all_type_vars_in_formula = type_vars_in_formula false

(* t[u/x] *)
let rec type_subst (t: typ) (u: typ) (x: id) = match t with
  | Bool | Type | Base _ -> t
  | TypeVar y -> if x = y then u else t
  | Fun (v, w) -> Fun (type_subst v u x, type_subst w u x)
  | Product typs -> Product (typs |> map (fun t -> type_subst t u x))
  | Pi (y, t') -> if x = y then t else
      if mem y (free_type_vars u) && mem x (free_type_vars t')
        then let y' = rename y (x :: free_type_vars t') in
             Pi (y', type_subst (type_subst t' (TypeVar y') y) u x)
        else Pi (y, type_subst t' u x)

let subst_types tsubst t : typ =
  fold_left (fun t (x, u) -> type_subst t u x) t tsubst

let rec next_var x avoid =
  if mem x avoid then
    let c, rest = usplit x in
    let t = match c with
      | "o" -> "a'"  (* constants a .. o *)
      | "z" -> "q'"  (* variables q .. z *)
      | "ω" -> "σ'"  (* type variables σ .. ω *)
      | _ -> uchar_to_string (Uchar.succ (uchar c)) in
    next_var (t ^ rest) avoid
  else x

(* f[u/x] *)
let rec type_subst_in_formula (f: formula) (u: typ) (x: id) =
  let subst typ = type_subst typ u x in
  match f with
    | Const (id, typ) ->
        (* if id = "is_mapping" then
          printf "is_mapping: typ = %s, u/x = %s/%s, result = %s\n" (show_type typ) (show_type u) x (show_type (subst typ)); *)
        Const (id, subst typ)
    | Var (id, typ) -> Var (id, subst typ)
    | Lambda (id, typ, f) ->
        Lambda (id, subst typ, type_subst_in_formula f u x)
    | _ -> map_formula (fun f -> type_subst_in_formula f u x) f

let subst_types_in_formula tsubst f : formula =
  fold_left (fun f (x, t) -> type_subst_in_formula f t x) f tsubst

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

let elem = binop "∈" (Pi ("σ",
    Fun (TypeVar "σ", Fun (Fun (TypeVar "σ", Bool), Bool))))  (* σ → (σ → 𝔹) → 𝔹 *)

let not_elem f g = _not (elem f g)

let multi_and = function
  | [] -> _true
  | xs -> fold_left1 _and xs

let multi_or = function
  | [] -> _false
  | xs -> fold_left1 _or xs

let quant q id typ f =
  let quant_type = Fun (Fun (typ, Bool), Bool) in
  App (Const (q, quant_type), Lambda (id, typ, f))
  
let quant' q (id, typ) f = quant q id typ f

let _for_all = quant "∀"
let _for_all' = quant' "∀"
let _exists = quant "∃"
let _exists' = quant' "∃"

let c_and = Const("∧", logical_op_type)

let is_quantifier = function
  | Const (id, _) when id = "∀" || id = "∃" -> true
  | _ -> false

let mk_neq f g = _not (mk_eq f g)
let mk_eq' eq f g = (if eq then mk_eq else mk_neq) f g

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

let without_type_suffix id =
  let id = fst (split_type_suffix id) in
  if id = "u-" then "-" else id  (* display unary minus as ordinary minus *)

let collect_args t : formula * formula list =
  let rec collect = function
    | App (f, g) ->
        let (head, args) = collect f in
        (head, g :: args)
    | head -> (head, []) in
  let (head, args) = collect t in
  (head, rev args)

let is_tuple_apply f : (id * formula list) option =
  let (head, args) = collect_args f in
  match head with
    | Const (s, _) when is_tuple_constructor s -> Some (s, args)
    | _ -> None

type formula_kind =
  | True
  | False
  | Not of formula
  | Binary of id * typ * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let rec get_const_type f = match f with
  | Const (id, t) when id = _type -> t
  | Var (v, Type) -> TypeVar v
  | _ ->
      printf "get_const_type: f = %s (%b)\n" (show_formula f) (is_const f);
      failwith "type expected"

and type_of f : typ = match f with
  | Const (_, typ) | Var (_, typ) -> typ
  | App (f, g) -> (match type_of f with
      | Fun (_, u) -> u
      | Pi (x, t) -> type_subst t (get_const_type g) x
      | _ -> assert false)
  | Lambda (id, Type, f) -> Pi (id, type_of f)
  | Lambda (_, typ, f) -> Fun (typ, type_of f)
  | Eq (_, _) -> Bool

and fkind boolean f : formula_kind = match f with
  | Const ("⊤", _) -> True
  | Const ("⊥", _) -> False
  | App (Const ("¬", _), f) -> Not f
  | App (App (Const (op, typ), t), u)
  | App (App (Var (op, typ), t), u)
      when mem op logical_binary || (not boolean) ->
        Binary (op, typ, t, u)
  | App (Const (q, _) as c, Lambda (id, typ, u)) when is_quantifier c ->
      Quant(q, id, typ, u)
  | Eq (f, g) when boolean && type_of f = Bool -> (
      assert (type_of g = Bool);
      Binary ("↔", logical_op_type, f, g))   (* via boolean extensionality *)
  | f -> Other f

and bool_kind f = fkind true f
and kind f = fkind false f

and gather_associative op f = match kind f with
  | Binary (op', _, f, g) when op' = op ->
      gather_associative op f @ gather_associative op g
  | _ -> [f]

and gather_implies f = match bool_kind f with
  | Binary ("→", _, f, g) -> f :: gather_implies g
  | _ -> [f]

and show_formula_multi multi f =
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
        | Const (id, typ) ->
            if id = _type then show_type typ else
              sprintf "%s" (without_type_suffix id)
        | Var (id, _typ) -> id
        | App _ ->
            let (head, args) = collect_args f in (
            match head with
              | Const (c, _typ) when is_tuple_constructor c ->
                  parens_if (outer > -2) @@
                    comma_join (map (show1 (-1) false) args)
              | _ ->  (* display curried args in uncurried form *)
                  let args_s = map (show1 (-2) false) args in
                  sprintf "%s(%s)" (show1 10 false head) (comma_join args_s))
        | Lambda (id, typ, t) ->
            parens_if (quantifier_prec < outer)
              (sprintf "λ%s:%s.%s" id (show_type typ) (show1 quantifier_prec false t))
        | Eq (t, u) -> show_eq "=" t u in
  show 0 multi (-1) false f

and show_formula f = show_formula_multi false f
let show_formulas fs =
  sprintf "[%s]" (comma_join (map show_formula fs))
  
let show_multi = show_formula_multi true

let prefix_show prefix f =
  indent_with_prefix prefix (show_multi f)

let negate f = match bool_kind f with
  | Not f -> f
  | _ -> _not f

let gather_and = gather_associative "∧"
let gather_or = gather_associative "∨"

let implies f g = fold_right implies1 (gather_and f) g

let premises f = split_last (gather_implies f)

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

let free_vars_and_type_vars f = free_vars f @ free_type_vars_in_formula f

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

let for_all_vars_types : (id * typ) list -> formula -> formula =
  fold_right _for_all'
let exists_vars_types : (id * typ) list -> formula -> formula =
  fold_right _exists'

let for_all_vars_typs_if_free ids_typs f : formula =
  let fv = free_vars_and_type_vars f in
  for_all_vars_types (ids_typs |> filter (fun (id, _typ) -> mem id fv)) f

let rec gather_pi typ : id list * typ = match typ with
  | Pi (x, typ) ->
      let (xs, typ) = gather_pi typ in
      (x :: xs, typ)
  | _ -> ([], typ)

let without_pi typ = snd (gather_pi typ)

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

let rec remove_quant q f : (id * typ) list * formula = match kind f with
  | Quant (q', x, typ, g) when q = q' ->
      let (xs, h) = remove_quant q g in
      ((x, typ) :: xs, h)
  | _ -> ([], f)

let remove_for_all = remove_quant "∀"
let remove_exists = remove_quant "∃"

let remove_quants with_existential : formula -> formula * id list =
  let rec remove f = match kind f with
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

let remove_universal f : formula = fst (remove_quants false f)
let remove_quantifiers f : formula = fst (remove_quants true f)

let rec mono_const c typ args : formula = match typ with
  | Pi (x, typ) -> (
      match args with
        | (arg :: args) ->
            let t = get_const_type arg in
            mono_const c (type_subst typ t x) args
        | _ -> failwith "to_mono")
  | _ -> apply (Const (c, typ) :: args)

let rec implicit_formula f : formula = match f with
  | App (Const ("∀", _), Lambda (_, Type, f)) -> implicit_formula f
  | App _ -> (match collect_args f with
    | (Const (c, typ), args) -> mono_const c typ (map implicit_formula args)
    | _ -> map_formula implicit_formula f)
  | _ -> map_formula implicit_formula f

let raise_definition f : id * formula =
  (* Transform ∀σ₁...σₙ v₁...vₙ (C v₁ ... vₙ = φ) to C = λσ₁... σₙ v₁...vₙ.φ .
     This is applied before type inference, so we don't expect C to be applied
     to type arguments. *)
  let (xs, f) = gather_quant "∀" f in
  let (type_vars, vars) = xs |> partition (fun (_, typ) -> typ = Type) in
  match f with
    | Eq (f, g) | App (App (Const ("↔", _), f), g) ->
        let (c, args) = collect_args f in (
        match c with
          | Const (id, _) | Var (id, _) ->
              let arg_vars = map get_var args in
              if std_sort (map fst vars) <> std_sort arg_vars
                then failwith "raise";
              let h = fold_right (fun v f -> lambda v (assoc v vars) f) arg_vars g in
              let h = fold_right (fun (x, _) f -> lambda x Type f) type_vars h in
              (id, h)
          | _ -> failwith "raise")
    | _ -> failwith "raise"

let mk_var_or_type_const (id, typ) =
  if typ = Type then Const (_type, TypeVar id) else Var (id, typ)

let lower_definition f : formula option = match f with
  (* Transform C = λσ₁... σₙ v₁...vₙ.φ to ∀σ₁...σₙ v₁...vₙ (C σ₁...σₙ v₁ ... vₙ = φ) .*)
  | Eq ((Const (_, typ) as c), f) ->
      let (vars_typs, g) = gather_lambdas f in
      let eq = if target_type typ = Bool then _iff else mk_eq in
      let f = for_all_vars_types vars_typs (
                eq (apply (c :: map mk_var_or_type_const vars_typs)) g) in
      Some f
  | _ -> None

let suffix id avoid : id =
  let rec try_suffix n =
    let id' = sprintf "%s_%d" id n in
    if mem id' avoid then try_suffix (n + 1) else id' in
  if mem id avoid then try_suffix 1 else id

(* replace [u/v] in t *)
let rec replace_in_formula u v t : formula =
  if t == v then u  (* physical equality test *)
  else map_formula (replace_in_formula u v) t 

(* t[u/x] *)
let rec subst1 (t: formula) (u: formula) (x: id) = match t with
  | Const _ -> t
  | Var (y, _) -> if x = y then u else t
  | App (f, g) | Eq (f, g) ->
      app_or_eq t (subst1 f u x) (subst1 g u x)
  | Lambda (y, typ, t') -> if x = y then t else
      if not (mem y (free_vars u)) then Lambda (y, typ, subst1 t' u x)
      else let y' = rename y (x :: free_vars t') in
        Lambda (y', typ, subst1 (subst1 t' (Var (y', typ)) y) u x)

type tsubst = (id * typ) list
type vsubst = (id * formula) list
type subst = tsubst * vsubst

let subst_vars vsubst f : formula =
  fold_left (fun f (x, t) -> subst1 f t x) f vsubst

let subst_n (tsubst, vsubst) f : formula =
  subst_types_in_formula tsubst (subst_vars vsubst f)

(* β-reduction *)
let rec b_reduce = function
  | App (f, g) -> (match b_reduce f, b_reduce g with
      | Lambda (x, _typ, f), g -> b_reduce (subst1 f g x)  
      | f, g -> App (f, g))
  | Lambda (id, typ, f) -> Lambda (id, typ, b_reduce f)
  | Eq (f, g) -> Eq (b_reduce f, b_reduce g)
  | f -> f

let rsubst1 t u x : formula = b_reduce (subst1 t u x)
let rsubst subst f : formula = b_reduce (subst_n subst f)

let eta = function
  | Lambda (id, typ, App (f, Var (id', typ'))) when id = id' && typ = typ' -> f  
  | f -> f

(* t and u unify if tσ = uσ for some type substitution σ.
   t matches u if tσ = u for some type substitution σ.   *)
let unify_or_match_types is_unify tsubst t u : tsubst option =
  let rec unify tsubst t u : tsubst option = match t, u with
    | TypeVar x, t ->
        if t = TypeVar x then Some tsubst
        else (match assoc_opt x tsubst with
          | Some u ->
              if is_unify then unify tsubst t u
              else if t = u then Some tsubst else None
          | None ->
              let t = subst_types tsubst t in
              if mem x (free_type_vars t) then None else
                let tsubst = tsubst |> map (fun (y, u) -> (y, type_subst u t x)) in
                Some ((x, u) :: tsubst))
    | _t, TypeVar _x when is_unify -> unify tsubst u t
    | Fun (t, u), Fun (t', u') ->
        let* tsubst = unify tsubst t t' in
        unify tsubst u u'
    | Product [], Product [] -> Some tsubst
    | Product (t :: ts), Product (u :: us) ->
        let* tsubst = unify tsubst t u in
        unify tsubst (Product ts) (Product us)
    | t, u -> if t = u then Some tsubst else None in
  unify tsubst t u

let unify_types tsubst t u = unify_or_match_types true tsubst t u

(* Allow * → τ to match Πσ.τ.
 * For example, in ∀(λσ:* ∀x:σ x = x) we have
 * ∀ : [* → 𝔹] → 𝔹 applied to (∏σ.𝔹). *)
let unify_types_or_pi tsubst t u = match t, u with
  | Fun (Type, t), Pi (_, u) -> unify_types tsubst t u
  | _ -> unify_types tsubst t u

(* f and g unify if fσ = gσ for some substitution σ.
   f matches g if fσ = g for some substitution σ.   *)
let unify_or_match is_unify subst t u : subst option =
  let rec unify' ((tsubst, vsubst) as subst) t u : subst option =
    let unify_pairs f g f' g' : subst option =
      let* subst = unify' subst f f' in
      unify' subst g g' in
    match eta t, eta u with
      | Const (c, typ), Const (c', typ') ->
          if c = c' && typ = typ' then Some subst else None
      | Var (x, typ), f ->
          if f = Var (x, typ) then Some subst
          else
            let* tsubst = unify_or_match_types is_unify tsubst typ (type_of f) in
            let subst = (tsubst, vsubst) in(
            match assoc_opt x vsubst with
              | Some g ->
                  if is_unify then unify' subst f g
                  else if f = g then Some subst else None
              | None ->
                  let f = subst_n subst f in
                  if mem x (free_vars f) then None else
                    let vsubst = vsubst |> map (fun (y, g) -> (y, subst1 g f x)) in
                    Some (tsubst, (x, f) :: vsubst))
      | _f, Var (_x, _typ) when is_unify -> unify' subst u t
      | App (f, g), App (f', g') ->
          unify_pairs f g f' g'
      | Eq (f, g), Eq (f', g') -> (
          match unify_pairs f g f' g' with
            | Some subst -> Some subst
            | None -> unify_pairs f g g' f')
      | Lambda (x, xtyp, f), Lambda (y, ytyp, g) ->
          let* tsubst = unify_or_match_types is_unify tsubst xtyp ytyp in
          let* (tsubst, vsubst) = unify' (tsubst, vsubst) f g in
          let x', y' = assoc_opt x vsubst, assoc_opt y vsubst in
          if (x' = None || x' = Some (Var (y, ytyp))) &&
            (y' = None || y' = Some (Var (x, xtyp)))
          then let vsubst = remove_assoc x (remove_assoc y vsubst) in
              let fs = map snd vsubst in
              if is_free_in_any x fs || is_free_in_any y fs then None
              else Some (tsubst, vsubst)
          else None
      | _, _ -> None
  in unify' subst t u

let unify = unify_or_match true ([], [])
let _match = unify_or_match false ([], [])
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

let first_var start_var = function
  | Fun (_, Bool) -> "P"
  | _ -> start_var

let looks_like_var id = 'q' <= id.[0] && id.[0] <= 'z'

(* Alpha-equivalent formulas should have the same form after renaming.
 * We choose a new name for each variable and type variable as soon as
 * we encounter it in the formula structure. *)
let rename_vars f : formula =
  let consts = all_consts f in
  let free = free_vars f in
  let num_vars = count_binders f + length free +
    length (filter looks_like_var consts) in
  let start_var = char_to_string (
    if num_vars <= 3 then 'x' else
      let c = Char.chr (Char.code 'z' - num_vars + 1) in
      if c < 'q' then 'q' else c) in
  let name_map, used = ref [], ref (consts @ free) in
  let type_map, used_types = ref [], ref [] in
  let next_id id typ =
    let x = next_var (first_var start_var typ) !used in
    name_map := (id, x) :: !name_map;
    used := x :: !used;
    x in
  let rec map_type = function
    | TypeVar id -> (
        match assoc_opt id !type_map with
          | Some name -> TypeVar name
          | None ->
              let v = next_var "σ" !used_types in
              type_map := (id, v) :: !type_map;
              used_types := v :: !used;
              TypeVar v)
    | Fun (t, u) -> Fun (map_type t, map_type u)
    | Product typs -> Product (map map_type typs)
    | Pi _ -> failwith "rename_vars"
    | t -> t in
  let rec rename h : formula =
    match h with
      | Const _ -> h
      | Var (id, typ) -> (
          let typ = map_type typ in
          match assoc_opt id !name_map with
            | Some name -> Var (name, typ)
            | None -> Var (next_id id typ, typ))
      | App (f, g) | Eq (f, g) -> app_or_eq h (rename f) (rename g)
      | Lambda (id, typ, f) ->
          let typ = map_type typ in
          let x = next_id id typ in
          let f = rename f in
          name_map := remove_assoc id !name_map;
          Lambda (x, typ, f) in
  rename f
