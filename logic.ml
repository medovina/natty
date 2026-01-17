open Printf

open Util

type id = string

type typ =
  | Bool
  | Type
  | Base of id * range
  | TypeVar of id
  | Fun of typ * typ
  | Pi of id * typ
  | TypeApp of id * typ list
  | Product of typ list
  | Sub of formula

and formula =
  | Const of id * typ * range
  | Var of id * typ * range
  | App of formula * formula * range
  | Lambda of id * typ * formula
  | Eq of formula * formula

let base_type_range typ range = match typ with
  | "𝔹" -> Bool
  | id -> Base (id, range)

let base_type typ = base_type_range typ empty_range

let mk_type_var x = TypeVar x
let mk_fun_type t u = Fun (t, u)
let mk_pi_type x t = Pi (x, t)
let mk_product_type ts = Product ts

let mk_fun_types ts u : typ = fold_right mk_fun_type ts u
let mk_pi_types xs u : typ = fold_right mk_pi_type xs u

let rec arg_types t : typ list = match t with
  | Fun (t, u) -> t :: arg_types u
  | _ -> []

let rec target_type = function
  | Fun (_, u) -> target_type u
  | t -> t

let unknown_type = base_type "?"

let is_unknown = function
  | Base (id, _) -> id.[0] = '?'
  | _ -> false

let rec arity = function
  | Fun (_, typ) -> 1 + arity typ
  | _ -> 0

let map_type fn = function
  | Fun (t, u) -> Fun (fn t, fn u)
  | Pi (id, t) -> Pi (id, fn t)
  | TypeApp (x, typs) -> TypeApp (x, map fn typs)
  | Product typs -> Product (map fn typs)
  | t -> t

let rec strip_type_range typ = match typ with
  | Base (id, _) -> Base (id, empty_range)
  | _ -> map_type strip_type_range typ

let eq_type t u = strip_type_range t = strip_type_range u

let eq_id_type (x, t) (x', u) = x = x' && eq_type t u

let mem_id_type x ys = exists (eq_id_type x) ys

let const c typ = Const (c, typ, empty_range)
let _const c = const c unknown_type

let var v typ = Var (v, typ, empty_range)
let _var v = var v unknown_type
let mk_var' (id, typ) = var id typ

let app f g = App (f, g, empty_range)
let lambda id typ f = Lambda (id, typ, f)
let lambda' (id, typ) f = Lambda (id, typ, f)
let mk_eq f g = Eq (f, g)

(* Const ("_type", τ) is the type τ itself. *)
let _type = "_type"

let type_const typ = const _type typ

let apply formulas : formula = fold_left1 app formulas

let tuple_cons n = sprintf "(%s)" (String.make (n - 1) ',')

let tuple_cons_type typs : typ = fold_right mk_fun_type typs (Product typs)

let _tuple n : formula =
  (* Build a type such as Πσ.Πτ.σ → τ → σ ⨯ τ. *)
  let sigma = Uchar.to_int (uchar "σ") in
  let ids = List.init n (fun i -> uchar_to_string (Uchar.of_int (sigma + i))) in
  let typ = fold_right mk_pi_type (ids) (tuple_cons_type (map mk_type_var ids)) in
  const (tuple_cons n) typ

let is_tuple_constructor = starts_with "(,"

let mk_tuple = function
  | [] -> failwith "mk_tuple" 
  | [g] -> g
  | vals -> apply (_tuple (length vals) :: vals)

let is_const = function
  | Const _ -> true
  | _ -> false

let is_const_id c = function
  | Const (c', _, _) when c = c' -> true
  | _ -> false

let is_const_id_type id typ = function
   | Const (id', typ', _) when id = id' && eq_type typ typ' -> true
   | _ -> false

let is_var = function
  | Var _ -> true
  | _ -> false

let is_var_id_type id typ = function
   | Var (id', typ', _) when id = id' && eq_type typ typ' -> true
   | _ -> false

let get_var = function
  | Var (v, typ, _) -> (v, typ)
  | _ -> failwith "variable expected"

let opt_const = function
  | Const (c, _, _) -> Some c
  | _ -> None

let get_const_or_var = function
  | Const (id, _, _) | Var (id, _, _) -> id
  | _ -> failwith "const or var expected"

let is_fun = function
  | Fun _ -> true
  | _ -> false

let is_lambda = function
  | Lambda _ -> true
  | _ -> false

let is_eq = function
  | Eq _ -> true
  | _ -> false

let is_neq = function
  | App (Const ("(¬)", _, _), Eq _, _) -> true
  | _ -> false

let is_iff = function
  | App (App (Const ("(↔)", _, _), _, _), _, _) -> true
  | _ -> false

let app_or_eq h f g = match h with
  | App _ -> app f g
  | Eq _ -> Eq (f, g)
  | _ -> assert false

let map_formula fn = function
  | App (f, g, r) -> App (fn f, fn g, r)
  | Lambda (id, typ, f) -> Lambda (id, typ, fn f)
  | Eq (f, g) -> Eq (fn f, fn g)
  | f -> f

let iter_formula fn = function
  | App (f, g, _) | Eq (f, g) -> fn f; fn g
  | Lambda (_, _, f) -> fn f
  | _ -> ()

let rec base_types typ : id list =
  let find = function
    | Bool | Type | TypeVar _ -> []
    | Base (id, _) -> [id]
    | Fun (t, u) -> base_types t @ base_types u
    | Pi (_, t) -> base_types t
    | TypeApp (_, types) | Product types ->
        concat_map base_types types
    | Sub f -> concat_map base_types (formula_types f)
  in unique (find typ)

and formula_types f = unique @@ match f with
  | Const (_, typ, _) | Var (_, typ, _) -> [typ]
  | App (f, g, _) | Eq (f, g) -> concat_map formula_types [f; g]
  | Lambda (_, typ, f) -> typ :: formula_types f

let formula_base_types f = unique @@
  concat_map base_types (formula_types f)

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id

let rec vars_in_type only_free typ : (id * typ) list =
  let rec find = function
    | Bool | Type | Base _ -> []
    | TypeVar id -> [id, Type]
    | Fun (t, u) -> find t @ find u
    | Pi (id, t) -> 
        if only_free then remove_all_assoc id (find t) else (id, Type) :: find t
    | TypeApp (_, ts) | Product ts -> concat_map find ts
    | Sub f -> vars_in_formula only_free f in
  find typ

and vars_in_formula only_free f : (id * typ) list =
  let rec find = function
    | Const _ -> []
    | Var (id, typ, _) -> (id, typ) :: vars_in_type only_free typ
    | App (t, u, _) | Eq (t, u) -> find t @ find u
    | Lambda (id, typ, t) ->
        vars_in_type only_free typ @
        if only_free then remove_all_assoc id (find t) else (id, typ) :: find t in
  find f

let free_vars_in_type typ = unique (map fst (vars_in_type true typ))

let find_vars only_free f = unique (map fst (vars_in_formula only_free f))
let all_vars = find_vars false
let free_vars = find_vars true

let free_vars_types f = unique (vars_in_formula true f)

let only_type_vars ids_typs : id list = unique @@
  ids_typs |> filter_map (fun (id, typ) -> if typ = Type then Some id else None)

let free_type_vars_in_type t : id list = only_type_vars (vars_in_type true t)
let free_type_vars f : id list = only_type_vars (vars_in_formula true f)

let rec has_subformula s f = s = f || match f with
  | App (f, g, _) | Eq (f, g) -> has_subformula s f || has_subformula s g
  | Lambda (_, _, f) -> has_subformula s f
  | _ -> false

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

(* t[u/x] *)
let rec type_subst (t: typ) (u: typ) (x: id) =
  let subst w = type_subst w u x in
  match t with
    | Bool | Type | Base _ -> t
    | TypeVar y -> if x = y then u else t
    | Fun (v, w) -> Fun (subst v, subst w)
    | TypeApp (id, typs) -> TypeApp (id, map subst typs)
    | Product typs -> Product (map subst typs)
    | Pi (y, t') -> if x = y then t else
        if mem y (free_vars_in_type u) && mem x (free_vars_in_type t')
          then let y' = rename y (x :: free_vars_in_type t') in
              Pi (y', subst (type_subst t' (TypeVar y') y))
          else Pi (y, subst t')
    | Sub f -> Sub (type_subst_in_formula f u x)

(* f[u/x] *)
and type_subst_in_formula (f: formula) (u: typ) (x: id) =
  let subst typ = type_subst typ u x in
  match f with
    | Const (id, typ, r) -> Const (id, subst typ, r)
    | Var (id, typ, r) -> Var (id, subst typ, r)
    | Lambda (id, typ, f) ->
        Lambda (id, subst typ, type_subst_in_formula f u x)
    | _ -> map_formula (fun f -> type_subst_in_formula f u x) f

let subst_types tsubst t : typ =
  fold_left (fun t (x, u) -> type_subst t u x) t tsubst

let subst_types_in_formula tsubst f : formula =
  fold_left (fun f (x, t) -> type_subst_in_formula f t x) f tsubst

let rec count_binders = function
  | Const _ | Var _ -> 0
  | App (f, g, _) | Eq (f, g) -> count_binders f + count_binders g
  | Lambda (_, _, f) -> 1 + count_binders f

let _false = const "%⊥" Bool
let _true = const "%⊤" Bool

let undefined = const "undef" (Pi ("σ", TypeVar "σ"))

let is_bool_const x = x = _true || x = _false

let _not f = app (const "(¬)" (Fun (Bool, Bool))) f
let _neq f g = _not (Eq (f, g))

let logical_binary = ["(∧)"; "(∨)"; "(→)"; "(↔)"]

let logical_syms = ["(¬)"; "(∀)"; "(∃)"] @ logical_binary

let logical_ops = ["%⊥"; "%⊤"] @ logical_syms

let binop op typ f g : formula = app (app (const op typ) f) g
let binop_unknown op = binop op unknown_type

let logical_op_type = Fun (Bool, Fun (Bool, Bool))
let logical_op op = binop op logical_op_type

let _and = logical_op "(∧)"
let _or = logical_op "(∨)"
let implies1 = logical_op "(→)"
let _iff = logical_op "(↔)"

let elem = binop "∈" (Pi ("σ",
    Fun (TypeVar "σ", Fun (Fun (TypeVar "σ", Bool), Bool))))  (* σ → (σ → 𝔹) → 𝔹 *)

let not_elem f g = _not (elem f g)

let _eif_c = const "eif" (Pi ("σ",
    Fun (Bool, Fun (TypeVar "σ", Fun (TypeVar "σ", TypeVar "σ")))))  (* 𝔹 → σ → σ → σ *)

let _eif p f g = apply [_eif_c; p; f; g]  (* exclusive if *)

let multi_and = function
  | [] -> _true
  | xs -> fold_left1 _and xs

let multi_or = function
  | [] -> _false
  | xs -> fold_left1 _or xs

let quant q id typ f : formula =
  let quant_type = Fun (Fun (typ, Bool), Bool) in
  app (const q quant_type) (Lambda (id, typ, f))
  
let quant' q (id, typ) f : formula = quant q id typ f

let _for_all = quant "(∀)"
let _for_all' = quant' "(∀)"
let _exists = quant "(∃)"
let _exists' = quant' "(∃)"

let generalize f : formula =
  let vs = free_type_vars f in
  let all_type x f = _for_all x Type f in
  fold_right all_type vs f

let c_and = const "(∧)" logical_op_type

let is_quantifier = function
  | Const (id, _, _) when id = "(∀)" || id = "(∃)" -> true
  | _ -> false

let mk_neq f g = _not (mk_eq f g)
let mk_eq' eq f g = (if eq then mk_eq else mk_neq) f g

let binary_ops = [
  ("^", 9);
  ("·", 8); ("/", 8); ("div", 8); ("mod", 8);
  ("+", 7); ("-", 7);
  ("∈", 6); ("|", 6); 
  ("<", 5); ("≤", 5); (">", 5); ("≥", 5); ("~", 5); ("⊆", 5);
  ("∧", 4); ("∨", 3); ("→", 2); ("↔", 1)
]

let not_prec = 9
let eq_prec = 5
let quantifier_prec = 0

let single_letter = function
  | (Const (id, _, _) | Var (id, _, _)) when is_letter id.[0] -> Some id
  | _ -> None

let split_type_suffix id =
  match String.index_opt id ':' with
    | Some i -> (String.sub id 0 i, string_from id i)
    | None -> (id, "")

let without_type_suffix id =
  let id = fst (split_type_suffix id) in
  if id = "u-" then "-" else id  (* display unary minus as ordinary minus *)

let collect_args f : formula * formula list =
  let rec collect = function
    | App (f, g, _) ->
        let (head, args) = collect f in
        (head, g :: args)
    | head -> (head, []) in
  let (head, args) = collect f in
  (head, rev args)

let head_of f : formula = fst (collect_args f)

let is_eq_or_iff f = match f with
  | Eq (f, g) | App (App (Const ("(↔)", _, _), f, _), g, _) -> Some (f, g)
  | _ -> None

let strip_prefix c = match c.[0] with
  | '%' | '~' -> string_from c 1
  | '[' -> let i = String.index c ']' in string_from c (i + 1)
  | '(' ->
      assert (last_char c = ')');
      string_range c 1 (strlen c - 1)
  | _ -> c

let basic_const c = without_type_suffix (strip_prefix c)

type formula_kind =
  | True
  | False
  | Not of formula
  | Binary of id * typ * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let rec get_const_type f = match f with
  | Const (id, t, _) when id = _type -> t
  | Const (id, Type, r) -> Base (id, r)
  | Var (v, Type, _) -> TypeVar v
  | _ ->
      printf "get_const_type: f = %s (%b)\n" (show_formula f) (is_const f);
      failwith "type expected"

and fkind boolean f : formula_kind = match f with
  | Const ("%⊤", _, _) -> True
  | Const ("%⊥", _, _) -> False
  | App (Const ("(¬)", _, _), f, _) -> Not f
  | App (App (Const (op, typ, _), t, _), u, _)
  | App (App (Var (op, typ, _), t, _), u, _)
      when mem op logical_binary || (not boolean) ->
        Binary (op, typ, t, u)
  | App (Const (q, _, _) as c, Lambda (id, typ, u), _) when is_quantifier c ->
      Quant(q, id, typ, u)
  | f -> Other f

and bool_kind f = fkind true f
and kind f = fkind false f

and gather_associative op f = match kind f with
  | Binary (op', _, f, g) when op' = op ->
      gather_associative op f @ gather_associative op g
  | _ -> [f]

and gather_implies f = match bool_kind f with
  | Binary ("(→)", _, f, g) -> f :: gather_implies g
  | _ -> [f]

and show_type t =
  let rec show outer left typ : string =
    let op prec sym t u =
      parens_if (outer > prec || outer = prec && left) @@
      sprintf "%s %s %s" (show prec true t) sym (show prec false u) in
    match typ with
      | Bool -> "𝔹"
      | Type -> "*"
      | Base (id, _) -> id
      | TypeVar id -> id
      | Fun (t, u) -> op 1 "→" t u
      | Pi (id, t) ->
          parens_if (0 < outer) (sprintf "Π%s.%s" id (show 0 false t))
      | TypeApp (c, [typ]) when c.[0] = '@' -> show outer left typ
      | TypeApp (id, typs) ->
          sprintf "%s(%s)" id (comma_join (map show_type typs))
      | Product typs ->
          parens_if (outer >= 2) @@
          String.concat " ⨯ " (map (show 2 true) typs)
      | Sub f -> sprintf "[%s]" (show_formula f) in
  show (-1) false t

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
      | Binary (binop, _, t, u) when mem_assoc (basic_const binop) binary_ops ->
          let op = basic_const binop in
          let prec = assoc op binary_ops in
          let p = prec < outer ||
            prec = outer &&
              (op = "·" || op = "/" || op = "+" || op = "→" && not right) in
          let layout multi =
            match single_letter t, single_letter u with
              | Some t, Some u when op = "·" && strlen t = 1 && strlen u = 1
                  -> t ^ u
              | _ ->
                  let sep = if op = "^" then "" else " " in
                  sprintf "%s%s%s%s%s" (show indent multi prec false t) sep op sep
                                     (show indent multi prec true u) in
          let s = if (op = "→" || op = "∧" || op = "∨") && multi then
            let line = layout false in
            if String.length line <= 60 then line
            else
              let fs = (if op = "→" then gather_implies else gather_associative binop) f in
              let ss = (show1 prec false (hd fs)) ::
                map (show (indent + 3) multi prec false) (tl fs) in
              String.concat (sprintf "\n%s %s " (n_spaces indent) op) ss
          else layout multi in
          parens_if p s
      | Quant (q, id, typ, u) ->
          let prefix = sprintf "%s%s:%s." (strip_prefix q) id (show_type typ) in
          parens_if (quantifier_prec < outer)
            (prefix ^ show (indent + utf8_len prefix) multi quantifier_prec false u)
      | _ -> match f with
        | Const (id, typ, _) ->
            if id = _type then show_type typ else
              sprintf "%s" (basic_const id)
        | Var (id, _typ, _) -> id
        | App _ ->
            let (head, args) = collect_args f in (
            match head with
              | Const (c, _typ, _) when is_tuple_constructor c ->
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

let is_and f = match bool_kind f with
  | Binary ("(∧)", _, _, _) -> true
  | _ -> false

let gather_and = gather_associative "(∧)"
let gather_or = gather_associative "(∨)"

let implies f g = if f = _true then g else fold_right implies1 (gather_and f) g

let is_ground f =
  let rec has_free outer = function
    | Const _ -> false
    | Var (v, _, _) -> not (mem v outer)
    | Lambda (x, _, f) -> has_free (x :: outer) f
    | App (t, u, _) | Eq (t, u) ->
        has_free outer t || has_free outer u in
  not (has_free [] f)

let all_consts0 f : id list =
  let rec find = function
    | Const (id, _typ, _) -> [id]
    | Var _ -> []
    | App (t, u, _) | Eq (t, u) -> find t @ find u
    | Lambda (id, _typ, t) -> remove id (find t)
  in find f

let all_consts f : id list =
  unique (subtract (all_consts0 f) logical_ops)

let is_var_in v =
  let rec find_var = function
    | Const _ -> false
    | Var (x, _, _) -> x = v
    | App (f, g, _) | Eq (f, g) -> find_var f || find_var g
    | Lambda (x, _typ, f) -> x = v || find_var f
  in find_var

let is_free_in x f = mem x (free_vars f)
let any_free_in xs f = overlap xs (free_vars f)

let is_free_in_any x fs = exists (fun f -> is_free_in x f) fs

let quant_vars_typ quant ids typ f =
  fold_right (fun id f -> quant id typ f) ids f

let for_all_vars_typ = quant_vars_typ _for_all

let for_all_vars_types : (id * typ) list -> formula -> formula =
  fold_right _for_all'
let exists_vars_types : (id * typ) list -> formula -> formula =
  fold_right _exists'

let for_all_vars_types_if_free ids_typs f : formula =
  let fv = free_vars f in
  for_all_vars_types (ids_typs |> filter (fun (id, _typ) ->
    mem id fv || id = "·")) f  (* "·" may not be explicitly present *)

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

let gather_for_all = gather_quant "(∀)"
let remove_for_all f = snd (gather_for_all f)
let gather_exists = gather_quant "(∃)"
let remove_exists f = snd (gather_exists f)

let remove_quants with_existential : formula -> formula * id list =
  let rec remove f = match kind f with
    | Quant ("(∀)", _x, _typ, g) -> remove g
    | Quant ("(∃)", x, _typ, g) when with_existential ->
        let (f, ex) = remove g in
        (f, x :: ex)
    | Not g -> (match bool_kind g with
        | Quant ("(∀)", x, _typ, h) when with_existential ->
            let (f, ex) = remove (_not h) in
            (f, x :: ex)
        | Quant ("(∃)", _x, _typ, h) -> remove (_not h)
        | _ -> (f, []))
    | _ -> (f, []) in
  remove

let remove_universal f : formula = fst (remove_quants false f)
let remove_quantifiers f : formula = fst (remove_quants true f)

let rec apply_types c typ args : formula = match typ with
  | Pi (x, typ) -> (
      match args with
        | (arg :: args) ->
            let t = get_const_type arg in
            apply_types c (type_subst typ t x) args
        | _ -> failwith "to_mono")
  | _ -> apply (const c typ :: args)

let rec apply_types_in_formula f : formula = match f with
  | App (Const ("(∀)", _, _), Lambda (_, Type, f), _) -> apply_types_in_formula f
  | App _ -> (match collect_args f with
    | (Const (c, typ, _), args) -> apply_types c typ (map apply_types_in_formula args)
    | _ -> map_formula apply_types_in_formula f)
  | _ -> map_formula apply_types_in_formula f

let mk_var_or_type_const (id, typ) =
  if typ = Type then type_const (TypeVar id) else var id typ

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
  | Var (y, _, _) -> if x = y then u else t
  | App (f, g, _) | Eq (f, g) ->
      app_or_eq t (subst1 f u x) (subst1 g u x)
  | Lambda (y, typ, t') -> if x = y then t else
      if not (mem y (free_vars u)) then Lambda (y, typ, subst1 t' u x)
      else let y' = rename y (x :: free_vars t') in
        Lambda (y', typ, subst1 (subst1 t' (var y' typ) y) u x)

type tsubst = (id * typ) list
type vsubst = (id * formula) list
type subst = tsubst * vsubst

let subst_vars vsubst f : formula =
  fold_left (fun f (x, t) -> subst1 f t x) f vsubst

let subst_n (tsubst, vsubst) f : formula =
  subst_types_in_formula tsubst (subst_vars vsubst f)

(* β-reduction *)
let rec b_reduce = function
  | App (f, g, _) -> (match b_reduce f, b_reduce g with
      | Lambda (x, _typ, f), g -> b_reduce (subst1 f g x)  
      | f, g -> app f g)
  | Lambda (id, typ, f) -> Lambda (id, typ, b_reduce f)
  | Eq (f, g) -> Eq (b_reduce f, b_reduce g)
  | f -> f

let rsubst1 t u x : formula = b_reduce (subst1 t u x)
let rsubst subst f : formula = b_reduce (subst_n subst f)

let eta = function
  | Lambda (id, typ, App (f, Var (id', typ', _), _))
      when id = id' && typ = typ' && not (is_free_in id f) -> f  
  | f -> f

(* t and u unify if tσ = uσ for some type substitution σ.
   t matches u if tσ = u for some type substitution σ.   *)
let unify_or_match_types is_unify is_var tsubst t u : tsubst option =
  let rec unify tsubst t u : tsubst option = match t, u with
    | Base (t, _), Base (u, _) -> if t = u then Some tsubst else None
    | TypeVar x, t when is_var x ->
        if t = TypeVar x then Some tsubst
        else (match assoc_opt x tsubst with
          | Some u ->
              if is_unify then unify tsubst t u
              else if t = u then Some tsubst else None
          | None ->
              let t = subst_types tsubst t in
              if mem x (free_vars_in_type t) then None else
                let tsubst = tsubst |> map (fun (y, u) -> (y, type_subst u t x)) in
                Some ((x, u) :: tsubst))
    | _t, TypeVar x when is_unify && is_var x -> unify tsubst u t
    | Fun (t, u), Fun (t', u') ->
        let* tsubst = unify tsubst t t' in
        unify tsubst u u'
    | Product [], Product [] -> Some tsubst
    | Product (t :: ts), Product (u :: us) ->
        let* tsubst = unify tsubst t u in
        unify tsubst (Product ts) (Product us)
    | t, u -> if t = u then Some tsubst else None in
  unify tsubst t u

let unify_types is_var tsubst t u = unify_or_match_types true is_var tsubst t u

(* Allow * → τ to match Πσ.τ.
 * For example, in ∀(λσ:* ∀x:σ x = x) we have
 * ∀ : [* → 𝔹] → 𝔹 applied to (Πσ.𝔹). *)
let unify_types_or_pi is_var tsubst t u = match t, u with
  | Fun (Type, t), Pi (_, u) -> unify_types is_var tsubst t u
  | _ -> unify_types is_var tsubst t u

let rec type_of1 tsubst f : typ = match f with
  | Const (_, typ, _) | Var (_, typ, _) -> typ
  | App (f, g, _) -> (match type_of f with
      | Fun (t, u) ->
          let g_type = type_of g in
          if t = g_type then u (* optimization: try direct comparison first *)
          else (match unify_types (Fun.const true) tsubst t g_type with
            | Some tsubst -> subst_types tsubst u
            | None ->
                printf "f = %s, type(f) = %s, g = %s, type(g) = %s\n"
                  (show_formula f) (show_type (type_of f))
                  (show_formula g) (show_type (type_of g));
                failwith "type_of1"
          )
      | Pi (x, t) -> type_subst t (get_const_type g) x
      | _ -> assert false)
  | Lambda (id, Type, f) -> Pi (id, type_of f)
  | Lambda (_, typ, f) -> Fun (typ, type_of f)
  | Eq (_, _) -> Bool

and type_of f : typ = type_of1 [] f

(* f and g unify if fσ = gσ for some substitution σ.
   f matches g if fσ = g for some substitution σ.   *)
let unify_or_match is_unify comm_ops subst t u : subst list =
  let rec unify' ((tsubst, vsubst) as subst) t u : subst list =
    let unify_pairs f g f' g' : subst list =
      let+ subst = unify' subst f f' in
      unify' subst g g' in
    let unify_commutative f g f' g' : subst list =
      unify_pairs f g f' g' @ unify_pairs f g g' f' in
    let unify_term_types t u =
      if t = unknown_type || u = unknown_type then [tsubst] else
      opt_to_list (unify_or_match_types is_unify (Fun.const true) tsubst t u) in
    match eta t, eta u with
      | Const (c, t, _), Const (c', u, _) when c = c' ->
          let+ tsubst = unify_term_types t u in
          [(tsubst, vsubst)]
      | Var _, Const (c, _, _) when mem c logical_syms -> []
      | Var _, App (Const ("(∨)", _, _), _, _) -> []
      | Var (x, typ, _), f ->
          if is_var_id_type x typ f then [subst]
          else
            let+ tsubst = unify_term_types typ (type_of1 tsubst f) in
            let subst = (tsubst, vsubst) in (
            match assoc_opt x vsubst with
              | Some g ->
                  if is_unify then unify' subst f g
                  else if f = g then [subst] else []
              | None ->
                  let f = subst_n subst f in
                  if mem x (free_vars f) then [] else
                    let vsubst = vsubst |> map (fun (y, g) -> (y, subst1 g f x)) in
                    [(tsubst, (x, f) :: vsubst)])
      | _f, Var (_x, _typ, _) when is_unify -> unify' subst u t
      | App (App (Const (op, _, _), f, _), g, _),
        App (App (Const (op', _, _), f', _), g', _)
          when op = op' && mem op comm_ops -> unify_commutative f g f' g'
      | App (f, g, _), App (f', g', _) -> unify_pairs f g f' g'
      | Eq (f, g), Eq (f', g') -> unify_commutative f g f' g'
      | Lambda (x, xtyp, f), Lambda (y, ytyp, g) ->
          let+ tsubst = unify_term_types xtyp ytyp in
          let+ (tsubst, vsubst) = unify' (tsubst, vsubst) f g in
          let x', y' = assoc_opt x vsubst, assoc_opt y vsubst in
          if (x' = None || opt_exists (is_var_id_type y ytyp) x') &&
            (y' = None || opt_exists (is_var_id_type x xtyp) y')
          then let vsubst = remove_assoc x (remove_assoc y vsubst) in
              let fs = map snd vsubst in
              if is_free_in_any x fs || is_free_in_any y fs then []
              else [(tsubst, vsubst)]
          else []
      | _, _ -> []
  in unify' subst t u

let unify comm_ops = unify_or_match true comm_ops ([], [])
let _match comm_ops = unify_or_match false comm_ops ([], [])
let try_match comm_ops = unify_or_match false comm_ops

let erase_sub typ = match typ with
  | Sub f -> (match type_of f with
      | Fun (t, Bool) -> t
      | _ -> failwith "erase_sub")
  | typ -> typ

let extract_definition f : (formula * (id * typ) list * formula) option =
  (* Look for f of the form ∀x₁...xₙ C y₁...yₙ = D.  The arguments yᵢ must be
     a permutation of the variables xⱼ.  *)
  let (xs, f) = gather_for_all f in
  let xs_vars = map mk_var' xs in
  match is_eq_or_iff f with
    | Some (head, g) ->
        let (c, ys) = collect_args head in (
        match c with
          | Const _ when subset ys xs_vars && subset xs_vars ys ->
              Some (c, map get_var ys, g)
          | _ -> None)
    | _ -> None

(* Transform ∀x₁...xₙ C x₁...xₙ = λy₁...yₙ.φ to
              ∀x₁...xₙ y₁...yₙ (C x₁...xₙ y₁...yₙ = φ) .*)
let lower_definition f : formula option =
  let* (c, xs, g) = extract_definition f in
  let (ys, g) = gather_lambdas g in
  let eq = if type_of g = Bool then _iff else mk_eq in
  let h = for_all_vars_types (xs @ ys) (
    eq (apply (c :: map mk_var' xs @ map mk_var_or_type_const ys)) g) in
  if f = h then None else Some h

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
      | Const (c, typ, r) -> Const (c, map_type typ, r)
      | Var (id, typ, r) -> (
          let typ = map_type typ in
          match assoc_opt id !name_map with
            | Some name -> Var (name, typ, r)
            | None -> Var (next_id id typ, typ, r))
      | App (f, g, _) | Eq (f, g) -> app_or_eq h (rename f) (rename g)
      | Lambda (id, typ, f) ->
          let typ = map_type typ in
          let x = next_id id typ in
          let f = rename f in
          name_map := remove_assoc id !name_map;
          Lambda (x, typ, f) in
  rename f
