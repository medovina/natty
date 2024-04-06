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

type formula =
  | Const of id * typ
  | Var of id * typ
  | App of formula * formula
  | Lambda of id * typ * formula
  | Eq of formula * formula

let mk_var' (id, typ) = Var (id, typ)
let mk_app f g = App (f, g)
let mk_eq f g = Eq (f, g)

let apply = fold_left1 mk_app

let is_eq = function
  | Eq _ -> true
  | _ -> false

let map_formula fn = function
  | App (f, g) -> App (fn f, fn g)
  | Lambda (id, typ, f) -> Lambda (id, typ, fn f)
  | Eq (f, g) -> Eq (fn f, fn g)
  | f -> f

let rec fold_left_formula fn acc = function
  | App (f, g) | Eq (f, g) ->
      let acc = fold_left_formula fn acc f in
      fold_left_formula fn acc g
  | Lambda (_, _, f) -> fold_left_formula fn acc f
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

let alpha_equiv =
  let rec equiv ((vars1, vars2) as vars) f g = match f, g with
    | Const (x, _xtyp), Const (y, _ytyp) -> x = y
    | Var (x, _xtyp), Var (y, _ytyp) ->
        index_of x vars1 = index_of y vars2
    | App (f1, g1), App (f2, g2) | Eq (f1, g1), Eq (f2, g2) ->
        equiv vars f1 f2 && equiv vars g1 g2
    | Lambda (x, xtyp, f), Lambda (y, ytyp, g) ->
        xtyp = ytyp && equiv (x :: vars1, y :: vars2) f g
    | _ -> false in
  equiv ([], [])

let mk_false = Const ("⊥", Bool)
let mk_true = Const ("⊤", Bool)

let _not f = App (Const ("¬", Fun (Bool, Bool)), f)

let logical_binary = ["∧"; "∨"; "→"]

let quant_type = Fun (Fun (Base "_", Bool), Bool)

let binop op typ f g = App (App (Const (op, typ), f), g) 
let binop_unknown op = binop op unknown_type

let logical_op op = binop op (Fun (Bool, Fun (Bool, Bool)))

let _and = logical_op "∧"
let _or = logical_op "∨"
let implies1 = logical_op "→"

let lambda id typ f = Lambda (id, typ, f)

let binder name id typ f = App (Const (name, quant_type), Lambda (id, typ, f))
let binder' name (id, typ) f = binder name id typ f

let _for_all = binder "∀"
let _for_all' = binder' "∀"

let _exists = binder "∃"

let mk_neq f g = _not (mk_eq f g)

type formula_kind =
  | Not of formula
  | Binary of id * formula * formula
  | Quant of id * id * typ * formula
  | Other of formula

let fkind boolean = function
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

let find_vars only_free f =
  let rec find = function
    | Const _ -> []
    | Var (id, _) -> [id]
    | App (t, u) | Eq (t, u) -> find t @ find u
    | Lambda (id, _, t) ->
        if only_free then remove id (find t)
        else id :: find t in
  unique (find f)

let all_vars = find_vars false
let free_vars = find_vars true

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

let rec rename id avoid =
  if mem id avoid then rename (id ^ "'") avoid else id
  
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
  
let rec reduce = function
  | App (f, g) -> (match reduce f, reduce g with
      | Lambda (x, _typ, f), g -> reduce (subst1 f g x)
      | Const ("¬", _), Const ("⊤", Bool) -> mk_false
      | Const ("¬", _), Const ("⊥", Bool) -> mk_true
      | App(Const ("→", _), Const("⊤", Bool)), g -> g
      | App(Const ("→", _), Const("⊥", Bool)), _ -> mk_true
      | f, g -> App (f, g))
  | Lambda (id, typ, f) -> Lambda (id, typ, reduce f)
  | Eq (f, g) ->
      let f, g = reduce f, reduce g in
      if f = g then mk_true else Eq (f, g)
  | f -> f

let simp = function
  | Lambda (id, typ, App (f, Var (id', typ'))) when id = id' && typ = typ' ->
      f  (* η-reduction *)
  | f -> f

let unify =
  let rec unify' subst t u = match simp t, simp u with
    | Const (c, typ), Const (c', typ') ->
        if c = c' && typ = typ' then Some subst else None
    | Var (x, typ), f | f, Var (x, typ) ->
        if typ = type_of f then
          let f = subst_n subst f in
          if mem x (free_vars f) then None else
            let subst = subst |> map (fun (y, g) -> (y, subst1 g f x)) in
            Some ((x, f) :: subst)
        else None
    | App (f, g), App (f', g') | Eq (f, g), Eq (f', g') ->
        let* subst = unify' subst f f' in
        unify' subst g g'
    | _, _ -> None
  in unify' []

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

let rename_vars f =
  let num_vars = count_binders f in
  let start_var = char_to_string (
    if num_vars <= 3 then 'x' else
      let c = Char.chr (Char.code 'z' - num_vars + 1) in
      if c < 'q' then 'q' else c) in
  let rec rename names h = match h with
    | Const (id, typ) -> (Const (id, typ), names)
    | Var (id, typ) -> (Var (assoc id names, typ), names)
    | App (f, g) | Eq (f, g) ->
        let (f, names) = rename names f in
        let (g, names) = rename names g in
        (app_or_eq h f g, names)
    | Lambda (id, typ, f) ->
        let x = next_var (first_var start_var typ) (map snd names) in
        let (f, names) = rename ((id, x) :: names) f in
        (Lambda (x, typ, f), names) in
  fst (rename [] f)
  
(* statements *)

type proof_step =
  | Assert of formula
  | Let of id list * typ
  | LetVal of id * typ * formula
  | Assume of formula
  | IsSome of id * typ * formula
  | By of id * id list * id
      (* theorem/axiom name, outer vars, induction variable *)

let step_decl_vars = function
  | Let (ids, _) -> ids
  | LetVal (id, _, _) -> [id]
  | IsSome (id, _, _) -> [id]
  | _ -> []

let step_free_vars = function
  | Assert f -> free_vars f
  | LetVal (_, _, f) -> free_vars f
  | Assume f -> free_vars f
  | IsSome (id, _, f) -> remove id (free_vars f)
  | _ -> []

let show_proof_step = function
  | Assert f -> sprintf "assert %s" (show_formula f)
  | Let (ids, typ) -> sprintf "let %s : %s" (comma_join ids) (show_type typ)
  | LetVal (id, typ, f) -> sprintf "let %s : %s = %s"
      id (show_type typ) (show_formula f)
  | Assume f -> sprintf "assume %s" (show_formula f)
  | IsSome (id, typ, f) -> sprintf "exists %s : %s : %s"
      id (show_type typ) (show_formula f)
  | By (name, outer, var) ->
      let for_any =
        if outer = [] then ""
        else " for any " ^ comma_join outer in
      sprintf "by %s on %s%s" name var for_any

type proof =
  | Steps of proof_step list
  | Formulas of formula list

type statement =
  | TypeDecl of id
  | ConstDecl of id * typ
  | Axiom of id * formula * id option (* id, formula, name *)
  | Definition of id * typ * formula
  | Theorem of id * formula * proof option

let stmt_name = function
  | TypeDecl id -> "type " ^ id
  | ConstDecl (id, _) -> "const " ^ id
  | Axiom (id, _, _) -> "axiom " ^ id
  | Definition (id, _, _) -> "definition " ^ id
  | Theorem (id, _, _) -> "theorem " ^ id

let stmt_formula = function
  | Axiom (_, f, _) -> Some f
  | Definition (_, _, f) -> Some f
  | Theorem (_, f, _) -> Some f
  | _ -> None

let stmt_const = function
  | ConstDecl (id, _) -> Some id
  | Definition (id, _, _) -> Some id
  | _ -> None

let axiom_named name = function
  | Axiom (_id, f, Some n) when eq_icase n name -> Some f
  | _ -> None

let show_statement multi s =
  let show = show_formula_multi multi in
  stmt_name s ^ match s with
    | TypeDecl _ -> ""
    | ConstDecl (_, typ) -> sprintf " : %s" (show_type typ)
    | Axiom (_, f, _) -> sprintf ": %s" (show f)
    | Definition (_, typ, f) ->
        sprintf " : %s ; %s" (show_type typ) (show f)
    | Theorem (_, t, _) -> ":" ^
        (if multi then "\n" ^ indent_lines 2 (show t)
        else " " ^ show t)
