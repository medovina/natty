open List
open Printf

open MParser

open Logic
open Util

let (<<?) p q = attempt (p << q)

let triple p q r = pair p (pair q r) |>> fun (x, (y, z)) -> (x, y, z)

let opt_fold p q f = p >>= fun x -> opt x (q |>> f x)

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  empty >>? satisfy match_first >>? string (string_from s 1) >>$ s

let any_str ss = choice (map str ss)

let var = empty >>? (letter |>> char_to_string)

let id = var <|> any_str ["𝔹"; "ℕ"]

let sym = (empty >>? (digit <|> char '+') |>> char_to_string) <|> str "·"

let id_or_sym = id <|> sym

let word = empty >>? many1_chars letter

(* types *)

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let type_operators = [
  [ infix "→" (fun t u -> Fun (t, u)) Assoc_right ]
]

let typ = expression type_operators (id |>> fun id -> mk_base_type id)

let id_type = pair id (str ":" >> typ)

let ids_type = pair (sep_by1 id (str ",")) (str ":" >> typ)

(* terms *)

let rec term s = choice [
  (sym |>> fun c -> Const (c, unknown_type));
  (pipe2 (id <<? str "(") (expr << str ")")
    (fun i f -> App (Var (i, unknown_type), f)));
  var |>> (fun v -> Var (v, unknown_type));
  str "(" >> expr << str ")"
 ] s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left (binop "·") t next_term) s

(* expressions *)

and operators = [
  [ infix "·" (binop "·") Assoc_left ];
  [ infix "+" (binop "+") Assoc_left ];
  [ infix "=" mk_eq Assoc_right ; infix "≠" mk_neq Assoc_right ]
]

and expr s = (expression operators terms |>> multi_eq) s

let atomic = expr << optional (str "is true")

(* small propositions *)

let prop_operators = [
  [ infix "and" mk_and Assoc_left ];
  [ infix "or" mk_or Assoc_left ];
  [ infix "implies" implies Assoc_right ];
  [ Postfix (str "for all" >> id_type |>> for_all') ];
  [ Infix (str "," >>? str "and" >>$ mk_and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ mk_or, Assoc_left) ];
]

let small_prop = expression prop_operators atomic

(* propositions *)

let if_then_prop =
  pipe2 (str "if" >> small_prop << optional (str ",")) (str "then" >> small_prop)
    implies

let rec for_all_prop s = pipe2
  (str "For all" >> ids_type) (str "," >> proposition) for_all_n s

and exists_prop s = pipe3
  (str "There is" >> ((str "some" >>$ true) <|> (str "no" >>$ false)))
  id_type (str "such that" >> proposition)
  (fun some (id, typ) p ->
    (if some then Fun.id else mk_not) (exists id typ p)) s

and proposition s = choice [
  for_all_prop; exists_prop; if_then_prop; small_prop
] s

(* top propositions *)

let rec let_prop s = pipe2 (str "Let" >> id_type << str ".") top_prop for_all' s

and suppose s = pipe2
  (str "Suppose that" >> sep_by1 proposition (str ", and that") << str ".")
  (str "Then" >> proposition)
  (fold_right implies) s

and top_prop s = (let_prop <|> suppose <|> proposition) s

(* proposition lists *)

let label = empty >>?
  ((letter |>> char_to_string) <|> many1_chars digit) <<? string "."

let proposition_item = triple
  label (top_prop << str ".") (option (str "(" >> word << str ")"))

let prop_items = many1 proposition_item

let top_prop_or_items ids_typ =
  (prop_items <|> (top_prop << str "." |>> fun f -> [("", f, None)])) |>>
    map (fun (label, f, name) -> (label, for_all_n' ids_typ f, name))

let propositions =
  (opt ([], unknown_type) (str "for all" >> ids_type << str ",")) >>=
    top_prop_or_items

(* axioms *)

let axiom_decl =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 (any_str ["an element"; "a function"; "a binary operation"] >> id_or_sym)
    (str ":" >> typ)
    (fun c typ -> ConstDecl (c, typ))

let count_label c label =
  if label = "" then sprintf "%d" !c
  else sprintf "%d_%s" !c label

let axiom_group = str "Axiom." >> any_str ["There exists"; "There is"] >> pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  (str "such that" >> pipe2 propositions get_user_state
    (fun props (ax, _) -> incr ax;
      props |> map (fun (label, f, name) ->
        Axiom (count_label ax label, f, name))))
  (@)

(* definitions *)

let definition = pipe3
  (str "Definition." >> str "Let" >> sym) (str ":" >> typ)
  (str "=" >> term << str ".")
  (fun sym typ f -> [Definition (sym, typ, Eq (Const (sym, typ), f))])

(* theorems *)

let proof_item = pair label
  (pipe2 (str "By" >> word) (str "on" >> var << str ".")
    (fun w v -> By (w, v)))

let proofs = str "Proof." >> many1 proof_item

let theorem_group = (str "Lemma." <|> str "Theorem.") >>
  str "Let" >> ids_type << str "." >>=
  fun ids_typ -> pipe3 (top_prop_or_items ids_typ) (opt [] proofs) get_user_state
    (fun props proofs (_, th) -> incr th;
      props |> map (fun (label, f, _name) ->
        Theorem (count_label th label, f, assoc_opt label proofs)))

(* program *)

let program =
  many (axiom_group <|> definition <|> theorem_group) << empty << eof |>> concat

let parse in_channel = MParser.parse_channel program in_channel (ref 0, ref 0)
