open MParser
open Printf

open Logic
open Util

let (<<?) p q = attempt (p << q)

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  empty >>? satisfy match_first >>? string (string_from s 1) >>$ s

let any_str ss = choice (List.map str ss)

let var = letter |>> char_to_string

let id = (empty >>? var) <|> any_str ["𝔹"; "ℕ"]

let sym = (empty >>? (digit <|> char '+') |>> char_to_string) <|> str "·"

let id_or_sym = id <|> sym

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let type_operators = [
  [ infix "→" (fun t u -> Fun (t, u)) Assoc_right ]
]

let typ = expression type_operators (id |>> fun id -> mk_base_type id)

let id_typ = pair id (str ":" >> typ)

let ids_typ = pair (sep_by1 id (str ",")) (str ":" >> typ)

let operators = [
  [ infix "·" (binop "·") Assoc_left ];
  [ infix "+" (binop "+") Assoc_left ];
  [ infix "=" mk_eq Assoc_right ; infix "≠" mk_neq Assoc_right ]
]

let rec term s = choice [
  (sym |>> fun c -> Const (c, unknown_type));
  (pipe2 (id <<? str "(") (expr << str ")")
    (fun i f -> App (Var (i, unknown_type), f)));
  empty >>? var |>> (fun v -> Var (v, unknown_type));
  str "(" >> expr << str ")"
 ] s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left (binop "·") t next_term) s

and expr s = (expression operators terms |>> multi_eq) s

let atomic = expr << optional (str "is true")

let small_prop = pipe2 (choice [
  pipe2 (atomic <<? str "implies") atomic implies;
  atomic
  ]) (option (str "for all" >> id_typ))
  (fun p all_opt -> Option.fold all_opt ~none:p ~some:(fun id_typ -> for_all' id_typ p))

let if_then_prop =
  pipe2 (str "if" >> small_prop << optional (str ",")) (str "then" >> small_prop)
    implies

let rec for_all_prop s = pipe2
  (str "For all" >> ids_typ) (str "," >> proposition) for_all_n s

and not_exists_prop s = pipe2
  (str "There is no" >> id_typ) (str "such that" >> proposition)
  (fun (id, typ) p -> not (exists id typ p)) s

and proposition s = choice [
  for_all_prop; not_exists_prop; if_then_prop; small_prop
] s

let rec let_prop s = pipe2 (str "Let" >> id_typ << str ".") top_prop for_all' s

and suppose s = pipe2
  (str "Suppose that" >> sep_by1 proposition (str ", and that") << str ".")
  (str "Then" >> proposition)
  (List.fold_right implies) s

and top_prop s = (let_prop <|> suppose <|> proposition) s

let label = (letter |>> char_to_string) <|> many1_chars digit

let proposition_item = empty >>? pair (label <<? string ".") (top_prop << str ".")

let prop_items ids_typ = many1 proposition_item |>>
  List.map (fun (label, f) -> (label, for_all_n' ids_typ f))

let propositions =
  (opt ([], unknown_type) (str "for all" >> ids_typ << str ",")) >>= prop_items

let axiom_decl =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 (any_str ["an element"; "a function"; "a binary operation"] >> id_or_sym)
    (str ":" >> typ)
    (fun c typ -> ConstDecl (c, typ))

let mk_stmts count mk = incr count;
  List.map (fun (label, f) -> mk (sprintf "%d_%s" !count label) f)

let axiom_group = str "Axiom." >> any_str ["There exists"; "There is"] >> pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  (str "such that" >> pipe2 propositions get_user_state
    (fun props (ax, _) -> mk_stmts ax mk_axiom props))
  (@)

let definition = pipe3
  (str "Definition." >> str "Let" >> sym) (str ":" >> typ)
  (str "=" >> term << str ".")
  (fun sym typ f -> [Definition (sym, typ, Eq (Const (sym, typ), f))])

let theorem_group = (str "Theorem." >> str "Let" >> ids_typ << str ".") >>=
  fun ids_typ -> pipe2 (prop_items ids_typ) get_user_state
    (fun props (_, th) -> mk_stmts th mk_theorem props)

let program = many (axiom_group <|> definition <|> theorem_group) |>> List.concat

let parse in_channel = MParser.parse_channel program in_channel (ref 0, ref 0)
