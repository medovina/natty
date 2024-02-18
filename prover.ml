open MParser

open Logic
open Util

let (<<?) p q = attempt (p << q)

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  spaces >>? satisfy match_first >>? string (string_from s 1) >>$ s

let any_str ss = choice (List.map str ss)

let id = (spaces >>? letter |>> char_to_string) <|> any_str ["𝔹"; "ℕ"]

let sym = spaces >>? (digit <|> char '+') |>> char_to_string

let id_or_sym = id <|> sym

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let type_operators = [
  [ infix "→" (fun t u -> Fun (t, u)) Assoc_right ]
]

let typ = expression type_operators (id |>> fun id -> Base id)

let id_typ = pair id (str ":" >> typ)

let ids_typ = pair (sep_by1 id (str ",")) (str ":" >> typ)

let operators = [
  [ infix "+" (binop "+") Assoc_left ]
]

let rec term s = choice [
  (sym |>> fun c -> Const (c, unknown_type));
  (pipe2 (id <<? str "(") (expr << str ")")
    (fun i f -> App (Var (i, unknown_type), f)));
  id |>> fun v -> Var (v, unknown_type)
 ] s

and expr s = expression operators term s

let atomic = choice [
  pipe2 (expr <<? str "=") expr (fun f g -> Eq (f, g));
  expr << optional (str "is true")
]

let small_prop = pipe2 (choice [
  pipe2 (atomic <<? str "implies") atomic implies;
  atomic
  ]) (option (str "for all" >> id_typ))
  (fun p all_opt -> Option.fold all_opt ~none:p ~some:(fun id_typ -> for_all' id_typ p))

let if_then_prop =
  pipe2 (str "if" >> small_prop) (str "then" >> small_prop) implies

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

let proposition_item = spaces >>? letter >>? string "." >> top_prop << str "."

let propositions = (opt ([], unknown_type) (str "for all" >> ids_typ << str ",")) >>=
  (fun ids_typ -> many1 proposition_item |>> List.map (for_all_n' ids_typ))

let axiom_decl =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 (any_str ["an element"; "a function"; "a binary operation"] >> id_or_sym)
    (str ":" >> typ)
    (fun c typ -> ConstDecl (c, typ))

let axiom_group = str "Axiom." >> any_str ["There exists"; "There is"] >> pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  (str "such that" >> propositions |>> List.map (fun p -> Axiom p))
  (@)

let program = many axiom_group |>> List.concat

;;

match MParser.parse_channel program In_channel.stdin () with
  | Success prog ->
      List.iter (fun s -> print_endline (show_statement s)) prog
  | Failed (msg, _) ->
      failwith msg
