open MParser

open Logic

let char_to_string = String.make 1

let (<<?) p q = attempt (p << q)

let str s = spaces >>? attempt (string s)

let id = spaces >>? (letter |>> char_to_string <|> string "ℕ")

let sym = spaces >>? digit |>> char_to_string

let id_or_sym = id <|> sym

let type_operators = [
  [ Infix ((str "→" >>$ fun t u -> Fun (t, u)), Assoc_right) ]
]

let typ = expression type_operators (id |>> fun id -> Base id)

let rec formula s = choice [
  (sym |>> fun c -> Const (c, unknown_type));
  (pipe2 (id <<? str "(") (formula << str ")")
    (fun i f -> App (Var (i, unknown_type), f)));
  id |>> fun v -> Var (v, unknown_type)
 ] s

let subprop = choice [
  pipe2 (formula <<? str "=") formula (fun f g -> Eq (f, g))
]

let proposition = pipe3
  (str "There is no" >> id) (str ":" >> typ) (str "such that" >> subprop << str ".")
  (fun id typ p -> not (exists id typ p))

let decl =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 ((str "an element" <|> str "a function") >> id_or_sym) (str ":" >> typ)
    (fun c typ -> ConstDecl (c, typ))

let _and = str "and" <|> str "with"

let axiom_group = pipe2
  (str "Axiom." >> str "There exists" >> sep_by decl _and)
  (str "such that" >> str "a." >> proposition)
  (fun stmts stmt -> stmts @ [Axiom stmt])

let program = axiom_group

;;

match MParser.parse_channel program In_channel.stdin () with
  | Success prog ->
      List.iter (fun s -> print_endline (show_statement s)) prog
  | Failed (msg, _) ->
      failwith msg
