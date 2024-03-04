open List

open MParser

open Logic
open Proof
open Util

let any_line = skip_many_until any_char newline

let comment = char '#' << any_line

let empty = skip_many (space <|> comment)

let str s = empty >>? string s

let parens p = str "(" >> p << str ")"

let brackets p = str "[" >> p << str "]"

let chars first = pipe2 first (many_chars (alphanum <|> char '_')) (fun c s ->
  char_to_string c ^ s)

let quoted_id = char '\'' >> many_chars_until any_char (char '\'')

let id = empty >>? (chars lowercase <|> quoted_id)

let var = empty >>? chars uppercase

let infix1 s f assoc = Infix (s >>$ f, assoc)

let infix s f assoc = infix1 (str s) f assoc

(* types *)

let type_operators = [
  [ infix ">" (fun t u -> Fun (t, u)) Assoc_right ]
]

let rec type_term s = choice [
  parens typ;
  str "$i" >>$ Base "I";
  str "$o" >>$ Bool;
  str "nat" >>$ Base "ℕ";
  id |>> fun id -> Base id
  ] s
and typ s = expression type_operators type_term s

(* formulas *)

let eq = empty >>? attempt (char '=' >> not_followed_by (char '>') "")

let operators = [
  [ infix "@" (fun f g -> App (f, g)) Assoc_left ];
  [ infix1 eq mk_eq Assoc_left;
    infix "!=" mk_neq Assoc_left ];
  [ infix "&" mk_and Assoc_left ];
  [ infix "|" mk_or Assoc_left ];
  [ infix "=>" implies1 Assoc_left ];
  (* [ infix "<=>" (fun f g -> Iff (f, g)) Assoc_left ] *)
]

let inline_comment = string "/*" >> skip_many_until any_char (string "*/")

let arg = pair (var << optional inline_comment << str ":") typ

let build_quant quant args formula =
  let rec f = function
    | ((id, typ) :: args) -> quant id typ (f args)
    | [] -> formula
  in f args

let rec term s = choice [
  parens formula;
  str "$false" >>$ mk_false;
  str "$true" >>$ mk_true;
  str "'*'" >>$ Const ("·", unknown_type);
  id |>> (fun id -> Const (id, unknown_type));
  var |>> (fun id -> Var (id, unknown_type));
  (str "~" >> term) |>> mk_not;
  quantifier "!" mk_for_all;
  quantifier "?" exists;
  quantifier "^" lambda
  ] s
and quantifier s mk =
  pipe2 (str s >> brackets (sep_by1 arg (str ",")) << str ":") term
    (build_quant mk)
and formula s = expression operators term s

let thf_type = id >> str ":" >> (skip (str "$tType") <|> skip typ)

let rec source s = choice [
  str "file" >> parens (pair (quoted_id << str ",") id) |>>
    (fun (filename, id) -> File (filename, id));
  str "inference" >> parens (pipe3 id
    (str ",[status(" >> id << str ")],")
    (brackets (sep_by source (str ",")))
    (fun name status children -> Inference (name, status, children)));
  id |>> fun id -> Id id
] s

let proof_clause = str "thf" >> parens ( (id << str ",") >>= fun name ->
  choice [
    str "type" >> str "," >> thf_type >>$ [];
    pipe3 id (str "," >> formula)
      (str "," >> source << optional (str "," >> brackets quoted_id))
      (fun role f source -> [(name, role, f, source)])
  ]) << str "."

let line s = string s << newline

let stat name =
  (skip_many_until any_line (string ("# " ^ name)) >> spaces >>
    str ":" >> spaces >> many_chars (digit <|> char '.'))

let proof_file = skip_many_until any_line (line "# SZS status Theorem") >>
  line "# SZS output start CNFRefutation" >>
  triple (many1 proof_clause |>> List.concat)
    (stat "Proof object total steps") (stat "User time")
;;

let parse text = MParser.parse_string (option proof_file) text ()
