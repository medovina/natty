open Either
open List

open MParser
open MParser_RE

open Logic
open Proof
open Util

let any_line = skip_many_until any_char newline

let line s = spaces >>? string s << newline

let empty = spaces

let integer = empty >>? (many1_chars digit |>> int_of_string)

let str s = empty >>? string s

let between_str l r p = between (str l) (str r) p

let parens p = between_str "(" ")" p
let brackets p = between_str "[" "]" p
let quotes p = between_str "\"" "\"" p

let comma_sep1 p = sep_by1 p (str ",")

let comment = str "#" <|> str "/*" << any_line

let id_chars = many_chars (alphanum <|> char '_' <|> char '-')

let chars first = pipe2 first id_chars (fun c s -> char_to_string c ^ s)

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
  pipe2 (str s >> brackets (comma_sep1 arg) << str ":") term
    (build_quant mk)
and formula s = expression operators term s

let thf_type = id >> str ":" >> (skip (str "$tType") <|> skip typ)

let rec source s = choice [
  str "file" >> parens (pair (quoted_id << str ",") id) |>>
    (fun (filename, id) -> File (filename, id));
  str "inference" >> parens (pipe3 id
    (str "," >> str "[status(" >> id << str ")],")
    (brackets (sep_by source (str ",")))
    (fun name status children -> Inference (name, status, children)));
  id |>> fun id -> Id id
] s

let clause_info = triple
  (str "\'" >> chars lowercase)
  (option (parens id_chars))
  (str "\'" >> (option (str "," >> str "info" >> parens (
    pipe2 integer (str "," >> integer)
      (fun proof_depth proof_size -> { proof_depth; proof_size })))))

let proof_clause = empty >>?
  str "thf" >> parens ( (id << str ",") >>= fun name ->
  choice [
    str "type" >> str "," >> thf_type >>$ [];
    pipe4 id (str "," >> formula) (str "," >> source)
      (opt ("", None, None) (str "," >> brackets clause_info))
      (fun role f source (info, arg, attributes) ->
        [{name; role; formula = f; source; info; arg; attributes}])
  ]) << str "."

let stat name =
  (skip_many_until any_line (string ("# " ^ name)) >> spaces >>
    str ":" >> spaces >> many_chars (digit <|> char '.'))

let szs_status = spaces >>? string "# SZS status " << any_line

let szs_theorem = line "# SZS status Theorem"

let heuristic_regexp = make_regexp {|\d\.\w+\([\w\d.,]+\)|}
let heuristic_eval = regexp heuristic_regexp

let proof_item = choice [
  (proof_clause |>> map mk_left);
  (str "# heuristic_def:" >> quotes (parens (comma_sep1 heuristic_eval)) |>>
    fun hs -> [Right hs]);
  comment >>$ []
]

let proof_file debug = pipe3
  (if debug > 1 then 
	  many (not_followed_by szs_status "" >> proof_item ) |>>
      concat |>> gather_left_right
   else
    many (not_followed_by szs_status "" >> any_line) >>$ ([], []))
  (option (pair
    (szs_theorem >> line "# SZS output start CNFRefutation" >>
     many_until proof_clause (line "# SZS output end CNFRefutation") |>> concat)
    (stat "Proof object total steps")))
  (stat "User time")
  (fun (clauses, hs) proof user_time ->
    { clauses; heuristic_def = nth_opt hs 0; proof; user_time })
;;

let parse debug text = MParser.parse_string (proof_file debug) text ()

let parse_file debug file = MParser.parse_channel (proof_file debug) (open_in file) ()
