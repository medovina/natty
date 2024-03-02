open List

open MParser

open Logic
open Util

type source =
  | Id of id
  | File of string * id  (* filename, id *)
  | Inference of id * id * source list  (* name, status, children *)

type proof_formula =
  ProofFormula of id * id * formula * source  (* name, role, formula, source *)

let any_line = skip_many_until any_char newline

let comment = char '#' << any_line

let empty = skip_many (space <|> comment)

let sym s = empty >>? string s

let parens p = sym "(" >> p << sym ")"

let brackets p = sym "[" >> p << sym "]"

let chars first = pipe2 first (many_chars (alphanum <|> char '_')) (fun c s ->
  char_to_string c ^ s)

let quoted_id = char '\'' >> many_chars_until any_char (char '\'')

let id = empty >>? (chars (lowercase <|> char '$') <|> quoted_id)

let var = empty >>? chars uppercase

let infix1 s f assoc = Infix (s >>$ f, assoc)

let infix s f assoc = infix1 (sym s) f assoc

(* types *)

let type_operators = [
  [ infix ">" (fun t u -> Fun (t, u)) Assoc_right ]
]

let rec type_term s = choice [
  parens typ;
  sym "$i" >>$ Base "I";
  sym "$o" >>$ Bool;
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

let arg = pair (var << optional inline_comment << sym ":") typ

let build_quant quant args formula =
  let rec f = function
    | ((id, typ) :: args) -> quant id typ (f args)
    | [] -> formula
  in f args

let rec term s = choice [
  parens formula;
  id |>> (fun id -> Const (id, unknown_type));
  var |>> (fun id -> Var (id, unknown_type));
  (sym "~" >> term) |>> mk_not;
  quantifier "!" for_all;
  quantifier "?" exists;
  quantifier "^" lambda
  ] s
and quantifier s mk =
  pipe2 (sym s >> brackets (sep_by1 arg (sym ",")) << sym ":") term
    (build_quant mk)
and formula s = expression operators term s

let thf_type = id >> sym ":" >> (skip (sym "$tType") <|> skip typ)

let rec source s = choice [
  sym "file" >> parens (pair (quoted_id << sym ",") id) |>>
    (fun (filename, id) -> File (filename, id));
  sym "inference" >> parens (pipe3 id
    (sym ",[status(" >> id << sym ")],")
    (brackets (sep_by source (sym ",")))
    (fun name status children -> Inference (name, status, children)));
  id |>> fun id -> Id id
] s

let proof_formula = sym "thf" >> parens ( (id << sym ",") >>= fun name ->
  choice [
    sym "type" >> sym "," >> thf_type >>$ [];
    pipe3 id (sym "," >> formula)
      (sym "," >> source << optional (sym "," >> brackets quoted_id))
      (fun role f source -> [ProofFormula (name, role, f, source)])
  ]) << sym "."

let line s = string s << newline

let proof_file = skip_many_until any_line (line "# SZS status Theorem") >>
  line "# SZS output start CNFRefutation" >>
  pair (many1 proof_formula |>> List.concat)
  (skip_many_until any_line (string "# Proof object total steps") >> spaces >>
    sym ":" >> spaces >> many_chars digit)
;;

let parse text = MParser.parse_string (option proof_file) text ()
