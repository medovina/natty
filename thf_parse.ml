open MParser
open Printf

open Logic
open Statement
open Util

type 'a p = ('a, unit) t   (* parser type *)

let comment = (any_of "%#" >> skip_many_until any_char newline)
  <|> (string "/*" >> skip_many_until any_char (string "*/"))

let empty = skip_many (skip space <|> comment)

let str s = empty >>? string s

let between_str l r p = between (str l) (str r) p

let parens p = between_str "(" ")" p
let brackets p = between_str "[" "]" p
let quotes p = between_str "\"" "\"" p

let comma_sep1 p = sep_by1 p (str ",")

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

let pi_arg = var << str ":" << str "$tType"

let rec type_term s = choice [
  parens typ;
  str "$o" >>$ Bool;
  str "$tType" >>$ Type;
  id |>> (fun id -> Base id);
  var |>> (fun id -> TypeVar id);
  pipe2 (str "!>" >> brackets (sep_by1 pi_arg (str ",")))
        (str ":" >> type_term)
        (fun ids typ -> fold_right mk_pi_type ids typ)
  ] s
and typ s = expression type_operators type_term s

(* formulas *)

let eq = empty >>? attempt (char '=' >> not_followed_by (char '>') "")

let operators = [
  [ infix "@" (fun f g -> App (f, g)) Assoc_left ];
  [ infix1 eq mk_eq Assoc_left;
    infix "!=" mk_neq Assoc_left ];
  [ infix "&" _and Assoc_left ];
  [ infix "|" _or Assoc_left ];
  [ infix "=>" implies1 Assoc_left ];
  [ infix "<=>" _iff Assoc_left ]
]

let arg = pair (var << str ":") typ

let build_quant quant args formula =
  let rec f = function
    | ((id, typ) :: args) -> quant id typ (f args)
    | [] -> formula
  in f args

let rec term s = choice [
  parens formula;
  str "$false" >>$ _false;
  str "$true" >>$ _true;
  id |>> _const;
  var |>> _var;
  (str "~" >> term) |>> _not;
  quantifier "!" _for_all;
  quantifier "?" _exists;
  quantifier "^" lambda
  ] s
and quantifier s mk =
  pipe2 (str s >> brackets (comma_sep1 arg) << str ":") term
    (build_quant mk)
and formula s = expression operators term s

let thf_type : statement p = id << str ":" >>= fun id ->
   (str "$tType" >>$ TypeDecl (id, None)) <|>
   (typ |>> fun typ -> ConstDecl (id, typ))

let thf_formula : statement p = empty >>?
  str "thf" >> parens (
    pair (id << str ",") (id << str ",") >>= fun (name, role) ->
      match role with
        | "type" -> thf_type
        | "axiom" | "definition" | "theorem"  ->
            formula |>> fun f -> Axiom (name, f, None)
        | "hypothesis" ->
            formula |>> fun f -> Hypothesis (name, f)
        | "conjecture" ->
            formula |>> fun f -> Theorem (name, None, f, [], empty_range)
        | _ -> failwith "unknown role")
  << str "."

let _include = str "include" >> parens quoted_id << str "."

let thf_file : statement list p =
  many _include >> many thf_formula << empty << eof

let relative_name from f = mk_path (Filename.dirname from) f

let parse_thf source : (_module list, string * frange) Stdlib.result =
  let rec parse source : (statement list, string * frange) Stdlib.result =
    let text = read_file source in
    let inc : str list =
      map (relative_name source) (always_parse (many _include) text ()) in
    let** inc_stmts = map_res parse inc in
    match MParser.parse_string thf_file text () with
      | Success stmts -> Ok (concat inc_stmts @ stmts)
      | Failed (err, Parse_error ((_index, line, col), _)) ->
          Error (err, (source, ((line, col), (0, 0))))
      | _ -> failwith "parse_thf" in
  let** stmts = parse source in
  Ok [{ filename = source; using = []; stmts; syntax_map = [] }]

type derivation =
  | Step of id
  | Inference of id * derivation list
  | File

let rec derivation s = choice [
  str "inference" >> parens (
    pipe2
      (id << char ',' << brackets (str "status" >> parens id) << char ',')
      (brackets (comma_sep1 derivation))
      (fun id derivs -> Inference (id, derivs)));
  str "file" >> parens (quoted_id << str "," << id) >>$ File;
  (id |>> fun id -> Step id)
] s

let proof_formula = empty >>?
  str "thf" >> char '(' >> (
    pair (id << str ",") (id << str ",") >>= fun (id, role) ->
      if role = "type" then return []
      else pipe2 (formula << str ",") derivation (fun f deriv -> [(id, f, deriv)])
  ) << skip_many_until any_char newline

let parse_proof source =
  MParser.parse_channel (many proof_formula |>> concat) (open_in source) ()

let id_num id = remove_prefix "c_0_" id

let rec show_derivation = function
  | Step id -> id_num id
  | Inference (id, [d]) -> show_derivation d ^ ", " ^ id
  | Inference ("rw", [d; Step id]) ->
      show_derivation d ^ sprintf ", rw(%s)" (id_num id)
  | Inference (rule, [d1; d2]) ->
      sprintf "%s, %s, %s" (show_derivation d1) (show_derivation d2) rule
  | Inference _ -> failwith "show_derivation"
  | File -> "file"

let format_proof formulas =
  formulas |> iter (fun (id, f, deriv) ->
    printf "%s. %s [%s]\n" (id_num id) (show_formula f) (show_derivation deriv))
