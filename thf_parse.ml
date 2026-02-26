open MParser
open Printf

open Logic
open Module
open Statement
open Util

type 'a p = ('a, unit) t   (* parser type *)
type 'a pr = ('a, unit) reply

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

let sq_char : char p = choice [
  string "\\'" >>$ '\'';
  string "\\\\" >>$ '\\';
  any_char
]

let quoted_id : string p =
  char '\'' >> (many_until sq_char (char '\'') |>> chars_to_string)

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
  id |>> base_type;
  var |>> (fun id -> TypeVar id);
  pipe2 (str "!>" >> brackets (comma_sep1 pi_arg))
        (str ":" >> type_term)
        (fun ids typ -> fold_right mk_pi_type ids typ)
  ] s
and typ s = expression type_operators type_term s

(* formulas *)

let eq = empty >>? attempt (char '=' >> not_followed_by (char '>') "")

let operators = [
  [ infix "@" app Assoc_left ];
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
  attempt (parens (formula));
  str "$false" >>$ _false;
  str "$true" >>$ _true;
  id |>> _const;
  var |>> _var;
  (str "~" >> term) |>> _not;
  quantifier "!" _for_all;
  quantifier "?" _exists;
  quantifier "^" lambda;
  typ |>> type_const
  ] s
and quantifier s mk =
  pipe2 (str s >> brackets (comma_sep1 arg) << str ":") term
    (build_quant mk)
and formula s = expression operators term s

let thf_type : (id * statement) p = id << str ":" >>= fun id ->
   (str "$tType" >>$ (id, mk_const_decl id Type)) <|>
   (typ |>> fun typ -> (id, mk_const_decl id typ))

type thm_info = stmt_ref list * bool  (* by, is_step *)

let extra_item : (thm_info -> thm_info) p = choice [
  str "step" >>$ (fun (by, _) -> (by, true));
  let$ ids = str "by" >> parens (brackets (comma_sep1 id)) in
  let refs = let& id = ids in LabelRef ("_", id) in
  fun (_, is_step) -> (refs, is_step)]

let thf_formula last_const : (id option * statement) p = empty >>?
  str "thf" >> parens (
    let> label, role = pair (id << str ",") (id << str ",") in
    match role with
      | "type" ->
          let$ (id, stmt) = thf_type in (Some id, stmt)
      | _ ->
        let p = match role with
          | "axiom" | "theorem"  ->
              formula |>> fun f ->
                Axiom {
                  label; formula = f; name = None;
                  defined = if role = "axiom"
                            then let* c = last_const in Some (c, unknown_type) else None }
          | "definition" ->
              formula |>> fun f ->
                Definition { label; id = opt_get last_const; typ = unknown_type; formula = f }
          | "hypothesis" ->
              formula |>> fun f -> Hypothesis { label; formula = f; name = None }
          | "conjecture" ->
              let> f = formula in
              let$ extras =
                opt [] (str "," >> str "file," >> brackets (comma_sep1 extra_item)) in
              let (by, is_step) = (fold_left Fun.compose Fun.id extras) ([], false) in
              Theorem { label; name = None; formula = f; steps = [];
                        by; is_step; range = empty_range; on_contra_path = false }
          | _ -> failwith "unknown role" in
        p |>> fun x -> ((if role = "axiom" || role = "definition" then last_const else None), x))
  << str "."

let _include = str "include" >> parens quoted_id << str "."

let rec formulas last_const : statement list p =
  opt [] (
    let> (last_const, stmt) = thf_formula last_const in
    let$ rest = formulas last_const in
    stmt :: rest)

let thf_file : statement list p =
  many _include >> formulas None << empty << eof

let parse_thf source : (smodule list, string * frange) Stdlib.result =
  parse_modules (many _include) thf_file [source] [] true

let reformat_proof source parser formatter =
  match parser source with
    | Failed (msg, _) -> print_endline msg
    | Success formulas -> formatter formulas

(* Parsing output from E *)

type e_derivation =
  | Step of id
  | Inference of id * e_derivation list
  | File

let rec e_derivation s = choice [
  str "inference" >> parens (
    pipe2
      (id << char ',' << brackets (str "status" >> parens id) << char ',')
      (brackets (comma_sep1 e_derivation))
      (fun id derivs -> Inference (id, derivs)));
  str "file" >> parens (quoted_id << str "," << id) >>$ File;
  (id |>> fun id -> Step id)
] s

let e_formula : (id * formula * e_derivation) list p = empty >>?
  str "thf" >> char '(' >> (
    pair (id << str ",") (id << str ",") >>= fun (id, role) ->
      if role = "type" then return []
      else pipe2 (formula << str ",") e_derivation (fun f deriv -> [(id, f, deriv)])
  ) << skip_many_until any_char newline

let parse_e_proof source : (id * formula * e_derivation) list result =
  MParser.parse_channel ((many e_formula << empty << eof) |>> concat) (open_in source) ()

let id_num id = remove_prefix "c_0_" id

let rec show_e_derivation = function
  | Step id -> id_num id
  | Inference (id, [d]) -> show_e_derivation d ^ ", " ^ id
  | Inference ("rw", [d; Step id]) ->
      show_e_derivation d ^ sprintf ", rw(%s)" (id_num id)
  | Inference (rule, [d1; d2]) ->
      sprintf "%s, %s, %s" (show_e_derivation d1) (show_e_derivation d2) rule
  | Inference _ -> failwith "show_derivation"
  | File -> "file"

let format_e_proof formulas =
  formulas |> iter (fun (id, f, deriv) ->
    printf "%s. %s [%s]\n" (id_num id) (show_formula f) (show_e_derivation deriv))

(* Parsing output from Vampire *)

let v_formula : (int * formula * string) p = empty >>?
  let> n = many1_chars digit << char '.' in
  let> f = formula in
  let$ s = str "[" >> many_chars_until any_char (char ']') in
  (int_of_string n, f, s)

let parse_v_proof source : (int * formula * string) list result =
  MParser.parse_channel (many v_formula << empty << eof) (open_in source) ()

let rec simplify_true f = match f with
   | Eq (Const ("%⊤", _, _), g)
   | Eq (g, Const ("%⊤", _, _)) -> simplify_true g
   | f -> map_formula simplify_true f

let format_v_proof formulas =
  formulas |> iter (fun (n, f, deriv) ->
    printf "%d. %s [%s]\n" n (show_formula (simplify_true f)) deriv)
