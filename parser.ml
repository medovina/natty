open List
open Printf

open MParser

open Logic
open Statement
open Util

let (<<?) p q = attempt (p << q)
let (>>=?) p q = attempt (p >>= q)

let opt_fold p q f = p >>= fun x -> opt x (q |>> f x)

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let number = empty >>? many1_chars digit

let int = number |>> int_of_string

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  empty >>? satisfy match_first >>? string (string_from s 1) >>$ s

let opt_str s = optional (str s)

let any_str ss = choice (map str ss)

let var = empty >>? (letter |>> char_to_string)

let id = var <|> any_str ["𝔹"; "ℕ"]

let sym =
  (empty >>? (digit <|> any_of "+-<>") |>> char_to_string) <|>
    any_str ["·"; "≤"; "≥"; "≮"]

let id_or_sym = id <|> sym

let word = empty >>? many1_chars letter

(* types *)

let of_type = any_str [":"; "∈"]

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let type_operators = [
  [ infix "→" (fun t u -> Fun (t, u)) Assoc_right ]
]

let typ = expression type_operators (id |>> fun id -> mk_base_type id)

let id_type = pair id (of_type >> typ)

let id_opt_type = pair id (opt unknown_type (of_type >> typ))

let ids_type = pair (sep_by1 id (str ",")) (of_type >> typ)

(* operators for small propositions *)

let theorem_num =
  number >> (many (char '.' >>? number)) >>$ "" 

let theorem_ref = choice [
  any_str ["lemma"; "theorem"] >> theorem_num;
  str "part" >> str "(" >> number << str ")" << opt_str "of this theorem" ]

let reason = str "by" >>? (theorem_ref <|> str "hypothesis")

let so = any_str ["hence"; "so"; "then"; "therefore"] <|>
  (str "which implies" << opt_str "that")

let have = any_str 
  ["clearly"; "the only alternative is";
   "we conclude that"; "we deduce that"; "we have";
   "we know that"; "we must have"; "we see that"] <|>
   (any_str ["it follows"; "it then follows"] >>
      optional reason >> str "that")

let so_or_have = so <|> (optional reason >> have)

let comma_and = str "," >>? str "and" <<? not_followed_by so_or_have ""

let prop_operators = [
  [ infix "and" _and Assoc_left ];
  [ infix "or" _or Assoc_left ];
  [ infix "implies" implies Assoc_right ];
  [ Postfix (str "for all" >> id_type |>> _for_all') ];
  [ infix "if and only if" _iff Assoc_right ];
  [ Infix (comma_and >>$ _and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ _or, Assoc_left) ];
]

(* terms *)

let compare_op op = infix op (binop_unknown op) Assoc_right

let mk_not_less f g = _not (binop_unknown "<" f g)

let rec term s = choice [
  (sym |>> fun c -> Const (c, unknown_type));
  (pipe2 (id <<? str "(") (expr << str ")")
    (fun i f -> App (Var (i, unknown_type), f)));
  var |>> (fun v -> Var (v, unknown_type));
  str "(" >> expr << str ")";
  pipe3 (str "{" >> var) (of_type >> typ) (str "|" >> proposition << str "}")
    (fun var typ expr -> Lambda (var, typ, expr))
 ] s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left (binop_unknown "·") t next_term) s

(* expressions *)

and operators = [
  [ infix "·" (binop_unknown "·") Assoc_left ];
  [ infix "+" (binop_unknown "+") Assoc_left;  infix "-" (binop_unknown "-") Assoc_left ];
  [ infix "∈" (binop_unknown "∈") Assoc_none ];
  [ infix "=" mk_eq Assoc_right ; infix "≠" mk_neq Assoc_right ] @
      map compare_op ["<"; "≤"; ">"; "≥"] @
      [ infix "≮" mk_not_less Assoc_right ]
]

and expr s = (expression operators terms |>> chain_ops) s

and atomic s =
  (expr << optional (any_str ["is true"; "always holds"])) s

(* small propositions *)

and small_prop s = expression prop_operators atomic s

(* propositions *)

and if_then_prop s =
  pipe2 (str "if" >> small_prop << opt_str ",") (str "then" >> small_prop)
    implies s

and either_or_prop s =
  (str "either" >> small_prop |>> fun f -> match bool_kind f with
    | Binary ("∨", _, _, _) -> f
    | _ -> failwith "either: expected or") s

and for_all_ids s = (str "For all" >> ids_type << str ",") s

and for_all_prop s = pipe2
  for_all_ids proposition for_all_vars_typ s

and exists_prop s = pipe3
  (str "There is" >> ((str "some" >>$ true) <|> (str "no" >>$ false)))
  id_type (str "such that" >> proposition)
  (fun some (id, typ) p ->
    (if some then Fun.id else _not) (_exists id typ p)) s

and precisely_prop s = (
  str "Precisely one of" >> small_prop << str "holds" |>> fun f ->
    let gs = gather_or f in
    assert (length gs > 1);
    let ns = all_pairs gs |> map (fun (f, g) -> _not (_and f g)) in
    fold_left1 _and (f :: ns)
  ) s

and cannot_prop s = (
  str "It cannot be that" >> proposition |>> _not) s

and proposition s = choice [
  for_all_prop; exists_prop; if_then_prop;
  either_or_prop; precisely_prop; cannot_prop;
  small_prop
] s

(* top propositions *)

let rec let_prop s = pipe2 (str "Let" >> id_type << str ".") top_prop _for_all' s

and suppose s = pipe2
  (str "Suppose that" >> sep_by1 proposition (str ", and that") << str ".")
  (str "Then" >> proposition)
  (fold_right implies) s

and top_prop s = (let_prop <|> suppose <|> proposition) s

(* proposition lists *)

let label = 
  ((empty >>? letter |>> char_to_string) <|> number) <<? string "."

let proposition_item = triple
  label (top_prop << str ".") (option (str "(" >> word << str ")"))

let prop_items = many1 proposition_item

let top_prop_or_items ids_typ =
  (prop_items <|> (top_prop << str "." |>> fun f -> [("", f, None)])) |>>
    map (fun (label, f, name) -> (label, for_all_vars_typ_if_free ids_typ f, name))

let propositions =
  (opt ([], unknown_type) for_all_ids) >>= top_prop_or_items

(* axioms *)

let axiom_decl =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 (any_str ["an element"; "a function"; "a binary operation"] >> id_or_sym)
    (of_type >> typ)
    (fun c typ -> ConstDecl (c, typ))

let count_label n label =
  if label = "" then sprintf "%d" n
  else sprintf "%d.%s" n label

let axiom_propositions n = propositions |>>
  map (fun (label, f, name) -> Axiom (count_label n label, f, name))

let axiom_group = (str "Axiom" >> int << str ".") >>= fun n ->
  any_str ["There exists"; "There is"] >> pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  ((str "such that" >> axiom_propositions n) <|> (str "." >>$ []))
  (@)

(* definitions *)

let eq_definition = pipe3
  (str "Let" >> sym) (str ":" >> typ) (str "=" >> term << str ".")
  mk_eq_def

let relation_definition (ids, typ) = opt_str "we write" >>?
  id >>=? fun x ->
    pipe3 sym id (str "iff" >> proposition) (fun op y prop ->
    assert (ids = [x; y]);
    mk_eq_def op (Fun (typ, Fun (typ, Bool)))
      (Lambda (x, typ, Lambda (y, typ, prop)))) << str "."

let definition = str "Definition." >>
  choice [
    single eq_definition;
    for_all_ids >>= fun ids_typ -> many1 (relation_definition ids_typ)
  ]

(* proofs *)

let mk_step f =
  match kind f with
    | Quant ("∃", x, typ, f) -> IsSome (x, typ, f)
    | _ -> mk_assert f

let opt_contra = opt []
  (str "," >>? opt_str "which is " >>?
    optional (any_str ["again"; "also"; "similarly"]) >>?
    str "a contradiction" >>
    (optional (str "to" >> theorem_ref)) >>$ [_false])

let rec proof_intro_prop = pipe2
  (reason >> opt_str "," >> optional have >> proposition) opt_contra cons

and proof_prop s = choice [
  proof_intro_prop;
  pipe2 (proposition << optional reason) opt_contra cons] s

let proof_if_prop = pipe3
  (str "if" >> small_prop)
  (opt_str "," >> str "then" >> proof_prop)
  (many (str "," >> so >> proof_prop) |>> concat)
  (fun f gs hs -> [Group (Assume f :: map mk_step (gs @ hs))])

let assert_step = proof_if_prop <|> (choice [
  proof_intro_prop;
  opt_str "and" >> so_or_have >> proof_prop;
  pipe2 (str "Since" >> proof_prop) (str "," >> have >> proof_prop) (@);
  any_str ["We will show that"; "We start by showing that"] >> proposition >>$ []
  ] |>> map mk_step)

let assert_steps =
  let join = str "," >> ((str "and" >> so_or_have) <|> so) in
  pipe2 assert_step (many (join >> proof_prop |>> map mk_step) |>> concat) (@)

let now = (str "First" >>$ false) <|>
  (any_str ["Conversely"; "Finally"; "Next"; "Now";
            "Putting the cases together"] >>$ true)

let let_step = pipe2 
  (str "let" >> ids_type |>> fun (ids, typ) -> [Let (ids, typ)])
  (opt [] (str "with" >> small_prop |>> fun f -> [Assume f]))
  (@)

let let_val_step = pipe2 (str "let" >>? id_opt_type <<? str "=") term
  (fun (id, typ) f -> LetVal (id, typ, f))

let assume_step =
  str "Suppose that" >> proposition |>> fun f -> Assume f

let let_or_assume =
  single let_val_step <|> let_step <|> single assume_step

let let_or_assumes =
  sep_by1 let_or_assume (str "," >> str "and") |>> concat

let proof_clause = pipe2
  (opt false (now << opt_str ","))
  (let_or_assumes <|> assert_steps)
  (fun escape steps -> (if escape then [Escape] else []) @ steps)

let proof_sentence =
  (sep_by1 proof_clause (str ";") |>> concat) << str "."

let proof_steps =
  many1 proof_sentence |>> (fun steps -> Steps (concat steps))

let proof_item = pair label proof_steps

let proofs = str "Proof." >> choice [
  many1 proof_item;
  proof_steps |>> (fun steps -> [("", steps)])]

(* theorems *)

let theorem_group =
  ((str "Lemma" <|> str "Theorem") >> int << str ".") >>= fun n -> 
  str "Let" >> ids_type << str "." >>=
  fun ids_typ -> pipe2 (top_prop_or_items ids_typ) (opt [] proofs)
    (fun props proofs ->
      props |> map (fun (label, f, _name) ->
        Theorem (count_label n label, f, assoc_opt label proofs)))

(* program *)

let program =
  many (axiom_group <|> definition <|> theorem_group) << empty << eof |>> concat

let parse in_channel = MParser.parse_channel program in_channel ()
