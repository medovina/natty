open List
open Printf

open MParser

open Logic
open Statement
open Util

let (<<?) p q = attempt (p << q)

let opt_fold p q f = p >>= fun x -> opt x (q |>> f x)

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let number = empty >>? many1_chars digit

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  empty >>? satisfy match_first >>? string (string_from s 1) >>$ s

let opt_str s = optional (str s)

let any_str ss = choice (map str ss)

let var = empty >>? (letter |>> char_to_string)

let id = var <|> any_str ["𝔹"; "ℕ"]

let sym = (empty >>? (digit <|> char '+' <|> char '-') |>> char_to_string) <|> str "·"

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
  str "(" >> expr << str ")";
  pipe3 (str "{" >> var) (str ":" >> typ) (str "|" >> expr << str "}")
    (fun var typ expr -> Lambda (var, typ, expr))
 ] s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left (binop_unknown "·") t next_term) s

(* expressions *)

and operators = [
  [ infix "·" (binop_unknown "·") Assoc_left ];
  [ infix "+" (binop_unknown "+") Assoc_left;  infix "-" (binop_unknown "-") Assoc_left ];
  [ infix "∈" (Fun.flip mk_app) Assoc_none ];
  [ infix "=" mk_eq Assoc_right ; infix "≠" mk_neq Assoc_right ]
]

and expr s = (expression operators terms |>> multi_eq) s

let atomic = expr << opt_str "is true"

(* small propositions *)

let so = any_str ["hence"; "so"; "then"; "therefore"]

let have = any_str 
  ["it follows that";
   "we deduce that"; "we have"; "we must have"; "we see that"]

let so_or_have = so <|> have

let comma_and = str "," >>? str "and" <<? not_followed_by so_or_have ""

let prop_operators = [
  [ infix "and" _and Assoc_left ];
  [ infix "or" _or Assoc_left ];
  [ infix "implies" implies Assoc_right ];
  [ Postfix (str "for all" >> id_type |>> _for_all') ];
  [ Infix (comma_and >>$ _and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ _or, Assoc_left) ];
]

let small_prop = expression prop_operators atomic

(* propositions *)

let if_then_prop =
  pipe2 (str "if" >> small_prop << opt_str ",") (str "then" >> small_prop)
    implies

let either_or_prop =
  str "either" >> small_prop |>> fun f -> match bool_kind f with
    | Binary ("∨", _, _) -> f
    | _ -> failwith "either: expected or"

let rec for_all_prop s = pipe2
  (str "For all" >> ids_type) (str "," >> proposition) for_all_vars_typ s

and exists_prop s = pipe3
  (str "There is" >> ((str "some" >>$ true) <|> (str "no" >>$ false)))
  id_type (str "such that" >> proposition)
  (fun some (id, typ) p ->
    (if some then Fun.id else _not) (_exists id typ p)) s

and proposition s = choice [
  for_all_prop; exists_prop; if_then_prop; either_or_prop; small_prop
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

let axiom_propositions = pipe2 propositions get_user_state
  (fun props (ax, _) -> incr ax;
    props |> map (fun (label, f, name) ->
      Axiom (count_label ax label, f, name)))

let axiom_group = str "Axiom." >> any_str ["There exists"; "There is"] >> pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  ((str "such that" >> axiom_propositions) <|> (str "." >>$ []))
  (@)

(* definitions *)

let definition = pipe3
  (str "Definition." >> str "Let" >> sym) (str ":" >> typ)
  (str "=" >> term << str ".")
  (fun sym typ f -> [Definition (sym, typ, Eq (Const (sym, typ), f))])

(* proofs *)

let reason = str "by" >>? choice [
  str "lemma" >> number;
  str "part" >> str "(" >> number << str ")" << opt_str "of this theorem";
  str "the inductive hypothesis"
]

let opt_contra f = opt f
  (str "," >>? str "which is a contradiction" >>$ _and f (implies f _false))

let rec proof_intro_prop s = choice [
  pipe2 (str "if" >> small_prop) (opt_str "," >> str "then" >> proof_prop) implies;
  (reason >> opt_str "," >> optional have >> proposition) >>= opt_contra
  ] s

and proof_prop s = (proof_intro_prop <|>
  (proposition << optional reason) >>= opt_contra) s

let assert_step = choice [
  single proof_intro_prop;
  optional (str "and") >> so_or_have >> single proof_prop;
  pipe2 (str "Since" >> proof_prop) (str "," >> have >> proof_prop)
    (fun f g -> [f; g])
  ]

let mk_step f =
  match kind f with
    | Quant ("∃", x, typ, f) -> IsSome (x, typ, f)
    | _ -> Assert f

let assert_steps =
  let join = str "," >> ((str "and" >> so_or_have) <|> so) in
  pipe2 assert_step (many (join >> proof_prop))
  (fun p ps -> map mk_step (p @ ps))

let _let = optional (any_str ["First"; "Now"]) >> str "let"

let let_step = pipe2 
  (_let >> ids_type |>> fun (ids, typ) -> [Let (ids, typ)])
  (opt [] (str "with" >> small_prop |>> fun f -> [Assume f]))
  (@)

let let_val_step = pipe2 (_let >>? id_type <<? str "=") term
  (fun (id, typ) f -> LetVal (id, typ, f))

let assume_step = str "Suppose that" >> proposition |>> fun f -> Assume f

let let_or_assume = single let_val_step <|> let_step <|> single assume_step

let let_or_assumes = (sep_by1 let_or_assume (str "," >> str "and")) |>> concat

let proof_sentence =
  (let_or_assumes <|> assert_steps) << str "."

let proof_item = pipe2 label (many1 proof_sentence |>> concat)
  (fun label steps -> (label, Steps steps))
  
let proofs = str "Proof." >> many1 proof_item

(* theorems *)

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
