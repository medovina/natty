open Printf

open MParser

open Logic
open Statement
open Util

type state = { syntax_map : (syntax * range) list; unique_count : int ref }
let empty_state = { syntax_map = []; unique_count = ref 0 }

type 'a p = ('a, state) t   (* parser type *)

let (<<?) p q = attempt (p << q)
let (>>=?) p q = attempt (p >>= q)

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let raw_number = many1_chars digit

let number = empty >>? raw_number

let int = number |>> int_of_string

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  empty >>? satisfy match_first >>? string (string_from s 1) >>$ s

let opt_str s = optional (str s)

let any_str ss = choice (map str ss)

let parens s = str "(" >> s << str ")"

let letter1 = letter |>> char_to_string

let var = empty >>? letter1

let id = var <|> any_str ["𝔹"; "ℕ"; "ℤ"]

let sym = choice [
  empty >>? (digit <|> any_of "+-<>|") |>> char_to_string;
  any_str ["·"; "≤"; "≥"; "≮"; "≯"];
  str "−" >>$ "-"]

let minus = any_str ["-"; "−"]

let id_or_sym = id <|> sym

let word = empty >>? many1_chars letter

let keywords = ["axiom"; "definition"; "lemma"; "proof"; "theorem"]

let with_range p = empty >>?
  (get_pos >>= fun (_index, line1, col1) ->
  p >>= fun x ->
  get_pos |>> fun (_index, line2, col2) ->
    (x, Range ((line1, col1), (line2, col2))))

let add_syntax pair state = { state with syntax_map = pair :: state.syntax_map }

let record kind p = with_range p >>=
  fun (f, range) -> update_user_state (add_syntax (kind f, range)) >>$ f

let record_formula = record mk_formula_syntax
let record_type = record mk_type_syntax

(* types *)

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let const_op p sym neg =
  record_formula (p >>
    get_user_state |>> fun st ->
    incr st.unique_count;
    (* We append a unique integer to the unknown type "?" here to force different
     * syntactic occurrences to be distinct objects, so they will have distinct
     * positions for error reporting. *)
    Const (sym, unknown_type_n !(st.unique_count))) |>> fun const ->
      fun f g ->
        let e = apply [const; f; g] in
        if neg then _not e else e

let infix_binop1 p sym assoc =
  Infix (const_op p sym false, assoc)

let infix_binop sym assoc = infix_binop1 (str sym) sym assoc

let infix_negop sym pos assoc = Infix (const_op (str sym) pos true, assoc)

let type_operators = [
  [ infix "⨯" (fun t u -> Product (t, u)) Assoc_right ];
  [ infix "→" mk_fun_type Assoc_right ]
]

let typ = expression type_operators
  (record_type (id |>> fun id -> mk_base_type id))

let of_type = any_str [":"; "∈"]

let id_type = pair id (of_type >> typ)

let id_opt_type = pair id (opt unknown_type (of_type >> typ))

let ids_type = pair (sep_by1 id (str ",")) (of_type >> typ)

(* reasons *)

let theorem_num =
  number >> (many (char '.' >>? raw_number)) >> optional (parens letter) >>$ "" 

let reference = choice [
  any_str ["axiom"; "lemma"; "theorem"] >> theorem_num;
  str "part" >> parens number << opt_str "of this theorem";
  str "the definition of" >> var
  ]

let reason =
  (any_str ["by"; "using"] >>? reference) <|>
    (str "by" >>? opt_str "the inductive" >>? str "hypothesis")

(* operators for small propositions *)

let so =
  any_str ["also"; "hence"; "so"; "then"; "therefore"; "which means that"] <|>
  (str "which implies" << opt_str "that")

let have = any_str 
  ["clearly"; "it is clear that"; "it must be that";
   "the only alternative is";
   "we conclude that"; "we deduce that"; "we have";
   "we know that"; "we must have"; "we see that"] <|>
   (str "similarly" << opt_str ",") <|>
   (any_str ["it follows"; "it then follows"] >>
      optional ((str "from" >> reference) <|> reason) >>
      str "that")

let new_phrase = so <|> (optional reason >> have) <|> str "that"

let and_op = str "and" <<? not_followed_by new_phrase ""

let prop_operators = [
  [ Infix (and_op >>$ _and, Assoc_left) ];
  [ infix "or" _or Assoc_left ];
  [ infix "implies" implies Assoc_right ];
  [ Postfix (str "for all" >> id_type |>> _for_all') ];
  [ Infix (any_str ["iff"; "if and only if"] >>$ _iff, Assoc_right) ];
  [ Infix (str "," >>? and_op >>$ _and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ _or, Assoc_left) ];
]

(* terms *)

let compare_op op = infix op (binop_unknown op) Assoc_right

let mk_not_less f g = _not (binop_unknown "<" f g)
let mk_not_greater f g = _not (binop_unknown ">" f g)

let id_term = id |>> (fun v -> Var (v, unknown_type))

let unary_minus f = App (Const ("-", unknown_type), f)

let ascribe typ f =
  App (Const (":", Fun (typ, typ)), f)

let rec term s = (record_formula @@ choice [
  (sym |>> fun c -> Const (c, unknown_type));
  pipe2 (record_formula id_term <<? str "(")
    (sep_by1 expr (str ",") << str ")") tuple_apply;
  id_term;
  str "⊤" >>$ _true;
  str "⊥" >>$ _false;
  parens expr;
  pipe3 (str "{" >> var) (of_type >> typ) (str "|" >> proposition << str "}")
    (fun var typ expr -> Lambda (var, typ, expr))
 ]) s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left mk_app t next_term) s

(* expressions *)

and operators = [
  [ Postfix (str ":" >> typ |>> ascribe) ];
  [ Prefix (minus >>$ unary_minus) ];
  [ Prefix (str "¬" >>$ _not) ];
  [ infix_binop "·" Assoc_left ];
  [ infix_binop "+" Assoc_left;
    infix_binop1 minus "-" Assoc_left ];
  [ infix_binop "∈" Assoc_none ;
    infix_negop "∉" "∈" Assoc_none ;
    infix_binop "|" Assoc_none ];
  [ infix "∧" _and Assoc_left ];
  [ infix "∨" _or Assoc_left ];
  [ infix "→" implies Assoc_right ];
  [ infix "↔" _iff Assoc_right ]
]

and base_expr s = expression operators terms s

and eq_op s = choice ([
  str "=" >>$ mk_eq;
  str "≠" >>$ mk_neq;
  str "≮" >>$ mk_not_less;
  str "≯" >>$ mk_not_greater] @
  map (fun op -> const_op (str op) op false) ["<"; "≤"; ">"; "≥"]) s

and eq_expr s = pair eq_op (base_expr << optional reason) s

and expr s = record_formula (pair base_expr (many eq_expr) |>> chain_ops) s

and atomic s =
  (expr << optional (any_str ["is true"; "always holds"])) s

(* small propositions *)

and if_then_prop s =
  pipe2 (str "if" >> small_prop << opt_str ",") (str "then" >> small_prop)
    implies s

and for_all_ids s = (str "For all" >> ids_type << str ",") s

and for_all_prop s = pipe2
  for_all_ids small_prop for_all_vars_typ s

and there_exists =
  str "There" >> any_str ["is"; "are"; "exists"; "exist"]

and exists_prop s = pipe4
  (there_exists >> opt true ((str "some" >>$ true) <|> (str "no" >>$ false)))
  ids_type (option (str "with" >> small_prop)) (str "such that" >> small_prop)
  (fun some (ids, typ) with_prop p ->
    let p = opt_fold _and with_prop p in
    (if some then Fun.id else _not) (exists_vars_typ (ids, typ) p)) s

and small_prop s = expression prop_operators
  (if_then_prop <|> for_all_prop <|> exists_prop <|> atomic) s

(* propositions *)

and either_or_prop s =
  (str "either" >> small_prop |>> fun f -> match bool_kind f with
    | Binary ("∨", _, _, _) -> f
    | _ -> failwith "either: expected or") s

and precisely_prop s = (
  any_str ["Exactly"; "Precisely"] >> str "one of" >> small_prop << str "holds" |>>
    fun f ->
      let gs = gather_or f in
      assert (length gs > 1);
      let ns = all_pairs gs |> map (fun (f, g) -> _not (_and f g)) in
      multi_and (f :: ns)
  ) s

and cannot_prop s = (
  str "It cannot be that" >> proposition |>> _not) s

and proposition s = choice [
  either_or_prop; precisely_prop; cannot_prop;
  small_prop
] s

(* top propositions *)

let rec let_prop s = pipe2 (str "Let" >> id_type << str ".") top_prop _for_all' s

and suppose s = (str "Suppose" >> opt_str "further" >> str "that" >>
      sep_by1 proposition (opt_str "," >> str "and that")) s

and suppose_then s = pipe2 (suppose << str ".") (str "Then" >> proposition)
  (fold_right implies) s

and top_prop s = (let_prop <|> suppose_then <|> proposition) s

(* proposition lists *)

let label : id p = 
  ((empty >>? letter |>> char_to_string) <|> number) <<? string "."

let top_sentence : (formula * range) p = with_range (top_prop << str ".")

let proposition_item : (id * (formula * range) * id option) p = triple
  label top_sentence (option (parens word))

let prop_items : (id * (formula * range) * id option) list p =
  many1 proposition_item

let top_prop_or_items ids_typ : (id * formula * id option * range) list p =
  (prop_items <|> (top_sentence |>> fun fr -> [("", fr, None)])) |>>
    map (fun (label, (f, range), name) ->
      (label, for_all_vars_typ_if_free ids_typ f, name, range))

let propositions : (id * formula * id option * range) list p =
  (opt ([], unknown_type) for_all_ids) >>= top_prop_or_items

(* axioms *)

let operation =
  any_str ["a"; "an"] >>? optional (any_str ["binary"; "unary"]) >>
    any_str ["operation"; "relation"]

let axiom_decl : statement p =
  str "a type" >> id |>> (fun id -> TypeDecl id) <|>
  pipe2 ((any_str ["a constant"; "an element"; "a function"] <|> operation) >> id_or_sym)
    (of_type >> typ)
    (fun c typ -> ConstDecl (c, typ))

let count_label n label =
  if label = "" then sprintf "%d" n
  else sprintf "%d.%s" n label

let axiom_propositions n : statement list p = propositions |>>
  map (fun (label, f, name, _range) -> Axiom (count_label n label, f, name))

let axiom_exists n : statement list p =
  there_exists >>? pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  ((str "such that" >> axiom_propositions n) <|> (str "." >>$ []))
  (@)

let axiom_group : statement list p = (str "Axiom" >> int << str ".") >>= fun n ->
  (axiom_exists n <|> axiom_propositions n)

(* definitions *)

let eq_definition : statement p = pipe3
  (str "Let" >> sym) (str ":" >> typ) (str "=" >> term << str ".")
  mk_def

let relation_definition (ids, typ) : statement p = opt_str "we write" >>?
  id >>=? fun x ->
    pipe3 sym id (str "iff" >> proposition) (fun op y prop ->
    assert (ids = [x; y]);
    Definition (op, Fun (typ, Fun (typ, Bool)),
                Lambda (x, typ, Lambda (y, typ, prop)))) << str "."

let predicate_definition (ids, typ) : statement p = 
  id >>=? fun x ->
    pipe2 (str "is" >> word) (str "iff" >> proposition) (fun word prop ->
      assert (ids = [x]);
      Definition (word, Fun (typ, Bool),
                  Lambda (x, typ, prop))) << str "."

let definition : statement list p = str "Definition." >>
  choice [
    many1 eq_definition;
    for_all_ids >>= fun ids_typ ->
      (many1 (relation_definition ids_typ) <|> single (predicate_definition ids_typ))
  ]

(* proofs *)

let mk_step f : proof_step =
  match kind f with
    | Quant ("∃", _, typ, _) ->
        let (ids, f) = gather_quant_of_type "∃" typ f in
        IsSome (ids, typ, f)
    | _ -> mk_assert f

let opt_contra : (formula * range) list p = opt []
  (str "," >>? with_range (opt_str "which is " >>?
    optional (any_str ["again"; "also"; "similarly"]) >>?
    str "a contradiction" >>
    (optional (str "to" >> reference))) |>>
      fun (_, range) -> [(_false, range)])

let proof_prop : (formula * range) list p = pipe2 (choice [
  reason >> opt_str "," >> optional have >> with_range proposition;
  optional have >> with_range proposition << optional reason
  ]) opt_contra cons

let proof_if_prop : proof_step_r list p = with_range (triple
  (with_range (str "if" >> small_prop))
  (opt_str "," >> str "then" >> proof_prop)
  (many (str "," >> so >> proof_prop) |>> concat)) |>>
  (fun (((f, range), gs, hs), outer_range) ->
    [(Group ((Assume f, range) :: map_fst mk_step (gs @ hs)), outer_range)])

let and_or_so = (str "and" << optional so) <|> so

let will_show = choice [
  str "We need to show that";
  str "We start by showing that";
  str "We will" >> (str "show" <|> str "deduce") >> str "that"
  ]

let to_show = str "To show that" >> small_prop << str ","

let assert_step : proof_step_r list p =
  (optional have >>? proof_if_prop) <|> (choice [
    pipe2 (any_str ["Because"; "Since"] >> proof_prop) (str "," >> proof_prop) (@);
    optional to_show >> will_show >> proposition >>$ [];
    str "The result follows" >> reason >>$ [];
    single (with_range (str "This is a contradiction to" >> reference >>$ _false));
    optional and_or_so >> proof_prop
    ] |>> map_fst mk_step)

let assert_steps : proof_step_r list p =
  let join = str "," >> and_or_so in
  pipe2 assert_step (many (join >> proof_prop |>> map_fst mk_step) |>> concat) (@)

let now = (str "First" >>$ false) <|>
  (any_str ["Conversely"; "Finally"; "Next"; "Now"; "Second";
            "In any case"; "In either case"; "Putting the cases together"] >>$ true)

let let_step : proof_step_r list p = pipe2 
  (with_range (str "let" >> ids_type) |>>
    fun ((ids, typ), range) -> [(Let (ids, typ), range)])
  (opt [] (str "with" >> with_range small_prop |>>
              fun (f, range) -> [(Assume f, range)]))
  (@)

let let_val_step : proof_step_r p = 
  with_range (pair (str "let" >>? id_opt_type <<? str "=") term) |>>
    fun (((id, typ), f), range) -> (LetVal (id, typ, f), range)

let assume_step : proof_step_r p =
  with_range suppose |>>
    fun (fs, range) -> (Assume (multi_and fs), range)

let let_or_assume : proof_step_r list p =
  single let_val_step <|> let_step <|> single assume_step

let let_or_assumes : proof_step_r list p =
  sep_by1 let_or_assume (str "," >> str "and") |>> concat

let proof_clause : proof_step_r list p = pipe2
  (opt false (now << opt_str ","))
  (let_or_assumes <|> assert_steps)
  (fun escape steps -> (if escape then [(Escape, empty_range)] else []) @ steps)

let proof_sentence : proof_step_r list p =
  (sep_by1 proof_clause (str ";") |>> concat) << str "."

let new_paragraph : id p = empty >>? (any_str keywords <|> label)

let proof_steps : proof p =
  many1 (not_followed_by new_paragraph "" >> proof_sentence) |>>
    (fun steps -> Steps (concat steps))

let proof_item : (id * proof) p = pair label proof_steps

let proofs : (id * proof) list p = str "Proof." >> choice [
  many1 proof_item;
  proof_steps |>> (fun steps -> [("", steps)])]

(* theorems *)

let theorem_group : statement list p =
  ((str "Lemma" <|> str "Theorem") >> int << str ".") >>= fun n -> 
  opt ([], Bool) (str "Let" >> ids_type << str ".") >>=
  fun ids_typ -> pipe2 (top_prop_or_items ids_typ) (opt [] proofs)
    (fun props proofs ->
      props |> map (fun (label, f, _name, range) ->
        Theorem (count_label n label, f, assoc_opt label proofs, range)))

(* program *)

let program : statement list p =
  many (axiom_group <|> definition <|> theorem_group) << empty << eof |>> concat

let get_syntax_map = get_user_state |>> fun state -> state.syntax_map

let parse text = MParser.parse_string (pair program get_syntax_map) text empty_state

let parse_formula text = match MParser.parse_string expr text empty_state with
  | Success f -> f
  | Failed _ -> failwith "parse_formula" 
