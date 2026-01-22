open MParser

open Hstatement
open Logic
open Module
open Util

type 'a p = ('a, unit) t   (* parser type *)
type 'a pr = ('a, unit) reply

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let raw_number = many1_chars digit

let number = empty >>? raw_number

let int = number |>> int_of_string

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  (empty >>? satisfy match_first >>? string (string_from s 1) >>=? fun _ ->
    if is_letter (last_char s) then not_before letter else return ()) >>$ s

let opt_str s = optional (str s)

let any_str ss = choice (map str ss)

let parens s = str "(" >> s << str ")"

let brackets s = str "[" >> s << str "]"

let letter1 = letter |>> char_to_string

let sub_digit = choice [
  str "₀"; str "₁";	str "₂"; str "₃";	str "₄";
  str "₅"; str "₆"; str "₇"; str "₈"; str "₉" ]

let var0 = pipe2 (empty >>? letter1) (opt "" (string "'")) (^)

let pvar = pipe2 var0 (opt "" (sub_digit)) (^)

let long_id = any_str [
  "π"; "σ"; "τ"; "Π"; "Σ"; "𝔹"; "ℕ"; "ℚ"; "ℤ";
  "𝒢"; "𝒫"; "𝒮"; "𝒲"; (* script characters G, P, S, W *)
  "div"; "egcd"; "gcd"; "mod"
]

let base_id = long_id <|> var0

let id = long_id <|> pvar

let sym = choice [
  empty >>? (digit <|> any_of "+-/<>~^") |>> char_to_string;
  any_str ["·"; "≤"; "≥"; "≮"; "≯"; "≁"; "⊆"];
  str "−" >>$ "-"]

let minus = any_str ["-"; "−"]

let mid_ellipsis : string p = any_str ["···"; "⋯"]

let id_or_sym = id <|> sym

let keywords = ["and"; "div"; "from"; "is"; "mod"; "of"; "or"]

let word = empty >>? attempt @@
  let> w = many1_chars letter in
  if mem w keywords then fail "word" else return w

let adverb = attempt @@
  let> w = word in
  if ends_with "ly" w then return w else fail "adverb"

let adjective_phrase =
  let> m = option adverb in
  let$ w = word in
  String.concat "_" (opt_to_list m @ [w])

let is_name_char c =
  c = ' ' || not (Char.Ascii.is_white c) && not (str_contains "[]:" c)

let name = empty >>? many1_satisfy is_name_char

let in_parens_name = empty >>?
  many1_satisfy (fun c -> is_name_char c && c <> '(' && c <> ')')

let sub_digit1 = sub_digit |>> sub_to_digit

let sub_letter_map = [
  "ₐ", "a";	"ₑ", "e"; "ₕ", "h"; "ᵢ", "i"; "ⱼ", "j";	"ₖ", "k";	"ₗ", "l"; "ₘ", "m"; "ₙ", "n";
  "ₒ", "o";	"ₚ", "p"; "ᵣ", "r";	"ₛ", "s";	"ₜ", "t";	"ᵤ", "u";	"ᵥ", "v"; "ₓ", "x"
]

let sub_letters = map fst sub_letter_map

let sub_letter = any_str sub_letters |>> fun s -> assoc s sub_letter_map

let sub_sym = (str "₊" >>$ "+") <|> (str "₋" >>$ "-")

(* Unicode superscript digits are not at contiguous code points! *)
let super_digit_map = [
  "⁰", "0"; "¹", "1";	"²", "2"; "³", "3";	"⁴", "4";
  "⁵", "5"; "⁶", "6"; "⁷", "7"; "⁸", "8"; "⁹", "9"
]

let super_digits = map fst super_digit_map

let super_digit = any_str super_digits |>> fun s -> assoc s super_digit_map

let sub_index : id p = (raw_number <|> (letter |>> char_to_string))

let stmt_num : string p =
  let> n = number in
  let$ sub = many (char '.' >>? sub_index) in
  String.concat "." (n :: sub)

let paragraph_keywords = [
  "axiom"; "corollary"; "definition"; "justification"; "lemma"; "proof"; "theorem"
]

let with_range (p : 'a p) : (('a * range) p) = empty >>?
  let> (_index, line1, col1) = get_pos in
  let> x = p in
  let$ (_index, line2, col2) = get_pos in
  (x, ((line1, col1), (line2, col2)))

let with_set_range p : formula p =
  let$ (f, range) = with_range p in
  set_range f range

(* types *)

let infix sym f assoc = Infix (str sym >>$ f, assoc)

let const_op p sym neg : (formula -> formula -> formula) p = p >>$
  fun f g ->
    let e = apply [_var sym; f; g] in
    if neg then _not e else e

let infix_binop1 p sym assoc =
  Infix (const_op p sym false, assoc)

let infix_binop sym assoc = infix_binop1 (str sym) sym assoc

let infix_negop sym pos assoc = Infix (const_op (str sym) pos true, assoc)

let type_operators = [
  [ infix "→" mk_fun_type Assoc_right ]
]

let is_type_var s = "σ" <= s && s <= "ω"

let rec typ_term s : typ pr = choice [
  str "Set" >> parens typ |>> (fun typ -> (Fun (typ, Bool)));
  (with_range id |>> fun (id, range) ->
    if is_type_var id then TypeVar id else base_type_range id range);
  parens typ
] s

and typ_terms s = (sep_by1 typ_term (str "⨯") |>> function
  | [] -> failwith "type(s) expected"
  | [t] -> t
  | ts -> Product ts) s

and typ s = (expression type_operators typ_terms) s

let of_type = choice [
  str ":" >> typ;
  str "∈" >> let$ id in Sub (_var id)
]

let decl_id_type = pair id_or_sym of_type

let id_opt_type = pair id (opt unknown_type of_type)

let decl_ids : (id list) p = sep_by1 id_or_sym (str ",")

let decl_ids_type : (id list * typ) p = pair decl_ids of_type

let decl_ids_types : ((id * typ) list) p =
  sep_by1 decl_ids_type (str "and") |>> fun ids_typs ->
    let+ (ids, typ) = ids_typs in
    let+ id = ids in [(id, typ)]

(* terms *)

let compare_op op = infix op (binop_unknown op) Assoc_right

let mk_not_binop op f g = _not (binop_unknown op f g)

(* We use separate constant names for unary and binary minus so that
 * a - b cannot be interpreted as (-a)(b) using implicit multiplication. *)
let unary_minus f = app (_const "u-") f

let ascribe typ f =
  app (const ":" (Fun (typ, typ))) f

let sub_term = (sub_digit1 |>> _const) <|> (sub_letter |>> _var)

let small_term = (number |>> _const) <|> (letter1 |>> _var)

let sub_expr = choice [
  chain_left1 sub_term (sub_sym |>> fun sym e1 e2 ->
    apply [_const sym; e1; e2]);
  str "_" >> small_term
]

let super_expr : formula p =
  let> opt_minus = opt Fun.id (str "⁻" >>$ unary_minus) in
  let$ d = super_digit in
  opt_minus (_const d)

let for_all_vars_with ids_types prop opt_with : formula =
    for_all_vars_types ids_types (opt_fold implies opt_with prop)

let exists_vars_with ids_types prop opt_with : formula =
    exists_vars_types ids_types (opt_fold _and opt_with prop)

let id_sub : (formula * formula option) p =
  pair (base_id |>> _var) (option sub_expr)

let mk_sub f sub : formula = match sub with
  | Some (Const (c, _, _) as g) when strlen c = 1 && is_digit c.[0] ->
      (* This could be either a variable x₀ or a sequence element x₀.
         Let the type checker resolve it. *)
      apply [_const "_"; f; g]
  | Some sub -> app f sub  (* not a variable *)
  | None -> f

let rec parens_exprs s = (parens (sep_by1 expr (str ","))) s

and range_term f f_sub =
  mid_ellipsis >> id_sub |>> (fun (g, g_sub) ->
    match f_sub, g_sub with
      | Some f_sub, Some g_sub ->
          assert (f = g);
          app (_const "Π") (mk_tuple [f; f_sub; g_sub])
      | _ -> failwith "subscript expected");

and id_term s = (
  let> (f, f_sub) = id_sub in
  opt (mk_sub f f_sub) (range_term f f_sub)
  ) s

and unit_term s : formula pr = s |> with_set_range (choice [
  id_term;
  parens_exprs |>> mk_tuple
])

and comprehension s : formula pr = (
  let>? var = str "{" >> pvar in
  let>? typ = of_type in
  let$ expr = str "|" >> proposition << str "}" in
  app (const "{}" unknown_type) (Lambda (var, typ, expr))) s

and if_clause s : (formula * formula) pr =
  (pair expr (str "if" >> expr)) s

and if_block s : formula pr = (
  let$ cs = str "{" >> sep_by1 if_clause (str ";") << str "}" in
  fold_right (fun (f, p) g -> _eif p f g) cs undefined) s

and base_term s : formula pr = s |> with_set_range @@ choice [
  unit_term;
  (sym |>> _const);
  str "⊤" >>$ _true;
  str "⊥" >>$ _false;
  str "|" >> expr1 false << str "|" |>> app (_const "abs");
  comprehension;
  if_block
 ]

and apply_super f super : formula =
  opt_fold (fun c f -> apply [_var "^"; f; c]) super f

and term s = s |>
  with_set_range (pipe2 base_term (option super_expr) apply_super)

and next_term s = s |> (not_before space >>?
  with_set_range (pipe2 unit_term (option super_expr) apply_super))

and terms s = (term >>= fun t -> many_fold_left app_range t next_term) s

(* expressions *)

and compare_ops = ["<"; "≤"; ">"; "≥"; "~"; "⊆"]

and eq_op s = choice ([
  str "=" >>$ mk_eq;
  str "≠" >>$ mk_neq;
  str "≮" >>$ mk_not_binop "<";
  str "≯" >>$ mk_not_binop ">";
  str "≁" >>$ mk_not_binop "~" ] @
  map (fun op -> const_op (str op) op false) compare_ops) s

and apply_reasons rs f : formula =
  if rs = [] then f else
  app (_const ("$by " ^ String.concat "," (map fst rs))) f

and quant_op c quant =
  Prefix (str c >> decl_ids_type << str "." |>>
             (fun (ids, typ) -> quant_vars_typ quant ids typ))

and operators with_bar = [
  [ Postfix (str ":" >> typ |>> ascribe) ];
  [ Prefix (minus >>$ unary_minus) ];
  [ Prefix (str "¬" >>$ _not) ];
  [ infix_binop "^" Assoc_right ];
  (let& op = ["·"; "/"; "div"; "mod"] in infix_binop op Assoc_left);
  [ infix_binop "+" Assoc_left;
    infix_binop1 minus "-" Assoc_left ];
  [ Postfix (by_reason |>> fun r -> apply_reasons r) ];
  (if with_bar then [ infix_binop "|" Assoc_none ] else []) @
  [ infix_negop "∤" "|" Assoc_none;   (* does not divide *)
    infix "∈" elem Assoc_none ;
    infix "∉" not_elem Assoc_none
  ];
  [ Infix (eq_op,  Assoc_left) ];
  [ infix "∧" _and Assoc_left ];
  [ infix "∨" _or Assoc_left ];
  [ infix "→" implies Assoc_right ];
  [ infix "↔" _iff Assoc_right ];
  [ quant_op "∀" _for_all; quant_op "∃" _exists ]
]

and expr1 with_bar s = (expression (operators with_bar) terms) s

and expr s = expr1 true s

and exprs s = (sep_by1 expr (str "and") |>> multi_and) s

and opt_predicate_target word : (formula -> formula) p =
  let app_pred xs f = apply ([_const ("is_" ^ word); f] @ xs) in
  choice [
    str "as" >> expr |>> (fun x -> app_pred [x]);
    pipe2 (str "of" >> expr) (opt [] (single (str "and" >> expr)))
        (fun x y -> (app_pred ([x] @ y)));
    pipe2 (str "from" >> expr) (str "to" >> expr) (fun y z -> app_pred [y; z]);
    return (app_pred [])
  ]

and target_predicate s : (formula -> formula) pr = (
  let> w1 = any_str ["a"; "an"; "the"] >>? word in
  let> w2 = option word in
  let w = String.concat "_" (w1 :: opt_to_list w2) in
  opt_predicate_target w) s

and predicate s : (formula -> formula) pr = choice [
  target_predicate;
  pipe2 (option (str "not")) adjective_phrase (fun neg word f ->
    let g = app (_const word) f in
    if is_some neg then _not g else g)
] s

and predicate_is_expr s = (
  let> p = target_predicate in
  let$ f = str "is" >> expr in
  p f
) s

and compound_are e2 word e1 : formula =
  apply [_const word; e1; e2]

and atomic s : formula pr = (choice [
  predicate_is_expr;
  let> e = expr in
  let$ f = choice [
    any_str ["is true"; "always holds"] >>$ Fun.id;
    any_str ["is also"; "is"; "must be"; "must also be"] >>? predicate;
    pipe2 (str "and" >>? expr <<? str "are") adjective_phrase compound_are;
    return Fun.id
   ] in
  f e;
  ]) s

(* reasons *)

and id_eq_term s : formula pr = (id >> str "=" >> term) s

and theorem_ref s : string pr = s |> choice [
  (let> kind = any_str ["Axiom"; "Lemma"; "Theorem"] in
  let$ num = stmt_num in
  "$" ^ to_lower kind ^ " " ^ num);
  brackets (name << optional (str ":" << sep_by1 id_eq_term (str ",")))
]

and reference s : reason pr = choice [
  single (with_range theorem_ref);
  any_str ["our"; "the"] >>?
    str "assumption" >> optional (str "that" >> atomic) >>$ [];
  str "part" >> parens number >> opt_str "of this theorem" >>$ []
  ] s

and reason s : reason pr = (
  reference <|>
  (choice [
    str "contradiction with" >> reference >>$ "";
    optional (opt_str "the" >>? any_str ["inductive"; "induction"]) >>?
      any_str ["assumption"; "hypothesis"];
    str "definition";
    str "the definition of" << term;
    opt_str "the" >>? any_str ["substitutivity"; "transitivity"] <<
      any_str ["of ="; "of equality"]
    ] >>$ [])) s

and reasons s : reason pr = s |> (sep_by1 reason (str "and") |>> concat)

and by_reason s : reason pr = (opt_str "again" >> str "by" >> reasons) s

(* so / have *)

and so = choice [
  any_str ["also"; "consequently"; "hence"; "however"; "so"; "that is";
           "then"; "therefore"; "thus"; "whence"; "which means that"];
  str "but" << opt_str "then";
  str "which implies" << opt_str "that" ]

and have s : reason pr = (
  (any_str ["it follows"; "it then follows"] >>
    opt [] ((str "from" >> reference) <|> by_reason) << str "that") <|>
  (choice [
    any_str ["clearly"; "it must be that"; "notice that";
      "observe that"; "the only alternative is"; "this means that";
      "this shows that"; "trivially";
      "we conclude that"; "we deduce that";
      "we know that"; "we must have"; "we obtain"; "we see that"];
    str "it is" >> any_str ["clear"; "obvious"] >> str "that";
    any_str ["likewise"; "on the other hand"; "similarly"] << opt_str ",";
    str "we have" << opt_str "shown that"
  ] >>$ [])) s

and new_phrase s =
  (so <|> (optional by_reason >> have >>$ "") <|> str "that") s

and and_op s = (str "and" <<? not_before new_phrase) s

(* small propositions *)

and for_with text q s : (formula -> formula) pr =
  pipe2 (str text >> decl_ids_type) (option with_exprs)
    (fun (ids, typ) opt_with f ->
      let ids_types = (let+ id = ids in [(id, typ)]) in
      q ids_types f opt_with) s

and post_for_all_with s = for_with "for all" for_all_vars_with s
and post_for_some_with s = for_with "for some" exists_vars_with s

and _if_op = str "if" <<? not_before (str "and only")

and prop_operators () = [
  [ Infix (and_op >>$ _and, Assoc_left) ];
  [ infix "or" _or Assoc_left ];
  [ Infix (str "implies" << opt_str "that" >>$ implies, Assoc_right) ];
  [ Postfix post_for_all_with ];
  [ Postfix post_for_some_with ];
  [ Infix (any_str ["iff"; "if and only if"] >>$ _iff, Assoc_right);
    Infix (_if_op >>$ Fun.flip implies1, Assoc_right) ];
  [ Infix (str "," >>? and_op >>$ _and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ _or, Assoc_left) ];
]

and if_then_prop s : formula pr =
  pipe2 (str "if" >> small_prop << opt_str ",") (str "then" >> small_prop)
    implies s

and for_all_ids s : (id * typ) list pr =
    (str "For all" >> decl_ids_types) s

and for_all_with s : ((id * typ) list * formula option) pr = s |>
  pair for_all_ids (option with_exprs << opt_str ",")

and for_all_prop s : formula pr = s |>
  let> (ids_types, with_exprs) = for_all_with in
  let$ prop = small_prop in
  for_all_vars_with ids_types prop with_exprs

and there_exists =
  str "There" >> any_str ["is"; "are"; "exists"; "exist"; "must be"; "must exist"]

and with_exprs s = (str "with" >> exprs) s

and exists_prop s : formula pr = pipe4
  (there_exists >>
    opt true ((any_str ["some"; "an operation"] >>$ true) <|> (str "no" >>$ false)))
  decl_ids_types (option with_exprs) (str "such that" >> small_prop)
  (fun some ids_types with_exprs p ->
    (if some then Fun.id else _not) (exists_vars_with ids_types p with_exprs)) s

and exclusive_or exact f : formula =
  let gs = gather_or f in
  assert (length gs > 1);
  let ns = all_pairs gs |> map (fun (f, g) -> _not (_and f g)) in
  multi_and (if exact then f :: ns else ns)

and multi_or_prop s : formula pr = (
  let> g = choice [
    str "At least" >>$ Fun.id;
    str "At most" >>$ exclusive_or false;
    any_str ["Exactly"; "Precisely"] >>$ exclusive_or true] in
  let$ f = str "one of" >> opt_str "the conditions" >> small_prop << str "holds" in
  g f
  ) s

and small_prop s : formula pr = expression (prop_operators ())
  (if_then_prop <|> for_all_prop <|> exists_prop <|> multi_or_prop <|> atomic) s

(* propositions *)

and either_or_prop s : formula pr =
  (str "either" >> small_prop >>= fun f -> match bool_kind f with
    | Binary ("(∨)", _, _, _) -> return f
    | _ -> fail "either: expected or") s

and cannot_prop s : formula pr = (
  str "It cannot be that" >> small_prop |>> _not) s

and proposition s : formula pr = choice [
  either_or_prop; cannot_prop;
  small_prop
] s

(* top propositions *)

let operation =
  optional (any_str ["binary"; "unary"]) >>
    any_str ["operation"; "operations"; "relation"; "relations"]

let an_operation = optional (any_str ["a"; "an"]) >>? operation

let let_decl : (id * typ) list p =
  str "Consider any" >> decl_ids_types <|> (
  str "Let" >> choice [
    id <<? str "be a type" |>> (fun id -> [(id, Type)]);
    decl_ids_types << optional (str "be" >> an_operation)
  ])

let let_step : proof_step list p = pipe2 
  (let_decl |>> fun ids_types -> [Let ids_types])
  (opt [] (str "with" >> exprs |>> fun f -> [Assume f]))
  (@)

let let_val_step : proof_step p = 
  pipe2 (str "let" >>? id_opt_type <<? str "=") expr
    (fun (id, typ) f ->
      (LetDef (id, typ, Eq (const id typ, f))))

let define_step : proof_step p =
  pipe2 (str "define" >> atomic) for_all_ids (fun f ids_types ->
    let g = for_all_vars_types ids_types f in
    LetDef (definition_id g, unknown_type, g))

let let_def_step : proof_step p = let_val_step <|> define_step

let suppose = (opt_str "also" >>? any_str ["assume"; "suppose"] >> opt_str "further" >>
    opt_str "that" >> sep_by1 proposition (opt_str "," >> str "and that"))

let assume_step : proof_step p = suppose |>> fun fs -> Assume (multi_and fs)

let let_or_assume : proof_step list p =
  single let_def_step <|> let_step <|> single assume_step

let top_prop : proof_step list p =
  pipe2 (many_concat (let_or_assume << str "."))
  (opt_str "Then" >> proposition)
  (fun lets p -> lets @ [mk_assert p])

(* proposition lists *)

let sub_index_dot : id p =
  empty >>? sub_index <<? string "."

let stmt_name = parens in_parens_name

let label = brackets name

let top_sentence : (proof_step list * id option) p =
    pair (top_prop << str ".") (option label)

let proposition_item : (id * (proof_step list * id option)) p =
  pair sub_index_dot top_sentence

let prop_items : (id * ((proof_step list) * id option)) list p =
  let> items = many1 proposition_item in
  if has_duplicate (map fst items) then fail "duplicate label"
  else return items

let top_prop_or_items (name: id option): (id * proof_step list * id option) list p =
  choice [
    prop_items;
    top_sentence |>> fun (fr, name1) -> [("", (fr, opt_or_opt name1 name))]
  ] |>> map (fun (sub_index, (steps, name)) -> (sub_index, steps, name))

let propositions name : (id * proof_step list * id option) list p =
  let> (vars, with_expr) = opt ([], None) for_all_with in
  let$ props = top_prop_or_items name in
  let assume_steps = map mk_assume (opt_to_list with_expr) in
  let& (id, steps, name) = props in
  (id, Let vars :: assume_steps @ steps, name)

(* axioms *)

let unary_prefix id typ =
  if arity typ = 1 && id = "-" then "u-" else id

let words2 : string p =
    pipe2 word (option word) (fun w x ->
        unwords (w :: opt_to_list x)) 

let type_name : (id * string option) p =
  let> id = str "type" >> id in
  let$ opt_name = option (parens (str "the" >> words2)) in
  (id, Option.map singular opt_name)

let type_decl : hstatement p =
  let$ (id, opt_name) = str "a" >>? type_name in
  HTypeDef (id, [], opt_name)

let const_decl : hstatement list p =
  let$ (cs, typ) = (any_str ["a constant"; "an element"; "a function"] <|> an_operation) >>
    decl_ids_type in
  let& c = cs in
  HConstDecl (unary_prefix c typ, typ)

let axiom_decl : hstatement list p =
  single type_decl <|> const_decl

let axiom_propositions id_typ num name : hstatement list p =
  let$ props = propositions name in
  [HAxiomGroup (num, id_typ, 
    let& (sub_index, steps, name) = props in
    { sub_index; name; steps })]

let axiom_exists num name : hstatement list p =
  there_exists >>?
  let> consts = sep_by1 axiom_decl (any_str ["and"; "with"]) in
  let consts = concat consts in
  let id_typ = defined_id_type (last consts) in
  let$ props = (str "such that" >> axiom_propositions (Some id_typ) num name) <|>
               (str "." >>$ []) in
  consts @ props

let axiom_group : hstatement list p =
  let> num = str "Axiom" >> opt "" stmt_num in
  let> name = option stmt_name << str "." in
  axiom_exists num name <|> axiom_propositions None num name

(* proofs *)

let mk_step f reasons : proof_step =
  match kind f with
    | Quant ("(∃)", _, _, _) ->
        let (ids_types, f) = gather_quant "(∃)" f in
        IsSome (ids_types, f, reasons)
    | _ -> Assert (f, reasons)

let because_prop : proof_step p =
  any_str ["because"; "since"] >> proposition |>>
    (fun p -> Assert (p, []))

let contradiction : proof_step list p =
  let> contra = choice [
      str "a contradiction" >> (opt [] (str "to" >> reference));
      str "contradicting" >> reference ] in
  let step = [Assert (_false, contra)] in
  let$ because = opt [] (single because_prop) in
  because @ step

let which_is_contradiction : proof_step list p = str "," >>?
  (opt_str "which is" >>? optional (any_str ["again"; "also"; "similarly"])) >>? contradiction

let have_contradiction : proof_step list p =
  any_str ["This is"; "We have"] >>? contradiction

let prop_reason : (formula * reason) p =
  pair proposition (opt [] by_reason)

let proof_prop : proof_step list p =
  let> reason = opt [] (by_reason << opt_str ",") in
  let> reason2 = opt [] have in
  let> (f, reason3) = prop_reason in
  let> because = option because_prop in
  let$ c = opt [] which_is_contradiction in
  let reasons = reason @ reason2 @ reason3 in
  opt_to_list because @ (mk_step f reasons :: c)

let proof_if_prop : proof_step list p =
  let> f = str "if" >> small_prop in
  let> gs = opt_str "," >> str "then" >> proof_prop in
  let$ hs = many_concat (str "," >> so >> proof_prop) in
  [Group (Assume f :: gs @ hs)]

let and_or_so =
  ((str "and" << optional so) <|> so) << opt_str ","

let will_show =
  (str "We" >>? any_str ["must"; "need to"; "will"]) >>?
    opt_str "now" >>? any_str ["deduce"; "prove"; "show"] >>
    optional by_reason >> str "that"

let assert_step : proof_step list p =
  choice [
    optional have >>? proof_if_prop;
    optional have >>? pipe2 (single because_prop) (opt_str "," >> proof_prop) (@);
    will_show >> proposition >>$ [];
    str "The result follows" >> by_reason >>$ [];
    optional and_or_so >>? have_contradiction;
    optional and_or_so >> proof_prop
    ]

let assert_steps : proof_step list p =
  let join = str "," >> and_or_so in
  pipe2 assert_step (many_concat (join >> proof_prop)) (@)

let now = any_str ["Conversely"; "Finally"; "Next"; "Now"; "Second"]

let any_case = str "in" >>?
  any_str ["all cases"; "any case"; "both cases"; "either case" ]

let let_or_assumes : proof_step list p =
  sep_by1 let_or_assume (str "," >> str "and") |>> concat

let clause_intro = choice [
  str "First" >>$ 0;
  now >>$ 1;
  optional so >>? any_case >>$ 2
]

let proof_clause : proof_step list p = pipe2
  (opt 0 (clause_intro << opt_str ","))
  (let_or_assumes <|> assert_steps)
  (fun now steps ->
    let esc = if now = 1 && is_assume (hd steps) || now = 2
                then [Escape] else []
    in esc @ steps)

let proof_sentence : proof_step list p =
  (sep_by1 proof_clause (str ";") |>> concat) << str "." << optional label

let new_paragraph : id p = empty >>? (any_str paragraph_keywords <|> sub_index_dot)

let proof_by : proof_step list p =
  let$ reasons = choice [
    str "Follows from" >> reasons;
    str "Left to the reader" >>$ []] << str "." in
  [Assert (_const "$thm", reasons)]

let proof_steps : proof_step list p = proof_by <|> (
  many1 (not_before new_paragraph >> proof_sentence) |>>
    (fun steps -> concat steps))

let proof_item : (id * proof_step list) p = pair sub_index_dot proof_steps

let proof_items : (id * proof_step list) list p =
  let> items = many1 proof_item in
  if has_duplicate (map fst items) then fail "duplicate proof item"
  else return items

let proofs : (id * proof_step list) list p = str "Proof." >> choice [
  proof_items;
  proof_steps |>> (fun steps -> [("", steps)])]

(* definitions *)

let type_definition : hstatement p =
  let> (id, opt_name) = str "The" >>? type_name in
  let$ constructors =
    str "is defined inductively with constructors" >> decl_ids_types << str "." in
  HTypeDef (id, constructors, opt_name)

let explicit_definition : hstatement p =
  let> id_type = str "The" >> operation >> decl_id_type in
  let> recursive = str "is defined" >> opt false (str "recursively" >>$ true) in
  let> all = str "such that" >> for_all_ids in
  let$ props = str "," >> top_prop_or_items None in
  let defs = let& (sub_index, steps, _) = props in
    match steps with
      | [Assert (f, _)] -> { sub_index; formula = for_all_vars_types_if_free all f }
      | _ -> failwith "explicit_definition" in
  HDefinition { id_type = Some id_type; recursive; defs; justification = [] }

let define ids_types justification prop : hstatement =
  let prop = for_all_vars_types ids_types prop in
  let defs = [{ sub_index = ""; formula = prop }] in
  HDefinition { id_type = None; recursive = false; defs; justification }

let def_prop : formula p = 
    not_before new_paragraph >> opt_str "we write" >>
      small_prop << str "."

let definition_body : ((id * typ) list * formula list) p =
  let> let_ids_types = many (let_decl <<? str ".") in
  let> ids_types = opt [] (for_all_ids << str ",") in
  let$ props = many1 (opt_str "Let" >> def_prop) in
  let ids_types = concat let_ids_types @ ids_types in
  (ids_types, props)

let const_or_fun_definition : hstatement list p =
  let> (ids_types, props) = definition_body in
  let$ justification = opt [] (str "Justification." >> proof_steps) in
  define ids_types justification (hd props) ::
  map (define ids_types []) (tl props)

let definition : hstatement list p =
  str "Definition" >> optional stmt_name >> str "." >>
  (single type_definition <|> single explicit_definition <|> const_or_fun_definition)

(* theorems *)

let theorem_group : hstatement list p =
  any_str ["Corollary"; "Lemma"; "Theorem"] >>
  let> num = opt "" stmt_num in
  let> name = option stmt_name << str "." in
  let> let_steps = many_concat (let_step << str ".") in
  let> props = top_prop_or_items name in
  let$ proofs = opt [] proofs in [HTheoremGroup (num, 
  props |> map (fun (sub_index, steps, name) ->
    { sub_index; name;
      steps = let_steps @ steps;
      proof_steps = opt_default (assoc_opt sub_index proofs) [] })
  )]

(* module *)

let module_name : string p =
  let$ name = empty >>? many1_chars (alphanum <|> char '_') in
  name ^ ".n"

let using : string list p =
  str "using" >> sep_by1 module_name (str ",") << str ";"

let _module : hstatement list p = optional using >>
  many (axiom_group <|> definition <|> theorem_group) << empty << eof |>> concat

let parse_formula text : formula = always_parse expr text

let parse_files filenames sources : (hmodule list, string * frange) Stdlib.result =
  parse_modules (opt [] using) _module filenames sources

let parse_file filename = profile @@
  parse_files [filename] []
