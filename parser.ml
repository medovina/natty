open Printf

open MParser

open Logic
open Statement
open Util

let (let>) = bind

let bind_ret p f = p >>= (fun x -> return (f x))

let (let$) = bind_ret

type state = {
    axiom_count : int ref; theorem_count : int ref;
}

let empty_state () = {
    axiom_count = ref 0; theorem_count = ref 0
}

type 'a p = ('a, state) t   (* parser type *)
type 'a pr = ('a, state) reply

let comment = char '#' << skip_many_until any_char newline

let empty = skip_many (space <|> comment)

let raw_number = many1_chars digit

let number = empty >>? raw_number

let int = number |>> int_of_string

let str s =
  let match_first c =
    Char.lowercase_ascii c = Char.lowercase_ascii (s.[0]) in
  (empty >>? satisfy match_first >>? string (string_from s 1) >>=? fun _ ->
    if is_letter (last_char s) then not_followed_by letter "" else return ()) >>$ s

let opt_str s = optional (str s)

let any_str ss = choice (map str ss)

let parens s = str "(" >> s << str ")"

let brackets s = str "[" >> s << str "]"

let letter1 = letter |>> char_to_string

let sub_digit = choice [
  str "₀"; str "₁";	str "₂"; str "₃";	str "₄";
  str "₅"; str "₆"; str "₇"; str "₈"; str "₉" ]

let var = pipe2 (empty >>? letter1) (opt "" sub_digit) (^)

let long_id = any_str ["π"; "σ"; "τ"; "∏"; "𝔹"; "ℕ"; "ℤ"; "𝒫"; "gcd"]

let base_id = long_id <|> (empty >>? letter1)

let id = long_id <|> var

let sym = choice [
  empty >>? (digit <|> any_of "+-<>|~^") |>> char_to_string;
  any_str ["·"; "≤"; "≥"; "≮"; "≯"; "≁"; "⊆"];
  str "−" >>$ "-"]

let minus = any_str ["-"; "−"]

let mid_ellipsis : string p = any_str ["···"; "⋯"]

let id_or_sym = id <|> sym

let word = empty >>? many1_chars letter

let adjective = word

let name = empty >>? many1_chars (alphanum <|> char '_' <|> char ' ')

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

let keywords = ["axiom"; "corollary"; "definition"; "lemma"; "proof"; "theorem"]

let with_range (p : 'a p) : (('a * range) p) = empty >>?
  (get_pos >>= fun (_index, line1, col1) ->
  p >>= fun x ->
  get_pos |>> fun (_index, line2, col2) ->
    (x, ((line1, col1), (line2, col2))))

let record_formula (p : formula p) : formula p = with_range p |>>
  fun (f, range) -> match f with
    | App (Const (c, _), g) when c.[0] = '@' -> g   (* avoid double record *)
    | _ -> App (_const (encode_range range), f)

let record_type p = with_range p |>>
  fun (t, range) -> TypeApp (encode_range range, [t])

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
  record_type (id |>> fun id ->
    if is_type_var id then TypeVar id else mk_base_type id);
  parens typ
] s

and typ_terms s = (sep_by1 typ_term (str "⨯") |>> function
  | [] -> failwith "type(s) expected"
  | [t] -> t
  | ts -> Product ts) s

and typ s = (expression type_operators typ_terms) s

let of_type = any_str [":"; "∈"]

let id_type = pair id (of_type >> typ)

let id_opt_type = pair id (opt unknown_type (of_type >> typ))

let decl_ids : (id list) p = sep_by1 id_or_sym (str ",")

let decl_ids_type : (id list * typ) p = pair decl_ids (of_type >> typ)

let decl_ids_types : ((id * typ) list) p =
  sep_by1 decl_ids_type (str "and") |>> fun ids_typs ->
    let+ (ids, typ) = ids_typs in
    let+ id = ids in [(id, typ)]

(* terms *)

let compare_op op = infix op (binop_unknown op) Assoc_right

let mk_not_binop op f g = _not (binop_unknown op f g)

(* We use separate constant names for unary and binary minus so that
 * a - b cannot be interpreted as (-a)(b) using implicit multiplication. *)
let unary_minus f = App (_const "u-", f)

let ascribe typ f =
  App (Const (":", Fun (typ, typ)), f)

let sub_term = (sub_digit1 |>> _const) <|> (sub_letter |>> _var)

let small_term = (number |>> _const) <|> (letter1 |>> _var)

let sub_expr = choice [
  chain_left1 sub_term (sub_sym |>> fun sym e1 e2 ->
    apply [_const sym; e1; e2]);
  str "_" >> small_term
]

let super_term = super_digit |>> _const

let for_all_with ids_types prop opt_with : formula =
    for_all_vars_types ids_types (opt_fold implies opt_with prop)

let exists_with ids_types prop opt_with : formula =
    exists_vars_types ids_types (opt_fold _and opt_with prop)

let id_sub : (formula * formula option) p =
  pair (base_id |>> _var) (option sub_expr)

let mk_sub f sub : formula = match sub with
  | Some (Const (c, _) as g) when strlen c = 1 && is_digit c.[0] ->
      (* This could be either a variable x₀ or a sequence element x₀.
         Let the type checker resolve it. *)
      apply [_const "_"; f; g]
  | Some sub -> App (f, sub)  (* not a variable *)
  | None -> f

let rec parens_exprs s = (str "(" >> (sep_by1 expr (str ",") << str ")")) s

and range_term f f_sub =
  mid_ellipsis >> id_sub |>> (fun (g, g_sub) ->
    match f_sub, g_sub with
      | Some f_sub, Some g_sub ->
          assert (f = g);
          App (_const "∏", mk_tuple [f; f_sub; g_sub])
      | _ -> failwith "subscript expected");

and id_term s = (id_sub >>=
  (fun (f, f_sub) -> choice [
    parens_exprs |>> (fun args -> App (mk_sub f f_sub, mk_tuple args));
    range_term f f_sub;
    return (mk_sub f f_sub)
  ])) s

and base_term s : formula pr = (record_formula @@ choice [
  (sym |>> _const);
  id_term;
  str "⊤" >>$ _true;
  str "⊥" >>$ _false;
  parens_exprs |>> mk_tuple;
  pipe3 (str "{" >> var) (of_type >> typ) (str "|" >> proposition << str "}")
    (fun var typ expr -> Lambda (var, typ, expr))
 ]) s

and term s = pipe2 base_term (option super_term) (fun f super ->
  opt_fold (fun c f -> apply [_var "^"; f; c]) super f) s

and next_term s = (not_followed_by space "" >>? term) s

and terms s = (term >>= fun t -> many_fold_left mk_app t next_term) s

(* expressions *)

and compare_ops = ["<"; "≤"; ">"; "≥"; "~"; "⊆"]

and eq_op s = choice ([
  str "=" >>$ mk_eq;
  str "≠" >>$ mk_neq;
  str "≮" >>$ mk_not_binop "<";
  str "≯" >>$ mk_not_binop ">";
  str "≁" >>$ mk_not_binop "~" ] @
  map (fun op -> const_op (str op) op false) compare_ops) s

and operators = [
  [ Postfix (str ":" >> typ |>> ascribe) ];
  [ Prefix (minus >>$ unary_minus) ];
  [ Prefix (str "¬" >>$ _not) ];
  [ infix_binop "·" Assoc_left ];
  [ infix_binop "+" Assoc_left;
    infix_binop1 minus "-" Assoc_left ];
  [ infix "∈" elem Assoc_none ;
    infix "∉" not_elem Assoc_none ;
    infix_binop "|" Assoc_none;
    infix_negop "∤" "|" Assoc_none   (* does not divide *)
    ];
  [ Infix (eq_op,  Assoc_left) ];
  [ infix "∧" _and Assoc_left ];
  [ infix "∨" _or Assoc_left ];
  [ infix "→" implies Assoc_right ];
  [ infix "↔" _iff Assoc_right ];
  [ Prefix (str "∀" >> decl_ids_type << str "." |>>
             (fun ids_type -> for_all_vars_typ ids_type)) ] 
]

and expr s = record_formula (expression operators terms) s

and exprs s = (sep_by1 expr (str "and") |>> multi_and) s

and predicate_target word =
  let app xs f = apply ([_const ("is_" ^ word); f] @ xs) in
  choice [
    str "as" >> atomic |>> (fun x -> app [x]);
    pipe2 (str "of" >> atomic) (opt [] (single (str "and" >> atomic)))
        (fun x y -> (app ([x] @ y)));
    pipe2 (str "from" >> atomic) (str "to" >> atomic) (fun y z -> app [y; z])
  ]

and predicate s : (formula -> formula) pr = choice [
  any_str ["a"; "an"; "the"] >> word >>= (fun w ->
    predicate_target w <|> (word >>= fun x -> predicate_target (w ^ "_" ^ x)));
  pipe2 (option (str "not")) adjective (fun neg word f ->
    let g = App (_const word, f) in
    if Option.is_some neg then _not g else g)
] s

and atomic s = (
  pipe2 expr (choice [
    any_str ["is true"; "always holds"] >>$ Fun.id;
    any_str ["is"; "must be"; "must also be"] >> predicate;
    return Fun.id
   ]) (fun e f -> f e)) s

(* reasons *)

and id_eq_term s = (id >> str "=" >> term) s

and theorem_ref s = brackets (
  name << optional (str ":" << sep_by1 id_eq_term (str ","))) s

and reference s = choice [
  theorem_ref;
  str "part" >> parens number << opt_str "of this theorem"
  ] s

and reason s = choice [
  any_str ["by contradiction with"; "by"; "using"] >>? reference;
  str "by" >>? optional (any_str ["the inductive"; "the induction"]) >>?
    any_str ["assumption"; "hypothesis"];
  str "by definition";
  str "by the definition of" << term;
  str "by transitivity of ="] s

(* so / have *)

and so = choice [
  any_str ["also"; "consequently"; "hence"; "however"; "so";
           "then"; "therefore"; "which means that"];
  str "but" << opt_str "then";
  str "which implies" << opt_str "that" ]

and have s = (any_str 
  ["clearly"; "it is clear that"; "it must be that";
   "observe that"; "the only alternative is"; "this means that";
   "this shows that"; "trivially";
   "we conclude that"; "we deduce that";
   "we know that"; "we must have"; "we see that"] <|>
   (str "we have" << opt_str "shown that") <|>
   (any_str ["on the other hand"; "similarly"] << opt_str ",") <|>
   (any_str ["it follows"; "it then follows"] >>
      optional ((str "from" >> reference) <|> reason) >>
      str "that")) s

and new_phrase s = (so <|> (optional reason >> have) <|> str "that") s

and and_op s = (str "and" <<? not_followed_by new_phrase "") s

(* small propositions *)

and for_with text q s =
  pipe2 (str text >> id_type) (option with_exprs)
    (fun id_type opt_with f -> q [id_type] f opt_with) s

and post_for_all_with s = for_with "for all" for_all_with s
and post_for_some_with s = for_with "for some" exists_with s

and prop_operators () = [
  [ Infix (and_op >>$ _and, Assoc_left) ];
  [ infix "or" _or Assoc_left ];
  [ Infix (str "implies" << opt_str "that" >>$ implies, Assoc_right) ];
  [ Postfix post_for_all_with ];
  [ Postfix post_for_some_with ];
  [ Infix (any_str ["iff"; "if and only if"] >>$ _iff, Assoc_right) ];
  [ Infix (str "," >>? and_op >>$ _and, Assoc_left) ];
  [ Infix (str "," >>? str "or" >>$ _or, Assoc_left) ];
]

and if_then_prop s : formula pr =
  pipe2 (str "if" >> small_prop << opt_str ",") (str "then" >> small_prop)
    implies s

and for_all_ids s : (id * typ) list pr =
    (str "For all" >> decl_ids_types) s

and for_all_prop s : formula pr = (pipe3
  for_all_ids (option with_exprs) (opt_str "," >> small_prop)
    (fun ids_types with_exprs prop -> 
        for_all_with ids_types prop with_exprs)) s

and there_exists =
  str "There" >> any_str ["is"; "are"; "exists"; "exist"; "must exist"]

and with_exprs s = (str "with" >> exprs) s

and exists_prop s : formula pr = pipe4
  (there_exists >>
    opt true ((any_str ["some"; "an operation"] >>$ true) <|> (str "no" >>$ false)))
  decl_ids_types (option with_exprs) (str "such that" >> small_prop)
  (fun some ids_types with_exprs p ->
    (if some then Fun.id else _not) (exists_with ids_types p with_exprs)) s

and precisely_prop s : formula pr = (
  any_str ["Exactly"; "Precisely"] >> str "one of" >> small_prop << str "holds" |>>
    fun f ->
      let gs = gather_or f in
      assert (length gs > 1);
      let ns = all_pairs gs |> map (fun (f, g) -> _not (_and f g)) in
      multi_and (f :: ns)
  ) s

and small_prop s : formula pr = expression (prop_operators ())
  (if_then_prop <|> for_all_prop <|> exists_prop <|> precisely_prop <|> atomic) s

(* propositions *)

and either_or_prop s : formula pr =
  (str "either" >> small_prop >>= fun f -> match bool_kind f with
    | Binary ("∨", _, _, _) -> return f
    | _ -> fail "either: expected or") s

and cannot_prop s : formula pr = (
  str "It cannot be that" >> small_prop |>> _not) s

and proposition s : formula pr = choice [
  either_or_prop; cannot_prop;
  small_prop
] s

(* top propositions *)

let operation =
  any_str ["a"; "an"] >>? optional (any_str ["binary"; "unary"]) >>
    any_str ["operation"; "relation"]

let let_decl : (id * typ) list p = str "Let" >> choice [
  id <<? str "be a type" |>> (fun id -> [(id, Type)]);
  decl_ids_types << optional (str "be" >> operation)
]

let let_step : proof_step list p = pipe2 
  (let_decl |>> fun ids_types -> [Let ids_types])
  (opt [] (str "with" >> exprs |>> fun f -> [Assume f]))
  (@)

let let_val_step : proof_step p = 
  pipe2 (str "let" >>? id_opt_type <<? str "=") expr
    (fun (id, typ) f ->
      (LetDef (id, typ, Eq (Const (id, typ), f))))

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
  (fun lets p -> lets @ [Assert p])

(* proposition lists *)

let sub_index : id p = 
  ((empty >>? letter |>> char_to_string) <|> number) <<? string "."

let stmt_name = parens name

let label = brackets name

let top_sentence : (proof_step list * id option) p =
    pair (top_prop << str ".") (option label)

let proposition_item : (id * (proof_step list * id option)) p =
  pair sub_index top_sentence

let prop_items : (id * ((proof_step list) * id option)) list p =
  many1 proposition_item

let top_prop_or_items (name: id option):
  (id * proof_step list * id option) list p =
    choice [
        prop_items;
        top_sentence |>> fun (fr, name1) -> [("", (fr, opt_or_opt name1 name))]
    ] |>> map (fun (sub_index, (steps, name)) -> (sub_index, steps, name))

let propositions name : (id * proof_step list * id option) list p =
  pipe2 (opt [] (for_all_ids << str ",")) (top_prop_or_items name)
  (fun vars props ->
    props |> map (fun (id, steps, name) -> (id, Let vars :: steps, name)))

(* axioms *)

let unary_prefix id typ =
  if arity typ = 1 && id = "-" then "u-" else id

let words2 : string p =
    pipe2 word (option word) (fun w x ->
        String.concat " " (w :: Option.to_list x)) 

let type_decl : statement p =
    pipe2 (str "a type" >> id) (option (parens (str "the" >> words2)))
        (fun id opt_name -> TypeDecl (id, Option.map singular opt_name))

let const_decl : statement p =
    pipe2 ((any_str ["a constant"; "an element"; "a function"] <|> operation) >> id_or_sym)
        (of_type >> typ)
        (fun c typ -> ConstDecl (unary_prefix c typ, typ))

let axiom_decl : statement p = type_decl <|> const_decl

let count_sub_index num sub_index =
  if sub_index = "" then sprintf "%d" num
  else sprintf "%d.%s" num sub_index

let axiom_propositions name : statement list p =
  let> st = get_user_state in
  incr st.axiom_count;
  propositions name |>> map (fun (sub_index, steps, name) ->
    HAxiom (count_sub_index (!(st.axiom_count)) sub_index, steps, name))

let axiom_exists name : statement list p =
  there_exists >>? pipe2
  (sep_by1 axiom_decl (any_str ["and"; "with"]))
  ((str "such that" >> axiom_propositions name) <|> (str "." >>$ []))
  (@)

let axiom_group : statement list p =
  (str "Axiom" >> option stmt_name << str ".") >>= fun name ->
  (axiom_exists name <|> axiom_propositions name)

(* definitions *)

let mk_def id typ formula = Definition (id, typ, Eq (Const (id, typ), formula))

let new_paragraph : id p = empty >>? (any_str keywords <|> sub_index)

let define ids_types prop : statement =
  let prop = for_all_vars_types ids_types prop in
  Definition ("_", unknown_type, prop)

let def_prop : formula p = 
    not_followed_by new_paragraph "" >> opt_str "we write" >> small_prop << str "."

let definition : statement list p = str "Definition." >>
  choice [
    let> let_ids_types = many (let_decl <<? str ".") in
    let> ids_types = opt [] (for_all_ids << str ",") in
    let$ props = many1 (opt_str "Let" >> def_prop) in
    map (define (concat let_ids_types @ ids_types)) props
  ]

(* proofs *)

let mk_step f : proof_step =
  match kind f with
    | Quant ("∃", _, typ, _) ->
        let (ids, f) = gather_quant_of_type "∃" typ f in
        IsSome (ids, typ, f)
    | _ -> mk_assert f

let opt_contra : formula list p = opt []
  (str "," >>? (opt_str "which is " >>?
    optional (any_str ["again"; "also"; "similarly"]) >>?
    str "a contradiction" >>
    (optional (str "to" >> reference))) >>$ [_false])

let rec proof_eq_props s : formula pr =
  pipe2 proposition (option (reason >> option (pair eq_op proof_eq_props)))
  (fun f -> function
    | Some (Some (eq, g)) -> eq f g
    | _ -> f)
  s

let proof_prop : formula list p = pipe2 (
  optional (reason >> opt_str ",") >>
  optional have >> proof_eq_props
  ) opt_contra cons

let proof_if_prop : proof_step list p = pipe3
  (str "if" >> small_prop)
  (opt_str "," >> str "then" >> proof_prop)
  (many_concat (str "," >> so >> proof_prop))
  (fun f gs hs -> [Group (Assume f :: map mk_step (gs @ hs))])

let and_or_so = (str "and" << optional so) <|> so

let will_show = choice [
  str "We need to show that";
  str "We start by showing that";
  str "We will" >> (str "show" <|> str "deduce") >> str "that"
  ]

let to_show = str "To show that" >> small_prop << str ","

let assert_step : proof_step list p =
  (optional have >>? proof_if_prop) <|> (choice [
    pipe2 (any_str ["Because"; "Since"] >> proof_prop) (opt_str "," >> proof_prop) (@);
    optional to_show >> will_show >> proposition >>$ [];
    str "The result follows" >> reason >>$ [];
    single (any_str ["This is"; "We have"] >>? str "a contradiction" >>
        optional (str "to" >> reference) >>$ _false);
    optional and_or_so >> proof_prop
    ] |>> map mk_step)

let assert_steps : proof_step list p =
  let join = str "," >> and_or_so in
  pipe2 assert_step (many_concat (join >> proof_prop |>> map mk_step)) (@)

let now = any_str ["Conversely"; "Finally"; "Next"; "Now"; "Second"]

let any_case = any_str ["In any case"; "In either case"; "Putting the cases together"]

let let_or_assumes : proof_step list p =
  sep_by1 let_or_assume (str "," >> str "and") |>> concat

let clause_intro = choice [ str "First" >>$ 0; now >>$ 1; any_case >>$ 2]

let proof_clause : proof_step list p = pipe2
  (opt 0 (clause_intro << opt_str ","))
  (let_or_assumes <|> assert_steps)
  (fun now steps ->
    let esc = if now = 1 && is_assume (hd steps) || now = 2
                then [Escape] else []
    in esc @ steps)

let proof_sentence : proof_step list p =
  (sep_by1 proof_clause (str ";") |>> concat) << str "." << optional label

let proof_steps : proof_step list p =
  many1 (not_followed_by new_paragraph "" >> proof_sentence) |>>
    (fun steps -> concat steps)

let proof_item : (id * proof_step list) p = pair sub_index proof_steps

let proofs : (id * proof_step list) list p = str "Proof." >> choice [
  many1 proof_item;
  proof_steps |>> (fun steps -> [("", steps)])]

(* theorems *)

let theorem_group : statement list p =
  any_str ["Corollary"; "Lemma"; "Theorem"] >> option stmt_name << str "." >>= fun name -> 
  many_concat (let_step << str ".") >>=
  fun let_steps ->
    let> st = get_user_state in
    incr st.theorem_count;
    pipe2 (top_prop_or_items name) (opt [] proofs)
    (fun props proofs ->
      props |> map (fun (sub_index, steps, name) ->
        HTheorem (count_sub_index (!(st.theorem_count)) sub_index, name,
                  let_steps @ steps,
                  opt_default (assoc_opt sub_index proofs) [])))

(* module *)

let using : string list p = str "using" >> sep_by1 name (str ",") << str ";"

let _module : statement list p = optional using >>
  many (axiom_group <|> definition <|> theorem_group) << empty << eof |>> concat

let parse_module_text text init_state : (statement list * state) MParser.result =
  MParser.parse_string (pair _module get_user_state) text init_state

let parse_formula text = always_parse expr text (empty_state ())

let relative_name from f = mk_path (Filename.dirname from) (f ^ ".n")
  
let parse_files filenames sources : (_module list, string * frange) Stdlib.result =
  let rec parse (modules, state) filename : (_module list * state, string * frange) Stdlib.result =
    if exists (fun m -> m.filename = filename) modules then Ok (modules, state) else
      let text = opt_or (assoc_opt filename sources) (fun () -> read_file filename) in
      let using : str list =
        map (relative_name filename) (always_parse (opt [] using) text (empty_state ())) in
      let** (modules, state) = fold_left_res parse (modules, state) using in
      match parse_module_text text state with
        | Success (stmts, state) ->
            let modd = { filename; using; stmts } in
            Ok (modd :: modules, state)
        | Failed (err, Parse_error ((_index, line, col), _)) ->
            Error (err, (filename, ((line, col), (0, 0))))
        | Failed _ -> failwith "parse_files" in
  let** (modules, _state) = fold_left_res parse ([], empty_state ()) filenames in
  Ok (rev modules)

let parse_file filename = parse_files [filename] []
