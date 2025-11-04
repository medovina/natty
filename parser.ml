open Printf

open MParser

open Logic
open Statement
open Util

let (let&) = bind

type state = {
    syntax_map : (syntax * range) list;
    axiom_count : int ref; theorem_count : int ref;
    unique_count : int ref
}

let empty_state () = {
    syntax_map = []; axiom_count = ref 0; theorem_count = ref 0; unique_count = ref 0
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

let var = empty >>? letter1

let id = str "gcd" <|> var <|>
  any_str ["𝔹"; "ℕ"; "ℤ"; "π"; "σ"; "τ"; "∏"]

let sym = choice [
  empty >>? (digit <|> any_of "+-<>|~^") |>> char_to_string;
  any_str ["·"; "≤"; "≥"; "≮"; "≯"];
  str "−" >>$ "-"]

let minus = any_str ["-"; "−"]

let mid_ellipsis : string p = any_str ["···"; "⋯"]

let id_or_sym = id <|> sym

let word = empty >>? many1_chars letter

let adjective = word

let name = empty >>? many1_chars (alphanum <|> char '_')

let to_digit base s : str =
    string_of_int (Uchar.to_int (uchar s) - Uchar.to_int (uchar base))

let sub_digit = choice [
  str "₀"; str "₁";	str "₂"; str "₃";	str "₄";
  str "₅"; str "₆"; str "₇"; str "₈"; str "₉" ] |>> to_digit "₀"

let sub_letter_map = [
  "ₐ", "a";	"ₑ", "e"; "ₕ", "h"; "ᵢ", "i"; "ⱼ", "j";	"ₖ", "k";	"ₗ", "l"; "ₘ", "m"; "ₙ", "n";
  "ₒ", "o";	"ₚ", "p"; "ᵣ", "r";	"ₛ", "s";	"ₜ", "t";	"ᵤ", "u";	"ᵥ", "v"; "ₓ", "x"
]

let sub_letters = map fst sub_letter_map

let sub_var = any_str sub_letters |>> fun s -> assoc s sub_letter_map

let sub_sym = (str "₊" >>$ "+") <|> (str "₋" >>$ "-")

(* Unicode superscript digits are not at contiguous code points. *)
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
    Var (sym, unknown_type_n !(st.unique_count))) |>> fun const ->
      fun f g ->
        let e = apply [const; f; g] in
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

(* reasons *)

let theorem_ref = str ":" >> name

let reference = choice [
  theorem_ref;
  str "part" >> parens number << opt_str "of this theorem"
  ]

let reason = choice [
  any_str ["by"; "using"] >>? reference;
  str "by" >>? optional (any_str ["the inductive"; "the induction"]) >>?
    any_str ["assumption"; "hypothesis"];
  str "by definition" ]

(* operators for small propositions *)

let so = choice [
  any_str ["also"; "consequently"; "hence"; "however"; "so";
           "then"; "therefore"; "which means that"];
  str "but" << opt_str "then";
  str "which implies" << opt_str "that" ]

let have = any_str 
  ["clearly"; "it is clear that"; "it must be that";
   "the only alternative is"; "this shows that"; "trivially";
   "we conclude that"; "we deduce that";
   "we know that"; "we must have"; "we see that"] <|>
   (str "we have" << opt_str "shown that") <|>
   (any_str ["on the other hand"; "similarly"] << opt_str ",") <|>
   (any_str ["it follows"; "it then follows"] >>
      optional ((str "from" >> reference) <|> reason) >>
      str "that")

let new_phrase = so <|> (optional reason >> have) <|> str "that"

let and_op = str "and" <<? not_followed_by new_phrase ""

(* terms *)

let compare_op op = infix op (binop_unknown op) Assoc_right

let mk_not_less f g = _not (binop_unknown "<" f g)
let mk_not_greater f g = _not (binop_unknown ">" f g)

(* We use separate constant names for unary and binary minus so that
 * a - b cannot be interpreted as (-a)(b) using implicit multiplication. *)
let unary_minus f = App (Const ("u-", unknown_type), f)

let ascribe typ f =
  App (Const (":", Fun (typ, typ)), f)

let sub_term = (sub_digit |>> _const) <|> (sub_var |>> _var)

let small_term = (number |>> _const) <|> (var |>> _var)

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

let rec parens_exprs s = (str "(" >> (sep_by1 expr (str ",") << str ")")) s

and id_term s = (id |>> _var >>=
  (fun var -> choice [
    parens_exprs |>> (fun args -> App (var, mk_tuple args));
    pipe2 sub_expr (option (pair (mid_ellipsis >> id |>> _var) sub_expr))
      (fun sub range -> match range with
        | Some (var2, sub2) ->
            assert (var = var2);
            App ((Const ("∏", unknown_type), mk_tuple [var; sub; sub2]))
        | None -> App (var, sub));
    return var
  ])) s

and term s : formula pr = (record_formula @@ choice [
  (sym |>> fun c -> Const (c, unknown_type));
  id_term;
  str "⊤" >>$ _true;
  str "⊥" >>$ _false;
  parens_exprs |>> mk_tuple;
  pipe3 (str "{" >> var) (of_type >> typ) (str "|" >> proposition << str "}")
    (fun var typ expr -> Lambda (var, typ, expr))
 ]) s

and exp_term s = pipe2 term (option super_term) (fun f super ->
  opt_fold (fun c f -> apply [Var ("^", unknown_type); f; c]) super f) s

and next_term s = (not_followed_by space "" >>? exp_term) s

and terms s = (exp_term >>= fun t -> many_fold_left mk_app t next_term) s

(* expressions *)

and compare_ops = ["<"; "≤"; ">"; "≥"]

and eq_op s = choice ([
  str "=" >>$ mk_eq;
  str "≠" >>$ mk_neq;
  str "≮" >>$ mk_not_less;
  str "≯" >>$ mk_not_greater] @
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
    infix_negop "∤" "|" Assoc_none ;  (* does not divide *)
    infix_binop "~" Assoc_none ];
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
  let app xs f = apply ([Const ("is_" ^ word, unknown_type); f] @ xs) in
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
    let g = App (Const (word, unknown_type), f) in
    if Option.is_some neg then _not g else g)
] s

and atomic s = (
  pipe2 expr (choice [
    any_str ["is true"; "always holds"] >>$ Fun.id;
    str "is" >> predicate;
    return Fun.id
   ]) (fun e f -> f e)) s

(* small propositions *)

and for_with text q s =
  pipe2 (str text >> id_type) (option with_exprs)
    (fun id_type opt_with f -> q [id_type] f opt_with) s

and post_for_all_with s = for_with "for all" for_all_with s
and post_for_some_with s = for_with "for some" exists_with s

and prop_operators = [
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

and small_prop s : formula pr = expression prop_operators
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

let let_step : proof_step_r list p = pipe2 
  (with_range let_decl |>>
    fun (ids_types, range) -> [(Let ids_types, range)])
  (opt [] (str "with" >> with_range exprs |>>
              fun (f, range) -> [(Assume f, range)]))
  (@)

let let_val_step : proof_step p = 
  pipe2 (str "let" >>? id_opt_type <<? str "=") expr
    (fun (id, typ) f ->
      (LetDef (id, typ, Eq (Const (id, typ), f))))

let define_step : proof_step p =
  pipe2 (str "define" >> atomic) for_all_ids (fun f ids_types ->
    let g = for_all_vars_types ids_types f in
    LetDef (definition_id g, unknown_type, g))

let let_def_step : proof_step_r p = with_range (let_val_step <|> define_step)

let suppose = (opt_str "also" >>? any_str ["assume"; "suppose"] >> opt_str "further" >>
    opt_str "that" >> sep_by1 proposition (opt_str "," >> str "and that"))

let assume_step : proof_step_r p = (
  with_range suppose |>>
    fun (fs, range) -> (Assume (multi_and fs), range))

let let_or_assume : proof_step_r list p =
  single let_def_step <|> let_step <|> single assume_step

let top_prop : proof_step_r list p =
  pipe2 (many_concat (let_or_assume << str "."))
  (opt_str "Then" >> with_range proposition)
  (fun lets (p, range) -> lets @ [(Assert p, range)])

(* proposition lists *)

let label : id p = 
  ((empty >>? letter |>> char_to_string) <|> number) <<? string "."

let stmt_name = parens name

let top_sentence : (proof_step_r list * id option) p =
    pair (top_prop << str ".") (option (brackets name))

let proposition_item : (id * (proof_step_r list * id option)) p =
  pair label top_sentence

let prop_items : (id * ((proof_step_r list) * id option)) list p =
  many1 proposition_item

let top_prop_or_items (name: id option):
  (id * proof_step_r list * id option) list p =
    choice [
        prop_items;
        top_sentence |>> fun (fr, name1) -> [("", (fr, opt_or_opt name1 name))]
    ] |>> map (fun (label, (steps, name)) -> (label, steps, name))

let propositions name : (id * proof_step_r list * id option) list p =
  pipe2 (with_range (opt [] (for_all_ids << str ","))) (top_prop_or_items name)
  (fun (vars, range) props ->
    props |> map (fun (id, steps, name) -> (id, (Let vars, range) :: steps, name)))

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

let count_label num label =
  if label = "" then sprintf "%d" num
  else sprintf "%d.%s" num label

let axiom_propositions name : statement list p =
  let& st = get_user_state in
  incr st.axiom_count;
  propositions name |>> map (fun (label, steps, name) ->
    HAxiom (count_label (!(st.axiom_count)) label, steps, name))

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

let eq_definition : statement p = pipe3
  (str "Let" >> sym) (str ":" >> typ) (str "=" >> term << str ".")
  mk_def

let new_paragraph : id p = empty >>? (any_str keywords <|> label)

let generalize f : formula =
  let vs = free_type_vars_in_formula f in
  let all_type x f = _for_all x Type f in
  fold_right all_type vs f

let define ids_types prop : statement p =
  let prop = for_all_vars_types ids_types prop in
  return @@ Definition ("_", unknown_type, generalize prop)

let def_prop ids_types : statement p = 
    (not_followed_by new_paragraph "" >> opt_str "we write" >> small_prop << str ".") >>=
    define ids_types

let definition : statement list p = str "Definition." >>
  choice [
    many1 eq_definition;
    (for_all_ids << str ",") >>= fun ids_types -> many1 (def_prop ids_types)
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

let rec proof_eq_props s : formula pr =
  pipe2 proposition (option (reason >> option (pair eq_op proof_eq_props)))
  (fun f -> function
    | Some (Some (eq, g)) -> eq f g
    | _ -> f)
  s

let proof_prop : (formula * range) list p = pipe2 (
  optional (reason >> opt_str ",") >>
  optional have >> with_range proof_eq_props
  ) opt_contra cons

let proof_if_prop : proof_step_r list p = with_range (triple
  (with_range (str "if" >> small_prop))
  (opt_str "," >> str "then" >> proof_prop)
  (many_concat (str "," >> so >> proof_prop))) |>>
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
    pipe2 (any_str ["Because"; "Since"] >> proof_prop) (opt_str "," >> proof_prop) (@);
    optional to_show >> will_show >> proposition >>$ [];
    str "The result follows" >> reason >>$ [];
    single (with_range (str "This is a contradiction" >>
        optional (str "to" >> reference) >>$ _false));
    optional and_or_so >> proof_prop
    ] |>> map_fst mk_step)

let assert_steps : proof_step_r list p =
  let join = str "," >> and_or_so in
  pipe2 assert_step (many_concat (join >> proof_prop |>> map_fst mk_step)) (@)

let now = any_str ["Conversely"; "Finally"; "Next"; "Now"; "Second"]

let any_case = any_str ["In any case"; "In either case"; "Putting the cases together"]

let let_or_assumes : proof_step_r list p =
  sep_by1 let_or_assume (str "," >> str "and") |>> concat

let clause_intro = choice [ str "First" >>$ 0; now >>$ 1; any_case >>$ 2]

let proof_clause : proof_step_r list p = pipe2
  (opt 0 (clause_intro << opt_str ","))
  (let_or_assumes <|> assert_steps)
  (fun now steps ->
    let esc = if now = 1 && is_assume (fst (hd steps)) || now = 2
                then [(Escape, empty_range)] else []
    in esc @ steps)

let proof_sentence : proof_step_r list p =
  (sep_by1 proof_clause (str ";") |>> concat) << str "."

let proof_steps : proof_step_r list p =
  many1 (not_followed_by new_paragraph "" >> proof_sentence) |>>
    (fun steps -> concat steps)

let proof_item : (id * proof_step_r list) p = pair label proof_steps

let proofs : (id * proof_step_r list) list p = str "Proof." >> choice [
  many1 proof_item;
  proof_steps |>> (fun steps -> [("", steps)])]

(* theorems *)

let theorem_group : statement list p =
  any_str ["Corollary"; "Lemma"; "Theorem"] >> option stmt_name << str "." >>= fun name -> 
  many_concat (let_step << str ".") >>=
  fun let_steps ->
    let& st = get_user_state in
    incr st.theorem_count;
    pipe2 (top_prop_or_items name) (opt [] proofs)
    (fun props proofs ->
      props |> map (fun (label, steps, name) ->
        HTheorem (count_label (!(st.theorem_count)) label, name,
                  let_steps @ steps,
                  opt_default (assoc_opt label proofs) [])))

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
            let modd = { filename; using; stmts; syntax_map = state.syntax_map } in
            Ok (modd :: modules, { state with syntax_map = [] })
        | Failed (err, Parse_error ((_index, line, col), _)) ->
            Error (err, (filename, ((line, col), (0, 0))))
        | Failed _ -> failwith "parse_files" in
  let** (modules, _state) = fold_left_res parse ([], empty_state ()) filenames in
  Ok (rev modules)

let parse_file filename = parse_files [filename] []
