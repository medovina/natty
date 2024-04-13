open List
open Printf

open Logic
open Statement
open Util

let formula_counter = ref 0

type pformula = {
  id: int;
  rule: string;
  parents: pformula list;
  formula: formula
}

let print_formula with_origin prefix pformula =
  let prefix = prefix ^ sprintf "%d. " (pformula.id) in
  let origin =
    if with_origin then sprintf " [%s]" (comma_join
      ((pformula.parents |> map (fun p -> string_of_int (p.id))) @ [pformula.rule]))
    else "" in
  printf "%s%s\n"
    (indent_with_prefix prefix (show_multi pformula.formula)) origin

let mk_pformula rule parents formula =
  { id = 0; rule; parents; formula }

let number_formula clause =
  incr formula_counter;
  let clause = { clause with id = !formula_counter } in
  print_formula true "" clause;
  clause

let create_pformula rule parents formula =
  number_formula (mk_pformula rule parents formula)

let refute pformulas =
  print_newline ();
  let queue = Queue.of_seq (to_seq pformulas) in
  let rec loop used =
    match (Queue.take_opt queue) with
      | None -> None
      | Some pformula ->
          print_formula false "given: " pformula;
          let new_pformulas = [] in
          let new_pformulas = map number_formula (rev new_pformulas) in
          let used = pformula :: used in
          print_newline ();
          match find_opt (fun p -> p.formula = _false) new_pformulas with
            | Some c -> Some c
            | None ->
                queue_add queue new_pformulas;
                loop used
  in loop []

let to_pformula stmt = stmt_formula stmt |> Option.map (fun f ->
  create_pformula (stmt_name stmt) [] f)

let prove known_stmts stmt =
  formula_counter := 0;
  let known = known_stmts |> filter_map (fun s ->
    match to_pformula s with
      | Some p -> print_newline(); Some p
      | None -> None) in
  let pformula = Option.get (to_pformula stmt) in
  let negated = create_pformula "negate" [pformula] (_not pformula.formula) in
  refute (known @ [negated])

let prove_all prog =
  let rec prove_stmts known_stmts = function
    | [] -> print_endline "All theorems were proved."
    | stmt :: rest ->
        if (match stmt with
          | Theorem _ -> (
              match prove known_stmts stmt with
                | Some _clause ->
                    printf "proof found!\n";
                    true
                | None -> false)
          | _ -> true) then (
          prove_stmts (known_stmts @ [stmt]) rest)
        else print_endline "Not proved.\n" in
  prove_stmts [] prog
