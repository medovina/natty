open List
open Printf

open Logic
open Proof
open Thf
open Util

let first_var = function
  | Base "ℕ" -> "a"
  | Fun (_, Bool) -> "P"
  | _ -> "x"

let next_var x names =
  let all = map snd names in
  let rec next x =
    if mem x all then next (char_to_string (Char.chr (Char.code (x.[0]) + 1)))
    else x in
  next x

let rename_vars f =
  let rec rename names h = match h with
    | Const (id, typ) -> (Const (id, typ), names)
    | Var (id, typ) -> (Var (assoc id names, typ), names)
    | App (f, g) | Eq (f, g) ->
        let (f, names) = rename names f in
        let (g, names) = rename names g in
        (app_or_eq h f g, names)
    | Lambda (id, typ, f) ->
        let x = next_var (first_var typ) names in
        let (f, names) = rename ((id, x) :: names) f in
        (Lambda (x, typ, f), names) in
  fst (rename [] f)

let skolem_names fs =
  let cs = filter (String.starts_with ~prefix:"esk") (unique (concat_map consts fs)) in
  let name names c =
    let d = next_var (if String.ends_with ~suffix:"_0" c then "a" else "f") names in
    (c, d) :: names in
  fold_left name [] cs

let rec skolem_subst names f = match f with
  | Const (id, typ) ->
      (match assoc_opt id names with
        | Some name -> Const ("$" ^ name, typ)
        | None -> f)
  | _ -> map_formula (skolem_subst names) f

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name proven stmt =
  let out = open_out (thf_file dir name) in
  let write is_last stmt = (
    fprintf out "%% %s\n" (show_statement false stmt);
    fprintf out "%s\n\n" (thf_statement is_last stmt)) in
  iter (write false) proven;
  write true stmt;
  Out_channel.close out

let write_files dir prog = 
  prog |> mapi (fun i stmt -> (
    match stmt with
      | Theorem (name, _, proof) ->
          let proven = take i prog in (
          match proof with
            | Some (Formulas fs) ->
                fs |> mapi (fun j f ->
                  let step_name = sprintf "%s_%d" name j in
                  let t = Theorem (step_name, f, None) in
                  write_thf dir step_name proven t;
                  t)
            | Some _ -> assert false
            | None ->
                write_thf dir name proven stmt;
                [stmt])
      | _ -> [] )) |> concat

let colors = [
  ("axiom", "forestgreen"); ("conjecture", "red");
  ("plain", "forestgreen"); ("negated_conjecture", "blue")]

let encode s =
  if is_char_in '\n' s
    then replace "\n" "\\l" s ^ "\\l" (* all lines left-aligned *)
    else s ^ "\\n"  (* centers string *)

let given = "new_given"

let proof_graph debug all_clauses proof_clauses =
  let index_of id =
    find_index (fun s -> s.name = id) proof_clauses in
  let box i { name; role; formula; source; info } =
    let color = assoc role colors in
    let suffix =
      if debug > 1 then
        let orig_name = find_map
          (fun c -> if c.formula = formula then Some c.name
                    else None) all_clauses in
        match orig_name with
          | Some orig -> if orig = name then ""
                         else sprintf " (%s)" (remove_prefix "c_0_" orig)
          | None -> " (none)"
      else "" in
    let name = sprintf "%s%s: " name suffix in
    let text = encode (indent_with_prefix name (show_formula_multi true formula)) in
    let hyps = hypotheses source in
    let explain =
      if info = given then "given"
      else if hyps = [] then ""
      else if length hyps = 1 then comma_join (rev (source_rules source))
      else show_source source in
    let text = text ^ (if explain = "" then "" else "\\n" ^ explain) in
    sprintf "  %d [shape = box, color = %s, fontname = monospace, label = \"%s\"]\n"
      i color text in
  let arrows i clause =
    let arrow_from id = match index_of id with
      | Some index -> sprintf "  %d -> %d []\n" index i
      | None -> "" (* parent may be absent in a debug tree *) in
    String.concat "" (map arrow_from (hypotheses clause.source)) in
  let box_arrows i clause = box i clause ^ arrows i clause in
  "digraph proof {\n" ^ String.concat "" (mapi box_arrows proof_clauses) ^ "}\n"

let write_trace file clauses =
  let oc = open_out file in
  clauses |> iter (fun { name; formula; source; info; _ } ->
    fprintf oc "%s%s [%s]%s\n"
      (if info = given then "\n" else "")
      (indent_with_prefix (name ^ ": ") (show_formula_multi true formula))
      (show_source source)
      (if info = given then " (given)" else "")
      )
      ;
  close_out oc

let skolem_adjust clauses =
  let skolem_map = skolem_names (map (fun c -> c.formula) clauses) in
  let adjust f = rename_vars (skolem_subst skolem_map f) in
  map (map_clause adjust)

let rec prove debug dir = function
  | Theorem (id, _, _) as thm :: thms ->
      print_endline (show_statement true thm);
      let prog = "eprover-ho" in
      let args = Array.of_list (
        [ prog; "--auto"; (if debug > 0 then "-l6" else "-s");
           "-T"; "20000"; "-p"; "--proof-statistics"; "-R"] @
          (if debug > 1 then ["-S"; "--print-sat-info"] else []) @
          [thf_file dir id ]) in
      let ic = Unix.open_process_args_in prog args in
      let result = In_channel.input_all ic in
      In_channel.close ic;
      let debug_dir = dir ^ "_dbg" in
      if debug > 0 then
        write_file (mk_path debug_dir (id ^ ".thf")) result;
      (match Proof_parse.parse debug result with
        | Success (all_clauses, proof, time) ->
            let time = float_of_string time in
            let all = match proof with
              | Some (proof_clauses, steps) ->
                  let hyps = gather_hypotheses proof_clauses in
                  printf "  %.1f s, %s steps [%s]\n\n" time steps (comma_join hyps);
                  if debug > 1 then all_clauses else proof_clauses
              | None ->
                  printf "failed to prove (%.1f s)!\n" time;
                  all_clauses in
            if debug > 0 then (
              let adjust = skolem_adjust all in
              let all_clauses = adjust all in (
              match proof with
                | Some (proof_clauses, _) ->
                    write_file (mk_path debug_dir (id ^ ".dot"))
                      (proof_graph debug all_clauses (adjust proof_clauses))
                | _ -> ());
              if debug > 1 then
                write_trace (mk_path debug_dir (id ^ ".trace")) all_clauses);
            if Option.is_some proof then
              prove debug dir thms
        | Failed (msg, _) ->
            print_endline msg)
  | [] -> print_endline "All theorems were proved."
  | _ -> assert false

let write_tree thf_file ids limit =
  match Proof_parse.parse_file 2 thf_file with
    | Success (clauses, _proof, _time) ->
        let clauses = if limit = 0 then clauses else take limit clauses in
        let clauses = skolem_adjust clauses clauses in
        ids |> iter (fun id ->
          if Option.is_none (find_clause_opt id clauses) then
            failwith ("id not found: " ^ id));
        let pairs_from clause =
          map (fun parent -> (parent, clause.name)) (hypotheses_of clause) in
        let pairs = sort Stdlib.compare (concat_map pairs_from clauses) in
        let parent_map = gather_pairs pairs in
        let rec reachable_from p =
          match assoc_opt p parent_map with
            | Some children -> 
                p :: concat_map reachable_from children
            | None -> [] in
        let tree_clause_ids = concat_map reachable_from ids in
        let tree_clauses = map (fun id -> find_clause id clauses) tree_clause_ids in
        printf "%d clauses found\n" (length tree_clauses);
        let tree_file = (Filename.chop_extension thf_file) ^ "_tree.dot" in
        write_file tree_file (proof_graph 0 [] tree_clauses)
    | Failed (msg, _) ->
        print_endline msg
