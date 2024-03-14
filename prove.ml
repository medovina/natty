open List
open Printf

open Logic
open Proof
open Thf
open Util

let first_var start_var = function
  | Fun (_, Bool) -> "P"
  | _ -> start_var

let next_var x names =
  let all = map snd names in
  let rec next x =
    if mem x all then
      let wrap c = sprintf "%c'" c in  (* add prime mark *)
      let t = match x.[0] with
        | 'o' -> wrap 'a'  (* constants a .. o *)
        | 'z' -> wrap 'q'  (* variables q .. z *)
        | _ -> char_to_string (Char.chr (Char.code x.[0] + 1)) in
      next (t ^ string_from x 1)
    else x in
  next x

let rename_vars f =
  let num_vars = count_binders f in
  let start_var = char_to_string (
    if num_vars <= 3 then 'x' else
      let c = Char.chr (Char.code 'z' - num_vars + 1) in
      if c < 'q' then 'q' else c) in
  let rec rename names h = match h with
    | Const (id, typ) -> (Const (id, typ), names)
    | Var (id, typ) -> (Var (assoc id names, typ), names)
    | App (f, g) | Eq (f, g) ->
        let (f, names) = rename names f in
        let (g, names) = rename names g in
        (app_or_eq h f g, names)
    | Lambda (id, typ, f) ->
        let x = next_var (first_var start_var typ) names in
        let (f, names) = rename ((id, x) :: names) f in
        (Lambda (x, typ, f), names) in
  fst (rename [] f)

let skolem_names fs =
  let cs = filter (String.starts_with ~prefix:"esk") (unique (concat_map consts fs)) in
  let name names c =
    let d = next_var "a" names in
    (c, d) :: names in
  fold_left name [] cs

let rec skolem_subst names f = match f with
  | Const (id, typ) ->
      (match assoc_opt id names with
        | Some name -> Const (name, typ)
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

let simplify_info info =
  if info = given then "given" else info

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
      if length hyps <= 1 then comma_join (rev (source_rules source))
      else show_source source in
    let explain =
      if info <> "" then sprintf "%s(%s)" explain (simplify_info info) else explain in
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
      (if info <> "" then sprintf " (%s)" (simplify_info info) else "")
      )
      ;
  close_out oc

let skolem_adjust clauses =
  let skolem_map = skolem_names (map (fun c -> c.formula) clauses) in
  let adjust f = rename_vars (skolem_subst skolem_map f) in
  map (map_clause adjust)

let process_proof debug path = function
  | MParser.Success (all_clauses, proof, time) ->
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
            write_file (change_extension path ".dot")
              (proof_graph debug all_clauses (adjust proof_clauses))
        | _ -> ());
      if debug > 1 then
        write_trace (change_extension path ".trace") all_clauses);
    Option.is_some proof
  | Failed (msg, _) ->
    print_endline msg;
    false

let rec prove debug dir = function
  | Theorem (id, _, _) as thm :: thms ->
      print_endline (show_statement true thm);
      let prog = "eprover-ho" in
      let debug_out = mk_path (dir ^ "_dbg") (id ^ ".thf") in
      let args = Array.of_list (
        [ prog; "--auto"; (if debug > 0 then "-l6" else "-s");
           "-T"; "10000"; "-p"; "--proof-statistics"; "-R"] @
          [thf_file dir id ]) in
      let result = if debug = 0 then
        let ic = Unix.open_process_args_in prog args in
        let process_out = In_channel.input_all ic in
        In_channel.close ic;
        Proof_parse.parse 0 process_out
      else
        let out_descr = Unix.openfile debug_out [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o640  in
        let pid = Unix.create_process prog args Unix.stdin out_descr out_descr in
        ignore (Unix.waitpid [] pid);
        Proof_parse.parse_file debug debug_out in
      if process_proof debug debug_out result then
        prove debug dir thms
  | [] -> print_endline "All theorems were proved."
  | _ -> assert false

(* given list of ids, returns list of (id, num_roots) *)
let count_roots =
  let f _id roots = roots + 1 in
  group_by Fun.id f 0

let bfs roots max_depth children =
  let q = Queue.of_seq (List.to_seq (map (fun r -> (r, 0)) roots)) in
  let rec loop visited =
    match Queue.take_opt q with
      | Some (x, depth) when depth < max_depth || max_depth = 0 ->
          let cs = children x in
          let new_cs = StringSet.diff (StringSet.of_list cs) visited in
          let elems = Seq.map (fun x -> (x, depth + 1)) (StringSet.to_seq new_cs) in
          Queue.add_seq q elems;
          loop (StringSet.union new_cs visited)
      | _ -> StringSet.to_list visited in
  loop (StringSet.of_list roots)

let lookup map id = opt_default (assoc_opt id map) []

let write_tree thf_file roots clause_limit depth_limit min_roots =
  match Proof_parse.parse_file 2 thf_file with
    | Success (clauses, _proof, _time) ->
        let clauses = if clause_limit = 0 then clauses else take clause_limit clauses in
        let clauses = skolem_adjust clauses clauses in
        roots |> iter (fun id ->
          if Option.is_none (find_clause_opt id clauses) then
            failwith ("id not found: " ^ id));
        let pairs_from clause =
          map (fun parent -> (clause.name, parent)) (hypotheses_of clause) in
        let pairs = concat_map pairs_from clauses in
        let child_parents = gather_pairs pairs in
        let parent_children = gather_pairs (map swap pairs) in
        let below = count_roots (bfs roots depth_limit (lookup parent_children)) in
        let selected_ids = below |> filter_map (fun (id, num_roots) ->
          if num_roots >= min_roots || min_roots = 0 then Some id else None) in
        let all_ids = bfs selected_ids 0 (lookup child_parents) in
        let tree_clauses = filter_map (fun id -> find_clause_opt id clauses) all_ids in
        printf "%d clauses matching, %d total\n"
          (length selected_ids) (length tree_clauses);
        let tree_file = (Filename.chop_extension thf_file) ^ "_tree.dot" in
        write_file tree_file (proof_graph 0 [] tree_clauses)
    | Failed (msg, _) ->
        print_endline msg
