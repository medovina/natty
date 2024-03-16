open Fun
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
  let cs = filter (starts_with "esk") (unique (concat_map consts fs)) in
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

let simplify_info info =
  if info = "new_given" then "given" else info

let id_prefix = "c_0_"

let strip_id = remove_prefix id_prefix

let id_to_num id =
  if starts_with id_prefix id then int_of_string_opt (strip_id id) else None

let show_attributes prefix = function
  | Some atts -> prefix ^ sprintf "(%d/%d)" atts.proof_depth atts.proof_size
  | None -> ""

let proof_graph debug all_clauses proof_clauses highlight clause_info shade =
  let index_of id =
    find_index (fun s -> s.name = id) proof_clauses in
  let box i { name; role; formula; source; _ } =
    let color = assoc role colors in
    let (outcome, eval_info) = opt_default (assoc_opt name clause_info) (None, None) in
    let suffix =
      if debug > 1 then
        let orig_name = find_map
          (fun c -> if c.formula = formula then Some c.name
                    else None) all_clauses in
        match orig_name with
          | Some orig -> if orig = name then ""
                         else sprintf " (%s)" orig
          | None -> " (none)"
      else show_attributes " " eval_info in
    let name_suffix = sprintf "%s%s: " name suffix in
    let text = encode (indent_with_prefix name_suffix (show_multi formula)) in
    let hyps = hypotheses source in
    let explain =
      if length hyps <= 1 then
        comma_join (subtract (rev (source_rules source)) ["variable_rename"])
      else show_source source in
    let explain_info = String.concat "\\n\\n"
      ((if explain = "" then [] else [explain]) @ Option.to_list outcome) in
    let text = text ^ (if explain_info = "" then "" else "\\n" ^ explain_info) in
    sprintf "  %d [shape = box, color = %s, %s%sfontname = monospace, label = \"%s\"]\n"
      i color
      (if mem name highlight then "penwidth = 3, " else "")
      (if shade name then "style = filled, fillcolor = oldlace," else "")
      text in
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
      (if info = "new_given" then "\n" else "")
      (indent_with_prefix (name ^ ": ") (show_multi formula))
      (show_source source)
      (if info <> "" then sprintf " (%s)" (simplify_info info) else "")
      );
  close_out oc

let find_main_phase clauses = clauses |> find_map (fun c ->
  if c.info = "move_eval" then id_to_num c.name else None)
  
let write_given_trace file clauses heuristic_def =
  let main_phase = find_main_phase clauses in
  let oc = open_out file in

  heuristic_def |> Option.iter (fun hs ->
    hs |> iteri (fun i h -> fprintf oc "[%d] %s\n" i h);
    fprintf oc "\n");

  let rec loop n = function
    | [] -> ()
    | { name; formula; info; arg; attributes; _ } :: rest ->
        let n' =
          if info = "new_given" && id_to_num name >= main_phase
            then (
              let queue = match arg with
                | Some arg -> sprintf "[%s] " arg
                | None -> "" in
              let prefix = sprintf "%d. %s%s: " n queue name in
              fprintf oc "%s%s\n"
                (indent_with_prefix prefix (show_multi formula))
                (show_attributes "   " attributes);
              n + 1)
            else n in
        loop n' rest in
  loop 1 clauses;
  
  close_out oc

let skolem_adjust clauses =
  let skolem_map = skolem_names (map (fun c -> c.formula) clauses) in
  let adjust f = rename_vars (skolem_subst skolem_map f) in
  map (map_clause adjust)

let process_proof debug path = function
  | MParser.Success { clauses = all_clauses; heuristic_def; proof; user_time = time } ->
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
              (proof_graph debug all_clauses (adjust proof_clauses) [] [] (const false))
        | _ -> ());
      if debug > 1 then (
        write_trace (change_extension path ".trace") all_clauses;
        write_given_trace
          (change_extension path ".given.trace") all_clauses heuristic_def));
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
      | Some (x, depth) ->
          if depth < max_depth - 1 || max_depth = 0 then
            let cs = children x in
            let new_cs = StringSet.diff (StringSet.of_list cs) visited in
            let elems = Seq.map (fun x -> (x, depth + 1)) (StringSet.to_seq new_cs) in
            Queue.add_seq q elems;
            loop (StringSet.union new_cs visited)
          else loop visited
      | _ -> StringSet.to_list visited in
  loop (StringSet.of_list roots)

let lookup map id = opt_default (assoc_opt id map) []

let parents clause = hypotheses_of clause

let id_maps clauses mapper =
  let pairs_from clause =
    map (fun parent -> (clause.name, mapper parent)) (parents clause) in
  let pairs = concat_map pairs_from clauses in
  (gather_pairs pairs, gather_pairs (map swap pairs))

let is_empty c = match c.source with
  | Id _ -> true
  | _ -> false

let reduce_clause clause_map down_map resolve c =
  let has_one_child c = match assoc_opt c.name down_map with
    | Some [_] -> true
    | _ -> false in
  let elide c = is_empty c || has_one_child c && match source_rules c.source with
    | [rule] -> mem rule
        ["assume_negation"; "fof_nnf"; "shift_quantors"; "skolemize"; "variable_rename"]
    | _ -> false in
  let rec reduce id =
    let id = resolve id in
    match StringMap.find_opt id clause_map with
      | Some c when elide c -> reduce_source c.source
      | _ -> Id id
  and reduce_source s = match s with
    | Id id -> reduce id
    | Inference (name, status, parents) ->
        Inference (name, status, map reduce_source parents)
    | File _ -> s in
  if elide c then None else Some { c with source = reduce_source c.source }

let write_debug_tree thf_file roots clause_limit depth_limit min_roots =
  match Proof_parse.parse_file 2 thf_file with
    | Success { clauses; _ } ->
        let clauses = if clause_limit = 0 then clauses else take clause_limit clauses in
        let clause_map = StringMap.of_list (clauses |> map (fun c -> (c.name, c))) in
        roots |> iter (fun id ->
          if not (StringMap.mem id clause_map) then failwith ("id not found: " ^ id));
        let resolve id =
          if StringMap.mem id clause_map then id
          else match id_to_num id with
            | Some n -> (nth clauses (n - 1)).name
            | None -> id in
        let begin_main_phase = find_main_phase clauses in
        let is_pre_main id = id_to_num id < begin_main_phase in
        let is_given clause = clause.info = "new_given" && not (is_pre_main clause.name) in
        let is_eval clause = clause.info = "eval" || clause.info = "move_eval" in
        let all_given = clauses |> filter_map (fun c ->
          if is_given c then Some c.name else None) in
        let clauses = skolem_adjust clauses clauses in
        let (_, down_map) = id_maps clauses resolve in
        let rec descendents clause =
          let child = lookup down_map clause.name |> find_map (fun id ->
            let c = StringMap.find id clause_map in
            if is_empty c then Some c else None) in
          match child with
            | None -> []
            | Some c -> c :: descendents c in
        let info clause =
          let ds = descendents clause in
          let outcome = ds |> find_map (fun c ->
            if is_given c then
              Some (sprintf "given #%d @ %s" (index_of c.name all_given + 1)
                      (strip_id c.name))
            else None) in
          let eval_attrs = ds |> find_map (fun c ->
            if is_eval c then c.attributes else None) in
          (outcome, eval_attrs) in
        let reduced_clauses =
          filter_map (reduce_clause clause_map down_map resolve) clauses in
        let (child_parents, parent_children) = id_maps reduced_clauses Fun.id in
        let selected_ids =
          if min_roots = 0 then bfs roots depth_limit (lookup parent_children)
          else
            roots |> concat_map (fun root ->
                bfs [root] depth_limit (lookup parent_children)) |>
              count_roots |> filter_map (fun (id, num_roots) ->
                if num_roots >= min_roots then Some id else None) in
        let all_ids = bfs selected_ids 0 (lookup child_parents) in
        let tree_clauses = filter_map
          (fun id -> find_clause_opt id reduced_clauses) all_ids in
        printf "%d clauses matching, %d total\n"
          (length selected_ids) (length tree_clauses);
        let clause_info = reduced_clauses |> map (fun c -> (c.name, info c)) in
        let tree_file = (Filename.chop_extension thf_file) ^ "_tree.dot" in
        write_file tree_file
          (proof_graph 0 [] tree_clauses roots clause_info is_pre_main)
    | Failed (msg, _) ->
        print_endline msg
