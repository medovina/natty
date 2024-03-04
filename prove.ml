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

let thf_file dir name = Filename.concat dir (name ^ ".thf")

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

let encode s = (replace "\n" "\\l" s) ^ "\\l"

let proof_graph formulas =
  let skolem_map = skolem_names (map formula_of formulas) in
  let index_of id =
    Option.get (find_index (fun s -> name_of s = id) formulas) in
  let box i (name, role, formula, _) =
    let color = assoc role colors in
    let formula = rename_vars (skolem_subst skolem_map formula) in
    let text = encode (indent_with_prefix (name ^ ": ") (show_formula_multi true formula)) in
    sprintf "  %d [shape = box, color = %s, fontname = monospace, label = \"%s\"]\n"
      i color text in
  let arrows i (_, _, _, source) =
    let arrow_from id = sprintf "  %d -> %d []\n" (index_of id) i in
    String.concat "" (map arrow_from (hypotheses source)) in
  let box_arrows i formula = box i formula ^ arrows i formula in
  "digraph proof {\n" ^ String.concat "" (mapi box_arrows formulas) ^ "}\n"

let rec prove debug dir = function
  | Theorem (id, _, _) as thm :: thms ->
      print_endline (show_statement true thm);
      let args =
        [| "eprover-ho"; "--auto"; (if debug then "-l6" else "-s");
           "-p"; "--proof-statistics"; "-R"; thf_file dir id |] in
      let ic = Unix.open_process_args_in "eprover-ho" args in
      let result = In_channel.input_all ic in
      In_channel.close ic;
      let debug_dir = dir ^ "_dbg" in
      if debug then
        write_file (Filename.concat debug_dir (id ^ ".thf")) result;
      (match Proof_parse.parse result with
        | Success (Some (formulas, steps, time)) ->
            let time = float_of_string time in
            let hyps = gather_hypotheses formulas in
            printf "  %.1f s, %s steps [%s]\n\n" time steps (String.concat ", " hyps);
            if debug then
              write_file (Filename.concat debug_dir (id ^ ".dot"))
                (proof_graph formulas);
            prove debug dir thms
        | Success None -> print_endline "failed to prove!"
        | Failed (msg, _) ->
            print_endline msg)
  | [] -> print_endline "All theorems were proved."
  | _ -> assert false
