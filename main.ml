open Printf

open Logic
open Options
open Statement
open Thf_gen
open Util

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name proven stmt =
  let f = thf_file dir (str_replace "." "_" name) in
  if not (Sys.file_exists f) then (
    let out = open_out f in
    let problem = Option.get (stmt_formula stmt) in
    let problem =
      if free_vars problem = [] then remove_universal problem else problem in
    fprintf out "%% Problem: %s\n\n" (show_formula problem);
    let write is_last stmt = (
      fprintf out "%% %s\n" (show_statement false stmt);
      fprintf out "%s\n\n" (thf_statement is_last stmt)) in
    iter (write false) proven;
    write true stmt;
    Out_channel.close out)

let write_files dir prog =
  Prove.expand_proofs prog true |> iter (fun (thm, known) ->
    write_thf dir (stmt_id thm) (rev known) thm)

let write_thm_info prog =
  let thms = filter is_theorem prog in
  let thm_steps = function
    | Theorem (_, _, proof, _) -> (match proof with
        | Some (ExpandedSteps steps) -> Some steps
        | Some (Steps _) -> assert false
        | None -> None)
    | _ -> assert false in
  let step_groups = filter_map thm_steps thms in
  printf "%d theorems (%d with proofs, %d without)\n"
    (length thms) (length step_groups) (length thms - length step_groups);
  printf "%d output steps\n" (length (concat step_groups))
;;

if Array.length Sys.argv = 1 then usage();

let source = parse_args (tl (Array.to_list Sys.argv)) in
  if !(opts.server) then Server.run ()
  else match source with
    | None -> usage()
    | Some source ->
        let ext = Filename.extension source in
        let parser = match ext with
          | ".n" -> Parser.parse
          | ".thf" -> Thf_parse.parse
          | _ -> failwith "unknown extension" in
        match parser (read_file source) with
          | Failed (msg, _) ->
              print_endline msg
          | Success (prog, origin_map) ->
              match Check.check_program (parser == Thf_parse.parse)
                                        origin_map prog with
                | Error (err, opt_range) ->
                    let range = match opt_range with
                      | Some r -> " at " ^ show_range r
                      | None -> "" in
                    print_endline (err ^ range)
                | Ok prog ->
                  (if !(opts.verbose) then write_thm_info prog);
                  if !(opts.export) then
                      let dir = Filename.remove_extension source in
                      clean_dir dir;
                      write_files dir prog
                    else
                      Prove.prove_all (ext = ".thf") prog;
                      profile_report ()
