open List
open Printf

open Logic
open Options
open Statement
open Thf_gen
open Util

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name proven stmt problem =
  let f = thf_file dir (str_replace "." "_" name) in
  if not (Sys.file_exists f) then (
    let out = open_out f in
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
  Prove.expand_proofs prog true |> iter (fun (thm, orig, known) ->
    write_thf dir (stmt_id thm) (rev known) thm orig)

;;

if Array.length Sys.argv = 1 then usage();

let (opts, source) = parse_args (tl (Array.to_list Sys.argv)) in
  let ext = Filename.extension source in
  let parser = match ext with
    | ".n" -> Parser.parse
    | ".thf" -> Thf_parse.parse
    | _ -> failwith "unknown extension" in
  match parser (open_in source) with
    | Success prog ->
        let prog = Check.check_program opts.debug prog in
        if opts.export then
          let dir = Filename.remove_extension source in
          clean_dir dir;
          write_files dir prog
        else
          Prove.prove_all opts (ext = ".thf") prog
    | Failed (msg, _) ->
        print_endline msg
