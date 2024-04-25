open List
open Printf

open Logic
open Options
open Statement
open Thf_gen
open Util

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name proven stmt problem =
  let f = thf_file dir name in
  if not (Sys.file_exists f) then (
    let out = open_out f in
    fprintf out "%% Problem: %s\n\n" (show_formula (remove_universal problem));
    let write is_last stmt = (
      fprintf out "%% %s\n" (show_statement false stmt);
      fprintf out "%s\n\n" (thf_statement is_last stmt)) in
    iter (write false) proven;
    write true stmt;
    Out_channel.close out)

let write_files dir prog = 
  prog |> iteri (fun i stmt -> (
    match stmt with
      | Theorem (name, formula, proof) ->
          let proven = take i prog in (
          match proof with
            | Some (Formulas fs) ->
                fs |> iteri (fun j (f, orig) ->
                  let step_name = sprintf "%s_%d" name (j + 1) in
                  let t = Theorem (step_name, f, None) in
                  write_thf dir step_name proven t orig)
            | Some _ -> assert false
            | None ->
                write_thf dir name proven stmt formula)
      | _ -> ()
      ))

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
