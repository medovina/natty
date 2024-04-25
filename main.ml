open List
open Printf

open Statement
open Thf_gen
open Util

let thf_file dir name = mk_path dir (name ^ ".thf")

let write_thf dir name proven stmt =
  let f = thf_file dir name in
  if not (Sys.file_exists f) then (
    let out = open_out f in
    let write is_last stmt = (
      fprintf out "%% %s\n" (show_statement false stmt);
      fprintf out "%s\n\n" (thf_statement is_last stmt)) in
    iter (write false) proven;
    write true stmt;
    Out_channel.close out)

let write_files dir prog = 
  prog |> iteri (fun i stmt -> (
    match stmt with
      | Theorem (name, _, proof) ->
          let proven = take i prog in (
          match proof with
            | Some (Formulas fs) ->
                fs |> iteri (fun j f ->
                  let step_name = sprintf "%s_%d" name (j + 1) in
                  let t = Theorem (step_name, f, None) in
                  write_thf dir step_name proven t)
            | Some _ -> assert false
            | None ->
                write_thf dir name proven stmt)
      | _ -> ()
      ))

type options = {
  debug: int;
  show_proofs: bool;
  export: bool;
}

let parse_args args =
  let (args, file) = split_last args in
  let rec parse = function
    | [] -> { debug = 0; show_proofs = false; export = false }
    | arg :: rest ->
        let args = parse rest in
        if arg.[0] = '-' then
          match arg.[1] with
            | 'd' ->
              let level =
                if arg = "-d" then 1 else int_of_string (string_from arg 2) in
              { args with debug = level }
            | 'p' -> { args with show_proofs = true }
            | 'x' -> { args with export = true }
            | _ -> failwith "unknown option"
        else failwith "option expected" in
  (parse args, file)

let usage () =
  print_endline
{|usage: prover [options] <file>.{n,thf}

    -d<level>     debug level
    -p            output proofs
    -x            export theorems to THF files
    |};
  exit 1

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
        let prog = Check.check_program prog in
        if opts.export then
          let dir = Filename.remove_extension source in
          clean_dir dir;
          write_files dir prog
        else
          Prove.prove_all opts.debug opts.show_proofs (ext = ".thf") prog
    | Failed (msg, _) ->
        print_endline msg
