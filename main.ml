open List
open Printf

open Ext_prove
open Util

type parsed_args = {
  prover: string;
  command: string;
  command_args: string list;
  debug: int;
  id_limit: int;
  depth_limit: int;
  min_roots: int
}

let parse_args args =
  let (args, file) = split_last args in
  let rec parse = function
    | [] -> { prover = ""; command = ""; command_args = []; debug = 0;
              depth_limit = 0; id_limit = 0; min_roots = 0 }
    | arg :: rest ->
        let args = parse rest in
        if arg.[0] = '-' then
          let int_param () = int_of_string (string_from arg 2) in
          match arg.[1] with
            | 'd' ->
              let level =
                if arg = "-d" then 1 else int_of_string (string_from arg 2) in
              { args with debug = level }
            | 'h' -> { args with depth_limit = int_param () }
            | 'l' -> { args with id_limit = int_param () }
            | 'p' -> { args with prover = "e" }
            | 'r' -> { args with min_roots = int_param () }
            | _ -> failwith "unknown option"
        else (
          assert (args.command = "");
          let words = String.split_on_char ':' arg in
          { args with command = hd words; command_args = tl words }) in
  (parse args, file)

let usage () =
  print_endline
{|usage: prover [options] [command] <file>

  global options:
    -d<level>     debug level
                    (0 = default, 1 = thf log + proof graph, 2 = trace file)
    -p            use external prover (E)

  commands:
    process       process .thf log
    tree:id,...   generate debug tree from .thf log
      -h<num>       debug tree depth limit
      -l<num>       debug tree id limit
      -r<num>       debug tree minimum roots
    |};
  exit 1

;;

if Array.length Sys.argv = 1 then usage();

let (args, source) = parse_args (tl (Array.to_list Sys.argv)) in
match args with
  | { command = ""; debug; prover; _ } -> (
      match Parser.parse (open_in source) with
        | Success prog ->
            let prog = Check.check_program prog in
            let dir = Filename.remove_extension source in
            let dir_source = mk_path dir (dir ^ ".orig.n") in
            let dir_ok = Sys.file_exists dir_source &&
              read_file dir_source = read_file source in
            if not dir_ok then (
              if Sys.file_exists dir then (
                let bak_dir = dir ^ "_bak" in
                rm_dir bak_dir;
                Sys.rename dir bak_dir
              );
              mk_dir dir;
              write_file dir_source (read_file source));
            if prover = "" then Prove.prove_all prog else (
              if debug > 0 then clean_dir (dir ^ "_dbg");
              let names = write_files dir prog in
              ext_prove debug dir names)
        | Failed (msg, _) ->
            print_endline msg)
  | { command = "process"; debug; _ } -> (
      match Ext_proof_parse.parse_file debug source with
        | MParser.Success e_proof ->
            ignore (process_proof debug source e_proof)
        | Failed (msg, _) ->
            print_endline msg)
  | { command = "tree"; command_args = [ids]; id_limit; depth_limit; min_roots; _ } ->
      let ids = String.split_on_char ',' ids in (
      match Ext_proof_parse.parse_file 2 source with
        | Success { clauses; _ } ->
            let outfile = change_extension source "_tree.dot" in
            let (matching, total) =
              write_tree clauses ids id_limit depth_limit min_roots outfile in
            printf "%d clauses matching, %d total\n" matching total
        | Failed (msg, _) ->
            print_endline msg)
  | _ ->
      usage()
