open List
open Printf

open Prove
open Util

type parsed_args = {
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
    | [] -> { command = ""; command_args = []; debug = 0;
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

  options:
    -d<level>     debug level
                    (0 = default, 1 = thf log + proof graph, 2 = trace file)
    -h<num>       debug tree depth limit
    -l<num>       debug tree id limit
    -r<num>       debug tree minimum roots

  commands:
    process       process .thf log
    tree:id,...   generate debug tree from .thf log
  |};
  exit 1

;;

if Array.length Sys.argv = 1 then usage();

let (args, file) = parse_args (tl (Array.to_list Sys.argv)) in
match args with
  | { command = ""; debug; _ } -> (
      match Parser.parse (open_in file) with
        | Success prog ->
            let prog = Check.check_program prog in
            let dir = Filename.remove_extension file in
            clean_dir dir;
            if debug > 0 then clean_dir (dir ^ "_dbg");
            let names = write_files dir prog in
            prove debug dir names
        | Failed (msg, _) ->
            print_endline msg)
  | { command = "process"; debug; _ } -> (
      match Proof_parse.parse_file debug file with
        | MParser.Success e_proof ->
            ignore (process_proof debug file e_proof)
        | Failed (msg, _) ->
            print_endline msg)
  | { command = "tree"; command_args = [ids]; id_limit; depth_limit; min_roots; _ } ->
      let ids = String.split_on_char ',' ids in (
      match Proof_parse.parse_file 2 file with
        | Success { clauses; _ } ->
            let outfile = change_extension file "_tree.dot" in
            let (matching, total) =
              write_tree clauses ids id_limit depth_limit min_roots outfile in
            printf "%d clauses matching, %d total\n" matching total
        | Failed (msg, _) ->
            print_endline msg)
  | _ ->
      usage()
