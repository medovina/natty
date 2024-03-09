open List

open Prove
open Util

type args = {
  file: string; debug: int; tree: string list option; tree_limit: int
}

let rec parse_args = function
  | [] -> { file = ""; debug = 0; tree = None; tree_limit = 0 }
  | arg :: rest ->
      let args = parse_args rest in
      if arg.[0] = '-' then
        match arg.[1] with
          | 'd' ->
            let level =
              if arg = "-d" then 1 else int_of_string (string_from arg 2) in
            { args with debug = level }
          | 'l' ->
            let limit = int_of_string (string_from arg 2) in
            { args with tree_limit = limit }
          | 't' ->
             assert (arg.[2] = ':');
             let ids = String.split_on_char ',' (string_from arg 3) in
             { args with tree = Some ids }
          | _ -> failwith "unknown option"
      else if args.file <> "" then failwith "double filename"
      else { args with file = arg }

;;

if Array.length Sys.argv = 1 then (
  print_endline
{|usage: prover [options] <file>
  -d<level>   debug
  -l<num>     debug tree clause limit
  -t:id,...   generate debug tree from .thf log
  |};
  exit 1);

match parse_args (tl (Array.to_list Sys.argv)) with
  | { file = source; debug; tree = None; _ } -> (
      match Parser.parse (open_in source) with
        | Success prog ->
            let prog = Check.check_program prog in
            let dir = Filename.remove_extension source in
            clean_dir dir;
            if debug > 0 then clean_dir (dir ^ "_dbg");
            let names = write_files dir prog in
            prove debug dir names
        | Failed (msg, _) ->
            print_endline msg)
  | { file = name; tree = Some ids; tree_limit = limit; _ } ->
      write_tree name ids limit
