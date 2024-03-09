open List

open Prove
open Util

let rec parse_args = function
  | [] -> ("", 0, None)
  | arg :: rest ->
      let (name, debug, tree) = parse_args rest in
      if arg.[0] = '-' then
        match arg.[1] with
          | 'd' ->
            let level =
              if arg = "-d" then 1 else int_of_string (string_from arg 2) in
            (name, level, tree)
          | 't' ->
              assert (arg.[2] = ':');
              let ids = String.split_on_char ',' (string_from arg 3) in
              (name, debug, Some ids)
          | _ -> failwith "unknown option"
      else if name <> "" then failwith "double filename"
      else (arg, debug, tree)

;;

if Array.length Sys.argv = 1 then (
  print_endline
{|usage: prover [options] <file>
  -d<level>   debug
  -t:id,...   generate debug tree from .thf log|};
  exit 1);

match parse_args (tl (Array.to_list Sys.argv)) with
  | (source, debug, None) -> (
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
  | (name, _, Some ids) ->
      write_tree name ids
        