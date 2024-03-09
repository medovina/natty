open List

open Prove
open Util

let rec parse_args = function
  | [] -> ("", 0)
  | arg :: rest ->
      let (name, debug) = parse_args rest in
      if arg.[0] = '-' then
        if arg.[1] = 'd' then
          let level =
            if arg = "-d" then 1 else int_of_string (string_from arg 2) in
          (name, level)
        else failwith "unknown option"
      else if name <> "" then failwith "double filename"
      else (arg, debug)

;;

if Array.length Sys.argv = 1 then (
  print_endline "usage: prover [-d] <file>";
  exit 1);

let (source, debug) = parse_args (tl (Array.to_list Sys.argv)) in
match Parser.parse (open_in source) with
  | Success prog ->
      let prog = Check.check_program prog in
      let dir = Filename.remove_extension source in
      clean_dir dir;
      if debug > 0 then clean_dir (dir ^ "_dbg");
      let names = write_files dir prog in
      prove debug dir names
  | Failed (msg, _) ->
      print_endline msg
