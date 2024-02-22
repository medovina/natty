open List
open Printf

open Logic
open Thf
open Util
;;

if Array.length Sys.argv != 2 then (
  print_endline "usage: prover <file>";
  exit 1);

let source = Sys.argv.(1) in
match Parser.parse (open_in source) with
  | Success prog ->
      let prog = Check.check_program prog in
      let base = Filename.remove_extension source in
      clean_dir base;
      prog |> iteri (fun i stmt -> (
        match stmt with
          | Theorem (name, _) ->
              let out = open_out (Filename.concat base (name ^ ".thf")) in
              take (i + 1) prog |> iteri (fun j stmt ->
                fprintf out "%% %s\n" (show_statement stmt);
                fprintf out "%s\n\n" (thf_statement (i = j) stmt))
          | _ -> () ))
  | Failed (msg, _) ->
      failwith msg
