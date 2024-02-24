open List
open Printf

open Logic
open Thf
open Util

let write_thf base name proven stmt =
  let out = open_out (Filename.concat base (name ^ ".thf")) in
  let write is_last stmt = (
    fprintf out "%% %s\n" (show_statement stmt);
    fprintf out "%s\n\n" (thf_statement is_last stmt)) in
  iter (write false) proven;
  write true stmt

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
          | Theorem (name, _, proof) ->
              let proven = take i prog in
              let steps = (match proof with
                | Some (Steps fs) ->
                    fs |> mapi (fun j f ->
                      let step_name = sprintf "%s_%d" name j in
                      let t = Theorem (step_name, f, None) in
                      write_thf base step_name proven t;
                      t)
                | Some _ -> assert false
                | None -> []) in
              write_thf base name (proven @ steps) stmt
          | _ -> () ))
  | Failed (msg, _) ->
      failwith msg
