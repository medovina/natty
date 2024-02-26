open List
open Printf

open Logic
open Thf
open Util

let thf_file dir name = Filename.concat dir (name ^ ".thf")

let write_thf dir name proven stmt =
  let out = open_out (thf_file dir name) in
  let write is_last stmt = (
    fprintf out "%% %s\n" (show_statement stmt);
    fprintf out "%s\n\n" (thf_statement is_last stmt)) in
  iter (write false) proven;
  write true stmt;
  Out_channel.close out

let write_files dir prog = 
  prog |> mapi (fun i stmt -> (
    match stmt with
      | Theorem (name, _, proof) ->
          let proven = take i prog in
          let steps = (match proof with
            | Some (Formulas fs) ->
                fs |> fold_lefti (fun steps j f ->
                  let step_name = sprintf "%s_%d" name j in
                  let t = Theorem (step_name, f, None) in
                  write_thf dir step_name (proven @ rev steps) t;
                  t :: steps) [] |> rev
            | Some _ -> assert false
            | None -> []) in
          write_thf dir name (proven @ steps) stmt;
          steps @ [stmt]
      | _ -> [] )) |> concat

let rec prove dir = function
  | Theorem (id, _, _) as thm :: thms ->
      print_endline (show_statement thm);
      let ic = Unix.open_process_args_in "eprover-ho"
        [| "-s"; "--auto"; thf_file dir id |] in
      let lines = In_channel.input_lines ic in
      In_channel.close ic;
      if mem "# SZS status Theorem" lines then
        prove dir thms
      else
        print_endline "failed to prove!"
  | [] -> print_endline "All theorems were proved."
  | _ -> assert false
;;

if Array.length Sys.argv != 2 then (
  print_endline "usage: prover <file>";
  exit 1);

let source = Sys.argv.(1) in
match Parser.parse (open_in source) with
  | Success prog ->
      let prog = Check.check_program prog in
      let dir = Filename.remove_extension source in
      clean_dir dir;
      let names = write_files dir prog in
      prove dir names
  | Failed (msg, _) ->
      print_endline msg
