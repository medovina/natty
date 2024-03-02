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
          let proven = take i prog in (
          match proof with
            | Some (Formulas fs) ->
                fs |> mapi (fun j f ->
                  let step_name = sprintf "%s_%d" name j in
                  let t = Theorem (step_name, f, None) in
                  write_thf dir step_name proven t;
                  t)
            | Some _ -> assert false
            | None ->
                write_thf dir name proven stmt;
                [stmt])
      | _ -> [] )) |> concat

let rec prove debug dir = function
  | Theorem (id, _, _) as thm :: thms ->
      print_string (show_statement thm);
      flush stdout;
      let args =
        [| "eprover-ho"; "--auto"; (if debug then "-l6" else "-s");
           "-p"; "--proof-statistics"; "-R"; thf_file dir id |] in
      let ic = Unix.open_process_args_in "eprover-ho" args in
      let result = In_channel.input_all ic in
      In_channel.close ic;
      if debug then (
        let oc = open_out (Filename.concat (dir ^ "_dbg") (id ^ ".thf")) in
        output_string oc result;
        close_out oc) else ();
      if contains result "SZS status Theorem" then
        let exp = Str.regexp {|# Proof object total steps +: \([0-9]+\)|} in
        ignore (Str.search_forward exp result 0);
        let steps = Str.matched_group 1 result in
        printf " [%s steps]\n" steps;
        prove debug dir thms
      else
        print_endline "failed to prove!"
  | [] -> print_endline "All theorems were proved."
  | _ -> assert false

let rec parse_args = function
  | [] -> ("", false)
  | arg :: rest ->
      let (name, debug) = parse_args rest in
      if arg.[0] = '-' then
        if arg.[1] = 'd' then (name, true)
        else failwith "unknown option"
      else if name != "" then failwith "double filename"
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
      if debug then clean_dir (dir ^ "_dbg") else ();
      let names = write_files dir prog in
      prove debug dir names
  | Failed (msg, _) ->
      print_endline msg
