open Printf

open Options
open Statement
open Thf_gen
open Thf_parse
open Util

;;

if Array.length Sys.argv = 1 then usage();

let source = parse_args (tl (Array.to_list Sys.argv)) in
  if !(opts.server) then Server.run ()
  else match source with
    | None -> usage()
    | Some source ->
        if !(opts.e_proof) then
          match parse_proof source with
            | Failed (msg, _) -> print_endline msg
            | Success formulas -> format_proof formulas
        else
          let ext = Filename.extension source in
          let parser = match ext with
            | ".n" -> Parser.parse_file
            | ".thf" -> Thf_parse.parse_thf
            | _ -> failwith "unknown extension" in
          let from_thf = (ext = ".thf") in
          let res =
            let** modules = parser source in
            Check.check from_thf modules in
          match res with
            | Error (msg, (filename, range)) ->
                printf "%s at %s: %s\n" msg filename (show_range range)
            | Ok modules ->
                if !(opts.verbose) then iter write_thm_info modules;
                if !(opts.export) then (
                  clean_dir "thf";
                  iter (export_module "thf" modules) modules)
                else
                  Prove.prove_all from_thf modules;
                  profile_report ()
