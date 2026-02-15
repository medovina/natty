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
          let res = match ext with
            | ".n" ->
                let** modules =
                  Result.bind (Parser.parse_file source) Check.check in
                Ok (false, modules)
            | ".thf" ->
                let** modules =
                  Result.bind (Thf_parse.parse_thf source) Check.basic_check_modules in
                Ok (true, modules)
            | _ -> failwith "unknown extension" in
          match res with
            | Error (msg, (filename, range)) ->
                printf "%s at %s: %s\n" msg filename (show_range range)
            | Ok (from_thf, modules) ->
                if !(opts.thm_count) then write_all_thm_info modules
                else if !(opts.export) then (
                  clean_dir "thf";
                  iter (export_module "thf" modules) modules)
                else
                  Prove.prove_all from_thf modules
