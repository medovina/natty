open Unix

open Options
open Printf
open Util

let run opts =
  if opts.pipe = "" then failwith "--pipe expected"
  else
    printf "language server running: pipe = %s\n" opts.pipe;
    let (input, _output) = open_connection (ADDR_UNIX opts.pipe) in
    printf "connected\n";
    
    while (true) do
      let line = String.trim (input_line input) in
      match opt_remove_prefix "Content-Length: " line with
        | None ->
            print_endline line;
            failwith "Content-Length expected"
        | Some count ->
            let line = String.trim (input_line input) in
            if line <> "" then
              failwith "empty line expected"
            else
              let n = int_of_string count in
              let bytes = Bytes.create n in
              really_input input bytes 0 n;
              let s = String.of_bytes bytes in
              print_endline s
    done
