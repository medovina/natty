open Unix
open Yojson
open Yojson.Basic.Util

open Options
open Printf
open Util

let read_message input =
  let line = String.trim (input_line input) in
  match opt_remove_prefix "Content-Length: " line with
    | None ->
        failwith "Content-Length expected"
    | Some count ->
        let line = String.trim (input_line input) in
        if line <> "" then failwith "empty line expected"
        else
          let n = int_of_string count in
          let bytes = Bytes.create n in
          really_input input bytes 0 n;
          Basic.from_string (String.of_bytes bytes)

let read_expect input method_name =
  let m = read_message input in
  assert (m |> member "method" |> to_string = method_name);
  m

let run opts =
  if opts.pipe = "" then failwith "--pipe expected"
  else
    printf "language server running: pipe = %s\n%!" opts.pipe;
    let (input, output) = open_connection (ADDR_UNIX opts.pipe) in
    printf "connected%!\n";
    
    let init = read_expect input "initialize" in
    let id = init |> member "id" in

    let result = `Assoc [("capabilities", `Assoc [("textDocumentSync", `Int 1)])] in
    let response = `Assoc [("jsonrpc", `String "2.0"); ("id", id); ("result", result)] in
    let s = Basic.to_string response in
    fprintf output "Content-Length: %d\r\n\r\n" (strlen s);
    printf "sending %s\n%!" s;
    fprintf output "%s%!" s;

    ignore (read_expect input "initialized");

    while (true) do
      let m = read_message input in
      printf "%s\n%!" (Basic.to_string m)
    done
