open Unix

open MParser
open Yojson
open Yojson.Basic.Util

open List
open Options
open Printf
open Util

let adjust_pos text (line_num, col_num) =
  let lines = str_lines text in
  let line = nth lines (line_num - 1) in
  let col_num = utf16_encode_len (String.sub line 0 (col_num - 1)) in
  (line_num - 1, col_num)

let check text =
  match Parser.parse text with
    | Failed (msg, Parse_error ((_index, line, col), _)) ->
        let (line, col) = adjust_pos text (line, col) in
        Some ((line, col), (line, col + 1), last (str_lines (String.trim msg)))
    | Success (prog, origin_map) -> (
        match Check.check_program 0 prog with
          | Error (err, formula) ->
              let (pos1, pos2) = match assq_opt formula origin_map with
                | Some (pos1, pos2) -> (adjust_pos text pos1, adjust_pos text pos2)
                | None -> ((0, 0), (0, 0)) in
              Some (pos1, pos2, err)
          | Ok _ -> None)
    | _ -> failwith "check"

(* Yojson *)

let mem_str name j = j |> member name |> to_string

(* base protocol *)

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

let write_message output msg =
  let s = Basic.to_string msg in
  fprintf output "Content-Length: %d\r\n\r\n" (strlen s);
  printf "sending %s\n%!" s;
  fprintf output "%s%!" s

let message data = `Assoc (("jsonrpc", `String "2.0") :: data)

let response id result = message [("id", id); ("result", result)]

let notification mth params = message [("method", `String mth); ("params", params)]

let msg_method = mem_str "method"

let params = member "params"

(* JSON structures *)

let range start_pos end_pos =
  let line_char (line, char) = `Assoc [("line", `Int line); ("character", `Int char)] in
  `Assoc [("start", line_char start_pos); ("end", line_char end_pos)]

let diagnostic start_pos end_pos message =
  `Assoc [("range", range start_pos end_pos); ("message", `String message)]

(* lifecycle messages *)

let parse_initialize init =
  assert (msg_method init = "initialize");
  (init |> member "id",
   params init |> member "workspaceFolders" |> index 0 |> mem_str "uri")

(* document synchronization *)

let parse_did_open msg =
  let doc = params msg |> member "textDocument" in
  (doc |> mem_str "uri", doc |> mem_str "text")

let parse_did_change msg =
  let p = params msg in
  (p |> member "textDocument" |> mem_str "uri",
   p |> member "contentChanges" |> index 0 |> mem_str "text")

let parse_did_close msg =
  params msg |> member "textDocument" |> mem_str "uri"

(* language features *)

let publish_diagnostics uri diagnostics =
  notification "textDocument/publishDiagnostics" @@
  `Assoc [("uri", `String uri); ("diagnostics", `List diagnostics)]

(* main loop *)

let report output (uri, text) = 
  let diags = Option.to_list (check text) |> map (fun (pos1, pos2, err) ->
    diagnostic pos1 pos2 err) in
  write_message output (publish_diagnostics uri diags)

let clear_diags output uri =
  write_message output (publish_diagnostics uri [])

let run opts =
  if opts.pipe = "" then failwith "--pipe expected"
  else
    printf "language server running: pipe = %s\n%!" opts.pipe;
    let (input, output) = open_connection (ADDR_UNIX opts.pipe) in
    printf "connected%!\n";
    
    let (id, uri) = parse_initialize (read_message input) in
    let folder = Option.get (opt_remove_prefix "file://" uri) in
    printf "folder = %s\n%!" folder;

    let result = `Assoc [("capabilities", `Assoc [("textDocumentSync", `Int 1)])] in
    write_message output (response id result);

    let inited = read_message input in
    assert (msg_method inited = "initialized");

    while (true) do
      let msg = read_message input in
      match msg_method msg with
        | "textDocument/didOpen" -> report output (parse_did_open msg)
        | "textDocument/didChange" -> report output (parse_did_change msg)
        | "textDocument/didClose" -> clear_diags output (parse_did_close msg)
        | _ -> printf "%s\n%!" (Basic.to_string msg)
    done
