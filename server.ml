open Unix

open MParser
open Yojson
open Yojson.Basic.Util

open List
open Options
open Printf
open Prove
open Statement
open Util

let adjust_pos text (line_num, col_num) =
  let lines = str_lines text in
  let line = nth lines (line_num - 1) in
  let col_num = utf16_encode_len (String.sub line 0 (col_num - 1)) in
  (line_num - 1, col_num)

type prover_data = {
  mutex: Mutex.t;
  semaphore: Semaphore.Binary.t;
  pipe_in: file_descr;
  pipe_out: file_descr;

  (* uri, stmt to prove, known stmts *)
  statements: (string * statement * statement list) list ref;

  progress: int ref;
  not_proven: statement list ref
}

let prover_thread data =
  while true do
    Semaphore.Binary.acquire data.semaphore
  done

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

(* server *)

let check text =
  match Parser.parse text with
    | Failed (msg, Parse_error ((_index, line, col), _)) ->
        let (line, col) = adjust_pos text (line, col) in
        Error ((line, col), (line, col + 1), last (str_lines (String.trim msg)))
    | Success (prog, origin_map) -> (
        match Check.check_program 0 prog with
          | Error (err, formula) ->
              let (pos1, pos2) = match assq_opt formula origin_map with
                | Some (Range (pos1, pos2)) -> (adjust_pos text pos1, adjust_pos text pos2)
                | None -> ((0, 0), (0, 0)) in
              Error (pos1, pos2, err)
          | Ok prog -> Ok prog)
    | _ -> failwith "check"

let clear_diags output uri =
  write_message output (publish_diagnostics uri [])

let init opts =
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
  (input, output)

  let reprove sources data output f =
    sources := f !sources;
    let checked = map_snd check !sources in
    checked |> iter (fun (uri, r) ->
      let diags = match r with
        | Ok _ -> []
        | Error (pos1, pos2, err) -> [diagnostic pos1 pos2 err] in
      write_message output (publish_diagnostics uri diags));

    let rec to_prove = function
      | [] -> Some []
      | (_uri, Error _) :: _ -> None
      | (uri, Ok prog) :: rs ->
          let* ss = to_prove rs in
          Some ((expand_proofs prog false |> filter_map (
            fun (thm, _, known) ->
              match thm with
                | Theorem (_, _, None, _) -> Some (uri, thm, known)
                | _ -> None)) @ ss) in

    let stmts = opt_default (to_prove checked) [] in
    Mutex.protect data.mutex (fun () ->
      data.statements := stmts;
      data.progress := 0;
      data.not_proven := []
      );
    Semaphore.Binary.release data.semaphore

let run opts =
  if opts.pipe = "" then failwith "--pipe expected"
  else
    let (input, output) = init opts in
    let (pipe_out, pipe_in) = Unix.pipe () in
    let data = {
      mutex = Mutex.create ();
      semaphore = Semaphore.Binary.make false;
      pipe_in; pipe_out;
      statements = ref []; progress = ref 0; not_proven = ref []
      } in
    let _thread = Thread.create prover_thread data in

    let sources = ref [] in
    let reprove1 = reprove sources data output in

    while (true) do
      let msg = read_message input in
      match msg_method msg with
        | "textDocument/didOpen" ->
            reprove1 (update_assoc (parse_did_open msg))
        | "textDocument/didChange" ->
            reprove1 (update_assoc (parse_did_change msg))
        | "textDocument/didClose" ->
            let uri = parse_did_close msg in
            clear_diags output uri;
            reprove1 (remove_assoc uri)
        | _ -> printf "%s\n%!" (Basic.to_string msg)
    done
