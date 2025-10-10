open Unix

open Yojson
open Yojson.Basic.Util

open Options
open Printf
open Prove
open Statement
open Util

let adjust_pos text (line_num, col_num) : pos =
  let lines = str_lines text in
  let line = nth lines (line_num - 1) in
  let col_num = utf16_encode_len (String.sub line 0 (col_num - 1)) in
  (line_num - 1, col_num)

type prover_data = {
  mutex: Mutex.t;
  semaphore: Semaphore.Binary.t;
  notify_out: out_channel;

  (* filename, theorem to prove, known stmts *)
  statements: (string * statement * statement list) list ref;

  progress: int ref;
  not_proven: (string * statement) list ref    (* filename, theorem *)
}

let cancel_check data stmts () : bool =
  Mutex.protect data.mutex (fun () -> !(data.statements) != stmts)

let prove_stmts data stmts =
  let rec loop = function
    | [] -> ()
    | (filename, thm, known) :: ss ->
        let success =
          printf "proving %s\n%!" (stmt_name thm);
          let (proof, _elapsed) =
            prove known thm (cancel_check data stmts) in
          match proof with
            | Proof _ -> true
            | _ -> false in
        let abort = Mutex.protect data.mutex (fun () ->
          if !(data.statements) != stmts then true
          else (
            incr data.progress;
            if not success then
              data.not_proven := (filename, thm) :: !(data.not_proven);
            false
          )) in
        if abort then
          printf "worker thread: aborting\n%!"
        else (
          fprintf data.notify_out "notify\n%!";
          loop ss) in
  loop stmts

let prover_thread data =
  let stmts = ref [] in
  while true do
    Semaphore.Binary.acquire data.semaphore;
    let ss = Mutex.protect data.mutex (fun () -> !(data.statements)) in
    if ss != !stmts then (
      stmts := ss;
      prove_stmts data !stmts
    )
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

let response msg result = message [("id", member "id" msg); ("result", result)]

let notification mth params = message [("method", `String mth); ("params", params)]

let msg_method = mem_str "method"

let params = member "params"

(* JSON structures *)

let range start_pos end_pos =
  let line_char (line, char) = `Assoc [("line", `Int line); ("character", `Int char)] in
  `Assoc [("start", line_char start_pos); ("end", line_char end_pos)]

type severity = DiagError | Warning | Information | Hint

let severity_code = function
  | DiagError -> 1 | Warning -> 2 | Information -> 3 | Hint -> 4

let diagnostic start_pos end_pos severity message =
  `Assoc [("range", range start_pos end_pos);
          ("severity", `Int (severity_code severity));
          ("message", `String message)]

(* lifecycle messages *)

let parse_initialize init : string =
  assert (msg_method init = "initialize");
  params init |> member "workspaceFolders" |> index 0 |> mem_str "uri"

(* document synchronization *)

let parse_did_open msg : string * string =
  let doc = params msg |> member "textDocument" in
  (doc |> mem_str "uri", doc |> mem_str "text")

let parse_did_change msg : string * string =
  let p = params msg in
  (p |> member "textDocument" |> mem_str "uri",
   p |> member "contentChanges" |> index 0 |> mem_str "text")

let parse_did_close msg : string =
  params msg |> member "textDocument" |> mem_str "uri"

(* language features *)

let publish_diagnostics uri diagnostics =
  notification "textDocument/publishDiagnostics" @@
  `Assoc [("uri", `String uri); ("diagnostics", `List diagnostics)]

(* server *)

let uri_to_filename uri = remove_prefix "file://" uri
let filename_to_uri f = "file://" ^ f

let text_of sources file =
  opt_or (assoc_opt file sources) (fun () -> read_file file)

let check (sources : (string * string) list) : (_module list, string * frange) result =
  let res =
    let** modules = Parser.parse_files (map fst sources) sources in
    Check.check false modules in
  match res with
    | Error (err, (filename, (pos1, pos2))) ->
        let text = text_of sources filename in
        let (line, col) as pos1 = if pos1 = (0, 0) then (0, 0) else adjust_pos text pos1 in
        let pos2 = if pos2 = (0, 0) then (line, col + 1) else adjust_pos text pos2 in
        let frange = (filename, (pos1, pos2)) in
        Error (last (str_lines (String.trim err)), frange)
    | Ok modules -> Ok modules

let update_diagnostics output existing new_diags =
  let output_diags (filename, ds) =
    write_message output (publish_diagnostics (filename_to_uri filename) ds) in
  let new_filenames = map fst new_diags in
  !existing |> iter (fun filename ->
    if not (mem filename new_filenames) then output_diags (filename, []));
  iter output_diags new_diags;
  existing := new_filenames

let init opts : in_channel * out_channel =
  printf "language server running: pipe = %s\n%!" !(opts.pipe);
  let (input, output) = open_connection (ADDR_UNIX !(opts.pipe)) in
  printf "connected%!\n";
  
  let msg = read_message input in
  let uri = parse_initialize msg in
  let folder = uri_to_filename uri in
  printf "folder = %s\n%!" folder;

  let result = `Assoc [("capabilities", `Assoc [("textDocumentSync", `Int 1)])] in
  write_message output (response msg result);

  let inited = read_message input in
  assert (msg_method inited = "initialized");
  (input, output)

let notify_progress output n total =
  write_message output (notification "natty/progress" (
    `List [`Int n; `Int total]))

let reprove sources existing_diags data output proving =
  let diags, stmts = match check sources with
    | Error (msg, (filename, (pos1, pos2))) ->
        [(filename, [diagnostic pos1 pos2 DiagError msg])], []
    | Ok modules ->
        [], if proving then expand_modules modules else [] in
  update_diagnostics output existing_diags diags;
  
  Mutex.protect data.mutex (fun () ->
    data.statements := stmts;
    data.progress := 0;
    data.not_proven := []
    );
  Semaphore.Binary.release data.semaphore;
  notify_progress output 0 (length stmts)

let run () =
  if !(opts.pipe) = "" then failwith "--pipe expected"
  else
    let (input, output) = init opts in
    let input_descr = descr_of_in_channel input in
    let (pipe_read, pipe_write) = Unix.pipe () in
    let notify_in = in_channel_of_descr pipe_read in
    let data = {
      mutex = Mutex.create ();
      semaphore = Semaphore.Binary.make false;
      notify_out = out_channel_of_descr pipe_write;
      statements = ref []; progress = ref 0; not_proven = ref []
      } in
    let _thread = Thread.create prover_thread data in

    let sources : (str * str) list ref = ref [] in
    let existing_diags = ref [] in
    let proving = ref false in
    let reprove1 () = reprove !sources existing_diags data output !proving in

    let exit = ref false in
    while (not !exit) do
      let (ready_in, _, _) = select [input_descr; pipe_read] [] [] (-1.0) in
      if memq input_descr ready_in then
        let msg = read_message input in
        match msg_method msg with
          | "textDocument/didOpen" ->
              let uri, text = parse_did_open msg in
              sources := update_assoc (uri_to_filename uri, text) !sources;
              reprove1 ()
          | "textDocument/didChange" ->
              let uri, text = parse_did_change msg in
              sources := update_assoc (uri_to_filename uri, text) !sources; 
              reprove1 ()
          | "textDocument/didClose" ->
              let uri = parse_did_close msg in
              sources := remove_assoc (uri_to_filename uri) !sources;
              reprove1 ()
          | "natty/setProving" ->
              proving := params msg |> index 0 |> to_bool;
              reprove1 ()
          | "shutdown" ->
              write_message output (response msg `Null)
          | "exit" ->
              exit := true
          | _ -> printf "%s\n%!" (Basic.to_string msg)
      else
        ignore (input_line notify_in);
        if !proving then (
          let (n, not_proven, total) = Mutex.protect data.mutex (fun () ->
            (!(data.progress), !(data.not_proven), length (!(data.statements)))) in
          notify_progress output n total;
          let all_diags =
            gather_pairs not_proven |> map (fun (filename, stmts) ->
              let text = text_of !sources filename in
              let stmts = stmts |> map (function
                | Theorem (_, _, _, _, (pos1, pos2)) as thm ->
                    diagnostic (adjust_pos text pos1) (adjust_pos text pos2) Warning
                      ("could not prove " ^ (stmt_name thm))
                | _ -> assert false) in
              (filename, stmts)) in
          update_diagnostics output existing_diags all_diags
        )
    done
