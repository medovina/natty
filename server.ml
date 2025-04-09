open Unix

open MParser
open Yojson
open Yojson.Basic.Util

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
  notify_out: out_channel;

  (* uri, theorem to prove, known stmts *)
  statements: (string * statement * statement list) list ref;

  progress: int ref;
  not_proven: (string * statement) list ref    (* uri, theorem *)
}

let cancel_check data stmts () =
  Mutex.protect data.mutex (fun () -> !(data.statements) != stmts)

let prove_stmts data stmts =
  let rec loop = function
    | [] -> ()
    | (uri, thm, known) :: ss ->
        let success =
          printf "proving %s\n%!" (stmt_name thm);
          match prove !(opts.timeout) known thm false (cancel_check data stmts) with
            | Proof _ -> true
            | _ -> false in
        let abort = Mutex.protect data.mutex (fun () ->
          if !(data.statements) != stmts then true
          else (
            incr data.progress;
            if not success then
              data.not_proven := (uri, thm) :: !(data.not_proven);
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

let parse_initialize init =
  assert (msg_method init = "initialize");
  params init |> member "workspaceFolders" |> index 0 |> mem_str "uri"

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
        match Check.check_program false origin_map prog with
          | Error (err, range) ->
              let (pos1, pos2) = match range with
                | Some (Range (pos1, pos2)) -> (adjust_pos text pos1, adjust_pos text pos2)
                | None -> ((0, 0), (0, 0)) in
              Error (pos1, pos2, err)
          | Ok prog -> Ok prog)
    | _ -> failwith "check"

let clear_diags output uri =
  write_message output (publish_diagnostics uri [])

let init opts =
  printf "language server running: pipe = %s\n%!" !(opts.pipe);
  let (input, output) = open_connection (ADDR_UNIX !(opts.pipe)) in
  printf "connected%!\n";
  
  let msg = read_message input in
  let uri = parse_initialize msg in
  let folder = Option.get (opt_remove_prefix "file://" uri) in
  printf "folder = %s\n%!" folder;

  let result = `Assoc [("capabilities", `Assoc [("textDocumentSync", `Int 1)])] in
  write_message output (response msg result);

  let inited = read_message input in
  assert (msg_method inited = "initialized");
  (input, output)

  let notify_progress output n total =
    write_message output (notification "natty/progress" (
      `List [`Int n; `Int total]))

  let reprove sources data output proving f =
    sources := f !sources;

    let checked = map_snd check !sources in
    checked |> iter (fun (uri, r) ->
      let diags = match r with
        | Ok _ -> []
        | Error (pos1, pos2, err) -> [diagnostic pos1 pos2 DiagError err] in
      write_message output (publish_diagnostics uri diags));

    let rec to_prove = function
      | [] -> Some []
      | (_uri, Error _) :: _ -> None
      | (uri, Ok prog) :: rs ->
          let* ss = to_prove rs in
          Some ((expand_proofs prog |> filter_map (
            fun (thm, known) ->
              match thm with
                | Theorem (_, _, None, _) -> Some (uri, thm, known)
                | _ -> None)) @ ss) in

    let stmts =
      if proving then opt_default (to_prove checked) [] else [] in
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

    let sources = ref [] in
    let proving = ref false in
    let reprove1 f = reprove sources data output !proving f in

    let exit = ref false in
    while (not !exit) do
      let (ready_in, _, _) = select [input_descr; pipe_read] [] [] (-1.0) in
      if memq input_descr ready_in then
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
          | "natty/setProving" ->
              proving := params msg |> index 0 |> to_bool;
              reprove1 Fun.id
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
          gather_pairs not_proven |> iter (fun (uri, stmts) ->
            let diags = stmts |> map (function
              | Theorem (_, _, _, Range (pos1, pos2)) as thm ->
                  let text = assoc uri !sources in
                  diagnostic (adjust_pos text pos1) (adjust_pos text pos2) Warning
                    ("could not prove " ^ (stmt_name thm))
              | _ -> assert false) in
            write_message output (publish_diagnostics uri diags))
        )
    done
