open Util

type 's _module = {
  filename: string;
  using: string list;
  stmts: 's list;
}

let find_module modules name : 's _module =
    find (fun m -> m.filename = name) modules

let all_using md existing : 's _module list =
  let uses m = map (find_module existing) m.using in
  rev (dsearch1 (uses md) uses)

let module_env md existing : 's list =
  concat_map (fun m -> m.stmts) (all_using md existing)

let relative_name from f = mk_path (Filename.dirname from) f

let parse_modules using_parser text_parser filenames sources :
    ('s _module list, string * frange) Stdlib.result =
  let rec parse modules filename : ('s _module list, string * frange) Stdlib.result =
    if exists (fun m -> m.filename = filename) modules then Ok modules else
      let text = opt_or (assoc_opt filename sources) (fun () -> read_file filename) in
      let using : string list =
        map (relative_name filename) (always_parse using_parser text) in
      let** modules = fold_left_res parse modules using in
      match MParser.parse_string text_parser text () with
        | Success stmts ->
            let modd = { filename; using; stmts } in
            Ok (modd :: modules)
        | Failed (err, Parse_error ((_index, line, col), _)) ->
            Error (err, (filename, ((line, col), (0, 0))))
        | Failed _ -> failwith "parse_files" in
  let** modules = fold_left_res parse [] filenames in
  Ok (rev modules)
