open Util

type options = {
  debug: int; profile: bool; timeout: float; show_proofs: bool; verbose: bool;
  keep_going: bool; disprove: bool; export: bool;
  server: bool; pipe: string
}

let default_options = {
  debug = 0; profile = false; timeout = 5.0; show_proofs = false; verbose = false;
  keep_going = false; disprove = false; export = false;
  server = false; pipe = ""
}

let parse_args args =
  let rec parse = function
    | [] -> (default_options, None)
    | arg :: rest ->
        let (args, file) = parse rest in
        let value () = int_of_string (string_from arg 2) in
        if arg.[0] = '-' then
          let args = match arg.[1] with
            | 'a' -> { args with keep_going = true }
            | 'c' -> { args with disprove = true }
            | 'd' -> let level = if arg = "-d" then 1 else value () in
                     { args with debug = level }
            | 'l' -> { args with server = true }
            | 'p' -> { args with show_proofs = true }
            | 'r' -> { args with profile = true }
            | 't' -> { args with timeout = float_of_int (value ()) }
            | 'v' -> { args with verbose = true }
            | 'x' -> { args with export = true }
            | '-' -> (match opt_remove_prefix "--pipe=" arg with
                        | Some name -> { args with pipe = name }
                        | None -> failwith "unknown option")
            | _ -> failwith "unknown option" in
          (args, file)
        else match file with
          | Some _ -> failwith "duplicate filename"
          | None -> (args, Some arg) in
  parse args

  let usage () =
    print_endline
  {|usage: natty [options] <file>.{n,thf}
  
      -a              continue proof attempts even if one or more proofs fail
      -c              try to disprove all theorems
      -d<level>       debug level
      -l              run as language server
      -p              output proofs
      --pipe=<name>   pipe name for language server
      -r              profile performance
      -t<num>         time limit in seconds
      -v              verbose output
      -x              export theorems to THF files
      |};
    exit 1
    