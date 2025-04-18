open Util

type options = {
  disprove: bool ref;
  export: bool ref;
  keep_going: bool ref;
  pipe: string ref;
  quick: bool ref;
  server: bool ref;
  show_proofs: bool ref;
  only_thm: string option ref;
  timeout: float ref;
  verbose: bool ref
}

let opts = {
  disprove = ref false;
  export = ref false;
  keep_going = ref false;
  pipe = ref "";
  quick = ref false;
  server = ref false;
  show_proofs = ref false;
  only_thm = ref None;
  timeout = ref 5.0;
  verbose = ref false
}

let debug = ref 0

let parse_args args =
  let rec parse = function
    | [] -> None
    | arg :: rest ->
        let file = parse rest in
        if arg.[0] = '-' then (
          let value = string_from arg 2 in
          let int_val () = int_of_string value in
          (match arg.[1] with
            | 'a' -> opts.keep_going := true
            | 'c' -> opts.disprove := true
            | 'd' -> let level = if arg = "-d" then 1 else int_val () in
                     debug := level
            | 'l' -> opts.server := true
            | 'n' -> opts.only_thm := Some value
            | 'p' -> opts.show_proofs := true
            | 'q' -> opts.quick := true
            | 'r' -> profiling := true
            | 't' -> opts.timeout := float_of_int (int_val ())
            | 'v' -> opts.verbose := true
            | 'x' -> opts.export := true
            | '-' -> (match opt_remove_prefix "--pipe=" arg with
                        | Some name -> opts.pipe := name
                        | None -> failwith "unknown option")
            | _ -> failwith "unknown option");
          file)
        else match file with
          | Some _ -> failwith "duplicate filename"
          | None -> Some arg in
  parse args

  let usage () =
    print_endline
  {|usage: natty [options] <file>.{n,thf}
  
      -a              continue proof attempts even if one or more proofs fail
      -c              try to disprove all theorems
      -d<level>       debug level
      -l              run as language server
      -n<name>        only prove/export theorem with given name
      -p              output proofs
      --pipe=<name>   pipe name for language server
      -q              only use quick refute
      -r              profile performance
      -t<num>         time limit in seconds
      -v              verbose output
      -x              export theorems to THF files
      |};
    exit 1
    