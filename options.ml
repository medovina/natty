open Util

type options = {
  debug: int;
  timeout: float;
  show_proofs: bool;
  export: bool;
}

let parse_args args =
  let (args, file) = split_last args in
  let rec parse = function
    | [] -> { debug = 0; timeout = 0.0; show_proofs = false; export = false }
    | arg :: rest ->
        let args = parse rest in
        let value () = int_of_string (string_from arg 2) in
        if arg.[0] = '-' then
          match arg.[1] with
            | 'd' ->
              let level = if arg = "-d" then 1 else value () in
              { args with debug = level }
            | 'p' -> { args with show_proofs = true }
            | 't' -> { args with timeout = float_of_int (value ()) }
            | 'x' -> { args with export = true }
            | _ -> failwith "unknown option"
        else failwith "option expected" in
  (parse args, file)

  let usage () =
    print_endline
  {|usage: prover [options] <file>.{n,thf}
  
      -d<level>     debug level
      -p            output proofs
      -t<num>       time limit in seconds
      -x            export theorems to THF files
      |};
    exit 1
    