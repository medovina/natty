open Util

type options = {
  disprove: bool ref;
  e_proof: bool ref;
  export: bool ref;
  keep_going: bool ref;
  no_quick: bool ref;
  only_quick: bool ref;
  pipe: string ref;
  server: bool ref;
  show_proofs: bool ref;
  show_proof_of: int ref;
  only_thm: string option ref;
  timeout: float ref;
  verbose: bool ref
}

let opts = {
  disprove = ref false;
  e_proof = ref false;
  export = ref false;
  keep_going = ref false;
  no_quick = ref false;
  only_quick = ref false;
  pipe = ref "";
  server = ref false;
  show_proofs = ref false;
  show_proof_of = ref 0;
  only_thm = ref None;
  timeout = ref 5.0;
  verbose = ref false
}

let debug = ref 0
let debug_super = ref (0, 0)

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
            | 'e' -> opts.e_proof := true
            | 'l' -> opts.server := true
            | 'n' -> opts.only_thm := Some value
            | 'p' -> if arg = "-p" then opts.show_proofs := true
                     else opts.show_proof_of := int_val ()
            | 'q' -> opts.only_quick := true
            | 'r' -> profiling := true
            | 's' -> (
              match String.split_on_char ',' value with
                | [i; j] -> debug_super := (int_of_string i, int_of_string j)
                | _ -> failwith "expected formula ids")
            | 't' -> opts.timeout := float_of_int (int_val ())
            | 'v' -> opts.verbose := true
            | 'w' -> opts.no_quick := true
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
      -e              reformat proof from E
      -l              run as language server
      -n<name>        only prove/export theorem with given name
      -p[<id>]        output proof of theorems, or only of given formula
      --pipe=<name>   pipe name for language server
      -q              only use quick refute
      -r              profile performance
      -s<id>,<id>     debug superposition of given formulas
      -t<num>         time limit in seconds
      -v              verbose output
      -w              skip quick refute
      -x              export theorems to THF files
      |};
    exit 1
    