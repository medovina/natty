open Util

type options = {
  all_modules: bool ref;
  deferred: bool ref;
  disprove: bool ref;
  e_proof: bool ref;
  export: bool ref;
  export_full: bool ref;
  keep_going: bool ref;
  from_thm: string option ref;
  only_thm: string option ref;
  pipe: string ref;
  server: bool ref;
  show_proofs: bool ref;
  show_proof_of: int ref;
  stats: bool ref;
  timeout: float ref;
  verbose: bool ref
}

let opts = {
  all_modules = ref false;
  deferred = ref false;
  disprove = ref false;
  e_proof = ref false;
  export = ref false;
  export_full = ref false;
  from_thm = ref None;
  keep_going = ref false;
  only_thm = ref None;
  pipe = ref "";
  server = ref false;
  show_proofs = ref false;
  show_proof_of = ref 0;
  stats = ref false;
  timeout = ref 5.0;
  verbose = ref false
}

let debug = ref 0
let debug_super = ref (0, 0)

let usage () =
    print_endline
  {|usage: natty [options] <file>.{n,thf}
  
      -a                continue proof attempts even if one or more proofs fail
      -c                try to disprove all theorems
      -d<level>         debug level
      -e                reformat proof from E
      -f<name>          prove/export given theorem and following
      -h                print this help message
      -i                print proof statistics
      -l                run as language server
      -o<name>          only prove/export given theorem or proof step
      -p[<id>]          output proof of theorems, or only of given formula
      --pipe=<name>     pipe name for language server
      -r                prove theorems in all modules
      -s<id>,<id>       debug superposition of given formulas
      -t<num>           time limit in seconds
      -u                use deferred superposition
      -v                verbose output
      -x                export theorems to THF files
         -xf              also generate THF files for full theorems with proof steps
      |};
    exit 1

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
            | 'f' -> opts.from_thm := Some value
            | 'h' -> usage ()
            | 'i' -> opts.stats := true
            | 'l' -> opts.server := true
            | 'o' -> opts.only_thm := Some value
            | 'p' -> if arg = "-p" then opts.show_proofs := true
                     else opts.show_proof_of := int_val ()
            | 'r' -> opts.all_modules := true
            | 's' -> (
              match String.split_on_char ',' value with
                | [i; j] -> debug_super := (int_of_string i, int_of_string j)
                | _ -> failwith "expected formula ids")
            | 't' -> opts.timeout := float_of_string value
            | 'u' -> opts.deferred := true
            | 'v' -> opts.verbose := true
            | 'x' -> opts.export := true;
                     if arg = "-xf" then opts.export_full := true
            | '-' -> (match opt_remove_prefix "--pipe=" arg with
                        | Some name -> opts.pipe := name
                        | None -> failwith "unknown option")
            | _ -> failwith "unknown option");
          file)
        else match file with
          | Some _ -> failwith "duplicate filename"
          | None -> Some arg in
  parse args
