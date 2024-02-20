open Logic
open Parser

;;

match parse () with
  | Success prog ->
      List.iter (fun s -> print_endline (show_statement s)) prog
  | Failed (msg, _) ->
      failwith msg
