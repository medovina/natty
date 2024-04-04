open List
open Logic

let rec nnf fm = match kind fm with
  | Not f -> (match kind f with
    | Not f -> nnf f
    | Binary ("∧", f, g) ->
        mk_or (nnf (mk_not f)) (nnf (mk_not g))
    | Binary ("∨", f, g) ->
        mk_and (nnf (mk_not f)) (nnf (mk_not g))
    | Binary ("→", f, g) ->
        mk_and (nnf f) (nnf (mk_not g))
    | Quant ("∀", x, typ, f) ->
        mk_exists x typ (nnf (mk_not f))
    | Quant ("∃", x, typ, f) ->
        mk_for_all x typ (nnf (mk_not f))
    | _ -> fm)
  | Binary ("→", f, g) ->
      mk_or (nnf (mk_not f)) (nnf g)
  | Binary (op, f, g) when mem op logical_binary ->
      logical_op op (nnf f) (nnf g)
  | _ -> fm

let prove _known _f =
  print_endline "Not proved."

let prove_all prog =
  let rec loop known = function
    | [] -> print_endline "No theorems were proved."
    | stmt :: rest -> match stmt with
        | Axiom (_, f, _) | Definition (_, _, f) ->
            loop (f :: known) rest
        | Theorem (_, f, _) ->
            prove known f;
            loop (f :: known) rest
        | _ -> loop known rest in
  loop [] prog
