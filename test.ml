open List

(* multisets *)

let rec remove_once x = function
  | [] -> []
  | y :: ys ->
      if x = y then ys else y :: remove_once x ys

let multi_sub xs ys = fold_left (Fun.flip remove_once) xs ys

let multi_gt comparer xs ys =
  let xy, yx = multi_sub xs ys, multi_sub ys xs in
  xy <> [] && yx |> for_all (fun y -> xy |> exists (fun x -> comparer x y > 0))
