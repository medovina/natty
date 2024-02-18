open List

(* strings *)

let char_to_string = String.make 1

let string_from s i = String.sub s i (String.length s - i)

(* lists *)

let intersect xs ys = filter (fun x -> mem x ys) xs

let subtract xs ys = filter (fun x -> not (mem x ys)) xs

let unique l = sort_uniq Stdlib.compare l
