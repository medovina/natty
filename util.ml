open List

(* options *)

let (let*) = Option.bind

(* chars *)

let is_lower c = 'a' <= c && c <= 'z'

(* strings *)

let char_to_string = String.make 1

let string_from s i = String.sub s i (String.length s - i)

let capitalize s =
  char_to_string (Char.uppercase_ascii s.[0]) ^ string_from s 1

let eq_icase s t = (String.lowercase_ascii s = String.lowercase_ascii t) 

let contains s1 s2 =
  let re = Str.regexp_string s2 in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false

(* lists *)

let singleton x = [x]

let rec last = function
  | [x] -> x
  | _ :: xs -> last xs
  | [] -> failwith "last"

let rec take n xs =
  if n = 0 then [] else
    match xs with
      | x :: xs -> x :: take (n - 1) xs
      | [] -> failwith "take"

let fold_left1 f = function
  | [] -> failwith "fold_left1: empty list"
  | x :: xs -> fold_left f x xs    

let fold_lefti (f: 'a -> int -> 'b -> 'a) (acc: 'a) (xs: 'b list): 'a =
  let rec fn i acc xs = match xs with
    | [] -> acc
    | (x :: xs) -> fn (i + 1) (f acc i x) xs
  in fn 0 acc xs
      
let intersect xs ys = filter (fun x -> mem x ys) xs

let overlap xs ys = intersect xs ys != []

let subtract xs ys = filter (fun x -> not (mem x ys)) xs

let remove x xs = subtract xs [x]

let unique l = sort_uniq Stdlib.compare l

(* I/O *)

let clean_dir dir =
  if Sys.file_exists dir then
    Sys.readdir dir |> Array.iter (fun file -> Sys.remove (Filename.concat dir file))
  else
    Sys.mkdir dir 0o755
