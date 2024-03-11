open List
open MParser

(* options *)

let (let*) = Option.bind

(* chars *)

let is_lower c = 'a' <= c && c <= 'z'

let is_letter c = is_lower c || ('A' <= c && c <= 'Z')

(* strings *)

let char_to_string = String.make 1

let string_from s i = String.sub s i (String.length s - i)

let prepend p s = p ^ s

let n_spaces n = String.make n ' '

let capitalize s =
  char_to_string (Char.uppercase_ascii s.[0]) ^ string_from s 1

let eq_icase s t = (String.lowercase_ascii s = String.lowercase_ascii t) 

let is_char_in c s = Option.is_some (String.index_opt s c)

let contains s1 s2 =
  let re = Str.regexp_string s2 in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false

(* 'replace s t u' replaces s with t in u *)
let replace s = Str.global_replace (Str.regexp s)

let remove_prefix p s =
  if String.starts_with ~prefix:p s
    then string_from s (String.length p) else s

let comma_join = String.concat ", "

let str_lines = String.split_on_char '\n'

let unlines = String.concat "\n"

let indent_by n = map (prepend (n_spaces n))

let indent_lines n s = unlines (indent_by n (str_lines s))

let indent_with_prefix prefix s =
  let lines = str_lines s in
  unlines ((prefix ^ hd lines) :: indent_by (String.length prefix) (tl lines))

let utf8_len s =
  let ulen c =
    if c < 0x80 then 1
    else if c < 0xe0 then 2
    else if c < 0xf0 then 3 else 4 in
  let rec len k =
    if k >= String.length s then 0
    else let n = ulen (Char.code s.[k]) in 1 + len (k + n)
  in len 0 

(* lists *)

let singleton x = [x]

let rec last = function
  | [] -> failwith "last"
  | [x] -> x
  | _ :: xs -> last xs

let rec split_last = function
  | [] -> failwith "chop_last"
  | [x] -> ([], x)
  | x :: xs ->
      let (ys, last) = split_last xs in
      (x :: ys, last)

let rec take n xs =
  if n = 0 then [] else
    match xs with
      | x :: xs -> x :: take (n - 1) xs
      | [] -> failwith "take"

let index_of y xs = Option.get (find_index (fun z -> z = y) xs)
   
let fold_left1 f = function
  | [] -> failwith "fold_left1: empty list"
  | x :: xs -> fold_left f x xs    

let fold_lefti (f: 'a -> int -> 'b -> 'a) (acc: 'a) (xs: 'b list): 'a =
  let rec fn i acc xs = match xs with
    | [] -> acc
    | (x :: xs) -> fn (i + 1) (f acc i x) xs
  in fn 0 acc xs
      
let intersect xs ys = filter (fun x -> mem x ys) xs

let overlap xs ys = intersect xs ys <> []

let subtract xs ys = filter (fun x -> not (mem x ys)) xs

let remove x xs = subtract xs [x]

let std_sort xs = sort Stdlib.compare xs

let sort_by f = sort (fun x y -> Stdlib.compare (f x) (f y))

let unique l = sort_uniq Stdlib.compare l

let group_by fold init key_vals =
  let rec gather = function
    | [] -> []
    | (key, x) :: key_vals ->
        match gather key_vals with
          | [] -> [(key, fold x init)]
          | (key', acc) :: pairs as rest ->
              if key = key' then (key, fold x acc) :: pairs
              else (key, fold x init) :: rest in
  gather (sort_by fst key_vals)

let gather_pairs xs = group_by cons [] xs

(* I/O *)

let mk_path = Filename.concat

let change_extension path ext =
  Filename.chop_extension path ^ ext

let clean_dir dir =
  if Sys.file_exists dir then
    Sys.readdir dir |> Array.iter (fun file -> Sys.remove (mk_path dir file))
  else
    Sys.mkdir dir 0o755

let write_file filename text =
  let oc = open_out filename in
  output_string oc text;
  close_out oc

(* parsing *)

let single s = count 1 s

let triple p q r = pipe3 p q r (fun x y z -> (x, y, z))

let quadruple p q r s = pipe4 p q r s (fun w x y z -> (w, x, y, z))
