open Either
open List
open Printf

open MParser

(* functions *)

let uncurry f (x, y) = f x y

(* options *)

let (let*) = Option.bind

let opt_default opt def = Option.value opt ~default:def

let opt_fold f acc opt = fold_left f acc (Option.to_list opt)

(* chars *)

let is_lower c = 'a' <= c && c <= 'z'

let is_letter c = is_lower c || ('A' <= c && c <= 'Z')

(* strings *)

let strlen = String.length

let char_to_string = String.make 1

let string_from s i = String.sub s i (String.length s - i)

let prepend p s = p ^ s

let n_spaces n = String.make n ' '

let capitalize s =
  char_to_string (Char.uppercase_ascii s.[0]) ^ string_from s 1

let to_lower = String.lowercase_ascii

let eq_icase s t = (to_lower s = to_lower t) 

let is_char_in c s = Option.is_some (String.index_opt s c)

let starts_with p s = String.starts_with ~prefix:p s

let ends_with p s = String.ends_with ~suffix:p s

let contains s1 s2 =
  let re = Str.regexp_string s2 in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false

(* 'str_replace s t u' replaces s with t in u *)
let str_replace s = Str.global_replace (Str.regexp_string s)

let opt_remove_prefix p s =
  if starts_with p s then Some (string_from s (String.length p))
  else None

let remove_prefix p s = opt_default (opt_remove_prefix p s) s

let comma_join = String.concat ", "

let str_lines = String.split_on_char '\n'

let unlines = String.concat "\n"

let indent_by n = map (prepend (n_spaces n))

let indent_lines n s = unlines (indent_by n (str_lines s))

let indent_with_prefix prefix s =
  let lines = str_lines s in
  unlines ((prefix ^ hd lines) :: indent_by (String.length prefix) (tl lines))

let ulen c =
  if c < 0x80 then 1
  else if c < 0xe0 then 2
  else if c < 0xf0 then 3 else 4

let utf8_count f s =
  let rec len k =
    if k >= String.length s then 0
    else
      let n = ulen (Char.code s.[k]) in
      f n + len (k + n)
  in len 0 

(* Return the number of characters in a UTF-8 string. *)
let utf8_len = utf8_count (Fun.const 1)

(* Given a UTF-8 string, return the number of code units it would
 * occupy in UTF-16. *)
let utf16_encode_len = utf8_count (fun n -> if n > 3 then 2 else 1)

let ascii_map = [("·", "*"); ("≤", "<="); ("≥", ">=")]

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* either *)

let mk_left x = Left x

let gather_left_right xs =
  let f x (ls, rs) = match x with
    | Left l -> (l :: ls, rs)
    | Right r -> (ls, r :: rs) in
  fold_right f xs ([], [])

(* tuples *)

let swap (x, y) = (y, x)

(* lists *)

let (let+) = fun a f -> concat_map f a

let singleton x = [x]

let map_fst f = map (fun (x, y) -> (f x, y))
let map_triple_fst f = map (fun (x, y, z) -> (f x, y, z))

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

let index_of_opt x ys = find_index (fun z -> z = x) ys

let index_of x ys = Option.get (index_of_opt x ys)

let fold_left1 f = function
  | [] -> failwith "fold_left1: empty list"
  | x :: xs -> fold_left f x xs    

let rec fold_right1 f = function
  | [] -> failwith "fold_right1: empty list"
  | [x] -> x
  | x :: xs -> f x (fold_right1 f xs)

let fold_lefti (f: 'a -> int -> 'b -> 'a) (acc: 'a) (xs: 'b list): 'a =
  let rec fn i acc xs = match xs with
    | [] -> acc
    | (x :: xs) -> fn (i + 1) (f acc i x) xs
  in fn 0 acc xs

let rec all_pairs = function
  | [] -> []
  | x :: xs -> map (fun y -> (x, y)) xs @ all_pairs xs

let intersect xs ys = filter (fun x -> mem x ys) xs

let overlap xs ys = intersect xs ys <> []

let subtract xs ys = filter (fun x -> not (mem x ys)) xs

let subtractq xs ys = filter (fun x -> not (memq x ys)) xs

let remove x xs = subtract xs [x]

let rec remove1 x = function
  | [] -> failwith "not found"
  | y :: ys -> if x = y then ys else y :: remove1 x ys

let union xs ys = subtract xs ys @ ys

(* Replace x by y exactly once in the list zs. *)
let rec replace1 y x = function
  | [] -> failwith "replace1"
  | z :: zs ->
      if z = x then y :: zs
      else z :: replace1 y x zs

let std_sort xs = sort Stdlib.compare xs

let sort_by f = sort (fun x y -> Stdlib.compare (f x) (f y))

let unique l = sort_uniq Stdlib.compare l

let is_maximal gt x ys =
  not (exists (fun y -> y <> x && gt y x) ys)

let sum xs = fold_left (+.) 0.0 xs

(* search *)

let search xs neighbors =
  let rec loop visited = function
    | [] -> visited
    | x :: rest ->
        let ns = subtractq (neighbors x) visited in
        loop (ns @ visited) (ns @ rest) in
  loop xs xs

(* I/O *)

let print_line = print_endline

let mk_path = Filename.concat

let change_extension path ext =
  Filename.chop_extension path ^ ext

let mk_dir dir = Sys.mkdir dir 0o755

let empty_dir dir =
  Sys.readdir dir |> Array.iter (fun file -> Sys.remove (mk_path dir file))

let rm_dir dir =
  if Sys.file_exists dir then (
    empty_dir dir;
    Sys.rmdir dir
  )

let clean_dir dir =
  if Sys.file_exists dir then empty_dir dir else mk_dir dir

let read_file filename =
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let write_file filename text =
  let oc = open_out filename in
  output_string oc text;
  close_out oc

(* parsing *)

let single s = count 1 s

let triple p q r = pipe3 p q r (fun x y z -> (x, y, z))

let quadruple p q r s = pipe4 p q r s (fun w x y z -> (w, x, y, z))

let trace msg s =
  (return () |>> (fun _ -> printf "entering %s\n" msg)) >>
  s |>> (fun x ->
  printf "parsed %s\n" msg; x)

(* multisets *)

let rec remove_once x = function
  | [] -> []
  | y :: ys ->
      if x = y then ys else y :: remove_once x ys

let multi_sub xs ys = fold_left (Fun.flip remove_once) xs ys

let multi_gt gt xs ys =
  let xy, yx = multi_sub xs ys, multi_sub ys xs in
  xy <> [] && yx |> for_all (fun y -> xy |> exists (fun x -> gt x y))

(* profiling *)

let profiling = ref false

let sys_time_cost = ref 0.0
let profiling_cost = ref 0.0

let measure_cost () =
  let start = Sys.time () in
  let count = ref 1 in
  let interval = 0.05 in
  while Sys.time () -. start < interval do
    incr count
  done;
  sys_time_cost := interval /. float_of_int !count

type prof_node = {
  name: string;
  time: float ref;
  children: prof_node list ref
}

let cur_prof = ref { name = ""; time = ref 0.0; children = ref [] }

let profile name f =
  if !profiling then (
    if !sys_time_cost = 0.0 then
      measure_cost ();
    let parent = !cur_prof in
    let cur = match find_opt (fun n -> n.name = name) !(parent.children) with
      | Some child -> child
      | None ->
          let node = { name; time = ref 0.0; children = ref [] } in
          parent.children := node :: !(parent.children);
          node in
    cur_prof := cur;
    let start = Sys.time () -. !profiling_cost in
    profiling_cost := !profiling_cost +. !sys_time_cost;
    let ret = f () in
    cur.time := !(cur.time) +. (Sys.time () -. !profiling_cost) -. start;
    profiling_cost := !profiling_cost +. !sys_time_cost;
    cur_prof := parent;
    ret)
  else f ()

let profile_report () =
  if !profiling then (
    let rec print_node indent node =
      if node.name <> "" then
        printf "%s%s: %.2f\n" indent node.name !(node.time);
      let children = sort_by (fun n -> -. !(n.time)) !(node.children) in
      let indent = if node.name = "" then "" else indent ^ "  " in
      iter (print_node indent) children in
    print_node "" !cur_prof;
    printf "\nprofiling cost = %.2f\n" !profiling_cost)
