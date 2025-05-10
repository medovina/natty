(* Export all List functions from this module, but omit the type List.t. *)
include (List : module type of List with type 'a t := 'a list)
open List

open Printf
open MParser

(* options *)

let (let*) = Option.bind

let opt_default opt def = Option.value opt ~default:def

let opt_for_all f = function
  | Some x -> f x
  | None -> true

let opt_all_eq x = opt_for_all ((=) x)

let opt_exists f = function
  | Some x -> f x
  | None -> false

let opt_fold f opt acc = fold_right f (Option.to_list opt) acc

let opt_or x y = match x with
  | Some x -> x
  | None -> y ()

let or_opt x y = match x with
  | Some x -> Some x
  | None -> y ()

(* chars *)

let is_lower c = 'a' <= c && c <= 'z'

let is_letter c = is_lower c || ('A' <= c && c <= 'Z')

let is_digit c = '0' <= c && c <= '9'

let is_id_char c = is_letter c || is_digit c || c = '_'

(* strings *)

let strlen = String.length

let char_to_string = String.make 1

let string_from s i = String.sub s i (String.length s - i)

let prepend p s = p ^ s

let n_spaces n = String.make n ' '

let capitalize s =
  char_to_string (Char.uppercase_ascii s.[0]) ^ string_from s 1

let to_lower = String.lowercase_ascii

let to_upper = String.uppercase_ascii

let starts_with p s = String.starts_with ~prefix:p s

let ends_with p s = String.ends_with ~suffix:p s

(* 'str_replace s t u' replaces s with t in u *)
let str_replace s = Str.global_replace (Str.regexp_string s)

let opt_remove_prefix p s =
  if starts_with p s then Some (string_from s (String.length p))
  else None

let remove_prefix p s = opt_default (opt_remove_prefix p s) s

let comma_join = String.concat ", "

let str_lines = String.split_on_char '\n'

let unlines = String.concat "\n"

let parens_if b s = if b then sprintf "(%s)" s else s

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

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* tuples *)

let swap (x, y) = (y, x)

let map_fst f = map (fun (x, y) -> (f x, y))
let map_snd f = map (fun (x, y) -> (x, f y))

(* lists *)

let (let+) = fun a f -> concat_map f a

let head_opt xs = nth_opt xs 0

let to_option = function
  | [] -> None
  | [x] -> Some x
  | _ -> failwith "to_option"

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

let filter_mapi f list = filter_map (Fun.id) (mapi f list)

let rec all_pairs = function
  | [] -> []
  | x :: xs -> map (fun y -> (x, y)) xs @ all_pairs xs

let intersect xs ys = filter (fun x -> mem x ys) xs

let overlap xs ys = intersect xs ys <> []

let subtract xs ys = filter (fun x -> not (mem x ys)) xs
let subtractq xs ys = filter (fun x -> not (memq x ys)) xs

let remove x xs = subtract xs [x]

let rec remove1_by op x = function
  | [] -> failwith "not found"
  | y :: ys -> if op x y then ys else y :: remove1_by op x ys

let remove1 x xs = remove1_by (=) x xs
let remove1q x xs = remove1_by (==) x xs

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

let minimum xs = fold_left1 min xs

let maximum xs = fold_left1 max xs

let is_maximal gt x ys =
  not (exists (fun y -> y <> x && gt y x) ys)

let sum xs = fold_left (+.) 0.0 xs

let group_by key_fun fold init xs =
  let rec gather = function
    | [] -> []
    | x :: xs ->
        let key = key_fun x in
        match gather xs with
          | [] -> [(key, fold x init)]
          | (key', acc) :: pairs as rest ->
              if key = key' then (key, fold x acc) :: pairs
              else (key, fold x init) :: rest in
  gather (sort_by key_fun xs)
  
let gather_pairs xs =
  group_by fst (fun (_, x) acc -> cons x acc) [] xs

(* association lists *)

let update_assoc (k, v) assoc = (k, v) :: remove_assoc k assoc

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
  calls: int ref;
  time: float ref;
  children: prof_node list ref
}

let cur_prof = ref { name = ""; calls = ref 0; time = ref 0.0; children = ref [] }

let profile name f =
  if !profiling then (
    if !sys_time_cost = 0.0 then
      measure_cost ();
    let parent = !cur_prof in
    let cur = match find_opt (fun n -> n.name = name) !(parent.children) with
      | Some child -> child
      | None ->
          let node = { name; calls = ref 0; time = ref 0.0; children = ref [] } in
          parent.children := node :: !(parent.children);
          node in
    cur_prof := cur;
    let start = Sys.time () -. !profiling_cost in
    profiling_cost := !profiling_cost +. !sys_time_cost;
    let ret = f () in
    incr cur.calls;
    cur.time := !(cur.time) +. (Sys.time () -. !profiling_cost) -. start;
    profiling_cost := !profiling_cost +. !sys_time_cost;
    cur_prof := parent;
    ret)
  else f ()

let profile_report () =
  if !profiling then (
    let rec print_node indent node =
      (if node.name <> "" then
        let calls = str_replace "_" "," (sprintf "%#d" !(node.calls)) in
        printf "%s%s (%s): %.2f\n" indent node.name calls !(node.time));
      let children = sort_by (fun n -> -. !(n.time)) !(node.children) in
      let indent = if node.name = "" then "" else indent ^ "  " in
      iter (print_node indent) children in
    print_node "" !cur_prof;
    printf "\nprofiling cost = %.2f\n" !profiling_cost)
