(* Export all List functions from this module, but omit the type List.t. *)
include (List : module type of List with type 'a t := 'a list)
open List

open Printf
open MParser

(* booleans *)

let int_of_bool b = if b then 1 else 0

(* options *)

let (let*) = Option.bind

let mk_some x = Some x

let opt_default opt def = Option.value opt ~default:def

let opt_for_all f = function
  | Some x -> f x
  | None -> true

let opt_all_eq x = opt_for_all ((=) x)

let opt_exists f = function
  | Some x -> f x
  | None -> false

let opt_fold f opt acc = fold_right f (Option.to_list opt) acc

let opt_or (x: 'a option) (y: unit -> 'a) : 'a = match x with
  | Some x -> x
  | None -> y ()

let or_opt (x: 'a option) (y: unit -> 'a option) : 'a option = match x with
  | Some x -> Some x
  | None -> y ()

let opt_or_opt (x: 'a option) (y: 'a option) : 'a option = match x with
  | Some x -> Some x
  | None -> y

(* results *)

let (let**) = Stdlib.Result.bind

(* ('a -> ('b, 'e) result) -> 'a list -> ('b list, 'e) result *)
let rec map_res f xs = match xs with
  | [] -> Ok []
  | x :: xs ->
      let** y = f x in
      let** rest = map_res f xs in
      Ok (y :: rest)

(* ('a -> 'b -> ('a, 'e) result) -> 'a -> 'b list -> ('a, 'e) result *)
let rec fold_left_res f acc xs = match xs with
  | [] -> Ok acc
  | x :: xs ->
      let** acc = f acc x in
      fold_left_res f acc xs

(* chars *)

let is_lower c = 'a' <= c && c <= 'z'

let is_upper c = 'A' <= c && c <= 'Z'

let is_letter c = is_lower c || ('A' <= c && c <= 'Z')

let is_digit c = '0' <= c && c <= '9'

let is_id_char c = is_letter c || is_digit c || c = '_'

(* strings *)

let strlen = String.length

let char_to_string = String.make 1

let string_range s i j = String.sub s i (j - i)

let string_from s i = string_range s i (String.length s)

let last_char s = s.[strlen s - 1]

let str_contains s c = Option.is_some (String.index_opt s c)

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

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let singular s =
  if last_char s = 's' then string_range s 0 (String.length s - 1)
  else failwith "word must end with 's'"

(* unicode *)

let uchar s =
  let u = String.get_utf_8_uchar s 0 in
  assert (Uchar.utf_decode_is_valid u);
  Uchar.utf_decode_uchar u

let uchar_to_string u =
  let b = Buffer.create 4 in
  Buffer.add_utf_8_uchar b u;
  Buffer.contents b

let uchars s : string list =
  let rec from i =
    if i >= strlen s then []
    else
      let d = String.get_utf_8_uchar s i in
      let c = uchar_to_string (Uchar.utf_decode_uchar d) in
      c :: from (i + Uchar.utf_decode_length d)
  in from 0

let to_digit base s : string =
    string_of_int (Uchar.to_int (uchar s) - Uchar.to_int (uchar base))

let sub_to_digit = to_digit "₀"  (* map e.g. "₀" to "0" *)

let digit_to_sub d : string =  (* map e.g. "0" to "₀" *)
  uchar_to_string (Uchar.of_int (Uchar.to_int (uchar "₀") + int_of_string d))

let usplit s : string * string =
  let i = Uchar.utf_8_decode_length_of_byte s.[0] in
  (String.sub s 0 i, string_from s i)

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

(* tuples *)

let map_fst f = map (fun (x, y) -> (f x, y))
let map_snd f = map (fun (x, y) -> (x, f y))

(* lists *)

let (let+) = fun a f -> concat_map f a

let head_opt xs = nth_opt xs 0

let rec last = function
  | [] -> failwith "last"
  | [x] -> x
  | _ :: xs -> last xs

let rec split_last (xs : 'a list) : ('a list * 'a) = match xs with
  | [] -> failwith "split_last"
  | [x] -> ([], x)
  | x :: xs ->
      let (ys, last) = split_last xs in
      (x :: ys, last)

let index_of_opt x ys = find_index ((=) x) ys

let fold_left1 f = function
  | [] -> failwith "fold_left1: empty list"
  | x :: xs -> fold_left f x xs    

let rec fold_right1 f = function
  | [] -> failwith "fold_right1: empty list"
  | [x] -> x
  | x :: xs -> f x (fold_right1 f xs)

let filter_mapi f list = filter_map (Fun.id) (mapi f list)

let rec count_true p = function
  | [] -> 0
  | x :: xs -> (if p x then 1 else 0) + count_true p xs

let rec all_pairs = function
  | [] -> []
  | x :: xs -> map (fun y -> (x, y)) xs @ all_pairs xs

let rec unzip = function
  | [] -> ([], [])
  | (x, y) :: ps ->
      let (xs, ys) = unzip ps in (x :: xs, y :: ys)

let rec unzip3 = function
  | [] -> ([], [], [])
  | (x, y, z) :: ps ->
      let (xs, ys, zs) = unzip3 ps in (x :: xs, y :: ys, z :: zs)

let subset xs ys = for_all (fun x -> mem x ys) xs

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

(* Replace x by y exactly once in the list zs. *)
let rec replace1 y x = function
  | [] -> failwith "replace1"
  | z :: zs ->
      if z = x then y :: zs
      else z :: replace1 y x zs

let std_sort xs = sort Stdlib.compare xs

let sort_by f = sort (fun x y -> Stdlib.compare (f x) (f y))

let unique l = sort_uniq Stdlib.compare l

let all_same = function
  | [] -> true
  | (x :: xs) -> for_all ((=) x) xs

let minimum (xs: 'a list) : 'a = fold_left1 min xs

let maximum (xs: 'a list) : 'a = fold_left1 max xs

let is_maximal gt x ys =
  not (exists (fun y -> y <> x && gt y x) ys)

let maximum_by f xs =
  snd (maximum (map (fun x -> (f x, x)) xs))

let sum xs = fold_left (+.) 0.0 xs

(* span f xs returns (take_while f xs, drop_while f xs). *)
let rec span f = function
  | [] -> ([], [])
  | x :: xs ->
      if f x then 
        let (xs, ys) = span f xs in (x :: xs, ys)
      else ([], x :: xs)

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
  
let gather_pairs (xs: ('a * 'b) list) : ('a * 'b list) list =
  group_by fst (fun (_, x) acc -> cons x acc) [] xs

(* association lists *)

let update_assoc (k, v) assoc = (k, v) :: remove_assoc k assoc

let remove_all_assoc k pairs = pairs |> filter (fun (k', _v) -> k <> k')

(* search *)

(* return values in reverse topological order *)
let dsearch (x: 'a) (neighbors: 'a -> 'a list) : 'a list =
  let rec find all x =
    if memq x all then all else
      x :: fold_left find all (neighbors x) in
  find [] x

let search1 sub (initial: 'a list) (neighbors: 'a -> 'a list) : 'a list =
  let rec loop visited = function
    | [] -> visited
    | x :: rest ->
        let ns = sub (neighbors x) visited in
        loop (ns @ visited) (ns @ rest) in
  loop initial initial

let search init f = search1 subtract init f
let searchq init f = search1 subtractq init f

(* I/O *)

let print_line = print_endline

let mk_path = Filename.concat

let change_extension path ext =
  Filename.chop_extension path ^ ext

let mk_dir dir = Sys.mkdir dir 0o755

let rec empty_dir dir =
  Sys.readdir dir |> Array.iter (fun file ->
    let path = mk_path dir file in
    if Sys.is_directory path then (
      empty_dir path;
      Sys.rmdir path
    ) else Sys.remove path)

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

let (<<?) p q = attempt (p << q)
let (>>=?) p q = attempt (p >>= q)

let (let>) = bind

let bind_ret p f = p >>= (fun x -> return (f x))

let (let$) = bind_ret

let single s = count 1 s

let pipe2a p1 p2 f =
  p1 >>=? fun x1 ->
  p2 >>= fun x2 ->
  return (f x1 x2)

let triple p q r = pipe3 p q r (fun x y z -> (x, y, z))

let not_before p = not_followed_by p ""

let many_concat p = many p |>> concat

let trace msg s =
  (return () |>> (fun _ -> printf "entering %s\n" msg)) >>
  s |>> (fun x ->
  printf "parsed %s\n" msg; x)

let always_parse parser text state =
  match MParser.parse_string parser text state with
    | Success x -> x
    | Failed _ -> failwith "parse failure"

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
