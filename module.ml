open Util

type 's _module = {
  filename: string;
  using: string list;
  stmts: 's list;
}

let find_module modules name : 's _module =
    find (fun m -> m.filename = name) modules

let all_using md existing : 's _module list =
  let uses m = map (find_module existing) m.using in
  rev (dsearch1 (uses md) uses)

let module_env md existing : 's list =
  concat_map (fun m -> m.stmts) (all_using md existing)
