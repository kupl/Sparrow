open Cil
open Global
open BasicDom
open Vocab
open ItvDom
open ItvSem
open IntraCfg
open IntraCfg.Cmd

module AccessSem = AccessSem.Make(ItvSem)
module AccessAnalysis = AccessAnalysis.Make(AccessSem)
module Access = ItvSem.Dom.Access

let adjust_ctxmap ctxmap global =
  let callgraph = global.callgraph in
  let ctxset = BatMap.foldi (fun pid depth -> BatSet.add (pid, depth)) ctxmap BatSet.empty in
  let transfer ctxset = 
    BatSet.fold (fun (pid,depth) set ->
      if depth > 0 then 
        if Global.is_rec pid global then set
        else 
          let callers = PowProc.fold BatSet.add (CallGraph.callers pid callgraph) BatSet.empty in 
            BatSet.fold (fun f -> BatSet.add (f,depth-1)) callers set
      else set
    ) ctxset ctxset in
  let ctxset = fix transfer ctxset in
    (* find the deepest depth *)
    BatSet.fold (fun (pid,depth) map -> 
      let old_depth = try BatMap.find pid map with _ -> -1 in 
        if depth > old_depth then BatMap.add pid depth map else map) ctxset BatMap.empty

let rec inline_with_ctxmap ctxmap global =
  (* inline functions whose depths are >= 1 *)
  let pids_to_inline = 
        BatMap.foldi (fun pid depth lst -> 
          if depth >= 1 then pid::lst else lst
        ) ctxmap [] in
    if pids_to_inline = [] then true 
    else
      let b_inlined = Frontend.inline global pids_to_inline in
      (* decrease depths by 1 *)
      let ctxmap = 
        BatMap.foldi (fun pid depth -> 
          if depth < 1 then id 
          else BatMap.add pid (depth-1)
        ) ctxmap BatMap.empty in
      inline_with_ctxmap ctxmap global

let print_ctxmap ctxmap = 
  prerr_endline "== Context Depths ==";
  BatMap.iter (fun pid depth -> prerr_endline (pid ^ " : " ^ string_of_int depth)) ctxmap

(* Generate context map from the inline option *)
let gen_ctxmap_default global = 
  let to_inline = Frontend.get_procs_to_inline global in
    list_fold (fun pid ->
      if List.mem pid to_inline then BatMap.add pid 1
      else BatMap.add pid 0
    ) (InterCfg.pidsof global.icfg) BatMap.empty
 
let inline global ctxmap = 
  let ctxmap = adjust_ctxmap ctxmap global in
  let b_inlined = inline_with_ctxmap ctxmap global in
  let _ = print_ctxmap ctxmap in
    b_inlined 
