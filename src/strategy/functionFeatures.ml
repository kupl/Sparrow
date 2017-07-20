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


type pid = string
type funset = pid BatSet.t

type feature = {
  (* Implemented *)
  leaf : funset; (* leaf function *)
  has_alloc : funset; (* allocate memory*)
  has_realloc : funset; 
  has_calloc : funset; 
  has_loop : funset; 
  has_branch : funset; 
  write_gvar : funset; 
  rtn_const : funset; (* return constant value *)
  rtn_void : funset; 
  pass_const : funset;  (* constants are passed to arguments *)

  (* Not implemented *)
  has_switch : funset; (* has switch statements *) 
  has_str_lib : funset; (* use string libraries *)
  read_gvar : funset; (* Done *)
  write_lvar : funset; 
  read_lvar : funset; 
  write_field : funset; 
  read_field : funset;  
  rtn_alloced : funset; (* return allocated memory : Done *)
  rtn_realloced : funset; (* return allocated memory : Done *)
  rtn_field : funset; (* return values of structure field *)
  rtn_dep_on_buf : funset; (* return values depend on buffer contents *)
  pass_unknown : funset; (* unknowns are passed to arguments: Done *)
  no_arg : funset; (* no arguments *)
  arg_one : funset; (* only one argument *)
  arg_many : funset; (* more than one args *)
  arg_int : funset; (* has integer type arguments *)
  arg_ptr : funset; (* has ptr type arguments *)
  arg_com : funset; (* has structure arguments *)
}

let empty = {
  leaf = BatSet.empty;
  has_alloc = BatSet.empty;
  has_realloc = BatSet.empty;
  has_calloc = BatSet.empty;
  has_loop = BatSet.empty;
  write_gvar = BatSet.empty;
  read_gvar = BatSet.empty;
  has_branch = BatSet.empty;
  rtn_const = BatSet.empty;
  rtn_alloced = BatSet.empty;
  rtn_realloced = BatSet.empty;
  rtn_void = BatSet.empty;
  pass_const = BatSet.empty;
  pass_unknown = BatSet.empty;
  write_lvar = BatSet.empty;
  read_lvar  = BatSet.empty;
  write_field = BatSet.empty;
  read_field = BatSet.empty;
  no_arg = BatSet.empty;
  arg_one = BatSet.empty; 
  arg_many = BatSet.empty;
  arg_int  = BatSet.empty;
  arg_ptr  = BatSet.empty;
  arg_com  = BatSet.empty;
  rtn_field = BatSet.empty;  
  rtn_dep_on_buf = BatSet.empty;
  has_switch = BatSet.empty;
  has_str_lib = BatSet.empty;
}

(* Implemented *)
let add_has_loop pid feat = {feat with has_loop = BatSet.add pid feat.has_loop}
let add_has_alloc pid feat = {feat with has_alloc = BatSet.add pid feat.has_alloc}
let add_has_branch pid feat = {feat with has_branch = BatSet.add pid feat.has_branch}
let add_write_gvar pid feat = {feat with write_gvar = BatSet.add pid feat.write_gvar}
let add_rtn_void pid feat = {feat with rtn_void = BatSet.add pid feat.rtn_void}
let add_rtn_const pid feat = {feat with rtn_const = BatSet.add pid feat.rtn_const}
let add_has_realloc pid feat = {feat with has_realloc = BatSet.add pid feat.has_realloc}
let add_pass_const pid feat = {feat with pass_const = BatSet.add pid feat.pass_const}
let add_has_calloc pid feat = {feat with has_realloc = BatSet.add pid feat.has_calloc}

(* Not implemented *)
let add_pass_unknown pid feat = {feat with pass_unknown = BatSet.add pid feat.pass_unknown}
let add_read_gvar pid feat = {feat with read_gvar = BatSet.add pid feat.read_gvar}
let add_rtn_alloced pid feat = {feat with rtn_alloced = BatSet.add pid feat.rtn_alloced}
let add_rtn_realloced pid feat = {feat with rtn_alloced = BatSet.add pid feat.rtn_alloced}

let has_constant es = 
  List.exists (fun e -> match e with | Const _ -> true | _ -> false) es

let extract : Spec.t -> Global.t -> feature
= fun spec global -> 
  let locs_feature = PartialFlowSensitivity.extract_feature global spec.locset in
  let leafs = Global.get_leaf_procs global in
  let icfg = global.icfg in
  let nodes = InterCfg.nodesof icfg in
    list_fold (fun n -> 
      let pid = InterCfg.Node.get_pid n in
      (if InterCfg.is_inside_loop n icfg then add_has_loop pid else id)
      >>>
      (match InterCfg.cmdof icfg n with
      | Calloc _ -> add_has_alloc pid 
      | Cassume _ -> add_has_branch pid 
      | Cset ((Var x,NoOffset),e,_) -> 
        (if x.vglob then add_write_gvar pid else id) 
        (* >>> (if read_gvar pid e mem then add_read_gvar pid else id) *)
      | Creturn (None,_) -> add_rtn_void pid 
      | Creturn (Some (Const _),_) -> add_rtn_const pid
(*      | Creturn (Some e,_) -> 
        (if has_alloced_vars pid e mem locs_feature then add_rtn_alloced pid else id)
        >>> (if has_realloced_vars pid e mem locs_feature then add_rtn_realloced pid else id) *)
      | Ccall (_,Lval (Var f, NoOffset),_,_) when f.vname = "realloc" -> add_has_realloc pid
      | Ccall (_,Lval (Var f, NoOffset),_,_) when f.vname = "calloc" -> add_has_calloc pid
      | Ccall (_,Lval (Var f, NoOffset),es,_) ->
        (if has_constant es then add_pass_const pid else id)
        (* >>> (if has_unknown pid es mem locs_feature then add_pass_unknown pid else id) *)
      | _ -> id) 
    ) nodes empty

let prerr_feature feature = 
  let f2s funs = string_of_set id funs in
  prerr_endline ("leaf : " ^ f2s feature.leaf);
  prerr_endline ("has_alloc : " ^ f2s feature.has_alloc);
  prerr_endline ("has_realloc : " ^ f2s feature.has_realloc);
  prerr_endline ("has_calloc : " ^ f2s feature.has_calloc);
  prerr_endline ("has_loop : " ^ f2s feature.has_loop);
  prerr_endline ("has_branch : " ^ f2s feature.has_branch);
  prerr_endline ("write_gvar : " ^ f2s feature.write_gvar);
  prerr_endline ("rtn_const : " ^ f2s feature.rtn_const);
  prerr_endline ("rtn_void : " ^ f2s feature.rtn_void);
  prerr_endline ("pass_const : " ^ f2s feature.pass_const);
