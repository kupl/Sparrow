open Global
open InterCfg
open BasicDom
open Vocab
open Frontend
open IntraCfg
open ItvDom
open ItvSem
open ArrayBlk
open AlarmExp
open Report

let expr_index = ref 0

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module Speck = Analysis.Spec
module AccessAnalysis = AccessAnalysis.Make (AccessSem.Make (ItvSem))
module DUGraph = Dug.Make (ItvSem.Dom)
module SsaDug = SsaDug.Make (DUGraph) (AccessAnalysis)
module Worklist = Worklist.Make (DUGraph)

type path_info = InterCfg.node list
type node_set = InterCfg.node BatSet.t

exception ConversionFailure
exception SolverConversionFailure

type ae = Var of string | Num of int | Ptr of ae 
  | Mul of ae * ae | Div of ae * ae | Add of ae * ae | Sub of ae * ae | Mod of ae * ae
  | Neg of ae 
  | Lnot of ae | Land of ae * ae | Lor of ae * ae
  | Bnot of ae
  | Band of ae * ae | Bxor of ae * ae | Bor of ae * ae | Sleft of ae * ae | Sright of ae * ae 
  | ArrSize of ae | SizeOfE of ae | Addr of ae
  | Eq of ae * ae | Lt of ae * ae | Le of ae * ae | Not of ae

type formula =
  | Undef | True | False | Not of formula | Eq of ae * ae | Lt of ae * ae | Le of ae * ae
  | And of formula * formula | Or of formula * formula

let rec varsof : formula -> string BatSet.t
= fun f -> 
  match f with
  | True | False -> BatSet.empty
  | Not f -> varsof f
  | Lt (e1,e2) | Le (e1,e2) | Eq (e1,e2) -> BatSet.union (varsof_e e1) (varsof_e e2)
  | And (f1,f2) | Or (f1,f2) -> BatSet.union (varsof f1) (varsof f2)

and varsof_e : ae -> string BatSet.t
= fun e ->
  match e with 
  | Var x -> BatSet.singleton x
  | Num _ -> BatSet.empty
  | Ptr e | Lnot e | Bnot e | Not e | Neg e -> varsof_e e
  | Mod (e1, e2) | Eq (e1, e2) | Le (e1, e2)
  | Lt (e1, e2) | Band (e1, e2) | Bxor (e1, e2) | Bor (e1, e2) 
  | Land (e1, e2) | Lor (e1, e2) | Sleft (e1, e2) | Sright (e1, e2)
  | Mul (e1,e2) | Add (e1,e2) | Sub (e1,e2) | Div (e1, e2) -> BatSet.union (varsof_e e1) (varsof_e e2)
  | ArrSize e | SizeOfE e | Addr e -> varsof_e e
  (*| Arr (e1, e2) -> BatSet.union (varsof_e e1) (varsof_e e2)*)

let rec string_of_ae e = 
  match e with
  | Ptr e -> ("*(" ^ string_of_ae e ^ ")")
  | Var x -> x | Num n -> string_of_int n | ArrSize e -> ("arrsize(" ^ string_of_ae e ^ ")")
  | SizeOfE e -> "SizeOfE(" ^ string_of_ae e ^ ")"
  | Addr e -> "Addr(" ^ string_of_ae e ^ ")"
  (*| Arr (e1, e2) -> (string_of_ae e1 ^ " + " ^ string_of_ae e2)*)
  | Mul (e1,e2) -> ("(" ^ string_of_ae e1 ^ " * " ^ string_of_ae e2 ^ ")")
  | Div (e1, e2) -> ("(" ^ string_of_ae e1 ^ " / " ^ string_of_ae e2 ^ ")")
  | Add (e1,e2) -> ("(" ^ string_of_ae e1 ^ " + " ^ string_of_ae e2 ^ ")")
  | Sub (e1,e2) -> ("(" ^ string_of_ae e1 ^ " - " ^ string_of_ae e2 ^ ")")
  | Mod (e1, e2) -> ("(" ^ string_of_ae e1 ^ " % " ^ string_of_ae e2 ^ ")")
  | Lt (e1, e2) -> ("(" ^ string_of_ae e1 ^ " < " ^ string_of_ae e2 ^ ")")
  | Le (e1, e2) -> ("(" ^ string_of_ae e1 ^ " <= " ^ string_of_ae e2 ^ ")")
  | Eq (e1, e2) -> ("(" ^ string_of_ae e1 ^ " == " ^ string_of_ae e2 ^ ")")
  | Band (e1, e2) -> ("(" ^ string_of_ae e1 ^ " & " ^ string_of_ae e2 ^ ")")
  | Bxor (e1, e2) -> ("(" ^ string_of_ae e1 ^ " ^ " ^ string_of_ae e2 ^ ")")
  | Bor (e1, e2) -> ("(" ^ string_of_ae e1 ^ " | " ^ string_of_ae e2 ^ ")")
  | Land (e1, e2) -> ("(" ^ string_of_ae e1 ^ " && " ^ string_of_ae e2 ^ ")")
  | Lor (e1, e2) -> ("(" ^ string_of_ae e1 ^ " || " ^ string_of_ae e2 ^ ")")
  | Sleft (e1, e2) -> ("(" ^ string_of_ae e1 ^ " << " ^ string_of_ae e2 ^ ")")
  | Sright (e1, e2) -> ("(" ^ string_of_ae e1 ^ " >> " ^ string_of_ae e2 ^ ")")
  | Neg e -> "- " ^ (string_of_ae e)
  | Not e -> ("not (" ^ string_of_ae e ^")")
  | Lnot e -> ("!("^string_of_ae e ^ ")")
  | Bnot e -> ("~("^string_of_ae e ^ ")")

let rec string_of_formula f =
  match f with
  | True -> "true" | False -> "false" | Not f -> ("not (" ^ string_of_formula f ^")")
  | Eq (e1, e2)  -> string_of_ae e1 ^ " == " ^ string_of_ae e2 
  | Lt (e1, e2)  -> string_of_ae e1 ^ " < " ^ string_of_ae e2
  | Le (e1, e2)  -> string_of_ae e1 ^ " <= " ^ string_of_ae e2
  | And (f1, f2) -> string_of_formula f1 ^ " ^ " ^ string_of_formula f2
  | Or (f1, f2)  -> "(" ^ string_of_formula f1 ^ " v " ^ string_of_formula f2 ^ ")"
  | Undef -> "Undef"

(************************************************)
(* data-flow analysis for constraint generation *)
(************************************************)
module DFATable = struct
  type facts = formula BatSet.t
  type node = InterCfg.Node.t
  type t = (node, facts) BatMap.t
  let empty = BatMap.empty
  let find : node -> t -> facts 
  = fun n t -> try BatMap.find n t with _ -> BatSet.empty
  let add = BatMap.add
  let add_union : node -> facts -> t -> t 
  = fun node facts t ->
    let old = find node t in
      BatMap.add node (BatSet.union facts old) t
  let string_of_facts : facts -> string
  = fun facts -> 
    BatSet.fold (fun fact str -> str ^ " ^ " ^ string_of_formula fact) facts ""
  let print t = 
    BatMap.iter (fun node facts ->
      prerr_endline (InterCfg.Node.to_string node ^ " |-> " ^ string_of_facts facts)) t
end

(* Struct for basic path information *)
module BasicPath = struct
  type branch_path_info =  (InterCfg.node, path_info) BatMap.t
  type branch_node_info = (InterCfg.node, node_set) BatMap.t
  type t = branch_path_info * branch_node_info

  let init : branch_path_info -> branch_node_info -> t
  = fun bp_info bn_info ->
    let bp_info = BatMap.empty in
    let bn_info = BatMap.empty in
    (bp_info, bn_info)

  let get_bp : t -> branch_path_info
  = fun t ->
    let (bp_info, bn_info) = t in
    bp_info

  let get_bn : t -> branch_node_info
  = fun t ->
    let (bp_info, bn_info) = t in
    bn_info

  let find_path_info : InterCfg.node -> t -> path_info
  = fun node t ->
    let (bp_info, bn_info) = t in
    try BatMap.find node bp_info with _ -> []

  let find_node_info : InterCfg.node -> t -> node_set
  = fun node t ->
    let (bp_info, bn_info) = t in
    try BatMap.find node bn_info with _ -> BatSet.empty

  let node_info_empty : t -> bool
  = fun t ->
    let (bp_info, bn_info) = t in
    if BatMap.is_empty bn_info then true
    else false

  let add_node : InterCfg.node -> node_set -> t -> t
  = fun n nodes t ->
    let (bp_info, bn_info) = t in
    let bn_info = BatMap.add n nodes bn_info in
    (bp_info, bn_info)

  let add_path : InterCfg.node -> path_info -> t -> t
  = fun n paths t ->
    let (bp_info, bn_info) = t in
    let bp_info = BatMap.add n paths bp_info in
    (bp_info, bn_info)

  let del_path_info : InterCfg.node -> t -> t
  = fun n t ->
    let basic_path = get_bp t in
    let basic_path = BatMap.remove n basic_path in
    (basic_path, get_bn t)

  let del_node_info : InterCfg.node -> t -> t
  = fun n t ->
    let nodes = get_bn t in
    let nodes = BatMap.remove n nodes in
    (get_bp t, nodes)

  let del_path_node_info : InterCfg.node -> t -> t
  = fun n t ->
    let (bp_info, bn_info) = t in
    let bp_info = BatMap.remove n bp_info in
    let bn_info = BatMap.remove n bn_info in
    (bp_info, bn_info)
(*
  let lastly_added : t -> InterCfg.node * path_info
  = fun t ->
    let last_ele =
      let rec iterate t =
        let (ele, bp_map) = BatMap.pop (get_bp t) in
        let tmp = (bp_map, get_bn t) in
        match BatMap.is_empty bp_map with
          | true -> ele
          | _ -> iterate tmp
        in
      iterate t
    in
    last_ele
*)
end