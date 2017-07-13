open Graph
open Cil
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

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module AccessAnalysis = AccessAnalysis.Make (AccessSem.Make (ItvSem))
module DUGraph = Dug.Make (ItvSem.Dom)
module SsaDug = SsaDug.Make (DUGraph) (AccessAnalysis)

exception ConversionFailure

(* formulas *)
type ae = Var of string | Num of int | Mul of ae * ae | Add of ae * ae | Sub of ae * ae | ArrSize of ae 
type formula = 
  | True | False | Not of formula | Eq of ae * ae | Lt of ae * ae | Le of ae * ae
  | And of formula * formula | Or of formula * formula

let rec string_of_ae e = 
  match e with
  | Var x -> x | Num n -> string_of_int n | ArrSize e -> ("arrsize(" ^ string_of_ae e ^ ")")
  | Mul (e1,e2) -> ("(" ^ string_of_ae e1 ^ " * " ^ string_of_ae e2 ^ ")")
  | Add (e1,e2) -> ("(" ^ string_of_ae e1 ^ " + " ^ string_of_ae e2 ^ ")")
  | Sub (e1,e2) -> ("(" ^ string_of_ae e1 ^ " - " ^ string_of_ae e2 ^ ")")

let rec string_of_formula f =
  match f with
  | True -> "true" | False -> "false" | Not f -> ("not " ^ string_of_formula f)
  | Eq (e1, e2)  -> string_of_ae e1 ^ " = " ^ string_of_ae e2
  | Lt (e1, e2)  -> string_of_ae e1 ^ " < " ^ string_of_ae e2
  | And (f1, f2) -> string_of_formula f1 ^ " ^ " ^ string_of_formula f2
  | Or (f1, f2)  -> string_of_formula f1 ^ " v " ^ string_of_formula f2

let slice_dug : DUGraph.t -> Report.query -> DUGraph.t
= fun dug query ->
  let same_pid node = (InterCfg.Node.get_pid node = InterCfg.Node.get_pid query.node) in
  let reachable = 
    let add_preds nodes =
      BatSet.fold (fun node -> 
        let preds = List.filter same_pid (DUGraph.pred node dug) in
          list_fold BatSet.add preds
      ) nodes nodes in
      fix add_preds (BatSet.singleton query.node) in
    DUGraph.project dug reachable

let rec convert_exp : exp -> ae
= fun exp ->
  match exp with
  | Const (CInt64 (i64,_,_)) -> Num (Cil.i64_to_int i64)
  | Lval (Var vi, NoOffset)  -> Var vi.vname
  | BinOp (PlusA, e1, e2, _) -> Add (convert_exp e1, convert_exp e2)
  | _ -> raise ConversionFailure

let convert_allocsite_to_size allocsite = Var (Allocsite.to_string allocsite ^ ".size")

let deref2vc : Report.query -> exp * exp -> Mem.t -> formula
= fun query (e1,e2) mem -> 
  let arr = ArrSize (convert_exp e1) in
  let idx = convert_exp e2 in
    Lt (idx, arr)
 
let query2vc : Report.query -> ItvAnalysis.Table.t -> formula
= fun query inputof -> 
  let mem = Table.find query.node inputof in
    match query.exp with
    | ArrayExp (lv, e, _) -> deref2vc query (Lval lv, e) mem
    | DerefExp (BinOp (PlusPI,e1,e2,_), _) -> deref2vc query (e1,e2) mem
    | _ -> True

let generate_vc : Report.query -> Global.t -> ItvAnalysis.Table.t * ItvAnalysis.Table.t -> DUGraph.t -> formula
= fun query global (inputof, outputof) dug -> 
  let vc_query = query2vc query inputof in
  prerr_endline (string_of_formula vc_query);
    vc_query

let solve_vc : formula -> bool
= fun formula -> true (* TODO *)

let verify : Global.t -> DUGraph.t -> ItvAnalysis.Table.t -> ItvAnalysis.Table.t -> Report.query -> bool
= fun global dug inputof outputof query -> 
  prerr_endline ("** verifying " ^ Report.string_of_query query);
  let dug_sliced = slice_dug dug query in
  let formula  = generate_vc query global (inputof, outputof) dug_sliced in
  let verified = solve_vc formula in
  (* print_string (DUGraph.to_dot dug_sliced); *)
    verified

let perform : Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list -> 
              Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list
= fun (global, inputof, outputof, queries) -> 
  let spec = ItvAnalysis.get_spec global in
  let access = AccessAnalysis.perform global spec.Spec.locset (ItvSem.run Strong spec) spec.Spec.premem in
  let dug = SsaDug.make (global, access, spec.Spec.locset_fs) in
  let queries_unproven = Report.get queries Report.UnProven in
  let queries_unproven = List.filter (fun q -> not (verify global dug inputof outputof q)) queries_unproven in
    (global, inputof, outputof, queries_unproven)
