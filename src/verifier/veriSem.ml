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
module Speck = Analysis.Spec
module AccessAnalysis = AccessAnalysis.Make (AccessSem.Make (ItvSem))
module DUGraph = Dug.Make (ItvSem.Dom)
module SsaDug = SsaDug.Make (DUGraph) (AccessAnalysis)
module Worklist = Worklist.Make (DUGraph)

type ae = Var of string | Num of int | Mul of ae * ae | Add of ae * ae | Sub of ae * ae | ArrSize of ae | SizeOfE of ae
type formula =
  | True | False | Not of formula | Eq of ae * ae | Lt of ae * ae | Le of ae * ae
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
  | Mul (e1,e2) | Add (e1,e2) | Sub (e1,e2) -> BatSet.union (varsof_e e1) (varsof_e e2)
  | ArrSize e | SizeOfE e -> varsof_e e

let rec string_of_ae e = 
  match e with
  | Var x -> x | Num n -> string_of_int n | ArrSize e -> ("arrsize(" ^ string_of_ae e ^ ")")
  | SizeOfE e -> "SizeOfE(" ^ string_of_ae e ^ ")"
  | Mul (e1,e2) -> ("(" ^ string_of_ae e1 ^ " * " ^ string_of_ae e2 ^ ")")
  | Add (e1,e2) -> ("(" ^ string_of_ae e1 ^ " + " ^ string_of_ae e2 ^ ")")
  | Sub (e1,e2) -> ("(" ^ string_of_ae e1 ^ " - " ^ string_of_ae e2 ^ ")")

let rec string_of_formula f =
  match f with
  | True -> "true" | False -> "false" | Not f -> ("not (" ^ string_of_formula f ^")")
  | Eq (e1, e2)  -> string_of_ae e1 ^ " = " ^ string_of_ae e2 
  | Lt (e1, e2)  -> string_of_ae e1 ^ " < " ^ string_of_ae e2
  | Le (e1, e2)  -> string_of_ae e1 ^ " <= " ^ string_of_ae e2
  | And (f1, f2) -> string_of_formula f1 ^ " ^ " ^ string_of_formula f2
  | Or (f1, f2)  -> "(" ^ string_of_formula f1 ^ " v " ^ string_of_formula f2 ^ ")"
