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
