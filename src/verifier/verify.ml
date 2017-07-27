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
open VeriSem

exception ConversionFailure

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

let rec convert_exp : exp -> ae
= fun exp ->
  match exp with
  | Const (CInt64 (i64,_,_)) -> Num (Cil.i64_to_int i64)
  | Lval (Var vi, NoOffset)  -> Var vi.vname
  | Lval (Mem (Lval (Var vi, NoOffset)), Field (fi, NoOffset)) -> Var (vi.vname ^ "->" ^ fi.fname)
  | Lval (Mem (Lval (Var vi, NoOffset)), NoOffset) -> Var (vi.vname ^ "->this") (* FIXME *)
  | BinOp (PlusA, e1, e2, _) -> Add (convert_exp e1, convert_exp e2)
  | CastE (_,e) -> convert_exp e
  | SizeOfE e -> SizeOfE (convert_exp e)
  | _ -> raise ConversionFailure

let rec convert_lv : lval -> ae
= fun lv -> convert_exp (Lval lv)

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

(* genset for assignment *)
let gen_set : Global.t -> Cil.lval * Cil.exp -> DFATable.facts
= fun global (lv,exp) -> 
  try (*prerr_endline (string_of_formula (Eq (convert_lv lv, convert_exp exp)));*) BatSet.singleton (Eq (convert_lv lv, convert_exp exp))
  with ConversionFailure -> BatSet.empty

(* genset for external call *)
let gen_ext : Global.t -> Cil.lval -> DFATable.facts
= fun global lv -> (*prerr_endline ("EXTERNAL CALL ");*) BatSet.empty

(* genset for alloc *)
let gen_alloc : Global.t -> Cil.lval * IntraCfg.Cmd.alloc -> DFATable.facts
= fun global (lv,alloc) ->
  match lv, alloc with
  | (Cil.Var vi, NoOffset), Array e -> (* prerr_endline (string_of_formula (Eq (ArrSize (Var vi.vname), convert_exp e)));*) BatSet.singleton (Eq (ArrSize (Var vi.vname), convert_exp e))
  | _ -> (* prerr_endline ("ALLOC ETC ");*) BatSet.empty

(* genset for assume *)
let gen_assume : Global.t -> Cil.exp -> DFATable.facts
= fun global exp -> 
  let rec helper exp = 
    match exp with
    | UnOp (Cil.LNot, exp, _) -> (* prerr_endline ("UnOp");*) BatSet.map (fun fact -> Not fact) (helper exp)
    | BinOp (Cil.Lt, e1, e2, _) -> (* prerr_endline (string_of_formula (Lt (convert_exp e1, convert_exp e2)));*) BatSet.singleton (Lt (convert_exp  e1, convert_exp e2))
    | _ -> (* prerr_endline ("ASSUME ETC ");*) BatSet.empty in
    helper exp 

(* genset for call *)
let gen_call : Global.t -> (Cil.lval option * Cil.exp * Cil.exp list) -> DFATable.facts
= fun global (lvo, func, el) ->
  match lvo, func, el with
    (* handling phi-function *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (Lval (Var a1, NoOffset))::(Lval (Var a2, NoOffset))::tl when f.vname = "phi" -> 
    (*prerr_endline ("Call phi " ^ (string_of_formula (Or (Eq (Var vi.vname, Var a1.vname), Eq (Var vi.vname, Var a2.vname))))); *)
    BatSet.singleton (Or (Eq (Var vi.vname, Var a1.vname), Eq (Var vi.vname, Var a2.vname)))
  | _ -> BatSet.empty

let gen_node : Global.t -> InterCfg.Node.t -> DFATable.facts
= fun global node -> 
  match InterCfg.cmdof global.icfg node with
  | Cset (lv, exp, _) -> gen_set global (lv,exp) 
  | Cexternal (lv, _) -> gen_ext global lv
  | Calloc (lv,alloc,_,_) -> gen_alloc global (lv,alloc)
  | Cassume (exp,_) -> gen_assume global exp
  | Cskip -> (*prerr_endline "SKIP";*) BatSet.empty
  | Ccall (lv, f, el, _) -> gen_call global (lv, f, el)
  | _ -> (*prerr_endline "ETC";*) BatSet.empty

let dfa_gen : Global.t -> InterCfg.Node.t -> DFATable.facts
= fun global node -> gen_node global node

(* TODO: call SMT solver *)
let no_contradiction : DFATable.facts -> bool
= fun facts -> 
  BatSet.for_all (fun fact -> BatSet.for_all (fun fact' -> fact <> Not fact') facts) facts

let dfa_kill : Global.t -> InterCfg.Node.t -> DFATable.facts -> DFATable.facts
= fun global node input_facts -> 
  let gen = gen_node global node in
  let facts = BatSet.filter (fun fact -> no_contradiction (BatSet.add fact gen)) input_facts in
  let facts = BatSet.filter (fun fact -> no_contradiction (BatSet.singleton fact)) facts in
    facts

let get_input : InterCfg.Node.t -> DUGraph.t -> DFATable.t -> DFATable.facts
= fun node dug table ->
  list_fold (fun p -> BatSet.union (DFATable.find p table)) 
    (DUGraph.pred node dug) BatSet.empty
 
let perform_dfa : Global.t -> DUGraph.t -> DFATable.t * DFATable.node BatSet.t
= fun global dug -> 
  let nodes = DUGraph.nodesof dug in
  let table0 = BatSet.fold (fun n -> DFATable.add n BatSet.empty) nodes DFATable.empty in
  let workset = DUGraph.nodesof dug in
  let dfa_transfer node input = dfa_kill global node (BatSet.union input (dfa_gen global node)) in
  let node_set = BatSet.empty in
  let rec iterate workset table node_set = 
    if BatSet.is_empty workset then (table, node_set)
    else 
      let node = BatSet.choose workset in
      (*let _ = prerr_endline ("dfa: "^InterCfg.Node.to_string node) in *)
      let workset = BatSet.remove node workset in
      let input = get_input node dug table in
      let new_output = dfa_transfer node input in
     (*let _ = prerr_endline (DFATable.string_of_facts input) in *)
      (*let _ = prerr_endline (DFATable.string_of_facts new_output) in *)
      let old_output = DFATable.find node table in
        if BatSet.subset new_output old_output then iterate workset table node_set
        else
	  begin 
	    let node_set = BatSet.add node node_set in
	    iterate (BatSet.union (list2set (DUGraph.succ node dug)) workset) 
                     (DFATable.add_union node new_output table) node_set 
	  end in
    iterate workset table0 node_set

let get_pred : DUGraph.t -> Worklist.t -> Report.query -> DUGraph.t
= fun dug worklist query ->
  let pred_nodes =
    let add_pred nodes =
      BatSet.fold (fun node nodes->
	if (Worklist.is_loopheader node worklist) && (query.node <> node) then BatSet.add node nodes
	else 
	begin 
	  let preds = DUGraph.pred node dug in
(*	  let _ = List.iter (fun f -> prerr_endline (BasicDom.Node.to_string f)) preds in*)
	  List.fold_left (fun b l -> BatSet.add l b) nodes preds
	end
	  ) nodes nodes in
	fix add_pred (BatSet.singleton query.node) in
      DUGraph.project dug pred_nodes
(*
(* ex) (< (+ pos 1) nstr) -> (= pos (+ pos 1)) & (< pos nstr)*)
let query_node : string -> formula -> DFATable.facts -> string * formula * DFATable.facts
= fun tmp_s f facts ->
  match f with
  | Lt (e1, e2) -> 
    begin
      match e1 with
      | Mul (Var s, ae2) | Add (Var s, ae2) | Sub (Var s, ae2) -> 
	begin
	  let query = Lt (Var s, e2) in
	  let facts = BatSet.add (Eq (Var s, e1)) facts in
	  (s, query, facts)
	end
      | _ -> (tmp_s, f, facts)
    end
  | _ -> (tmp_s, f, facts)
*)

let rec start_nodes : InterCfg.node BatSet.t -> DUGraph.t -> InterCfg.node BatSet.t
= fun nodes dug ->
  let nodes = BatSet.filter (fun f -> List.length (DUGraph.pred f dug) = 0) nodes in
  nodes
(*
let rec make_bp : Report.query -> DFATable.node BatSet.t -> formula list list -> formula list list
= fun query nodes form_list->
  let node = BatSet.choose nodes in
  let nodes = 
  if (DUGraph.succ node = []) then let nodes = BatSet.remove node nodes 
  else let nodes = nodes in
  *)

let rec make_bp : InterCfg.node -> Report.query -> Global.t -> DUGraph.t -> InterCfg.node BatSet.t -> formula list -> formula list
= fun node query global dug workset formulae ->
  let nodes = workset in
  let workset = BatSet.remove node workset in
  let succ = DUGraph.succ node dug in
  let forms = dfa_gen global node in
  let facts = formulae@[(BatSet.choose forms)] in
(*  let facts = 
  (
    match List.length succ with
    | 0 -> facts
    | 1 -> BatSet.union facts (dfa_gen global (List.hd succ))
    | _ -> BatSet.union facts (dfa_gen global (List.hd succ))
  ) in
(*  let _ = prerr_endline "facts string" in
  let _ = BatSet.iter (fun f -> prerr_endline (string_of_formula f)) facts in*)
  (*let vc = BatSet.fold (fun fact f -> fact::f) facts formulae in*)
  if (List.hd succ) <> query.node then make_bp (List.hd succ) query global dug workset facts
  else facts
*)
  if (List.hd succ) <> query.node then make_bp (List.hd succ) query global dug workset facts
  else facts

let generate_vc : Report.query -> Global.t -> ItvAnalysis.Table.t * ItvAnalysis.Table.t -> DUGraph.t -> (formula list) BatSet.t(*string * formula * formula list *)
= fun query global (inputof, outputof) dug -> 
  let vc_query = query2vc query inputof in
  let (table, nodes) = perform_dfa global dug in (* nodes = set of convertable nodes *)
  let nodes_dug = DUGraph.project dug nodes in
  let starts = start_nodes nodes nodes_dug in
  BatSet.iter (fun f -> prerr_endline (InterCfg.Node.to_string f)) starts;
(*  let nodes = BatSet.remove query.node in *)
(*  let _ = prerr_endline "NODES" in
  let _ = BatSet.iter (fun f -> prerr_endline ("dfa: "^InterCfg.Node.to_string f)) nodes in *)
  let vc = [] in
  let basic_paths = BatSet.empty in
  let basic_paths = BatSet.fold (fun f a -> BatSet.add (make_bp f query global nodes_dug nodes vc) a) starts basic_paths in
(*  let tt = BatSet.choose basic_paths in
  let _ = prerr_endline "tests" in
  let _ = BatSet.iter (fun f -> prerr_endline (string_of_formula f)) tt in
  let basic_paths = BatSet.remove tt basic_paths in
  let ss = BatSet.choose basic_paths in
  let _ = prerr_endline "test" in
  let _ = BatSet.iter (fun f -> prerr_endline (string_of_formula f)) ss in*)
(*  let vc = BatSet.fold (fun f a -> BatSet.add (make_bp f query global nodes_dug nodes formulae) vc) starts vc in *)
(*  let sss = BatSet.to_list basic_paths in
  let _ = prerr_endline "tjflasfjweof" in
  let _ = List.iter (fun f -> 
			List.iter (fun g -> prerr_endline (string_of_formula g)) f) sss in*)
  basic_paths

(*
  let facts = get_input query.node dug table in
  let vc = BatSet.fold (fun fact formula -> And (formula, fact)) facts vc_query in
  prerr_endline (string_of_formula vc);
  vc
*)
(*  let s = "" in
  let (s, vc_query, facts) = query_node s vc_query facts in
(*  let forms = gen_sp vc_query facts in *)
  let vc = BatSet.fold (fun fact formulae -> fact::formulae) facts [] in
    (s, vc_query, vc) *)

let verify : Global.t -> ItvAnalysis.Table.t -> ItvAnalysis.Table.t -> Report.query -> bool
= fun global inputof outputof query ->
  let spec = ItvAnalysis.get_spec global in
  let access = AccessAnalysis.perform global spec.Spec.locset (ItvSem.run Strong spec) spec.Spec.premem in
  let dug = SsaDug.make (global, access, spec.Spec.locset_fs) in
  prerr_endline ("** verifying " ^ Report.string_of_query query);
  let dug_sliced = slice_dug dug query in
(*  let _ = prerr_endline "DUG_SLICED" in
  let _ = prerr_endline (DUGraph.to_dot dug_sliced) in *)
  let worklist = Worklist.init dug_sliced in
  let worklist = Worklist.push_set InterCfg.start_node (DUGraph.nodesof dug_sliced) worklist in
  let dug_bp = get_pred dug_sliced worklist query in
(*  let _ = prerr_endline (DUGraph.to_dot dug_bp) in*)
  let basic_paths = generate_vc query global (inputof, outputof) dug_bp in
  let vc_query = query2vc query inputof in
  let verified = Z3Solve.solve_vc dug_bp vc_query basic_paths in
(*  let test1 = BatSet.choose formula in
  let formula = BatSet.remove test1 formula in
  prerr_endline "test1";
  List.iter (fun f -> prerr_endline (string_of_formula f)) test1;
  prerr_endline "test2";
*)
(*  let (s, vc_query, formulae)  = generate_vc query global (inputof, outputof) dug_bp in*)
  (*let _ = prerr_endline "Formula list" in
  let _ = List.iter (fun f -> prerr_endline (string_of_formula f)) formulae in*)
  (if verified then prerr_endline "TRUE SATISFIED - FALSE ALARM"
  else prerr_endline "FALSE - DUNNO");
  verified

let perform : Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list -> 
              Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list
= fun (global, inputof, outputof, queries) -> 
  let queries_unproven = Report.get queries Report.UnProven in
  let queries_unproven = List.filter (fun q -> not (verify global inputof outputof q)) queries_unproven in
    (global, inputof, outputof, queries_unproven)
