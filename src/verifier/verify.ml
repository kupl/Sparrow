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
open Options

let slice_dug : DUGraph.t -> Report.query -> DUGraph.t
= fun dug query ->
  let same_pid node = (InterCfg.Node.get_pid node = InterCfg.Node.get_pid query.node) in
  let reachable = 
    let add_preds nodes =
      BatSet.fold (fun node -> 
        (*prerr_endline (InterCfg.Node.to_string node);*)
        let preds = List.filter same_pid (DUGraph.pred node dug) in
          list_fold BatSet.add preds
      ) nodes nodes in
      fix add_preds (BatSet.singleton query.node) in
    DUGraph.project dug reachable

let rec convert_typ : typ -> exp -> ae
= fun t exp ->
  match t with
  | TComp (ci, _) -> Var (ci.cname)
  | TArray (t1, _, _) -> convert_typ t1 exp
  | _ -> (*prerr_endline "Convert_typ Parsing Error";
    let _ = prerr_endline "EXP" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in*)
    raise ConversionFailure

let rec convert_offset : offset -> ae -> ae
= fun f ae ->
  match f with
  | NoOffset -> ae
  | Field (fi, NoOffset) -> Var (string_of_ae ae ^ "->" ^ fi.fname)
  | Field (fi, off) -> convert_offset off (Var (string_of_ae ae ^ "->" ^ fi.fname))
  | Index (e, NoOffset) -> Add (ae, convert_exp e)
  | Index (e, off) -> (* Need to check  *)
    (*And (Add (Var str, convert_exp e), *)
          convert_offset off (Var (string_of_ae ae ^ "[" ^ string_of_ae (convert_exp e) ^ "]"))
(*
and start_offset : offset -> string -> ae
= fun f str ->
  match f with
  | NoOffset -> Var str
  | Field (fi, NoOffset) -> Var (str ^ "->" ^ fi.fname)
  | Field (fi, off) -> convert_offset off (str ^ "->" ^ fi.fname)
  | Index (e, NoOffset) -> Sub (Var str, convert_exp e)
  | Index (e, off) -> (* Need to check  *)
    (*And (Add (Var str, convert_exp e), *)
          convert_offset off (str ^ "[" ^ string_of_ae (convert_exp e) ^ "]")
*)
and prune_size : ae -> ae
= fun e ->
  match e with
  | SizeOfE (SizeOfE e1) -> prune_size (SizeOfE e1)
  | SizeOfE (ArrSize e1) -> prune_size (ArrSize e1)
  | ArrSize (ArrSize e1) -> prune_size (ArrSize e1)
  | ArrSize (SizeOfE e1) -> prune_size (SizeOfE e1)
  | _ -> e

(* Generalization required *)
and convert_exp : exp -> ae
= fun exp ->
  match exp with
  | Const (CInt64 (i64,_,_)) -> Num (Cil.i64_to_int i64)
  | Const (CStr str) -> Var str
  | Const (CChr cha) -> Var (Char.escaped cha)
  | Lval (Var vi, off) -> convert_offset off (Var vi.vname)
  | Lval (Mem e, off) -> Ptr (convert_offset off (convert_exp e))
  (*| Lval (Var vi, NoOffset)  -> Var (vi.vname)
  | Lval (Var vi, Index (e, _)) -> Add (Var (vi.vname), convert_exp e) (* array expression *)
  | Lval (Var vi, Field (fi, NoOffset)) -> Var (vi.vname ^ "->" ^ fi.fname) (* array expression *)
  | Lval (Var vi, Field (fi, Index (e, _))) -> Add (Var (vi.vname ^ "->" ^ fi.fname), convert_exp e)
  | Lval (Var vi, Field (fi, Field (_, _))) -> 
    let _ = prerr_endline "LVAL-field-field" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in
    raise ConversionFailure
  | Lval (Mem (Lval (Var vi, NoOffset)), Field (fi, NoOffset)) -> Var (vi.vname ^ "->" ^ fi.fname)
  | Lval (Mem (Lval (Var vi, NoOffset)), NoOffset) -> Var ("ptr("^vi.vname^")")
  | Lval (Mem e, Field (fi, NoOffset)) -> Var ((string_of_ae (convert_exp e)) ^ "->" ^ fi.fname)
  | Lval (Mem e, _) -> convert_exp e
  | Lval (Var vi, Index _) -> 
    let _ = prerr_endline "LVAL-index" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in
    raise ConversionFailure
  | Lval (Var vi, Field (fi, _)) -> 
    let _ = prerr_endline "LVAL-field" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in
    raise ConversionFailure*)
  | UnOp (Cil.Neg, e, _) -> Neg (convert_exp e)
  | UnOp (Cil.BNot, e, _) -> Bnot (convert_exp e)
  | UnOp (Cil.LNot, e, _) -> Lnot (convert_exp e)

  | BinOp (PlusPI, e1, e2, _)
  | BinOp (PlusA, e1, e2, _) -> Add (convert_exp e1, convert_exp e2)

  | BinOp (MinusPI, e1, e2, _)
  | BinOp (MinusA, e1, e2, _) -> Sub (convert_exp e1, convert_exp e2)
  | BinOp (MinusPP, e1, e2, _) -> Sub (SizeOfE (convert_exp e1), SizeOfE (convert_exp e2))

  | BinOp (Mult, e1, e2, _) -> Mul (convert_exp e1, convert_exp e2)
  | BinOp (Div, e1, e2, _) -> Div (convert_exp e1, convert_exp e2)
  | BinOp (Mod, e1, e2, _) -> Mod (convert_exp e1, convert_exp e2)

  | BinOp (BAnd, e1, e2, _) -> Band (convert_exp e1, convert_exp e2)    (* Need to modify *)
  | BinOp (BXor, e1, e2, _) -> Bxor (convert_exp e1, convert_exp e2)
  | BinOp (BOr, e1, e2, _) -> Bor (convert_exp e1, convert_exp e2)
  | BinOp (LAnd, e1, e2, _) -> Land (convert_exp e1, convert_exp e2)
  | BinOp (LOr, e1, e2, _) -> Lor (convert_exp e1, convert_exp e2)
  | BinOp (Shiftlt, e1, e2, _) -> Sleft (convert_exp e1, convert_exp e2)
  | BinOp (Shiftrt, e1, e2, _) -> Sright (convert_exp e1, convert_exp e2)
  | BinOp (_, e1, e2, _) -> convert_exp e1
(*
  | BinOp (Eq, e1, e2, _) -> Eq (convert_exp e1, convert_exp e2)
  | BinOp (Lt, e1, e2, _) -> Lt (convert_exp e1, convert_exp e2)
  | BinOp (Le, e1, e2, _) -> Le (convert_exp e1, convert_exp e2)
  | BinOp (Gt, e1, e2, _) -> Lt (convert_exp e2, convert_exp e1)
  | BinOp (Ge, e1, e2, _) -> Le (convert_exp e2, convert_exp e1)
  | BinOp (Ne, e1, e2, _) -> Not (Eq (convert_exp e1, convert_exp e2))
*)
  | CastE (TPtr _, e) -> (convert_exp e)
  | CastE (TArray _, e) -> ArrSize (convert_exp e)
  (*| CastE (TPtr _, Lval (Var vi, Field (fi, NoOffset))) -> ArrSize (Var (vi.vname ^ "->" ^ fi.fname))*)
  (*| CastE (TNamed (t, _), e) -> Value (Var t.tname)*)
  | CastE (_, e) -> convert_exp e
  (*| CastE _ -> 
    let _ = prerr_endline "CastE" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in
    raise ConversionFailure*)
  | StartOf (Var vi, off) -> convert_offset off (ArrSize (Var vi.vname))
  | StartOf (Mem e, off) -> convert_offset off (convert_exp e)
  (*| StartOf (Var vi, off) -> convert_offset off (string_of_ae (ArrSize (Var vi.vname)))
  | StartOf (Mem e, off) -> convert_offset off (string_of_ae (convert_exp e))*)
  (*| StartOf (Var vi, NoOffset)  -> Var (vi.vname)
  | StartOf (Var vi, Field (fi, NoOffset)) -> Var (vi.vname ^ "->" ^ fi.fname)
  | StartOf (Mem e, Field (fi, NoOffset)) -> Var ((string_of_ae (convert_exp e)) ^ "->" ^ fi.fname)
*)
  | SizeOf (TInt _) -> Num 1(*prerr_endline "sizeof int"; raise ConversionFailure*) (* Array Index *)
  | SizeOf (TPtr _) -> Num 1
  | SizeOf (TNamed _) -> Num 1
  | SizeOf t -> SizeOfE (convert_typ t exp)          (*Structure name*)
  | SizeOfE e -> SizeOfE (convert_exp e)
  | AddrOf (Var vi, _) -> Addr (Var vi.vname)
  | AddrOf (Mem e, _) -> Addr (convert_exp e)
  | _ -> 
    let _ = prerr_endline "Conversion Failure" in
    let _ = prerr_endline (CilHelper.s_exp_paren exp) in
    raise ConversionFailure

let convert_allocsite_to_size allocsite = Var (Allocsite.to_string allocsite ^ ".size")

let make_arrsize : ae * ae -> ae * ae
= fun (e1, e2) ->
  match e1, e2 with
  | ArrSize tmp1, ArrSize tmp2 -> (e1, e2)
  | ArrSize _, _ -> (e1, ArrSize e2)
  | _, ArrSize _ -> (ArrSize e1, e2)
  | _, _ -> (ArrSize e1, ArrSize e2)

let deref2vc_arr : Report.query -> exp * exp -> Mem.t -> formula
= fun query (e1,e2) mem -> 
  let arr = ArrSize (convert_exp e1) in
  let idx = convert_exp e2 in
  let result = Lt (idx, arr) in
  result

let deref2vc_bop : Report.query -> exp * exp -> Mem.t -> formula
= fun query (e1,e2) mem -> 
  let arr = convert_exp e1 in
  let arr = prune_size arr in
  let idx = convert_exp e2 in
  let result = Lt (idx, arr) in
  result
(*
let deref2vc_val : Report.query -> exp -> Mem.t -> formula
= fun query e mem -> 
  let arr = convert_exp e in
  let size = SizeOfE (convert_exp e) in
  let result = Lt (arr, size) in
  result

let deref2vc_field : Report.query -> exp -> exp -> Mem.t -> formula
= fun query vi e mem -> 
  let arr = convert_exp e in
  let size = SizeOfE (Var vi.vname) in
  let result = Lt (arr, size) in
  result
*)

let convert_ae : ae -> ae
= fun ae ->
  match ae with
  | Add (e1, e2) -> Sub (e1, e2)
  | Sub (e1, e2) -> Add (e1, e2)
  | _ -> ae

let deref2vc_mem : exp -> offset -> formula
= fun e off -> 
  let arr = convert_offset off (convert_exp e) in
  let size = SizeOfE (convert_exp e) in
  let size = prune_size size in
  let arr = prune_size arr in
  let result = Lt (arr, size) in
  result

let deref2vc_var : varinfo -> offset -> formula
= fun vi off -> 
  let arr = convert_offset off (Var vi.vname) in
  let size = SizeOfE (Var vi.vname) in
  let size = prune_size size in
  let arr = prune_size arr in
  let result = Lt (arr, size) in
  result

let memory2vc : Report.query -> exp * exp * exp -> Mem.t -> formula
= fun query (e1, e2, e3) mem ->
  let to_mem = convert_exp e1 in
  let from_mem = convert_exp e2 in
  let to_mem = prune_size to_mem in
  let from_mem = prune_size from_mem in
  let (to_mem, from_mem) = (convert_ae to_mem, convert_ae from_mem) in
  let mem_size = Sub (convert_exp e3, Num 1) in
  And (Le (mem_size, to_mem), Le (mem_size, from_mem))

let strn2vc : Report.query -> exp * exp * exp -> Mem.t -> formula
= fun query (e1, e2, e3) mem ->
  let to_mem = convert_exp e1 in
  let from_mem = convert_exp e2 in
  let mem_size = convert_exp e3 in
  let to_mem = prune_size to_mem in
  let from_mem = prune_size from_mem in
  let mem_size = prune_size mem_size in
  let (to_mem, from_mem) = make_arrsize (to_mem, from_mem) in
  And (Le (mem_size, to_mem), Le (mem_size, from_mem))

let str2vc : Report.query -> exp * exp -> Mem.t -> formula
= fun query (e1, e2) mem ->
  let to_mem = convert_exp e1 in
  let from_mem = convert_exp e2 in
  let size = prune_size to_mem in
  let size = prune_size from_mem in
  let (to_mem, from_mem) = make_arrsize (to_mem, from_mem) in
  Le (from_mem, to_mem)

(* Need some modification... length(dest) + arrsize(src) < arrsize(dest) *)
let strc2vc : Report.query -> exp * exp -> Mem.t -> formula
= fun query (e1, e2) mem ->
  let dest = SizeOfE (convert_exp e1) in
  let src = SizeOfE (convert_exp e2) in
  Le (src, dest)
(*
  let to_mem = convert_exp e1 in
  let to_mem = prune_size to_mem in
  let to_mem_size = SizeOfE(to_mem) in
  let source = SizeOfE(convert_exp e2) in
  let to_mem_size = prune_size to_mem in
  let source = prune_size source in
  let source_size = Add (to_mem, source) in
  Le (source_size, to_mem_size)
*)
let rec query2vc : Report.query -> ItvAnalysis.Table.t -> formula
= fun query inputof -> 
  let mem = Table.find query.node inputof in
  (*let _ = prerr_endline "Alarm exp" in
  let _ = prerr_endline (AlarmExp.to_string query.exp) in*)
    match query.exp with
    | ArrayExp (lv, e, _) -> deref2vc_arr query (Lval lv, e) mem
    | DerefExp (BinOp (_,e1,e2,_), _) -> deref2vc_bop query (e1,e2) mem
    | DerefExp (Lval (Var vi, off), _) -> deref2vc_var vi off
    | DerefExp (Lval (Mem m, off), _) -> deref2vc_mem m off
    (*| DerefExp (Lval (Var vi, NoOffset), _) -> deref2vc_val query (Lval (Var vi, NoOffset)) mem
    | DerefExp (Lval (Var vi, Index (e, _)), _) -> deref2vc_mem query vi e mem
    | DerefExp (Lval (Mem m, NoOffset), _) -> deref2vc_val query m mem
    | DerefExp (Lval (Mem m, Field (e, _)), _) -> deref2vc_field m e mem*)
    | Memcpy (e1, e2, e3, loc)
    | Memmove (e1, e2, e3, loc) -> memory2vc query (e1, e2, e3) mem
    | Strncpy (e1, e2, e3, loc) -> strn2vc query (e1, e2, e3) mem
    | Strcpy (e1, e2, loc) -> str2vc query (e1, e2) mem
    | Strcat (e1, e2, loc) -> strc2vc query (e1, e2) mem
    | _ -> False

(* genset for assignment *)
let gen_set : Global.t -> Cil.lval * Cil.exp -> DFATable.facts
= fun global (lv,exp) -> 
  (*let _ = prerr_endline "gen_set" in
  let _ = prerr_endline (CilHelper.s_lv lv  ^ " = " ^ CilHelper.s_exp exp) in*)
  match exp with
  | CastE (TPtr _, e) -> BatSet.singleton (Eq (convert_exp (Lval lv), convert_exp exp))
  | _ -> try (*prerr_endline (string_of_formula (Eq (convert_lv lv, convert_exp exp)));*) BatSet.singleton (Eq (convert_exp (Lval lv), convert_exp exp))
  with ConversionFailure -> (*BatSet.empty*) BatSet.singleton Undef

(* genset for external call *)
let gen_ext : Global.t -> Cil.lval -> DFATable.facts
= fun global lv -> (*prerr_endline ("EXTERNAL CALL "); BatSet.empty*)BatSet.singleton Undef

(* genset for alloc *)
let gen_alloc : Global.t -> Cil.lval * IntraCfg.Cmd.alloc -> DFATable.facts
= fun global (lv,alloc) ->
  (*let _ = prerr_endline "gen_alloc" in*)
  match lv, alloc with
  | (Cil.Var vi, NoOffset), Array e -> (*prerr_endline (string_of_formula (Eq (ArrSize (Var vi.vname), convert_exp e)));*) BatSet.singleton (Eq (ArrSize (Var vi.vname), convert_exp e))
  | _ -> (* prerr_endline ("ALLOC ETC "); BatSet.empty*) BatSet.singleton Undef

(* genset for assume *)
let gen_assume : Global.t -> Cil.exp -> DFATable.facts
= fun global exp -> 
  (*let _ = prerr_endline "EXP" in
  let _ = prerr_endline (CilHelper.s_exp_paren exp) in *)
  let rec helper exp = 
    match exp with
    | UnOp (Cil.LNot, exp, _) -> BatSet.map (fun fact -> Not fact) (helper exp)
    | BinOp (Cil.Lt, e1, e2, _) -> (*prerr_endline (string_of_formula (Lt (convert_exp e1, convert_exp e2)));*) BatSet.singleton (Lt (convert_exp  e1, convert_exp e2))
    | BinOp (Cil.Le, e1, e2, _) -> BatSet.singleton (Le (convert_exp e1, convert_exp e2))
    | BinOp (Cil.Eq, e1, e2, _) -> BatSet.singleton (Eq (convert_exp e1, convert_exp e2))
    | _ -> (* prerr_endline ("ASSUME ETC "); BatSet.empty*) BatSet.singleton Undef in
    helper exp 

(* genset for call *)
let gen_call : Global.t -> (Cil.lval option * Cil.exp * Cil.exp list) -> DFATable.facts
= fun global (lvo, func, el) ->
  (*let _ = prerr_endline "CALL EXP" in
  let _ = prerr_endline (CilHelper.s_exp_paren func) in*)
  match lvo, func, el with
    (* handling phi-function *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (Lval (Var a1, NoOffset))::(Lval (Var a2, NoOffset))::tl when f.vname = "phi" -> 
    BatSet.singleton (Or (Eq (Var vi.vname, Var a1.vname), Eq (Var vi.vname, Var a2.vname)))
    (* handling memcpy *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (Lval (Var a1, NoOffset))::(Lval (Var a2, NoOffset))::tl when f.vname = "memcpy" ->
    let len = Sub (Var a2.vname, Num 1) in
    BatSet.singleton (And (Le (len, Var vi.vname), Le (len, Var a1.vname)))

    (* handling strncpy *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (Lval (Var a1, NoOffset))::(Lval (Var a2, NoOffset))::tl when f.vname = "strncpy" ->
    BatSet.singleton (And (Le (Var a2.vname, Var vi.vname), Le (Var a2.vname, Var a1.vname)))

    (* handling memmov *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (Lval (Var a1, NoOffset))::(Lval (Var a2, NoOffset))::tl when f.vname = "memmov" ->
    BatSet.singleton (And (Le (Var a2.vname, Var vi.vname), Le (Var a2.vname, Var a1.vname)))

    (* handling strlen x = strlen(y) *)
  | Some (Var vi, NoOffset), Lval (Var f, NoOffset), (CastE (_, e))::tl when f.vname = "strlen" ->
    BatSet.singleton (Eq (Var vi.vname, convert_exp e))

  | _ -> (*BatSet.empty*) BatSet.singleton Undef

let gen_sparrow : Global.t -> Cil.exp list -> DFATable.facts
= fun global exps ->
  (*let _ = List.iter (fun exp -> prerr_endline (CilHelper.s_exp_paren exp)) exps in*)
  let exps = List.hd exps in
  match exps with
  | BinOp _ -> gen_assume global exps
  | _ -> (*BatSet.empty*) BatSet.singleton Undef

let gen_node : Global.t -> InterCfg.Node.t -> DFATable.facts
= fun global node ->
  (*prerr_endline "THis NODE...";
  prerr_endline (InterCfg.Node.to_string node);*)
  match InterCfg.cmdof global.icfg node with
  | Cset (lv, exp, _) -> gen_set global (lv,exp) 
  | Cexternal (lv, _) -> gen_ext global lv
  | Calloc (lv,alloc,_,_) -> gen_alloc global (lv,alloc)
  | Cassume (exp,_) -> gen_assume global exp
  | Csmt (f, exp, _) -> gen_sparrow global exp
  | Cskip -> (*prerr_endline "SKIP";*) BatSet.empty
  | Ccall (lv, f, el, _) -> gen_call global (lv, f, el)
  | _ -> (*prerr_endline "ETC"; BatSet.empty*) BatSet.singleton Undef

let gen_form : Global.t -> InterCfg.Node.t -> formula * InterCfg.Node.t
= fun global node ->
  let gen_formula = BatSet.choose (gen_node global node) in
  (gen_formula, node)

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

let get_loop : DUGraph.t -> Worklist.t -> Report.query -> InterCfg.node BatSet.t
= fun dug worklist query ->
  let succ_nodes = 
    let add_succ nodes = 
      BatSet.fold (fun node nodes ->
          let succs = DUGraph.succ node dug in
          List.fold_left (fun b l -> BatSet.add l b) nodes succs
      ) nodes nodes in
      fix add_succ (BatSet.singleton query.node) in
      succ_nodes

(* Get Predecessor node *)
let get_pred : InterCfg.t -> DUGraph.t -> Worklist.t -> Report.query -> DUGraph.t
= fun icfg dug worklist query ->
  if (InterCfg.is_inside_loop query.node icfg) then
    let loop = get_loop dug worklist query in
    DUGraph.project dug loop
  else
  begin    
    let pred_nodes =
      let add_pred nodes =
        BatSet.fold (fun node nodes->
          if (Worklist.is_loopheader node worklist) && (query.node <> node) then 
          (*let _ = prerr_endline "This is loop header node" in
          let _ = prerr_endline (InterCfg.Node.to_string node) in*)
          BatSet.add node nodes
          else 
          begin 
            let preds = DUGraph.pred node dug in
     (*let _ = List.iter (fun f -> prerr_endline (BasicDom.Node.to_string f)) preds in *)
            List.fold_left (fun b l -> BatSet.add l b) nodes preds
          end
        ) nodes nodes in
        fix add_pred (BatSet.singleton query.node) in
        DUGraph.project dug pred_nodes
  end


let rec make_basic_paths : InterCfg.node -> DUGraph.t -> path_info -> BasicPath.t -> InterCfg.node list -> path_info BatSet.t -> path_info BatSet.t
= fun node dug path_list bp_module br_nodes bp_set ->
  let pred_nodes = DUGraph.pred node dug in 
  let check_node::ori_path = path_list in

  if (List.mem check_node ori_path) || (List.length path_list > !Options.smt_depth) then
    let bp_set = BatSet.add ori_path bp_set in
    if br_nodes == [] then bp_set
    else begin
      let last_node::tl = br_nodes in
      let new_path = BasicPath.find_path_info last_node bp_module in
      make_basic_paths last_node dug new_path bp_module br_nodes bp_set
    end
  else
  match List.length pred_nodes with
  | 0 -> 
    let bp_set = BatSet.add path_list bp_set in
    let check_empty = BasicPath.node_info_empty bp_module in
    if check_empty then bp_set
    else begin
      let last_node::tl = br_nodes in      
      let new_path = BasicPath.find_path_info last_node bp_module in
      make_basic_paths last_node dug new_path bp_module br_nodes bp_set
    end
  | 1 -> 
    let try_node = List.hd pred_nodes in
    if List.mem try_node path_list then
      let check_empty = BasicPath.node_info_empty bp_module in
      if check_empty then bp_set
      else begin
        let last_node::tl = br_nodes in
        let bp_set = BatSet.add path_list bp_set in
        let nxt_nodes = BasicPath.find_node_info last_node bp_module in
        let new_path = BasicPath.find_path_info last_node bp_module in
        let (nxt_node, nxt_nodes) = BatSet.pop nxt_nodes in
        let new_path = nxt_node::new_path in

        if BatSet.is_empty nxt_nodes then begin
          let bp_module = BasicPath.del_path_node_info last_node bp_module in   
          make_basic_paths nxt_node dug new_path bp_module tl bp_set
        end else
        begin
          let bp_module = BasicPath.add_node last_node nxt_nodes bp_module in
          make_basic_paths nxt_node dug new_path bp_module br_nodes bp_set 
        end

      end
    else begin
      let path_list = try_node::path_list in
      make_basic_paths try_node dug path_list bp_module br_nodes bp_set
    end

  | _ -> 
    let tmp_bn = BasicPath.get_bn bp_module in
    let try_node::tl = pred_nodes in
    begin
      if BatMap.mem node tmp_bn then begin
        let tmp_bn = BatMap.find node tmp_bn in
        let (nxt_node, nxt_nodes) = BatSet.pop tmp_bn in
        let hd::tl = br_nodes in

        if BatSet.is_empty nxt_nodes then
          let bp_module = BasicPath.del_path_node_info node bp_module in
          let path_list = nxt_node::path_list in
          make_basic_paths nxt_node dug path_list bp_module tl bp_set
        else begin
          let bp_module = BasicPath.add_node node nxt_nodes bp_module in
          let path_list = nxt_node::path_list in
          make_basic_paths nxt_node dug path_list bp_module br_nodes bp_set
        end
      end else 
        let br_nodes = node::br_nodes in
        (*prerr_endline (InterCfg.Node.to_string node);*)
        let bp_module = BasicPath.add_node node (BatSet.of_list tl) bp_module in
        let bp_module = BasicPath.add_path node path_list bp_module in
        let path_list = try_node::path_list in
        (*prerr_endline "TRY NODE";
          prerr_endline (InterCfg.Node.to_string try_node);*)
        make_basic_paths try_node dug path_list bp_module br_nodes bp_set
    end

let query_check : InterCfg.node -> InterCfg.node -> Global.t -> bool
= fun query node global ->
  let node_cmd = InterCfg.cmdof global.icfg node in
  if (query == node) || (node_cmd == Cskip) then false
  else true

let query_prune_cfg : Report.query -> Global.t -> InterCfg.node BatSet.t -> IntraCfg.t -> path_info BatSet.t -> path_info BatSet.t
= fun query global smts icfg bp_set ->
  let bp_set = BatSet.map (fun f -> List.filter (fun l -> query_check query.node l global) f) bp_set in
  let bp_set = BatSet.map (fun f -> 
        List.filter (fun l -> 
              let intra_n = InterCfg.Node.get_cfgnode l in
              let cmd = IntraCfg.find_cmd intra_n icfg in
              match cmd with
              | Csmt _ -> false
              | _ -> true 
            )
        f) bp_set in
  BatSet.filter (fun f -> f <> []) bp_set

let query_prune : Report.query -> Global.t -> path_info BatSet.t -> path_info BatSet.t
= fun query global bp_set ->
  let bp_set = BatSet.map (fun f -> List.filter (fun l -> query_check query.node l global) f) bp_set in
  BatSet.filter (fun f -> f <> []) bp_set

let rec check_undef : formula -> bool
= fun f ->
  match f with
  | Not f2 -> check_undef f2
  | Undef -> false
  | _ -> true
 
let rec make_bp : InterCfg.node -> IntraCfg.t -> Proc.t -> Worklist.t -> path_info -> BasicPath.t -> InterCfg.node list -> path_info BatSet.t -> path_info BatSet.t
= fun node icfg pid worklist path_list bp_module br_nodes bp_set ->
  let intra_node = InterCfg.Node.get_cfgnode node in
  let pred_nodes = IntraCfg.pred intra_node icfg in 
  let pred_nodes = List.map (fun f -> InterCfg.Node.make pid f) pred_nodes in
  let check_node::ori_path = path_list in

  if Worklist.is_loopheader check_node worklist then 
    let bp_set = BatSet.add path_list bp_set in
    if br_nodes == [] then bp_set
    else begin
      let last_node::tl = br_nodes in
      let new_path = BasicPath.find_path_info last_node bp_module in
      make_bp last_node icfg pid worklist new_path bp_module br_nodes bp_set
    end
  else
  match List.length pred_nodes with
  | 0 -> 
    let bp_set = BatSet.add path_list bp_set in
    let check_empty = BasicPath.node_info_empty bp_module in
    if check_empty then bp_set
    else begin
      let last_node::tl = br_nodes in      
      let new_path = BasicPath.find_path_info last_node bp_module in
      make_bp last_node icfg pid worklist new_path bp_module br_nodes bp_set
    end
  | 1 -> 
    let try_node = List.hd pred_nodes in
    if List.mem try_node path_list then
      let check_empty = BasicPath.node_info_empty bp_module in
      if check_empty then bp_set
      else begin
        let last_node::tl = br_nodes in
        let bp_set = BatSet.add path_list bp_set in
        let nxt_nodes = BasicPath.find_node_info last_node bp_module in
        let new_path = BasicPath.find_path_info last_node bp_module in
        let (nxt_node, nxt_nodes) = BatSet.pop nxt_nodes in
        let new_path = nxt_node::new_path in

        if BatSet.is_empty nxt_nodes then begin
          let bp_module = BasicPath.del_path_node_info last_node bp_module in   
          make_bp nxt_node icfg pid worklist new_path bp_module tl bp_set
        end else
        begin
          let bp_module = BasicPath.add_node last_node nxt_nodes bp_module in
          make_bp nxt_node icfg pid worklist new_path bp_module br_nodes bp_set 
        end

      end
    else begin
      let path_list = try_node::path_list in
      make_bp try_node icfg pid worklist path_list bp_module br_nodes bp_set
    end

  | _ -> 
    let tmp_bn = BasicPath.get_bn bp_module in
    let try_node::tl = pred_nodes in
    begin
      if BatMap.mem node tmp_bn then begin
        let tmp_bn = BatMap.find node tmp_bn in
        let (nxt_node, nxt_nodes) = BatSet.pop tmp_bn in
        let hd::tl = br_nodes in

        if BatSet.is_empty nxt_nodes then
          let bp_module = BasicPath.del_path_node_info node bp_module in
          let path_list = nxt_node::path_list in
          make_bp nxt_node icfg pid worklist path_list bp_module tl bp_set
        else begin
          let bp_module = BasicPath.add_node node nxt_nodes bp_module in
          let path_list = nxt_node::path_list in
          make_bp nxt_node icfg pid worklist path_list bp_module br_nodes bp_set
        end
      end else 
        let br_nodes = node::br_nodes in
        (*prerr_endline (InterCfg.Node.to_string node);*)
        let bp_module = BasicPath.add_node node (BatSet.of_list tl) bp_module in
        let bp_module = BasicPath.add_path node path_list bp_module in
        let path_list = try_node::path_list in
        (*prerr_endline "TRY NODE";
          prerr_endline (InterCfg.Node.to_string try_node);*)
        make_bp try_node icfg pid worklist path_list bp_module br_nodes bp_set
    end
(*
let generate_bp : Report.query -> Global.t -> Worklist.t -> InterCfg.node BatSet.t -> (formula * InterCfg.Node.t) list BatSet.t
= fun query global worklist smts ->
  let pid = InterCfg.Node.get_pid query.node in
  let intra_cfg = InterCfg.cfgof global.icfg pid in
  let bp_module = BasicPath.init BatMap.empty BatMap.empty in
  let bp_set = make_bp query.node intra_cfg pid worklist [query.node] bp_module [] BatSet.empty in
  let bp_set = query_prune_cfg query global smts intra_cfg bp_set in
  let basic_path = BatSet.map (fun f -> List.map (fun l ->
        gen_form global l) f
      ) bp_set in
  (*let tmp = BatSet.choose basic_path in
  List.iter (fun f -> let (x, y) = f in prerr_endline ((string_of_formula x)^" "^(InterCfg.Node.to_string y))) tmp;*)
  let basic_path = BatSet.map (fun f -> List.filter (fun l ->
        let (x, y) = l in
        check_undef x) f) basic_path in
  basic_path
*)


let generate_vc : Report.query -> Global.t -> ItvAnalysis.Table.t * ItvAnalysis.Table.t -> DUGraph.t -> (formula * InterCfg.Node.t) list BatSet.t
= fun query global (inputof, outputof) dug -> 
  let (table, nodes) = perform_dfa global dug in (* nodes = set of convertible nodes *)
  let nodes_dug = DUGraph.project dug nodes in
  let bp_module = BasicPath.init BatMap.empty BatMap.empty in
  let bp_set = make_basic_paths query.node nodes_dug [query.node] bp_module [] BatSet.empty in
  let bp_set = query_prune query global bp_set in
  let basic_path = BatSet.map (fun f -> List.map (fun l ->
        gen_form global l) f
      ) bp_set in
  (*let tmp = BatSet.choose basic_path in
  List.iter (fun f -> let (x, y) = f in prerr_endline ((string_of_formula x)^" "^(InterCfg.Node.to_string y))) tmp;*)
  let basic_path = BatSet.map (fun f -> List.filter (fun l ->
        let (x, y) = l in
        check_undef x) f) basic_path in
  basic_path
  (*let result = BatSet.map (fun f -> List.map (fun l ->
        let (form_list, node_set) = l in
        form_list) f) basic_path in
  result*)

let rec find_smt_start : IntraCfg.node -> IntraCfg.t -> IntraCfg.node * bool
= fun node icfg ->
  let cmd = IntraCfg.find_cmd node icfg in
  match cmd with
  | Csmt _ -> (node, true)
  | _ -> 
  begin
    let tmp = IntraCfg.pred node icfg in
    match tmp with
    | [] -> (node, false)
    | hd::tl -> find_smt_start hd icfg
  end

let rec group_smt : IntraCfg.node -> IntraCfg.t -> IntraCfg.node BatSet.t -> IntraCfg.node BatSet.t
= fun node icfg smt_nodes->
  let cmd = IntraCfg.find_cmd node icfg in
  match cmd with
  | Csmt _ ->
    begin
      let pred = IntraCfg.pred node icfg in
      if (List.length pred <> 1) then smt_nodes
      else begin 
        let smt_nodes = BatSet.add node smt_nodes in
        let pred = List.hd (IntraCfg.pred node icfg) in
        group_smt pred icfg smt_nodes    
      end
    end
  | _ -> smt_nodes

let query_smt : Report.query -> Global.t -> DUGraph.node BatSet.t
= fun query global ->
  let cfg_node = InterCfg.Node.get_cfgnode query.node in
  let pid = InterCfg.Node.get_pid query.node in
  let intra_cfg = InterCfg.cfgof global.icfg pid in
  let (q_pred, check) = find_smt_start cfg_node intra_cfg in
  if check then
  begin
    let smt_set = BatSet.add q_pred BatSet.empty in
    let tmp_smt = group_smt q_pred intra_cfg smt_set in
    let result = BatSet.map (fun f -> InterCfg.Node.make pid f) tmp_smt in
    result
  end
  else BatSet.empty

let verify : InterCfg.node BatSet.t -> DUGraph.t -> Global.t -> ItvAnalysis.Table.t -> ItvAnalysis.Table.t -> Report.query -> bool
= fun smts dug global inputof outputof query ->
  prerr_endline ("\n\n** verifying " ^ Report.string_of_query query);
  print_string ("\n\n** verifying " ^ Report.string_of_query query);
  let dug_sliced = slice_dug dug query in
  let worklist = Worklist.init dug_sliced in
  let worklist = Worklist.push_set InterCfg.start_node (DUGraph.nodesof dug_sliced) worklist in
  (*to get path inside loop - loop header info*)  
  let dug_bp = get_pred global.icfg dug_sliced worklist query in      
  (*print_string (DUGraph.to_dot dug_bp);*)
  (*let dug_tmp = DUGraph.dug_merge dug_bp node_b in
  let _ = print_string (DUGraph.to_dot dug_tmp) in
  let _ = print_string (DUGraph.to_dot dug_bp) in*)
  let vc_query = query2vc query inputof in        (* VC for query *)
  (*let basic_paths = generate_bp query global worklist smts in*)
  let basic_paths = generate_vc query global (inputof, outputof) dug_bp in
  let verified = 
    begin
      if (BatSet.is_empty smts) then 
        Z3Solve.solve_vc dug_bp vc_query basic_paths []
      else begin
        let smt_nodes = query_smt query global in
        if BatSet.is_empty smt_nodes then Z3Solve.solve_vc dug_bp vc_query basic_paths []
        else begin
          let smt_formula = BatSet.fold (fun f a -> let t = BatSet.choose (gen_node global f) in
                  BatSet.add t a) smt_nodes BatSet.empty in
          let smt_formula = BatSet.to_list smt_formula in
          Z3Solve.solve_vc dug_bp vc_query basic_paths smt_formula
        end
      end
    end in
  (if verified then prerr_endline "Potential Buffer Overflow"
    else prerr_endline "false alarm");
  verified

let perform : Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list -> 
              Global.t * ItvAnalysis.Table.t * ItvAnalysis.Table.t * Report.query list
= fun (global, inputof, outputof, queries) -> 
  let spec = ItvAnalysis.get_spec global in
  let access = AccessAnalysis.perform global spec.Spec.locset (ItvSem.run Strong spec) spec.Spec.premem in
  let dug = SsaDug.make (global, access, spec.Spec.locset_fs) in
  let node_list = DUGraph.nodesof dug in
  let smt_nodes = BatSet.filter (fun q -> InterCfg.is_smt global.icfg q) node_list in
  (*let _ = print_string (DUGraph.to_dot dug) in*)
  let queries_unproven = Report.get queries Report.UnProven in
  let new_queries = Report.get_unique_query queries_unproven in
  let test = Report.pid_partition queries_unproven in
  let _ = BatMap.iter (fun part q_l -> prerr_endline (part); List.iter (fun q -> prerr_endline (Report.string_of_query q)) q_l) test in
  (*let _ = BatSet.iter (fun t -> prerr_endline "HELO"; List.iter (fun f -> prerr_endline (string_of_query f)) t)new_queries in*)
  (*let _ = List.iter (fun f -> prerr_endline (string_of_query f)) new_queries in*)
  let queries_unproven = List.filter (fun q -> verify smt_nodes dug global inputof outputof q) new_queries in
    (global, inputof, outputof, queries_unproven)