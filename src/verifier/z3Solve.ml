open VeriSem
open Z3
open Z3.Params

let z3ctx = Z3.mk_context [("model", "true"); ("proof", "true")]
(*
let rec ae2bv : Z3.context -> ae -> Z3.Expr.expr
= fun ctx ae ->             (* 64 bit*)
  match ae with
    | Var s -> Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx s) 64
    | Num n -> Z3.BitVector.mk_numeral ctx (string_of_int n) 64
    | Band (e1, e2) -> Z3.BitVector.mk_and ctx (ae2bv ctx e1) (ae2bv ctx e2)

    | Mul (e1, e2) -> Z3.BitVector.mk_mul ctx (ae2bv ctx e1) (ae2bv ctx e2)
    | Div (e1, e2) -> Z3.BitVector.mk_sdiv ctx (ae2bv ctx e1) (ae2bv ctx e2)      (* signed division *)
    | Add (e1, e2) -> Z3.BitVector.mk_add ctx (ae2bv ctx e1) (ae2bv ctx e2)
    | Sub (e1, e2) -> Z3.BitVector.mk_sub ctx (ae2bv ctx e1) (ae2bv ctx e2)

    | ArrSize e -> Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx ("sizeof("^(Z3.Expr.to_string (ae2bv ctx e))^")")) 64
    | Addr e -> Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx ("addr("^(Z3.Expr.to_string (ae2bv ctx e))^")")) 64
    | SizeOfE (Var s) -> Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx ("sizeof("^s^")")) 64
    | SizeOfE e -> ae2bv ctx e

let rec form2bv : Z3.context -> formula -> Z3.Expr.expr
= fun ctx formula ->
  match formula with
    | True -> Z3.Boolean.mk_true ctx
    | False -> Z3.Boolean.mk_false ctx
    | Not f -> Z3.Boolean.mk_not ctx (form2bv ctx f)
    | Eq (e1, e2) -> Z3.Boolean.mk_eq ctx (ae2bv ctx e1) (ae2bv ctx e2)
    | Lt (e1, e2) -> Z3.Arithmetic.mk_lt ctx (ae2bv ctx e1) (ae2bv ctx e2)
    | Le (e1, e2) -> Z3.Arithmetic.mk_le ctx (ae2bv ctx e1) (ae2bv ctx e2)
    | And (f1, f2) -> Z3.Boolean.mk_and ctx [(form2bv ctx f1); (form2bv ctx f2)]
    | Or (f1, f2) -> Z3.Boolean.mk_or ctx [(form2bv ctx f1); (form2bv ctx f2)]
    | Undef -> Z3.Boolean.mk_true ctx
*)

let rec ae2vc : Z3.context -> ae -> Z3.Expr.expr
= fun ctx ae ->
  let is = Z3.Arithmetic.Integer.mk_sort ctx in
  match ae with
    | Ptr e -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx (string_of_ae ae)) is
    | Var s -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx s) is
    | Num n -> Z3.Expr.mk_numeral_int ctx n is
    | Neg e -> Z3.Arithmetic.mk_unary_minus ctx (ae2vc ctx e)
    | Mul (e1, e2) -> Z3.Arithmetic.mk_mul ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | Div (e1, e2) -> Z3.Arithmetic.mk_div ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | Add (e1, e2) -> Z3.Arithmetic.mk_add ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | Sub (e1, e2) -> Z3.Arithmetic.mk_sub ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | Lt (e1, e2) -> Z3.Arithmetic.mk_lt ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | Le (e1, e2) -> Z3.Arithmetic.mk_le ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | Eq (e1, e2) -> Z3.Arithmetic.mk_lt ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | ArrSize e -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx ("sizeof("^(Z3.Expr.to_string (ae2vc ctx e))^")")) is
    | Addr e -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx ("addr("^(Z3.Expr.to_string (ae2vc ctx e))^")")) is
    | SizeOfE (Var s) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx ("sizeof("^s^")")) is
    | SizeOfE e -> ae2vc ctx e
    | Lnot e -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx ("!("^(Z3.Expr.to_string (ae2vc ctx e))^")")) is
    | Bnot e -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx ("~("^(Z3.Expr.to_string (ae2vc ctx e))^")")) is
    | Mod (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("mod("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Band (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("&("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Bxor (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("^("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Bor (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("|("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Land (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("&&("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Lor (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("||("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Sleft (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      ("<<("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is
    | Sright (e1, e2) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx 
      (">>("^(Z3.Expr.to_string (ae2vc ctx e1))^", "^(Z3.Expr.to_string (ae2vc ctx e2))^")")) is

let rec form2vc : Z3.context ->  formula -> Z3.Expr.expr
= fun ctx formula ->
  match formula with
    | True -> Z3.Boolean.mk_true ctx
    | False -> Z3.Boolean.mk_false ctx
    | Not f -> Z3.Boolean.mk_not ctx (form2vc ctx f)
    | Eq (e1, e2) -> Z3.Boolean.mk_eq ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | Lt (e1, e2) -> Z3.Arithmetic.mk_lt ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | Le (e1, e2) -> Z3.Arithmetic.mk_le ctx (ae2vc ctx e1) (ae2vc ctx e2)
    | And (f1, f2) -> Z3.Boolean.mk_and ctx [(form2vc ctx f1); (form2vc ctx f2)]
    | Or (f1, f2) -> Z3.Boolean.mk_or ctx [(form2vc ctx f1); (form2vc ctx f2)]
    | Undef -> Z3.Boolean.mk_true ctx

let print_z3_expr : Z3.Expr.expr list -> unit
= fun expr ->
  let exprs = List.map (Z3.Expr.to_string) expr in
  List.iter prerr_endline exprs

let make_form : string -> ae -> string -> Z3.context -> Z3.Expr.expr
= fun s e rval ctx ->
  match e with
  | Mul (_, e2) -> 
    let form = Eq (Var s, Mul (Var rval, e2)) in (* i = i0 * k *)
    form2vc ctx form
  | Add (_, e2) ->
    let form = Eq (Var s, Add (Var rval, e2)) in (* i = i0 + k *)
    form2vc ctx form
  | Sub (_, e2) ->
    let form = Eq (Var s, Sub (Var rval, e2)) in (* i = i0 - k *)
    form2vc ctx form
  | Div (_, e2) ->
    let form = Eq (Var s, Div (Var rval, e2)) in (* i = i0 / k *)
    form2vc ctx form
  | _ -> raise SolverConversionFailure

let rec bv_check : formula -> bool
= fun formula ->
  match formula with
  | Not f -> bv_check f
  | Eq (Band _, _)
  | Eq (_, Band _) -> true
  | _ -> false
(*
(* strongest postcondition *)
let do_sp_cfg : Z3.Expr.expr list * Z3.Expr.expr list -> formula -> Z3.context -> Z3.Expr.expr list
= fun (pre_cond, b_cond) expr ctx -> 
  let result = 
  begin
    match expr with
    | Eq (Var s1, e1) -> 
    begin
      let rval = s1 ^ "---" ^ (string_of_int !expr_index) in
      let sym_rval = ae2vc ctx (Var rval) in
      let sym_s1 = ae2vc ctx (Var s1) in
      let pre_cond = List.map (fun exp -> Z3.Expr.substitute_one exp sym_s1 sym_rval) pre_cond in
      match e1 with
      | Mul (Var s2, e2) | Add (Var s2, e2) | Sub (Var s2, e2) | Div (Var s2, e2) ->
      begin
        if (s1 = s2) then 
          let new_expr = make_form s1 e1 rval ctx in
          expr_index := !expr_index + 1;
          new_expr::pre_cond
        else
          (form2vc ctx expr)::pre_cond
      end
      | _ -> if bv_check expr then (form2bv ctx expr)::b_cond
          else (form2vc ctx expr)::pre_cond
    end
    | _ -> if bv_check expr then (form2bv ctx expr)::b_cond
          else (form2vc ctx expr)::pre_cond
  end in
  result
*)

let do_sp : Z3.Expr.expr list -> formula -> Z3.context -> Z3.Expr.expr list
= fun pre_cond expr ctx -> 
  let result = 
    begin
      match expr with
      | Eq (Var s1, e1) -> 
      begin
        let rval = s1 ^ "---" ^ (string_of_int !expr_index) in
        let sym_rval = ae2vc ctx (Var rval) in
        let sym_s1 = ae2vc ctx (Var s1) in
        let pre_cond = List.map (fun exp -> Z3.Expr.substitute_one exp sym_s1 sym_rval) pre_cond in
        match e1 with
        | Mul (Var s2, e2) | Add (Var s2, e2) | Sub (Var s2, e2) | Div (Var s2, e2) ->
        begin
          if (s1 = s2) then 
            let new_expr = make_form s1 e1 rval ctx in
            expr_index := !expr_index + 1;
            new_expr::pre_cond
          else
            (form2vc ctx expr)::pre_cond
        end
        | _ -> (form2vc ctx expr)::pre_cond
      end
      | _ -> (form2vc ctx expr)::pre_cond
    end in
  result

(*
let rec get_sp_cfg : Z3.Expr.expr list * Z3.Expr.expr list -> formula list -> Z3.context -> Z3.Expr.expr list * Z3.Expr.expr list
= fun (pre_cond, b_cond) formulae ctx ->
  match formulae with
  | [] -> (pre_cond, b_cond)
  | hd::tl -> 
  begin
      let cond = do_sp (pre_cond, b_cond) hd ctx in
      (*let goal = Z3.Goal.mk_goal ctx true false false in
      let test = do_sp pre_cond hd ctx in
      let _ = Z3.Goal.add goal test in
      let cond = Z3.Goal.simplify goal None in	(* simplify the exprs *)
      let cond = Z3.Goal.get_formulas goal in*)
  (*    let cond_test = Z3.Expr.simplify (List.hd cond) None in
      let args = Z3.Expr.simplify (List.hd cond) None in
      let _ = prerr_endline "expr test" in
      let args = Z3.Expr.get_args args in
      let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) (List.rev args) in
      let ttt = Z3.Expr.substitute cond_test (List.rev args) args in
      let _ = prerr_endline (Z3.Expr.to_string ttt) in 
      let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) cond in *)
  (*    pre_cond*)
      get_sp (cond, b_cond) tl ctx
  end
*)

let rec get_sp : Z3.Expr.expr list -> formula list -> Z3.context -> Z3.Expr.expr list
= fun pre_cond formulae ctx ->
  match formulae with
  | [] -> pre_cond
  | hd::tl -> 
  begin
      let cond = do_sp pre_cond hd ctx in
      (*let goal = Z3.Goal.mk_goal ctx true false false in
      let test = do_sp pre_cond hd ctx in
      let _ = Z3.Goal.add goal test in
      let cond = Z3.Goal.simplify goal None in  (* simplify the exprs *)
      let cond = Z3.Goal.get_formulas goal in*)
  (*    let cond_test = Z3.Expr.simplify (List.hd cond) None in
      let args = Z3.Expr.simplify (List.hd cond) None in
      let _ = prerr_endline "expr test" in
      let args = Z3.Expr.get_args args in
      let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) (List.rev args) in
      let ttt = Z3.Expr.substitute cond_test (List.rev args) args in
      let _ = prerr_endline (Z3.Expr.to_string ttt) in 
      let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) cond in *)
  (*    pre_cond*)
      get_sp cond tl ctx
  end

let solve_check : Z3.context -> formula list -> Z3.Expr.expr list
= fun ctx formulae ->
  let cond = List.map (fun f -> form2vc ctx f) formulae in 
  cond

let rec neg_check : Z3.Expr.expr BatSet.t -> Z3.Expr.expr BatSet.t -> Z3.Expr.expr BatSet.t
= fun workset exprs ->
  if BatSet.is_empty workset then exprs
  else
  begin
    let (w, workset) = BatSet.pop workset in
    let check = Z3.Boolean.mk_not z3ctx w in
    let result = 
      if BatSet.mem check exprs then BatSet.remove check exprs 
      else exprs in
    neg_check workset result
  end
(*
let solve_path : Z3.Expr.expr -> Z3.context -> (formula * InterCfg.Node.t) list -> Z3.Goal.goal -> Z3.Solver.solver -> Z3.Model.model option
= fun query ctx form_node goal solver ->
  expr_index := 0;
  let form_list = List.map (fun f -> let (form, node) = f in form) form_node in
  let (exprs, b_exprs) = get_sp_cfg ([], []) form_list ctx in
  let result = 
    ( let b_goal = Z3.Goal.mk_goal z3ctx true false false in
      let b_solver = Z3.Solver.mk_solver z3ctx None in
      let _ = Z3.Goal.add b_goal b_exprs in
      let _ = Z3.Solver.add solver (Z3.Goal.get_formulas b_goal) in
      let _ = ignore (Z3.Solver.check b_solver []) in
      try Z3.Solver.get_model b_solver with _ -> prerr_endline "BitVector None"; None) in
  match result with
  | None -> None
  | _ -> 
      let _ = Z3.Goal.add goal exprs in
      let _ = print_string "\n*************** Basic Paths *******************" in
      let _ = List.iter (fun f -> print_string (Z3.Expr.to_string f)) exprs in
      let _ = Z3.Goal.add goal [query] in
      let _ = print_string "\n******************* What to solve (with query) ******************" in 
      let _ = print_string (Z3.Goal.to_string goal) in
      let _ = Z3.Solver.add solver (Z3.Goal.get_formulas goal) in
      let _ = ignore (Z3.Solver.check solver []) in
      try Z3.Solver.get_model solver with _ -> print_string "None"; None
*)


let solve_path : Z3.Expr.expr -> Z3.context -> (formula * InterCfg.Node.t) list -> Z3.Goal.goal -> Z3.Solver.solver -> Z3.Model.model option
= fun query ctx form_node goal solver ->
  expr_index := 0;
  let form_list = List.map (fun f -> let (form, node) = f in form) form_node in
  let exprs = get_sp [] form_list ctx in
  let _ = Z3.Goal.add goal exprs in
  let _ = print_string "\n*************** Basic Paths *******************\n" in
  let _ = List.iter (fun f -> print_string ((Z3.Expr.to_string f)^"\n")) exprs in
  let _ = Z3.Goal.add goal [query] in
  let _ = print_string "\n******************* What to solve (with query) ******************\n" in 
  let _ = print_string (Z3.Goal.to_string goal) in
  let _ = Z3.Solver.add solver (Z3.Goal.get_formulas goal) in
  let _ = ignore (Z3.Solver.check solver []) in
  try Z3.Solver.get_model solver with _ -> print_string "None"; None

let z3_solver : formula -> (formula * InterCfg.Node.t) list BatSet.t -> formula list -> bool
= fun vc_query formulae invariants ->
  let query = Z3.Boolean.mk_not z3ctx (form2vc z3ctx vc_query) in
  let _ = print_string "\n******************** Query in solvable form ***********************\n" in
  let _ = print_string (Z3.Expr.to_string query) in
  let invariants_solve = solve_check z3ctx invariants in
  let _ = print_string "\n***************** Precondition **********************\n" in
  let _ = List.iter (fun f -> print_string ((Z3.Expr.to_string f)^"\n")) invariants_solve in
  
  if BatSet.is_empty formulae then begin        (* When no basic paths exist *)
    let tmp = (
      let goal = Z3.Goal.mk_goal z3ctx true false false in
      let solver = Z3.Solver.mk_solver z3ctx None in
      let _ = Z3.Goal.add goal invariants_solve in
      let _ = Z3.Goal.add goal [query] in
      let _ = Z3.Solver.add solver (Z3.Goal.get_formulas goal) in
      let _ = BatSet.iter (fun f -> print_string "\n*************** Basic Paths *******************\n"; List.iter (fun t -> let (form, node) = t in print_string ((string_of_formula form)^"\n")) f) formulae in
      let _ = print_string "\n******************* What to solve (with query) ******************\n" in 
      let _ = print_string (Z3.Goal.to_string goal ^ "\n") in
  
      let _ = ignore (Z3.Solver.check solver []) in
      try Z3.Solver.get_model solver with _ -> 
      print_string "None";None
    ) in
    match tmp with
    | None -> false (* false positive *)
    | _ -> true (* potential bug *)
  end
  else begin    
    let check =BatSet.exists (fun f ->
                    let _ = Z3.Goal.reset in
                    let goal = Z3.Goal.mk_goal z3ctx true false false in
                    let solver = Z3.Solver.mk_solver z3ctx None in
                    let _ = Z3.Goal.add goal invariants_solve in         (* Add invariants into solver*)
                    let solved = solve_path query z3ctx f goal solver in
                    solved <> None) formulae in
    if check then check
    else 
  let _ = BatSet.iter (fun f -> print_string "\n*************** Basic Paths *******************\n"; List.iter (fun t -> let (form, node) = t in print_string (string_of_formula form)) f) formulae in
    check (*
    let check =BatSet.filter (fun f ->
                    let _ = Z3.Goal.reset in
                    let goal = Z3.Goal.mk_goal z3ctx true false false in
                    let solver = Z3.Solver.mk_solver z3ctx None in
                    let _ = Z3.Goal.add goal invariants_solve in         (* Add invariants into solver*)
                    let solved = solve_path query z3ctx f goal solver in
                    solved <> None) formulae in
    BatSet.is_empty check*)
  end

  (*
  let exprs = BatSet.fold (fun f expr -> (get_sp [] f z3ctx)@expr) formulae [] in
  let exprs = BatSet.of_list exprs in
  let exprs = BatSet.to_list (neg_check exprs exprs) in
  (*let _ = prerr_endline "\n*************** Conjunction of Basic Paths *******************" in
  let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) exprs in*)
  let _ = Z3.Goal.add goal exprs in
  let goal = Z3.Goal.simplify goal None in	(* Not necessary *)
  let _ = Z3.Goal.add goal [query] in
  (*let _ = prerr_endline "\n******************* What to solve (with query) ******************" in 
  let _ = prerr_endline (Z3.Goal.to_string goal) in*)
(*  let _ = prerr_endline "ORI EXPR" in
  let _ = prerr_endline "MODIFIED" in
  let _ = prerr_endline (Z3.Goal.to_string goal) in*)
  let _ = Z3.Solver.add solver (Z3.Goal.get_formulas goal) in
  let _ = ignore (Z3.Solver.check solver []) in
  try Z3.Solver.get_model solver with _ -> None*)

let solve_vc : DUGraph.t -> formula -> (formula * InterCfg.Node.t) list BatSet.t -> formula list -> bool
= fun dug vc_query formulae invariants -> 
  let _ = prerr_endline "\n******************** Query ***********************" in
  let _ = prerr_endline (string_of_formula vc_query) in
  let _ = print_string "\n******************** Query ***********************\n" in
  let _ = print_string (string_of_formula vc_query) in
  let result = z3_solver vc_query formulae invariants in
  (*let _ = prerr_endline "\n********************* RESULT **********************" in*)
  result
  (*
  | None -> false (* Solver fails/ UNSATISFIABLE - false alarm *)
  | _ -> true (* SATISFIABLE - potential buffer overflow*)
*)
