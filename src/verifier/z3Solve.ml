open VeriSem
open Z3
open Z3.Params

let expr_index = ref 0
let z3ctx = Z3.mk_context [("model", "true"); ("proof", "true")]

let rec ae2vc : Z3.context -> ae -> Z3.Expr.expr
= fun ctx ae ->
  let is = Z3.Arithmetic.Integer.mk_sort ctx in
  match ae with
    | Var s -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx s) is
    | Num n -> Z3.Expr.mk_numeral_int ctx n is
    | Mul (e1, e2) -> Z3.Arithmetic.mk_mul ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | Add (e1, e2) -> Z3.Arithmetic.mk_add ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | Sub (e1, e2) -> Z3.Arithmetic.mk_sub ctx [(ae2vc ctx e1); (ae2vc ctx e2)]
    | ArrSize (Var s) -> Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx s) is
    | ArrSize _ -> Z3.Boolean.mk_true ctx
    | SizeOfE _ -> Z3.Boolean.mk_true ctx

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
  | _ -> form2vc ctx True

(* strongest postcondition *)
let do_sp : Z3.Expr.expr list -> formula -> Z3.context -> Z3.Expr.expr list
= fun pre_cond expr ctx -> 
  let result = 
  begin
    match expr with
    | Eq (Var s1, e1) -> 
    begin
      let rval = s1 ^ "___" ^ (string_of_int !expr_index) in
      let sym_rval = ae2vc ctx (Var rval) in
      let sym_s1 = ae2vc ctx (Var s1) in
      let pre_cond = List.map (fun exp -> Z3.Expr.substitute_one exp sym_s1 sym_rval) pre_cond in
      match e1 with
      | Mul (Var s2, e2) | Add (Var s2, e2) | Sub (Var s2, e2) ->
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

let rec get_sp : Z3.Expr.expr list -> formula list -> Z3.context -> Z3.Expr.expr list
= fun pre_cond formulae ctx ->
  match formulae with
  | [] -> pre_cond
  | hd::tl -> 
  begin
    let goal = Z3.Goal.mk_goal ctx true false false in
    let test = do_sp pre_cond hd ctx in
    let _ = Z3.Goal.add goal test in
    let cond = Z3.Goal.simplify goal None in	(* simplify the exprs *)
    let cond = Z3.Goal.get_formulas goal in
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

let solve_paths : Z3.context -> formula list -> Z3.Expr.expr list
= fun ctx formulae ->
  let pre_cond = form2vc ctx True in (* true precondition *)
  let _ = prerr_endline "\n************** Basic Path *****************" in
  let _ = List.iter (fun f -> prerr_endline (string_of_formula f)) formulae in
  let _ = prerr_endline "\n************** Start Strongest Postcondition *************" in
  let sp = get_sp [pre_cond] formulae ctx in
  let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) sp in
  sp

let z3_solver : formula -> (formula list) BatSet.t -> Z3.Model.model option
= fun vc_query formulae ->
(*  let exprs = List.map (form2vc z3ctx) (formulae@[vc_query]) in*)
  let query = form2vc z3ctx vc_query in
  let goal = Z3.Goal.mk_goal z3ctx true false false in
  let solver = Z3.Solver.mk_solver z3ctx None in
  let exprs = BatSet.fold (fun f expr -> (solve_paths z3ctx f)@expr) formulae [] in
  let _ = prerr_endline "\n*************** Conjunction of Basic Paths *******************" in
  let _ = List.iter (fun f -> prerr_endline (Z3.Expr.to_string f)) exprs in
  let _ = Z3.Goal.add goal exprs in
  let goal = Z3.Goal.simplify goal None in	(* Not necessary *)
  let _ = Z3.Goal.add goal [query] in
  let _ = prerr_endline "\n******************* What to solve (with query) ******************" in 
  let _ = prerr_endline (Z3.Goal.to_string goal) in
(*  let _ = prerr_endline "ORI EXPR" in
  let _ = prerr_endline "MODIFIED" in
  let _ = prerr_endline (Z3.Goal.to_string goal) in*)
  let _ = Z3.Solver.add solver (Z3.Goal.get_formulas goal) in
  let _ = ignore (Z3.Solver.check solver []) in
  try Z3.Solver.get_model solver with _ -> None

let solve_vc : DUGraph.t -> formula -> (formula list) BatSet.t -> bool
= fun dug vc_query formulae -> 
  let result = z3_solver vc_query formulae in
  let _ = prerr_endline "\n********************* RESULT **********************" in
  match result with
  | None -> false (* Solver fails/ UNSATISFIABLE *)
  | _ -> true (* SATISFIABLE *)

