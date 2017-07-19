open VeriSem
open Z3

let z3ctx = Z3.mk_context [("model", "true"); ("proof", "false")]

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

let z3_solver : formula list -> Z3.Model.model option
= fun formulas ->
  let exprs = List.map (form2vc z3ctx) formulas in
  print_z3_expr exprs;
  let goal = Z3.Goal.mk_goal z3ctx true false false in
  let solver = Z3.Solver.mk_solver z3ctx None in
  Z3.Goal.add goal exprs;
  let goal = Z3.Goal.simplify goal None in	(* Not necessary *)
  Z3.Solver.add solver (Z3.Goal.get_formulas goal);
  ignore (Z3.Solver.check solver []);
  try Z3.Solver.get_model solver with _ -> None

let solve_vc : formula list -> bool
= fun formulas -> 
  let result = z3_solver formulas in
  match result with
  | None -> false (* Solver fails/ UNSATISFIABLE *)
  | _ -> true (* SATISFIABLE *)

