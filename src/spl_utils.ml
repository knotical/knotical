open Spl_syn
open PSpl_syn
open Apron.Texpr1
open Lib.Print

(* Normalization *)
let norm_neg_e (exp: cons): cons =
  let (l, op, r) = exp in
  let norm_op = match op with
    | EQ -> NEQ
    | NEQ -> EQ
    | GT -> LEQ
    | GEQ -> LT
    | LEQ -> GT
    | LT -> GEQ in
  (l, norm_op, r)

let rec norm_neg (bexp: bexpr): bexpr =
  match bexp with
  | TRUE
  | FALSE
  | BRANDOM
  | CONS _ -> bexp
  | AND (l, r) ->
    let norm_l = norm_neg l in
    let norm_r = norm_neg r in
    AND (norm_l, norm_r)
  | OR (l, r) ->
    let norm_l = norm_neg l in
    let norm_r = norm_neg r in
    OR (norm_l, norm_r)
  | NOT e ->
    (match e with
     | TRUE -> FALSE
     | FALSE -> TRUE
     | BRANDOM -> BRANDOM
     | CONS c -> CONS (norm_neg_e c)
     | AND (l, r) ->
       let norm_neg_l = norm_neg (NOT l) in
       let norm_neg_r = norm_neg (NOT r) in
       OR (norm_neg_l, norm_neg_r)
     | OR (l, r) ->
       let norm_neg_l = norm_neg (NOT l) in
       let norm_neg_r = norm_neg (NOT r) in
       AND (norm_neg_l, norm_neg_r)
     | NOT f -> norm_neg f)

(* Printing *)
let get_comment_printer pr_comment =
  if not pr_comment then
    fun _ _ -> ()
  else print_point

let pr_var = pr_to_string print_var

let pr_typ = pr_to_string print_typ

let pr_point = pr_to_string print_point

let pr_iexpr = pr_to_string print_iexpr

let pr_cons = pr_to_string print_cons

let pr_bexpr = pr_to_string print_bexpr

let pr_instr ?(pr_comment=true) =
  let comment_printer = get_comment_printer pr_comment in
  pr_to_string (print_instr comment_printer)

let pr_instruction ?(pr_comment=true) =
  let comment_printer = get_comment_printer pr_comment in
  pr_to_string (print_instruction comment_printer)

let pr_block ?(pr_comment=true) =
  let comment_printer = get_comment_printer pr_comment in
  pr_to_string (print_block comment_printer)

let pr_decl = pr_to_string print_declaration

let pr_decls = pr_to_string print_declarations

let pr_proc ?(pr_comment=true) =
  let comment_printer = get_comment_printer pr_comment in
  pr_to_string (print_procedure comment_printer)

let pr_prog ?(pr_comment=true) =
  let comment_printer = get_comment_printer pr_comment in
  pr_to_string (print_program comment_printer)

(* Comparison *)
let eq_var v1 v2 =
  (Apron.Var.compare v1 v2) == 0

let eq_typ = function
  | INT, INT
  | REAL, REAL -> true
  | _ -> false

let eq_point pt1 pt2 =
  (pt1.line == pt2.line) &&
  (pt1.col == pt2.col)

let compare_point pt1 pt2 =
  (* let cmp_line = compare pt1.line pt2.line in
   * if cmp_line == 0 then compare pt1.col pt2.col
   * else cmp_line *)
  let r = compare pt1.line pt2.line in
  (* let () = Debug.hprint "pt1: " pr_point pt1 in
   * let () = Debug.hprint "pt2: " pr_point pt2 in
   * let () = Debug.hprint "cmp: " pr_int r in *)
  r

let eq_unop op1 op2 =
  match op1, op2 with
  | Neg, Neg
  | Cast, Cast
  | Sqrt, Sqrt -> true
  | _ -> false

let eq_binop op1 op2 =
  op1 = op2
  (* match op1, op2 with
   * | Add, Add
   * | Sub, Sub
   * | Mul, Mul
   * | Div, Div
   * | Mod, Mod -> true
   * | _ -> false *)

let eq_constyp t1 t2 =
  t1 = t2
  (* match t1, t2 with
   * | EQ, EQ
   * | NEQ, NEQ
   * | GT, GT
   * | GEQ, GEQ
   * | LEQ, LEQ
   * | LT, LT -> true
   * | _ -> false *)

let eq_typ t1 t2 =
  t1 = t2
  (* match t1, t2 with
   * | Real, Real
   * | Int, Int
   * | Single, Single
   * | Double, Double
   * | Extended, Extended
   * | Quad, Quad -> true
   * | _ -> false *)

let eq_commutative eq (l1, r1) (l2, r2) =
  ((eq l1 l2) && (eq r1 r2)) ||
  ((eq l1 r2) && (eq r1 l2))

let rec eq_iexpr expr1 expr2 =
  match expr1, expr2 with
  | Cst c1, Cst c2 -> Apron.Coeff.equal c1 c2
  | Var v1, Var v2 -> Apron.Var.compare v1 v2 == 0
  | Unop (op1, e1, t1, _), Unop (op2, e2, t2, _) ->
    if (eq_unop op1 op2) && (eq_typ t1 t2) then
      eq_iexpr e1 e2
    else false
  | Binop (op1, l1, r1, t1, _), Binop (op2, l2, r2, t2, _) ->
    if (eq_binop op1 op2) && (eq_typ t1 t2) then
      match op1 with
      | Add | Mul -> eq_commutative eq_iexpr (l1, r1) (l2, r2)
      | _ -> (eq_iexpr l1 l2) && (eq_iexpr r1 r2)
    else false
  | _ -> false

let rec eq_bexpr expr1 expr2 =
  match expr1, expr2 with
  | TRUE, TRUE
  | FALSE, FALSE
  | BRANDOM, BRANDOM -> true
  | CONS (l1, op1, r1), CONS (l2, op2, r2) ->
    (match op1, op2 with
     | EQ, EQ | NEQ, NEQ -> eq_commutative eq_iexpr (l1, r1) (l2, r2)
     | GT, GT | GEQ, GEQ | LEQ, LEQ | LT, LT ->
       (eq_iexpr l1 l2) && (eq_iexpr r1 r2)
     | GT, LT | LT, GT | GEQ, LEQ | LEQ, GEQ ->
       (eq_iexpr l1 r2) && (eq_iexpr r1 l2)
     | _ -> false)
  | AND (l1, r1), AND (l2, r2)
  | OR (l1, r1), OR (l2, r2) ->
    eq_commutative eq_bexpr (l1, r1) (l2, r2)
  | NOT b1, NOT b2 -> eq_bexpr b1 b2
  | _ -> false

let rec eq_instruction instr1 instr2 =
  match instr1, instr2 with
  | SKIP, SKIP
  | HALT, HALT
  | FAIL, FAIL -> true
  | ASSUME c1, ASSUME c2 -> eq_bexpr c1 c2
  | ASSIGN (v1, e1), ASSIGN (v2, e2) ->
    (eq_var v1 v2) && (eq_iexpr e1 e2)
  | CALL (os1, s1, is1), CALL (os2, s2, is2) ->
    (try
      (List.for_all2 eq_var os1 os2) &&
      (String.equal s1 s2) &&
      (List.for_all2 eq_var is1 is2)
    with _ -> false)
  | IF (c1, t1), IF (c2, t2) ->
    (eq_bexpr c1 c2) && (eq_block t1 t2)
  | IFELSE (c1, t1, e1), IFELSE (c2, t2, e2) ->
    (eq_bexpr c1 c2) && (eq_block t1 t2) && (eq_block e1 e2)
  | LOOP (c1, b1), LOOP (c2, b2) ->
    (eq_bexpr c1 c2) && (eq_block b1 b2)
  | _ -> false

and eq_instr instr1 instr2 =
  eq_instruction instr1.instruction instr2.instruction

and eq_block blk1 blk2 =
  try
    List.for_all2 eq_instr blk1.instrs blk2.instrs
  with _ -> false

let find_proc (prog: program) (pname: string): procedure =
  List.find (fun proc -> String.equal proc.pname pname) prog.procedures

let replace_proc (proc: procedure) (prog: program): program =
  let rec helper (procs: procedure list): procedure list =
    match procs with
    | [] -> []
    | p::ps ->
      if String.equal p.pname proc.pname
      then proc::ps
      else p::(helper ps)
  in
  { procedures = helper prog.procedures }

let remove_proc (pname: string) (prog: program): program =
  let rec helper (procs: procedure list): procedure list =
    match procs with
    | [] -> []
    | p::ps ->
      if String.equal p.pname pname then ps
      else p::(helper ps)
  in
  { procedures = helper prog.procedures }

let remove_call_stmt (proc: procedure) (pname: string): procedure =
  let rec helper (instrs: instr list): instr list =
    match instrs with
    | [] -> []
    | i::is ->
      (match i.instruction with
       | CALL (_, cname, _) when String.equal cname pname ->
         helper is
       | _ -> i::(helper is))
  in
  let code = proc.pcode in
  { proc with pcode = { code with instrs = helper code.instrs }}

let pr_stats (prog: program) : string =
  let numprocs = List.fold_left (fun acc _ -> acc + 1) 0 (prog.procedures) in
  ("{procs=" ^ (string_of_int (numprocs-2)) ^ "}")  
    
module HElem =
struct
  type t =
    | INST of instruction
    | EXPR of bexpr

  let equal t1 t2 =
    match t1, t2 with
    | INST i1, INST i2 -> eq_instruction i1 i2
    | EXPR e1, EXPR e2 -> eq_bexpr e1 e2
    | _ -> false

  let hash = Hashtbl.hash
end

module H = Hashtbl.Make(HElem)


