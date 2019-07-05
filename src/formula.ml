open Globals

type formula =
  | BVar of (var * pos)
  | BConst of (bool * pos)
  | BinRel of (bin_rel * exp * exp * pos)
  | Neg of (formula * pos)
  | Conj of (formula * formula * pos)
  | Disj of (formula * formula * pos)
  | Forall of (var * formula * pos)
  | Exists of (var * formula * pos)

and exp =
  | Var of (var * pos)
  | IConst of (int * pos)
  | FConst of (float * pos)
  | Func of (func * exp list * pos)
  | BinOp of (bin_op * exp * exp * pos)

and func =
  | Max
  | Min
  | Abs

and bin_rel =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne

and bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

let mk_true () =
  BConst(true, no_pos)

let mk_conj left right loc =
  Conj(left, right, loc)

let mk_disj left right loc =
  Disj(left, right, loc)

let mk_neg f loc =
  Neg(f, loc)

let mk_bin_rel op left right loc =
  BinRel(op, left, right, loc)

let mk_bin_exp op left right loc =
  BinOp(op, left, right, loc)

let mk_iconst v loc =
  IConst(v, loc)

let mk_fconst v loc =
  FConst(v, loc)

let mk_bconst v loc =
  BConst(v, loc)

let mk_bvar v loc =
  BVar(v, loc)

let mk_evar v loc =
  Var(v, loc)

let pr_bin_rel = function
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "="
  | Ne -> "!="

let pr_bin_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"

let pr_func = function
  | Max -> "max"
  | Min -> "min"
  | Abs -> "abs"

let rec pr_exp ?(pr_paren=false) e =
  let pr_e = pr_exp ~pr_paren:pr_paren in
  match e with
  | Var (v, _) -> pr_var v
  | IConst (v, _) -> string_of_int v
  | FConst (v, _) -> string_of_float v
  | Func (name, args, _) -> (pr_func name) ^ "(" ^ ")"
  | BinOp (op, f1, f2, _) ->
    let s = (pr_e f1) ^ (pr_bin_op op) ^ (pr_e f2) in
    if pr_paren then "(" ^ s ^ ")" else s

let rec pr_formula ?(pr_paren=false) f =
  let pr_f = pr_formula ~pr_paren:pr_paren in
  let pr_e = pr_exp ~pr_paren:pr_paren in
  match f with
  | BVar (v, _) -> pr_var v
  | BConst (v, _) -> string_of_bool v
  | BinRel (op, f1, f2, _) -> (pr_e f1) ^ (pr_bin_rel op) ^ (pr_e f2)
  | Neg (f, _) -> "!" ^ (pr_formula f)
  | Conj (f1, f2, _) ->
    let s = (pr_f f1) ^ " & " ^ (pr_f f2) in
    if pr_paren then "(" ^ s ^ ")" else s
  | Disj (f1, f2, _) ->
    let s = (pr_f f1) ^ " | " ^ (pr_f f2) in
    if pr_paren then "(" ^ s ^ ")" else s
  | Forall (v, f, _) -> "forall " ^ (pr_var v) ^ ". (" ^ (pr_formula f) ^ ")"
  | Exists (v, f, _) -> "exists " ^ (pr_var v) ^ ". (" ^ (pr_formula f) ^ ")"



  (*norm_neg, e.g. !(p | q ) -> !p & !q  *)

let rec norm_neg func =
    match func with
    | BVar (v, p) -> func
    | BConst (b, p) -> func
    | BinRel (br, e1, e2, p) -> func
    | Neg (f, p) ->
           (match f with
           | BVar (v, p) -> f
           | BConst (b, p) -> f
           | BinRel (br, e1, e2, p) -> f
           | Neg (f1, _) -> norm_neg f1
           | Conj (f1, f2, p1) ->
                   let norm_f1 = norm_neg f1 in
                   let norm_f2 = norm_neg f2 in
                   Disj (Neg (norm_f1, p1), Neg (norm_f2, p1), p1)
           | Disj (f1, f2, p1) -> 
                   let norm_f1 = norm_neg f1 in
                   let norm_f2 = norm_neg f2 in
                   Conj (Neg (norm_f1, p1), Neg (norm_f2, p1), p1)
           | Forall (v, f1, p1) ->
                   let norm_f1 = norm_neg f1 in
                   Exists (v, Neg (norm_f1, p1), p1)
           | Exists (v, f1, p1) ->
                   let norm_f1 = norm_neg f1 in
                   Forall (v, Neg (f1, p1), p1))
    | Conj (f1, f2, p1) ->
            let norm_f1 = norm_neg f1 in
            let norm_f2 = norm_neg f2 in
            Conj (norm_f1, norm_f2, p1)
    | Disj (f1, f2, p1) ->
            let norm_f1 = norm_neg f1 in
            let norm_f2 = norm_neg f2 in
            Disj (norm_f1, norm_f2, p1)
    | Forall (v, f, p1) -> Forall (v, norm_neg f, p1)
    | Exists (v, f, p1) -> Exists (v, norm_neg f, p1)
            
