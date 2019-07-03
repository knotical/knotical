open Globals
open Lib
open Lib.Print 

module DB = Debug
module F = Formula
module A = Kautomata

type prog_decl = {
  prog_proc_decls: proc_decl list;
  prog_file: string;
}

and proc_decl = {
  proc_name: ident;
  proc_params: param list;
  proc_return_type: typ;
  proc_body: statement option;
  proc_pos: pos;
}

and param = {
  param_type: typ;
  param_name: ident;
  param_pos: pos;
}

and statement =
  | Assert of stmt_assert_assume
  | Assume of stmt_assert_assume
  | VarDecl of stmt_var_decl
  | Assign of stmt_assign
  | Cond of stmt_cond
  | While of stmt_while
  | Call of stmt_call
  | Block of stmt_block
  | Seq of stmt_seq
  | Break of stmt_break
  | Continue of stmt_continue
  | Return of stmt_return
  | Skip of stmt_skip
  | Goto of stmt_goto
  | Label of stmt_label
  | IntLit of stmt_int_lit
  | FloatLit of stmt_float_lit
  | BoolLit of stmt_bool_lit
  | Nondet of stmt_nondet
  | Var of stmt_var
  | Unary of stmt_unary
  | Binary of stmt_binary

and stmt_var = {
  stmt_var_name: ident;
  stmt_var_pos: pos;
}

and stmt_int_lit = {
  stmt_int_lit_val: int;
  stmt_int_lit_pos: pos;
}

and stmt_float_lit = {
  stmt_float_lit_val: float;
  stmt_float_lit_pos: pos;
}

and stmt_bool_lit = {
  stmt_bool_lit_val: bool;
  stmt_bool_lit_pos: pos;
}

and stmt_nondet = {
  stmt_nondet_type: typ;
  stmt_nondet_pos: pos;
}

and stmt_binary = {
  stmt_binary_op: binary_op;
  stmt_binary_left: statement;
  stmt_binary_right: statement;
  stmt_binary_pos: pos;
}

and stmt_unary = {
  stmt_unary_op: unary_op;
  stmt_unary_exp: statement;
  stmt_unary_pos: pos;
}

and stmt_var_decl = {
  stmt_var_decl_type: typ;
  stmt_var_decl_lst: (ident * statement option * pos) list;
  stmt_var_decl_pos: pos;
}

and stmt_assert_assume = {
  stmt_assert_assume_condition: F.formula;
  stmt_assert_assume_pos: pos;
}

and stmt_assign = {
  stmt_assign_op: assign_op;
  stmt_assign_left: ident;
  stmt_assign_right: statement;
  stmt_assign_pos: pos;
}

and stmt_cond = {
  stmt_cond_condition: statement;
  stmt_cond_then: statement;
  stmt_cond_else: statement;
  stmt_cond_pos: pos;
}

and stmt_while = {
  stmt_while_condition: statement;
  stmt_while_body: statement;
  stmt_while_pos: pos;
}

and stmt_call = {
  stmt_call_method: ident;
  stmt_call_args: statement list;
  stmt_call_pos: pos;
}

and stmt_block = {
  stmt_block_body: statement;
  stmt_block_local_vars: (ident * typ * pos) list;
  stmt_block_pos: pos;
}

and stmt_seq = {
  stmt_seq_fst: statement;
  stmt_seq_snd: statement;
  stmt_seq_pos: pos;
}

and stmt_break = {
  stmt_break_pos: pos;
}

and stmt_continue = {
  stmt_continue_pos: pos;
}

and stmt_return = {
  stmt_return_val: statement option;
  stmt_return_pos: pos;
}

and stmt_skip = {
  stmt_skip_pos: pos;
}

and stmt_goto = {
  stmt_goto_label: string;
  stmt_goto_pos: pos;
}

and stmt_label = {
  stmt_label_name: string;
  stmt_label_stmt: statement;
  stmt_label_pos: pos;
}

and unary_op =
  | OpUMinus
  | OpPreInc
  | OpPreDec
  | OpPostInc
  | OpPostDec
  | OpLogicalNot

and binary_op =
  | OpPlus
  | OpMinus
  | OpMult
  | OpDiv
  | OpMod
  | OpEq
  | OpNe
  | OpLt
  | OpLe
  | OpGt
  | OpGe
  | OpLogicalAnd
  | OpLogicalOr

and assign_op =
  | OpAssign
  | OpPlusAssign
  | OpMinusAssign
  | OpMultAssign
  | OpDivAssign
  | OpModAssign

type kat_itest =
  | Dsj of kat_itest * kat_itest
  | Cnj of kat_itest * kat_itest
  | Neg of kat_itest
  | Top
  | Bot
  | Prd of F.formula

type kat_iexpr =
  | Pls of kat_iexpr * kat_iexpr
  | Dot of kat_iexpr * kat_iexpr
  | Str of kat_iexpr
  | Tst of kat_itest
  | KVar of statement
  | Any

let pos_of_stmt = function
  | Assert s -> s.stmt_assert_assume_pos
  | Assume s -> s.stmt_assert_assume_pos
  | VarDecl s -> s.stmt_var_decl_pos
  | Assign s -> s.stmt_assign_pos
  | Cond s -> s.stmt_cond_pos
  | While s -> s.stmt_while_pos
  | Call s -> s.stmt_call_pos
  | Block s -> s.stmt_block_pos
  | Seq s -> s.stmt_seq_pos
  | Break s -> s.stmt_break_pos
  | Continue s -> s.stmt_continue_pos
  | Return s -> s.stmt_return_pos
  | Skip s -> s.stmt_skip_pos 
  | Goto s -> s.stmt_goto_pos
  | Label s -> s.stmt_label_pos
  | IntLit s -> s.stmt_int_lit_pos
  | FloatLit s -> s.stmt_float_lit_pos
  | BoolLit s -> s.stmt_bool_lit_pos
  | Nondet s -> s.stmt_nondet_pos
  | Var s -> s.stmt_var_pos
  | Unary s -> s.stmt_unary_pos
  | Binary s -> s.stmt_binary_pos

let mk_prog ?(source_file="") procs =
  { prog_proc_decls = procs;
    prog_file = source_file; }

let mk_proc ty name params body loc =
  { proc_name = name;
    proc_params = params;
    proc_return_type = ty;
    proc_body = body;
    proc_pos = loc; }

let mk_param ty name loc =
  { param_type = ty;
    param_name = name;
    param_pos = loc; }

let mk_binary op left right loc =
  Binary {
    stmt_binary_op = op;
    stmt_binary_left = left;
    stmt_binary_right = right;
    stmt_binary_pos = loc; }

let mk_unary op exp loc =
  Unary {
    stmt_unary_op = op;
    stmt_unary_exp = exp;
    stmt_unary_pos = loc; }

let mk_var v loc =
  Var {
    stmt_var_name = v;
    stmt_var_pos = loc; }

let mk_int_lit v loc =
  IntLit {
    stmt_int_lit_val = v;
    stmt_int_lit_pos = loc; }

let mk_float_lit v loc =
  FloatLit {
    stmt_float_lit_val = v;
    stmt_float_lit_pos = loc; }

let mk_bool_lit v loc =
  BoolLit {
    stmt_bool_lit_val = v;
    stmt_bool_lit_pos = loc; }

let mk_stmt_assert_assume f loc =
  { stmt_assert_assume_condition = f;
    stmt_assert_assume_pos = loc; }

let mk_assume f loc =
  Assume (mk_stmt_assert_assume f loc)

let mk_stmt_seq fst snd loc =
  { stmt_seq_fst = fst;
    stmt_seq_snd = snd;
    stmt_seq_pos = loc; }

let mk_seq fst snd loc =
  Seq (mk_stmt_seq fst snd loc)

let mk_stmt_label label stmt loc =
  { stmt_label_name = label;
    stmt_label_stmt = stmt;
    stmt_label_pos = loc; }

let mk_label label stmt loc =
  Label (mk_stmt_label label stmt loc)

let mk_stmt_goto label loc =
  { stmt_goto_label = label;
    stmt_goto_pos = loc; }

let mk_goto label loc =
  Goto (mk_stmt_goto label loc)

let mk_skip loc =
  Skip { stmt_skip_pos = loc }

let mk_stmt_assign op v exp loc =
  { stmt_assign_op = op;
    stmt_assign_left = v;
    stmt_assign_right = exp;
    stmt_assign_pos = loc; }

let mk_assign op v exp loc =
  Assign (mk_stmt_assign op v exp loc)

let mk_stmt_nondet t loc =
  { stmt_nondet_type = t;
    stmt_nondet_pos = loc; }

let mk_nondet t loc =
  Nondet (mk_stmt_nondet t loc)

let add_var_decls (vars: var list) (stmt: statement): statement =
  match stmt with
  | Block s -> Block { s with stmt_block_local_vars =
                                s.stmt_block_local_vars @
                                List.map (fun (v, t) -> (v, t, s.stmt_block_pos)) vars }
  | _ ->
    let loc = pos_of_stmt stmt in
    Block { stmt_block_body = stmt;
            stmt_block_local_vars = List.map (fun (v, t) -> (v, t, loc)) vars;
            stmt_block_pos = loc; }

let is_single_stmt s =
  match s with
  | Assert _ | Assume _ | VarDecl _
  | Assign _ | Cond _ | While _ | Call _
  (* | Block _ | Seq _ *)
  | Break _ | Continue _
  | Return _ | Skip _ | Goto _ | Label _ -> true
  | _ -> false

let is_var_stmt s =
  match s with
  | Var _ -> true
  | _ -> false

let is_const_stmt s =
  match s with
  | IntLit _
  | FloatLit _
  | BoolLit _ -> true
  | _ -> false

let get_name_var_stmt = function
  | Var s -> Some (s.stmt_var_name)
  | _ -> None

let rec eq_stmt stmt1 stmt2 =
  let l1 = pos_of_stmt stmt1 in
  let l2 = pos_of_stmt stmt2 in
  if (eq_pos l1 l2) then
    match stmt1, stmt2 with
    | Assert _, Assert _
    | Assume _, Assume _
    | VarDecl _, VarDecl _
    | Assign _, Assign _
    | Break _, Break _
    | Continue _, Continue _
    | Return _, Return _
    | Skip _, Skip _
    | Nondet _, Nondet _ -> true
    | Cond _, Cond _
    | While _, While _
    | Call _, Call _
    | Block _, Block _
    | Seq _, Seq _ -> true
    | Goto s1, Goto s2 -> String.equal s1.stmt_goto_label s2.stmt_goto_label 
    | Label s1, Label s2 -> String.equal s1.stmt_label_name s2.stmt_label_name
    | IntLit _, IntLit _
    | FloatLit _, FloatLit _
    | BoolLit _, BoolLit _
    | Var _, Var _
    | Unary _, Unary _
    | Binary _, Binary _ -> true
    | _ -> false
  else false

let rec pr_prog ?(pr_paren=false) prog =
  List.fold_left (fun acc proc -> acc ^ "\n\n" ^
                                  (pr_proc ~pr_paren:pr_paren proc))
    "" prog.prog_proc_decls

and pr_proc ?(pr_paren=false) proc =
  (pr_typ proc.proc_return_type) ^ " " ^ proc.proc_name ^
  "(" ^ (String.concat ", " (List.map pr_param proc.proc_params)) ^ ")" ^
  (match proc.proc_body with
   | None -> ""
   | Some s -> "\n" ^ (pr_stmt ~pr_paren:pr_paren ~ntabs:1 s))

and pr_param param =
  (pr_typ param.param_type) ^ " " ^ param.param_name

and pr_stmt ?(pr_paren=false) ?(ntabs=0) stmt =
  let pr = F.pr_formula ~pr_paren:pr_paren in
  (if is_single_stmt stmt then pr_indent ntabs else "") ^
  (match stmt with
   | Assert s -> "assert " ^ (pr s.stmt_assert_assume_condition)
   | Assume s -> "assume " ^ (pr s.stmt_assert_assume_condition)
   | VarDecl s -> pr_var_decl_stmt s
   | Assign s -> pr_assign_stmt ~pr_paren:pr_paren s
   | Cond s -> pr_cond_stmt ~pr_paren:pr_paren ~ntabs:ntabs s
   | While s -> pr_while_stmt ~pr_paren:pr_paren ~ntabs:ntabs s
   | Call s -> pr_call_stmt ~pr_paren:pr_paren s
   | Block s -> pr_block_stmt ~pr_paren:pr_paren ~ntabs:ntabs s
   | Seq s -> pr_seq_stmt ~pr_paren:pr_paren ~ntabs:ntabs s
   | Break _ -> "break"
   | Continue _ -> "continue"
   | Return s -> pr_return_stmt ~pr_paren:pr_paren s
   | Skip _ -> "skip"
   | Goto s -> "goto " ^ s.stmt_goto_label
   | Label s -> pr_label_stmt ~pr_paren:pr_paren s
   | IntLit s -> string_of_int s.stmt_int_lit_val
   | FloatLit s -> string_of_float s.stmt_float_lit_val
   | BoolLit s -> string_of_bool s.stmt_bool_lit_val
   | Nondet _ -> "nondet()"
   | Var s -> pr_var_stmt s
   | Unary s -> pr_unary_stmt ~pr_paren:pr_paren s
   | Binary s -> pr_binary_stmt ~pr_paren:pr_paren s)

and pr_var_decl_stmt ?(pr_paren=false) s =
  (pr_typ s.stmt_var_decl_type) ^ " " ^
  (String.concat ", " (List.map (fun (id, v, _) ->
       id ^ (match v with
           | Some i -> " = " ^ (pr_stmt ~pr_paren:pr_paren i)
           | _ -> "")) s.stmt_var_decl_lst))

and pr_assign_stmt ?(pr_paren=false) s =
  s.stmt_assign_left ^ " " ^ (pr_assign_op s.stmt_assign_op) ^ " " ^
  (pr_stmt ~pr_paren:pr_paren s.stmt_assign_right)

and pr_cond_stmt ?(pr_paren=false) ?(ntabs=0) s =
  let pr = pr_stmt ~pr_paren:pr_paren ~ntabs:(ntabs+1) in
  "if (" ^ (pr_stmt ~pr_paren:pr_paren s.stmt_cond_condition) ^ ")\n" ^
  (pr s.stmt_cond_then) ^ "\n" ^
  (pr_indent ntabs) ^ "else \n" ^
  (pr s.stmt_cond_else)

and pr_while_stmt ?(pr_paren=false) ?(ntabs=0) s =
  let pr = pr_stmt ~pr_paren:pr_paren ~ntabs:(ntabs+1) in
  "while (" ^ (pr s.stmt_while_condition) ^ ")\n" ^
  (pr s.stmt_while_body)

and pr_call_stmt ?(pr_paren=false) s =
  let pr = pr_stmt ~pr_paren:pr_paren in
  s.stmt_call_method ^ "(" ^
  (String.concat ", " (List.map pr s.stmt_call_args)) ^ ")"

and pr_block_stmt ?(pr_paren=false) ?(ntabs=0) s =
  (pr_indent (ntabs-1)) ^ "{\n" ^
  (pr_stmt ~pr_paren:pr_paren ~ntabs:ntabs s.stmt_block_body) ^
  "\n" ^ (pr_indent (ntabs-1)) ^ "}"

and pr_seq_stmt ?(pr_paren=false) ?(ntabs=0) s =
  let pr = pr_stmt ~pr_paren:pr_paren ~ntabs:ntabs in
  (pr s.stmt_seq_fst) ^ "\n" ^ (pr s.stmt_seq_snd)

and pr_return_stmt ?(pr_paren=false) s =
  let pr = pr_stmt ~pr_paren:pr_paren in
  "return" ^ (pr_opt pr s.stmt_return_val)

and pr_label_stmt ?(pr_paren=false) s =
  s.stmt_label_name ^ ": " ^
  (pr_stmt ~pr_paren:pr_paren s.stmt_label_stmt)

and pr_var_stmt s =
  s.stmt_var_name

and pr_unary_stmt ?(pr_paren=false) s =
  let str_op = pr_unary_op s.stmt_unary_op in
  let str_s = pr_stmt ~pr_paren:pr_paren s.stmt_unary_exp in
  match s.stmt_unary_op with
  | OpPostInc
  | OpPostDec -> str_s ^ str_op
  | _ -> str_op ^ str_s

and pr_binary_stmt ?(pr_paren=false) s =
  let pr = pr_stmt ~pr_paren:pr_paren in
  let oparen = if pr_paren then "(" else "" in
  let cparen = if pr_paren then ")" else "" in
  oparen ^
  (pr s.stmt_binary_left) ^
  (pr_binary_op s.stmt_binary_op) ^
  (pr s.stmt_binary_right) ^
  cparen

and pr_unary_op = function
  | OpUMinus -> "-"
  | OpPreInc
  | OpPostInc -> "++"
  | OpPreDec
  | OpPostDec -> "--"
  | OpLogicalNot -> "!"

and pr_binary_op = function
  | OpPlus -> "+"
  | OpMinus -> "-"
  | OpMult -> "*"
  | OpDiv -> "/"
  | OpMod -> "%"
  | OpEq -> "=="
  | OpNe -> "!="
  | OpLt -> "<"
  | OpLe -> "<="
  | OpGt -> ">"
  | OpGe -> ">="
  | OpLogicalAnd -> "&&"
  | OpLogicalOr -> "||"

and pr_assign_op = function
  | OpAssign -> "="
  | OpPlusAssign -> "+="
  | OpMinusAssign -> "-="
  | OpMultAssign -> "*="
  | OpDivAssign -> "/="
  | OpModAssign -> "%="

and pr_kat_itest ?(pr_paren=false) = function
  | Dsj (e1, e2) -> "(" ^ (pr_kat_itest e1) ^ " | " ^ (pr_kat_itest e2) ^ ")"
  | Cnj (e1, e2) -> "(" ^ (pr_kat_itest e1) ^ " & " ^ (pr_kat_itest e2) ^ ")"
  | Neg e -> "!" ^ (pr_kat_itest e)
  | Top -> "T"
  | Bot -> "B"
  | Prd e -> "[" ^ (F.pr_formula ~pr_paren:pr_paren e) ^ "]"

and pr_kat_iexpr ?(pr_paren=false) = function
  | Pls (e1, e2) -> "(" ^ (pr_kat_iexpr e1) ^ " + " ^ (pr_kat_iexpr e2) ^ ")"
  | Dot (e1, e2) -> "(" ^ (pr_kat_iexpr e1) ^ "." ^ (pr_kat_iexpr e2) ^ ")"
  | Str e -> (pr_kat_iexpr e) ^ "*"
  | Tst t -> pr_kat_itest t
  | KVar s -> "{" ^ (pr_stmt ~pr_paren:pr_paren s) ^ "}"
  | Any -> "Any"

let fop_of_stmt_bin_op op =
  match op with
  | OpPlus -> F.Add
  | OpMinus -> F.Sub
  | OpMult -> F.Mul
  | OpDiv -> F.Div
  | OpMod -> F.Mod
  | _ -> warning_unexpected "fop_of_stmt_bin_op" pr_binary_op op

let fop_of_stmt_bin_rel op =
  match op with
  | OpEq -> F.Eq
  | OpNe -> F.Ne
  | OpLt -> F.Lt
  | OpLe -> F.Le
  | OpGt -> F.Gt
  | OpGe -> F.Ge
  | _ -> warning_unexpected "fop_of_stmt_bin_rel" pr_binary_op op

let rec fexp_of_stmt stmt =
  match stmt with
  | IntLit s -> F.mk_iconst s.stmt_int_lit_val s.stmt_int_lit_pos
  | FloatLit s -> F.mk_fconst s.stmt_float_lit_val s.stmt_float_lit_pos
  | Var s -> F.mk_evar (s.stmt_var_name, TInt) s.stmt_var_pos
  | Binary s ->
    let op = fop_of_stmt_bin_op s.stmt_binary_op in
    let left = fexp_of_stmt s.stmt_binary_left in
    let right = fexp_of_stmt s.stmt_binary_right in
    F.mk_bin_exp op left right s.stmt_binary_pos
  | _ -> warning_unexpected "fexp_of_stmt" pr_stmt stmt

let rec formula_of_stmt stmt =
  match stmt with
  | BoolLit s -> F.mk_bconst s.stmt_bool_lit_val s.stmt_bool_lit_pos
  | Var s ->  F.mk_bvar (s.stmt_var_name, TBool) s.stmt_var_pos
  | Binary s ->
    let loc = s.stmt_binary_pos in
    begin
      match s.stmt_binary_op with
      | OpLogicalOr ->
        let left = formula_of_stmt s.stmt_binary_left in
        let right = formula_of_stmt s.stmt_binary_right in
        F.mk_disj left right loc
      | OpLogicalAnd ->
        let left = formula_of_stmt s.stmt_binary_left in
        let right = formula_of_stmt s.stmt_binary_right in
        F.mk_conj left right loc
      | _ ->
        let op = fop_of_stmt_bin_rel s.stmt_binary_op in
        let left = fexp_of_stmt s.stmt_binary_left in
        let right = fexp_of_stmt s.stmt_binary_right in
        F.mk_bin_rel op left right loc
    end
  | Unary s ->
    begin
      match s.stmt_unary_op with
      | OpLogicalNot -> F.mk_neg (formula_of_stmt s.stmt_unary_exp) s.stmt_unary_pos
      | _ -> warning_unexpected "formula_of_stmt" pr_unary_op s.stmt_unary_op
    end
  | _ -> warning_unexpected "formula_of_stmt" pr_stmt stmt

let label_id = ref 0

let mk_fresh_label () =
  label_id := !label_id + 1;
  "lbl_" ^ (string_of_int !label_id)

let label_of_stmt stmt =
  match stmt with
  | Label s -> s.stmt_label_name
  | _ -> ""

let trans_proc_decl f proc =
  { proc with
    proc_body = Basic.map_option f proc.proc_body }

let trans_prog_decl f prog =
  { prog with
    prog_proc_decls = List.map f prog.prog_proc_decls; }

let rec trans_cfg_stmt ?(begin_label="") ?(end_label="") stmt =
  let trans_f = trans_cfg_stmt ~begin_label:begin_label ~end_label:end_label in
  match stmt with
  | While s ->
    let loc = s.stmt_while_pos in
    let begin_while_label = "while_" ^ (pr_pos_line loc) in
    let end_while_label = "endwhile_" ^ (pr_pos_line loc) in
    let cond = formula_of_stmt s.stmt_while_condition in
    let assume_cond = mk_assume cond loc in
    let labeled_assume_cond = mk_label begin_while_label assume_cond loc in
    let assume_not_cond = mk_assume (F.mk_neg cond loc) loc in
    let labeled_assume_not_cond = mk_label begin_while_label assume_not_cond loc in
    let goto_while_cond = mk_goto begin_while_label loc in
    let skip_stmt = mk_skip loc in
    let labeled_skip_stmt = mk_label end_while_label skip_stmt loc in
    let trans_body = trans_cfg_stmt
        ~begin_label:begin_while_label ~end_label:end_while_label
        s.stmt_while_body in
    mk_seq (mk_seq labeled_assume_cond (mk_seq trans_body goto_while_cond loc) loc)
      (mk_seq labeled_assume_not_cond labeled_skip_stmt loc) loc
  | Cond s ->
    let loc = s.stmt_cond_pos in
    let begin_if_label = "if_" ^ (pr_pos_line loc) in
    let end_if_label = "endif_" ^ (pr_pos_line loc) in
    let cond = formula_of_stmt s.stmt_cond_condition in
    let assume_then = mk_assume cond loc in
    let labeled_assume_then = mk_label begin_if_label assume_then loc in
    let assume_else = mk_assume (F.mk_neg cond loc) loc in
    let labeled_assume_else = mk_label begin_if_label assume_else loc in
    let goto_endif_stmt = mk_goto end_if_label loc in
    let then_stmt = trans_f s.stmt_cond_then in
    let then_seq = mk_seq labeled_assume_then
        (mk_seq then_stmt goto_endif_stmt loc) loc in
    let skip_stmt = mk_skip loc in
    let labeled_skip_stmt = mk_label end_if_label skip_stmt loc in
    let else_stmt = trans_f s.stmt_cond_else in
    let else_seq = mk_seq labeled_assume_else
        (mk_seq else_stmt labeled_skip_stmt loc) loc in
    mk_seq then_seq else_seq loc
  | Seq s ->
    let trans_fst = trans_f s.stmt_seq_fst in
    let trans_snd = trans_f s.stmt_seq_snd in
    mk_seq trans_fst trans_snd s.stmt_seq_pos
  | Block s -> trans_f s.stmt_block_body
  | Break s -> mk_goto end_label s.stmt_break_pos
  | Continue s -> mk_goto begin_label s.stmt_continue_pos
  | Assert _
  | Assume _
  | VarDecl _
  | Assign _
  | Call _
  | Return _
  | Skip _ -> mk_label (mk_fresh_label ()) stmt (pos_of_stmt stmt)
  | Goto _
  | Label _ -> stmt
  | _ -> warning_unexpected "trans_cfg_stmt" pr_stmt stmt

let trans_cfg_proc_decl proc =
  trans_proc_decl trans_cfg_stmt proc

let trans_cfg_prog_decl prog =
  trans_prog_decl trans_cfg_proc_decl prog

let rec flatten_stmt stmt =
  match stmt with
  | Seq s ->
    let flatten_fst = flatten_stmt s.stmt_seq_fst in
    let flatten_snd = flatten_stmt s.stmt_seq_snd in
    flatten_fst @ flatten_snd
  | Block s -> flatten_stmt s.stmt_block_body
  | _ -> [stmt]

let flatten_proc_decl proc =
  match proc.proc_body with
  | None -> []
  | Some s -> flatten_stmt s

let flatten_prog_decl prog =
  List.map (fun proc -> (proc.proc_name, flatten_proc_decl proc))
    prog.prog_proc_decls

let trans_iprog_stmt stmt =
  let merge_tl_stmts stmt stmt_lst =
    List.fold_right (fun stmt acc ->
      mk_seq stmt acc (pos_of_stmt stmt)) stmt_lst stmt
  in
  let merge_hd_stmts stmt stmt_lst =
    List.fold_left (fun acc stmt ->
      mk_seq acc stmt (pos_of_stmt stmt)) stmt stmt_lst
  in
  let rec helper ?(is_exp=false) (stmt: statement)
    : statement * statement list * var list =
    match stmt with
    | VarDecl s ->
      let decl_assigns, exp_vars = List.fold_left (fun (a_acc, v_acc) (v, s_opt, loc) ->
          match s_opt with
          | None -> (a_acc, v_acc)
          | Some exp ->
            let trans_exp, exp_assigns, exp_vars = helper exp in
            let init_assign = mk_assign OpAssign v trans_exp loc in
            (a_acc @ exp_assigns @ [init_assign], v_acc @ exp_vars)) ([], []) s.stmt_var_decl_lst in
      let trans_var_decl = VarDecl { s with stmt_var_decl_lst =
                                              List.map (fun (v, _, loc) -> (v, None, loc))
                                                s.stmt_var_decl_lst } in
      let decl_vars = List.map (fun (v, _, _) -> (v, s.stmt_var_decl_type)) s.stmt_var_decl_lst in
      (merge_hd_stmts trans_var_decl decl_assigns, [], decl_vars @ exp_vars)
    | Assign s ->
      let trans_exp, exp_assigns, exp_vars = helper s.stmt_assign_right in
      let trans_assign = Assign { s with stmt_assign_right = trans_exp } in
      (merge_tl_stmts trans_assign exp_assigns, [], exp_vars)
    | Cond s ->
      let trans_cond, cond_assigns, cond_vars = helper ~is_exp:true s.stmt_cond_condition in
      let trans_then, then_assigns, then_vars = helper s.stmt_cond_then in
      let trans_else, else_assigns, else_vars = helper s.stmt_cond_else in
      let trans_cond = Cond { s with
                              stmt_cond_condition = trans_cond;
                              stmt_cond_then = merge_tl_stmts trans_then then_assigns;
                              stmt_cond_else = merge_tl_stmts trans_else else_assigns; } in
      (merge_tl_stmts trans_cond cond_assigns, [], cond_vars @ then_vars @ else_vars)
    | While s ->
      let trans_cond, cond_assigns, cond_vars = helper ~is_exp:true s.stmt_while_condition in
      let trans_body, body_assigns, body_vars = helper s.stmt_while_body in
      let trans_while = While { s with
                                stmt_while_condition = trans_cond;
                                stmt_while_body = merge_tl_stmts trans_body body_assigns; } in
      (merge_tl_stmts trans_while cond_assigns, [], cond_vars @ body_vars)
    | Block s ->
      let trans_body, block_assigns, block_vars = helper s.stmt_block_body in
      let merged_body = merge_tl_stmts trans_body block_assigns in
      let trans_block = Block { s with stmt_block_body = merged_body } in
      (trans_block, [], block_vars)
    | Seq s ->
      let trans_fst, fst_assigns, fst_vars = helper s.stmt_seq_fst in
      let trans_snd, snd_assigns, snd_vars = helper s.stmt_seq_snd in
      let trans_seq = Seq { s with
                            stmt_seq_fst = merge_tl_stmts trans_fst fst_assigns;
                            stmt_seq_snd = merge_tl_stmts trans_snd snd_assigns; } in
      (trans_seq, [], fst_vars @ snd_vars)
    | Return s ->
      let loc = s.stmt_return_pos in
      begin match s.stmt_return_val with
        | None -> (mk_skip loc, [], [])
        | Some exp ->
          let trans_exp, exp_assigns, exp_vars = helper ~is_exp:true exp in
          let ret_assign = mk_assign OpAssign str_ret_name trans_exp loc in
          (merge_tl_stmts ret_assign exp_assigns, [], exp_vars)
      end
    | Unary s ->
      let trans_exp, exp_assigns, exp_vars = helper ~is_exp:true s.stmt_unary_exp in
      let trans_unary = Unary { s with stmt_unary_exp = trans_exp } in
      (trans_unary, exp_assigns, exp_vars)
    | Binary s ->
      let trans_left, left_assigns, left_vars = helper ~is_exp:true s.stmt_binary_left in
      let trans_right, right_assigns, right_vars = helper ~is_exp:true s.stmt_binary_right in
      let trans_binary = Binary { s with stmt_binary_left = trans_left;
                                         stmt_binary_right = trans_right; } in
      (trans_binary, left_assigns @ right_assigns, left_vars @ right_vars)
    | Call s ->
      let loc = s.stmt_call_pos in
      let trans_args, arg_assigns_lst, arg_vars_lst =
        List.split3 (List.map (helper ~is_exp:true) s.stmt_call_args) in
      let arg_assigns = List.concat arg_assigns_lst in
      let arg_vars = List.concat arg_vars_lst in
      let fresh_arg_assigns, fresh_arg_vars, var_args =
        List.fold_left (fun (acc_assigns, acc_vars, acc_args) arg ->
            if is_var_stmt arg (* || is_const_stmt arg *) then
            (acc_assigns, acc_vars, acc_args @ [arg])
          else
            let fresh_var_name = fresh_var_new_name () in
            let fresh_arg_assign = mk_stmt_assign OpAssign fresh_var_name arg loc in
            (acc_assigns @ [fresh_arg_assign],
             acc_vars @ [(fresh_var_name, TInt)],
             acc_args @ [mk_var fresh_var_name loc])
        ) ([], [], []) trans_args in
      let trans_call = Call { s with stmt_call_args = var_args } in
      if is_exp then
        let fresh_var_call = fresh_var_new_name () in
        let fresh_call_assign = mk_assign OpAssign fresh_var_call trans_call loc in
        (mk_var fresh_var_call loc,
         arg_assigns @ (List.map (fun assign -> Assign assign) fresh_arg_assigns)
         @ [fresh_call_assign],
        arg_vars @ fresh_arg_vars @ [(fresh_var_call, TInt)])
      else
        (* (merge_tl_stmts trans_call
         *    (arg_assigns @ (List.map (fun assign -> Assign assign) fresh_arg_assigns)), [],
         *  arg_vars @ fresh_arg_vars) *)
        (trans_call,
         arg_assigns @ (List.map (fun assign -> Assign assign) fresh_arg_assigns),
         arg_vars @ fresh_arg_vars)
    | _ -> (stmt, [], [])
  in
  let trans_stmt, stmt_assigns, decl_vars = helper stmt in
  merge_tl_stmts trans_stmt stmt_assigns, decl_vars

let trans_iprog_proc_decl (proc: proc_decl): proc_decl =
  match proc.proc_body with
  | None -> proc
  | Some s ->
    let trans_s, decl_vars = trans_iprog_stmt s in
    let () = Debug.dhprint "New decl_vars: " (pr_list pr_var) decl_vars in 
    { proc with proc_body = Some (add_var_decls decl_vars trans_s) }

let trans_iprog_prog_decl prog =
  trans_prog_decl trans_iprog_proc_decl prog
