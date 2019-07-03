open Format
open Globals
open Lib.Print

module I = Iast
module F = Formula

module S = Spl_syn
module SU = Spl_utils
module Iproc = Frontend

let spl_main_name = ""
let iprog_main_name = "main"

(* Printing *)
let pr_output prog fp =
  pr_to_string (fun fmt fp ->
      Solving.print_output prog fmt fp) fp

let pr_abs pt fp =
  let abs = PSHGraph.attrvertex fp pt in
  pr_to_string (fun fmt fp ->
      Apron.Abstract1.print fmt abs) fp

(* Apron Utilities *)
let mk_spl_var (v: string): S.var =
  Apron.Var.of_string v

let mk_spl_iexpr_var (v: string): S.iexpr =
  Apron.Texpr1.Var (mk_spl_var v)

let mk_apron_scalar_int (v: int): Apron.Scalar.t =
  Apron.Scalar.of_int v

let mk_apron_scalar_float (v: float): Apron.Scalar.t =
  Apron.Scalar.of_float v

let mk_spl_iexpr_const (scalar: Apron.Scalar.t): S.iexpr =
  let coeff = Apron.Coeff.Scalar scalar in
  Apron.Texpr1.Cst coeff

let mk_spl_iexpr_random (): S.iexpr =
  Apron.Texpr1.Cst (Apron.Coeff.i_of_float neg_infinity infinity)

let mk_spl_iexpr_binop (bop: Apron.Texpr1.binop)
    (typ: Apron.Texpr1.typ) (left: S.iexpr) (right: S.iexpr)
  : S.iexpr =
  Apron.Texpr1.Binop (bop, left, right, typ, Apron.Texpr1.Rnd)

let mk_spl_block_of_instruction (pt: S.point) (instr: S.instruction): S.block =
  { S.bpoint = pt;
    S.instrs = [ { S.instruction = instr; S.ipoint = pt } ]; }

(* Translation to Interproc's Spl *)
let spl_of_pos (loc: pos): S.point =
  let pos = loc.pos_begin in
  { S.line = pos.Lexing.pos_lnum;
    S.col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol;
    S.char = pos.Lexing.pos_cnum; }

let spl_of_typ (t: typ): S.typ =
  match t with
  | TInt -> S.INT
  | TFloat -> S.REAL
  | _ -> warning_unexpected "spl_of_typ" pr_typ t

let apron_typ_of_typ (t: typ): Apron.Texpr1.typ =
  match t with
  | TInt -> Apron.Texpr1.Int
  | TFloat -> Apron.Texpr1.Real
  | _ -> warning_unexpected "apron_typ_of_typ" pr_typ t

let typ_of_apron_typ (t: Apron.Texpr1.typ): typ =
  match t with
  | Apron.Texpr1.Int -> TInt
  | Apron.Texpr1.Real -> TFloat
  | _ -> warning_unexpected "typ_of_apron_typ" Apron.Texpr1.string_of_typ t

let spl_constyp_of_bin_rel (brel: F.bin_rel): S.constyp =
  match brel with
  | F.Eq -> S.EQ
  | F.Ne -> S.NEQ
  | F.Gt -> S.GT
  | F.Ge -> S.GEQ
  | F.Lt -> S.LT
  | F.Le -> S.LEQ

let bin_rel_of_spl_constyp (srel: S.constyp): F.bin_rel  =
  match srel with
  | S.EQ -> F.Eq
  | S.NEQ -> F.Ne
  | S.GT -> F.Gt
  | S.GEQ -> F.Ge
  | S.LT -> F.Lt
  | S.LEQ -> F.Le

let apron_binop_of_bin_op (bop: F.bin_op): Apron.Texpr1.binop =
  match bop with
  | F.Add -> Apron.Texpr1.Add
  | F.Sub -> Apron.Texpr1.Sub
  | F.Mul -> Apron.Texpr1.Mul
  | F.Div -> Apron.Texpr1.Div
  | F.Mod -> Apron.Texpr1.Mod

let bin_op_of_apron_binop (sop: Apron.Texpr1.binop): F.bin_op =
  match sop with
  | Apron.Texpr1.Add -> F.Add
  | Apron.Texpr1.Sub -> F.Sub
  | Apron.Texpr1.Mul -> F.Mul
  | Apron.Texpr1.Div -> F.Div
  | Apron.Texpr1.Mod -> F.Mod
  | _ ->
    warning_unexpected "bin_op_of_apron_binop"
      Apron.Texpr1.string_of_binop sop

let spl_iexpr_of_exp (e: F.exp): S.iexpr =
  let rec helper e =
    match e with
    | F.Var ((v, typ), _) ->
      mk_spl_iexpr_var v, apron_typ_of_typ typ
    | F.IConst (v, _) ->
      mk_spl_iexpr_const (mk_apron_scalar_int v),
      apron_typ_of_typ TInt
    | F.FConst (v, _) ->
      mk_spl_iexpr_const (mk_apron_scalar_float v),
      apron_typ_of_typ TFloat
    | F.BinOp (bop, l, r, _) ->
      let sl, typl = helper l in
      let sr, typr = helper r in
      let typ =
        match typl, typr with
        | Apron.Texpr1.Int, Apron.Texpr1.Int -> Apron.Texpr1.Int
        | _ -> Apron.Texpr1.Real
      in
      mk_spl_iexpr_binop (apron_binop_of_bin_op bop) typ sl sr, typ
    | _ -> warning_unexpected "spl_iexpr_of_exp" F.pr_exp e
  in
  fst (helper e)

let exp_of_spl_iexpr
    ?(symtab=Hashtbl.create 10)
    (e: S.iexpr): F.exp =
  let rec helper t e =
    match e with
    | Apron.Texpr1.Var v ->
      let v_name = Apron.Var.to_string v in
      let latest_v =
        match Hashtbl.find_opt symtab v_name with
        | None ->
          let fresh_id = 0 in
          let () = Hashtbl.add symtab v_name fresh_id in
          v_name ^ (string_of_int fresh_id)
        | Some id -> v_name ^ (string_of_int id)
      in
      F.mk_evar (latest_v, typ_of_apron_typ t) no_pos
    | Apron.Texpr1.Cst c ->
      (match c with
       | Apron.Coeff.Scalar s ->
         (match s with
          | Float f -> F.mk_fconst f no_pos
          | Mpqf i -> F.mk_iconst (int_of_float (Mpqf.to_float i)) no_pos
          | Mpfrf f -> F.mk_fconst (Mpfrf.to_float f) no_pos)
       | _ -> warning_unexpected "exp_of_spl_iexpr" SU.pr_apron_coeff c)
    | Apron.Texpr1.Binop (op, l, r, ty, _) ->
      let fl = helper ty l in
      let fr = helper ty r in
      F.mk_bin_exp (bin_op_of_apron_binop op) fl fr no_pos
    | _ -> warning_unexpected "exp_of_spl_iexpr" SU.pr_iexpr e
  in
  helper Apron.Texpr1.Int e

let spl_cons_of_binrel (brel: F.bin_rel) (l: F.exp) (r: F.exp): S.cons =
  (spl_iexpr_of_exp l, spl_constyp_of_bin_rel brel, spl_iexpr_of_exp r)

let binrel_of_spl_cons
    ?(symtab=Hashtbl.create 10)
    (c: S.cons): F.formula =
  let (l, op, r) = c in
  F.mk_bin_rel (bin_rel_of_spl_constyp op)
    (exp_of_spl_iexpr ~symtab:symtab l)
    (exp_of_spl_iexpr ~symtab:symtab r) no_pos

let rec spl_bexpr_of_formula (form: F.formula): S.bexpr =
  match form with
  | F.BConst (b, _) -> if b then S.TRUE else S.FALSE
  | F.BinRel (brel, l, r, _) -> S.CONS (spl_cons_of_binrel brel l r)
  | F.Neg (f, _) -> S.NOT (spl_bexpr_of_formula f)
  | F.Conj (l, r, _) -> S.AND (spl_bexpr_of_formula l, spl_bexpr_of_formula r)
  | F.Disj (l, r, _) -> S.OR (spl_bexpr_of_formula l, spl_bexpr_of_formula r)
  | _ -> warning_unexpected "spl_bexpr_of_formula" F.pr_formula form

let formula_of_spl_bexpr
    ?(symtab=Hashtbl.create 10)
    (e: S.bexpr): F.formula =
  let rec helper e =
    match e with
    | S.TRUE -> F.mk_bconst true no_pos
    | S.FALSE -> F.mk_bconst false no_pos
    | S.CONS c -> binrel_of_spl_cons ~symtab:symtab c
    | S.AND (l, r) ->
      F.mk_conj (helper l) (helper r) no_pos
    | S.OR (l, r) ->
      F.mk_disj (helper l) (helper r) no_pos
    | S.NOT ne -> F.mk_neg (helper ne) no_pos
    | _ -> warning_unexpected "formula_of_spl_bexpr" SU.pr_bexpr e
  in helper e

let formula_of_spl_instruction
    ?(symtab=Hashtbl.create 10)
    (instr: S.instruction): F.formula =
  let incr_id vname =
    match Hashtbl.find_opt symtab vname with
    | None -> Hashtbl.add symtab vname 0; 0
    | Some id -> Hashtbl.replace symtab vname (id + 1); id + 1
  in
  let rec helper instr =
    match instr with
    | S.SKIP
    | S.HALT
    | S.FAIL -> F.mk_true ()
    | S.ASSUME c -> formula_of_spl_bexpr ~symtab:symtab c
    | S.ASSIGN (v, e) ->
      let f_e = exp_of_spl_iexpr ~symtab:symtab e in
      let vname = Apron.Var.to_string v in
      let latest_v_id = incr_id vname in
      F.mk_bin_rel F.Eq
        (F.mk_evar (vname ^ (string_of_int latest_v_id), TInt) no_pos)
        f_e
        no_pos
    | S.CALL (vs, _, _) ->
      let () =
        (match vs with
         | [] -> ()
         | _ -> List.iter (fun v ->
             let _ = incr_id (Apron.Var.to_string v) in
             ()) vs
        ) in
      F.mk_true ()
    | _ -> warning_unexpected "formula_of_spl_instruction" SU.pr_instruction instr
  in
  helper instr

let spl_var_of_stmt (stmt: I.statement): S.var =
  match stmt with
  | I.Var s -> mk_spl_var s.I.stmt_var_name
  | _ -> warning_unexpected "spl_var_of_stmt" I.pr_stmt stmt

let rec spl_instruction_of_stmt (stmt: I.statement): S.instruction =
  match stmt with
  | I.Skip s -> S.SKIP
  | I.Assume s -> S.ASSUME (spl_bexpr_of_formula s.I.stmt_assert_assume_condition)
  | I.Assert s ->
    let pt = spl_of_pos (I.pos_of_stmt stmt) in
    let cond = spl_bexpr_of_formula s.I.stmt_assert_assume_condition in
    let skip_block = mk_spl_block_of_instruction pt S.SKIP in
    let fail_block = mk_spl_block_of_instruction pt S.FAIL in
    S.IFELSE (cond, skip_block, fail_block)
  | I.Assign s ->
    let v = mk_spl_var s.I.stmt_assign_left in
     (try
        let exp = I.fexp_of_stmt s.I.stmt_assign_right in
        let iexp = spl_iexpr_of_exp exp in
        S.ASSIGN (v, iexp)
      with _ ->
        (match s.I.stmt_assign_right with
         | I.Call r ->
           let input_args = List.map spl_var_of_stmt r.I.stmt_call_args in
           S.CALL ([v], r.I.stmt_call_method, input_args)
         | I.Nondet r ->
           let exp = mk_spl_iexpr_random () in
           S.ASSIGN (v, exp)
         | _ -> warning_unexpected "spl_instruction_of_stmt" I.pr_stmt stmt))
  | I.Call s ->
    let input_args = List.map spl_var_of_stmt s.I.stmt_call_args in
    let output_args = [] in
    S.CALL (output_args, s.I.stmt_call_method, input_args)
  | I.Cond s ->
    let cond = spl_bexpr_of_formula
        (I.formula_of_stmt s.I.stmt_cond_condition) in
    let _, then_block = spl_block_of_stmt s.I.stmt_cond_then in
    let _, else_block = spl_block_of_stmt s.I.stmt_cond_else in
    S.IFELSE (cond, then_block, else_block)
  | I.While s ->
    let cond = spl_bexpr_of_formula
        (I.formula_of_stmt s.I.stmt_while_condition) in
    let _, body_block = spl_block_of_stmt s.I.stmt_while_body in
    S.LOOP (cond, body_block)
  | _ -> warning_unexpected "spl_instruction_of_stmt" I.pr_stmt stmt

and spl_instr_of_stmt (stmt: I.statement): S.instr =
  let instr = spl_instruction_of_stmt stmt in
  { S.instruction = instr; S.ipoint = spl_of_pos (I.pos_of_stmt stmt); }

and spl_instrs_of_stmt (stmt: I.statement): (S.declaration list * S.instr list) =
  match stmt with
  | I.Block s ->
    let local_vars = s.I.stmt_block_local_vars in
    let local_decls = List.map (fun (v, t, _) -> (mk_spl_var v, spl_of_typ t)) local_vars in
    let decls_body, instrs_body = spl_instrs_of_stmt s.I.stmt_block_body in
    (* TODO: To consider variable scope and name clashing problem *)
    (local_decls @ decls_body, instrs_body)
  | I.Seq s ->
    let decls_fst, instrs_fst = spl_instrs_of_stmt s.I.stmt_seq_fst in
    let decls_snd, instrs_snd = spl_instrs_of_stmt s.I.stmt_seq_snd in
    (decls_fst @ decls_snd, instrs_fst @ instrs_snd)
  | I.VarDecl _ -> ([], [])
  (* | I.VarDecl s ->
   *   let t = spl_of_typ s.I.stmt_var_decl_type in
   *   let decls = List.map (fun (v, _, _) -> (mk_spl_var v, t)) s.I.stmt_var_decl_lst in
   *   (decls, []) *)
  | _ -> ([], [spl_instr_of_stmt stmt])

and spl_block_of_stmt (s: I.statement): (S.declaration list * S.block) =
  let decls, instrs = spl_instrs_of_stmt s in
  (decls, { S.bpoint = spl_of_pos (I.pos_of_stmt s);
            S.instrs = instrs; })

and spl_block_of_stmt_opt (proc: I.proc_decl): (S.declaration list * S.block) =
  let loc = proc.I.proc_pos in
  let stmt =
    match proc.I.proc_body with
    | None -> (
        match proc.I.proc_return_type with
        | TVoid -> I.mk_skip loc
        | _ as t -> I.mk_assign I.OpAssign str_ret_name (I.mk_nondet t loc) loc)
    | Some s -> s
  in
  spl_block_of_stmt stmt

let spl_of_param (p: I.param): S.declaration =
  let v = mk_spl_var p.I.param_name in
  let t = spl_of_typ p.I.param_type in
  (v, t)

let spl_of_proc (proc: I.proc_decl): S.procedure =
  let poutput = match proc.I.proc_return_type with
    | TVoid -> []
    | _ as t -> [(mk_spl_var str_ret_name, spl_of_typ t)] in
  let plocal, pcode = spl_block_of_stmt_opt proc in
  let pname =
    if String.equal proc.I.proc_name iprog_main_name
    then spl_main_name
    else proc.I.proc_name in
  { S.pname = pname;
    S.pinput = List.map spl_of_param proc.I.proc_params;
    S.poutput = poutput;
    S.plocal = plocal;
    S.pcode = pcode; }

let spl_of_prog (prog: I.prog_decl): S.program =
  let iprog = I.trans_iprog_prog_decl prog in
  let sprog = { S.procedures = List.map spl_of_proc iprog.I.prog_proc_decls } in
  let () = Debug.dhprint "Input program" I.pr_prog iprog in
  let () = Debug.dhprint "Spl program" SU.pr_prog sprog in
  sprog

(* Apron Analysis *)
let get_context fp point =
  PSHGraph.attrvertex fp point

let is_bottom_abs fp point =
   let abs = PSHGraph.attrvertex fp point in
   let man = Apron.Abstract1.manager abs in
   Apron.Abstract1.is_bottom man abs

let is_infeasible_instr fp (i: S.instr) =
  is_bottom_abs fp i.S.ipoint

let is_infeasible_block fp (blk: S.block) =
  try
    let last_instr = List.nth blk.instrs ((List.length blk.instrs) - 1) in
    is_infeasible_instr fp last_instr
  with _ -> false

let is_infeasible_proc fp (proc: S.procedure) =
  is_infeasible_block fp proc.S.pcode

let is_infeasible_prog fp (prog: S.program) =
  try
    let main_proc = List.find (fun proc ->
        String.equal proc.S.pname spl_main_name) prog.procedures in
    is_infeasible_proc fp main_proc
  with _ -> false

let analyze_and_print domain prog =
  let () = Opt.domain := domain in
  pr_to_string (fun fmt prog ->
      Frontend.analyze_and_display fmt prog) prog

(* Parsing the program *)
let parse lexbuf =
  let prog = Frontend.parse_lexbuf Format.err_formatter lexbuf in

  if !Opt.debug > 0 then
    printf "%sProgram with its control points:%s@.%a@."
      (!Opt.displaytags).precolorB (!Opt.displaytags).postcolor
      (PSpl_syn.print_program
	       (begin fun fmt point ->
	          fprintf fmt "%s%a%s"
	            (!Opt.displaytags).precolorR
	            PSpl_syn.print_point point
	            (!Opt.displaytags).postcolor
	        end))
      prog
  ;
  prog

let parse_input_file input_file =
  let input = open_in input_file in
  let lexbuf = Lexing.from_channel input in
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                Lexing.pos_fname = "file " ^ (input_file); };
  let prog = parse lexbuf in
  close_in input;
  prog

let parse_string str =
  let lexbuf = Lexing.from_string str in
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                Lexing.pos_fname = "string"; };
  let prog = parse lexbuf in
  prog

let analyze_from_source input_file =
  let prog = parse_input_file input_file in
  (* Computing solution *)
  Debug.hprint "Analysis result:\n" (analyze_and_print !Opt.domain) prog

let analyze_from_string sprog =
  let prog = parse_string sprog in
  Debug.hprint "Analysis result:\n" (analyze_and_print !Opt.domain) prog

let analyze_forward
    (man: 'a Apron.Manager.t)
    (prog: S.program)
  : (S.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output =
  let fmt = Format.str_formatter in
  let (fgraph, bgraph) = Iproc.build_graphs fmt prog in
  Solving.Forward.compute ~fmt fgraph ~output:None man ~debug:!Opt.debug
