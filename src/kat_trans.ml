open Globals
open Lib.Print

module H = Extlib.ExtHashtbl.Hashtbl

module SL = Spl_lbl
module B = Boolexpr
module S = Spl_syn
module SU = Spl_utils
module I = Iast

type 'a iproc_output =
  (S.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output

module type KSym = functor (K: Kat_sig.K) ->
sig
  type store
  type symtab

  val key_of_spl_cons: S.point -> S.cons -> K.key
  val var_of_spl_instr: S.point -> S.instruction -> K.var
  val spl_cons_of_key: ?symtbl:(symtab option) ->
    K.key -> (S.point list * S.cons) option
  val spl_instr_of_var: ?symtbl:(symtab option) ->
    K.var -> (S.point list * S.instruction) option

  val spl_cons_of_sym: K.sym -> (S.point list * S.cons) option
  val spl_instr_of_sym: K.sym -> (S.point list * S.instruction) option

  val rename_var: K.var -> K.var
  val rename_key: K.key -> K.key
  val backup: unit -> store
  val restore: store -> unit
  val reset: unit -> unit

  val get_symtab: unit -> symtab
  val get_vars: unit -> K.var list
  val get_keys: unit -> K.key list
  val get_syms: unit -> K.sym list

  val pr_symtab: symtab -> string
  val pr_bexpr_mapping: unit -> string
  val pr_instr_mapping: unit -> string
  val pr_loc_mapping: unit -> string
end

module type KTrans = functor (K: Kat_sig.K) ->
sig
  type test = K.test
  type expr = K.expr
  type key = K.key
  type var = K.var
  type sym = K.sym
  type symtab

  (* Translation of Interproc internal boolean expressions *)
  val kat_of_slabel: (key SL.label) -> test
  val kat_of_sconj: ((key SL.label list * _)) -> test
  val kat_of_boolexpr: ((key SL.label list * _) B.t) -> test

  (* Translation of Spl programs *)
  val kat_of_prog: S.program -> (ident * expr) list
  val kat_of_cmp_proc: S.program -> string -> string -> expr

  (* Translation of Iast KAT properties *)
  val kat_of_prop: I.kat_iexpr -> expr

  val spl_cons_of_key: ?symtbl:(symtab option) ->
    key -> (S.point list * S.cons) option
  val spl_instr_of_var: ?symtbl:(symtab option) ->
    var -> (S.point list * S.instruction) option
  val spl_cons_of_sym: sym -> (S.point list * S.cons) option
  val spl_instr_of_sym: sym -> (S.point list * S.instruction) option

  val spl_prog_of_kat: expr -> S.program

  val rename_var: var -> var
  val rename_key: key -> key
  val wrap: (unit -> 'a) -> 'a

  val get_symtab: unit -> symtab

  val pr_symtab: symtab -> string
  val print_kprog: (ident * expr) list -> unit
end

module MakeTrans (KSym: KSym): KTrans = functor (K: Kat_sig.K) ->
struct
  module KS = KSym (K)

  type test = K.test
  type expr = K.expr
  type key = K.key
  type var = K.var
  type sym = K.sym
  type symtab = KS.symtab

  type 'l lcons = ('l, S.cons) SL.lcons

  let lcons_of_scons (pt: S.point) (scons: S.cons): 'l lcons =
    let symb = KS.key_of_spl_cons pt scons in
    ((true, symb), scons)

  let kat_of_slabel
      (l: key SL.label): test =
    let (b, s) = l in
    let ks = K.mk_prd s in
    let kl = if b then ks else K.mk_neg ks in
    kl

  let kat_of_sconj
      (conj: (key SL.label list * _)): test =
    let lbl, _ = conj in
    match lbl with
    | [] -> K.mk_top
    | l::ls ->
      let kl = kat_of_slabel l in
      List.fold_left (fun acc kl -> K.mk_conj acc kl)
        kl (List.map kat_of_slabel ls)

  let kat_of_boolexpr
      (expr: (key SL.label list * _) B.t): test =
    match expr with
    | B.TRUE -> K.mk_top
    | B.DISJ conjs ->
      (match conjs with
       | [] -> K.mk_bot
       | c::cs ->
         let kc = kat_of_sconj c in
         List.fold_left (fun acc kc -> K.mk_disj acc kc)
           kc (List.map kat_of_sconj cs))

  let rec kat_test_of_spl_bexpr
      (pt: S.point)
      (bexp: S.bexpr): test =
    match bexp with
    | S.TRUE -> K.mk_top
    | S.FALSE -> K.mk_bot
    | S.BRANDOM -> K.mk_prd K.key_of_brandom
    | S.CONS cons ->
      let test_symb = KS.key_of_spl_cons pt cons in 
      K.mk_prd test_symb
    | S.AND (l, r) ->
      let kl = kat_test_of_spl_bexpr pt l in
      let kr = kat_test_of_spl_bexpr pt r in
      K.mk_conj kl kr
    | S.OR (l, r) ->
      let kl = kat_test_of_spl_bexpr pt l in
      let kr = kat_test_of_spl_bexpr pt r in
      K.mk_disj kl kr
    | S.NOT e ->
      let ke = kat_test_of_spl_bexpr pt e in
      K.mk_neg ke

  let rec kat_of_spl_instruction
      (fp: 'a iproc_output option)
      (pt: S.point)
      (instr: S.instruction): expr =
    match instr with
    | S.SKIP -> K.mk_tst K.mk_top
    | S.ASSUME c ->
      (* let skip_block = Spl.mk_spl_block_of_instruction pt S.SKIP in
       * let halt_block = Spl.mk_spl_block_of_instruction pt S.HALT in
       * kat_of_spl_instruction fp pt (S.IFELSE (c, skip_block, halt_block)) *)
      K.mk_tst (kat_test_of_spl_bexpr pt c)
    | S.HALT
    | S.FAIL
    | S.ASSIGN _
    | S.CALL _ ->
      let symb = KS.var_of_spl_instr pt instr in
      K.mk_var symb
    | S.IF (c, t) ->
      let kt = kat_of_spl_block fp t in
      if K.is_bot_expr kt then
        K.mk_tst K.mk_top
      else 
        let kc = kat_test_of_spl_bexpr t.S.bpoint c in
        let knc = K.mk_neg kc in
        (* if c then t = c.t + !c *)
        K.mk_pls (K.mk_dot (K.mk_tst kc) kt) (K.mk_tst knc)
    | S.IFELSE (c, t, e) ->
      let kt = kat_of_spl_block fp t in
      let ke = kat_of_spl_block fp e in
      if K.is_bot_expr kt then
        ke
      else if K.is_bot_expr ke then
        kt
      else
        let kc = kat_test_of_spl_bexpr t.S.bpoint c in
        let knc = K.mk_neg kc in
        (* if c then t else e = c.t + !c.e *)
        K.mk_pls (K.mk_dot (K.mk_tst kc) kt) (K.mk_dot (K.mk_tst knc) ke)
    | S.LOOP (c, b) ->
      let kc = kat_test_of_spl_bexpr b.S.bpoint c in
      let knc =
        match fp with
        | None -> K.mk_neg kc
        | Some fp ->
          let labeled_c = SL.bexpr_of_spl (lcons_of_scons b.S.bpoint) c in
          let () = Debug.dhprint "labeled_c: "
              (SL.pr_bexpr (SL.pr_lcons K.pr_key SU.pr_cons)) labeled_c in
          let neg_labeled_c = SL.NOT labeled_c in

          let ctx = Spl.get_context fp pt in
          let man = Apron.Abstract1.manager ctx in
          let env = Apron.Abstract1.env ctx in
          let bexpr_arr_neg_c = SL.boolexpr_of_bexpr
              (Syn2equation.tcons_of_cons env) neg_labeled_c in
          let bexpr_earray_neg_c = Boolexpr.map (SL.earray_of_lcons_array env) bexpr_arr_neg_c in

          let feasible_bexpr_neg_c =
            match bexpr_earray_neg_c with
            | Boolexpr.TRUE -> Boolexpr.TRUE
            | Boolexpr.DISJ conjs ->
              let feasible_conjs = List.filter (fun (_, conj) ->
                  let ctx_conj = Apron.Abstract1.meet_tcons_array man ctx conj in
                  not (Apron.Abstract1.is_bottom man ctx_conj)) conjs in
              Boolexpr.DISJ feasible_conjs in

          let feasible_knc = kat_of_boolexpr feasible_bexpr_neg_c in
          feasible_knc
      in
      let kb = kat_of_spl_block fp b in
      (* while c do b = (c.b)*!c *)
      K.mk_dot (K.mk_str (K.mk_dot (K.mk_tst kc) kb)) (K.mk_tst knc)

  and kat_of_spl_instr
      (fp: 'a iproc_output option)
      (instr: S.instr): expr =
    match fp with
    | Some fp when (Spl.is_bottom_abs fp instr.S.ipoint) ->
      K.mk_tst K.mk_bot
    | _ -> kat_of_spl_instruction fp instr.S.ipoint instr.S.instruction

  and kat_of_spl_block
      (fp: 'a iproc_output option)
      (blk: S.block): expr =
    let pt = blk.S.bpoint in
    let () = Debug.dhprint "pt: " SU.pr_point pt in
    let () = Debug.dhprint "abs: " (pr_opt (Spl.pr_abs pt)) fp in

    let rec helper instrs = 
      match instrs with
      | [] -> kat_of_spl_instruction fp pt S.SKIP
      | [i] -> kat_of_spl_instr fp i
      | i::is -> K.mk_dot (kat_of_spl_instr fp i) (helper is)
    in
    match fp with
    | Some fp when Spl.is_bottom_abs fp pt -> K.mk_tst K.mk_bot
    | _ -> helper blk.instrs

  let kat_of_proc
      (fp: 'a iproc_output option)
      (proc: S.procedure): ident * expr =
    let ke = kat_of_spl_block fp proc.S.pcode in
    let pname =
      if String.length proc.S.pname == 0
      then "main" else proc.S.pname in
    (pname, ke)

  let kat_of_prog (prog: S.program): (ident * expr) list =
    let () = if !use_diff_sym then KS.reset () in
    try
      let man = Polka.manager_alloc_loose () in
      let fp = Spl.analyze_forward man prog in
      let () = Debug.dhprint "iproc: " (Spl.pr_output prog) fp in 
      let pk_list = List.map (kat_of_proc (Some fp)) prog.S.procedures in
      pk_list
    with e ->
      let () = Debug.hprint "Interproc Exception: " Printexc.to_string e in
      raise e

  let kat_of_cmp_proc (prog: S.program)
      (pname: string) (other_pname: string)
    : expr =
    let pname_main = "" in
    let pmain = SU.find_proc prog pname_main in
    let mod_pmain = SU.remove_call_stmt pmain other_pname in
    let mod_prog =
      prog
      |> SU.replace_proc mod_pmain
      |> SU.remove_proc other_pname in
    let () = Debug.dhprint "mod_prog: " SU.pr_prog mod_prog in
    let klprog = kat_of_prog mod_prog in
    List.assoc pname klprog

  let kat_of_prop (prop: I.kat_iexpr): expr =
    let vars =
      KS.get_vars ()
      |> List.map (fun v -> v |> K.sym_of_var |> K.var_of_sym)
    in
    let expr_of_any =
      match vars with
      | [] -> K.mk_tst K.mk_top
      | v::vs ->
        List.fold_left (fun a v -> K.mk_pls a (K.mk_var v)) (K.mk_var v) vs
    in
    let () = Debug.nhprint "vars for Any: " (pr_list K.pr_var) vars in
    let () = Debug.nhprint "expr_of_any: " K.pr_expr expr_of_any in
    let rec kat_of_itest tst =
      match tst with
      | I.Dsj (e1, e2) -> K.mk_disj (kat_of_itest e1) (kat_of_itest e2)
      | I.Cnj (e1, e2) -> K.mk_conj (kat_of_itest e1) (kat_of_itest e2)
      | I.Neg e -> K.mk_neg (kat_of_itest e)
      | I.Top -> K.mk_top
      | I.Bot -> K.mk_bot
      | I.Prd f ->
        kat_test_of_spl_bexpr
          (Spl.spl_of_pos (I.F.pos_of_formula f))
          (Spl.spl_bexpr_of_formula f)
    in
    let rec kat_of_iexpr expr =
      match expr with
      | I.Pls (e1, e2) -> K.mk_pls (kat_of_iexpr e1) (kat_of_iexpr e2)
      | I.Dot (e1, e2) -> K.mk_dot (kat_of_iexpr e1) (kat_of_iexpr e2)
      | I.Str e -> K.mk_str (kat_of_iexpr e)
      | I.Tst t -> K.mk_tst (kat_of_itest t)
      | I.KVar s ->
        kat_of_spl_instruction None
          (Spl.spl_of_pos (I.pos_of_stmt s))
          (Spl.spl_instruction_of_stmt s)
      | I.Any -> expr_of_any
    in
    kat_of_iexpr prop

  let spl_cons_of_key = KS.spl_cons_of_key

  let spl_instr_of_var = KS.spl_instr_of_var

  let spl_cons_of_sym = KS.spl_cons_of_sym

  let spl_instr_of_sym = KS.spl_instr_of_sym

  let curr_line = ref 0

  let reset_curr_line () =
    curr_line := 0

  let gen_new_line () =
    let () = curr_line := !curr_line + 1 in
    !curr_line

  let gen_new_point () =
    { S.line = gen_new_line ();
      S.col = 0;
      S.char = 0; }

  let update_line (pt: S.point) =
    { pt with S.line = gen_new_line () }

  let rec spl_prog_of_kat (e: expr): S.program =
    let () = reset_curr_line () in
    { S.procedures = [ spl_main_proc_of_kat e ] }

  and spl_main_proc_of_kat (e: expr): S.procedure =
    let plocal, pcode = spl_block_of_kat e in
    let pname = Spl.spl_main_name in
    { S.pname = pname;
      S.pinput = [];
      S.poutput = [];
      S.plocal = plocal;
      S.pcode = pcode; }

  and spl_block_of_kat ?(symtab=[]) (e: expr): (S.declaration list * S.block) =
    let pt = gen_new_point () in
    let decls, instrs = spl_instrs_of_kat symtab e in
    (decls, { S.bpoint = pt;
              S.instrs = instrs; })

  and spl_instrs_of_kat symtab (e: expr): (S.declaration list * S.instr list) =
    match e with
    | K.Var v ->
      (match spl_instr_of_var v with
       | None -> ([], [])
       | Some (ps, i) ->
         let pt =
           match ps with
           | p::_ -> update_line p
           | _ -> gen_new_point ()
         in
         (match i with
          | S.ASSIGN (v, ie) ->
            let decls =
              let vname = Apron.Var.to_string v in
              (match List.assoc_opt vname symtab with
               | Some _ -> []
               | None ->
                 let t = SU.typ_of_iexpr symtab ie in
                 [(v, t)])
            in
            (decls, [{ S.instruction = i;
                       S.ipoint = pt; }])
          | _ -> ([], [])))
    | K.Tst t ->
      let decls, pt, e = spl_bexpr_of_kat symtab t in
      (decls, [{ S.instruction = S.ASSUME e;
              S.ipoint = pt; }])
    | K.Str s ->
      let pt = gen_new_point () in
      let decls, loop_block = spl_block_of_kat ~symtab:symtab s in
      (decls, [{ S.instruction = S.LOOP (S.BRANDOM, loop_block);
                 S.ipoint = pt; }])
    | K.Dot (l, r) ->
      let ldecls, linstrs = spl_instrs_of_kat symtab l in
      let rdecls, rinstrs = spl_instrs_of_kat
          (update_symtab symtab ldecls)
          r
      in
      (ldecls @ rdecls, linstrs @ rinstrs)
    | K.Pls (l, r) ->
      let pt = gen_new_point () in
      let ldecls, then_block = spl_block_of_kat ~symtab:symtab l in
      let rdecls, else_block = spl_block_of_kat ~symtab:symtab r in
      (ldecls @ rdecls,
       [{ S.instruction = S.IFELSE (S.BRANDOM, then_block, else_block);
          S.ipoint = pt; }])

  and spl_bexpr_of_kat symtab (t: test): (S.declaration list * S.point * S.bexpr) =
    match t with
    | K.Dsj (l, r) ->
      let ldecls, pl, el = spl_bexpr_of_kat symtab l in
      let rdecls, _, er = spl_bexpr_of_kat (update_symtab symtab ldecls) r in
      ldecls @ rdecls, pl, S.OR (el, er)
    | K.Cnj (l, r) ->
      let ldecls, pl, el = spl_bexpr_of_kat symtab l in
      let rdecls, _, er = spl_bexpr_of_kat (update_symtab symtab ldecls) r in
      ldecls @ rdecls, pl, S.AND (el, er)
    | K.Neg nt ->
      let decls, p, e = spl_bexpr_of_kat symtab nt in
      decls, p, S.NOT e
    | K.Top -> [], gen_new_point(), S.TRUE
    | K.Bot -> [], gen_new_point(), S.FALSE
    | K.Prd k ->
      if K.eq_key k K.key_of_brandom then
        [], gen_new_point(), S.BRANDOM
      else
        match spl_cons_of_key k with
        | None -> ([], gen_new_point (), S.TRUE)
        | Some (ps, c) ->
          let pt =
            match ps with
            | p::_ -> update_line p
            | _ -> gen_new_point ()
          in
          get_decls_from_cons symtab c, pt, S.CONS c

  and get_decls_from_cons symtab (l, _, r) =
    let ldecls = get_decls_from_iexpr symtab l in
    let rdecls = get_decls_from_iexpr symtab r in
    ldecls @ rdecls

  and get_decls_from_iexpr symtab ie =
    let rec helper symtab expected_typ ie =
      match ie with
      | Apron.Texpr1.Cst _ -> []
      | Apron.Texpr1.Unop (_, e, ty, _) ->
        helper symtab (SU.typ_of_apron_typ ty) e
      | Apron.Texpr1.Binop (_, el, er, ty, _) ->
        let etyp = SU.typ_of_apron_typ ty in
        let ldecls = helper symtab etyp el in
        let rdecls = helper (update_symtab symtab ldecls) etyp er in
        ldecls @ rdecls
      | Apron.Texpr1.Var v ->
        let vname = Apron.Var.to_string v in
        (match List.assoc_opt vname symtab with
         | None -> [(v, expected_typ)]
         | Some _ -> [])
    in
    helper symtab INT ie


  and update_symtab symtab decls =
    symtab @
    (List.map (fun ((v, _) as d) -> (Apron.Var.to_string v, d)) decls)

  let rename_var = KS.rename_var

  let rename_key = KS.rename_key

  let wrap (f: unit -> 'a): 'a =
    let k_store = K.backup () in
    let ks_store = KS.backup () in
    let r = f () in
    let () = K.restore k_store in
    let () = KS.restore ks_store in
    r

  let get_symtab () = KS.get_symtab ()

  let pr_symtab = KS.pr_symtab

  let print_kprog (kprog: (ident * expr) list) =
    (Debug.hprint "bexpr_mapping:\n" KS.pr_bexpr_mapping ();
     Debug.hprint "instr_mapping:\n" KS.pr_instr_mapping ();
     Debug.hprint "loc_mapping:\n" KS.pr_loc_mapping ();
     Debug.hprint "KAT of procedures:"
       (pr_list ~sep:"\n" (fun (p, k) ->
            p ^ ": " ^ (K.pr_expr k))) kprog)
end
