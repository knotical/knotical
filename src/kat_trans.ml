open Globals
open Lib.Print

module H = Extlib.ExtHashtbl.Hashtbl

module SL = Spl_lbl
module B = Boolexpr
module S = Spl_syn
module SU = Spl_utils

type 'a iproc_output =
  (S.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output

module type KSig =
sig
  type key
  type var
  type sym
  type test
  type expr
  type store

  val sym_of_key: key -> sym
  val sym_of_var: var -> sym
  val key_of_sym: sym -> key
  val var_of_sym: sym -> var

  val key_of_brandom: key
  val var_of_spl_halt: var
  val var_of_spl_fail: var

  val mk_key_sym: unit -> key
  val mk_var_sym: string -> var

  val mk_top: test
  val mk_bot: test
  val mk_neg: test -> test
  val mk_conj: test -> test -> test
  val mk_disj: test -> test -> test
  val mk_prd: key -> test

  val mk_tst: test -> expr
  val mk_var: var -> expr
  val mk_dot: expr -> expr -> expr
  val mk_pls: expr -> expr -> expr
  val mk_str: expr -> expr

  val is_bot_expr: expr -> bool
  val eq_sym: sym -> sym -> bool

  val backup: unit -> store
  val restore: store -> unit

  val pr_key: key -> string
  val pr_var: var -> string
  val pr_sym: sym -> string
  val pr_test: test -> string
  val pr_expr: expr -> string
end

module type KSym = functor (K: KSig) ->
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
  val get_symtab: unit -> symtab

  val pr_symtab: symtab -> string
  val pr_bexpr_mapping: unit -> string
  val pr_instr_mapping: unit -> string
  val pr_loc_mapping: unit -> string
end

module type KTrans = functor (K: KSig) ->
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

  val spl_cons_of_key: ?symtbl:(symtab option) ->
    key -> (S.point list * S.cons) option
  val spl_instr_of_var: ?symtbl:(symtab option) ->
    var -> (S.point list * S.instruction) option
  val spl_cons_of_sym: sym -> (S.point list * S.cons) option
  val spl_instr_of_sym: sym -> (S.point list * S.instruction) option

  val rename_var: var -> var
  val rename_key: key -> key
  val wrap: (unit -> 'a) -> 'a

  val get_symtab: unit -> symtab
  val pr_symtab: symtab -> string

  val print_kprog: (ident * expr) list -> unit
end

module MakeTrans (KSym: KSym): KTrans = functor (K: KSig) ->
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
    (fp: 'a iproc_output)
    (pt: S.point)
    (instr: S.instruction): expr =
    match instr with
    | S.SKIP
    | S.ASSUME _ -> K.mk_tst K.mk_top
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
      let labeled_c = SL.bexpr_of_spl (lcons_of_scons b.S.bpoint) c in
      let () = Debug.dhprint "labeled_c: "
          (SL.pr_bexpr (SL.pr_lcons K.pr_key SU.pr_cons)) labeled_c in
      let neg_labeled_c = SL.NOT labeled_c in

      let ctx = Iproc.get_context fp pt in
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

      let kb = kat_of_spl_block fp b in
      (* while c do b = (c.b)*!c *)
      K.mk_dot (K.mk_str (K.mk_dot (K.mk_tst kc) kb)) (K.mk_tst feasible_knc)

  and kat_of_spl_instr
      (fp: 'a iproc_output)
      (instr: S.instr): expr =
    if Iproc.is_bottom_abs fp instr.S.ipoint then
      K.mk_tst K.mk_bot
    else
      kat_of_spl_instruction fp instr.S.ipoint instr.S.instruction

  and kat_of_spl_block
      (fp: 'a iproc_output)
      (blk: S.block): expr =
    let pt = blk.S.bpoint in
    let () = Debug.dhprint "pt: " SU.pr_point pt in
    let () = Debug.dhprint "abs: " (Iproc.pr_abs pt) fp in
    if Iproc.is_bottom_abs fp pt then
      K.mk_tst K.mk_bot
    else
      let rec helper instrs = 
        match instrs with
        | [] -> kat_of_spl_instruction fp pt S.SKIP
        | [i] -> kat_of_spl_instr fp i
        | i::is -> K.mk_dot (kat_of_spl_instr fp i) (helper is)
      in
      helper blk.instrs

  let kat_of_proc
      (fp: 'a iproc_output)
      (proc: S.procedure): ident * expr =
    let ke = kat_of_spl_block fp proc.S.pcode in
    let pname =
      if String.length proc.S.pname == 0
      then "main" else proc.S.pname in
    (pname, ke)

  let kat_of_prog (prog: S.program): (ident * expr) list =
    try
      let man = Polka.manager_alloc_loose () in
      let fp = Iproc.analyze_forward man prog in
      let () = Debug.dhprint "iproc: " (Iproc.pr_output prog) fp in 
      let pk_list = List.map (kat_of_proc fp) prog.S.procedures in
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

  let spl_cons_of_key = KS.spl_cons_of_key

  let spl_instr_of_var = KS.spl_instr_of_var

  let spl_cons_of_sym = KS.spl_cons_of_sym

  let spl_instr_of_sym = KS.spl_instr_of_sym

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


