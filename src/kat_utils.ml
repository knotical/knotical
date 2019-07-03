open Globals
open Lib
open Lib.Print
open Iast

module DB = Debug
module F = Formula

module S = Spl_syn
module SU = Spl_utils
module H = SU.H
module HE = SU.HElem
(* module KW = Symkat_wrapper *)

type kat =
  | Kcomp of kat * kat
  | Kunion of kat * kat
  | Kstar of kat
  | Ksym of string        (* non-test symbols *)
  | Ktrue
  | Kfalse
  | Kneg of bsym
  | Kbsym of bsym

and bsym =
  | Bsym of string
;;

type kat_symb_defn = (ident * statement)

type kat_formula = {
  k_defn_lst: kat_symb_defn list;
  k_expr: kat;
}

let rec pr_kat = function
  | Kcomp (k1, k2) -> "(" ^ (pr_kat k1) ^ " . " ^ (pr_kat k2) ^ ")"
  | Kunion (k1, k2) -> "(" ^  (pr_kat k1) ^ " + " ^ (pr_kat k2) ^ ")" 
  | Kstar k -> "(" ^ (pr_kat k) ^ ")*"
  | Ksym s -> s
  | Kbsym (Bsym s) -> "_" ^ s ^ "_"
  | Ktrue -> "true"
  | Kfalse -> "false"
  | Kneg (Bsym s) -> "_!" ^ s ^ "_"

let pr_kat_defn (id, stmt) =
  id ^ ": " ^ (pr_stmt stmt)

(* Transformation from spl programs to KATs *)
let kat_suffix = ref 0

let fresh_ksym () =
  fresh_var_new_name ~prefix:"k" ~suffix:kat_suffix ()

let fresh_bsym () =
  fresh_var_new_name ~prefix:"b" ~suffix:kat_suffix ()

let kat_of_spl_bexpr (tab: string H.t) (bexp: S.bexpr): kat =
  let rec helper (bexp: S.bexpr): kat =
    match bexp with
    | S.TRUE -> Ktrue
    | S.FALSE -> Kfalse
    | S.BRANDOM -> Kbsym (Bsym "rand")
    | S.CONS (l, op, r) ->
      let bsym =
        try
          H.find tab (HE.EXPR bexp)
        with _ ->
          let sym = fresh_bsym () in
          let () = H.add tab (HE.EXPR bexp) sym in
          sym
      in
      Kbsym (Bsym bsym)
    | S.AND (l, r) ->
      let kl = helper l in
      let kr = helper r in
      Kcomp (kl, kr)
    | S.OR (l, r) ->
      let kl = helper l in
      let kr = helper r in
      Kunion (kl, kr)
    | S.NOT b ->
      let kb = helper b in
      (match kb with
       | Kbsym bs -> Kneg bs
       | _ -> warning_unexpected "kat_of_spl_bexpr" (fun _ -> "") kb)
  in
  helper (SU.norm_neg bexp)

let rec kat_of_spl_instruction
    (tab: string H.t)
    (instr: S.instruction): kat =
  match instr with
  | S.SKIP -> Ksym "skip"
  | S.HALT -> Ksym "halt"
  | S.FAIL -> Ksym "fail"
  | S.ASSUME bexp -> kat_of_spl_bexpr tab bexp
  | S.ASSIGN _
  | S.CALL _ ->
    let ksym =
      try
        H.find tab (HE.INST instr)
      with _ ->
        let sym = fresh_ksym () in
        let () = H.add tab (HE.INST instr) sym in
        sym
    in
    Ksym ksym
  | S.IF (c, t) ->
    let kc = kat_of_spl_bexpr tab c in
    let knc = kat_of_spl_bexpr tab (S.NOT c) in
    let kt = kat_of_spl_block tab t in
    (* if c then t = c.t + !c *)
    Kunion (Kcomp (kc, kt), knc)
  | S.IFELSE (c, t, e) ->
    let kc = kat_of_spl_bexpr tab c in
    let knc = kat_of_spl_bexpr tab (S.NOT c) in
    let kt = kat_of_spl_block tab t in
    let ke = kat_of_spl_block tab e in
    (* if c then t else e = c.t + !c.e *)
    Kunion (Kcomp (kc, kt), Kcomp (knc, ke))
  | S.LOOP (c, b) ->
    let kc = kat_of_spl_bexpr tab c in
    let knc = kat_of_spl_bexpr tab (S.NOT c) in
    let kb = kat_of_spl_block tab b in
    (* while c do b = (c.b)*!c *)
    Kcomp (Kstar (Kcomp (kc, kb)), knc)

and kat_of_spl_instr (tab: string H.t) (instr: S.instr): kat =
  kat_of_spl_instruction tab instr.S.instruction

and kat_of_spl_block (tab: string H.t) (blk: S.block): kat =
  let rec helper instrs = 
    match instrs with
    | [] -> kat_of_spl_instruction tab S.SKIP
    | [i] -> kat_of_spl_instr tab i
    | i::is -> Kcomp (kat_of_spl_instr tab i, helper is)
  in
  helper blk.instrs

let kat_of_proc (proc: S.procedure): kat =
  let tab = H.create 50 in
  kat_of_spl_block tab proc.S.pcode

let kat_of_prog (prog: S.program): kat list =
  List.map kat_of_proc prog.S.procedures

module Kat = struct
  type t = kat

  let mk_true () = Ktrue

  let print k = pr_kat k
end;;

let rec norm_kat k =
    match k with
     | Kcomp (k1, k2) ->
            (match k1 with
             | Kcomp (k1_1, k1_2) ->
                    (match k2 with
                     | Kcomp (k2_1, k2_2) -> Kcomp (norm_kat k1, norm_kat k2)
                     | Kunion (k2_1, k2_2) ->
                            let norm_k1 = Kcomp (norm_kat k1, norm_kat k2_1) in
                            let norm_k2 = Kcomp (norm_kat k1, norm_kat k2_2) in
                            Kunion (norm_k1, norm_k2)
                     | Kstar ks -> Kcomp (norm_kat k1, Kstar (norm_kat ks))
                     | Ksym s -> Kcomp (norm_kat k1, Ksym s)
                     | Kbsym (Bsym s) -> Kcomp (norm_kat k1, Kbsym (Bsym s))
                     | Ktrue -> Kcomp (norm_kat k1, Ktrue)
                     | Kfalse -> Kcomp (norm_kat k1, Kfalse)
                     | Kneg (Bsym s) -> Kcomp (norm_kat k1, Kneg (Bsym s)))
             | Kunion (k1_1, k1_2) ->
                    (match k2 with
                     | Kcomp (k2_1, k2_2) ->
                             let norm_k1 = Kcomp (norm_kat k1_1, norm_kat k2) in
                             let norm_k2 = Kcomp (norm_kat k1_2, norm_kat k2) in
                             Kunion (norm_k1, norm_k2)
                     | Kunion (k2_1, k2_2) ->
                            let norm_k1_1 = Kcomp (norm_kat k1_1, norm_kat k2_1) in
                            let norm_k1_2 = Kcomp (norm_kat k1_1, norm_kat k2_2) in
                            let norm_k1 = Kunion (norm_k1_1, norm_k1_2) in
                            let norm_k2_1 = Kcomp (norm_kat k1_2, norm_kat k2_1) in
                            let norm_k2_2 = Kcomp (norm_kat k1_2, norm_kat k2_2) in
                            let norm_k2 = Kunion (norm_k2_1, norm_k2_2) in
                            Kunion (norm_k1, norm_k2)
                     | Kstar ks ->
                             Kcomp (norm_kat k1, norm_kat k2)
                     | Ksym s -> 
                             let norm_k1 = Kcomp (norm_kat k1_1, Ksym s) in
                             let norm_k2 = Kcomp (norm_kat k1_2, Ksym s) in
                             Kunion (norm_k1, norm_k2)
                     | Kbsym (Bsym s) ->
                             let norm_k1 = Kcomp (norm_kat k1_1, Kbsym (Bsym s)) in
                             let norm_k2 = Kcomp (norm_kat k1_2, Kbsym (Bsym s)) in
                             Kunion (norm_k1, norm_k2)
                     | Ktrue -> Kcomp (norm_kat k1, Ktrue)
                     | Kfalse -> Kcomp (norm_kat k1, Kfalse)
                     | Kneg (Bsym s) -> Kcomp (norm_kat k1, Kneg (Bsym s)))
             | Kstar ks -> Kcomp (norm_kat k1, norm_kat k2)
             | Ksym s -> Kcomp (Ksym s, norm_kat k2)
             | Kbsym (Bsym s) -> Kcomp (Kbsym (Bsym s), norm_kat k2)
             | Ktrue -> Kcomp (Ktrue, norm_kat k2)
             | Kfalse -> Kcomp (Kfalse, norm_kat k2)
             | Kneg (Bsym s) -> Kcomp (Kneg (Bsym s), norm_kat k2)
             )
    | Kunion (k1, k2) -> Kunion (norm_kat k1, norm_kat k2)
    | Kstar k1 -> Kstar (norm_kat k1)
    | Ksym s -> k 
    | Kbsym (Bsym s) -> k 
    | Ktrue -> k 
    | Kfalse -> k
    | Kneg (Bsym s) -> k


(* let run () =
 *   (\* test code here *\)
 *   let k = Kcomp ((Kunion (Ksym "p", Ksym "q")), Kstar (Ksym "r")) in
 *   let () = print_endline (Kat.print k) in
 *   let var_x = Apron.Var.of_string "x" in
 *   let const_1 = Apron.Scalar.of_int 1 in
 *   let e1 = Apron.Texpr1.Binop(Apron.Texpr1.Add,
 *                               Apron.Texpr1.Var var_x,
 *                               Apron.Texpr1.Cst (Apron.Coeff.Scalar const_1),
 *                               Apron.Texpr1.Int,
 *                               Apron.Texpr1.Rnd) in
 *   let e2 = Apron.Texpr1.Binop(Apron.Texpr1.Add,
 *                               Apron.Texpr1.Var var_x,
 *                               Apron.Texpr1.Cst (Apron.Coeff.Scalar const_1),
 *                               Apron.Texpr1.Int,
 *                               Apron.Texpr1.Rnd) in
 *   let a1 = S.ASSIGN (var_x, e1) in
 *   let a2 = S.ASSIGN (var_x, e2) in
 *   let i1 = HE.INST a1 in
 *   let i2 = HE.INST a2 in
 *   let () = print_endline (string_of_bool (a1 = a2)) in
 *   let () = print_endline (string_of_bool (SU.eq_instruction a1 a2)) in
 *   let () = print_endline (string_of_bool (HE.equal i1 i2)) in
 *   let () = print_endline (string_of_int (HE.hash i1)) in
 *   let () = print_endline (string_of_int (HE.hash i2)) in
 *   let tab = H.create 10 in
 *   let () = H.add tab i1 "i1" in
 *   let () = H.add tab i2 "i2" in
 *   let l1 = H.find tab i1 in
 *   let l2 = H.find tab i2 in
 *   let () = print_endline l1 in
 *   let () = print_endline l2 in
 * 
 *   () *)
