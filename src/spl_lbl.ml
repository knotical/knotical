open Lib
open Lib.Print

module S = Spl_syn
module B = Boolexpr
module K = Kat
module KL = Kat_lbl

type 'a label = (bool * 'a)

type ('a, 'cons) lcons = ('a label * 'cons)

type 'cons _bexpr =
  | TRUE
  | FALSE
  | BRANDOM
  | CONS of 'cons
  | AND of ('cons _bexpr) * ('cons _bexpr)
  | OR of ('cons _bexpr) * ('cons _bexpr)
  | NOT of ('cons _bexpr)

let pr_label pr_sym = pr_pair pr_bool pr_sym

let pr_lcons pr_sym pr_cons =
  pr_pair (pr_label pr_sym) pr_cons

let rec pr_bexpr pr_cons bexpr =
  let pr = pr_bexpr pr_cons in
  match bexpr with
  | TRUE -> "true"
  | FALSE -> "false"
  | BRANDOM -> "brandom"
  | CONS c -> pr_cons c
  | AND (l, r) ->
    "(" ^ (pr l) ^ " & " ^ (pr r) ^ ")"
  | OR (l, r) ->
    "(" ^ (pr l) ^ " | " ^ (pr r) ^ ")"
  | NOT e -> "!" ^ (pr e)

let negate_label (lbl: ('a label)): 'a label =
  let sign, sym = lbl in
  (not sign, sym)

let rec bexpr_of_spl
    (cons_of_spl: S.cons -> 'cons)
    (expr: S.bexpr)
  : 'cons _bexpr =
  let trans_f = bexpr_of_spl cons_of_spl in
  match expr with
  | S.TRUE -> TRUE
  | S.FALSE -> FALSE
  | S.BRANDOM -> BRANDOM
  | S.CONS c -> CONS (cons_of_spl c)
  | S.AND (l, r) -> AND (trans_f l, trans_f r)
  | S.OR (l, r) -> OR (trans_f l, trans_f r)
  | S.NOT e -> NOT (trans_f e)

let tcons_of_cons
    (trans_cons: 'cons -> Apron.Tcons1.t)
    (cons: ('a, 'cons) lcons)
  : ('a, Apron.Tcons1.t) lcons =
  let lbl, scons = cons in
  (lbl, trans_cons scons)

let negate_tcons
    (cons: ('a, Apron.Tcons1.t) lcons)
  : ('a, Apron.Tcons1.t) lcons =
  let lbl, tcons = cons in
  (negate_label lbl, Syn2equation.negate_tcons tcons)

let boolexpr_of_bexpr
    (trans_cons: 'cons -> Apron.Tcons1.t)
    (bexpr: ('a, 'cons) lcons _bexpr)
  : ('a, Apron.Tcons1.t) lcons array B.t =
  let cand t1 t2 = Boolexpr.make_conjunction (Array.append t1 t2) in
  let rec translate bexpr =
    match bexpr with
    | TRUE | BRANDOM -> Boolexpr.make_cst true
    | FALSE -> Boolexpr.make_cst false
    | CONS cons  ->
	    let tcons = tcons_of_cons trans_cons cons in
	    Boolexpr.make_conjunction [|tcons|]
    | AND (e1, e2) ->
	    Boolexpr.make_and ~cand (translate e1) (translate e2)
    | OR (e1, e2) ->
	    Boolexpr.make_or (translate e1) (translate e2)
    | NOT e ->
	    begin match e with
	      | FALSE | BRANDOM -> Boolexpr.make_cst true
	      | TRUE -> Boolexpr.make_cst false
	      | CONS cons ->
	        let tcons = tcons_of_cons trans_cons cons in
	        let tcons = negate_tcons tcons in
	        Boolexpr.make_conjunction [|tcons|]
	      | AND (e1, e2) ->
	        Boolexpr.make_or (translate (NOT e1)) (translate (NOT e2))
	      | OR (e1, e2) ->
	        Boolexpr.make_and ~cand
	          (translate (NOT e1)) (translate (NOT e2))
	      | NOT e -> translate e
	    end
  in
  translate bexpr

let earray_of_lcons_array env
    (arr_lcons: ('a, Apron.Tcons1.t) lcons array)
  : ('a label list * Apron.Tcons1.earray) =
  let arr_lbl, arr_cons = Array.to_list arr_lcons |> List.split in
  let earr_cons =
    let tcons = Array.of_list arr_cons in
    let () = assert (tcons <> [||]) in
    let res = Apron.Tcons1.array_make env (Array.length tcons) in
    let () = Array.iteri (fun i cons ->
        Apron.Tcons1.array_set res i cons) tcons in
    res
  in
  (arr_lbl, earr_cons)

