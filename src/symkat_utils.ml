open Globals
open Lib
open Lib.Print
open Iast

module H = Extlib.ExtHashtbl.Hashtbl
module Enum = Extlib.Enum

module S = Spl_syn
module K = Kat

module DB = Debug
module SU = Spl_utils

module KL = Kat_lbl
module KT = Kat_trans

(* Printing *)
let pr_test (f: K.test) =
  pr_to_string K.print_test f

let pr_expr (e: K.expr) =
  pr_to_string K.print_expr e

(* let pr_ctx = pr_to_string Apron.Abstract1.print *)

let pr_var = pr_char

let pr_key = pr_char

let pr_gstring (gs: K.gstring): string =
  let pr_list = pr_list ~obrace:"[" ~cbrace:"]" in
  let pr_atom atom =
    "atom: " ^
    (pr_list (pr_pair pr_key pr_bool) atom) in
  let pr_gstring_ gs_=
    "gstring: " ^
    (pr_list (pr_pair pr_var pr_atom) gs_) in
  pr_pair pr_atom pr_gstring_ gs

let pr_hypo (l, _, r) =
  (pr_expr l) ^ "=" ^ (pr_expr r)

let pr_hypos (hypos: Hypotheses.t) =
  pr_list ~obrace:"{" ~cbrace:"}" pr_hypo hypos

let pr_hypos_tex (hypos: Hypotheses.t) =
  pr_list ~obrace:"\\{" ~cbrace:"\\}" pr_hypo hypos

(* Utils *)
let is_bot_expr (e: K.expr) =
  match e with
  | K.Tst K.Bot -> true
  | _ -> false

let is_top_expr (e: K.expr) =
  match e with
  | K.Tst K.Top -> true
  | _ -> false

let is_top_test (t: K.test) =
  match t with
  | K.Top -> true
  | _ -> false

let is_bot_test (t: K.test) =
  match t with
  | K.Bot -> true
  | _ -> false

let eq_var (v1: K.var) (v2: K.var) =
  Char.equal v1 v2

let eq_key (k1: Bdd.key) (k2: Bdd.key) =
  Char.equal k1 k2

let eq_kat_expr (axioms: Hypotheses.t)
    (k1: K.expr) (k2: K.expr): bool =
  let _, diff = Symkat.compare ~hyps:axioms k1 k2 in
  match diff with
  | `E -> true
  | _ -> false

let keys_of_value (tab: ('a, 'b) H.t) (value: 'b): 'a list =
  let kv_pairs = H.enum tab in
  Extlib.Enum.fold (fun ks (k, s) ->
      if Char.equal s value then ks @ [k]
      else ks) [] kv_pairs

(* Translation from spl programs to SymKAT formulas *)

let (bexpr_symb_mapping: (S.bexpr, char) H.t) = H.create 26

let (instr_symb_mapping: (S.instruction, char) H.t) = H.create 26

let (loc_symb_mapping: (S.point, char) H.t) = H.create 26

let pr_tab_symb_mapping pr_e pr_s tab =
  H.to_list tab
  |> List.map (fun (e, s) ->
      (pr_e e) ^ " -> " ^ (pr_s s))
  |> String.concat "\n"

module Sym =
struct
  type store = {
    s_avail_instr_symb: char BatSet.t;
    s_test_sym_code: int; }

  let init_test_symb_code = ((Char.code 'a') - 1)

  let test_symb_of_brandom = 'r'

  let instr_symb_code = ref ((Char.code 'A') - 1)

  let instr_symb_of_halt = 'H'

  let instr_symb_of_fail = 'F'

  let builtin_instr_symb =
    [ (instr_symb_of_halt, "halt");
      (instr_symb_of_fail, "fail") ]

  (* 'A'-'Z' *)
  let init_instr_symb =
    let a_to_z_set = 
      BatSet.of_array (
        Array.make 26 'A'
        |> Array.mapi (fun i c -> int_of_char c + i |> char_of_int)) in
    let builtin_set = BatSet.of_list (List.map fst builtin_instr_symb) in
    BatSet.diff a_to_z_set builtin_set

  let test_symb_code = ref init_test_symb_code

  let avail_instr_symb = ref init_instr_symb

  let reset () =
    (avail_instr_symb := init_instr_symb;
     test_symb_code := init_test_symb_code)

  let backup () =
    { s_avail_instr_symb = !avail_instr_symb;
      s_test_sym_code = !test_symb_code; }

  let restore store =
    (avail_instr_symb := store.s_avail_instr_symb;
     test_symb_code := store.s_test_sym_code)

  let update_avail_instr_symb symb =
    avail_instr_symb := BatSet.remove symb !avail_instr_symb

  let mk_test_symb () =
    let () = test_symb_code :=
        if !test_symb_code + 1 == Char.code test_symb_of_brandom then
          !test_symb_code + 2
        else
          !test_symb_code + 1 in
    Char.chr !test_symb_code

  let mk_instr_symb id =
    let cs = EString.to_list (String.uppercase_ascii id) in
    let symb =
      try List.find (fun c -> BatSet.mem c !avail_instr_symb) cs
      with _ ->
        BatSet.min_elt !avail_instr_symb
    in
    let () = update_avail_instr_symb symb in
    symb
end

module SK =
struct
  type key = Bdd.key
  type var = K.var
  type sym = char
  type test = K.test
  type expr = K.expr

  type store = Sym.store

  let sym_of_key k = k
  let sym_of_var v = v
  let key_of_sym s = s
  let var_of_sym s = s

  let key_of_brandom = Sym.test_symb_of_brandom
  let var_of_spl_halt = Sym.instr_symb_of_halt
  let var_of_spl_fail = Sym.instr_symb_of_fail

  let mk_key_sym = Sym.mk_test_symb
  let mk_var_sym = Sym.mk_instr_symb 

  let mk_top = K.Top
  let mk_bot = K.Bot
  let mk_neg t = K.Neg t
  let mk_conj l r = K.Cnj (l, r)
  let mk_disj l r = K.Dsj (l, r)
  let mk_prd k = K.Prd k

  let mk_tst t = K.Tst t
  let mk_var v = K.Var v
  let mk_dot l r = K.Dot (l, r)
  let mk_pls l r = K.Pls (l, r)
  let mk_str e = K.Str e

  let is_bot_expr e =
    match e with
    | K.Tst K.Bot -> true
    | _ -> false

  let eq_sym = Char.equal

  let backup = Sym.backup

  let restore = Sym.restore

  let pr_key = pr_char
  let pr_var = pr_char
  let pr_sym = pr_char
  let pr_test = pr_to_string K.print_test
  let pr_expr = pr_to_string K.print_expr
end

module SKSym: KT.KSym = functor (K: KT.KSig) ->
struct
  type store = {
    s_bcons_symb_mapping: (S.cons, K.key) H.t;
    s_instr_symb_mapping: (S.instruction, K.var) H.t; }

  type symtab = unit

  let (bcons_symb_mapping: (S.cons, K.key) H.t ref) = ref (H.create 26)

  let (instr_symb_mapping: (S.instruction, K.var) H.t ref) = ref (H.create 26)

  let backup () =
    { s_bcons_symb_mapping = H.copy !bcons_symb_mapping;
      s_instr_symb_mapping = H.copy !instr_symb_mapping }

  let restore store =
    (bcons_symb_mapping := store.s_bcons_symb_mapping;
     instr_symb_mapping := store.s_instr_symb_mapping)

  let key_of_spl_cons (pt: S.point) (cons: S.cons): K.key =
    match H.find_option !bcons_symb_mapping cons with
    | Some k -> k
    | None ->
      let nk = K.mk_key_sym () in
      let () = H.add !bcons_symb_mapping cons nk in
      nk

  let var_of_spl_instr (pt: S.point) (instr: S.instruction): K.var =
    match H.find_option !instr_symb_mapping instr with
    | Some v -> v
    | None ->
      let nv = match instr with
        | S.HALT -> K.var_of_spl_halt
        | S.FAIL -> K.var_of_spl_fail
        | S.ASSIGN (v, _) -> K.mk_var_sym (Apron.Var.to_string v)
        | S.CALL (_, id, _) -> K.mk_var_sym id
        | _ -> warning_unexpected "SKSym: var_of_spl_instr" SU.pr_instruction instr
      in
      let () = H.add !instr_symb_mapping instr nv in
      nv

  let spl_cons_of_key
      ?(symtbl=None)
      (k: K.key): (S.point list * S.cons) option =
    None

  let spl_instr_of_var
      ?(symtbl=None)
      (v: K.var): (S.point list * S.instruction) option =
    None

  let spl_cons_of_sym (k: K.sym): (S.point list * S.cons) option =
    None

  let spl_instr_of_sym (v: K.sym): (S.point list * S.instruction) option =
    None

  let rename_var (v: K.var) = v

  let rename_key (k: K.key) = k

  let get_symtab () = ()

  let pr_symtab s = "No symtab"

  let pr_bexpr_mapping () =
    pr_tab_symb_mapping SU.pr_cons K.pr_key !bcons_symb_mapping

  let pr_instr_mapping () =
    pr_tab_symb_mapping SU.pr_instruction K.pr_var !instr_symb_mapping

  let pr_loc_mapping () = "No location mapping"
end

module SKTrans = KT.MakeTrans (SKSym) (SK)

let skat_of_prog (prog: S.program): (ident * K.expr) list =
  SKTrans.kat_of_prog prog

module LInt: KL.Label =
struct
  type t = int

  let dummy_label = 0

  let ilabel = ref dummy_label
 
  let get_label () =
   let () = ilabel := !ilabel + 1 in
   !ilabel

  let get_dummy_label () = dummy_label

  let is_dummy_label l = l == dummy_label

  let eq = (==)

  let string_of = pr_int
end

module LK = functor (L: KL.Label) ->
struct
  module V = KL.LVar (L)
  module K = KL.LKey (L)
  module LK = KL.LK (V) (K)

  type test = LK.test
  type expr = LK.expr
  type key = K.t
  type var = V.t
  type sym = char

  type store = Sym.store

  let sym_of_key (_, k) = k
  let sym_of_var (_, v) = v
  let key_of_sym s = K.from_kat s
  let var_of_sym s = V.from_kat s

  let key_of_brandom = K.from_kat Sym.test_symb_of_brandom
  let var_of_spl_halt = V.from_kat Sym.instr_symb_of_halt
  let var_of_spl_fail = V.from_kat Sym.instr_symb_of_fail

  let mk_key_sym () = K.from_kat (Sym.mk_test_symb ())
  let mk_var_sym id = V.from_kat (Sym.mk_instr_symb id)

  let mk_top = LK.Top
  let mk_bot = LK.Bot
  let mk_neg t = LK.Neg t
  let mk_conj l r = LK.Cnj (l, r)
  let mk_disj l r = LK.Dsj (l, r)
  let mk_prd k = LK.Prd k

  let mk_tst t = LK.Tst t
  let mk_var v = LK.Var v
  let mk_dot l r = LK.Dot (l, r)
  let mk_pls l r = LK.Pls (l, r)
  let mk_str e = LK.Str e

  let is_bot_expr e =
    match e with
    | LK.Tst LK.Bot -> true
    | _ -> false

  let eq_sym = Char.equal

  let backup = Sym.backup

  let restore = Sym.restore

  let pr_key = K.string_of
  let pr_var = V.string_of
  let pr_sym = pr_char
  let pr_test = LK.pr_test
  let pr_expr = LK.pr_expr
end

module KMap = functor (K: KT.KSig) ->
struct
  type spl_stmt =
    | BCons of S.cons
    | Instr of S.instruction

  type k_elt =
    | Key of K.key
    | Var of K.var

  let pr_spl_stmt s =
    match s with
    | BCons c -> SU.pr_cons c
    | Instr i -> SU.pr_instruction i

  let pr_k_elt e =
    match e with
    | Key k -> K.pr_key k
    | Var v -> K.pr_var v
end

module LKSym = functor (L: KL.Label) -> functor (K: KT.KSig) ->
struct
  module M = KMap (K)

  type symtab = (M.k_elt, (S.point * M.spl_stmt)) H.t

  type store = {
    s_bcons_symb_mapping: (S.cons, K.sym) H.t;
    s_instr_symb_mapping: (S.instruction, K.sym) H.t;
    s_loc_lsymb_mapping: ((S.point * M.spl_stmt), M.k_elt) H.t;
    s_lsymb_loc_mapping: (M.k_elt, (S.point * M.spl_stmt)) H.t; }

  let (bcons_symb_mapping: (S.cons, K.sym) H.t ref) = ref (H.create 26)

  let (instr_symb_mapping: (S.instruction, K.sym) H.t ref) = ref (H.create 26)

  let (loc_lsymb_mapping: ((S.point * M.spl_stmt), M.k_elt) H.t ref) =
    ref (H.create 26)

  let (lsymb_loc_mapping: (M.k_elt, (S.point * M.spl_stmt)) H.t ref) =
    ref (H.create 26)

  let backup () =
    { s_bcons_symb_mapping = H.copy !bcons_symb_mapping;
      s_instr_symb_mapping = H.copy !instr_symb_mapping;
      s_loc_lsymb_mapping = H.copy !loc_lsymb_mapping;
      s_lsymb_loc_mapping = H.copy !lsymb_loc_mapping }

  let restore store =
    (bcons_symb_mapping := store.s_bcons_symb_mapping;
     instr_symb_mapping := store.s_instr_symb_mapping;
     loc_lsymb_mapping := store.s_loc_lsymb_mapping;
     lsymb_loc_mapping := store.s_lsymb_loc_mapping)

  let key_of_elt elt =
    match elt with
    | M.Key k -> k
    | M.Var v -> warning_unexpected "key_of_elt" K.pr_var v

  let var_of_elt elt =
    match elt with
    | M.Var v -> v
    | M.Key k -> warning_unexpected "key_of_elt" K.pr_key k

  let elt_of_sym (s: K.sym): M.k_elt option =
    let elts = H.keys !lsymb_loc_mapping in
    try
      let e = BatEnum.find (fun elt ->
          let se =
            match elt with
            | M.Key k -> K.sym_of_key k
            | M.Var v -> K.sym_of_var v in
          K.eq_sym s se) elts
      in Some e
    with _ -> None

  let key_of_spl_cons (pt: S.point) (cons: S.cons): K.key =
    match H.find_option !loc_lsymb_mapping (pt, M.BCons cons) with
    | Some elt -> key_of_elt elt
    | None ->
      let k = match H.find_option !bcons_symb_mapping cons with
        | Some s -> K.key_of_sym s
        | None ->
          let nk = K.mk_key_sym () in
          let () = H.add !bcons_symb_mapping cons (K.sym_of_key nk) in
          nk
      in
      (* let k = K.mk_key_sym () in *)
      let () = H.add !loc_lsymb_mapping (pt, M.BCons cons) (M.Key k) in
      let () = H.add !lsymb_loc_mapping (M.Key k) (pt, M.BCons cons) in
      k

  let var_of_spl_instr (pt: S.point) (instr: S.instruction): K.var =
    match H.find_option !loc_lsymb_mapping (pt, M.Instr instr) with
    | Some elt -> var_of_elt elt
    | None ->
      let v = match H.find_option !instr_symb_mapping instr with
        | Some s -> K.var_of_sym s
        | None ->
          let nv = match instr with
            | S.HALT -> K.var_of_spl_halt
            | S.FAIL -> K.var_of_spl_fail
            | S.ASSIGN (v, _) -> K.mk_var_sym (Apron.Var.to_string v)
            | S.CALL (_, id, _) -> K.mk_var_sym id
            | _ -> warning_unexpected "LKSym: var_of_spl_instr" SU.pr_instruction instr
          in
          let () = H.add !instr_symb_mapping instr (K.sym_of_var nv) in
          nv
      in
      let () = H.add !loc_lsymb_mapping (pt, M.Instr instr) (M.Var v) in
      let () = H.add !lsymb_loc_mapping (M.Var v) (pt, M.Instr instr) in
      v

  let rename_var (v: K.var): K.var =
    match H.find_option !lsymb_loc_mapping (M.Var v) with
    | None -> v
    | Some (pt, stmt) ->
      (match stmt with
       | M.BCons _ -> v
       | M.Instr instr ->
         let nv = match instr with
           | S.ASSIGN (v, _) -> K.mk_var_sym (Apron.Var.to_string v)
           | S.CALL (_, id, _) -> K.mk_var_sym id
           | _ -> v
         in
         let () = H.remove !lsymb_loc_mapping (M.Var v) in
         let () = H.add !lsymb_loc_mapping (M.Var nv) (pt, stmt) in
         let () = H.replace !loc_lsymb_mapping (pt, stmt) (M.Var nv) in
         nv)

  let rename_key (k: K.key): K.key =
    match H.find_option !lsymb_loc_mapping (M.Key k) with
    | None -> k
    | Some (pt, stmt) ->
      (match stmt with
       | M.Instr _ -> k
       | M.BCons cons ->
         let nk = K.mk_key_sym () in
         let () = H.remove !lsymb_loc_mapping (M.Key k) in
         let () = H.add !lsymb_loc_mapping (M.Key nk) (pt, stmt) in
         let () = H.replace !loc_lsymb_mapping (pt, stmt) (M.Key nk) in
         nk)

  let spl_cons_of_key
      ?(symtbl=None)
      (k: K.key): (S.point list * S.cons) option =
    let symtbl =
      match symtbl with
      | None -> !lsymb_loc_mapping
      | Some syms -> syms in
    match H.find_option symtbl (M.Key k) with
    | None -> None
    | Some (pt, stmt) ->
      (match stmt with
       | M.BCons c -> Some ([pt], c)
       | _ -> None)

  let spl_instr_of_var
      ?(symtbl=None)
      (v: K.var): (S.point list * S.instruction) option =
    let symtbl =
      match symtbl with
      | None -> !lsymb_loc_mapping
      | Some syms -> syms in
    match H.find_option symtbl (M.Var v) with
    | None -> None
    | Some (pt, stmt) ->
      (match stmt with
       | M.Instr i -> Some ([pt], i)
       | _ -> None)

  let spl_cons_of_sym (s: K.sym): (S.point list * S.cons) option =
    match elt_of_sym s with
    | Some (M.Key k) -> spl_cons_of_key k
    | _ -> None

  let spl_instr_of_sym (s: K.sym): (S.point list * S.instruction) option =
    match elt_of_sym s with
    | Some (M.Var v) -> spl_instr_of_var v
    | _ -> None

  let get_symtab () = H.copy !lsymb_loc_mapping

  let pr_elt e = M.pr_k_elt e

  let pr_spl_stmt s = M.pr_spl_stmt s

  let pr_symtab (symtbl: symtab) =
    pr_tab_symb_mapping pr_elt (pr_pair SU.pr_point pr_spl_stmt) symtbl

  let pr_bexpr_mapping () =
    pr_tab_symb_mapping SU.pr_cons K.pr_sym !bcons_symb_mapping

  let pr_instr_mapping () =
    pr_tab_symb_mapping SU.pr_instruction K.pr_sym !instr_symb_mapping

  let pr_loc_mapping () =
    pr_tab_symb_mapping (pr_pair SU.pr_point pr_spl_stmt) pr_elt !loc_lsymb_mapping 
end

module ILK = LK (LInt)
module ILKSym = LKSym (LInt)
module LKTrans = KT.MakeTrans (ILKSym) (ILK)

(* let lkat_of_prog (prog: S.program): (ident * ILK.expr) list =
 *   (\* let () = Sym.reset () in *\)
 *   LKTrans.kat_of_prog prog *)
