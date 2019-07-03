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

let pr_diff = function
  | `E -> "Eq"
  | `L _ -> "Lt"
  | `G gs -> "Gt: " ^ (pr_gstring gs)
  | `D (gs, gs') ->
    "Diff:\n" ^ (pr_gstring gs) ^ "\n" ^ (pr_gstring gs') ^ ")"

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

(* This module handles KAT symbols *)
module Sym =
struct
  type store = {
    s_avail_instr_sym: char BatSet.t;
    s_test_sym_code: int; }

  let init_test_sym_code = ((Char.code 'a') - 1)

  let test_sym_of_brandom = 'r'

  let init_instr_sym_code = ref ((Char.code 'A') - 1)

  let instr_sym_of_halt = 'H'

  let instr_sym_of_fail = 'F'

  let builtin_instr_sym =
    [ (instr_sym_of_halt, "halt");
      (instr_sym_of_fail, "fail") ]

  (* 'A'-'Z' *)
  let init_instr_sym =
    let a_to_z_set = 
      BatSet.of_array (
        Array.make 26 'A'
        |> Array.mapi (fun i c -> int_of_char c + i |> char_of_int)) in
    let builtin_set = BatSet.of_list (List.map fst builtin_instr_sym) in
    BatSet.diff a_to_z_set builtin_set

  let current_test_sym_code = ref init_test_sym_code

  let avail_instr_sym = ref init_instr_sym

  let reset () =
    (avail_instr_sym := init_instr_sym;
     current_test_sym_code := init_test_sym_code)

  let backup () =
    { s_avail_instr_sym = !avail_instr_sym;
      s_test_sym_code = !current_test_sym_code; }

  let restore store =
    (avail_instr_sym := store.s_avail_instr_sym;
     current_test_sym_code := store.s_test_sym_code)

  let update_avail_instr_sym sym =
    avail_instr_sym := BatSet.remove sym !avail_instr_sym

  let mk_test_sym () =
    let () =
      current_test_sym_code :=
        if !current_test_sym_code + 1 == Char.code test_sym_of_brandom then
          !current_test_sym_code + 2
        else
          !current_test_sym_code + 1 in
    Char.chr !current_test_sym_code

  let mk_instr_sym id =
    let cs = EString.to_list (String.uppercase_ascii id) in
    let sym =
      try List.find (fun c -> BatSet.mem c !avail_instr_sym) cs
      with _ ->
        BatSet.min_elt !avail_instr_sym
    in
    let () = update_avail_instr_sym sym in
    sym
end

(* Wrapper of Symkat with builtin symbols *)
(* Following the signature Kat_sig.K *)
module SK =
struct
  type key = Bdd.key
  type var = K.var
  type sym = char

  type test = K.test =
    | Dsj of test * test
    | Cnj of test * test
    | Neg of test
    | Top
    | Bot
    | Prd of key

  type expr =
    | Pls of expr * expr
    | Dot of expr * expr
    | Str of expr
    | Tst of test
    | Var of var

  type store = Sym.store

  type diff = Eq | Lt | Gt | Diff

  let sym_of_key k = k
  let sym_of_var v = v
  let key_of_sym s = s
  let var_of_sym s = s
  let key_of_string s = String.get s 0
  let var_of_string s = String.get s 0

  let key_of_brandom = Sym.test_sym_of_brandom
  let var_of_spl_halt = Sym.instr_sym_of_halt
  let var_of_spl_fail = Sym.instr_sym_of_fail

  let mk_key_sym = Sym.mk_test_sym
  let mk_var_sym = Sym.mk_instr_sym 

  let mk_top = Top
  let mk_bot = Bot
  let mk_neg t = match t with | Neg r -> r | _ -> Neg t
  let mk_conj l r = Cnj (l, r)
  let mk_disj l r = Dsj (l, r)
  let mk_prd k = Prd k

  let mk_tst t = Tst t
  let mk_var v = Var v
  let mk_dot l r = Dot (l, r)
  let mk_pls l r = Pls (l, r)
  let mk_str e = Str e

  let test_of_kat (t: K.test): test = t

  let rec expr_of_kat (e: K.expr): expr =
    match e with
    | K.Pls (l, r) -> Pls (expr_of_kat l, expr_of_kat r)
    | K.Dot (l, r) -> Dot (expr_of_kat l, expr_of_kat r)
    | K.Str s -> Str (expr_of_kat s)
    | K.Tst t -> Tst (test_of_kat t)
    | K.Var v -> Var v

  let kat_of_test (t: test) = t

  let rec kat_of_expr (e: expr) =
    match e with
    | Pls (l, r) -> K.Pls (kat_of_expr l, kat_of_expr r)
    | Dot (l, r) -> K.Dot (kat_of_expr l, kat_of_expr r)
    | Str s -> K.Str (kat_of_expr s)
    | Tst t -> K.Tst (kat_of_test t)
    | Var v -> K.Var v

  let pr_key = pr_char
  let pr_var = pr_char
  let pr_sym = pr_char
  let pr_test = pr_to_string K.print_test
  let pr_expr = pr_to_string (fun fmt e -> K.print_expr fmt (kat_of_expr e))

  let is_bot_expr e =
    match e with
    | Tst Bot -> true
    | _ -> false

  let eq_sym = Char.equal
  let eq_var = eq_var
  let eq_key = eq_key

  let cmp_key e f =
    Char.compare e f

  let cmp_expr (e: expr) (f: expr) =
    let _, kdiff = Symkat.compare ~hyps:[]
        (kat_of_expr e) (kat_of_expr f) in
    match kdiff with
    | `E -> Eq
    | `L _ -> Lt
    | `G _ -> Gt
    | _ -> Diff

  let eq_expr e f =
    match cmp_expr e f with
    | Eq -> true
    | _ -> false

  let backup = Sym.backup

  let restore = Sym.restore
end

(* Obsolete *)
module SKSym: KT.KSym = functor (K: Kat_sig.K) ->
struct
  type store = {
    s_bcons_sym_mapping: (S.cons, K.key) H.t;
    s_instr_sym_mapping: (S.instruction, K.var) H.t; }

  type symtab = unit

  let (bcons_sym_mapping: (S.cons, K.key) H.t ref) = ref (H.create 26)

  let (instr_sym_mapping: (S.instruction, K.var) H.t ref) = ref (H.create 26)

  let backup () =
    { s_bcons_sym_mapping = H.copy !bcons_sym_mapping;
      s_instr_sym_mapping = H.copy !instr_sym_mapping }

  let restore store =
    (bcons_sym_mapping := store.s_bcons_sym_mapping;
     instr_sym_mapping := store.s_instr_sym_mapping)

  let reset () =
    (H.clear !bcons_sym_mapping;
     H.clear !instr_sym_mapping)

  let key_of_spl_cons (pt: S.point) (cons: S.cons): K.key =
    match H.find_option !bcons_sym_mapping cons with
    | Some k -> k
    | None ->
      let nk = K.mk_key_sym () in
      let () = H.add !bcons_sym_mapping cons nk in
      nk

  let var_of_spl_instr (pt: S.point) (instr: S.instruction): K.var =
    match H.find_option !instr_sym_mapping instr with
    | Some v -> v
    | None ->
      let nv = match instr with
        | S.HALT -> K.var_of_spl_halt
        | S.FAIL -> K.var_of_spl_fail
        | S.ASSIGN (v, _) -> K.mk_var_sym (Apron.Var.to_string v)
        | S.CALL (_, id, _) -> K.mk_var_sym id
        | _ -> warning_unexpected "SKSym: var_of_spl_instr" SU.pr_instruction instr
      in
      let () = H.add !instr_sym_mapping instr nv in
      nv

  let spl_cons_of_key
      ?(symtbl=None)
      (k: K.key): (S.point list * S.cons) option =
    H.to_list !bcons_sym_mapping
    |> List.find_opt (fun (_, kc) -> K.eq_key k kc)
    |> fun opt -> (match opt with None -> None | Some (c, _) -> Some ([], c))

  let spl_instr_of_var
      ?(symtbl=None)
      (v: K.var): (S.point list * S.instruction) option =
    H.to_list !instr_sym_mapping
    |> List.find_opt (fun (_, vi) -> K.eq_var v vi)
    |> fun opt -> (match opt with None -> None | Some (i, _) -> Some ([], i))

  let spl_cons_of_sym (k: K.sym): (S.point list * S.cons) option =
    spl_cons_of_key (K.key_of_sym k)

  let spl_instr_of_sym (v: K.sym): (S.point list * S.instruction) option =
    spl_instr_of_var (K.var_of_sym v)

  let rename_var (v: K.var) = v

  let rename_key (k: K.key) = k

  let get_symtab () =
    failwith "get_symtab: No symtab implemented"

  let get_vars () =
    H.to_list !instr_sym_mapping |> List.map snd

  let get_keys () =
    H.to_list !bcons_sym_mapping |> List.map snd

  let get_syms () =
    (get_vars () |> List.map K.sym_of_var) @
    (get_keys () |> List.map K.sym_of_key)
    |> List.dedup K.eq_sym

  let pr_symtab s = "No symtab"

  let pr_bexpr_mapping () =
    pr_tab_symb_mapping SU.pr_cons K.pr_key !bcons_sym_mapping

  let pr_instr_mapping () =
    pr_tab_symb_mapping SU.pr_instruction K.pr_var !instr_sym_mapping

  let pr_loc_mapping () = "No location mapping"
end

(* Transformation from SK to SKSym *)
module SKTrans = KT.MakeTrans (SKSym) (SK)

let skat_of_prog (prog: S.program): (ident * SK.expr) list =
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

  let from_string = int_of_string
end

(* Labeled KAT *)
(* Following the signature Kat_sig.K *)
module LK = functor (L: KL.Label) ->
struct
  module V = KL.LVar (L)
  module K = KL.LKey (L)

  type key = K.t
  type var = V.t
  type sym = char

  type test =
    | Dsj of test * test
    | Cnj of test * test
    | Neg of test
    | Top
    | Bot
    | Prd of key

  type expr =
    | Pls of expr * expr
    | Dot of expr * expr
    | Str of expr
    | Tst of test
    | Var of var

  type diff = Eq | Lt | Gt | Diff

  type store = Sym.store

  let sym_of_key = K.to_kat
  let sym_of_var = V.to_kat
  let key_of_sym = K.from_kat
  let var_of_sym = V.from_kat
  let key_of_string = K.from_string
  let var_of_string = V.from_string

  let syms_of_test (ke: test): char list =
    let rec helper ke =
      match ke with
      | Dsj (l, r) -> (helper l) @ (helper r)
      | Cnj (l, r) -> (helper l) @ (helper r)
      | Neg e -> helper e
      | Top
      | Bot -> []
      | Prd k -> [sym_of_key k]
    in
    helper ke

  let syms_of_expr (ke: expr): char list =
    let rec helper ke =
    match ke with
    | Pls (l, r)
    | Dot (l, r) -> (helper l) @ (helper r)
    | Str e -> helper e
    | Tst e -> syms_of_test e
    | Var v -> [sym_of_var v]
    in
    helper ke

  let key_of_brandom = K.from_kat Sym.test_sym_of_brandom
  let var_of_spl_halt = V.from_kat Sym.instr_sym_of_halt
  let var_of_spl_fail = V.from_kat Sym.instr_sym_of_fail

  let mk_key_sym () = K.from_kat (Sym.mk_test_sym ())
  let mk_var_sym id = V.from_kat (Sym.mk_instr_sym id)

  let rec syn_eq_test l r =
    match l, r with
    | Top, Top
    | Bot, Bot -> true
    | Prd kl, Prd kr -> K.eq kl kr
    | Neg nl, Neg nr -> syn_eq_test nl nr
    | Cnj (ll, lr), Cnj (rl, rr) ->
      ((syn_eq_test ll rl) && (syn_eq_test lr rr)) ||
      ((syn_eq_test ll rr) && (syn_eq_test lr rl))
    | Dsj (ll, lr), Dsj (rl, rr) ->
      ((syn_eq_test ll rl) && (syn_eq_test lr rr)) ||
      ((syn_eq_test ll rr) && (syn_eq_test lr rl))
    | _ -> false

  let rec syn_eq_expr l r =
    match l, r with
    | Var vl, Var vr -> V.eq vl vr
    | Tst tl, Tst tr -> syn_eq_test tl tr
    | Str sl, Str sr -> syn_eq_expr sl sr
    | Dot (ll, lr), Dot (rl, rr) ->
      ((syn_eq_expr ll rl) && (syn_eq_expr lr rr)) ||
      ((syn_eq_expr ll rr) && (syn_eq_expr lr rl))
    | Pls (ll, lr), Pls (rl, rr) ->
      ((syn_eq_expr ll rl) && (syn_eq_expr lr rr)) ||
      ((syn_eq_expr ll rr) && (syn_eq_expr lr rl))
    | _ -> false

  let mk_top = Top

  let mk_bot = Bot

  let mk_neg t =
    match t with
    | Neg r -> r
    | _ -> Neg t

  let mk_conj l r =
    match l, r with
    | Top, _ -> r
    | _, Top -> l
    | Bot, _
    | _, Bot -> mk_bot
    | _ when syn_eq_test l r -> l
    | _ -> Cnj (l, r)

  let rec mk_disj l r =
    match l, r with
    | Top, _
    | _, Top -> mk_top
    | Bot, _ -> r
    | _, Bot -> l
    | l, Neg nr when syn_eq_test l nr -> mk_top
    | Neg nl, r when syn_eq_test nl r -> mk_top
    | Cnj (ll, lr), Cnj (rl, rr) when syn_eq_test ll rl ->
      mk_conj ll (mk_disj lr rr)
    | Cnj (ll, lr), Cnj (rl, rr) when syn_eq_test ll rr ->
      mk_conj ll (mk_disj lr rl)
    | Cnj (ll, lr), Cnj (rl, rr) when syn_eq_test lr rl ->
      mk_conj lr (mk_disj ll rr)
    | Cnj (ll, lr), Cnj (rl, rr) when syn_eq_test lr rr ->
      mk_conj lr (mk_disj ll rl)
    | Cnj (ll, lr), _ when (syn_eq_test ll r) || (syn_eq_test lr r) -> r
    | _, Cnj (rl, rr) when (syn_eq_test l rl) || (syn_eq_test l rr) -> l
    | Dsj (ll, lr), Cnj (rl, rr) when
        (syn_eq_test ll rl) || (syn_eq_test ll rr) ||
        (syn_eq_test lr rl) || (syn_eq_test lr rr) ->
      l
    | _ when syn_eq_test l r -> l
    | _ -> Dsj (l, r)

  let mk_prd k = Prd k

  let mk_tst t = Tst t

  let mk_var v = Var v

  let mk_dot l r =
    match l, r with
    | Tst Top, _ -> r
    | _, Tst Top -> l
    | Tst Bot, _
    | _, Tst Bot -> mk_tst mk_bot
    | Tst lt, Tst rt -> mk_tst (mk_conj lt rt)
    | _ -> Dot (l, r)

  let rec mk_pls l r =
    match l, r with
    | Tst Bot, _ -> r
    | _, Tst Bot -> l
    | Tst lt, Tst rt -> mk_tst (mk_disj lt rt)
    | Dot (ll, lr), Dot (rl, rr) when syn_eq_expr lr rr ->
      mk_dot (mk_pls ll rl) lr
    | Dot (ll, lr), Dot (rl, rr) when syn_eq_expr ll rl ->
      mk_dot ll (mk_pls lr rr)
    | Dot (Tst _, lr), _ when syn_eq_expr lr r -> r
    | _, Dot (Tst _, rr) when syn_eq_expr l rr -> l
    | _ when syn_eq_expr l r -> l
    | _ -> Pls (l, r)

  let mk_str e =
    match e with
    | Tst Top -> Tst Top
    | Tst Bot -> Tst Bot
    | _ -> Str e

  let rec test_norm_neg (t: test): test =
    match t with
    | Dsj (l, r) -> Dsj (test_norm_neg l, test_norm_neg r)
    | Cnj (l, r) -> Cnj (test_norm_neg l, test_norm_neg r)
    | Neg e ->
      (match e with
       | Dsj (l, r) -> Cnj (test_norm_neg (Neg l),
                            test_norm_neg (Neg r))
       | Cnj (l, r) -> Dsj (test_norm_neg (Neg l),
                            test_norm_neg (Neg r))
       | Neg f -> test_norm_neg f
       | Top -> Bot
       | Bot -> Top
       | Prd k -> t)
    | _ -> t

  let rec kat_of_test (t: test): Kat.test =
    match t with
    | Dsj (k, m) -> Kat.Dsj (kat_of_test k, kat_of_test m)
    | Cnj (k, m) -> Kat.Cnj (kat_of_test k, kat_of_test m)
    | Neg k -> Kat.Neg (kat_of_test k)
    | Top -> Kat.Top
    | Bot -> Kat.Bot
    | Prd k -> Kat.Prd (K.to_kat k)

  let rec kat_of_expr (e: expr): Kat.expr =
    match e with
    | Pls (k, m) -> Kat.Pls (kat_of_expr k, kat_of_expr m)
    | Dot (k, m) -> Kat.Dot (kat_of_expr k, kat_of_expr m)
    | Str k -> Kat.Str (kat_of_expr k)
    | Tst k -> Kat.Tst (kat_of_test k)
    | Var v -> Kat.Var (V.to_kat v)

  let rec test_of_kat (t: Kat.test): test =
    match t with
    | Kat.Dsj (k, m) -> Dsj (test_of_kat k, test_of_kat m)
    | Kat.Cnj (k, m) -> Cnj (test_of_kat k, test_of_kat m)
    | Kat.Neg k -> Neg (test_of_kat k)
    | Kat.Top -> Top
    | Kat.Bot -> Bot
    | Kat.Prd k -> Prd (K.from_kat k)

  let rec expr_of_kat (e: Kat.expr): expr =
    match e with
    | Kat.Pls (k, m) -> Pls (expr_of_kat k, expr_of_kat m)
    | Kat.Dot (k, m) -> Dot (expr_of_kat k, expr_of_kat m)
    | Kat.Str k -> Str (expr_of_kat k)
    | Kat.Tst k -> Tst (test_of_kat k)
    | Kat.Var v -> Var (V.from_kat v)

  let is_bot_expr e =
    match e with
    | Tst Bot -> true
    | _ -> false

  let is_top = function Top -> true | _ -> false

  let is_tot_expr e =
    match e with
    | Tst Top -> true
    | _ -> false

  let eq_sym = Char.equal
  let eq_var = V.eq
  let eq_key = K.eq

  let cmp_key = K.cmp

  let cmp_expr e f =
    let _, kdiff = Symkat.compare ~hyps:[]
        (kat_of_expr e) (kat_of_expr f) in
    match kdiff with
    | `E -> Eq
    | `L _ -> Lt
    | `G _ -> Gt
    | _ -> Diff

  let eq_expr e f =
    match cmp_expr e f with
    | Eq -> true
    | _ -> false

  let backup = Sym.backup

  let restore = Sym.restore

  let pr_key = K.string_of
  let pr_var = V.string_of
  let pr_sym = pr_char

  let rec pr_test (t: test): string =
    match t with
    | Dsj (l, r) -> "(" ^ (pr_test l) ^ " | " ^ (pr_test r) ^ ")"
    | Cnj (l, r) -> "(" ^ (pr_test l) ^ " & " ^ (pr_test r) ^ ")"
    | Neg e -> "!" ^ (pr_test e)
    | Top -> "1"
    | Bot -> "0"
    | Prd k -> K.string_of k

  let rec pr_expr (e: expr): string =
    match e with
    | Pls (l, r) -> "(" ^ (pr_expr l) ^ " + " ^ (pr_expr r) ^ ")"
    | Dot (l, r) -> (pr_expr l) ^ "." ^ (pr_expr r)
    | Str e -> "(" ^ (pr_expr e) ^ ")*"
    | Tst t -> pr_test t
    | Var v -> V.string_of v

  let rec pr_test_tex (t: test): string =
    match t with
    | Dsj (l, r) -> "(" ^ (pr_test_tex l) ^ " \\vee " ^ (pr_test_tex r) ^ ")"
    | Cnj (l, r) -> "(" ^ (pr_test_tex l) ^ " \\wedge " ^ (pr_test_tex r) ^ ")"
    | Neg e -> "\\neg " ^ (pr_test_tex e)
    | Top -> "1"
    | Bot -> "0"
    | Prd k -> K.string_of k

  let rec pr_expr_tex (e: expr) (axl: V.t -> string): string =
    match e with
    | Pls (l, r) -> "(" ^ (pr_expr_tex l axl) ^ " + " ^ (pr_expr_tex r axl) ^ ")"
    | Dot (l, r) -> (pr_expr_tex l axl) ^ "\\!\\cdot\\!" ^ (pr_expr_tex r axl)
    | Str e -> "(" ^ (pr_expr_tex e axl) ^ ")*"
    | Tst t -> pr_test_tex t
    | Var v -> (* V.string_of v *) (axl v)
end

(* Unified mapping betwen program instructions and conditions
   to KAT keys and vars *)
module KMap = functor (K: Kat_sig.K) ->
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

module LKSym = functor (L: KL.Label) -> functor (K: Kat_sig.K) ->
struct
  module M = KMap (K)

  type symtab = (M.k_elt, (S.point * M.spl_stmt)) H.t

  type store = {
    s_bcons_sym_mapping: (S.cons, K.sym) H.t;
    s_instr_sym_mapping: (S.instruction, K.sym) H.t;
    s_loc_lsym_mapping: ((S.point * M.spl_stmt), M.k_elt) H.t;
    s_lsym_loc_mapping: (M.k_elt, (S.point * M.spl_stmt)) H.t; }

  let (bcons_sym_mapping: (S.cons, K.sym) H.t ref) = ref (H.create 26)

  let (instr_sym_mapping: (S.instruction, K.sym) H.t ref) = ref (H.create 26)

  let (loc_lsym_mapping: ((S.point * M.spl_stmt), M.k_elt) H.t ref) =
    ref (H.create 26)

  let (lsym_loc_mapping: (M.k_elt, (S.point * M.spl_stmt)) H.t ref) =
    ref (H.create 26)

  let backup () =
    { s_bcons_sym_mapping = H.copy !bcons_sym_mapping;
      s_instr_sym_mapping = H.copy !instr_sym_mapping;
      s_loc_lsym_mapping = H.copy !loc_lsym_mapping;
      s_lsym_loc_mapping = H.copy !lsym_loc_mapping }

  let restore store =
    (bcons_sym_mapping := store.s_bcons_sym_mapping;
     instr_sym_mapping := store.s_instr_sym_mapping;
     loc_lsym_mapping := store.s_loc_lsym_mapping;
     lsym_loc_mapping := store.s_lsym_loc_mapping)

  let reset () =
    (H.clear !bcons_sym_mapping;
     H.clear !instr_sym_mapping;
     H.clear !loc_lsym_mapping;
     H.clear !lsym_loc_mapping)

  let key_of_elt elt =
    match elt with
    | M.Key k -> k
    | M.Var v -> warning_unexpected "key_of_elt" K.pr_var v

  let var_of_elt elt =
    match elt with
    | M.Var v -> v
    | M.Key k -> warning_unexpected "var_of_elt" K.pr_key k

  let elt_of_sym (s: K.sym): M.k_elt option =
    let elts = H.keys !lsym_loc_mapping in
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
    match H.find_option !loc_lsym_mapping (pt, M.BCons cons) with
    | Some elt -> key_of_elt elt
    | None ->
      let k = match H.find_option !bcons_sym_mapping cons with
        | Some s -> K.key_of_sym s
        | None ->
          let nk = K.mk_key_sym () in
          let () = H.add !bcons_sym_mapping cons (K.sym_of_key nk) in
          nk
      in
      (* let k = K.mk_key_sym () in *)
      let () = H.add !loc_lsym_mapping (pt, M.BCons cons) (M.Key k) in
      let () = H.add !lsym_loc_mapping (M.Key k) (pt, M.BCons cons) in
      k

  let var_of_spl_instr (pt: S.point) (instr: S.instruction): K.var =
    match H.find_option !loc_lsym_mapping (pt, M.Instr instr) with
    | Some elt -> var_of_elt elt
    | None ->
      let v = match H.find_option !instr_sym_mapping instr with
        | Some s -> K.var_of_sym s
        | None ->
          let nv = match instr with
            | S.HALT -> K.var_of_spl_halt
            | S.FAIL -> K.var_of_spl_fail
            | S.ASSIGN (v, _) -> K.mk_var_sym (Apron.Var.to_string v)
            | S.CALL (_, id, _) -> K.mk_var_sym id
            | _ -> warning_unexpected "LKSym: var_of_spl_instr" SU.pr_instruction instr
          in
          let () = H.add !instr_sym_mapping instr (K.sym_of_var nv) in
          nv
      in
      let () = H.add !loc_lsym_mapping (pt, M.Instr instr) (M.Var v) in
      let () = H.add !lsym_loc_mapping (M.Var v) (pt, M.Instr instr) in
      v

  let rename_var (v: K.var): K.var =
    match H.find_option !lsym_loc_mapping (M.Var v) with
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
         let () = H.remove !lsym_loc_mapping (M.Var v) in
         let () = H.add !lsym_loc_mapping (M.Var nv) (pt, stmt) in
         let () = H.replace !loc_lsym_mapping (pt, stmt) (M.Var nv) in
         nv)

  let rename_key (k: K.key): K.key =
    match H.find_option !lsym_loc_mapping (M.Key k) with
    | None -> k
    | Some (pt, stmt) ->
      (match stmt with
       | M.Instr _ -> k
       | M.BCons cons ->
         let nk = K.mk_key_sym () in
         let () = H.remove !lsym_loc_mapping (M.Key k) in
         let () = H.add !lsym_loc_mapping (M.Key nk) (pt, stmt) in
         let () = H.replace !loc_lsym_mapping (pt, stmt) (M.Key nk) in
         nk)

  let spl_cons_of_key
      ?(symtbl=None)
      (k: K.key): (S.point list * S.cons) option =
    let symtbl =
      match symtbl with
      | None -> !lsym_loc_mapping
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
      | None -> !lsym_loc_mapping
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

  let get_symtab () = H.copy !lsym_loc_mapping

  let get_vars () =
    H.to_list !lsym_loc_mapping
    |> List.map fst
    |> List.fold_left (fun a s ->
        try a @ [var_of_elt s]
        with _ -> a) []

  let get_keys () =
    H.to_list !lsym_loc_mapping
    |> List.map fst
    |> List.fold_left (fun a s ->
        try a @ [key_of_elt s]
        with _ -> a) []

  let get_syms () =
    (H.to_list !bcons_sym_mapping |> List.map snd) @
    (H.to_list !instr_sym_mapping |> List.map snd)
    |> List.dedup K.eq_sym

  let pr_elt e = M.pr_k_elt e

  let pr_spl_stmt s = M.pr_spl_stmt s

  let pr_symtab (symtbl: symtab) =
    pr_tab_symb_mapping pr_elt (pr_pair SU.pr_point pr_spl_stmt) symtbl

  let pr_bexpr_mapping () =
    pr_tab_symb_mapping SU.pr_cons K.pr_sym !bcons_sym_mapping

  let pr_instr_mapping () =
    pr_tab_symb_mapping SU.pr_instruction K.pr_sym !instr_sym_mapping

  let pr_loc_mapping () =
    pr_tab_symb_mapping (pr_pair SU.pr_point pr_spl_stmt) pr_elt !loc_lsym_mapping 
end

module ILK = LK (LInt)
module ILKSym = LKSym (LInt)
module LKTrans = KT.MakeTrans (ILKSym) (ILK)
(* module Z3K = Z3lib.Z3K (ILK) *)

(* let lkat_of_prog (prog: S.program): (ident * ILK.expr) list =
 *   (\* let () = Sym.reset () in *\)
 *   LKTrans.kat_of_prog prog *)
