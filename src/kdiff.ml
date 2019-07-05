open Globals
open Lib
open Lib.Print

module HA = Extlib.ExtHashtbl.Hashtbl
module DB = Debug

module I = Iast

module S = Spl_syn
module SU = Spl_utils
module SA = Spl_assume

module H = Hypotheses
module SK = Symkat
module SKU = Symkat_utils

module IK = SKU.ILK
module KT = SKU.LKTrans
module K = IK.LK
module L = SKU.LInt
module M = SKU.KMap (IK)

(* Types *)
type diff_symb = (Kat.var * (Bdd.key * bool) list)

type kpos =
  | KFst
  | KSnd
  | KDsj of kpos
  | KCnj of kpos
  | KPls of kpos
  | KDot of kpos

type ('v, 'k) csym_ =
  | CKey of bool * 'k
  | CVar of 'v

type csym = (Kat.var, Bdd.key) csym_

type ksym = (IK.V.t, IK.K.t) csym_

type ('v, 'k) cmap_ =
  | KMap of Bdd.key * 'k
  | VMap of Kat.var * 'v

type axmap = ((S.point list * S.instruction),
              (S.point list * S.cons)) cmap_

type assumption = {
  assumpt_info: K.key SA.assumption;
  assumpt_pos: kpos; }

type refinement =
  | Axiom of H.t
  | Assumption of assumption

type refinement_log =
  | GenAxiom of (H.t * axmap list)
  | CaseAnalysis of (bool * K.key * axmap list)

type result =
  | RLeaf of rleaf
  | RTree of rtree

and rleaf = {
  rl_fst_kat: K.expr;
  rl_snd_kat: K.expr;
  rl_cmp_op: refinement_direction;
  rl_symtab: KT.symtab;
  rl_refined_prog: S.program;
  rl_axioms: H.t;
  rl_log: refinement_log list; }

and rtree = {
  rt_fst_kat: K.expr;
  rt_snd_kat: K.expr;
  rt_symtab: KT.symtab;
  rt_key: K.key;
  rt_kpos: kpos;
  rt_is_complete: bool;
  rt_pos_result: result option;
  rt_neg_result: result option; }

(* Utils *)
let symtab_of_result res =
  match res with
  | RLeaf rl -> rl.rl_symtab
  | RTree rt -> rt.rt_symtab

let rec count_leaves r =
  let count_opt t_opt =
    match t_opt with
    | None -> 0
    | Some t -> count_leaves t in
  match r with
  | RLeaf _ -> 1
  | RTree rt -> count_opt rt.rt_pos_result + count_opt rt.rt_neg_result

let rec count_axioms r =
  let count_opt t_opt =
    match t_opt with
    | None -> 0
    | Some t -> count_axioms t in
  match r with
  | RLeaf rl -> List.length rl.rl_axioms
  | RTree rt -> count_opt rt.rt_pos_result + count_opt rt.rt_neg_result

(* Printing *)
let pr_cex = pr_to_string Kat.print_gstring

let rec pr_kpos kp =
  match kp with
  | KFst -> "@1"
  | KSnd -> "@2"
  | KDsj p -> "Dsj" ^ (pr_kpos p)
  | KCnj p -> "Cnj" ^ (pr_kpos p)
  | KPls p -> "Pls" ^ (pr_kpos p)
  | KDot p -> "Dot" ^ (pr_kpos p)

let pr_diff_symb =
  pr_pair IK.V.string_of
    (pr_list ~obrace:"{" ~cbrace:"}" (pr_pair IK.K.string_of pr_bool))

let debug_cex pname ke cex =
  Debug.hprint ("kdiff.search: CEX from " ^ pname ^
                 (* " (" ^ (SKU.pr_expr ke) ^ ")" ^ *)
                 ": " ^ (pr_cex cex) ^ " ")
    SKU.pr_gstring cex

let pr_assumption assumpt =
  pr_pair pr_kpos SA.pr_assumption (assumpt.assumpt_pos, assumpt.assumpt_info)

let pr_assumptions (assumpts: assumption list) =
  pr_list ~obrace:"{" ~cbrace:"}" pr_assumption assumpts

let pr_refinement = function
  | Axiom hypos -> SKU.pr_hypos hypos
  | Assumption assumpt -> pr_assumption assumpt

let pr_refinements = pr_list pr_refinement

let pr_axmap (m: axmap) =
  match m with
  | KMap (k, cons) ->
    (SKU.pr_key k) ^ ": " ^ (pr_pair (pr_list SU.pr_point) SU.pr_cons cons)
  | VMap (v, instr) ->
    (SKU.pr_var v) ^ ": " ^ (pr_pair (pr_list SU.pr_point) SU.pr_instruction instr)

let pr_axmap_lst = pr_list ~sep:"\n" pr_axmap

let pr_refinement_log l =
  let pr_map = pr_list ~obrace:"{" ~cbrace:"}" ~sep:"; " pr_axmap in
  match l with
  | GenAxiom (axiom, m) -> "GenAxiom " ^ (SKU.pr_hypos axiom) ^ " " ^ (pr_map m)
  | CaseAnalysis (b, k, m) ->
    "Case " ^ (if b then "" else "!") ^
    (IK.K.string_of k) ^ " " ^ (pr_map m)

let pr_refinement_logs ls =
  "\t   " ^ (pr_list ~sep:"\n\t-> " pr_refinement_log ls)

let pr_result r =
  let pr_key rt =
    (IK.K.string_of rt.rt_key) ^ (pr_kpos rt.rt_kpos) in
  let rec helper ntabs r =
    "\n" ^
    (match r with
    | RLeaf rl ->
      (pr_indent ntabs) ^ " |_ (A) " ^ (SKU.pr_hypos rl.rl_axioms)
      ^ "\n" ^ (pr_refinement_logs rl.rl_log)
      ^ "\n\t-> " ^ (IK.pr_expr rl.rl_fst_kat)
      ^ (match rl.rl_cmp_op with | RLe -> " <= " | REq -> " = ")
      ^ (IK.pr_expr rl.rl_snd_kat)
    | RTree rt ->
      let k = rt.rt_key in
      let pr = rt.rt_pos_result in
      let nr = rt.rt_neg_result in
      let cons_str =
        match KT.spl_cons_of_key k with
        | None -> ""
        | Some (_, cons) -> SU.pr_cons cons in
      (pr_indent ntabs) ^ "(" ^
      (if rt.rt_is_complete then "C" else "P") ^ ")" ^ " " ^
      (pr_key rt) ^ ": " ^ cons_str ^ "\n" ^
      ((pr_indent ntabs) ^ " |_  " ^ (pr_key rt) ^
        (match pr with
       | None -> ": No solutions"
       | Some r -> (helper (ntabs+1) r)) ^ "\n") ^
      ((pr_indent ntabs) ^ " |_  " ^ "!" ^ (pr_key rt) ^
        (match nr with
       | None -> ": No solutions"
       | Some r -> (helper (ntabs+1) r))))
  in
  let num_leaves = count_leaves r in
  let num_axioms = count_axioms r in
  (helper 0 r) ^ "\n" ^
  "Solution Stats: " ^
  "Size=" ^ (pr_int num_leaves) ^ ", " ^
  "NAxioms=" ^ (pr_int num_axioms)

let pr_result_tex r =
  let instr_map_of_var symtbl v =
    match KT.spl_instr_of_var ~symtbl:(Some symtbl) v with
    | None -> "mapfail(" ^ (IK.V.string_of v) ^ ")"
    | Some (pts, instr) -> (SU.pr_instruction instr)
  in
  let pr_key = IK.K.texstring_of in
  let pr_indent_dir n = "."^(string_of_int n)^" " in
  let mk_label s symtbl k1 k2 =
    "$\\left\\{\\begin{array}{l}" ^ s ^ "\\\\ "
    ^ "k_1=" ^ (K.pr_expr_tex k1 (instr_map_of_var symtbl)) ^ "\\\\ "
    ^ "k_2=" ^ (K.pr_expr_tex k2 (instr_map_of_var symtbl)) ^ "\\end{array}\\right.$." in
  let rec helper ntabs r =
    match r with
    | RLeaf rl ->
      let axioms = rl.rl_axioms in
      let kat1 = rl.rl_fst_kat in
      let kat2 = rl.rl_snd_kat in
      [((pr_indent_dir ntabs) ^ "AComplete.");
       (pr_indent_dir (ntabs+1)) ^ (mk_label ("Axioms: "^(SKU.pr_hypos_tex axioms))
                                      rl.rl_symtab kat1 kat2)]
    | RTree rt ->
      let kat1 = rt.rt_fst_kat in
      let kat2 = rt.rt_snd_kat in
      let k = rt.rt_key in
      let pr = rt.rt_pos_result in
      let nr = rt.rt_neg_result in
      let cons_str =
        match KT.spl_cons_of_key ~symtbl:(Some rt.rt_symtab) k with
        | None -> ""
        | Some (_, cons) -> ", cond: $"^(SU.pr_cons cons)^"$" in
      [((pr_indent_dir ntabs) ^ "(" ^
        (if rt.rt_is_complete then "Complete" else "Partial") ^ ")" ^ cons_str^".")]
      @ (match pr with
          | None -> []
          | Some r ->
            [((pr_indent_dir (ntabs+1)) ^ (mk_label ("Cond: "^(pr_key k)) rt.rt_symtab kat1 kat2))]
            @ (helper (ntabs+2) r))
      @ (match nr with
          | None -> []
          | Some r ->
            [((pr_indent_dir (ntabs+1)) ^ (mk_label ("Cond: \\neg "^(pr_key k)) rt.rt_symtab kat1 kat2))]
            @ (helper (ntabs+2) r))
  in
  ["\\dirtree{%";".1 solution."]
  @ helper 2 r
  @ ["}"]

let _dot_id = ref 0
let _dot_id_gen () = _dot_id := !_dot_id + 1; (string_of_int !_dot_id)

let pr_result_dot r =
  let pr_key = IK.K.string_of in
  let mklabel s k1 k2 =
    " [shape=box label=\"" ^ s
    ^ "\\lk1=" ^ (K.pr_expr k1)
    ^ "\\lk2=" ^ (K.pr_expr k2) ^ "\"]" in
  let rec helper parent_id r =
    match r with
    | RLeaf rl ->
      let myid = _dot_id_gen() in
      let axioms = rl.rl_axioms in
      let kat1 = rl.rl_fst_kat in
      let kat2 = rl.rl_snd_kat in
      [(parent_id ^ " -> " ^ myid);
	     (myid ^ (mklabel (SKU.pr_hypos axioms) kat1 kat2))]
    | RTree rt ->
      let kat1 = rt.rt_fst_kat in
      let kat2 = rt.rt_snd_kat in
      let k = rt.rt_key in
      let pr = rt.rt_pos_result in
      let nr = rt.rt_neg_result in
      let prid = _dot_id_gen() in
      let nrid = _dot_id_gen() in
      List.append [
	      (parent_id ^ " -> " ^ prid);
	      (parent_id ^ " -> " ^ nrid);
	      (prid ^ (mklabel (pr_key k) kat1 kat2));
	      (nrid ^ (mklabel ("not "^(pr_key k)) kat1 kat2))]
		    (List.append
         (match pr with None -> [] | Some r -> helper prid r)
         (match nr with None -> [] | Some r -> helper prid r))
  in
  let rootid = _dot_id_gen() in
  [("subgraph g"^rootid^" {"); (rootid ^ " [style=filled, color=gray, label=\"root\"]")]
  @ (helper rootid r)
  @ ["}"]

(** Edit Distance for KAT *)

type kelt =
  | KExpr of K.expr
  | KTest of K.test

type cmap = (IK.V.t, IK.K.t) cmap_

type 'a kact_elt = kpos * 'a

type 'a kaction =
  | Remove of 'a kact_elt
  | Replace of ('a kact_elt * 'a kact_elt)

let pr_kelt = function
  | KExpr e -> K.pr_expr e
  | KTest t -> K.pr_test t

let pr_csym_ pr_v pr_k c =
  match c with
  | CKey (b, k) -> (if b then "" else "!") ^ (pr_k k)
  | CVar v -> pr_v v

let pr_csym = pr_csym_ SKU.pr_var SKU.pr_key

let pr_ksym = pr_csym_ IK.V.string_of IK.K.string_of

let pr_cmap_ pr_v pr_k m =
  match m with
  | KMap (k1, k2) -> pr_pair SKU.pr_key pr_k (k1, k2)
  | VMap (v1, v2) -> pr_pair SKU.pr_var pr_v (v1, v2)

let pr_cmap = pr_cmap_ IK.V.string_of IK.K.string_of

let pr_kact_elt (pr_sym: 'a -> string) =
  pr_pair pr_kpos pr_sym

let pr_kaction
    (pr_sym: 'a -> string)
    (act: 'a kaction)
  : string =
  let pr_elt = pr_kact_elt pr_sym in
  match act with
  | Remove (kp, ke) -> "Remove" ^ (pr_elt (kp, ke))
  | Replace (kl, kr) -> "Replace" ^ (pr_pair pr_elt pr_elt (kl, kr))

let pr_kdist pr_sym pr_match (d, a, m) =
  (pr_pair pr_int
     (pr_list ~obrace:"{" ~cbrace:"}" (pr_kaction pr_sym)) (d, a)) ^ "\n" ^
  (pr_match m)

(* Utils *)
let eq_assumption (a1: assumption) (a2: assumption) =
  IK.K.eql a1.assumpt_info.SA.assumpt_symbol a2.assumpt_info.SA.assumpt_symbol

let eq_refinement (r1: refinement) (r2: refinement) =
  match r1, r2 with
  | Axiom _, Axiom _ -> false
  | Assumption a1, Assumption a2 -> eq_assumption a1 a2
  | _ -> false

let map_csym_ (f_v, f_k) c =
  match c with
  | CKey (b, k) -> CKey (b, f_k k)
  | CVar v -> CVar (f_v v)

let eq_csym_ (eq_v, eq_k) c1 c2 =
  match c1, c2 with
  | CKey (b1, k1), CKey (b2, k2) ->
    b1 == b2 && eq_k k1 k2
  | CVar v1, CVar v2 -> eq_v v1 v2
  | _ -> false

let eq_csym = eq_csym_ (SKU.eq_var, SKU.eq_key)

let is_cvar = function
  | CVar _ -> true
  | _ -> false

let is_ckey = function
  | CKey _ -> true
  | _ -> false

let ksym_has_dummy_label (s: ksym) =
  match s with
  | CVar v -> IK.V.has_dummy_label v
  | CKey (_, k) -> IK.K.has_dummy_label k

let rec ksyms_of_expr ?(get_tests=true)
    (axioms: H.t) (e: K.expr): ksym list =
  let f_get = ksyms_of_expr ~get_tests:get_tests axioms in
  match e with
  | K.Pls (l, r)
  | K.Dot (l, r) -> (f_get l) @ (f_get r)
  | K.Str s -> f_get s
  | K.Tst t -> if get_tests then ksyms_of_test t else []
  | Var v ->
    if SKU.eq_kat_expr axioms
        (K.expr_to_kat e) (K.expr_to_kat (K.Tst K.Top))
    then []
    else [CVar v]

and ksyms_of_test ?(sign=true) (t: K.test): ksym list =
  match t with
  | K.Dsj (l, r)
  | K.Cnj (l, r) ->
    (ksyms_of_test ~sign:sign l) @ (ksyms_of_test ~sign:sign r)
  | K.Neg e -> (ksyms_of_test ~sign:(not sign) e)
  | K.Top | K.Bot -> []
  | K.Prd k -> [CKey (sign, k)]

let is_disj_kpos = function
  | KDsj _ | KPls _ -> true
  | _ -> false

let is_conj_kpos = function
  | KCnj _ | KDot _ -> true
  | _ -> false

let rec is_fst_kpos kp =
  match kp with
  | KFst -> true
  | KSnd -> false
  | KPls p | KDot p
  | KCnj p | KDsj p ->
    is_fst_kpos p

let rec is_snd_kpos kp =
  match kp with
  | KFst -> false
  | KSnd -> true
  | KPls p | KDot p
  | KCnj p | KDsj p ->
    is_fst_kpos p

let rec pos_of_kpos kp =
  match kp with
  | KFst | KSnd -> kp
  | KPls p | KDot p
  | KCnj p | KDsj p ->
    pos_of_kpos p

let kelt_of_atom (atom: (Bdd.key * bool) list): kelt list =
  let kat_of_atom ((k, b): (Bdd.key * bool)): kelt =
    let t = K.Prd (IK.K.fresh_from_kat k) in
    KTest (if b then t else K.Neg t)
  in
  List.map kat_of_atom atom

let kelt_of_g_expr
    (gs: (Kat.var * (Bdd.key * bool) list)): kelt list =
  let var, atom = gs in
  let kvar = KExpr (K.Var (IK.V.fresh_from_kat var)) in
  let katom = kelt_of_atom atom in
  kvar::katom

let kelt_of_gstring (gs: Kat.gstring): kelt list =
  let atom_test, g_expr_lst = gs in
  List.rev ((kelt_of_atom atom_test) @
            (List.map kelt_of_g_expr g_expr_lst |> List.concat))

let csyms_of_atom (atom: (Bdd.key * bool) list)
  : csym list =
  let csym_of_atom ((k, b): (Bdd.key * bool)): csym =
    CKey (b, k)
  in
  List.map csym_of_atom atom

let csyms_of_g_expr
    (gs: (Kat.var * (Bdd.key * bool) list))
  : csym list =
  let var, atom = gs in
  let kvar = CVar var in
  let katom = csyms_of_atom atom in
  kvar::katom

let csyms_of_gstring (gs: Kat.gstring): csym list =
  let atom_test, g_expr_lst = gs in
  List.rev ((csyms_of_atom atom_test) @
            (List.map csyms_of_g_expr g_expr_lst
             |> List.concat))

let rec csyms_of_kat_test (t: Kat.test): csym list =
  match t with
  | Kat.Dsj (l, r) -> (csyms_of_kat_test r) @ (csyms_of_kat_test r)
  | Kat.Cnj (l, r) -> (csyms_of_kat_test r) @ (csyms_of_kat_test r)
  | Kat.Neg e -> csyms_of_kat_test e
  | Kat.Top | Kat.Bot -> []
  | Kat.Prd k -> [CKey (true, k)]

let rec csyms_of_kat_expr (e: Kat.expr): csym list =
  match e with
  | Kat.Pls (l, r) -> (csyms_of_kat_expr l) @ (csyms_of_kat_expr r)
  | Kat.Dot (l, r) -> (csyms_of_kat_expr l) @ (csyms_of_kat_expr r)
  | Kat.Str e -> csyms_of_kat_expr e
  | Kat.Tst t -> csyms_of_kat_test t
  | Kat.Var v -> [CVar v]

let csyms_of_kat_hypo (h: H.t): csym list =
  List.map (fun (l, _, r) ->
      (csyms_of_kat_expr l) @ (csyms_of_kat_expr r)) h
  |> List.concat |> List.dedup eq_csym

(* let restore_labels_cex (e: K.expr) (ks: kelt list): kelt list = *)

let (|||)
    (rm1: (bool * 'a list) Lazy.t)
    (rm2: (bool * 'a list) Lazy.t)
  : (bool * 'a list) =
  let r1, m1 = Lazy.force rm1 in
  if r1 then r1, m1
  else
    let r2, m2 = Lazy.force rm2 in
    if r2 then r2, m2
    else false, []

let (&&&)
    (rm1: (bool * 'a list) Lazy.t)
    (rm2: (bool * 'a list) Lazy.t)
  : (bool * 'a list) =
  let r1, m1 = Lazy.force rm1 in
  if not r1 then false, []
  else
    let r2, m2 = Lazy.force rm2 in
    if not r2 then false, []
    else true, m1 @ m2

let rec split_lst ls =
  match ls with
  | [] -> [([], [])]
  | x::xs ->
    let split_xs = split_lst xs in
    (List.map (fun (s1, s2) -> (x::s1, s2)) split_xs) @
    (List.map (fun (s1, s2) -> (s1, x::s2)) split_xs)

let rec split_ordered_lst ls =
  match ls with
  | [] -> [([], [])]
  | x::xs ->
    let split_xs = split_ordered_lst xs in
    ([], ls)::(List.map (fun (s1, s2) -> (x::s1, s2)) split_xs)

let rec match_cex
    (axioms: H.t)
    (e: K.expr)
    (cs: csym list)
  : (bool * cmap list) =
  let e_syms = K.expr_kat_syms e in
  let cs = List.filter (fun c ->
      match c with
      | CVar v -> BatSet.mem v e_syms
      | CKey (_, k) -> BatSet.mem k e_syms) cs in
  let () = DB.dhprint "match_cex: cs: " (pr_list pr_csym) cs in
  expr_is_match axioms e cs

and expr_is_match
    (axioms: H.t)
    (e: K.expr)
    (cs: csym list)
  : (bool * cmap list) =
  let matcher = expr_is_match axioms in
  match e with
  | K.Pls (l, r) ->
    if (SKU.eq_kat_expr axioms
          (K.expr_to_kat e) (K.expr_to_kat (K.Tst K.Top)))
       && (List.is_empty cs)
    then true, []
    else
      let rm1 = lazy (matcher l cs) in
      let rm2 = lazy (matcher r cs) in
      rm1 ||| rm2
  | K.Dot (l, r) ->
    (* Assuming that the order of l and r in cs is not changed *)
    let spl_cs = split_ordered_lst cs in
    let rec find_split spl =
      match spl with
      | [] -> false, []
      | (sl, sr)::ss ->
        let rm1 = lazy (matcher l sl) in
        let rm2 = lazy (matcher r sr) in
        let r1, m1 = rm1 &&& rm2 in
        if r1 then r1, m1
        (* else if List.for_all (fun s -> is_ckey s) sl &&
         *         List.for_all (fun s -> is_ckey s) sr then
         *   let rm1 = lazy (matcher l sr) in
         *   let rm2 = lazy (matcher r sl) in
         *   let r2, m2 = rm1 &&& rm2 in
         *   if r2 then r2, m2
         *   else find_split ss *)
        else find_split ss
    in
    find_split (List.rev spl_cs)
  | K.Str s ->
    (match cs with
     | [] -> true, []
     | _ -> matcher (K.Dot (s, e)) cs)
  | K.Tst t -> test_is_match axioms t cs
  | K.Var v ->
    (match cs with
     | [] -> true, []
     | [(CVar c)] ->
       if SKU.eq_var (IK.V.to_kat v) c then
         true, [VMap (c, v)]
       else false, []
     | _ -> false, [])

and test_is_match
    (axioms: H.t)
    (t: K.test)
    (cs: csym list)
  : (bool * cmap list) =
  if List.exists (fun c ->
      match c with | CVar _ -> true | _ -> false) cs
  then false, []
  else
    let matcher = test_is_match axioms in
    match t with
    | K.Dsj (l, r) ->
      if (SKU.eq_kat_expr axioms
          (K.expr_to_kat (K.Tst t)) (K.expr_to_kat (K.Tst K.Top)))
      && (List.is_empty cs)
      then true, []
      else
        let spl_cs = split_lst cs in
        let rec find_split spl =
          match spl with
          | [] -> false, []
          | (sl, sr)::ss ->
            let rm1 = lazy (matcher l sl) in
            let rm2 = lazy (matcher r sr) in
            let r1, m1 = rm1 ||| rm2 in
            if r1 then r1, m1
            else find_split ss
        in
        find_split spl_cs
    | K.Cnj (l, r) ->
      let spl_cs = split_lst cs in
      let rec find_split spl =
        match spl with
        | [] -> false, []
        | (sl, sr)::ss ->
          let rm1 = lazy (matcher l sl) in
          let rm2 = lazy (matcher r sr) in
          let r1, m1 = rm1 &&& rm2 in
          if r1 then r1, m1
          else find_split ss
      in
      find_split spl_cs
    | K.Neg e ->
      (match e with
       | K.Prd k ->
         (match cs with
          | [(CKey (b, c))] ->
            if not b && (SKU.eq_key (IK.K.to_kat k) c) then
              true, [KMap (c, k)]
            else false, []
          | _ -> false, [])
       | _ -> matcher (K.test_norm_neg t) cs)
    | K.Top ->
      (match cs with
       | [] -> true, []
       | _ -> false, [])
    | K.Bot -> false, []
    | K.Prd k ->
      (match cs with
       | [(CKey (b, c))] ->
         if b && (SKU.eq_key (IK.K.to_kat k) c) then
           true, [KMap (c, k)]
         else false, []
       | _ -> false, [])

let rec match_cex_rem
    (axioms: H.t)
    (e: K.expr)
    (cs: csym list)
  : (bool * cmap list) =
  let e_syms = K.expr_kat_syms e in
  let cs = List.filter (fun c ->
      match c with
      | CVar v -> (* BatSet.mem v e_syms *) true
      | CKey (_, k) -> BatSet.mem k e_syms) cs in
  let () = DB.dhprint "match_cex: cs: " (pr_list pr_csym) cs in
  let lexicographic_compare (r1, m1) (r2, m2) =
    let compare_r = compare (List.length r1) (List.length r2) in
    if compare_r != 0 then
      -(compare (List.length m1) (List.length m2))
    else compare_r
  in

  let matching_res = expr_match_rem axioms e cs in
  let sorted_matching_res = List.sort lexicographic_compare matching_res in
  let () = DB.hprint "sorted_matching_res:"
      (pr_list ~sep:"\n"
         (pr_pair (pr_list pr_csym) (pr_list pr_cmap)))
      sorted_matching_res in
  match sorted_matching_res with
  | [] -> false, []
  | (rem_cs, mappings)::_ ->
    if List.is_empty rem_cs then true, mappings
    else false, mappings
  
and expr_match_rem
    (axioms: H.t)
    (e: K.expr)
    (cs: csym list)
  : (csym list * cmap list) list =
  let matcher = expr_match_rem axioms in
  if (SKU.eq_kat_expr axioms
        (K.expr_to_kat e) (K.expr_to_kat (K.Tst K.Top)))
  then [(cs, [])]
  else
    match e with
    | K.Pls (l, r) -> (matcher l cs) @ (matcher r cs)
    | K.Dot (l, r) ->
      let rem_match_l = matcher l cs in
      List.map (fun (l_rem_cs, l_cmap) ->
          let rem_match_r = matcher r l_rem_cs in
          List.map (fun (r_rem_cs, r_cmap) ->
              (r_rem_cs, l_cmap @ r_cmap)
            ) rem_match_r
        ) rem_match_l
      |> List.concat
    | K.Str s ->
      [(cs, [])] @ (matcher (K.Dot (s, e)) cs)
    | K.Tst t -> test_match_rem axioms t cs
    | K.Var v ->
      let rec helper cs =
        match cs with
        | [] -> []
        | (CVar c)::cr ->
          if SKU.eq_var (IK.V.to_kat v) c then
            [(cr, [VMap(c, v)])]
          else if SKU.eq_kat_expr axioms
              (Kat.Var (IK.V.to_kat v)) (Kat.Var c) then
            [(cr, [])]
          else []
        | (CKey _)::cr -> helper cr
      in
      helper cs

and test_match_rem
    (axioms: H.t)
    (t: K.test)
    (cs: csym list)
  : (csym list * cmap list) list =
  let rec split cs =
    match cs with
    | [] -> [], []
    | (CVar _)::_ -> [], cs
    | (CKey (b, c))::cr ->
      let test_cr, rem_cr = split cr in
      (b, c)::test_cr, rem_cr
  in

  let test_sym_match_rem is_pos k = 
    let test_cs, rem_cs = split cs in
    let rec helper test_cs =
      match test_cs with
      | [] -> [], []
      | (b, c)::test_cr ->
        if (b == is_pos) && (SKU.eq_key (IK.K.to_kat k) c) then
          [KMap (c, k)], test_cr
        else
          let mappings, rem_test_cr = helper test_cr in
          mappings, (b, c)::rem_test_cr
    in
    let mappings, rem_test_cs = helper test_cs in
    if List.is_empty mappings then []
    else
      [(List.map (fun (b, c) -> CKey (b, c)) rem_test_cs) @ rem_cs,
       mappings]
  in

  let matcher = test_match_rem axioms in
  if (SKU.eq_kat_expr axioms
        (K.expr_to_kat (K.Tst t)) (K.expr_to_kat (K.Tst K.Top)))
  then [(cs, [])]
  else
    match t with
    | K.Dsj (l, r) -> (matcher l cs) @ (matcher r cs)
    | K.Cnj (l, r) ->
      let rem_match_l = matcher l cs in
      List.map (fun (l_rem_cs, l_cmap) ->
          let rem_match_r = matcher r l_rem_cs in
          List.map (fun (r_rem_cs, r_cmap) ->
              (r_rem_cs, l_cmap @ r_cmap)
            ) rem_match_r
        ) rem_match_l
      |> List.concat
    | K.Top -> [(cs, [])]
    | K.Bot -> []
    | K.Prd k -> test_sym_match_rem true k
    | K.Neg e ->
      (match e with
       | K.Prd k -> test_sym_match_rem false k
       | _ -> matcher (K.test_norm_neg t) cs)

let rec add_label_gstring
    (axioms: H.t)
    (gs: Kat.gstring)
    (e: K.expr)
  : ksym list =
  let cs = csyms_of_gstring gs in
  let () = DB.dhprint "add_label_gstring: e: " K.pr_expr e in
  let () = DB.dhprint "add_label_gstring: cs: " (pr_list pr_csym) cs in
  let r, matcher = match_cex_rem axioms e cs in
  let () = DB.dhprint "add_label_gstring: matcher: " (pr_list pr_cmap) matcher in
  (* if r then
   *   add_label_csyms matcher cs
   * else
   *   failwith "add_label_gstring: failed to match cex with kat" *)
  add_label_csyms matcher cs

(* and add_label_csyms
 *     (ms: cmap list)
 *     (cs: csym list)
 *   : ksym list =
 *   match cs with
 *   | [] -> []
 *   | s::ss ->
 *     let sk, rem_ms =
 *       match s with
 *       | CKey (b, k) ->
 *         let nk, rem_ms = add_label_key ms k in
 *         CKey (b, nk), rem_ms
 *       | CVar v ->
 *         let nv, rem_ms = add_label_var ms v in
 *         CVar nv, rem_ms
 *     in
 *     sk::(add_label_csyms rem_ms ss)
 * 
 * and add_label_key ms k =
 *   match ms with
 *   | [] -> IK.K.fresh_from_kat k, []
 *   | m::rm ->
 *     (match m with
 *      | KMap (k1, k2) when SKU.eq_key k k1 ->
 *        k2, rm
 *      | _ -> IK.K.fresh_from_kat k, ms)
 * 
 * and add_label_var ms v =
 *   match ms with
 *   | [] -> IK.V.fresh_from_kat v, []
 *   | m::rm ->
 *     (match m with
 *      | VMap (v1, v2) when SKU.eq_var v v1 ->
 *        v2, rm
 *      | _ -> IK.V.fresh_from_kat v, ms) *)

and add_label_csyms
    (ms: cmap list)
    (cs: csym list)
  : ksym list =
  match cs with
  | [] -> []
  | s::ss ->
    (match s with
     | CKey (b, k) ->
       let nk_opt, rem_ms = add_label_key ms k in
       let rs = add_label_csyms rem_ms ss in
       (match nk_opt with
        | None -> (CKey (b, IK.K.fresh_from_kat k))::rs
        | Some nk -> (CKey (b, nk))::rs)
     | CVar v ->
       let nv_opt, rem_ms = add_label_var ms v in
       let rs = add_label_csyms rem_ms ss in
       (match nv_opt with
        | None -> (CVar (IK.V.fresh_from_kat v))::rs
        | Some nv -> (CVar nv)::rs))

and add_label_key ms k =
  let rec helper ms =
    match ms with
    | [] -> None, []
    | (VMap _)::_ -> None, ms
    | (KMap (k1, k2) as m)::mr ->
      if SKU.eq_key k k1 then
        Some k2, mr
      else
        let nk_opt, rem_mr = helper mr in
        nk_opt, m::rem_mr
  in
  helper ms

and add_label_var ms v =
  match ms with
  | [] -> None, []
  | m::rm ->
    (match m with
     | VMap (v1, v2) when SKU.eq_var v v1 ->
       Some v2, rm
     | _ -> None, ms)

let min2 key_of d1 d2 =
  if key_of d1 <= key_of d2 then d1
  else d2

let min3 key_of d1 d2 d3 =
  Core.List.reduce_exn ~f:(min2 key_of)
    [d1; d2; d3]

let dot_kelt k1 k2 =
  match k1, k2 with
  | KExpr e1, KExpr e2 -> KExpr (K.Dot (e1, e2))
  | KTest e1, KTest e2 -> KTest (K.Cnj (e1, e2))
  | KExpr e1, KTest e2 -> KExpr (K.Dot (e1, K.Tst e2))
  | KTest e1, KExpr e2 -> KExpr (K.Dot (K.Tst e1, e2))

let neg_kelt k =
  match k with
  | KTest e -> KTest (K.Neg e)
  | _ -> warning_unexpected "neg_kelt" pr_kelt k

let pls_kelt k1 k2 =
  match k1, k2 with
  | KExpr e1, KExpr e2 -> KExpr (K.Pls (e1, e2))
  | KTest e1, KTest e2 -> KTest (K.Dsj (e1, e2))
  | KExpr e1, KTest e2 -> KExpr (K.Pls (e1, K.Tst e2))
  | KTest e1, KExpr e2 -> KExpr (K.Pls (K.Tst e1, e2))

let str_kelt k =
  match k with
  | KExpr e -> KExpr (K.Str e)
  | _ -> warning_unexpected "str_kelt" pr_kelt k

let (+++) (d1, a1, (mf1, ms1)) (d2, a2, (mf2, ms2)) =
  (d1 + d2, a1 @ a2, (pls_kelt mf1 mf2, pls_kelt ms1 ms2))

let (++.) (d1, a1, (mf1, ms1)) (d2, a2, (mf2, ms2)) =
  (d1 + d2, a1 @ a2, (dot_kelt mf1 mf2, dot_kelt ms1 ms2))

let (++?) (d1, a1) (d2, a2, m) =
  (d1 + d2, a1 @ a2, m)

let neg_dist (d, a, (m1, m2)) =
  (d, a, (neg_kelt m1, neg_kelt m2))

let str_dist (d, a, (m1, m2)) =
  (d, a, (str_kelt m1, str_kelt m2))

let init_sum_cost = 5

let sum_cost = ref init_sum_cost

let match_cost = ref (-init_sum_cost)

let reset_edit_dist_cost () =
  (sum_cost := init_sum_cost;
   match_cost := -init_sum_cost)

let rec replace_cost k =
  match k with
  | KExpr e -> replace_cost_expr e
  | KTest t -> replace_cost_test t

and replace_cost_expr expr =
  match expr with
  | K.Pls (l, r) -> Core.Int.max (replace_cost_expr l) (replace_cost_expr r) + 1
  | K.Dot (h, t) -> (replace_cost_expr h) + (replace_cost_expr t) + 1
  | K.Str e -> (replace_cost_expr e) + 1
  | K.Tst e -> replace_cost_test e
  | K.Var _ -> 1

and replace_cost_test tst =
  match tst with
  | K.Dsj (l, r) -> Core.Int.max (replace_cost_test l) (replace_cost_test r) + 1
  | K.Cnj (l, r) -> (replace_cost_test l) + (replace_cost_test r) + 1
  | K.Neg e -> (replace_cost_test e) + 1
  | K.Top
  | K.Bot
  | K.Prd _ -> 1

and max_replace_cost k1 k2 =
  Core.Int.max (replace_cost k1) (replace_cost k2)

let replace_cost_ksym k =
  match k with
  | CVar v ->
    let instr = KT.spl_instr_of_var v in
    (match instr with
    | None -> replace_cost_expr (K.Var v)
    | Some (_, i) ->
      (match i with
       | S.CALL (_, c, _) when List.mem String.equal c !no_removed_events ->
         !sum_cost
       | _ -> replace_cost_expr (K.Var v)))
  | CKey (b, k) ->
    let prd = K.Prd k in
    replace_cost_test (if b then prd else K.Neg prd)

let max_replace_cost_ksym k1 k2 =
  Core.Int.max (replace_cost_ksym k1) (replace_cost_ksym k2)

let rec len_of_kat k =
  match k with
  | K.Dot (l, r) -> len_of_kat l + len_of_kat r
  | _ -> 1

let key_of_ed (d, _, _) = d

let edit_distance_test_norec edit_distance_test (t1, t2) =
  match t1, t2 with
  | K.Top, K.Top
  | K.Bot, K.Bot ->
    let m = (KTest t1, KTest t2) in
    (!match_cost, [], m)
  | K.Prd k1, K.Prd k2 ->
    let m = (KTest t1, KTest t2) in
    if IK.K.eq k1 k2 then (!match_cost, [], m)
    else (1, [Replace ((KFst, KTest t1), (KSnd, KTest t2))], m)
  | K.Neg n1, K.Neg n2 -> neg_dist (edit_distance_test (n1, n2))
  | K.Cnj (l1, r1), K.Cnj (l2, r2) ->
    let da1 = edit_distance_test (l1, l2) ++. edit_distance_test (r1, r2) in
    let da2 = edit_distance_test (l1, r2) ++. edit_distance_test (r1, l2) in
    min2 key_of_ed da1 da2
  | K.Cnj (l1, r1), _ ->
    let dl = (1, [Remove (KCnj KFst, KTest r1)]) ++? edit_distance_test (l1, t2) in
    let dr = (1, [Remove (KCnj KFst, KTest l1)]) ++? edit_distance_test (r1, t2) in
    min2 key_of_ed dl dr
  | _, K.Cnj (l2, r2) ->
    let dl = (1, [Remove (KCnj KSnd, KTest r2)]) ++? edit_distance_test (t1, l2) in
    let dr = (1, [Remove (KCnj KSnd, KTest l2)]) ++? edit_distance_test (t1, r2) in
    min2 key_of_ed dl dr
  | K.Dsj (l1, r1), K.Dsj (l2, r2) ->
    let da1 = edit_distance_test (l1, l2) +++ edit_distance_test (r1, r2) in
    let da2 = edit_distance_test (l1, r2) +++ edit_distance_test (r1, l2) in
    min2 key_of_ed da1 da2
  | K.Dsj (l1, r1), _ ->
    let dl = (1, [Remove (KDsj KFst, KTest r1)]) ++? edit_distance_test (l1, t2) in
    let dr = (1, [Remove (KDsj KFst, KTest l1)]) ++? edit_distance_test (r1, t2) in
    min2 key_of_ed dl dr
  | _, K.Dsj (l2, r2) ->
    let dl = (1, [Remove (KDsj KSnd, KTest r2)]) ++? edit_distance_test (t1, l2) in
    let dr = (1, [Remove (KDsj KSnd, KTest l2)]) ++? edit_distance_test (t1, r2) in
    min2 key_of_ed dl dr
  | _ ->
    let m = (KTest t1, KTest t2) in
    let max_cost = max_replace_cost (KTest t1) (KTest t2) in
    (max_cost, [Replace ((KFst, KTest t1), (KSnd, KTest t2))], m)

let edit_distance_test =
  Memo.memo_rec edit_distance_test_norec

let edit_distance_norec edit_distance (k1, k2) =
  let res = 
    match k1, k2 with
    | K.Var v1, K.Var v2 ->
      let m = (KExpr k1, KExpr k2) in
      if IK.V.eq v1 v2 then (!match_cost, [], m)
      else (1, [Replace ((KFst, KExpr k1), (KSnd, KExpr k2))], m)
    | K.Tst t1, K.Tst t2 -> edit_distance_test (t1, t2)
    | K.Str s1, K.Str s2 -> str_dist (edit_distance (s1, s2))
    | K.Pls (l1, r1), K.Pls (l2, r2) ->
      let da1 = edit_distance (l1, l2) +++ edit_distance (r1, r2) in
      let da2 = edit_distance (l1, r2) +++ edit_distance (r1, l2) in
      min2 key_of_ed da1 da2
    | K.Pls (l1, r1), _ ->
      let dl = (1, [Remove (KPls KFst, KExpr r1)]) ++? edit_distance (l1, k2) in
      let dr = (1, [Remove (KPls KFst, KExpr l1)]) ++? edit_distance (r1, k2) in
      min2 key_of_ed dl dr
    | _, K.Pls (l2, r2) ->
      let dl = (1, [Remove (KPls KSnd, KExpr r2)]) ++? edit_distance (k1, l2) in
      let dr = (1, [Remove (KPls KSnd, KExpr l2)]) ++? edit_distance (k1, r2) in
      min2 key_of_ed dl dr
    | K.Dot (h1, t1), K.Dot (h2, t2) ->
      let replace_hd_cost = edit_distance (h1, h2) in
      let replace_hd_dst = replace_hd_cost ++. edit_distance (t1, t2) in
      let remove_hd_fst_dst =
        (replace_cost (KExpr h1), [Remove (KDot KFst, KExpr h1)])
        ++? edit_distance (t1, k2) in
      let remove_hd_snd_dst =
        (replace_cost (KExpr h2), [Remove (KDot KSnd, KExpr h2)])
        ++? edit_distance (k1, t2) in
      min3 key_of_ed replace_hd_dst remove_hd_fst_dst remove_hd_snd_dst
    | K.Dot (h1, t1), _ ->
      let remove_hd_dst =
        (replace_cost (KExpr h1), [Remove (KDot KFst, KExpr h1)])
        ++? edit_distance (t1, k2) in
      let remove_tl_dst =
        (replace_cost (KExpr t1),
         [Remove (KDot KFst, KExpr t1)]) ++? edit_distance (h1, k2) in
      min2 key_of_ed remove_hd_dst remove_tl_dst
    | _, K.Dot (h2, t2) ->
      let remove_hd_dst =
        (replace_cost (KExpr h2),
         [Remove (KDot KSnd, KExpr h2)]) ++? edit_distance (k1, t2) in
      let remove_tl_dst =
        (replace_cost (KExpr t2),
         [Remove (KDot KSnd, KExpr t2)]) ++? edit_distance (k1, h2) in
      min2 key_of_ed remove_hd_dst remove_tl_dst
    | K.Tst t, _
    | _, K.Tst t ->
      let replace_cost = if K.test_is_top t then 1 else !sum_cost in
      let m = (KExpr k1, KExpr k2) in
      (replace_cost, [Replace ((KFst, KExpr k1), (KSnd, KExpr k2))], m)
    | _ ->
      let m = (KExpr k1, KExpr k2) in
      let max_cost = max_replace_cost (KExpr k1) (KExpr k2) in
      (max_cost, [Replace ((KFst, KExpr k1), (KSnd, KExpr k2))], m)
  in
  let pr_match (m1, m2) =
    ("fst match: " ^ (pr_kelt m1)) ^ "\n" ^
    ("snd match: " ^ (pr_kelt m2)) ^ "\n" in
  let () = DB.dhprint "edit_distance res: " (pr_kdist pr_kelt pr_match) res in
  res

let edit_distance (k1, k2) =
  let () = reset_edit_dist_cost () in
  let () =
    sum_cost := (replace_cost (KExpr k1)) + (replace_cost (KExpr k2));
    match_cost := -(!sum_cost / (Core.Int.min (len_of_kat k1) (len_of_kat k2)))
  in
  let () = DB.dhprint "sum_cost: " pr_int !sum_cost in
  let () = DB.dhprint "match_cost: " pr_int !match_cost in
  Memo.memo_rec edit_distance_norec (k1, k2)

(* Utils *)
let is_complete_result = function
  | RLeaf _ -> true
  | RTree rt -> rt.rt_is_complete

let mk_rtree fst_kat snd_kat symtab is_complete key kp pr nr =
  RTree {
    rt_fst_kat = fst_kat;
    rt_snd_kat = snd_kat;
    rt_symtab = symtab;
    rt_is_complete = is_complete;
    rt_key = key;
    rt_kpos = kp;
    rt_pos_result = pr;
    rt_neg_result = nr; }

let mk_rleaf fst_kat snd_kat cop prog symtab axioms logs =
  RLeaf {
    rl_fst_kat = fst_kat;
    rl_snd_kat = snd_kat;
    rl_cmp_op = cop;
    rl_refined_prog = prog;
    rl_symtab = symtab;
    rl_axioms = axioms;
    rl_log = logs; }

let merge_results_pair fst_kat snd_kat symtab rop
    assumpt pr1 pr2 =
  let key = assumpt.assumpt_info.SA.assumpt_symbol in
  let kp = assumpt.assumpt_pos in
  let build_complete =
    match rop with
    | REq -> true
    | RLe -> is_fst_kpos kp in
  if List.is_empty pr1 then
    List.map (fun r2 ->
        mk_rtree fst_kat snd_kat symtab (not build_complete && is_complete_result r2)
          key kp None (Some r2)) pr2
  else if List.is_empty pr2 then
    List.map (fun r1 ->
        mk_rtree fst_kat snd_kat symtab (not build_complete && is_complete_result r1)
          key kp (Some r1) None) pr1
  else
    List.fold_left
      (fun a1 r1 ->
         a1 @
         (List.fold_left
            (fun a2 r2 ->
               let r =
                 let is_complete =
                   if build_complete then
                     is_complete_result r1 && is_complete_result r2
                   else is_complete_result r1 || is_complete_result r2
                 in
                 mk_rtree fst_kat snd_kat symtab is_complete key kp (Some r1) (Some r2)
               in
               a2 @ [r]) [] pr2)
      ) [] pr1

let eq_axiom a1 a2 =
  (List.length a1 == List.length a2) &&
  (List.for_all (fun (v1, b1) ->
       let mth_opt = List.find_opt (fun (v2, _) -> SKU.eq_key v1 v2) a2 in
       match mth_opt with
       | None -> false
       | Some (_, b2) -> b1 == b2) a1)

(* Algorithms *)
let nil_char = Char.chr 0

let empty_cex = ([], [])

let is_nil v = (v = nil_char)

let (analyzed_test_symbols: Bdd.key list ref) = ref []

let add_elt_store (store: 'a list ref) (elt: 'a): unit =
  store := !store @ [elt]

let gen_actions_instructions (v1, instrs1) (v2, instrs2) =
  match instrs1, instrs2 with
  | i1::_, i2::_ ->
    (match i1, i2 with
     | S.ASSIGN (a1, _), S.ASSIGN (a2, _) when SU.eq_var a1 a2 ->
       let hypos = [(Kat.Var v1, `Eq, Kat.Var v2)] in
       [Axiom hypos]
     | S.CALL (_, c1, _), S.CALL (_, c2, _) when String.equal c1 c2 ->
       let hypos = [(Kat.Var v1, `Eq, Kat.Var v2)] in
       [Axiom hypos]
     | _ -> [])
  | _::_, [] -> [Axiom [(Kat.Var v1, `Eq, Kat.Tst Kat.Top)]]
  | [], _::_ -> [Axiom [(Kat.Var v2, `Eq, Kat.Tst Kat.Top)]]
  | _ -> []

(* let gen_actions_conditions
 *     (etab: (S.bexpr, char) HA.t)
 *     (as1: (Bdd.key * bool) list)
 *     (as2: (Bdd.key * bool) list) =
 *   let ks1 = List.map fst as1 in
 *   let ks2 = List.map fst as2 in
 *   let test_symbs =
 *     List.filter (fun s ->
 *         not (List.exists (fun k -> SKU.eq_key k s) !analyzed_test_symbols))
 *       (ks1 @ ks2)
 *     |> List.dedup SKU.eq_key in
 *   match test_symbs with
 *   | [] -> []
 *   | s::_ ->
 *     let () = Debug.dhprint "Considered test symbol: " SKU.pr_key s in
 *     let test_conds = SKU.keys_of_value etab s in
 *     let test_pos =
 *       SKU.keys_of_value SKU.loc_symb_mapping s
 *       |> List.dedup SU.eq_point in
 *     let () = Debug.dhprint "Program locations: "
 *         (pr_list SU.pr_point) test_pos in
 *     List.map (fun cond ->
 *         let () = add_elt_store analyzed_test_symbols s in
 *         let pos_assume =
 *           { SA.assumpt_cond = cond;
 *             SA.assumpt_neg = false;
 *             SA.assumpt_symbol = IK.K.from_kat s;
 *             SA.assumpt_pos = test_pos; } in
 *         (\* let neg_assume = { pos_assume with SU.assumpt_neg = true } in *\)
 *         Assumption pos_assume) test_conds
 * 
 * let gen_refinements
 *     (etab: (S.bexpr, char) HA.t)
 *     (itab: (S.instruction, char) HA.t)
 *     (s1: diff_symb) (s2: diff_symb): refinement list =
 *   let v1, as1 = s1 in
 *   let v2, as2 = s2 in
 *   if SKU.eq_key v1 v2 then
 *     gen_actions_conditions etab as1 as2
 *   else
 *     (\* let v1 = IK.V.to_kat v1 in
 *      * let v2 = IK.V.to_kat v2 in *\)
 *     let instrs1 = SKU.keys_of_value itab v1 in
 *     let instrs2 = SKU.keys_of_value itab v2 in
 *     let () = Debug.dhprint "First diff instr: "
 *         (pr_list Spl_utils.pr_instruction) instrs1 in
 *     let () = Debug.dhprint "Second diff instr: "
 *         (pr_list Spl_utils.pr_instruction) instrs2 in
 *     let axiom_acts = gen_actions_instructions (v1, instrs1) (v2, instrs2) in
 *     if not (is_nil v1) && not (is_nil v2) then
 *       let assumpt_acts = gen_actions_conditions etab as1 as2 in
 *       axiom_acts @ assumpt_acts
 *     else
 *       axiom_acts *)

let is_infeasible_kaction (kact: ksym kaction): bool =
  let elt_has_dummy_label (_, s) = ksym_has_dummy_label s in
  match kact with
  | Remove e -> elt_has_dummy_label e
  | Replace (e1, e2) -> (elt_has_dummy_label e1) &&
                        (elt_has_dummy_label e2)

let test_of_symbol
    (s: IK.V.t)
    (ks: ksym list)
  : IK.K.t list =
  let rec helper ~signal s ks =
    match ks with
    | [] -> []
    | k::ks ->
      (match k with
       | CVar v ->
         if signal then []
         else if IK.V.eql v s then
           helper ~signal:true s ks
         else helper ~signal:signal s ks
       | CKey (_, k) ->
         if signal then
           (* k::(helper ~signal:signal s ks) *)
           [k]
         else (helper ~signal:signal s ks))
  in
  helper ~signal:false s (List.rev ks)

let rec test_contains_key k sign t =
  match t with
  | K.Dsj (l, r)
  | K.Cnj (l, r) -> (test_contains_key k sign l) || (test_contains_key k sign r)
  | K.Top | K.Bot -> false
  | K.Prd p -> if IK.K.eql k p then sign else false
  | K.Neg nt -> test_contains_key k (not sign) nt

let rec direct_vars_of_key
    (axioms: H.t)
    (k: IK.K.t)
    (sign: bool)
    (e: K.expr)
  : IK.V.t list =
  let rec helper e =
    match e with
    | K.Pls (l, r) ->
      let sl = helper l in
      if List.not_empty sl then sl
      else helper r
    | K.Dot (l, r) ->
      (match l, r with
       | K.Tst t, _ ->
         if test_contains_key k sign t then
           let r_ksyms = ksyms_of_expr ~get_tests:false axioms r in
           List.map (fun s -> match s with
                 CVar v -> [v] | _ -> []) r_ksyms |> List.concat
         else helper r
       | K.Str s, K.Tst t ->
         if test_contains_key k sign t then []
         else helper s
       | _, _ ->
         let sl = helper l in
         if List.not_empty sl then sl
         else helper r)
    | _ -> []
  in helper e

let rec rev_expr (e: K.expr) =
  match e with
  | K.Var _
  | K.Tst _ -> e
  | K.Str s -> K.Str (rev_expr s)
  | K.Pls (l, r) -> K.Pls (rev_expr r, rev_expr l)
  | K.Dot (l, r) -> K.Dot (rev_expr r, rev_expr l)

let rec direct_test_of_var
    (v: IK.V.t)
    (e: K.expr)
  : K.test option =
  let rec helper rev_e =
    match rev_e with
    | K.Var kv -> IK.V.eql v kv, None
    | K.Pls (rev_r, rev_l) ->
      let (is_found, _) as res_r = helper rev_r in
      if is_found then res_r
      else helper rev_l
    | K.Dot (rev_r, rev_l) ->
      let (is_found, test_r) as res_r = helper rev_r in
      if is_found then
        match test_r with
        | None -> true, closest_test_of_rev_expr rev_l
        | Some _ -> res_r
      else helper rev_l
    | K.Str rev_s -> helper rev_s
    | K.Tst _ -> false, None
  in
  let _, res = helper (rev_expr e) in
  res

and closest_test_of_rev_expr e =
  match e with
  | K.Tst t -> Some t
  | K.Dot (rev_r, rev_l) ->
    let res = closest_test_of_rev_expr rev_r in
    (match res with
    | None -> closest_test_of_rev_expr rev_l
    | Some _ -> res)
  | K.Var _
  | K.Str _
  | K.Pls _ -> None

let refinement_of_kaction
    (axioms: H.t)
    (kacts: ksym kaction list)
    (fst_kat: K.expr)
    (snd_kat: K.expr)
    (fst_ksyms: ksym list)
    (snd_ksyms: ksym list)
    (kact: ksym kaction)
  : ((refinement * axmap list) Lazy.t) list =
  let test_of_key (b, k) =
    let s = IK.K.to_kat k in
    let p = Kat.Prd s in
    if b then p else Kat.Neg p
  in
  let expr_of_var v =
    let s = IK.V.to_kat v in
    Kat.Var s
  in
  let instr_map_of_var v =
    match KT.spl_instr_of_var v with
    | None -> []
    | Some instr -> [VMap (IK.V.to_kat v, instr)]
  in
  let cons_map_of_key k =
    match KT.spl_cons_of_key k with
    | None -> []
    | Some cons -> [KMap (IK.K.to_kat k, cons)]
  in

  let mk_assumpts k pos =
    let k_cons = KT.spl_cons_of_key k in
    let () = DB.dhprint "key: " IK.K.string_of k in
    let () = DB.dhprint "cons: "
        (pr_opt (pr_pair (pr_list SU.pr_point) SU.pr_cons)) k_cons in
    match k_cons with
    | None -> []
    | Some (pts, cons) ->
      let assumpt_info = {
        SA.assumpt_cond = S.CONS cons;
        SA.assumpt_neg = false;
        SA.assumpt_symbol = k;
        SA.assumpt_pos = pts; } in
      let assumpt = {
        assumpt_info = assumpt_info;
        assumpt_pos = pos; } in
      [lazy (Assumption assumpt, [KMap (IK.K.to_kat k, (pts, cons))])]
  in

  if is_infeasible_kaction kact then []
  else
    match kact with
    | Remove (kp, s) -> 
      (match s with
       | CVar v ->
         let instr = KT.spl_instr_of_var v in
         (match instr with
          | None -> []
          | Some (_, i) ->
            let not_removable =
              match i with
              | S.CALL (_, c, _) -> List.mem String.equal c !no_removed_events
              | _ -> false in
            let axiom_test = if is_disj_kpos kp then Kat.Bot else Kat.Top in
            let remove_axiom = lazy (
              let nv = KT.rename_var v in
              let () = DB.dhprint "old (removed) var: " IK.V.string_of v in
              let () = DB.dhprint "new var: " IK.V.string_of nv in
              let nv_kat = IK.V.to_kat nv in
              let nv_instrs = instr_map_of_var nv in
              Axiom [(Kat.Var nv_kat, `Eq, Kat.Tst axiom_test)],
              nv_instrs) in
            let ksym_tests, direct_test =
              if is_fst_kpos kp then
                test_of_symbol v fst_ksyms, direct_test_of_var v fst_kat
              else test_of_symbol v snd_ksyms, direct_test_of_var v snd_kat
            in
            let () = DB.hprint "kact: " (pr_kaction pr_ksym) kact in
            let () = DB.hprint "removed tests: " (pr_list IK.K.string_of) ksym_tests in
            let () = DB.hprint "direct tests: " (pr_opt K.pr_test) direct_test in
            let () = DB.hprint "not_removable: " pr_bool not_removable in
            let remove_assumpts =
              List.map (fun k -> mk_assumpts k (pos_of_kpos kp)) ksym_tests
              |> List.concat in
            if not_removable (* || Extlib.Option.is_none direct_test *)
            then remove_assumpts
            else [remove_axiom] (* @ remove_assumpts *))
       | CKey (b, k) ->
         let axiom_test =
           if is_disj_kpos kp then
             if b then Kat.Bot else Kat.Top
           else if b then Kat.Top else Kat.Bot in
         let remove_axioms = [lazy (Axiom [(Kat.Tst (test_of_key (true, k)),
                                            `Eq, Kat.Tst axiom_test)])] in
         let remove_assumpts = mk_assumpts k (pos_of_kpos kp) in
         remove_assumpts)
    | Replace ((kp1, s1), (kp2, s2)) ->
      (match s1, s2 with
       | CVar v1, CVar v2 ->
         let axioms = lazy (
           let v1_instrs = instr_map_of_var v1 in
           let v2_instrs = instr_map_of_var v2 in
           Axiom [(expr_of_var v1, `Eq, expr_of_var v2)],
           v1_instrs @ v2_instrs) in
         [axioms]
       | CKey (b1, k1), CKey (b2, k2) ->
         let hypos = lazy (
           let k2 = 
             if IK.K.eq k1 k2 then
               KT.rename_key k2
             else k2 in
           let k1_cons = cons_map_of_key k1 in
           let k2_cons = cons_map_of_key k2 in
           Axiom [(Kat.Tst (test_of_key (b1, k1)), `Eq,
                   Kat.Tst (test_of_key (b2, k2)))],
           k1_cons @ k2_cons) in
         let assumpt_k1 = mk_assumpts k1 kp1 in
         let assumpt_k2 = mk_assumpts k2 kp2 in
         if ksym_has_dummy_label s1 then
           assumpt_k2
         else if ksym_has_dummy_label s2 then
           assumpt_k1
         else
           let has_dummy_actions k =
             List.exists (fun ka ->
                 match ka with
                 | Remove (_, CKey (_, c)) -> IK.K.eq c k && IK.K.has_dummy_label c
                 | Replace ((_, CKey (_, c1)), (_, CKey (_, c2))) ->
                   (IK.K.eq c1 k && IK.K.has_dummy_label c1) ||
                   (IK.K.eq c2 k && IK.K.has_dummy_label c2)
                 | _ -> false) kacts in

           if has_dummy_actions k1 && has_dummy_actions k2 then
             let direct_vars_of_k1 = direct_vars_of_key axioms k1 b1 fst_kat in
             let direct_vars_of_k2 = direct_vars_of_key axioms k2 b2 snd_kat in
             let () = DB.hprint "direct_vars_of_k1: "
                 (pr_list IK.V.string_of) direct_vars_of_k1 in
             let () = DB.hprint "direct_vars_of_k2: "
                 (pr_list IK.V.string_of) direct_vars_of_k2 in

             if (List.exists (fun v1 -> List.exists (fun v2 ->
                 IK.V.eq v1 v2) direct_vars_of_k2) direct_vars_of_k1)
             then [hypos]
             else assumpt_k1 @ assumpt_k2
           else [hypos]
       | _ -> [])

let norm_cex (cex: Kat.gstring) =
  let atom, gstring = cex in
  (List.rev gstring) @ [(nil_char, atom)]

(* let first_diff_atom
 *     (fst_as: (Bdd.key * bool) list)
 *     (snd_as: (Bdd.key * bool) list) =
 *   (\* let rec helper fst_as snd_as =
 *    *   match fst_as, snd_as with
 *    *   | [], [] -> (None, None)
 *    *   | a1::_, [] -> (Some a1, None)
 *    *   | [], a2::_ -> (None, Some a2)
 *    *   | ((k1, b1) as a1)::as1, ((k2, b2) as a2)::as2 ->
 *    *     if SKU.eq_key k1 k2 then
 *    *       if b1 == b2 then helper as1 as2
 *    *       else (Some a1, Some a2)
 *    *     else (Some a1, Some a2)
 *    * in
 *    * helper (List.rev fst_as) (List.rev snd_as) *\)
 *   let find_diff as1 as2 = List.find_opt (fun (k1, b1) ->
 *       not (List.exists (fun (k2, b2) ->
 *           SKU.eq_key k1 k2 && b1 == b2) as2)) as1 in
 *   (find_diff fst_as snd_as, find_diff snd_as fst_as) *)

(* let first_diff_symbol
 *     (fst_cex: Kat.gstring)
 *     (snd_cex: Kat.gstring) =
 *   let rec helper fst_gs snd_gs =
 *     match fst_gs, snd_gs with
 *     | [], [] -> (None, None)
 *     | g1::_, [] -> (Some g1, None)
 *     | [], g2::_ -> (None, Some g2)
 *     | ((v1, as1) as g1)::gs1, ((v2, as2) as g2)::gs2 ->
 *       if SKU.eq_var v1 v2 then
 *         match first_diff_atom as1 as2 with
 *         | None, None -> helper gs1 gs2
 *         | Some a1, None -> (Some (v1, [a1]), None)
 *         | None, Some a2 -> (None, Some (v2, [a2]))
 *         | Some a1, Some a2 -> (Some (v1, [a1]), Some (v2, [a2]))
 *       else (Some g1, Some g2)
 *   in
 *   let d1, d2 = helper (norm_cex fst_cex) (norm_cex snd_cex) in
 *   (d1, d2) *)

let eq_atom_instruction instr1 instr2 =
  match instr1, instr2 with
  | S.SKIP, S.SKIP
  | S.HALT, S.HALT
  | S.FAIL, S.FAIL -> true
  | S.ASSIGN (v1, _), S.ASSIGN (v2, _) -> SU.eq_var v1 v2
  | S.CALL (_, c1, _), S.CALL (_, c2, _) ->
    if List.mem String.equal c1 !no_removed_events ||
       List.mem String.equal c2 !no_removed_events
    then String.equal c1 c2
    else true
    (* String.equal c1 c2 *)
  | _ -> false

let (++:) (d1, a1, (k1, k2)) (d2, a2, (s1, s2)) =
  let m =
    match k1, k2 with
    | None, None -> (s1, s2)
    | Some k1, None -> (k1::s1, s2)
    | None, Some k2 -> (s1, k2::s2)
    | Some k1, Some k2 -> (k1::s1, k2::s2)
  in
  (d1 + d2, a1 @ a2, m)

let edit_distance_cex_norec edit_distance_cex
    ((gs1, gs2): ksym list * ksym list) =
  match gs1, gs2 with
  | [], [] -> (!match_cost, [], ([], []))
  | _, [] ->
    let remove_cost = List.fold_left (fun c k -> c + (replace_cost_ksym k)) 0 gs1 in
    (remove_cost, List.map (fun g -> Remove (KFst, g)) gs1, (gs1, gs2))
  | [], _ ->
    let remove_cost = List.fold_left (fun c k -> c + (replace_cost_ksym k)) 0 gs2 in
    (remove_cost, List.map (fun g -> Remove (KSnd, g)) gs2, (gs1, gs2))
  | k1::ks1, k2::ks2 ->
    let remove_hd_fst_dst =
      (replace_cost_ksym k1, [Remove (KFst, k1)], (Some k1, None))
      ++: edit_distance_cex (ks1, gs2) in
    let remove_hd_snd_dst =
      (replace_cost_ksym k2, [Remove (KSnd, k2)], (None, Some k2))
      ++: edit_distance_cex (gs1, ks2) in
    (match k1, k2 with
     | CKey (b1, s1), CKey (b2, s2) ->
       let has_dummy_label_s1 = IK.K.has_dummy_label s1 in
       let has_dummy_label_s2 = IK.K.has_dummy_label s2 in
       let dst =
         if IK.K.eq s1 s2 then
           if b1 == b2 then !match_cost
           else if has_dummy_label_s1 != has_dummy_label_s2 then
             !sum_cost
           else replace_cost_ksym k1
         else if b1 == b2 then replace_cost_ksym k1
         else max_replace_cost_ksym k1 k2
       in
       let acts =
         if IK.K.eq s1 s2 && b1 == b2 then []
         else [Replace ((KFst, k1), (KSnd, k2))]
       in
       let elems =
         if IK.K.eq s1 s2 then
           match has_dummy_label_s1, has_dummy_label_s2 with
           | true, false ->
             let ns1 = IK.K.change_label s1 (IK.K.label_of s2) in
             Some (CKey (b1, ns1)), Some k2
           | false, true ->
             let ns2 = IK.K.change_label s2 (IK.K.label_of s1) in
             Some k1, Some (CKey (b2, ns2))
           | _ -> Some k1, Some k2
         else Some k1, Some k2
       in
       let replace_hd_dst = (dst, acts, elems) ++: edit_distance_cex (ks1, ks2) in
       (match has_dummy_label_s1, has_dummy_label_s2 with
       | true, false -> min2 key_of_ed replace_hd_dst remove_hd_fst_dst
       | false, true -> min2 key_of_ed replace_hd_dst remove_hd_snd_dst
       | _ -> min3 key_of_ed replace_hd_dst remove_hd_fst_dst remove_hd_snd_dst)
     | CVar v1, CVar v2 ->
       let instr_eq =
         if IK.V.eq v1 v2 then true
         else
           let instr1 = KT.spl_instr_of_var v1 in
           let instr2 = KT.spl_instr_of_var v2 in
           match instr1, instr2 with
           | Some (_, i1), Some (_, i2) ->
             eq_atom_instruction i1 i2
           | _ -> false
       in
       (** No replacement for different instructions *)
       if instr_eq then
         let replace_hd_action, replace_cost =
           if IK.V.eq v1 v2 then [], !match_cost
           else [Replace ((KFst, k1), (KSnd, k2))], max_replace_cost_ksym k1 k2 in
         let replace_hd_dst = (replace_cost, replace_hd_action, (Some k1, Some k2))
                              ++: edit_distance_cex (ks1, ks2) in
         min3 key_of_ed replace_hd_dst remove_hd_fst_dst remove_hd_snd_dst
       else
         min2 key_of_ed remove_hd_fst_dst remove_hd_snd_dst
       (* let dst, acts =
        *   if IK.V.eq v1 v2 then (!match_cost, [])
        *   else (max_replace_cost_ksym k1 k2, [Replace (k1, k2)])
        * in
        * let replace_hd_dst = (dst, acts) ++? edit_distance_cex (ks1, ks2) in
        * min3 key_of_ed replace_hd_dst remove_hd_fst_dst remove_hd_snd_dst *)
     | _ -> min2 key_of_ed remove_hd_fst_dst remove_hd_snd_dst)

let edit_distance_cex (gs1, gs2) =
  let () = DB.dhprint "gs1: " (pr_list pr_ksym) gs1 in
  let () = DB.dhprint "gs2: " (pr_list pr_ksym) gs2 in
  let () = reset_edit_dist_cost () in
  let replace_cost_gs =
    fun gs -> List.fold_left (fun c g -> c + (replace_cost_ksym g)) 0 gs in
  let () =
    let min_len = Core.Int.min (List.length gs1) (List.length gs2) in
    sum_cost := (replace_cost_gs gs1) + (replace_cost_gs gs2);
    match_cost := -(!sum_cost / (if min_len > 0 then min_len else 1))
  in
  let () = DB.dhprint "sum_cost: " pr_int !sum_cost in
  let () = DB.dhprint "match_cost: " pr_int !match_cost in
  Memo.memo_rec edit_distance_cex_norec (gs1, gs2)

let get_cex
    (axioms: H.t)
    (rop: refinement_direction)
    (fst_kat: K.expr) (snd_kat: K.expr)
  : (Kat.gstring * Kat.gstring) option =
  let _, diff = SK.compare ~hyps:axioms
      (K.expr_to_kat fst_kat) (K.expr_to_kat snd_kat) in
  match diff with
  | `E -> None
  | `L snd_cex ->
    (match rop with
     | RLe -> None
     | REq -> Some (empty_cex, snd_cex))
  | `G fst_cex -> Some (fst_cex, empty_cex)
  | `D (fst_cex, snd_cex) -> Some (fst_cex, snd_cex)

let build_axiom_syms_mapping (axioms: H.t): axmap list =
  let csyms = csyms_of_kat_hypo axioms in
  List.map (fun s ->
      match s with
      | CKey (_, k) ->
        (match KT.spl_cons_of_sym k with
         | None -> []
         | Some cons -> [KMap (k, cons)])
      | CVar v ->
        (match KT.spl_instr_of_sym v with
         | None -> []
         | Some instr -> [VMap (v, instr)])
    ) csyms
  |> List.concat

let rec search
    ~(rec_depth:int)
    (sprog: S.program)
    (fst_pname: string) (snd_pname: string)
    (rop: refinement_direction)
    (axioms: H.t)
    (assumptions: assumption list)
    (logs: refinement_log list)
  : result list =
  let handler = fun () ->
    try
      if !rec_depth_threshold > 0 &&
         rec_depth > !rec_depth_threshold then []
      else
        wrapped_search ~rec_depth:rec_depth sprog
          fst_pname snd_pname rop axioms assumptions logs
    with _ -> []
  in
  KT.wrap handler

and wrapped_search
    ~(rec_depth:int)
    (sprog: S.program)
    (fst_pname: string) (snd_pname: string)
    (rop: refinement_direction)
    (axioms: H.t)
    (assumptions: assumption list)
    (logs: refinement_log list)
  : result list =
  let instrumented_sprog = SA.assumpt_lst_instrument_prog
      (List.map (fun assumpt -> assumpt.assumpt_info) assumptions) sprog in
  let () =
    if List.not_empty assumptions then
      (DB.dhprint "assumptions: " (pr_list pr_assumption) assumptions;
       DB.dhprint "instrumented_sprog: " SU.pr_prog instrumented_sprog)
  in
  (* let klprog = KT.kat_of_prog instrumented_sprog in *)

  (** Input *)
  (* let () = if rec_depth == 0 then KT.print_kprog klprog in *)
  let () = Debug.hprint "kdiff.search: Hypos: " SKU.pr_hypos axioms in
  let () = Debug.hprint "kdiff.search: Assumpts: " pr_assumptions assumptions in
  let () = if List.not_empty assumptions then
      Debug.dhprint "kdiff.search: Instrumented prog:\n"
        SU.pr_prog instrumented_sprog
  in

  (** SymKAT comparison *)
  (* let fst_lkat = List.assoc fst_pname klprog in
   * let snd_lkat = List.assoc snd_pname klprog in *)
  let fst_lkat = KT.kat_of_cmp_proc instrumented_sprog fst_pname snd_pname in
  let snd_lkat = KT.kat_of_cmp_proc instrumented_sprog snd_pname fst_pname in
  let () = DB.hprint "kdiff.search: fst_kat: " K.pr_expr fst_lkat in
  let () = DB.hprint "kdiff.search: snd_kat: " K.pr_expr snd_lkat in

  (* let kdist, time = Func.core_time (fun () ->
   *     edit_distance (fst_lkat, snd_lkat)) in
   * let pr_match (m1, m2) =
   *   ("fst match: " ^ (pr_kelt m1)) ^ "\n" ^
   *   ("snd match: " ^ (pr_kelt m2)) ^ "\n" in
   * let () = DB.hprint "kdist: " (pr_kdist pr_kelt pr_match) kdist in
   * let () = DB.dhprint "time: " pr_core_time time in *)

  let cex = get_cex axioms rop fst_lkat snd_lkat in
  match cex with
  | None ->
    let symtab = KT.get_symtab () in
    [mk_rleaf fst_lkat snd_lkat rop
       instrumented_sprog symtab axioms logs]
  | Some (fst_cex, snd_cex) ->
    let () = debug_cex fst_pname fst_lkat fst_cex in
    let () = debug_cex snd_pname snd_lkat snd_cex in
    handle_cex ~rec_depth:rec_depth instrumented_sprog fst_pname snd_pname
      axioms rop fst_lkat snd_lkat fst_cex snd_cex logs

and handle_cex
    ~(rec_depth:int)
    (sprog: S.program)
    (fst_pname: string) (snd_pname: string)
    (axioms: H.t)
    (rop: refinement_direction)
    (fst_kat: K.expr) (snd_kat: K.expr)
    fst_cex snd_cex
    (logs: refinement_log list)
  : result list =
  let fst_ksyms = add_label_gstring axioms fst_cex fst_kat in
  let snd_ksyms = add_label_gstring axioms snd_cex snd_kat in

  let kdist, time = Func.core_time (fun () ->
      edit_distance_cex (fst_ksyms, snd_ksyms)) in
  let () = DB.hprint "ks1: " (pr_list pr_ksym) fst_ksyms in
  let () = DB.hprint "ks2: " (pr_list pr_ksym) snd_ksyms in
  let () = DB.hprint "kdist: " (pr_kdist pr_ksym (fun _ -> "")) kdist in
  let () = DB.dhprint "time: " pr_core_time time in

  let _, kacts, (fst_nks, snd_nks) = kdist in
  let () = DB.hprint "nks1: " (pr_list pr_ksym) fst_nks in
  let () = DB.hprint "nks2: " (pr_list pr_ksym) snd_nks in

  let () = List.iter (fun kact ->
      match kact with
      | Remove (_, s) ->
        (match s with
         | CKey (_, k) ->
           DB.dhprint "cons: "
             (pr_pair IK.K.string_of
                (pr_opt (pr_pair (pr_list SU.pr_point) SU.pr_cons)))
             (k, KT.spl_cons_of_key k)
         | CVar v ->
           DB.dhprint "instrs: "
             (pr_pair IK.V.string_of
                (pr_opt (pr_pair (pr_list SU.pr_point) SU.pr_instruction)))
             (v, KT.spl_instr_of_var v))
      | _ -> ()) kacts in

  let refines = List.map (refinement_of_kaction axioms kacts
                            fst_kat snd_kat fst_nks snd_nks) kacts |> List.concat in

  if List.is_empty refines then []
  else
    List.fold_left (fun (prev_refines, ares) lz_refine ->
        let updated_prev_refines, res = handle_refinement ~rec_depth:rec_depth
            prev_refines lz_refine sprog fst_pname snd_pname
            axioms rop fst_kat snd_kat logs in
        updated_prev_refines,
        ares @ res) ([], []) refines
    |> snd

and handle_refinement
    ~(rec_depth:int)
    (prev_refines: refinement list)
    (lz_refine: (refinement * axmap list) Lazy.t)
    (sprog: S.program)
    (fst_pname: string) (snd_pname: string)
    (axioms: H.t)
    (rop: refinement_direction)
    (fst_kat: K.expr) (snd_kat: K.expr)
    (logs: refinement_log list)
  : (refinement list * result list) =
  let handler = fun () ->
    let (refine_act, _) as refine = Lazy.force lz_refine in
    let () = DB.hprint "refine: " pr_refinement refine_act in
    let () = DB.hprint "prev_refines: " (pr_list pr_refinement) prev_refines in
    if List.mem eq_refinement refine_act prev_refines
    then prev_refines, []
    else
      let res = wrapped_handle_refinement ~rec_depth:rec_depth refine sprog
          fst_pname snd_pname axioms rop fst_kat snd_kat logs in
      (prev_refines @ [refine_act], res)
  in
  KT.wrap handler

and wrapped_handle_refinement
    ~(rec_depth:int)
    (refine: refinement * axmap list)
    (sprog: S.program)
    (fst_pname: string) (snd_pname: string)
    (axioms: H.t)
    (rop: refinement_direction)
    (fst_kat: K.expr) (snd_kat: K.expr)
    (logs: refinement_log list)
  : result list =
  match refine with
  | Axiom hypos, axm ->
    let log = GenAxiom (hypos, axm) in
    search ~rec_depth:(rec_depth + 1) sprog fst_pname snd_pname
      rop (axioms @ hypos) [] (logs @ [log])
  | Assumption assumpt, axm ->
    let assume_k = assumpt.assumpt_info.SA.assumpt_symbol in
    if List.exists (fun l ->
        match l with
        | CaseAnalysis (_, k, _) -> IK.K.eql k assume_k
        | _ -> false) logs
    then []
    else
      let assumpt_info = assumpt.assumpt_info in
      let neg_assumpt_info = { assumpt_info with
                               assumpt_neg = not assumpt_info.assumpt_neg } in
      let neg_assumpt = { assumpt with assumpt_info = neg_assumpt_info } in
      let pos_log = CaseAnalysis (true, assume_k, axm) in
      let neg_log = CaseAnalysis (false, assume_k, axm) in
      let symtab = KT.get_symtab () in
      let pos_res = search sprog ~rec_depth:(rec_depth + 1) fst_pname snd_pname
          rop axioms [assumpt] (logs @ [pos_log]) in
      let neg_res = search ~rec_depth:(rec_depth + 1) sprog fst_pname snd_pname
          rop axioms [neg_assumpt] (logs @ [neg_log]) in
      let () = Debug.dhprint "pos_res" (pr_list pr_result) pos_res in
      let () = Debug.dhprint "neg_res" (pr_list pr_result) neg_res in
      merge_results_pair fst_kat snd_kat symtab rop
        assumpt pos_res neg_res

let pr_kdiff_res fst_pname snd_pname results =
  List.iter (fun result ->
      Debug.hprint "========== Result ==========\n"
        pr_result result;
      (if !print_tex then
         (Debug.pprint "============================";
          Debug.texprint (pr_result_tex result)))
    ) results

let analyze (iprog: I.prog_decl)
    (fst_pname: string) (snd_pname: string) =
  let sprog = Iproc.spl_of_prog iprog in
  let () = DB.hprint "sprog: " SU.pr_prog sprog in
  let () = Debug.pprint ("Statistics: " ^ (SU.pr_stats sprog)) in
  let results = search ~rec_depth:0 sprog fst_pname snd_pname
      !refinement_op [] [] [] in
  pr_kdiff_res fst_pname snd_pname results
