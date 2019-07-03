open Globals
open Lib

module KSym = functor (K: Kat_sig.K) ->
struct
  type ktest = K.test
  type kexpr = K.expr

  type katom_sym =
    | Top
    | Bot
    | Key of bool * K.key

  type katom = katom_sym list

  let keys_of_katom (ka: katom) =
    List.fold_left (fun ks s ->
        match s with
        | Key (_, k) -> ks @ [k]
        | _ -> ks) [] ka
    |> List.dedup K.eq_key

  let keys_of_test (t: ktest) =
    let rec helper t =
      match t with
      | K.Dsj (k, m)
      | K.Cnj (k, m) -> (helper k) @ (helper m)
      | K.Neg k -> helper k
      | K.Top | Bot -> []
      | K.Prd k -> [k]
    in List.dedup K.eq_key (helper t)

  let keys_of_expr (e: kexpr) =
    let rec helper e =
      match e with
      | K.Pls (k, m)
      | K.Dot (k, m) -> (helper k) @ (helper m)
      | K.Str k -> helper k
      | K.Tst t -> keys_of_test t
      | K.Var v -> []
    in List.dedup K.eq_key (helper e)

  let vars_of_expr (e: kexpr) =
    let rec helper e =
      match e with
      | K.Pls (k, m)
      | K.Dot (k, m) -> (helper k) @ (helper m)
      | K.Str k -> helper k
      | K.Tst t -> []
      | K.Var v -> [v]
    in List.dedup K.eq_var (helper e)

  let pr_katom_sym = function
    | Top -> "1"
    | Bot -> "0"
    | Key (s, k) -> if s then K.pr_key k else "!" ^ (K.pr_key k)

  let pr_katom = pr_list ~sep:"" pr_katom_sym

  let katom_to_test (atom: katom): K.test =
    let katom_sym_to_test a =
      match a with
      | Top -> K.mk_top
      | Bot -> K.mk_bot
      | Key (true, k) -> K.mk_prd k
      | Key (false, k) -> K.mk_neg (K.mk_prd k)
    in
    List.fold_left (fun t a ->
        let ta = katom_sym_to_test a in
        K.mk_conj t ta) K.mk_top atom

  let katom_to_expr (atom: katom): K.expr =
    atom |> katom_to_test |> K.mk_tst

  let implies (atom: katom) t =
    let katom = katom_to_expr atom in
    match (K.cmp_expr katom (K.mk_tst t)) with
    | K.Eq | K.Lt -> true
    | _ -> false

  let eq_katom (a: katom) (b: katom) =
    let ka = katom_to_expr a in
    let kb = katom_to_expr b in
    match (K.cmp_expr ka kb) with
    | K.Eq -> true
    | _ -> false

  (* let rec simplify_test (t: ktest) =
   *   match t with
   *   | K.Dsj (k, m) ->
   *     let sk = simplify_test k in
   *     let sm = simplify_test m in
   *     (match sk, sm with
   *     | K.Top, _
   *     | _, K.Top -> K.Top
   *     | K.Bot, _ -> sm
   *     | _, K.Bot -> sk
   *     | _ -> K.Dsj (sk, sm))
   *   | K.Cnj (k, m) ->
   *     let sk = simplify_test k in
   *     let sm = simplify_test m in
   *     (match sk, sm with
   *     | K.Top, _ -> sm
   *     | _, K.Top -> sk
   *     | K.Bot, _
   *     | _, K.Bot -> K.Bot
   *     | _ -> K.Cnj (sk, sm))
   *   | _ -> t *)

  (* let rec simplify (e: kexpr) =
   *   match e with
   *   | K.Pls (k, m) ->
   *     let sk = simplify k in
   *     let sm = simplify m in
   *     (match sk, sm with
   *     | K.Tst K.Top, _
   *     | _, K.Tst K.Top -> K.Tst K.Top
   *     | K.Tst K.Bot, _ -> sm
   *     | _, K.Tst K.Bot -> sk
   *     | _ -> K.Pls (sk, sm))
   *   | K.Dot (k, m) ->
   *     let sk = simplify k in
   *     let sm = simplify m in
   *     (match sk, sm with
   *     | K.Tst K.Top, _ -> sm
   *     | _, K.Tst K.Top -> sk
   *     | K.Tst K.Bot, _
   *     | _, K.Tst K.Bot -> K.Tst K.Bot
   *     | _ -> K.Dot (sk, sm))
   *   | K.Str k -> K.Str (simplify k)
   *   | K.Tst t -> K.Tst (simplify_test t)
   *   | K.Var v -> K.Var v *)

  let gen_atom_list (test_syms: K.key list): katom list =
    let rec helper (test_syms: K.key list): katom list =
      match test_syms with
      | [] -> [[Top]]
      | k::ks ->
        let ks_atom = helper ks in
        (ks_atom
         |> List.map (fun a ->
             match a with
             | [Top] -> [[Key (true, k)]; [Key (false, k)]]
             | _ -> [(Key (true, k))::a; ((Key (false, k))::a)])
          |> List.concat)
        @ ks_atom
    in
    helper test_syms
    |> List.fast_sort (fun a1 a2 -> compare (List.length a1) (List.length a2))
end

module KDeriv = functor (K: Kat_sig.K) ->
struct
  include KSym (K)

  let rec epsilon (atom: katom) (e: kexpr) =
    match e with
    | K.Str _ -> true
    | K.Var _ -> false
    | K.Tst t -> implies atom t
    | K.Dot (k, m) -> (epsilon atom k) && (epsilon atom m)
    | K.Pls (k, m) -> (epsilon atom k) || (epsilon atom m)

  let delta (atom: katom) (action: K.var) (e: kexpr): kexpr =
    let rec helper e =
      match e with
      | K.Str k -> K.mk_dot (helper k) (K.mk_str k)
      | K.Var v -> if K.eq_var v action then K.mk_tst K.mk_top else K.mk_tst K.mk_bot
      | K.Tst _ -> K.mk_tst K.mk_bot
      | K.Dot (k, m) ->
        if epsilon atom k then
          K.mk_pls (K.mk_dot (helper k) m) (helper m)
        else K.mk_dot (helper k) m
      | K.Pls (k, m) ->
        K.mk_pls (helper k) (helper m)
    in
    helper e

  module V =
  struct
    type t =
      | S of kexpr
      | F

    let print = function
      | S k -> K.pr_expr k
      | F -> "F"

    let eq v1 v2 =
      match v1, v2 with
      | S k1, S k2 -> K.eq_expr k1 k2
      | F, F -> true
      | _ -> false
  end

  module E =
  struct
    type t = (katom * K.var option)

    let eq (k1, s1) (k2, s2) =
      (eq_katom k1 k2) &&
      (match s1, s2 with
       | Some v1, Some v2 -> K.eq_var v1 v2
       | None, None -> true
       | _ -> false)

    let print (a, p) =
      match p with
      | None -> pr_katom a
      | Some v -> (pr_katom a) ^ (K.pr_var v)

    let to_expr (atom, vopt): K.expr =
      let ka = (katom_to_expr atom) in
      match vopt with
      | None -> ka
      | Some v -> K.mk_dot ka (K.mk_var v)
  end

  module A = Kautomata.Make (V) (E)

  module AP = Kautomata.BinOps (A) (A)

  module R = AP.R

  let rec regex_to_kexpr (r: R.t) =
    match r with
    | R.Pls (k, m) -> K.mk_pls (regex_to_kexpr k) (regex_to_kexpr m)
    | R.Dot (k, m) -> K.mk_dot (regex_to_kexpr k) (regex_to_kexpr m)
    | R.Str k -> K.mk_str (regex_to_kexpr k)
    | R.Top -> K.mk_tst K.mk_top
    | R.Bot -> K.mk_tst K.mk_bot
    | R.Chr k -> E.to_expr k

  let gen_automaton ?(keys=[]) ?(vars=[]) (e: K.expr) =
    let all_keys = List.dedup K.eq_key (keys @ (keys_of_expr e)) in
    let all_vars = List.dedup K.eq_var (vars @ (vars_of_expr e)) in
    let all_atoms = gen_atom_list all_keys in

    let () = Debug.hprint "gen_automata: all_keys: " (pr_list K.pr_key) all_keys in
    let () = Debug.hprint "gen_automata: all_vars: " (pr_list K.pr_var) all_vars in

    let labels =
      (List.map (fun atom ->
           List.map (fun v -> (atom, Some v)) all_vars) all_atoms
       |> List.concat) @
      (List.map (fun atom -> (atom, None)) all_atoms)
    in

    let transition e (a, vopt) =
      match e with
      | V.S k ->
        (match vopt with
          | Some v -> let succ = delta a v k in [V.S succ]
          | None -> if epsilon a k then [V.F] else [])
      | V.F -> []
    in
    let aut = A.make (Some (S e)) [F] labels transition in
    aut

  let mk_product (a: A.t) (b: A.t): AP.t =
    let start_state =
      match A.start_state a, A.start_state b with
      | Some sa, Some sb -> Some (sa, sb)
      | _ -> None
    in
    let accept_states = List.cartesian_product (A.accept_states a) (A.accept_states b) in
    let symbols = List.dedup A.eq_symbol ((A.symbols a) @ (A.symbols b)) in
    let ks, vs =
      symbols
      |> List.fold_left (fun (aa, av) (atom, var) ->
          aa @ (keys_of_katom atom),
          av @ (match var with Some v -> [v] | _ -> [])) ([], []) in

    let all_keys = List.dedup K.eq_key ks in
    let all_vars = List.dedup K.eq_var vs in
    let all_atoms = gen_atom_list all_keys in
    let () = Debug.nhprint "all_atoms: " (pr_list pr_katom) all_atoms in
    let labels =
      (List.map (fun atom ->
           List.map (fun v -> (atom, Some v)) all_vars) all_atoms
       |> List.concat) @
      (List.map (fun atom -> (atom, None)) all_atoms)
    in
    let () = Debug.nhprint "labels: " (pr_list A.print_symbol) labels in
    let transition (p, q) e =
      List.cartesian_product (A.trans_func a p e) (A.trans_func b q e)
    in
    let product_aut = AP.make start_state accept_states labels transition in
    product_aut

  let intersect (ka: K.expr) (kb: K.expr): K.expr =
    let a = gen_automaton ka in
    let () = Debug.hprint "ka: " K.pr_expr ka in
    let () = Debug.hprint "aut of ka: " A.print a in
    let b = gen_automaton kb in
    let () = Debug.hprint "kb: " K.pr_expr kb in
    let () = Debug.hprint "aut of kb: " A.print b in
    let product_aut = mk_product a b in
    let () = Debug.hprint "product aut: " AP.print product_aut in
    let intersect_regex = AP.to_regex product_aut in

    (* let module R: AP.Sig_Regex = (val (AP.get_Regex_module ())) in *)

    let intersect_k = regex_to_kexpr intersect_regex in
    intersect_k
end

