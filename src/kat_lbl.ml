open Lib.Print

module type Var =
sig
  type t

  val string_of: t -> string
  val texstring_of: t -> string
  val to_kat: t -> Kat.var
  val from_kat: Kat.var -> t
  val eq: t -> t -> bool
end

module type Key =
sig
  type t

  val string_of: t -> string
  val texstring_of: t -> string
  val to_kat: t -> Bdd.key
  val from_kat: Bdd.key -> t
  val eq: t -> t -> bool
end

module LK = functor (V: Var) -> functor (K: Key) ->
struct
  type var = V.t

  type key = K.t

  type test =
    | Dsj of test * test
    | Cnj of test * test
    | Neg of test
    | Top
    | Bot
    | Prd of K.t

  type expr =
    | Pls of expr * expr
    | Dot of expr * expr
    | Str of expr
    | Tst of test
    | Var of V.t

  let rec pr_test (t: test): string =
    match t with
    | Dsj (l, r) -> "(" ^ (pr_test l) ^ " | " ^ (pr_test r) ^ ")"
    | Cnj (l, r) -> "(" ^ (pr_test l) ^ " & " ^ (pr_test r) ^ ")"
    | Neg e -> "!" ^ (pr_test e)
    | Top -> "1"
    | Bot -> "0"
    | Prd k -> K.string_of k

  let rec pr_test_tex (t: test): string =
    match t with
    | Dsj (l, r) -> "(" ^ (pr_test_tex l) ^ " \\vee " ^ (pr_test_tex r) ^ ")"
    | Cnj (l, r) -> "(" ^ (pr_test_tex l) ^ " \\wedge " ^ (pr_test_tex r) ^ ")"
    | Neg e -> "\\neg " ^ (pr_test_tex e)
    | Top -> "1"
    | Bot -> "0"
    | Prd k -> K.texstring_of k

  let rec pr_expr (e: expr): string =
    match e with
    | Pls (l, r) -> "(" ^ (pr_expr l) ^ " + " ^ (pr_expr r) ^ ")"
    | Dot (l, r) -> (pr_expr l) ^ "." ^ (pr_expr r)
    | Str e -> "(" ^ (pr_expr e) ^ ")*"
    | Tst t -> pr_test t
    | Var v -> V.string_of v

  let rec pr_expr_tex (e: expr) (axl: V.t -> string): string =
    match e with
    | Pls (l, r) -> "(" ^ (pr_expr_tex l axl) ^ " + " ^ (pr_expr_tex r axl) ^ ")"
    | Dot (l, r) -> (pr_expr_tex l axl) ^ "\\!\\cdot\\!" ^ (pr_expr_tex r axl)
    | Str e -> "(" ^ (pr_expr_tex e axl) ^ ")*"
    | Tst t -> pr_test_tex t
    | Var v ->
      (* let instr = Str.global_replace (Str.regexp_string "_") "" (axl v) in *)
      V.texstring_of v

  let rec map_test f_k (ke: test): test =
    match ke with
    | Dsj (l, r) -> Dsj (map_test f_k l, map_test f_k r)
    | Cnj (l, r) -> Cnj (map_test f_k l, map_test f_k r)
    | Neg e -> Neg (map_test f_k e)
    | Top -> Top
    | Bot -> Bot
    | Prd k -> Prd (f_k k)

  let rec map_expr ((f_v, f_k) as f) (ke: expr): expr =
    match ke with
    | Pls (l, r) -> Pls (map_expr f l, map_expr f r)
    | Dot (l, r) -> Dot (map_expr f l, map_expr f r)
    | Str e -> Str (map_expr f e)
    | Tst e -> Tst (map_test f_k e)
    | Var v -> Var (f_v v)

  let rec test_to_kat (ke: test): Kat.test =
    match ke with
    | Dsj (l, r) -> Kat.Dsj (test_to_kat l, test_to_kat r)
    | Cnj (l, r) -> Kat.Cnj (test_to_kat l, test_to_kat r)
    | Neg e -> Kat.Neg (test_to_kat e)
    | Top -> Kat.Top
    | Bot -> Kat.Bot
    | Prd k -> Kat.Prd (K.to_kat k)

  let rec expr_to_kat (ke: expr): Kat.expr =
    match ke with
    | Pls (l, r) -> Kat.Pls (expr_to_kat l, expr_to_kat r)
    | Dot (l, r) -> Kat.Dot (expr_to_kat l, expr_to_kat r)
    | Str e -> Kat.Str (expr_to_kat e)
    | Tst e -> Kat.Tst (test_to_kat e)
    | Var v -> Kat.Var (V.to_kat v)

  let test_kat_syms (ke: test): char BatSet.t =
    let rec helper ke =
      match ke with
      | Dsj (l, r) -> (helper l) @ (helper r)
      | Cnj (l, r) -> (helper l) @ (helper r)
      | Neg e -> helper e
      | Top
      | Bot -> []
      | Prd k -> [K.to_kat k]
    in
    BatSet.of_list (helper ke)

  let rec expr_kat_syms (ke: expr): char BatSet.t =
    match ke with
    | Pls (l, r) ->
      let sl = expr_kat_syms l in
      let sr = expr_kat_syms r in
      BatSet.union sl sr
    | Dot (l, r) ->
      let sl = expr_kat_syms l in
      let sr = expr_kat_syms r in
      BatSet.union sl sr
    | Str e -> expr_kat_syms e
    | Tst e -> test_kat_syms e
    | Var v -> BatSet.singleton (V.to_kat v)

  let test_is_top t =
    match t with
    | Top -> true
    | _ -> false

  let expr_is_str e =
    match e with
    | Str _ -> true
    | _ -> false

  let rec expr_to_list (e: expr): expr list =
    match e with
    | Dot (l, r) -> (expr_to_list l) @ (expr_to_list r)
    | _ -> [e]

  let rec test_to_list (t: test): test list =
    match t with
    | Cnj (l, r) -> (test_to_list l) @ (test_to_list r)
    | _ -> [t]

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
end

module type Label =
sig
  type t

  val get_label: unit -> t
  val get_dummy_label: unit -> t
  val is_dummy_label: t -> bool
  val string_of: t -> string
  val eq: t -> t -> bool
end

module LVar = functor (L: Label) ->
struct
  type t = (L.t * Kat.var)

  let string_of (l, v) =
    (pr_char v) ^ "_" ^ (L.string_of l)

  let texstring_of (l, v) =
    (pr_char v) ^ "_{" ^ (L.string_of l) ^ "}"

  let label_of (l, _) = l

  let to_kat (_, v) = v

  let from_kat v = (L.get_label (), v)

  let fresh_from_kat v = (L.get_dummy_label (), v)

  let has_dummy_label (l, _) = L.is_dummy_label l

  let eq (_, v1) (_, v2) = Char.equal v1 v2

  let eql ((l1, _) as v1) ((l2, _) as v2) =
    (L.eq l1 l2) && (eq v1 v2)

  let change_label (_, v) l = (l, v) 
end

module LKey = functor (L: Label) ->
struct
  type t = (L.t * Bdd.key)

  let string_of (l, k) =
    (pr_char k) ^ "_" ^ (L.string_of l)

  let texstring_of (l, k) = 
    (pr_char k) ^ "_{" ^ (L.string_of l) ^ "} "

  let label_of (l, _) = l

  let to_kat (_, k) = k

  let from_kat k = (L.get_label (), k)

  let fresh_from_kat k = (L.get_dummy_label (), k)

  let has_dummy_label (l, _) = L.is_dummy_label l

  let eq (_, k1) (_, k2) = Char.equal k1 k2

  let eql ((l1, _) as v1) ((l2, _) as v2) =
    (L.eq l1 l2) && (eq v1 v2)

  let change_label (_, k) l = (l, k)
end

