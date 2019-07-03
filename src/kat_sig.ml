module type K =
sig
  type key
  type var
  type sym

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

  type store
  type diff = Eq | Lt | Gt | Diff

  val sym_of_key: key -> sym
  val sym_of_var: var -> sym
  val key_of_sym: sym -> key
  val var_of_sym: sym -> var
  val key_of_string: string -> key
  val var_of_string: string -> var

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

  val cmp_key: key -> key -> int
  val cmp_expr: expr -> expr -> diff

  val is_bot_expr: expr -> bool
  val eq_sym: sym -> sym -> bool
  val eq_var: var -> var -> bool
  val eq_key: key -> key -> bool
  val eq_expr: expr -> expr -> bool

  val kat_of_test: test -> Kat.test
  val kat_of_expr: expr -> Kat.expr
  val test_of_kat: Kat.test -> test
  val expr_of_kat: Kat.expr -> expr

  val backup: unit -> store
  val restore: store -> unit

  val pr_key: key -> string
  val pr_var: var -> string
  val pr_sym: sym -> string
  val pr_test: test -> string
  val pr_expr: expr -> string
end
