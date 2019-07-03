(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Kleene algebra with tests (KAT) expressions *)

open Common
open Bdd

type var = char
type gstring = (var,key) Common.gstring
val print_gstring: gstring formatter
type 's mem = ('s,key) Bdd.mem
type 's node = ('s,key) Bdd.node
type 'a span = (var,'a) Common.span

(** Explicit Boolean formula *)
type test =
  | Dsj of test * test 
  | Cnj of test * test 
  | Neg of test
  | Top
  | Bot
  | Prd of key

(** Conversion to Boolean BDD *)
val test_to_formula: test -> formula

(** generic KAT constructors *)
type ('o,'e) expr_ =
  | Pls of 'e * 'e
  | Dot of 'e * 'e
  | Str of 'e
  | Tst of 'o
  | Var of var

(** explicit KAT expression *)
type expr = (test,expr) expr_

(** symbolic KAT expressions (hash-consed, otherwise abstract) *)
type abstr
type expr' = abstr hval

(** sets of symbolic expressions *)
type expr'_set = abstr hset

(** hash of an expression *)
val hash: expr' -> int

(** top constructor of a symbolic KAT expression *)
val head: expr' -> (formula,expr') expr_

(** term substitution *)
val subst: (var -> expr') -> expr' -> expr'

(** set of variables appearing in an expression *)
val vars: expr' -> var set

(** smart constructors for symbolic KAT expressions: 
    - sums are sorted and associated to the left, consecutive tests are merged, 
      duplicates and [0] are removed 
    - products are associated to the left are simplified w.r.t. constants [0] and [1],
      and consecutive tests (on the left) are merged
 *)
val pls: expr' -> expr' -> expr'
val dot: expr' -> expr' -> expr'
val tod: expr' -> expr' -> expr'	(* reverse composition, almost unoptimized *)
val str: expr' -> expr'
val tst: formula -> expr'
val var: char -> expr'
val zer: expr'
val one: expr'

(** from explicit expressions to (normalised) symbolic ones *)
val expr': expr -> expr'

(** output of a symbolic expression *)
val epsilon: expr' -> formula


(** putting an expression in strict star form: forall sub-expression
    of the shape [e*], it is guaranted that [e] does not contain [1] 
    (i.e., [epsilon e!=top]) *)
val ssf: expr' -> expr'


(** pretty-printing for tests and expressions *)
val print_test: Format.formatter -> test -> unit
val print_expr: Format.formatter -> expr -> unit
val print_expr': Format.formatter -> expr' -> unit


(** [random_expr as ps n] returns a random expression 
    constructed 
    - from atomic tests in [as] and atomic Kleene elements in [ps]
    - with [n] connectives 
    - with all negations at the leaves
    - without [0]
*)
val random_expr: key list -> var list -> int -> unit -> expr

(** [random_full_expr as ps n] returns a saturated random expression:
    a random expression as explained above, summed with the universal
    expression [(\sum ps)*] *)
val random_full_expr: key list -> var list -> int -> unit -> expr
