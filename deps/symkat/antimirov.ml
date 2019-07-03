(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

open Common
open Bdd
open Kat

let deriv mem = 
  let zer = constant mem Hset.empty in
  let one = constant mem (Hset.singleton one) in
  let rec deriv x = match head x with
  | Pls(x,y) -> Span.merge (binary mem Hset.union) (deriv x) (deriv y)
  | Dot(x,y) -> Span.merge (binary mem Hset.union)
    (Span.map (unary mem (Hset.map (tod y))) (deriv x))
    (Span.map (times mem zer (epsilon x)) (deriv y))
  | Str y -> Span.map (unary mem (Hset.map (tod x))) (deriv y)
  | Var i -> Span.single i one zer
  | Tst _ -> Span.empty zer
  in deriv

let nfa () = 
  let m = Bdd.init Hset.hash Hset.equal in 
  Automata.SNFA.({ m; t = deriv m; o = epsilon;
		   o0 = Bdd.bot; o2 = Bdd.dsj; state_info=print_expr' })

let rec split x = match head x with
  | Pls(x,y) -> Hset.union (split x) (split y)
  | _ -> Hset.singleton x
