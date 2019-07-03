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
  let zer = constant mem zer in
  let one = constant mem one in
  let rec deriv x = match head x with
  | Pls(x,y) -> Span.merge (binary mem pls) (deriv x) (deriv y)
  | Dot(x,y) -> Span.merge (binary mem pls)
    (Span.map (unary mem (fun x' -> dot x' y)) (deriv x))
    (Span.map (times mem zer (epsilon x)) (deriv y))
  | Str y -> Span.map (unary mem (fun x' -> dot x' x)) (deriv y)
  | Var i -> Span.single i one zer
  | Tst _ -> Span.empty zer
  in 
  deriv

let dfa () = 
  let m = Bdd.init Kat.hash (==) in
  Automata.SDFA.({
    m;
    t = deriv m;
    o = epsilon;
    output_check = generic_output_check epsilon;
    state_info = print_expr';
  })
