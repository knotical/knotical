(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Brzozowski's derivatives for symbolic KAT expressions *)

open Common
open Automata
open Bdd
open Kat

(** derivatives *)
val deriv: expr' mem -> expr' -> expr' node span

(** corresponding symbolic DFA  *)
val dfa: unit -> (expr', var, key, formula) sdfa
