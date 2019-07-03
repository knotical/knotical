(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Antimirov' partial derivatives for symbolic KAT expressions *)

open Common
open Bdd
open Kat
open Automata

(** partial derivatives *)
val deriv: expr'_set mem -> expr' -> expr'_set node span

(** corresponding symbolic NFA *)
val nfa: unit -> (expr', expr'_set, var, key, formula) snfa

(** split a sum into a set of expressions *)
val split: expr' -> expr'_set
