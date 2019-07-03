(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Ilie and Yu's construction extended to symbolic KAT expressions *)

open Kat
open Common
open Automata

(** corresponding automaton *)
val enfa: expr' -> expr' -> var senfa * int * int
