(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Elimination of KAT hypotheses  *)

open Kat

(** list of hypotheses, i.e., pairs of KAT expressions related either
    by inclusion, or equality. Only some kinds of equations can be 
    eliminated: 
    - x=0, for an arbitrary expression x;
    - ax=xb, ax<xb, or xb<ax, for arbitrary tests a and b and expression x;
    - ap=a, or pa=a, for arbitrary test a, but atomic variable p;
    - p=q, for atomic variables p and q. *)
type t = (expr*[`Le|`Eq]*expr) list

exception Unusable of string

(** eliminate [hyps] [x] [y] returns a triple [(x',y',z')] of symbolic
    expressions such that 
    - KAT|-x'=y' iff KAT+hyps|-x=y .
    - KAT|-x'<=y' iff KAT+hyps|-z=y .
    - KAT|-x'=>y' iff KAT+hyps|-x=z .
    ([z'] is almost [x'+y'])
    Raises [Unusable] if some hypothesis in [hyps] cannot be exploited *)
val eliminate: t -> expr -> expr -> expr' * expr' * expr'
