(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** High-level interface of the library, main entry point for standalone program *)

open Common
open Kat

(** do we use Hopcroft and Karp's version? *)
val hk: bool ref

(** do we use up-to congruence *)
val congruence: bool ref

(** do we put expressions in strict star form first? *)
val ssf: bool ref

(** do we trace unifications in [Format.str_formatter] *)
val trace: bool ref

(** which construction do we use *)
val construction: [ `Antimirov | `Brzozowski | `IlieYu ] ref

(** equivalence check, using the above parameters; returns a
    counter-example if any.  If [hyps] is specified, exploit the
    corresponding hypotheses (see module [Hypotheses]). *)
val equiv: ?hyps:Hypotheses.t -> expr -> expr -> gstring option

(** full comparison: [compare ~hyps x y] returns
    - [`E] if [x] and [y] are equivalent,
    - [`L w] if [x] is strictly contained in [y] (then [w] is a witness for strictness),
    - [`G w] if [y] is strictly contained in [x] (then [w] is a witness for strictness),
    - [`D(w1,w2)] if [x] and [y] are incomparable (then [w1] is a witness against [x<=y], and [w2] is a witness against [y<=x]).
    Also return the actually compared terms, in symbolic form.
    Exploit hypotheses if asked to.
*)
val compare: ?hyps:Hypotheses.t -> expr -> expr -> 
  (expr'*expr')*[`E | `L of gstring | `G of gstring | `D of gstring * gstring ]


(** utility for verifications: check two expressions for equivalence
    ([`E]), difference ([`D]), left-to-right inclusion ([`L]), or
    right-to-left inclusion ([`G]).  Exploit hypotheses if asked to.
*)
val check: [ `E | `L | `G | `D ] -> ?hyps:string -> string -> string -> unit

val run: string -> string -> int

val print_dfa: string -> unit

val set_construction: [ `Antimirov | `Brzozowski | `IlieYu ] -> unit
