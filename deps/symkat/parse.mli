(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Parser for KAT expressions *)

open Kat

(** parsing a string into a KAT expression 
    
    - atomic tests are characters from 'a' to 'j'
    - atomic Kleene elements are characters from 'k' to 'z'
    - multiplication or Boolean conjunction is implicit, by juxtaposition
    - addition or Boolean disjunction is "+"
    - Kleene star is postfix "*"
    - Boolean negation is prefix "!"
    - zero and one are "0" and "1"

    Typically, "(ap+q)*!a" is a wellformed expression, see [Tests] for examples of the syntax
*)
val expr: ?msg:string -> string -> expr

(** parsing a finite set of KAT equations (for hypothesis elimination) *)
val hyps: ?msg:string -> string -> Hypotheses.t
