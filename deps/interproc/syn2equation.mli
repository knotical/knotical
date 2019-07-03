(** Generating equations from abstract syntax tree *)

(* This file is part of the Interproc analyzer, released under GPL license.
   Please read the COPYING file packaged in the distribution.

   Copyright (C) Mathias Argoud, Gaël Lalire, Bertrand Jeannet 2007.
*)

val negate_tcons: Apron.Tcons1.t -> Apron.Tcons1.t

val tcons_of_cons:
  Apron.Environment.t -> Spl_syn.cons -> Apron.Tcons1.t

val boolexpr_of_bexpr:
  Apron.Environment.t -> Spl_syn.bexpr
  -> Apron.Tcons1.earray Boolexpr.t

(*  ********************************************************************* *)
(** {2 Forward analysis} *)
(*  ********************************************************************* *)

module Forward : sig
  val make :Spl_syn.program -> Equation.graph
    (** Generates the equation graph for forward analysis from a program. *)
end

(*  ********************************************************************* *)
(** {2 Backward analysis} *)
(*  ********************************************************************* *)


module Backward : sig
  val make :Spl_syn.program -> Equation.graph
    (** Generates the equation graph for backward analysis from a program. *)
end
