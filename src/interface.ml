open Globals
open Lib
open Lib.Print
open Iast
open Kat_utils

module DB = Debug
module F = Formula
module K = Kat_utils

module StatePredicate = struct
  type t = F.formula

  let mk_true = F.mk_true

  let print = F.pr_formula
end;;

module Interface = struct
  module SPred = StatePredicate
  type t = {
    i_in: SPred.t;
    i_restrict: Kat.t;
    i_out: Kat.t;
  }

  let mk_true () =
    { i_in = SPred.mk_true ();
      i_restrict = Kat.mk_true ();
      i_out = Kat.mk_true (); }

  let print (i: t): string =
    "interface(" ^ (StatePredicate.print i.i_in) ^ ", " ^
    (Kat.print i.i_restrict) ^ ", " ^
    (Kat.print i.i_out) ^ ")"
end;;
