(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** benchmarks *)

open Symkat

let random =
  Kat.random_full_expr ['a';'b';'c';'d';'e';'f';'g'] ['p';'q';'r';'s';'t';'u';'v'] 70

let _ =
  for i = 1 to 100 do
    let x,y = random(), random() in
    if equiv x y <> None then
      (Format.printf "WRONG(full): %a\n≠\n%a" Kat.print_expr x Kat.print_expr y; exit 1);
    Format.printf "\b\b\b%i%!" i;
    (* Bdd.reset_caches(); *)
  done;
  print_newline();
  Stats.print Format.std_formatter
