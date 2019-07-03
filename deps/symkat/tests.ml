(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** a few sanity checks *)

open Symkat

let assert_invalid_hyps h =
  let h' = Parse.hyps h in
  let z = Kat.Tst Kat.Bot in
  try ignore (Hypotheses.eliminate h' z z); Format.eprintf "Invalid hypothesis accepted: %s\n%!" h
  with Hypotheses.Unusable _ -> ()

let _ = 
  check `E "r(sr)*" "(rs)*r";
  check `E "(rs)*" "1+r(sr)*s";
  check `E "(r+s)*" "r*(sr*)*";
  check `L "(rs)*" "r*(sr*)*";
  check `D "(rs)*" "r*sr*";

  check `E "1" "a*";
  check `G "a" "ab";
  check `E "a+bc" "cb+a";
  check `E "aar+bc" "cb+ar+bc";
  check `L "(ara)*" "1+ar*a";
  check `D "(ra)*" "a+r*a";
  check `D "(ara)*" "1+ar*ba";
  check `E "1" "1+a";
  check `L "1" "1+ar";
  check `L "1" "1+ra";
  check `G "1" "0";
  check `E "1" "a+!a";
  check `E "0" "a!a";

  check `E "p*" "(1+p)*";
  check `E "p*" "(a+p+b)*";
  check `E "p*" "(1+p*)*";
  check `E "(p+q)*" "((1+p)(1+q))*";
  check `E "(p+q)*" "((1+p)q*)*";
  check `G "(p+q)*" "((a+p)(b+q))*";

  check `E "!b+!bb" "!b";
  check `E "!b+!bbr" "!b";
  check `E "!aar" "0";
  check `E "!b+!bbr(br)*" "!b";
  check `E "!b(1+br(br)*)" "!b";
  check `E "!b(br)*" "!b";
  check `E "(bc+!b!c)(brs+!brt)" "bcrs+!b!crt";
  check `D "(bc+!b!c)(brs+!brt)" "(bc+!b!c)r(cs+!ct)"; (* need rc=cr *)

  check `E "(ap!a)*" "1+ap!a";
  check `E "(a(ap)*!a)*!a" "(ap)*!a";
  check `E "(ap)*!a(ap)*!a" "(ap)*!a";

  check `L ~hyps:"ap<pb" "ap" "pb";
  check `E ~hyps:"ap=pb" "ap" "pb";
  check `G ~hyps:"ap>pb" "ap" "pb";
  check `E ~hyps:"qp=0" "(p+q)*" "p*q*";
  check `E ~hyps:"ap=a" "a" "ap";
  check `E ~hyps:"a=pa" "a" "pa";
  check `E ~hyps:"a=pa;pa=bp" "a" "bp";
  check `E ~hyps:"a=ap;ap=pb;pb=b" "a" "b";
  check `E
    "(p+q+r+s+t)* + abp*(q+!ars*+b(ct+s)*)"
    "(p+q+r+s+t)* + abcq*(q+!asr*+b(cs+t)*)";

  check `E
    "(p+q+r+s+t)* + abp*(q+!ars*+b(ct+s)*(t*r!cb+sss))"
    "(p+q+r+s+t)* + abcq*(q+!asr*+b(cs+t)*(t*r!cd+sts)+!bs*t*)";

  check `E
    "(p+q+r+s+t)* + abp*(q+!ar*(brr+!dt*s*(ar*(cs+tt)*))s*+b(ct+s)*(t*r!cb+sss))"
    "(p+q+r+s+t)* + abcq*(q+!asr*+b(cs+t)*!dt*s*(ar*(sc+ttt)*)(t*r!cd+sts)+!bs*t*)";

  assert_invalid_hyps "pq=p";
  assert_invalid_hyps "ap=qa";
  assert_invalid_hyps "apq=qa";
  assert_invalid_hyps "apq=qa";
  ()
