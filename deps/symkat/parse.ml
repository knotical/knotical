(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

let expr ?msg s = Common.parse ?msg Parser.expr Lexer.token (Lexing.from_string s)

let hyps ?msg s = Common.parse ?msg Parser.hyps Lexer.token (Lexing.from_string s)
