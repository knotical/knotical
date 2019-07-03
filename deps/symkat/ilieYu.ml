(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

open Kat

let enfa x y =
  let rec aux e t m i j x = match head x with
    | Var k -> (e, (i,k,j)::t, m)
    | Tst a -> ((i,a,j)::e, t, m)
    | Dot(x,y) ->
      let (e,t,m') = aux e t (m+1) i m x in
      aux e t m' m j y
    | Pls(x,y) ->
      let (e,t,m) = aux e t m i j x in
      aux e t m i j y
    | Str x -> 
      aux ((i,Bdd.top,m)::(m,Bdd.top,j)::e) t (m+1) m m x
  in 
  let (e,t,m) = aux [] [] 2     0 1 x in 
  let (e,t,n) = aux e  t  (m+1) m 1 y in 
  let o = Common.Set.singleton 1 in   
  Automata.SENFA.({e; t; o; size=n}),0,m
