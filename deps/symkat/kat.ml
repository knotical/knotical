(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

open Common
open Hashcons

type var = char
type gstring = (var,Bdd.key) Common.gstring
let print_gstring = print_gstring Format.pp_print_char Format.pp_print_char
type 's mem = ('s,Bdd.key) Bdd.mem
type 's node = ('s,Bdd.key) Bdd.node
type 'a span = (var,'a) Common.span

type test =
  | Dsj of test * test 
  | Cnj of test * test 
  | Neg of test
  | Top
  | Bot
  | Prd of Bdd.key

let rec test_to_formula = function
  | Dsj(x,y) -> Bdd.dsj (test_to_formula x) (test_to_formula y)
  | Cnj(x,y) -> Bdd.cnj (test_to_formula x) (test_to_formula y)
  | Neg x -> Bdd.neg (test_to_formula x)
  | Top -> Bdd.top
  | Bot -> Bdd.bot
  | Prd i -> Bdd.var i

type ('o,'e) expr_ =
  | Pls of 'e * 'e
  | Dot of 'e * 'e
  | Str of 'e
  | Tst of 'o
  | Var of var
  (* | Any *)

type expr = (test,expr) expr_
type abstr = (Bdd.formula,expr') expr_
and expr' = abstr hval
type expr'_set = abstr hset

let hash x = x.hkey
let head x = x.node

let rec epsilon x = match head x with
  | Pls(x,y) -> Bdd.dsj (epsilon x) (epsilon y)
  | Dot(x,y) -> Bdd.cnj (epsilon x) (epsilon y)
  | Str x -> Bdd.top
  | Var i -> Bdd.bot
  | Tst t -> t

let m = Hashcons.create 10003
(* let _ = at_exit Hashcons.(fun () -> *)
(*   let a,b,c,d,e,f = stats m in *)
(*   Format.printf "%i,%i,%i,%i,%i,%i\n" a b c d e f *)
(* ) *)

let hashcons = 
  let hash = function 
    | Tst t -> Bdd.hash t
    | Var i -> Hashtbl.hash i
    | Str x -> Hashtbl.hash (2,x.hkey)
    | Pls(x,y) -> Hashtbl.hash (3,x.hkey,y.hkey)
    | Dot(x,y) -> Hashtbl.hash (5,x.hkey,y.hkey)
  in
  let equal x y = match x,y with
    | Tst a,Tst b -> a==b
    | Var i,Var j -> i=j
    | Pls(x,x'),Pls(y,y')
    | Dot(x,x'),Dot(y,y') -> x==y && x'==y'
    | Str x,Str y -> x==y
    | _ -> false
  in Hashcons.hashcons hash equal m

let rec cmp e f = match head e,head f with
  | Tst a,Tst b -> compare (Bdd.tag a) (Bdd.tag b)
  | Tst _,_ -> -1 | _,Tst _ -> 1
  | _ -> compare e.tag f.tag

let zer = hashcons (Tst Bdd.bot)
let one = hashcons (Tst Bdd.top)
let str x = match head x with Tst _ -> one | _ -> hashcons (Str x)
let tst t = hashcons (Tst t)
let var i = hashcons (Var i)
let pls' x y = hashcons (Pls(x,y))
let dot' x y = hashcons (Dot(x,y))

let rec vars x = match head x with
  | Pls(x,y) | Dot(x,y) -> Set.union (vars x) (vars y)
  | Str x -> vars x
  | Var p -> Set.singleton p
  | Tst _ -> Set.empty

(* e should not be a sum or a test, f does not contain a test at toplevel *)
let rec insert_pls e f = 
  match head f with
    | Pls(y,q) -> (match cmp e y with
	| 0 -> pls' y q
	| 1 -> pls' y (insert_pls e q)
	| _ -> pls' e f)
    | _ -> (match cmp e f with
	| 0 -> e
	| 1 -> pls' f e
	| _ -> pls' e f)
(* e,f are not empty and do not contain tests at toplevel*)
let rec pls e f = 
  match head e,head f with
    | Pls(x,h),Pls(y,k) -> 
      (match cmp x y with
	| 1 -> pls' y (pls e k)
	| 0 -> pls' x (pls h k)
	| _ -> pls' x (pls h f))
    | Pls(_,_),_ -> insert_pls f e
    | _ -> insert_pls e f
(* normalising sum *)
let pls e f =
  if e==zer then f
  else if f==zer then e
  else match head e,head f with
    | Tst t, Tst t' -> tst (Bdd.dsj t t')
    | Pls({node=Tst b},q), Tst a 
    | Tst a, Pls({node=Tst b},q) -> pls' (tst (Bdd.dsj a b)) q
    | Pls({node=Tst a},e), Pls({node=Tst b},f) -> pls' (tst (Bdd.dsj a b)) (pls e f)
    | _ -> pls e f

let rec dot_x_tst e tt t =
  match head e with
    | Tst t' -> tst (Bdd.cnj t t')
    | Dot(x,y) -> 
      let yt = dot_x_tst y tt t in 
      if yt==zer then zer else dot' x yt
    | _ -> dot' e tt
let rec dot_x_tst_y e tt t ttf f =
  match head e with
    | Tst t' -> 
      let tt' = Bdd.cnj t t' in 
      if tt' == Bdd.bot then zer else dot' (tst tt') f
    | Dot(x,y) -> 
      let ytf = dot_x_tst_y y tt t ttf f in 
      if ytf==zer then zer else dot' x ytf
    | _ -> dot' e ttf
(* append two lists, f does not start with a test *)
let rec dot_app e f = 
  match head e with
    | Dot(x,h) -> dot' x (dot_app h f)
    | _ -> dot' e f
(* normalising product *)
let dot e f = 
  if e==zer || f==zer then zer 
  else if e==one then f 
  else if f==one then e
  else match head f with
    | Tst t -> dot_x_tst e f t
    | Dot({node=Tst t} as tt,y) -> dot_x_tst_y e tt t f y
    | _ -> dot_app e f

let rec subst f x = match head x with
  | Pls(x,y) -> pls (subst f x) (subst f y)  
  | Dot(x,y) -> dot (subst f x) (subst f y)
  | Str x -> str (subst f x)
  | Var p -> f p
  | Tst _ -> x

(*
let rec dot'' x y = match head x with		        (* intermediate: reassociate to the right *)
  | Dot(x,x') -> dot' x (dot'' x' y)
  | _ -> dot' x y
*)
let dot'' = dot'				(* fastest: do nothing... *)
(*
let dot'' = dot			        (* slowest: normalise, nicer *)
*)

(* reverse product is less optimised *)
let tod y x = if x==one then y else dot'' x y


let rec expr' = function
  | Pls(x,y) -> pls (expr' x) (expr' y)
  | Dot(x,y) -> dot (expr' x) (expr' y) 
  | Str x -> str (expr' x)
  | Tst t -> tst (test_to_formula t)
  | Var i -> var i

let ssf_str =
  (* ensuring strict star form *)
  let plus_but_one a b = 
    if a==one then b 
    else if b==one then a
    else pls a b
  in
  let plus_but_tst a b = match head a,head b with
    | Tst t, _ -> b
    | _, Tst t -> a
    | _ -> pls a b
  in
  let rec remove e = 
    if epsilon e == Bdd.top then
      match head e with
	| Pls(a,b) -> plus_but_one (remove a) (remove b)
	| Dot(a,b) -> plus_but_tst (remove a) (remove b)
	| Str e -> e
	| _ -> e 
    else e
  in 
  fun x -> match remove x with
    | {node=Tst t} -> one
    | x -> str x

let rec ssf x = match head x with
  | Pls(x,y) -> pls (ssf x) (ssf y)
  | Dot(x,y) -> dot (ssf x) (ssf y) 
  | Str x -> ssf_str (ssf x)
  | _ -> x

let rec print_test l f = function
  | Dsj(x,y) -> Format.fprintf f (paren l 0 "%a+%a") (print_test 0) x (print_test 0) y
  | Cnj(x,y) -> Format.fprintf f (paren l 1 "%a%a") (print_test 1) x (print_test 1) y
  | Neg x -> Format.fprintf f "!%a" (print_test 2) x
  | Top -> Format.fprintf f "1"
  | Bot -> Format.fprintf f "0"
  | Prd i -> Format.fprintf f "%c" i

let rec print_expr l f = function
  | Pls(x,y) -> Format.fprintf f (paren l 0 "%a+%a") (print_expr 0) x (print_expr 0) y
  | Dot(x,y) -> Format.fprintf f (paren l 1 "%a%a") (print_expr 1) x (print_expr 1) y
  | Str x -> Format.fprintf f "%a*" (print_expr 2) x
  | Var i -> Format.fprintf f "%c" i
  | Tst t -> print_test l f t

let rec print_expr' l f x = match head x with
  | Pls(x,y) -> Format.fprintf f (paren l 0 "%a+%a") (print_expr' 0) x (print_expr' 0) y
  | Dot(x,y) -> Format.fprintf f (paren l 1 "%a%a") (print_expr' 1) x (print_expr' 1) y
  | Str x -> Format.fprintf f "%a*" (print_expr' 2) x
  | Var i -> Format.fprintf f "%c" i
  | Tst t -> Bdd.print_formula l f t

let print_test = print_test 0
let print_expr = print_expr 0
let print_expr' = print_expr' 0

let random_expr k v n =
  let k = Array.of_list (Top::List.map (fun x -> Prd x) k@List.map (fun x -> Neg (Prd x)) k) in
  let nk = Array.length k in
  let v = Array.of_list v in
  let nv = Array.length v in
  let rec expr = function
  | 0 -> if Random.int (nk+nv) < nk then Tst k.(Random.int nk) else Var v.(Random.int nv)
  | n -> 
    if Random.int 4 = 0 then Str (expr (n-1))
    else let i = Random.int n in 
	 let l,r = expr i, expr (n-i-1) in
	 if Random.bool() then Pls(l,r) else Dot(l,r)
  in fun () -> expr n

let random_full_expr k v n =
  let full = Str(List.fold_left (fun z i -> Pls (z,Var i)) (Var (List.hd v)) (List.tl v)) in
  let expr = random_expr k v n in
  fun () -> Pls(full,expr ())
