(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

open Common
open Bdd
open Kat

type t = (expr*[`Le|`Eq]*expr) list

exception Unusable of string

let rec prune x = match head x with
  | Dot(x,y) -> cnj (prune x) (prune y)
  | Pls(x,y) -> dsj (prune x) (prune y)
  | Str(x) -> ignore(prune x); top
  | Var _ -> raise Not_found 
  | Tst p -> p

let find_subst a x =
  let rec left acc z = match head z with
    | Var p -> if a == acc then p,pls (dot (var p) (tst (neg a))) (tst a) else raise Not_found
    | Dot(x,y) -> left (cnj (prune y) acc) x
    | _ -> raise Not_found
  in
  let rec right acc z = match head z with
    | Var p -> if a == acc then p,pls (dot (tst (neg a)) (var p)) (tst a) else raise Not_found
    | Dot(x,y) -> right (cnj acc (prune x)) y
    | _ -> raise Not_found
  in
  try Some (left top x) with Not_found -> 
    try Some (right top x) with Not_found -> 
      None

let rec find x x' y = match head y with
  | Dot(y,z) -> let x'y = dot x' y in 
		if x==x'y then prune z
		else find x x'y z 
  | _ -> if x==x' then prune y else raise Not_found
let find x y = if x==y then top else find x one y

let err x y = raise (Unusable (Format.asprintf "Cannot use hypothesis %a <= %a" print_expr' x print_expr' y))

let is_test a = match head a with Tst _ -> true | _ -> false
let get_test a = match head a with Tst a -> a | _ -> failwith "get_test"

let rec add acc (y,z) = match head y,head z with
  | _ when y==zer -> acc
  | _ when z==zer -> pls y acc
  | Tst a,Tst b -> pls (tst (cnj a (neg b))) acc
  | Pls(p,q),_ -> add (add acc (p,z)) (q,z)
  | Dot(a,x),_ when is_test a -> 
    (try let b = find x z in pls (dot (tst (get_test a)) (dot x (tst (neg b)))) acc
     with Not_found -> err y z)
  | _,Dot(a,x) when is_test a-> 
    (try let b = find x y in pls (dot (tst (neg (get_test a))) (dot x (tst b))) acc
     with Not_found -> err y z)
  | _ -> err y z
  
let rec split (hoare,subst) = function
  | [] -> hoare,subst
  | (x,m,y)::q -> match head x,m,head y with
      | (Var x,`Eq,Var _) -> split (hoare,(x,y)::subst) q
      | (_,`Le,_) -> split (add hoare (x,y),subst) q
      | (Tst _,`Eq,Tst _) -> split (add (add hoare (y,x)) (x,y),subst) q
      | (_,`Eq,Tst a) when a!=bot -> 
	(match find_subst a x with
	  | Some s -> split (hoare,s::subst) q
	  | None -> raise (Unusable (Format.asprintf "Cannot use hypothesis %a = %a" print_expr' x print_expr' y)))
      | (Tst a,`Eq,_) when a!=bot -> 
	(match find_subst a y with
	  | Some s -> split (hoare,s::subst) q
	  | None -> raise (Unusable (Format.asprintf "Cannot use hypothesis %a = %a" print_expr' x print_expr' y)))
      | (_,`Eq,_) -> split (add (add hoare (y,x)) (x,y),subst) q


let eliminate hyps x y =
  let hyps = List.map (fun (l,e,r) -> (expr' l,e,expr' r)) hyps in
  let hoare,subst = split (zer,[]) hyps in
  let subst = List.fold_right (fun (p,p') -> Kat.subst (fun q->if p=q then p' else var q)) subst in
  let x = subst (expr' x) in
  let y = subst (expr' y) in
  let hoare = subst hoare in
  let vars = Set.union (vars x) (vars y) in
  let univ = str (Set.fold (fun p q -> pls (var p) q) vars zer) in
  let side = dot univ (dot hoare univ) in
  pls x side, pls y side, pls x (pls y side)
