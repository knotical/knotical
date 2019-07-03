(*******************************************************************)
(*  This is part of SymbolicKAT, it is distributed under the       *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

open Common
open Automata

(* generic symbolic algorithm*)
module Symb = Safa.Make(Queues.BFS) 

(* quiet or not, stats or not *)
let quiet = ref !Sys.interactive
let stats = ref false

(* recording traces or not *)
let trace = ref false

(* do we use Hopcroft and Karp's version? *)
let hk = ref false

(* do we put expressions in strict star form first? *)
let ssf = ref false

(* which construction to use *)
let construction = ref `Antimirov
let set x () = construction := x

(* do we use up-to congruence *)
let congruence = ref false

(* hypotheses to exploit *)
let hypotheses = ref ""

let hexprs hyps x y = 
  let x,y,z = Hypotheses.eliminate hyps x y in
  if !ssf then Kat.ssf x, Kat.ssf y, Kat.ssf z else x,y,z

let hexpr x = let x,_,_ = hexprs (Parse.hyps !hypotheses) x (Kat.Tst Kat.Bot) in x

let equiv_ e a exclude x y =
  let tracer = if !trace then (
    Trace.clear();
    let pp = SDFA.trace ~exclude
      Format.pp_print_char Format.pp_print_char (Bdd.print_formula 0) a
    in
    pp y; pp x;
    Some (fun k x y ->
      let x = Bdd.tag (Bdd.constant a.SDFA.m x) in
      let y = Bdd.tag (Bdd.constant a.SDFA.m y) in
      match k with
	| `CE -> Trace.ce x y
	| `OK -> Trace.ok x y
	| `Skip -> Trace.skip x y
    ) 
  ) else None 
  in
  match 
    if !hk then e ?tracer (Bdd.unify_dsf !trace) a x y 
    else e ?tracer (Bdd.unify_naive !trace) a x y 
  with
    | None -> None
    | Some (x,y,w) -> 
      let b,c = a.SDFA.o x, a.SDFA.o y in
      Some (List.rev (Bdd.witness (Bdd.xor b c)), w)

(* Antimirov' construction *)
let antimirov e x y =
  let a,f = SNFA.reindex (Antimirov.nfa()) in
  equiv_ e (Determinisation.optimised a) IntSet.empty
    (f (Antimirov.split x)) (f (Antimirov.split y))

(* Brzozowski's construction *)
let brzozowski e x y = 
  equiv_ e (Brzozowski.dfa()) Kat.zer x y

(* Ilie and Yu's construction *)
let ilie_yu e x y =
  let a,x,y = IlieYu.enfa x y in
  let a = Determinisation.optimised (Epsilon.remove a) in
  equiv_ e a IntSet.empty (IntSet.singleton x) (IntSet.singleton y)

(* equivance check *)
let equiv x y = 
  match !construction with
    | `Antimirov -> antimirov (if !congruence then Symb.equiv_c else Symb.equiv) x y
    | `IlieYu -> ilie_yu (if !congruence then Symb.equiv_c else Symb.equiv) x y
    | `Brzozowski -> 
      if !congruence then failwith "up-to congruence cannot be used with Brzozowski's automaton"
      else brzozowski Symb.equiv x y

(* full comparison *)
let compare ?(hyps=[]) x y = 
  Stats.reset(); 
  let x',y',z' = hexprs hyps x y in
  (x',y'),
  match equiv x' y' with
    | None -> `E
    | Some w -> Stats.reset(); Trace.save(); match equiv z' y' with
	| None -> `L w
	| Some w1 -> Stats.reset(); match equiv z' x' with
	    | None -> `G w
	    | Some w2 -> Trace.restore(); `D (w1,w2)

(* exported equivance check *)
let equiv ?(hyps=[]) x y = 
  let x',y',_ = hexprs hyps x y in
  equiv x' y'

(* equivalence/inclusion/difference check *)
let check m ?(hyps="") x y =
  let x = Parse.expr x in
  let y = Parse.expr y in
  let hyps' = Parse.hyps hyps in
  match snd (compare ~hyps:hyps' x y),m with
    | `E,`E | `L _,`L | `G _,`G | `D _,`D -> ()
    | _ -> 
      if hyps="" then Format.eprintf "Invalid result on %a and %a\n%!" Kat.print_expr x Kat.print_expr y
      else Format.eprintf "Invalid result on %a and %a (hyps: %s)\n%!" Kat.print_expr x Kat.print_expr y hyps

(* printing the dfa of an expression in DOT format *)
let print_dfa x =
  let x = hexpr (Parse.expr x) in
  let trace ~exclude = SDFA.trace ~exclude Format.pp_print_char Format.pp_print_char (Bdd.print_formula 0) in
  Trace.clear();
  (match !construction with
    | `Antimirov -> 
      let a,f = SNFA.reindex (Antimirov.nfa()) in 
      trace ~exclude:IntSet.empty (Determinisation.optimised a) (f (Antimirov.split x))
    | `Brzozowski -> 
      let a = Brzozowski.dfa() in
      trace ~exclude:Kat.zer a x 
    | `IlieYu -> 
      let a,x,_ = IlieYu.enfa x Kat.zer in 
      let a = Determinisation.optimised (Epsilon.remove a) in
      trace ~exclude:IntSet.empty a (IntSet.singleton x));
  print_endline (Trace.render !hk "\"")

(* print the parsed and normalised version of a given expression *)
let cat s = Format.printf "%a\n%!" Kat.print_expr' (hexpr (Parse.expr s))

(* compare [x] and [y] and prints the result on standard output *)
let run x y =
  let answer fmt = 
    if !quiet then Format.ifprintf Format.std_formatter fmt
    else if !trace then Format.printf ("//"^^fmt)
    else Format.printf fmt
  in
  let x' = Parse.expr ~msg:"First expression: " x in
  let y' = Parse.expr ~msg:"Second expression: " y in
  let _,r = compare ~hyps:(Parse.hyps ~msg:"hypotheses: " !hypotheses) x' y'  in
  let e = match r with
    | `E -> 
      answer "%s = %s\n" x y; 0
    | `L g -> 
      answer "%s < %s\n" x y; 
      answer "(strict because %a does not belong to the lhs)\n" Kat.print_gstring g; 1
    | `G g -> 
      answer "%s > %s\n" x y; 
      answer "(strict because %a does not belong to the rhs)\n" Kat.print_gstring g; 2
    | `D (g,g') -> 
      answer "%s ≠ %s\n" x y;
      answer "(%a does not belong to the rhs, and %a does not belong to the lhs)\n"
	Kat.print_gstring g Kat.print_gstring g'; 3
  in
  if !stats then Stats.print Format.std_formatter;
  if !trace then Format.printf "%s@." (Trace.render !hk "\"");
  e

(* usage message *)
let usage () =
  Format.printf "This programs checks equivalence of KAT expressions.
See http://perso.ens-lyon.fr/damien.pous/symbolickat/ for a complete description.

Usage: %s [options] {command}

Options are the following ones:
 -q      : quiet mode
 -s      : print statistics
 -t      : trace the execution of the algorithm, and print it in DOT format
 -hk     : use the symbolic version of Hopcroft and Karp's algorithm
 -con    : additionally use up-to congruence
 -ssf    : put expressions in strict star form first
 -hyps l : exploit hypotheses in [l] (see below for syntax and restrictions)
 -ant    : use Antimirov' partial derivatives (default)
 -brz    : use Brzozowski's derivatives
 -iyu    : use Ilie and Yu's construction
 -help   : print this usage message

Commands are:
  x y    : check expressions [x] and [y] for equivalence or inclusion
 -cat x  : print the symbolic expression associated to [x]
 -dfa x  : display the symbolic DFA computed for expression [x], in DOT format

The syntax for KAT expressions is the following:
 - atomic tests are characters from `a' to `j'
 - atomic Kleene elements are characters from `k' to `z'
 - multiplication or Boolean conjunction is implicit, by juxtaposition
 - addition or Boolean disjunction is `+'
 - Kleene star is postfix `*'
 - Boolean negation is prefix `!'
 - zero and one are `0' and `1'
Typically, `(ap+q)*!a' is a wellformed expression.

The [-hyps l] option allows one to exploit KAT hypotheses when comparing the 
expressions for equivalence. When used, [l] has to be a semi-colon (;) 
separated list of equations of shape expr<expr, expr=expr, or expr>expr.
Only some kinds of equations can be eliminated: 
- x=0, for an arbitrary expression x;
- ax=xb, ax<xb, or ax>xb, for arbitrary tests a and b and expression x;
- ap=a, or pa=a, for arbitrary test a, but atomic variable p;
- p=q, for atomic variables p and q;
An exception is raised if a given equation is not recognised to belong to 
one of these cases.
" Sys.argv.(0)

let set_construction x =
  match !construction with
    | `Antimirov -> construction := x
    | y -> if x<>y then (
      Format.printf "Please specify only one automata construction (options -brz, -ant, -iyu)\n";
      exit 4)

let is_option = function
  | "" -> false
  | s when s.[0] = '-' -> true
  | _ -> false
	
let check_empty = function
  | [] -> ()
  | s::_ when is_option s ->
    Format.printf "Unexpected option: `%s'
Please specify the options before the command\n" s;
    exit 4    
  | s::_ -> 
    Format.printf "Unexpected argument: `%s'\n" s;
    exit 4

let add_hypotheses h =
  match !hypotheses with
    | "" -> hypotheses := h
    | h' -> hypotheses := h'^";"^h
    
(* processing arguments *)
let rec process_args = function
  | "-q"::l -> quiet := true; process_args l
  | "-s"::l -> stats := true; process_args l
  | "-t"::l -> trace := true; process_args l
  | "-hk"::l -> hk := true; process_args l
  | "-con"::l -> congruence := true; process_args l
  | "-ssf"::l -> ssf := true; process_args l
  | "-ant"::l -> set_construction `Antimirov; process_args l
  | "-iyu"::l -> set_construction `IlieYu; process_args l
  | "-brz"::l -> set_construction `Brzozowski; process_args l
  | "-hyps"::h::l -> add_hypotheses h; process_args l
  | "-dfa"::x::l -> check_empty l; print_dfa x; exit 0;
  | "-cat"::x::l -> check_empty l; cat x; exit 0;
  | "-help"::_ -> usage(); exit 0
  | ["-dfa"] -> Format.printf "Missing expression after command `-dfa'\n"; exit 4
  | ["-cat"] -> Format.printf "Missing expression after command `-cat'\n"; exit 4
  | s::_ when is_option s -> Format.printf "Unknown option: `%s'\n" s; exit 4
  | _::s::_ when is_option s -> Format.printf "Second expression expected rather than `%s'\n" s; exit 4
  | [_] -> Format.printf "Expecting a second expression\n"; exit 4
  | x::y::l -> check_empty l; exit (run x y)
  | [] -> ()				(* required for the web-applet *)
 
(* entry point, for standalone program *)
let run_sk () = 
  if not !Sys.interactive then 
    try process_args (List.tl (Array.to_list Sys.argv))
    with Failure s | Hypotheses.Unusable s -> print_endline s; exit 5
